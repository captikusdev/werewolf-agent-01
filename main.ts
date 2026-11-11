import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';

// --- Constants ---
const CONCURRENCY = 10;
const ANTHROPIC_VERSION = '2023-06-01';

// --- Seeded RNG (from SDK) ---
const MASK64 = (1n << 64n) - 1n;
const TWO64 = 1n << 64n;
const rotl = (x: bigint, k: bigint): bigint => ((x << k) | (x >> (64n - k))) & MASK64;
const RNG_DOMAIN = 'agent-fun/agent/rng/v1';

class Rng {
  readonly seed: string;
  readonly label: string;
  #s: [bigint, bigint, bigint, bigint];

  constructor(seed: string | number | bigint, label = '') {
    this.seed = String(seed);
    this.label = label;
    const h = createHash('sha256').update(RNG_DOMAIN, 'utf8').update('\0').update(this.seed, 'utf8').update('\0').update(label, 'utf8').digest();
    const s: [bigint, bigint, bigint, bigint] = [h.readBigUInt64BE(0), h.readBigUInt64BE(8), h.readBigUInt64BE(16), h.readBigUInt64BE(24)];
    if (s.every((w) => w === 0n)) s[0] = 1n;
    this.#s = s;
  }

  nextU64(): bigint {
    const [s0, s1, s2, s3] = this.#s;
    const result = (rotl((s1 * 5n) & MASK64, 7n) * 9n) & MASK64;
    const t = (s1 << 17n) & MASK64;
    const a2 = s2 ^ s0;
    const a3 = s3 ^ s1;
    this.#s = [s0 ^ a3, s1 ^ a2, a2 ^ t, rotl(a3, 45n)];
    return result;
  }

  next(): number {
    return Number(this.nextU64() >> 11n) / 9_007_199_254_740_992;
  }

  int(min: number, max: number): number {
    const span = BigInt(max) - BigInt(min) + 1n;
    const limit = TWO64 - (TWO64 % span);
    for (;;) {
      const x = this.nextU64();
      if (x < limit) return Number(BigInt(min) + (x % span));
    }
  }

  pick<T>(items: readonly T[]): T {
    if (items.length === 0) throw new RangeError('Rng.pick of an empty list');
    return items[this.int(0, items.length - 1)]!;
  }
}

// --- State Tracking ---
type Seat = number;
type Role = 'werewolf' | 'seer' | 'doctor' | 'villager';

interface PlayerState {
  seat: Seat;
  name: string;
  alive: boolean;
  role: Role | null;
  claims: Role[];
  inspectedByMe: boolean;
  isWolfByMe: boolean | null;
  suspicion: number;
  votesReceived: number;
  votesCast: Record<number, Seat | null>; // day -> target
  lastProcessedSeq: number;
  speechCount: number;
}

interface GameState {
  id: number;
  me: Seat;
  myRole: Role;
  partner: Seat | null;
  players: Map<Seat, PlayerState>;
  day: number;
  phase: string;
  revealedWolves: Set<Seat>;
  confirmedVillagers: Set<Seat>;
  rng: Rng;
  seerInspections: Map<Seat, boolean>; // seat -> isWolf
  doctorLastProtected: Seat | null;
}

const getInitialState = (view: any, seed: string, gameId: number): GameState => {
  const players = new Map<Seat, PlayerState>();
  for (const p of view.players) {
    players.set(p.seat, {
      seat: p.seat,
      name: p.name,
      alive: p.alive,
      role: p.role || null,
      claims: [],
      inspectedByMe: false,
      isWolfByMe: null,
      suspicion: 50,
      votesReceived: 0,
      votesCast: {},
      lastProcessedSeq: -1,
      speechCount: 0,
    });
  }
  return {
    id: gameId,
    me: view.you.seat,
    myRole: view.you.role as Role,
    partner: view.you.partner?.seat || null,
    players,
    day: view.day,
    phase: view.phase,
    revealedWolves: new Set(),
    confirmedVillagers: new Set(),
    rng: new Rng(seed, `game-${gameId}`),
    seerInspections: new Map(),
    doctorLastProtected: null,
  };
};

const updateState = (state: GameState, view: any) => {
  state.day = view.day;
  state.phase = view.phase;
  
  // Sync basic info
  for (const [seat, p] of state.players) {
    const vPlayer = view.players.find((vp: any) => vp.seat === seat);
    if (vPlayer) {
      p.alive = vPlayer.alive;
      p.role = vPlayer.role || p.role;
      if (p.role === 'werewolf') state.revealedWolves.add(seat);
      else if (p.role) state.confirmedVillagers.add(seat);
    }
  }

  // Sync private knowledge
  if (view.you.inspections) {
    for (const insp of view.you.inspections) {
      state.seerInspections.set(insp.target, insp.is_wolf);
      if (insp.is_wolf) state.revealedWolves.add(insp.target);
      else state.confirmedVillagers.add(insp.target);
    }
  }
  if (view.you.last_protection) state.doctorLastProtected = view.you.last_protection;

  // Process ONLY new log entries
  for (const entry of view.log) {
    const player = state.players.get(entry.seat);
    if (!player || entry.seq <= player.lastProcessedSeq) continue;
    player.lastProcessedSeq = entry.seq;

    if (entry.kind === 'speech' && entry.text) {
      player.speechCount++;
      const text = entry.text.toLowerCase();
      if (text.includes('i am the seer') || text.includes('i\'m the seer') || text.includes('claim seer')) {
        if (!player.claims.includes('seer')) player.claims.push('seer');
      }
      if (text.includes('i am the doctor') || text.includes('i\'m the doctor') || text.includes('claim doctor')) {
        if (!player.claims.includes('doctor')) player.claims.push('doctor');
      }
    }

    if (entry.kind === 'vote') {
      player.votesCast[entry.day] = entry.target;
    }
  }

  // Suspicion logic
  for (const [seat, p] of state.players) {
    if (seat === state.me) { p.suspicion = 0; continue; }
    if (!p.alive) { p.suspicion = 0; continue; }
    if (state.revealedWolves.has(seat)) { p.suspicion = 100; continue; }
    if (state.confirmedVillagers.has(seat)) { p.suspicion = 0; continue; }

    let susp = 50;
    
    // Role claim conflicts
    if (p.claims.length > 1) susp += 40;
    if (p.claims.includes(state.myRole) && state.myRole !== 'villager') susp += 60;
    
    const livingSeerClaims = Array.from(state.players.values()).filter(op => op.seat !== seat && op.alive && op.claims.includes('seer'));
    if (p.claims.includes('seer') && livingSeerClaims.length > 0) susp += 30;

    // Behavioral: Quiet players are slightly suspicious
    if (state.day > 1 && p.speechCount === 0) susp += 10;

    // Voting behavior
    for (const d of Object.keys(p.votesCast)) {
      const day = Number(d);
      const target = p.votesCast[day];
      if (!target) continue;

      if (state.confirmedVillagers.has(target)) susp += 15;
      if (state.revealedWolves.has(target)) susp -= 25;
    }

    p.suspicion = Math.max(0, Math.min(100, susp));
  }
};

// --- Heuristic Strategy ---
const getHeuristicAction = (state: GameState, decision: string, options: Seat[]): any => {
  const alivePlayers = Array.from(state.players.values()).filter(p => p.alive && p.seat !== state.me);
  const others = alivePlayers.filter(p => p.seat !== state.me);
  
  // Tie-breaker helper
  const bestOf = (list: PlayerState[], compare: (a: PlayerState, b: PlayerState) => number) => {
    if (list.length === 0) return null;
    const sorted = [...list].sort((a, b) => {
      const res = compare(a, b);
      if (res !== 0) return res;
      return state.rng.next() - 0.5; // Deterministic tie-break
    });
    return sorted[0];
  };

  switch (decision) {
    case 'speak':
      // Seer revelation
      if (state.myRole === 'seer') {
        const wolf = Array.from(state.seerInspections.entries()).find(([s, isW]) => isW && state.players.get(s)?.alive);
        if (wolf) {
          return { say: `I am the seer, and I found a werewolf: seat ${wolf[0]} ${state.players.get(wolf[0])?.name}.` };
        }
      }
      const topSuspect = bestOf(others, (a, b) => b.suspicion - a.suspicion);
      if (topSuspect && topSuspect.suspicion > 65) {
        return { say: `Seat ${topSuspect.seat} ${topSuspect.name} is looking very suspicious based on their voting history.` };
      }
      return { say: null };

    case 'vote':
      // If seer revealed a wolf, follow them
      const revealedWolf = Array.from(state.players.values()).find(p => p.alive && state.revealedWolves.has(p.seat) && p.seat !== state.me);
      if (revealedWolf) return { target: revealedWolf.seat };
      
      const voteTarget = bestOf(others, (a, b) => b.suspicion - a.suspicion);
      return { target: voteTarget ? voteTarget.seat : null };

    case 'kill':
      const killTarget = bestOf(others.filter(p => p.seat !== state.partner), (a, b) => {
        if (b.claims.includes('seer')) return 1;
        if (a.claims.includes('seer')) return -1;
        return a.suspicion - b.suspicion; // Kill the most "trusted" villagers
      });
      return { target: killTarget ? killTarget.seat : null };

    case 'protect':
      const protectTarget = bestOf(others, (a, b) => {
        if (a.claims.includes('seer')) return -1;
        if (b.claims.includes('seer')) return 1;
        return a.suspicion - b.suspicion;
      });
      if (protectTarget?.seat === state.doctorLastProtected) {
         // Can't protect same person twice
         const secondBest = others.filter(p => p.seat !== state.doctorLastProtected).sort((a, b) => a.suspicion - b.suspicion)[0];
         return { target: secondBest ? secondBest.seat : null };
      }
      return { target: protectTarget ? protectTarget.seat : null };

    case 'inspect':
      const inspectTarget = bestOf(others.filter(p => !p.inspectedByMe), (a, b) => b.suspicion - a.suspicion);
      return { target: inspectTarget ? inspectTarget.seat : null };

    default:
      return { target: null };
  }
};

// --- Model Strategy ---
const MAX_REQUEST_BYTES = 131_072;
const CLIPPED_CHARS = 80;

const askModel = async (state: GameState, pending: any, rules: string, apiKey: string, baseUrl: string): Promise<any> => {
  const suspicionReport = Array.from(state.players.values())
    .filter(p => p.alive)
    .map(p => `Seat ${p.seat} (${p.name}): ${p.suspicion} ${p.claims.length ? `(Claims: ${p.claims.join(', ')})` : ''}`)
    .join('\n');

  const system = `You are an expert Werewolf player. Role: ${state.myRole}. Seat: ${state.me}.
Rules:
${rules}

Current Internal Suspicion Scores (0-100):
${suspicionReport}

Strategy:
- Track inconsistencies and claim conflicts.
- As Seer: Reveal if you found a wolf or if the village is lost.
- As Werewolf: Coordinate with partner, don't kill them, deflect suspicion.
- As Doctor: Protect claims, especially Seer.

Return ONLY a JSON object:
- speak: {"say": "text"} or {"say": null}
- vote/kill/protect/inspect: {"target": seat_number} or {"target": null}
Always justify briefly in your internal reasoning if asked, but only output the JSON.`;

  const getBody = (view: any) => ({
    model: 'claude-opus-5-5',
    max_tokens: 1024,
    thinking: { type: 'adaptive' },
    output_config: { effort: 'low' },
    system,
    messages: [{ role: 'user', content: `View: ${JSON.stringify(view)}\nDecision: ${pending.decision}\nOptions: ${JSON.stringify(pending.options)}` }],
  });

  let view = pending.view;
  let body = getBody(view);
  
  if (Buffer.byteLength(JSON.stringify(body)) > MAX_REQUEST_BYTES) {
    view = structuredClone(view);
    for (const entry of view.log) {
      if (entry.kind === 'speech' && typeof entry.text === 'string' && entry.text.length > CLIPPED_CHARS) {
        entry.text = entry.text.slice(0, CLIPPED_CHARS) + '...';
        body = getBody(view);
        if (Buffer.byteLength(JSON.stringify(body)) <= MAX_REQUEST_BYTES) break;
      }
    }
  }

  try {
    const res = await fetch(`${baseUrl}/v1/messages`, {
      method: 'POST',
      headers: {
        'content-type': 'application/json',
        'anthropic-version': ANTHROPIC_VERSION,
        'x-api-key': apiKey,
      },
      body: JSON.stringify(body),
    });

    if (!res.ok) {
       // Retry once without thinking if it was a 400 invalid_request
       if (res.status === 400) {
          const retryRes = await fetch(`${baseUrl}/v1/messages`, {
            method: 'POST',
            headers: { 'content-type': 'application/json', 'anthropic-version': ANTHROPIC_VERSION, 'x-api-key': apiKey },
            body: JSON.stringify({ model: 'claude-opus-5-5', max_tokens: 1024, system, messages: [{ role: 'user', content: user }] }),
          });
          if (!retryRes.ok) return null;
          const body: any = await retryRes.json();
          const text = body.content.find((c: any) => c.type === 'text')?.text || '';
          const match = text.match(/\{.*\}/s);
          return match ? JSON.parse(match[0]) : null;
       }
       return null;
    }
    const body: any = await res.json();
    const text = body.content.find((c: any) => c.type === 'text')?.text || '';
    const match = text.match(/\{.*\}/s);
    return match ? JSON.parse(match[0]) : null;
  } catch {
    return null;
  }
};


// --- Main Loop ---
const gameStates = new Map<number, GameState>();

async function run() {
  const env = process.env;
  const envUrl = (env.MAKEFUN_ENV_URL || '').replace(/\/+$/, '');
  const anthropicUrl = (env.ANTHROPIC_BASE_URL || '').replace(/\/+$/, '');
  const apiKey = env.ANTHROPIC_API_KEY || 'dummy';
  const seed = env.MAKEFUN_TRIAL_SEED || 'default-seed';
  const promptFile = env.MAKEFUN_PROMPT_FILE || '';
  
  if (!envUrl) throw new Error('MAKEFUN_ENV_URL is missing');

  const brief = promptFile ? readFileSync(promptFile, 'utf8') : '';
  const rules = brief.split('## The game')[1]?.split('## Trials')[0] || brief;

  const envPost = async (path: string, body: any) => {
    const res = await fetch(`${envUrl}${path}`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify(body),
    });
    return res.status === 200 ? await res.json() : null;
  };

  const inFlight = new Set<string>();

  for (;;) {
    const obs = await envPost('/observe', {});
    if (!obs || obs.done) break;

    const tasks = obs.pending.map(async (p: any) => {
      const key = `${p.game}:${p.decision}:${p.view.log.length}`;
      if (inFlight.has(key)) return;
      inFlight.add(key);

      try {
        let state = gameStates.get(p.game);
        if (!state) {
          state = getInitialState(p.view, seed, p.game);
          gameStates.set(p.game, state);
        }
        updateState(state, p.view);

        let action = await askModel(state, p, rules, apiKey, anthropicUrl);
        if (!action) {
          action = getHeuristicAction(state, p.decision, p.options || []);
        }

        // Validate action
        if (p.decision === 'speak') {
          const say = typeof action.say === 'string' ? action.say.slice(0, p.max_chars || 500) : null;
          await fetch(`${envUrl}/act`, {
            method: 'POST',
            headers: { 'content-type': 'application/json' },
            body: JSON.stringify({ game: p.game, decision: 'speak', text: say, pass: say === null }),
          });
        } else {
          const target = typeof action.target === 'number' && (p.options || []).includes(action.target) ? action.target : null;
          await fetch(`${envUrl}/act`, {
            method: 'POST',
            headers: { 'content-type': 'application/json' },
            body: JSON.stringify({ game: p.game, decision: p.decision, target }),
          });
        }
      } finally {
        inFlight.delete(key);
      }
    });

    if (tasks.length > 0) {
      await Promise.all(tasks);
    } else {
      await new Promise(r => setTimeout(r, 200));
    }
  }
}

run().catch(console.error);
