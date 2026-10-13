/**
 * Unsigned draft challenges, exported at build time from
 * challenges/drafts/*.draft.json (scripts/export-drafts.mjs). A draft is not
 * registered on the server, has no challenge id and accepts no submissions.
 */
export interface DraftChallenge {
  name: string;
  source_path: string;
  source_sha256: string;
  season: string;
  tier: string;
  created_at: string;
  nearcore_tag: string;
  nearcore_commit: string;
  protocol_version: number;
  scope: {
    name: string;
    kind: string;
    granularity: string;
    relation_module: string;
    relation_decl: string;
    restrictions: { id: string; text: string }[];
    excludes: string[];
  };
  coverage: { statement_spec: string; tiers: { id: string; rank: number; classes: string[] }[] } | null;
  classes: { id: string; description: string }[];
  weight_status: string;
  security_profile: string;
  limits: { max_prove_ms: number; max_verify_ms: number; max_proof_bytes: number; max_ram_bytes: number };
}

/** Hand-maintained status notes (source: docs/HANDOVER.md §4–§5). */
export interface DraftNotes {
  asOf: string;
  title: string;
  statement: string;
  tierSummary: Record<string, string>;
  claimed: string[];
  status: string[];
  remaining: string[];
  docs: { path: string; what: string }[];
}

export const DRAFT_NOTES: Record<string, DraftNotes> = {
  'near-chunk-v3': {
    asOf: '2026-10-13',
    title: 'Full NEAR chunk validation (unified challenge)',
    statement:
      'One challenge for the whole chunk state transition of NEAR protocol version 86: the statement is ' +
      'RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3, a drop-in for the stateless validator’s validate_chunk_state_witness. ' +
      'A candidate declares a coverage tier and may abstain on inputs outside it; entries rank by tier, then by cost.',
    tierSummary: {
      D0a: 'Succinct-STARK subset of D0 with explicit size bounds (B0 = 2.0 MB). Planned as the lowest tier; not yet listed in this draft.',
      D0: 'Chunk context authentication, quiet chunks, incoming cross-shard Transfer receipts and missing chunks.',
      D1: 'Adds Transfer transactions, including ones that fail validation.',
      D2: 'Adds every non-WASM action kind, delayed-receipt queues / outgoing buffers and epoch boundaries.',
      D3a: 'Adds WASM function calls (storage, promises and callbacks, yields) up to the gas capacity G_α.',
    },
    claimed: [
      'D0a tier: the Lean certificate nearV3_admission_final is proved with no open hypotheses (axiom audit: propext, Classical.choice, Quot.sound only).',
      'The Rust prover (np-udr-stark-v2) produces real proofs that the Lean verifier accepts on 3 fixtures (5.3–5.7 MB each); all buses balance on all 81 fixtures.',
      'The D1, D2 and D3α specifications are each difftested against nearcore, Lean and Python with 0 disagreements.',
    ],
    status: [
      'Unsigned draft: not frozen, not signed, not registered on this arena, not open for submissions.',
    ],
    remaining: [
      'Packaging the v3 prover for the judge-style build.',
      'Prove time: real proofs take 710–749 s against the draft’s 600 s limit (13.3 GB RSS against 16 GiB).',
      'Elaboration within the 4 h judge budget and leanchecker / nanoda / lean4lean rechecks of the certificate closure.',
      'lean4lean recursion failure on the D3α reference (blocks formal admission at D3α).',
      'Oracle fixture regeneration for the current A7 measure; adding the D0a tier’s classes to the draft.',
      'Then: freeze, measure, sign, register.',
    ],
    docs: [
      { path: 'challenges/drafts/near-chunk-v3.draft.json', what: 'the draft definition' },
      { path: 'docs/BENCHMARK_SPEC.md §17', what: 'coverage tiers and ranking' },
      { path: 'docs/CONTRACTS.md §11', what: 'coverage-tiered challenge contract' },
      { path: 'docs/HANDOVER.md §4–§5', what: 'current status and blockers' },
    ],
  },
};

/** Classes a tier adds over the tier ranked just below it. */
export function newClassesByTier(d: DraftChallenge): { id: string; rank: number; added: { id: string; description: string }[] }[] {
  if (!d.coverage) return [];
  const desc = new Map(d.classes.map((c) => [c.id, c.description.replace(/^\[[^\]]*\]\s*/, '')]));
  const tiers = [...d.coverage.tiers].sort((a, b) => a.rank - b.rank);
  const seen = new Set<string>();
  return tiers.map((t) => {
    const added = t.classes.filter((c) => !seen.has(c)).map((c) => ({ id: c, description: desc.get(c) ?? '' }));
    t.classes.forEach((c) => seen.add(c));
    return { id: t.id, rank: t.rank, added };
  });
}

/** Drafts that have status notes; only these are shown. */
export function shownDrafts(all: DraftChallenge[]): { d: DraftChallenge; notes: DraftNotes }[] {
  return all.flatMap((d) => (DRAFT_NOTES[d.name] ? [{ d, notes: DRAFT_NOTES[d.name] }] : []));
}
