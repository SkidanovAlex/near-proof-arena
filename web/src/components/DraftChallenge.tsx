import { DRAFTS } from '../generated/drafts';
import { fmtBytes } from '../lib/format';
import { newClassesByTier, shownDrafts, type DraftChallenge, type DraftNotes } from '../lib/drafts';
import { T } from './Text';

export const DraftBadge = () => <span className="badge draft">DRAFT · UNSIGNED</span>;

const DRAFT_NOTICE = 'Draft — unsigned, not open for submissions.';

/** Full draft card for the Challenges page. Never links to a submit action. */
function DraftCard({ d, notes }: { d: DraftChallenge; notes: DraftNotes }) {
  const tiers = newClassesByTier(d);
  const headingId = `draft-${d.name}`;
  return (
    <article className="card draft-card" aria-labelledby={headingId}>
      <h3 id={headingId}>
        <T v={d.name} max={80} /> <DraftBadge />
      </h3>
      <p className="draft-notice" role="note">
        <strong>{DRAFT_NOTICE}</strong> This definition is not registered on this arena and has no
        challenge id; nothing here is a judge result.
      </p>
      <p>
        <strong>{notes.title}.</strong> {notes.statement}
      </p>
      <p className="small muted">
        Scope <code>{d.scope.name}</code> · nearcore {d.nearcore_tag} · protocol v{d.protocol_version} · Lean
        relation <code>{d.scope.relation_decl}</code> · security profile <code>{d.security_profile}</code> · class
        weights {d.weight_status}
      </p>
      <h4>Coverage tiers (lowest first)</h4>
      <ol className="draft-tiers">
        {!tiers.some((t) => t.id === 'D0a') && notes.tierSummary.D0a && (
          <li>
            <strong>D0a</strong> <span className="small muted">(planned)</span> — {notes.tierSummary.D0a}
          </li>
        )}
        {tiers.map((t) => (
          <li key={t.id}>
            <strong>{t.id === 'D3a' ? 'D3α' : t.id}</strong> — {notes.tierSummary[t.id] ?? ''}
            {t.added.length > 0 && (
              <details className="small">
                <summary>
                  {t.added.length} workload class{t.added.length === 1 ? '' : 'es'} added
                </summary>
                <ul>
                  {t.added.map((c) => (
                    <li key={c.id}>
                      <code>{c.id}</code>: <T v={c.description} max={300} />
                    </li>
                  ))}
                </ul>
              </details>
            )}
          </li>
        ))}
      </ol>
      <div className="two-col">
        <div>
          <h4>What is claimed so far</h4>
          <ul className="small">
            {notes.claimed.map((x, i) => (
              <li key={i}>{x}</li>
            ))}
          </ul>
          <h4>Status</h4>
          <ul className="small">
            {notes.status.map((x, i) => (
              <li key={i}>{x}</li>
            ))}
          </ul>
        </div>
        <div>
          <h4>Remaining before release</h4>
          <ul className="small">
            {notes.remaining.map((x, i) => (
              <li key={i}>{x}</li>
            ))}
          </ul>
          <p className="small muted">
            Draft limits: prove {Math.round(d.limits.max_prove_ms / 1000)} s, verify{' '}
            {Math.round(d.limits.max_verify_ms / 1000)} s, proof {fmtBytes(d.limits.max_proof_bytes)}, RAM{' '}
            {fmtBytes(d.limits.max_ram_bytes)}.
          </p>
        </div>
      </div>
      <details className="small">
        <summary>
          Excluded from scope ({d.scope.excludes.length}) and restrictions ({d.scope.restrictions.length})
        </summary>
        <ul className="excl-list">
          {d.scope.excludes.map((x) => (
            <li key={x}>
              <code className="excl">{x}</code>
            </li>
          ))}
        </ul>
        <ul className="restrictions">
          {d.scope.restrictions.map((r) => (
            <li key={r.id}>
              <code>{r.id}</code>: <T v={r.text} max={400} />
            </li>
          ))}
        </ul>
      </details>
      <p className="small muted">
        Status as of {notes.asOf}. Specification (repository paths):{' '}
        {notes.docs.map((x, i) => (
          <span key={x.path}>
            {i > 0 && '; '}
            <code>{x.path}</code> ({x.what})
          </span>
        ))}
        . Draft file sha256 <span className="mono">{d.source_sha256.slice(0, 16)}…</span>
      </p>
    </article>
  );
}

export function DraftChallenges({ drafts = DRAFTS }: { drafts?: DraftChallenge[] }) {
  const shown = shownDrafts(drafts);
  if (shown.length === 0) return null;
  return (
    <section className="board-section draft-section" aria-labelledby="drafts-h">
      <h2 id="drafts-h">Drafts (unsigned, not open for submissions)</h2>
      <p className="small muted">
        Drafts are exported from the repository at build time. They are not governance-signed, not
        registered here and cannot be submitted to; their content may still change.
      </p>
      {shown.map(({ d, notes }) => (
        <DraftCard key={d.name} d={d} notes={notes} />
      ))}
    </section>
  );
}

/** Compact entry for the Research page. */
export function DraftResearchNote({ drafts = DRAFTS }: { drafts?: DraftChallenge[] }) {
  const shown = shownDrafts(drafts);
  if (shown.length === 0) return null;
  return (
    <section className="board-section draft-section" aria-labelledby="draft-research-h">
      <h2 id="draft-research-h">In preparation (draft, not open for submissions)</h2>
      {shown.map(({ d, notes }) => (
        <div key={d.name} className="card draft-card">
          <p>
            <strong>
              <T v={d.name} max={80} />
            </strong>{' '}
            <DraftBadge /> — {notes.title}. {DRAFT_NOTICE}
          </p>
          <ul className="small">
            {notes.claimed.map((x, i) => (
              <li key={i}>{x}</li>
            ))}
          </ul>
          <p className="small muted">
            Remaining: {notes.remaining.join(' ')} Status as of {notes.asOf}; details on the Challenges page and in{' '}
            <code>{notes.docs[notes.docs.length - 1]?.path}</code>.
          </p>
        </div>
      ))}
    </section>
  );
}
