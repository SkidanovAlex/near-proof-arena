import { useState } from 'react';
import { useSearchParams } from 'react-router-dom';
import { listChallenges, listSubmissions } from '../api/client';
import { useAsync } from '../api/hooks';
import { AsyncView } from '../components/AsyncView';
import { DecisionBadge, RevokedBadge, TierBadge } from '../components/Badges';
import { ChlLink, SubLink } from '../components/Links';
import { SupersededToggle, supersededIds, useShowSuperseded } from '../components/SupersededToggle';
import { T } from '../components/Text';
import type { SubmissionView } from '../api/types';
import { fmtScore, fmtTime } from '../lib/format';
import { isChallengeId } from '../lib/ids';
import { displayInline } from '../lib/text';

const DECISIONS = ['PENDING', 'ADMITTED', 'REJECTED', 'INCONCLUSIVE', 'INFRA_ERROR', 'CANCELLED'] as const;
const TIERS = ['formal', 'experimental', 'demo'] as const;
const MAX_AGENT = 64;

export function SubmissionsPage() {
  const [params, setParams] = useSearchParams();
  const challenge = params.get('challenge') ?? '';
  const decision = params.get('decision') ?? '';
  const tier = params.get('tier') ?? '';
  const agent = (params.get('agent') ?? '').slice(0, MAX_AGENT);
  const [agentDraft, setAgentDraft] = useState(agent);

  const [showSuperseded, setShowSuperseded] = useShowSuperseded();
  const [challenges] = useAsync((s) => listChallenges(s), []);
  // If the challenge list is unavailable nothing is hidden.
  const superseded = challenges.status === 'ok' ? supersededIds(challenges.data) : new Set<string>();
  // An explicitly selected challenge is always shown, superseded or not.
  const visibleChallenge = (id: string) => showSuperseded || id === challenge || !superseded.has(id);
  const [subs] = useAsync(
    (s) => listSubmissions({ challenge_id: isChallengeId(challenge) ? challenge : undefined, agent: agent || undefined }, s),
    [challenge, agent],
  );

  const set = (k: string, v: string) => {
    const next = new URLSearchParams(params);
    if (v) next.set(k, v);
    else next.delete(k);
    setParams(next, { replace: true });
  };

  const filter = (list: SubmissionView[]) =>
    list.filter(
      (s) =>
        (!decision || (decision === 'PENDING' ? s.decision == null : s.decision === decision)) &&
        (!tier || s.tier === tier) &&
        (!agent || s.agent === agent) &&
        (!isChallengeId(challenge) || s.challenge_id === challenge),
    );

  return (
    <section>
      <h1>Submissions</h1>
      <form
        className="filters"
        role="search"
        aria-label="Filter submissions"
        onSubmit={(e) => {
          e.preventDefault();
          set('agent', agentDraft.trim().slice(0, MAX_AGENT));
        }}
      >
        <label>
          Challenge
          <select value={challenge} onChange={(e) => set('challenge', e.target.value)}>
            <option value="">All challenges</option>
            {challenges.status === 'ok' &&
              challenges.data.filter((c) => visibleChallenge(c.id)).map((c) => (
                <option key={c.id} value={c.id}>
                  {displayInline(c.definition.name, 80)} ({c.definition.tier}){c.superseded_by ? ' — superseded' : ''}
                </option>
              ))}
          </select>
        </label>
        <label>
          Decision
          <select value={decision} onChange={(e) => set('decision', e.target.value)}>
            <option value="">Any</option>
            {DECISIONS.map((d) => (
              <option key={d} value={d}>
                {d.replace('_', ' ')}
              </option>
            ))}
          </select>
        </label>
        <label>
          Tier
          <select value={tier} onChange={(e) => set('tier', e.target.value)}>
            <option value="">Any</option>
            {TIERS.map((t) => (
              <option key={t} value={t}>
                {t}
              </option>
            ))}
          </select>
        </label>
        <label>
          Agent
          <input
            type="text"
            value={agentDraft}
            maxLength={MAX_AGENT}
            onChange={(e) => setAgentDraft(e.target.value)}
            placeholder="exact agent handle"
            spellCheck={false}
          />
        </label>
        <button type="submit">Apply</button>
        {challenges.status === 'ok' && (
          <SupersededToggle
            count={superseded.size}
            show={showSuperseded}
            onChange={setShowSuperseded}
            what="superseded challenges (and their submissions)"
          />
        )}
        {(challenge || decision || tier || agent) && (
          <button
            type="button"
            className="link-btn"
            onClick={() => {
              setAgentDraft('');
              setParams(new URLSearchParams(showSuperseded ? { superseded: '1' } : {}), { replace: true });
            }}
          >
            Clear filters
          </button>
        )}
      </form>
      <AsyncView state={subs} what="submissions">
        {(list) => {
          const matching = filter(list);
          const rows = matching.filter((s) => visibleChallenge(s.challenge_id));
          const hidden = matching.length - rows.length;
          const hiddenNote = hidden > 0 && ` · ${hidden} from superseded challenges hidden`;
          return rows.length === 0 ? (
            <p className="empty" role="status">
              No submissions match these filters{hiddenNote}.
            </p>
          ) : (
            <div className="table-wrap">
              <p className="small muted" role="status">
                {rows.length} submission{rows.length === 1 ? '' : 's'}
                {hiddenNote}
              </p>
              <table className="data">
                <thead>
                  <tr>
                    <th scope="col">Submission</th>
                    <th scope="col">Candidate / agent</th>
                    <th scope="col">Challenge</th>
                    <th scope="col">Tier</th>
                    <th scope="col">Stage</th>
                    <th scope="col">Decision</th>
                    <th scope="col">Score</th>
                    <th scope="col">Submitted</th>
                  </tr>
                </thead>
                <tbody>
                  {rows.map((s) => (
                    <tr key={s.id} className={s.tier === 'demo' ? 'row-demo' : s.revoked ? 'row-revoked' : undefined}>
                      <td>
                        <SubLink id={s.id} />
                      </td>
                      <td>
                        <T v={s.candidate_name} max={64} empty="(unnamed — manifest not yet validated)" />
                        <div className="small muted">
                          <T v={s.agent} max={64} />
                        </div>
                      </td>
                      <td className="small">
                        <ChlLink id={s.challenge_id} />
                      </td>
                      <td>
                        <TierBadge tier={s.tier} />
                      </td>
                      <td className="small">
                        <T v={s.stage} max={32} />
                      </td>
                      <td>
                        <DecisionBadge decision={s.decision} />
                        {s.revoked && <RevokedBadge />}
                      </td>
                      <td className="num">{s.accepted === true ? fmtScore(s.score_milli) : '—'}</td>
                      <td className="small nowrap">{fmtTime(s.created_at)}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          );
        }}
      </AsyncView>
    </section>
  );
}
