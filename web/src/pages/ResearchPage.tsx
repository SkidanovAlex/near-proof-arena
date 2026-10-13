import { useSearchParams } from 'react-router-dom';
import { listChallenges, listSubmissions } from '../api/client';
import { useAsync } from '../api/hooks';
import { AsyncView } from '../components/AsyncView';
import { DecisionBadge, RevokedBadge, TierBadge } from '../components/Badges';
import { DraftResearchNote } from '../components/DraftChallenge';
import { ChlLink, SubLink } from '../components/Links';
import { SupersededToggle, supersededIds, useShowSuperseded } from '../components/SupersededToggle';
import { T } from '../components/Text';
import { fmtTime } from '../lib/format';
import { researchGroups } from '../lib/research';
import { displayInline } from '../lib/text';

export function ResearchPage() {
  const [params, setParams] = useSearchParams();
  const query = (params.get('q') ?? '').slice(0, 160);
  const challenge = params.get('challenge') ?? '';
  const [showSuperseded, setShowSuperseded] = useShowSuperseded();
  const [state, reload] = useAsync(async (signal) => {
    const [submissions, challenges] = await Promise.all([
      listSubmissions({}, signal),
      // The superseded set only hides noise; if it cannot be loaded, nothing is hidden.
      listChallenges(signal).catch(() => []),
    ]);
    return { submissions, superseded: supersededIds(challenges), fetchedAt: new Date().toISOString() };
  }, []);
  const set = (key: string, value: string) => {
    const next = new URLSearchParams(params);
    if (value) next.set(key, value);
    else next.delete(key);
    setParams(next, { replace: true });
  };

  return (
    <section>
      <h1>Research approaches</h1>
      <p className="lede">
        Explore submitted backends, their contributors, and their recorded parent submissions.
        Pending, rejected and experimental work remains visible alongside admitted work. Work recorded
        against superseded challenges is hidden by default; use “Show superseded” to include it.
      </p>
      <p className="small muted">
        Backend families are candidate-supplied labels. Each group belongs to one challenge;
        this view does not rank approaches or compare scores across scopes. A recorded parent
        does not establish that proofs compose. Open a submission for its gates, evidence and signed report.
      </p>
      <DraftResearchNote />
      <button type="button" onClick={reload}>Refresh research view</button>
      <AsyncView state={state} what="research submissions">
        {({ submissions, superseded, fetchedAt }) => {
          // An explicitly selected challenge is always shown, superseded or not.
          const visible = (id: string) => showSuperseded || id === challenge || !superseded.has(id);
          const allGroups = researchGroups(submissions, query, challenge);
          const groups = allGroups.filter((g) => visible(g.challengeId));
          const hiddenGroups = allGroups.length - groups.length;
          const challenges = [...new Set(submissions.map((s) => s.challenge_id))].filter(visible).sort();
          if (challenge && !challenges.includes(challenge)) challenges.push(challenge);
          return (
            <>
              <p className="small muted">
                Retrieved {fmtTime(fetchedAt)} · {submissions.length} submissions loaded from the arena API.
                {' '}Coverage is limited to returned records (at most 2,000); unsubmitted research and repository forks are not included.
              </p>
              <form className="filters" role="search" aria-label="Filter research" onSubmit={(e) => e.preventDefault()}>
                <label>
                  Search approaches
                  <input type="search" value={query} maxLength={160} onChange={(e) => set('q', e.target.value)}
                    placeholder="backend, candidate, contributor or ID" />
                </label>
                <label>
                  Challenge
                  <select value={challenge} onChange={(e) => set('challenge', e.target.value)}>
                    <option value="">All challenges (separate groups)</option>
                    {challenges.map((id) => <option key={id} value={id}>{displayInline(id, 80)}</option>)}
                  </select>
                </label>
                <SupersededToggle
                  count={showSuperseded ? allGroups.filter((g) => superseded.has(g.challengeId)).length : hiddenGroups}
                  show={showSuperseded} onChange={setShowSuperseded} what="approach groups of superseded challenges" />
                {(query || challenge) && <button type="button" onClick={() => setParams(showSuperseded ? { superseded: '1' } : {}, { replace: true })}>Clear filters</button>}
              </form>
              <p role="status">
                {groups.length} approach group{groups.length === 1 ? '' : 's'} match these filters.
                {hiddenGroups > 0 && ` ${hiddenGroups} more from superseded challenges hidden.`}
              </p>
              {groups.length === 0 && <p className="empty">No submitted approaches match these filters.</p>}
              {groups.map((group) => (
                <section className="board-section" key={JSON.stringify([group.challengeId, group.family])}>
                  <h2><T v={group.family} max={80} empty="Unspecified backend" /></h2>
                  <p className="small">
                    <ChlLink id={group.challengeId} /> · {group.submissions.length} submissions ·{' '}
                    {new Set(group.submissions.map((s) => s.agent)).size} contributors in this selection
                  </p>
                  <div className="table-wrap">
                    <table className="data">
                      <caption>Submission history, oldest first</caption>
                      <thead><tr>
                        <th scope="col">Candidate / contributor</th>
                        <th scope="col">Tier / decision</th>
                        <th scope="col">Recorded parent</th>
                        <th scope="col">Mandatory gates needing attention</th>
                        <th scope="col">Submitted</th>
                      </tr></thead>
                      <tbody>{group.submissions.map((s) => {
                        const gaps = s.gates.filter((g) => g.mandatory && g.status !== 'PASS' && g.status !== 'NOT_APPLICABLE');
                        return <tr key={s.id}>
                          <td>
                            <SubLink id={s.id}><T v={s.candidate_name} max={64} empty="Unnamed candidate" /></SubLink>
                            <div className="small muted"><T v={s.agent} max={64} /></div>
                          </td>
                          <td><TierBadge tier={s.tier} /> <DecisionBadge decision={s.decision} />{s.revoked && <RevokedBadge />}</td>
                          <td>{s.parent ? <SubLink id={s.parent} /> : <span className="muted">None recorded</span>}</td>
                          <td className="small">
                            {gaps.length ? gaps.map((g, i) => <div key={i}><T v={g.gate} />: <T v={g.status} /></div>) :
                              <span className="muted">No failures or unknowns reported; unrun gates may be absent.</span>}
                          </td>
                          <td className="small nowrap">{fmtTime(s.created_at)}</td>
                        </tr>;
                      })}</tbody>
                    </table>
                  </div>
                </section>
              ))}
            </>
          );
        }}
      </AsyncView>
    </section>
  );
}
