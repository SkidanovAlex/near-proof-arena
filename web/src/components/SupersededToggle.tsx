import { useSearchParams } from 'react-router-dom';
import type { ChallengeRecord } from '../api/types';

/**
 * Superseded challenges (and work recorded against them) are hidden by
 * default; `?superseded=1` shows them. Direct links always still work.
 */
export function useShowSuperseded(): [boolean, (v: boolean) => void] {
  const [params, setParams] = useSearchParams();
  const show = params.get('superseded') === '1';
  const set = (v: boolean) => {
    const next = new URLSearchParams(params);
    if (v) next.set('superseded', '1');
    else next.delete('superseded');
    setParams(next, { replace: true });
  };
  return [show, set];
}

/** Ids of challenges that have a successor. */
export function supersededIds(list: ChallengeRecord[]): Set<string> {
  return new Set(list.filter((c) => !!c.superseded_by).map((c) => c.id));
}

export function SupersededToggle({ count, show, onChange, what }: { count: number; show: boolean; onChange: (v: boolean) => void; what: string }) {
  if (count === 0 && !show) return null;
  return (
    <label className="toggle" title={`${count} ${what} hidden by default`}>
      <input type="checkbox" checked={show} onChange={(e) => onChange(e.target.checked)} /> Show superseded ({count})
    </label>
  );
}
