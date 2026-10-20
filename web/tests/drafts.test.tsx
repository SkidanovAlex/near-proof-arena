import { screen, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { demoDataset } from '../mock/fixtures';
import { DRAFTS } from '../src/generated/drafts';
import { newClassesByTier, shownDrafts } from '../src/lib/drafts';
import { renderApp } from './helpers';

describe('unsigned draft challenges', () => {
  it('the generated export contains the unified near-chunk-v3 draft with its coverage tiers', () => {
    const d = DRAFTS.find((x) => x.name === 'near-chunk-v3');
    expect(d).toBeDefined();
    expect(d!.source_path).toBe('challenges/drafts/near-chunk-v3.draft.json');
    expect(d!.coverage?.tiers.map((t) => t.id)).toEqual(['D0a', 'D0', 'D1a', 'D1', 'D2', 'D3a']);
    const tiers = newClassesByTier(d!);
    // Every class is introduced by exactly one tier.
    expect(tiers.flatMap((t) => t.added.map((c) => c.id)).sort()).toEqual(d!.classes.map((c) => c.id).sort());
    expect(shownDrafts(DRAFTS).map((x) => x.d.name)).toEqual(['near-chunk-v3']);
  });

  it('Challenges page shows the draft clearly labelled, outside the challenge table, with no submit action or challenge id', async () => {
    renderApp('/', demoDataset());
    const section = (await screen.findByRole('heading', { name: /Drafts \(unsigned, not open for submissions\)/ })).closest('section')!;
    const card = within(section).getByRole('article', { name: /near-chunk-v3/ });
    expect(within(card).getByText('DRAFT · UNSIGNED')).toBeInTheDocument();
    expect(within(card).getByRole('note')).toHaveTextContent('Draft — unsigned, not open for submissions.');
    expect(card).toHaveTextContent('RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3');
    expect(card).toHaveTextContent('nearV3_admission_final');
    expect(card).toHaveTextContent('600 s limit');
    for (const t of ['D0a', 'D0', 'D1', 'D2', 'D3α']) expect(within(card).getAllByText(t).length).toBeGreaterThan(0);
    expect(card).toHaveTextContent('docs/BENCHMARK_SPEC.md §17');
    // Not registered: no challenge id, no links (nothing to submit to), not in the signed-challenge table.
    expect(card.textContent).not.toMatch(/chl_[0-9a-f]{8}/);
    expect(within(card).queryByRole('link')).toBeNull();
    expect(within(card).queryByRole('button')).toBeNull();
    expect(within(card).queryByText(/\b(ADMITTED|SIGNED|REGISTERED)\b/)).toBeNull();
    expect(within(screen.getByRole('table')).queryByText('near-chunk-v3')).toBeNull();
  });

  it('Research page carries a matching draft entry', async () => {
    renderApp('/research', demoDataset());
    const h = await screen.findByRole('heading', { name: /In preparation \(draft, not open for submissions\)/ });
    const section = h.closest('section')!;
    expect(section).toHaveTextContent('near-chunk-v3');
    expect(section).toHaveTextContent('Draft — unsigned, not open for submissions.');
    expect(within(section).queryByRole('link')).toBeNull();
  });
});
