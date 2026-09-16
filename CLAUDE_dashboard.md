# Whale Dashboard — Claude Code Project Guide

Single-page JS dashboard for the Whale Intelligence options system. Deployed on
GitHub Pages. This repo is the VIEW; the scanner repo is the source of truth.

## Primary file
- **`index.html`** — the entire dashboard (HTML + inline CSS + inline JS).

## How it works
- Reads `results.json` from the scanner repo (`eastbiz/whale-intelligence`) via
  `raw.githubusercontent.com` to bypass GitHub Pages CDN caching.
- Renders opportunities and position actions by filtering on each item's `mode`
  (CSP / CC / LEAPS / CONVEXITY / BCS / SPIKE_CC / DROP_CSP) and `action`
  (BIG MOVE / TAKE PROFIT / EARNINGS WARNING / HOLD).
- **The scanner is authoritative.** This dashboard only displays what the
  scanner emits. Do not compute trading logic here — if a value is wrong, the
  fix is almost always in `whale_scanner.py`, not here.

## Key tabs / sections
- **Opportunities** — CSP, CC, LEAPS, Convexity, Bull Call Spread, Spike CC,
  Post-Drop filters. LEAPS and Convexity have sortable table views.
- **Positions** — current holdings. `Positions | Holdings | Trade History`
  switch on the right; the account buttons on the left apply to all three.
  **Trade History (A73, 2026-09-15):** renders `results.trade_history` —
  closed option cycles from broker fills (stock price at the opening and
  closing fill, credit, buy-back, how closed, days held, kept % of credit,
  planned vs realized %/yr, DTE at open next to days actually held) plus open
  lots with their per-fill entry price. Newest first; filters for account
  (shared buttons), type (CC / CSP) and symbol (buttons built from the data,
  with counts) — John reads it per name before writing the next call.
  **LEAPS (A76, 2026-09-16):** a fourth type button. `renderLeapsHistory()`
  shows the `LONG_CALL` lots grouped by symbol — a summary line per name
  (contracts, cost, breakeven min–max and contract-weighted, stock now vs
  weighted BE, value, P&L) and one chip per EXPIRATION (DTE, contracts ×
  strikes, avg cost, BE range) — then one row per fill: stock at the buy,
  cost with the intrinsic + time-value split, breakeven and how far the
  stock had to rise, stock now vs breakeven, mark, P&L. Every number is the
  scanner's (`breakeven`, `extrinsic_*`, `mark`, `pnl_*`, `spot_vs_be_pct`;
  group lines from `trade_history.leaps_by_ticker` when all accounts are
  shown, plain sums of the same lot numbers under an account filter).
  `mark == null` prints "not priced" — the contract was not in that scan's
  position feed. "All" is CC + CSP only (`histTypeMatch`); long calls no
  longer print their cost in the Credit column. The symbol buttons follow
  the selected type. Closed-LEAPS %/yr is blank under 30 days held.
  Every figure is the scanner's (credit/strike basis, calendar days);
  `renderTradeHistory()` only formats. The note line shows each feed's
  status — "0 Trade rows" on IBKR means the Flex query lacks the Trades
  section, not that IBKR had no trades. CSP/CC opportunity cards carry one
  line from the same data (`lastCycleLine()`): the last closed cycle of the
  same kind on that name.
- **CSP / CC Actions** — position exit alerts. BIG MOVE sorts to the top
  ("🔴 ACT NOW" section). Shows "⚠ price stale — check live" when the scanner
  flags an unreliable option mark (`mark_src` not `chain`/`chain_near`).

## Conventions
- Validate JS before delivering: extract inline `<script>` to a temp file and
  run `node --check`.
- No browser storage APIs beyond what already exists; keep changes minimal.
- LEAPS "vs Owned" compares raw breakeven with a DTE-mismatch flag (⚠ ±Nmo DTE)
  when expiries differ >90 days — intentional, keep it.
- **LEAPS expiration filter (2026-09-01, John's request; MULTI-select since
  2026-09-16):** buttons in `#leaps-expiry-filter` (All dates / one per
  distinct opportunity expiry, with "own Nx" showing his contracts at that
  date). Each date button TOGGLES membership in `leapsExpirySel` (array of
  8-digit keys, empty = all; persisted in localStorage). **Dec 2028 + Jan 2028
  start selected by default** (`LEAPS_EXPIRY_DEFAULT_MONTHS`) — John's
  preferred dates; Jan 2029 is one click. His own clicks override the default
  and persist. Selected dates filter rows (table AND cards) and scope vs Owned
  to owned LEAPS with the SAME expiration AS EACH ROW — no same-date position
  means NO comparison ("—"), by design; do not fall back to another date.
  "All dates" (selection empty) keeps the cross-expiry compare + DTE flag
  above. The Actionable-Today tile's LEAPS click-through clears the selection
  for the session so its count maps 1:1 onto cards (A59). Expiry formats
  differ by source (opportunities `2028-01-21`, owned positions `20280121`) —
  always compare via `expKey()`, never raw strings.
- **LEAPS view defaults to At/Near buy target only (John, 2026-09-16):**
  `leapsNearOnly` (default true, persisted) filters the LEAPS table/cards to
  `in_zone === true` — the same predicate as the global 🎯 filter, keep them
  identical. The `#leaps-near-toggle` button shows the full list. The expiry
  buttons and the "No LEAPS card" panel are built from the FULL list, before
  this filter — a row hidden by the toggle is not a missing card.
- **The "No LEAPS card for N names" panel starts COLLAPSED and stays the way
  John left it** (`window.leapsMissingOpen`, via `ontoggle`). It used to
  re-expand on every date-filter click; John reads it only when
  troubleshooting. Do not re-add auto-open — the summary line already names
  the at/near count.

## Full context
The complete system guide, trading philosophy, gotchas, and conventions live in
the scanner repo's `CLAUDE.md` (`eastbiz/whale-intelligence`). Read that for
anything beyond dashboard rendering.

## Deploy
Push `index.html`; changes are live on GitHub Pages after the next scan writes
fresh `results.json`.
