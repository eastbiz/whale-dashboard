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
- **Positions** — current holdings.
- **CSP / CC Actions** — position exit alerts. BIG MOVE sorts to the top
  ("🔴 ACT NOW" section). Shows "⚠ price stale — check live" when the scanner
  flags an unreliable option mark (`mark_src` not `chain`/`chain_near`).

## Conventions
- Validate JS before delivering: extract inline `<script>` to a temp file and
  run `node --check`.
- No browser storage APIs beyond what already exists; keep changes minimal.
- LEAPS "vs Owned" compares raw breakeven with a DTE-mismatch flag (⚠ ±Nmo DTE)
  when expiries differ >90 days — intentional, keep it.

## Full context
The complete system guide, trading philosophy, gotchas, and conventions live in
the scanner repo's `CLAUDE.md` (`eastbiz/whale-intelligence`). Read that for
anything beyond dashboard rendering.

## Deploy
Push `index.html`; changes are live on GitHub Pages after the next scan writes
fresh `results.json`.
