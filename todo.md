# StamfordBridge.v — Issues and Fixes

1. Rename `t_march_north_start`/`t_march_north_end` to distinguish the London→York march (multi-day) from the Tadcaster→Stamford Bridge final approach (morning of Sep 25). Model both as separate timeline fields.
2. Add the missing `MarchNorthBegins`/`MarchNorthEnds` events to `events_T_sep25`.
3. Guard `duration` with a wrapper or dependent type so it cannot be called with reversed arguments, or add a `duration_comm_absurd` lemma documenting the nat-subtraction hazard.
4. Reduce `english_force` total from 11,000 toward 7,000–8,000, or parameterize it with a range and prove results hold across the range.
5. Connect force composition (heavy/light/archers) to phase-specific combat effectiveness.
6. Wire casualty accumulation into force strength — casualties should reduce effective combat power per phase, not just accumulate independently.
7. Increase Norse casualty rates (especially Rout phase) so total losses reach ~80% of the force, matching historical accounts of 24 ships returning from ~300.
8. Make crossing rate degrade as defending force depletes — bridge bottleneck should respond to attrition.
9. Prove battle outcome (rout) follows from force ratio crossing a threshold, not just assert it via phase structure.
10. Feed post-battle effective strength into march south feasibility — a depleted army marches slower.
11. Model supply consumption as a function of force size and days elapsed, not just days available vs days needed.
12. Elevate `speed_11_insufficient` / `speed_12_sufficient` into named capstone theorems establishing the minimum feasible march rate for the Hastings window.
13. Replace the current trivial capstone theorems with tighter results (e.g., minimum speed bounds, maximum feasible recovery time at Stamford Bridge before the window closes).
14. Replace the NorthSea distance constant with per-location coastal distances that carry geographic meaning.
15. Add a comment or docstring flag to each phase timing marking it as a modern reconstruction, not a primary-source value.
16. Add terminal periods to all inline comments.
