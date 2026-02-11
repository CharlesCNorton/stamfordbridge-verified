# StamfordBridge.v — Issues and Fixes

1. Extend the calendar anchors to include Sep 16–24 (d_sep16 through d_sep24) so pre-battle events can be placed on their actual dates.
2. Move `t_landing` to ~Sep 15–18, `t_fulford` to Sep 20, `t_york_taken` to Sep 24, and `t_march_north_start` to ~Sep 16–19 in `T_sep25` and the `timeline` record.
3. Reverse the Hardrada death constraint: change `stamford_end_before_hardrada` to `hardrada_before_stamford_end : t_hardrada_fall T <= t_stamford_end T` and place `t_hardrada_fall` within the ShieldWall phase (~14:00–14:30).
4. Rename `t_march_north_start`/`t_march_north_end` to distinguish the London→York march (multi-day) from the Tadcaster→Stamford Bridge final approach (morning of Sep 25). Model both as separate timeline fields.
5. Reduce `english_force` total from 11,000 toward 7,000–8,000, or parameterize it with a range and prove results hold across the range.
6. Increase Norse casualty rates (especially Rout phase) so total losses reach ~80% of the force, matching historical accounts of 24 ships returning from ~300.
7. Add a comment or docstring flag to each phase timing marking it as a modern reconstruction, not a primary-source value.
8. Elevate `speed_11_insufficient` / `speed_12_sufficient` into named capstone theorems establishing the minimum feasible march rate for the Hastings window.
9. Replace the current trivial capstone theorems with tighter results (e.g., minimum speed bounds, maximum feasible recovery time at Stamford Bridge before the window closes).
10. Add the missing `dist` pairs (e.g., `London`↔`Hastings`, `London`↔`StamfordBridge`) so the lookup table covers all locations used in routes, instead of returning 0 silently.
11. Guard `duration` with a wrapper or dependent type so it cannot be called with reversed arguments, or add a `duration_comm_absurd` lemma documenting the nat-subtraction hazard.
12. Delete the double blank line at line 607.
13. Add terminal periods to all inline comments.
