# StamfordBridge.v — Issues and Fixes

1. Reduce `english_force` total from 11,000 toward 7,000–8,000, or parameterize it with a range and prove results hold across the range.
2. Connect force composition (heavy/light/archers) to phase-specific combat effectiveness.
3. Wire casualty accumulation into force strength — casualties should reduce effective combat power per phase, not just accumulate independently.
4. Increase Norse casualty rates (especially Rout phase) so total losses reach ~80% of the force, matching historical accounts of 24 ships returning from ~300.
5. Make crossing rate degrade as defending force depletes — bridge bottleneck should respond to attrition.
6. Prove battle outcome (rout) follows from force ratio crossing a threshold, not just assert it via phase structure.
7. Feed post-battle effective strength into march south feasibility — a depleted army marches slower.
8. Model supply consumption as a function of force size and days elapsed, not just days available vs days needed.
9. Elevate `speed_11_insufficient` / `speed_12_sufficient` into named capstone theorems establishing the minimum feasible march rate for the Hastings window.
10. Replace the current trivial capstone theorems with tighter results (e.g., minimum speed bounds, maximum feasible recovery time at Stamford Bridge before the window closes).
11. Parameterize phase start/end times with uncertainty ranges and prove results hold across them, analogous to the speed robustness proofs.
12. Add terminal periods to all inline comments.
13. Generalize `casualties_bounded_robust` and `norse_casualties_bounded_robust` to quantify over the casualty rate estimates as well as the population total. As written, the casualty side of the inequality is fixed at the chosen rates and only the unknown true population is varied.
14. Bind primary-source citations into the file as documentation tied to the constants they justify: Anglo-Saxon Chronicle MS D/E for 1066, Snorri Sturluson's *Heimskringla* (*Saga of Harald Sigurdsson*), John of Worcester, for distances, force sizes, casualty rates, and phase timings.
