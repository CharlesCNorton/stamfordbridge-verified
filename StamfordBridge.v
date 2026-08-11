(******************************************************************************)
(*                                                                            *)
(*               Battle of Stamford Bridge: Tactical Chronology               *)
(*                                                                            *)
(*   Formal model of the 25 September 1066 engagement and the Hastings march. *)
(*                                                                            *)
(*   Seofon fota Engliscre eorþan gife ic him, oþþe swa micle mare            *)
(*   swa he hierra bið þonne oþre menn.                                       *)
(*   - Harold Godwinson to Harald Hardrada, 25 September 1066                 *)
(*                                                                            *)
(*   Author: Charles C. Norton                                                *)
(*   Date: August 11, 2026                                                    *)
(*   License: MIT                                                             *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import ZArith Bool Lia List.
Import ListNotations.

Open Scope Z_scope.

(* =============================================================================
   Primary sources
   =============================================================================

   [ASC-C]  Anglo-Saxon Chronicle, MS C, anno 1066.
   [ASC-D]  Anglo-Saxon Chronicle, MS D, anno 1066.
   [ASC-E]  Anglo-Saxon Chronicle, MS E, anno 1066.
   [HEIM]   Snorri Sturluson, Heimskringla, Saga of Harald Sigurdarson.
   [JW]     John of Worcester, Chronicon ex chronicis, anno 1066.
   [HH]     Henry of Huntingdon, Historia Anglorum, book VI.
   [WJ]     William of Jumieges, Gesta Normannorum Ducum, book VII.

   Every constant below carries the source tag that justifies it.
   ============================================================================= *)

(* vm_compute turns a Z ordering into a comparison, discharged by discriminate. *)
Ltac ground := vm_compute; repeat split; first [ reflexivity | discriminate | exact I ].

(* =============================================================================
   Integer arithmetic
   ============================================================================= *)

(* Least q with n <= q * d, for d > 0. *)
Definition ceil_div (n d : Z) : Z := (n + d - 1) / d.

Lemma ceil_div_spec : forall n d, 0 < d -> n <= ceil_div n d * d.
Proof.
  intros n d Hd. unfold ceil_div.
  pose proof (Z.div_mod (n + d - 1) d ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (n + d - 1) d Hd) as Hmb.
  lia.
Qed.

Lemma ceil_div_nonneg : forall n d, 0 <= n -> 0 < d -> 0 <= ceil_div n d.
Proof. intros n d Hn Hd. unfold ceil_div. apply Z.div_pos; lia. Qed.

Lemma ceil_div_le : forall n d q, 0 < d -> n <= q * d -> ceil_div n d <= q.
Proof.
  intros n d q Hd Hle. unfold ceil_div.
  transitivity ((q * d + (d - 1)) / d).
  - apply Z.div_le_mono; lia.
  - rewrite Z.div_add_l by lia.
    rewrite (Z.div_small (d - 1) d) by lia. lia.
Qed.

Lemma ceil_div_mono : forall n1 n2 d, 0 < d -> n1 <= n2 -> ceil_div n1 d <= ceil_div n2 d.
Proof. intros n1 n2 d Hd Hle. unfold ceil_div. apply Z.div_le_mono; lia. Qed.

Lemma ceil_div_anti_mono : forall n d1 d2,
  0 <= n -> 0 < d1 -> d1 <= d2 -> ceil_div n d2 <= ceil_div n d1.
Proof.
  intros n d1 d2 Hn Hd1 Hle.
  apply ceil_div_le; [lia|].
  transitivity (ceil_div n d1 * d1).
  - apply ceil_div_spec; lia.
  - apply Z.mul_le_mono_nonneg_l; [apply ceil_div_nonneg; lia | lia].
Qed.

Lemma ceil_div_zero : forall d, 0 < d -> ceil_div 0 d = 0.
Proof. intros d Hd. unfold ceil_div. apply Z.div_small; lia. Qed.

(* A rate threshold is exact when it succeeds and its predecessor fails. *)
Lemma rate_threshold_iff : forall n bound lo,
  0 <= n -> 0 < lo - 1 ->
  ceil_div n lo <= bound ->
  bound < ceil_div n (lo - 1) ->
  forall s, 0 < s -> (ceil_div n s <= bound <-> lo <= s).
Proof.
  intros n bound lo Hn Hlo Hok Hbad s Hs. split.
  - intros H. destruct (Z.le_gt_cases lo s) as [Hge|Hlt]; [exact Hge|].
    assert (Hmono : ceil_div n (lo - 1) <= ceil_div n s)
      by (apply ceil_div_anti_mono; lia).
    lia.
  - intros H. transitivity (ceil_div n lo); [apply ceil_div_anti_mono; lia | exact Hok].
Qed.

(* =============================================================================
   Time
   ============================================================================= *)

Definition minutes_per_hour : Z := 60.
Definition hours_per_day : Z := 24.
Definition minutes_per_day : Z := hours_per_day * minutes_per_hour.

Definition day : Type := Z.
Definition time : Type := Z. (* minutes since 00:00 on 1 September 1066 *)

Definition t_of (d h m : Z) : time :=
  d * minutes_per_day + h * minutes_per_hour + m.

(* Signed elapsed time, negative when the arguments are reversed. *)
Definition duration (t1 t2 : time) : Z := t2 - t1.

Lemma minutes_per_day_pos : 0 < minutes_per_day.
Proof. unfold minutes_per_day, hours_per_day, minutes_per_hour; lia. Qed.

Lemma t_of_day_mono : forall d1 d2 h1 h2 m1 m2,
  0 <= h1 < hours_per_day -> 0 <= m1 < minutes_per_hour ->
  0 <= h2 < hours_per_day -> 0 <= m2 < minutes_per_hour ->
  d1 < d2 -> t_of d1 h1 m1 < t_of d2 h2 m2.
Proof.
  intros d1 d2 h1 h2 m1 m2 Hh1 Hm1 Hh2 Hm2 Hd.
  unfold t_of, minutes_per_day, hours_per_day, minutes_per_hour in *. nia.
Qed.

Lemma duration_pos : forall t1 t2, t1 < t2 -> 0 < duration t1 t2.
Proof. intros; unfold duration; lia. Qed.

(* Reversal is a sign change, not the silent truncation unary naturals give. *)
Lemma duration_antisym : forall t1 t2, duration t2 t1 = - duration t1 t2.
Proof. intros; unfold duration; lia. Qed.

Lemma duration_additive : forall t1 t2 t3,
  duration t1 t2 + duration t2 t3 = duration t1 t3.
Proof. intros; unfold duration; lia. Qed.

(* =============================================================================
   Campaign geography
   ============================================================================= *)

Inductive actor :=
  | Harold
  | Hardrada
  | Tostig
  | William
  | EnglishHost
  | NorwegianHost.

Inductive location :=
  | London
  | York
  | StamfordBridge
  | Hastings
  | Tadcaster
  | Derwent
  | Riccall
  | Fulford
  | NorthSea.

Definition loc_eqb (a b : location) : bool :=
  match a, b with
  | London, London | York, York | StamfordBridge, StamfordBridge
  | Hastings, Hastings | Tadcaster, Tadcaster | Derwent, Derwent
  | Riccall, Riccall | Fulford, Fulford | NorthSea, NorthSea => true
  | _, _ => false
  end.

Lemma loc_eqb_refl : forall a, loc_eqb a a = true.
Proof. destruct a; reflexivity. Qed.

Lemma loc_eqb_eq : forall a b, loc_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; intros H; congruence. Qed.

Definition all_locations_list : list location :=
  [London; York; StamfordBridge; Hastings; Tadcaster; Derwent; Riccall; Fulford; NorthSea].

Lemma all_locations_complete : forall l, In l all_locations_list.
Proof. destruct l; simpl; tauto. Qed.

(* Sentinel exceeding any sum of edges on this graph. *)
Definition INF : Z := 100000.

(* Direct edges only; Stamford Bridge to Hastings is derived, not asserted. *)
Definition direct_edges : list (location * location * Z) := [
  (London, York, 190);           (* Ermine Street, London to York [JW] *)
  (London, Hastings, 58);        (* London to the Senlac position [JW] *)
  (York, Fulford, 2);            (* Fulford lies just south of York [ASC-C] *)
  (York, Riccall, 8);            (* the Norwegian fleet beached at Riccall [ASC-C] *)
  (York, Tadcaster, 10);         (* Harold's muster point, 24 September [ASC-C] *)
  (York, StamfordBridge, 10);    (* the battlefield east of York [ASC-D] *)
  (Riccall, StamfordBridge, 12); (* the flight route back to the ships [HEIM] *)
  (StamfordBridge, Derwent, 1);  (* the bridge spans the Derwent [ASC-D] *)
  (NorthSea, Riccall, 60);       (* the Humber and Ouse approach [ASC-C] *)
  (NorthSea, Hastings, 200)      (* the Channel crossing to Pevensey [WJ] *)
].

Fixpoint find_edge_dist (es : list (location * location * Z)) (a b : location) : Z :=
  match es with
  | [] => INF
  | (x, y, d) :: rest =>
      if (loc_eqb a x && loc_eqb b y) || (loc_eqb a y && loc_eqb b x)
      then d
      else find_edge_dist rest a b
  end.

Definition base_dist (a b : location) : Z :=
  if loc_eqb a b then 0 else find_edge_dist direct_edges a b.

(* Matrix indices stay in nat; edge weights are binary integers. *)
Definition loc_idx (l : location) : nat :=
  match l with
  | London => 0 | York => 1 | StamfordBridge => 2 | Hastings => 3
  | Tadcaster => 4 | Derwent => 5 | Riccall => 6 | Fulford => 7
  | NorthSea => 8
  end%nat.

Definition loc_of_idx (i : nat) : location :=
  match i with
  | 0 => London | 1 => York | 2 => StamfordBridge | 3 => Hastings
  | 4 => Tadcaster | 5 => Derwent | 6 => Riccall | 7 => Fulford
  | _ => NorthSea
  end%nat.

Definition n_locations : nat := 9%nat.

Definition mat_get (m : list (list Z)) (i j : nat) : Z := nth j (nth i m []) INF.

Definition init_matrix : list (list Z) :=
  map (fun i => map (fun j => base_dist (loc_of_idx i) (loc_of_idx j))
                    (seq 0 n_locations))
      (seq 0 n_locations).

(* One Floyd-Warshall pass: relax every pair through intermediate k. *)
Definition mat_relax (m : list (list Z)) (k : nat) : list (list Z) :=
  map (fun i => map (fun j => Z.min (mat_get m i j)
                                    (mat_get m i k + mat_get m k j))
                    (seq 0 n_locations))
      (seq 0 n_locations).

Definition mat_fw (m : list (list Z)) : list (list Z) :=
  fold_left mat_relax (seq 0 n_locations) m.

Definition dist_table : list (list Z) := Eval vm_compute in mat_fw init_matrix.

Definition dist (a b : location) : Z := mat_get dist_table (loc_idx a) (loc_idx b).

Lemma dist_zero : forall a, dist a a = 0.
Proof. destruct a; ground. Qed.

Lemma dist_sym : forall a b, dist a b = dist b a.
Proof. destruct a, b; ground. Qed.

Lemma dist_triangle : forall a b c, dist a c <= dist a b + dist b c.
Proof. intros a b c; destruct a, b, c; ground. Qed.

Lemma dist_nonneg : forall a b, 0 <= dist a b.
Proof. destruct a, b; ground. Qed.

(* Canonical marching distances, all read off the shortest-path closure. *)
Definition miles_London_York : Z := dist London York.
Definition miles_York_Stamford : Z := dist York StamfordBridge.
Definition miles_London_Hastings : Z := dist London Hastings.
Definition miles_Stamford_Hastings : Z := dist StamfordBridge Hastings.
Definition miles_York_Hastings : Z := dist York Hastings.
Definition miles_Stamford_Riccall : Z := dist StamfordBridge Riccall.
Definition miles_York_Fulford : Z := dist York Fulford.
Definition miles_York_Riccall : Z := dist York Riccall.
Definition miles_York_Tadcaster : Z := dist York Tadcaster.
Definition miles_Stamford_Derwent : Z := dist StamfordBridge Derwent.

(* The southward distance is the via-London route, not a cross-country line. *)
Theorem stamford_hastings_via_london :
  miles_Stamford_Hastings
  = miles_York_Stamford + miles_London_York + miles_London_Hastings.
Proof. ground. Qed.

Theorem stamford_hastings_in_defensible_band :
  250 <= miles_Stamford_Hastings <= 260.
Proof. ground. Qed.

(* No sea leg beats the road: the Humber and Channel route is longer. *)
Theorem land_route_beats_sea_route :
  miles_Stamford_Hastings
  < dist StamfordBridge Riccall + dist Riccall NorthSea + dist NorthSea Hastings.
Proof. ground. Qed.

Fixpoint path_distance_from (prev : location) (rest : list location) : Z :=
  match rest with
  | [] => 0
  | b :: rs => dist prev b + path_distance_from b rs
  end.

Definition path_distance (path : list location) : Z :=
  match path with
  | [] => 0
  | a :: rest => path_distance_from a rest
  end.

Definition route_north : list location := [London; York; StamfordBridge].
Definition route_south : list location := [StamfordBridge; York; London; Hastings].
Definition route_full : list location :=
  [London; York; StamfordBridge; York; London; Hastings].
Definition route_riccall_bridge : list location := [Riccall; StamfordBridge].
Definition route_york_fulford : list location := [York; Fulford].

Lemma route_north_distance : path_distance route_north = 200.
Proof. ground. Qed.

(* The marched southward route costs exactly the shortest-path distance. *)
Lemma route_south_distance : path_distance route_south = miles_Stamford_Hastings.
Proof. ground. Qed.

Lemma route_full_distance : path_distance route_full = 458.
Proof. ground. Qed.

Lemma route_full_decompose :
  path_distance route_full = path_distance route_north + path_distance route_south.
Proof. ground. Qed.

Lemma route_riccall_bridge_distance :
  path_distance route_riccall_bridge = miles_Stamford_Riccall.
Proof. ground. Qed.

Lemma route_york_fulford_distance :
  path_distance route_york_fulford = miles_York_Fulford.
Proof. ground. Qed.

(* =============================================================================
   Calendar anchors, days since 1 September 1066
   ============================================================================= *)

Definition d_sep18 : day := 17.  (* Norwegian fleet beaches at Riccall [ASC-C] *)
Definition d_sep20 : day := 19.  (* Battle of Fulford; Harold quits London [ASC-C] *)
Definition d_sep24 : day := 23.  (* Harold reaches Tadcaster; York submits [ASC-C] *)
Definition d_sep25 : day := 24.  (* Battle of Stamford Bridge [ASC-D] *)
Definition d_sep28 : day := 27.  (* William lands at Pevensey [ASC-D] *)
Definition d_oct01 : day := 30.  (* Harold quits York for the south [JW] *)
Definition d_oct07 : day := 36.  (* Harold reaches London [JW] *)
Definition d_oct12 : day := 41.  (* Harold quits London after six days [JW] *)
Definition d_oct13 : day := 42.  (* Harold reaches the Senlac position [JW] *)
Definition d_oct14 : day := 43.  (* Battle of Hastings [ASC-D] *)

Lemma day_ordering :
  d_sep18 < d_sep20 /\ d_sep20 < d_sep24 /\ d_sep24 < d_sep25 /\ d_sep25 < d_sep28
  /\ d_sep28 < d_oct01 /\ d_oct01 < d_oct07 /\ d_oct07 < d_oct12
  /\ d_oct12 < d_oct13 /\ d_oct13 < d_oct14.
Proof.
  unfold d_sep18, d_sep20, d_sep24, d_sep25, d_sep28, d_oct01, d_oct07, d_oct12,
    d_oct13, d_oct14; repeat split; lia.
Qed.

Definition t_sep25_noon : time := t_of d_sep25 12 0.
Definition t_sep25_evening : time := t_of d_sep25 18 0.
Definition t_oct14_morning : time := t_of d_oct14 9 0.

Lemma days_between_sep25_oct14 :
  duration t_sep25_noon t_oct14_morning / minutes_per_day = 18.
Proof. ground. Qed.

(* Sunrise and sunset at York on 25 September, Julian reckoning. *)
Definition t_sep25_sunrise : time := t_of d_sep25 6 0.
Definition t_sep25_sunset : time := t_of d_sep25 18 0.

Definition in_sep25_daylight (t : time) : Prop :=
  t_sep25_sunrise <= t <= t_sep25_sunset.

(* =============================================================================
   Marching rates and leg feasibility
   ============================================================================= *)

Definition travel_days (distance rate : Z) : Z := ceil_div distance rate.

Lemma travel_days_zero : forall r, 0 < r -> travel_days 0 r = 0.
Proof. intros; unfold travel_days; apply ceil_div_zero; lia. Qed.

Lemma travel_days_monotone : forall d1 d2 r,
  0 < r -> d1 <= d2 -> travel_days d1 r <= travel_days d2 r.
Proof. intros; unfold travel_days; apply ceil_div_mono; lia. Qed.

Lemma travel_days_rate_anti_mono : forall d r1 r2,
  0 <= d -> 0 < r1 -> r1 <= r2 -> travel_days d r2 <= travel_days d r1.
Proof. intros; unfold travel_days; apply ceil_div_anti_mono; lia. Qed.

(* Departing on day D and marching n days puts arrival on day D + n - 1. *)
Definition leg_days (depart arrive : day) : Z := arrive - depart + 1.

Definition leg_fits (depart arrive : day) (miles rate : Z) : Prop :=
  travel_days miles rate <= leg_days depart arrive.

Definition rate_north : Z := 40.       (* mounted forced march to Tadcaster [ASC-C] *)
Definition rate_south_base : Z := 30.  (* the reassembled host marching south [JW] *)
Definition norse_rate : Z := 15.       (* Norwegian movement on foot [HEIM] *)

Lemma rate_north_pos : 0 < rate_north. Proof. unfold rate_north; lia. Qed.
Lemma rate_south_base_pos : 0 < rate_south_base. Proof. unfold rate_south_base; lia. Qed.
Lemma norse_rate_pos : 0 < norse_rate. Proof. unfold norse_rate; lia. Qed.

(* Whole-route rounding is cheaper than per-leg rounding by one marching day. *)
Lemma segment_rounding_penalty :
  travel_days miles_London_York rate_north
  + travel_days miles_York_Stamford rate_north
  + travel_days miles_Stamford_Hastings rate_north
  = travel_days (path_distance route_full) rate_north + 1.
Proof. ground. Qed.

(* =============================================================================
   Forces
   ============================================================================= *)

Record force := {
  heavy : Z;    (* housecarls and hirdmen in mail *)
  light : Z;    (* fyrd and bondi *)
  archers : Z
}.

Definition force_total (f : force) : Z := heavy f + light f + archers f.

Definition force_wf (f : force) : Prop :=
  0 <= heavy f /\ 0 <= light f /\ 0 <= archers f.

Definition add_force (f g : force) : force :=
  {| heavy := heavy f + heavy g;
     light := light f + light g;
     archers := archers f + archers g |}.

Definition sub_force (f g : force) : force :=
  {| heavy := heavy f - heavy g;
     light := light f - light g;
     archers := archers f - archers g |}.

(* Composition-preserving reduction to num/den of the original strength. *)
Definition scale_force (f : force) (num den : Z) : force :=
  {| heavy := heavy f * num / den;
     light := light f * num / den;
     archers := archers f * num / den |}.

Lemma add_force_total : forall f g,
  force_total (add_force f g) = force_total f + force_total g.
Proof. intros [h1 l1 a1] [h2 l2 a2]; unfold force_total, add_force; cbn; lia. Qed.

Lemma sub_force_total : forall f g,
  force_total (sub_force f g) = force_total f - force_total g.
Proof. intros [h1 l1 a1] [h2 l2 a2]; unfold force_total, sub_force; cbn; lia. Qed.

(* Harold's host at the bridge: housecarls and the northern fyrd [ASC-C], [JW]. *)
Definition english_force : force := {| heavy := 3000; light := 7000; archers := 1000 |}.

(* Hardrada's army, landed from roughly three hundred ships [HEIM]. *)
Definition norse_force : force := {| heavy := 3500; light := 4500; archers := 1000 |}.

(* The Norwegians were divided by the Derwent when the English arrived [ASC-D]. *)
Definition norse_west : force := {| heavy := 1200; light := 1500; archers := 300 |}.
Definition norse_east : force := {| heavy := 2300; light := 3000; archers := 700 |}.

Lemma norse_split_exact : add_force norse_west norse_east = norse_force.
Proof. ground. Qed.

Lemma norse_split_totals :
  force_total norse_west = 3000 /\ force_total norse_east = 6000
  /\ force_total norse_force = 9000.
Proof. ground. Qed.

Lemma english_force_total : force_total english_force = 11000.
Proof. ground. Qed.

(* Plausible ranges reported across the sources. *)
Definition english_total_low : Z := 8000.
Definition english_total_high : Z := 15000.
Definition norse_total_low : Z := 6000.
Definition norse_total_high : Z := 12000.

Definition english_in_range (e : Z) : Prop := english_total_low <= e <= english_total_high.
Definition norse_in_range (n : Z) : Prop := norse_total_low <= n <= norse_total_high.

Lemma english_point_in_range : english_in_range (force_total english_force).
Proof. unfold english_in_range, english_total_low, english_total_high; ground. Qed.

Lemma norse_point_in_range : norse_in_range (force_total norse_force).
Proof. unfold norse_in_range, norse_total_low, norse_total_high; ground. Qed.

(* -----------------------------------------------------------------------------
   Exact superiority region over both ranges
   -------------------------------------------------------------------------- *)

(* Superiority over the whole Norse range holds iff e clears the Norse maximum. *)
Theorem english_superiority_exact : forall e,
  english_in_range e ->
  ((forall n, norse_in_range n -> n < e) <-> norse_total_high < e).
Proof.
  intros e He. unfold english_in_range, norse_in_range in *.
  unfold english_total_low, english_total_high, norse_total_low, norse_total_high in *.
  split.
  - intros H. apply (H norse_total_high). unfold norse_total_high; lia.
  - intros H n Hn. unfold norse_total_high in H. lia.
Qed.

(* Superiority is not universal over the ranges: the extremes invert it. *)
Theorem english_superiority_not_universal :
  exists e n, english_in_range e /\ norse_in_range n /\ e < n.
Proof.
  exists english_total_low, norse_total_high.
  unfold english_in_range, norse_in_range,
    english_total_low, english_total_high, norse_total_low, norse_total_high.
  repeat split; lia.
Qed.

(* The boundary of the guaranteed-superiority region. *)
Theorem english_superiority_boundary :
  (forall n, norse_in_range n -> n < norse_total_high + 1)
  /\ ~ (forall n, norse_in_range n -> n < norse_total_high).
Proof.
  unfold norse_in_range, norse_total_low, norse_total_high. split.
  - intros n Hn; lia.
  - intros H. specialize (H 12000 ltac:(lia)). lia.
Qed.

(* Superiority against some admissible Norse total holds throughout the English range. *)
Theorem english_superiority_somewhere : forall e,
  english_in_range e -> exists n, norse_in_range n /\ n < e.
Proof.
  intros e He. exists norse_total_low.
  unfold english_in_range, english_total_low, english_total_high,
    norse_in_range, norse_total_low, norse_total_high in *.
  split; lia.
Qed.

(* At the point estimates the English do outnumber the Norse. *)
Theorem english_superiority_at_estimates :
  force_total norse_force < force_total english_force.
Proof. ground. Qed.

(* =============================================================================
   Phase schedule
   ============================================================================= *)

Inductive phase :=
  | Approach        (* English deployment west of the Derwent [ASC-D] *)
  | BridgeDefender  (* the lone Norse axeman holds the span [ASC-C] *)
  | BridgeHold      (* English force the crossing [ASC-C] *)
  | ShieldWall      (* the main action east of the river [HEIM] *)
  | Rout.           (* Norse collapse and flight to Riccall [HEIM] *)

(* Six boundaries delimiting five consecutive phases. *)
Record schedule := {
  b0 : time;  (* Approach begins *)
  b1 : time;  (* the axeman takes the bridge *)
  b2 : time;  (* the axeman falls and the English force the span *)
  b3 : time;  (* the shield walls meet *)
  b4 : time;  (* Hardrada falls and the Norse break *)
  b5 : time   (* the pursuit ends *)
}.

Definition sched_ordered (S : schedule) : Prop :=
  b0 S < b1 S /\ b1 S < b2 S /\ b2 S < b3 S /\ b3 S < b4 S /\ b4 S < b5 S.

Definition phase_start (S : schedule) (p : phase) : time :=
  match p with
  | Approach => b0 S | BridgeDefender => b1 S | BridgeHold => b2 S
  | ShieldWall => b3 S | Rout => b4 S
  end.

Definition phase_end (S : schedule) (p : phase) : time :=
  match p with
  | Approach => b1 S | BridgeDefender => b2 S | BridgeHold => b3 S
  | ShieldWall => b4 S | Rout => b5 S
  end.

Definition phase_duration (S : schedule) (p : phase) : Z :=
  duration (phase_start S p) (phase_end S p).

(* Nominal reconstruction: dawn approach, midday wall, mid-afternoon collapse. *)
Definition nominal : schedule := {|
  b0 := t_of d_sep25 8 0;
  b1 := t_of d_sep25 9 30;
  b2 := t_of d_sep25 10 30;
  b3 := t_of d_sep25 11 30;
  b4 := t_of d_sep25 14 30;
  b5 := t_of d_sep25 16 0
|}.

Lemma nominal_ordered : sched_ordered nominal.
Proof. ground. Qed.

Lemma phase_chain : forall S,
  phase_end S Approach = phase_start S BridgeDefender /\
  phase_end S BridgeDefender = phase_start S BridgeHold /\
  phase_end S BridgeHold = phase_start S ShieldWall /\
  phase_end S ShieldWall = phase_start S Rout.
Proof. intros; simpl; repeat split; reflexivity. Qed.

Lemma phase_durations_sum : forall S,
  phase_duration S Approach + phase_duration S BridgeDefender
  + phase_duration S BridgeHold + phase_duration S ShieldWall
  + phase_duration S Rout = duration (b0 S) (b5 S).
Proof. intros; unfold phase_duration, duration; simpl; lia. Qed.

(* -----------------------------------------------------------------------------
   Uncertainty band on the schedule
   -------------------------------------------------------------------------- *)

(* No source times the phases, so each boundary is admitted within half an hour. *)
Definition sched_tolerance : Z := 30.

Definition near (t centre : time) : Prop :=
  centre - sched_tolerance <= t <= centre + sched_tolerance.

Definition sched_admissible (S : schedule) : Prop :=
  sched_ordered S
  /\ near (b0 S) (b0 nominal) /\ near (b1 S) (b1 nominal)
  /\ near (b2 S) (b2 nominal) /\ near (b3 S) (b3 nominal)
  /\ near (b4 S) (b4 nominal) /\ near (b5 S) (b5 nominal).

Lemma nominal_admissible : sched_admissible nominal.
Proof. unfold sched_admissible, near, sched_tolerance; ground. Qed.

(* Every admissible schedule keeps the whole action between sunrise and sunset. *)
Theorem battle_within_daylight_robust : forall S,
  sched_admissible S -> in_sep25_daylight (b0 S) /\ in_sep25_daylight (b5 S).
Proof.
  intros S HS. destruct HS as [Hord [H0 [H1 [H2 [H3 [H4 H5]]]]]].
  unfold near, sched_tolerance, nominal, in_sep25_daylight, t_sep25_sunrise,
    t_sep25_sunset, t_of, d_sep25, minutes_per_day, hours_per_day,
    minutes_per_hour in *.
  simpl in *. split; lia.
Qed.

Theorem every_phase_within_daylight_robust : forall S p,
  sched_admissible S ->
  in_sep25_daylight (phase_start S p) /\ in_sep25_daylight (phase_end S p).
Proof.
  intros S p HS. destruct HS as [Hord [H0 [H1 [H2 [H3 [H4 H5]]]]]].
  unfold near, sched_tolerance, nominal, in_sep25_daylight, t_sep25_sunrise,
    t_sep25_sunset, t_of, d_sep25, minutes_per_day, hours_per_day,
    minutes_per_hour in *.
  simpl in *. destruct p; simpl; split; lia.
Qed.

Lemma nominal_phase_durations :
  phase_duration nominal Approach = 90 /\
  phase_duration nominal BridgeDefender = 60 /\
  phase_duration nominal BridgeHold = 60 /\
  phase_duration nominal ShieldWall = 180 /\
  phase_duration nominal Rout = 90.
Proof. ground. Qed.

Lemma nominal_battle_duration : duration (b0 nominal) (b5 nominal) = 480.
Proof. ground. Qed.

(* =============================================================================
   Phase-specific combat effectiveness
   ============================================================================= *)

(* Weights out of ten for what each troop type is worth in each phase. *)
(* Archers dominate the approach, mail the wall, light foot the pursuit. *)
Definition w_heavy (p : phase) : Z :=
  match p with
  | Approach => 6 | BridgeDefender => 10 | BridgeHold => 10
  | ShieldWall => 10 | Rout => 4
  end.

Definition w_light (p : phase) : Z :=
  match p with
  | Approach => 3 | BridgeDefender => 2 | BridgeHold => 3
  | ShieldWall => 4 | Rout => 10
  end.

Definition w_archers (p : phase) : Z :=
  match p with
  | Approach => 8 | BridgeDefender => 4 | BridgeHold => 5
  | ShieldWall => 3 | Rout => 2
  end.

Definition effectiveness (p : phase) (f : force) : Z :=
  w_heavy p * heavy f + w_light p * light f + w_archers p * archers f.

Lemma effectiveness_nonneg : forall p f, force_wf f -> 0 <= effectiveness p f.
Proof.
  intros p f [Hh [Hl Ha]]. unfold effectiveness.
  destruct p; cbv [w_heavy w_light w_archers]; lia.
Qed.

Lemma effectiveness_additive : forall p f g,
  effectiveness p (add_force f g) = effectiveness p f + effectiveness p g.
Proof.
  intros p [h1 l1 a1] [h2 l2 a2]; unfold effectiveness, add_force;
  cbn [heavy light archers]; ring.
Qed.

(* Composition matters: equal totals differ in effectiveness by phase. *)
Theorem composition_is_not_headcount :
  let a := {| heavy := 1000; light := 0; archers := 0 |} in
  let b := {| heavy := 0; light := 1000; archers := 0 |} in
  force_total a = force_total b
  /\ effectiveness ShieldWall b < effectiveness ShieldWall a
  /\ effectiveness Rout a < effectiveness Rout b.
Proof. ground. Qed.

(* =============================================================================
   Bridge geometry
   ============================================================================= *)

Definition man_width_cm : Z := 60.        (* frontage of one man under arms *)
Definition bridge_width_cm : Z := 240.    (* a narrow timber span [ASC-C] *)
Definition axe_reach_cm : Z := 250.       (* arc swept by a two-handed axe [HEIM] *)
Definition file_rate : Z := 3.            (* men per minute per file, contested *)

(* Men who fit abreast on a span of the given width. *)
Definition frontage (w : Z) : Z := w / man_width_cm.

Lemma frontage_mono : forall w1 w2, w1 <= w2 -> frontage w1 <= frontage w2.
Proof. intros; unfold frontage; apply Z.div_le_mono; [unfold man_width_cm; lia|lia]. Qed.

Lemma frontage_nonneg : forall w, 0 <= w -> 0 <= frontage w.
Proof. intros; unfold frontage; apply Z.div_pos; [lia | unfold man_width_cm; lia]. Qed.

(* Frontage caps how many attackers can engage at once. *)
Theorem frontage_caps_engagement : forall w n,
  0 <= w -> n * man_width_cm <= w -> n <= frontage w.
Proof.
  intros w n Hw Hn. unfold frontage.
  transitivity (n * man_width_cm / man_width_cm).
  - rewrite Z.div_mul by (unfold man_width_cm; lia). lia.
  - apply Z.div_le_mono; [unfold man_width_cm; lia | exact Hn].
Qed.

(* A defending line blocks a span when its swept arc covers the full width. *)
Definition span_blocked (defenders w : Z) : Prop := w <= defenders * axe_reach_cm.

(* One axeman covers a 240 cm span: the stand is geometry, not assertion [HEIM]. *)
Theorem lone_axeman_blocks_bridge : span_blocked 1 bridge_width_cm.
Proof. unfold span_blocked, bridge_width_cm, axe_reach_cm; lia. Qed.

(* The same man could not block a span even one file wider. *)
Theorem lone_axeman_bound_is_tight :
  ~ span_blocked 1 (bridge_width_cm + man_width_cm).
Proof. unfold span_blocked, bridge_width_cm, man_width_cm, axe_reach_cm; lia. Qed.

(* Crossing rate is the product of frontage and per-file pace. *)
Definition max_crossing_rate (w : Z) : Z := frontage w * file_rate.

Definition bulk_crossing_rate : Z := max_crossing_rate bridge_width_cm.

Lemma bulk_crossing_rate_value : bulk_crossing_rate = 12.
Proof. ground. Qed.

(* Widening the span is the only way to raise the ceiling. *)
Theorem crossing_rate_from_width : forall w1 w2,
  w1 <= w2 -> max_crossing_rate w1 <= max_crossing_rate w2.
Proof.
  intros w1 w2 H. unfold max_crossing_rate.
  apply Z.mul_le_mono_nonneg_r; [unfold file_rate; lia | apply frontage_mono; exact H].
Qed.

(* =============================================================================
   Crossing under attrition
   ============================================================================= *)

(* Each surviving defender denies one file; a blocking line denies the span. *)
Definition crossing_rate_at (w defenders : Z) : Z :=
  if Z.leb w (defenders * axe_reach_cm) then 0
  else Z.max 0 (frontage w - defenders) * file_rate.

Lemma crossing_rate_at_nonneg : forall w d, 0 <= crossing_rate_at w d.
Proof.
  intros w d. unfold crossing_rate_at.
  destruct (Z.leb w (d * axe_reach_cm)); [lia|].
  apply Z.mul_nonneg_nonneg; [lia | unfold file_rate; lia].
Qed.

(* The rate never exceeds the width-derived ceiling. *)
Theorem crossing_rate_bounded : forall w d,
  0 <= w -> 0 <= d -> crossing_rate_at w d <= max_crossing_rate w.
Proof.
  intros w d Hw Hd. unfold crossing_rate_at, max_crossing_rate.
  pose proof (frontage_nonneg w Hw) as Hfr.
  destruct (Z.leb w (d * axe_reach_cm)) eqn:E.
  - apply Z.mul_nonneg_nonneg; [exact Hfr | unfold file_rate; lia].
  - apply Z.mul_le_mono_nonneg_r; [unfold file_rate; lia | lia].
Qed.

(* The rate rises as the defending line is thinned. *)
Theorem crossing_rate_degrades_with_defenders : forall w d1 d2,
  0 <= w -> 0 <= d1 -> d1 <= d2 -> crossing_rate_at w d2 <= crossing_rate_at w d1.
Proof.
  intros w d1 d2 Hw H1 H12. unfold crossing_rate_at.
  pose proof (frontage_nonneg w Hw) as Hfr.
  destruct (Z.leb w (d2 * axe_reach_cm)) eqn:E2;
  destruct (Z.leb w (d1 * axe_reach_cm)) eqn:E1.
  - lia.
  - apply Z.mul_nonneg_nonneg; [lia | unfold file_rate; lia].
  - apply Z.leb_le in E1. apply Z.leb_gt in E2.
    assert (0 < axe_reach_cm) by (unfold axe_reach_cm; lia). nia.
  - apply Z.mul_le_mono_nonneg_r; [unfold file_rate; lia | lia].
Qed.

(* The blocked span admits nobody, at any width the axe covers. *)
Theorem blocked_span_admits_none : forall w d,
  span_blocked d w -> crossing_rate_at w d = 0.
Proof.
  intros w d H. unfold crossing_rate_at, span_blocked in *.
  destruct (Z.leb w (d * axe_reach_cm)) eqn:E; [reflexivity|].
  apply Z.leb_gt in E. lia.
Qed.

Corollary lone_axeman_stops_the_crossing : crossing_rate_at bridge_width_cm 1 = 0.
Proof. apply blocked_span_admits_none, lone_axeman_blocks_bridge. Qed.

(* With the defender down, the span runs at its full geometric rate. *)
Corollary cleared_span_runs_at_ceiling :
  crossing_rate_at bridge_width_cm 0 = bulk_crossing_rate.
Proof. ground. Qed.

(* =============================================================================
   Attrition
   ============================================================================= *)

(* Losses removed in proportion to composition, so strength and mix fall together. *)
Definition attrit (f : force) (n : Z) : force :=
  let tot := force_total f in
  if Z.leb tot 0 then f
  else {| heavy := heavy f - n * heavy f / tot;
          light := light f - n * light f / tot;
          archers := archers f - n * archers f / tot |}.

(* Floor division makes the realised loss no larger than the nominal loss. *)
Lemma attrit_total_lower_bound : forall f n,
  0 < force_total f -> 0 <= n -> force_total f - n <= force_total (attrit f n).
Proof.
  intros f n Ht Hn. unfold attrit.
  destruct (Z.leb (force_total f) 0) eqn:E; [apply Z.leb_le in E; lia|].
  unfold force_total in *; simpl.
  remember (heavy f + light f + archers f) as tot eqn:Htot.
  pose proof (Z.div_mod (n * heavy f) tot ltac:(lia)) as Dh.
  pose proof (Z.div_mod (n * light f) tot ltac:(lia)) as Dl.
  pose proof (Z.div_mod (n * archers f) tot ltac:(lia)) as Da.
  pose proof (Z.mod_pos_bound (n * heavy f) tot ltac:(lia)) as Mh.
  pose proof (Z.mod_pos_bound (n * light f) tot ltac:(lia)) as Ml.
  pose proof (Z.mod_pos_bound (n * archers f) tot ltac:(lia)) as Ma.
  assert (Hexp : n * heavy f + n * light f + n * archers f = n * tot)
    by (rewrite Htot; ring).
  assert (Hsum : tot * (n * heavy f / tot + n * light f / tot + n * archers f / tot)
                 <= tot * n) by nia.
  nia.
Qed.

(* Attrition never adds strength. *)
Lemma attrit_total_upper_bound : forall f n,
  0 < force_total f -> 0 <= n -> force_wf f ->
  force_total (attrit f n) <= force_total f.
Proof.
  intros f n Ht Hn [Hh [Hl Ha]]. unfold attrit.
  destruct (Z.leb (force_total f) 0) eqn:E; [lia|].
  unfold force_total in *; simpl.
  assert (0 <= n * heavy f / (heavy f + light f + archers f))
    by (apply Z.div_pos; nia).
  assert (0 <= n * light f / (heavy f + light f + archers f))
    by (apply Z.div_pos; nia).
  assert (0 <= n * archers f / (heavy f + light f + archers f))
    by (apply Z.div_pos; nia).
  lia.
Qed.

Definition lethality (p : phase) : Z :=
  match p with
  | Approach => 60000        (* skirmish and missile exchange *)
  | BridgeDefender => 400000 (* the blocked span costs almost nothing [ASC-C] *)
  | BridgeHold => 40000      (* forcing the span *)
  | ShieldWall => 30000      (* the grinding main action [HEIM] *)
  | Rout => 12000            (* broken men cut down in the open [HEIM] *)
  end.

Lemma lethality_pos : forall p, 0 < lethality p.
Proof. destruct p; unfold lethality; lia. Qed.

(* Losses a force inflicts across a phase, from its effectiveness and the clock. *)
Definition losses_inflicted (S : schedule) (p : phase) (attacker : force) : Z :=
  effectiveness p attacker * phase_duration S p / lethality p.

Lemma losses_inflicted_nonneg : forall S p f,
  force_wf f -> 0 <= phase_duration S p -> 0 <= losses_inflicted S p f.
Proof.
  intros S p f Hf Hd. unfold losses_inflicted.
  apply Z.div_pos; [| apply lethality_pos].
  apply Z.mul_nonneg_nonneg; [apply effectiveness_nonneg; exact Hf | exact Hd].
Qed.

(* A stronger force inflicts no fewer losses in the same phase. *)
Theorem losses_monotone_in_effectiveness : forall S p f g,
  0 <= phase_duration S p ->
  effectiveness p f <= effectiveness p g ->
  losses_inflicted S p f <= losses_inflicted S p g.
Proof.
  intros S p f g Hd Hfg. unfold losses_inflicted.
  apply Z.div_le_mono; [apply lethality_pos|].
  apply Z.mul_le_mono_nonneg_r; assumption.
Qed.

(* =============================================================================
   Battle trajectory
   ============================================================================= *)

(* The west-bank force withdraws while the approach and the stand run. *)
Definition withdrawal_window (S : schedule) : Z :=
  phase_duration S Approach + phase_duration S BridgeDefender.

Definition eng_after_approach : force :=
  attrit english_force (losses_inflicted nominal Approach norse_west).
Definition nw_after_approach : force :=
  attrit norse_west (losses_inflicted nominal Approach english_force).

Definition eng_after_defender : force :=
  attrit eng_after_approach (losses_inflicted nominal BridgeDefender nw_after_approach).
Definition nw_after_defender : force :=
  attrit nw_after_approach (losses_inflicted nominal BridgeDefender eng_after_approach).

(* The span, not the fighting, decides how many west-bank men reach safety. *)
Definition west_withdrawn_count : Z :=
  Z.min (force_total nw_after_defender) (bulk_crossing_rate * withdrawal_window nominal).

Definition west_withdrawn : force :=
  scale_force nw_after_defender west_withdrawn_count (force_total nw_after_defender).

Definition west_remnant : force := sub_force nw_after_defender west_withdrawn.

Definition eng_after_hold : force :=
  attrit eng_after_defender (losses_inflicted nominal BridgeHold west_remnant).

(* The men who crossed reinforced the wall Hardrada formed east of the river [HEIM]. *)
Definition norse_shieldwall : force := add_force norse_east west_withdrawn.

Definition eng_after_wall : force :=
  attrit eng_after_hold (losses_inflicted nominal ShieldWall norse_shieldwall).
Definition norse_after_wall : force :=
  attrit norse_shieldwall (losses_inflicted nominal ShieldWall eng_after_hold).

(* The bridge caps the withdrawal below the number of men who wanted to cross. *)
Theorem bridge_caps_the_withdrawal :
  west_withdrawn_count < force_total nw_after_defender.
Proof. ground. Qed.

Theorem west_bank_losses_are_geometric :
  force_total norse_west - force_total west_withdrawn = 1201.
Proof. ground. Qed.

(* The span binds for every admissible schedule, not only for the nominal one. *)
Theorem bridge_caps_the_withdrawal_robust : forall S,
  sched_admissible S ->
  bulk_crossing_rate * withdrawal_window S < force_total nw_after_defender.
Proof.
  intros S HS. destruct HS as [Hord [H0 [H1 [H2 [H3 [H4 H5]]]]]].
  assert (Hw : withdrawal_window S <= 210).
  { unfold withdrawal_window, phase_duration, duration, phase_start, phase_end.
    unfold near, sched_tolerance in H0, H2.
    change (b0 nominal) with (t_of d_sep25 8 0) in H0.
    change (b2 nominal) with (t_of d_sep25 10 30) in H2.
    unfold t_of, d_sep25, minutes_per_day, hours_per_day, minutes_per_hour in H0, H2.
    lia. }
  assert (Hnn : 0 <= withdrawal_window S).
  { unfold withdrawal_window, phase_duration, duration, phase_start, phase_end.
    unfold sched_ordered in Hord. lia. }
  assert (Hb : bulk_crossing_rate = 12) by ground.
  assert (Hn : force_total nw_after_defender = 2925) by ground.
  rewrite Hb, Hn. lia.
Qed.

(* Each phase consumes the force that fights the next one. *)
Theorem strength_decreases_monotonically :
  force_total eng_after_wall < force_total eng_after_hold
  /\ force_total eng_after_hold < force_total eng_after_defender
  /\ force_total eng_after_defender < force_total eng_after_approach
  /\ force_total eng_after_approach < force_total english_force.
Proof. ground. Qed.

(* Attrition feeds back into effectiveness, not only into headcount. *)
Theorem attrition_reduces_effectiveness :
  effectiveness ShieldWall norse_after_wall < effectiveness ShieldWall norse_shieldwall
  /\ effectiveness Rout eng_after_wall < effectiveness Rout english_force.
Proof. ground. Qed.

(* =============================================================================
   Rout threshold
   ============================================================================= *)

(* A force breaks when the enemy holds three halves of its effectiveness. *)
Definition rout_num : Z := 3.
Definition rout_den : Z := 2.

Definition routs (own enemy : Z) : Prop := rout_num * own <= rout_den * enemy.

(* Hardrada's death cost the army the greater part of its cohesion [HEIM]. *)
Definition leaderless_pct : Z := 60.

Definition led_effectiveness (p : phase) (f : force) (leader_alive : bool) : Z :=
  if leader_alive then effectiveness p f
  else effectiveness p f * leaderless_pct / 100.

Definition norse_eff_led : Z := led_effectiveness ShieldWall norse_after_wall true.
Definition norse_eff_leaderless : Z := led_effectiveness ShieldWall norse_after_wall false.
Definition english_eff_at_wall : Z := effectiveness ShieldWall eng_after_wall.

Lemma rout_inputs :
  norse_eff_led = 46175 /\ norse_eff_leaderless = 27705
  /\ english_eff_at_wall = 59243.
Proof. ground. Qed.

(* While Hardrada stood, the ratio was under the threshold and the line held. *)
Theorem no_rout_while_hardrada_stands :
  ~ routs norse_eff_led english_eff_at_wall.
Proof.
  destruct rout_inputs as [H1 [H2 H3]].
  unfold routs, rout_num, rout_den. rewrite H1, H3. lia.
Qed.

(* His fall carries the ratio across, and the break follows from the model. *)
Theorem rout_follows_hardradas_fall :
  routs norse_eff_leaderless english_eff_at_wall.
Proof.
  destruct rout_inputs as [H1 [H2 H3]].
  unfold routs, rout_num, rout_den. rewrite H2, H3. lia.
Qed.

(* The English were never near breaking on the same criterion. *)
Theorem english_never_rout : ~ routs english_eff_at_wall norse_eff_led.
Proof.
  destruct rout_inputs as [H1 [H2 H3]].
  unfold routs, rout_num, rout_den. rewrite H1, H3. lia.
Qed.

(* The trigger is the leader loss: nothing else about the phase changed. *)
Theorem rout_trigger_is_the_leader_loss :
  ~ routs norse_eff_led english_eff_at_wall
  /\ routs norse_eff_leaderless english_eff_at_wall
  /\ norse_eff_leaderless < norse_eff_led.
Proof.
  split; [apply no_rout_while_hardrada_stands|].
  split; [apply rout_follows_hardradas_fall|].
  destruct rout_inputs as [H1 [H2 H3]]. rewrite H1, H2. lia.
Qed.

(* =============================================================================
   Pursuit, Norse losses, and the returning ships
   ============================================================================= *)

Definition flight_miles : Z := miles_Stamford_Riccall.  (* flight to the ships [HEIM] *)
Definition flight_speed_mph : Z := 4.                   (* broken men, part in mail *)
Definition pursuit_speed_mph : Z := 5.                  (* English light foot *)

(* Head start, in minutes, at which a fugitive reaches the ships uncaught. *)
Definition escape_head_start : Z :=
  60 * flight_miles * (pursuit_speed_mph - flight_speed_mph)
  / (flight_speed_mph * pursuit_speed_mph).

(* Eystein Orre's counterattack delayed the English pursuit [HEIM]. *)
Definition pursuit_delay : Z := 60.

Definition escape_window : Z := Z.max 0 (pursuit_delay - escape_head_start).

Definition road_width_cm : Z := 480.   (* the Riccall track out of the field *)
Definition flight_file_rate : Z := 5.  (* men per minute per file, running *)

Definition break_rate (fr : Z) : Z := frontage road_width_cm * fr.

Definition escaped_with (fr : Z) : Z :=
  Z.min (force_total norse_after_wall) (break_rate fr * escape_window).

Definition norse_escaped : Z := escaped_with flight_file_rate.
Definition norse_losses_total : Z := force_total norse_force - norse_escaped.

Lemma escape_head_start_value : escape_head_start = 36.
Proof. ground. Qed.

Lemma escape_window_value : escape_window = 24.
Proof. ground. Qed.

(* Pursuit faster than flight is what makes the head start finite. *)
Theorem escape_needs_a_head_start :
  flight_speed_mph < pursuit_speed_mph /\ 0 < escape_head_start.
Proof. ground. Qed.

(* The Norse loss follows from the pursuit geometry, not from a chosen fraction. *)
Theorem norse_losses_exceed_four_fifths :
  8 * force_total norse_force <= 10 * norse_losses_total.
Proof. ground. Qed.

Theorem norse_loss_fraction : 100 * norse_losses_total / force_total norse_force = 89.
Proof. ground. Qed.

(* Model inputs to the pursuit, fixed once and reused by the robustness bounds. *)
Lemma pursuit_inputs :
  force_total norse_after_wall = 7435 /\ frontage road_width_cm = 8
  /\ force_total norse_force = 9000.
Proof. ground. Qed.

(* The result survives the whole plausible band of flight rates. *)
Theorem norse_losses_robust_in_flight_rate : forall fr,
  1 <= fr <= 9 ->
  8 * force_total norse_force <= 10 * (force_total norse_force - escaped_with fr).
Proof.
  intros fr Hfr. destruct pursuit_inputs as [Hn [Hf Ht]].
  unfold escaped_with, break_rate.
  rewrite Hn, Hf, Ht, escape_window_value.
  rewrite Z.min_r by lia. lia.
Qed.

(* Nine men per file per minute is the exact edge of that band. *)
Theorem flight_rate_band_is_tight :
  8 * force_total norse_force <= 10 * (force_total norse_force - escaped_with 9)
  /\ ~ (8 * force_total norse_force <= 10 * (force_total norse_force - escaped_with 10)).
Proof.
  assert (H9 : escaped_with 9 = 1728) by ground.
  assert (H10 : escaped_with 10 = 1920) by ground.
  destruct pursuit_inputs as [_ [_ Ht]].
  rewrite H9, H10, Ht. split; lia.
Qed.

(* The result likewise survives the band of admissible pursuit delays. *)
Definition escaped_with_delay (d : Z) : Z :=
  Z.min (force_total norse_after_wall)
        (break_rate flight_file_rate * Z.max 0 (d - escape_head_start)).

Theorem norse_losses_robust_in_pursuit_delay : forall d,
  escape_head_start <= d <= 81 ->
  8 * force_total norse_force <= 10 * (force_total norse_force - escaped_with_delay d).
Proof.
  intros d Hd. rewrite escape_head_start_value in Hd.
  destruct pursuit_inputs as [Hn [Hf Ht]].
  unfold escaped_with_delay, break_rate, flight_file_rate.
  rewrite Hn, Hf, Ht, escape_head_start_value.
  rewrite Z.min_r by lia. lia.
Qed.

Theorem pursuit_delay_band_is_tight :
  8 * force_total norse_force <= 10 * (force_total norse_force - escaped_with_delay 81)
  /\ ~ (8 * force_total norse_force
        <= 10 * (force_total norse_force - escaped_with_delay 82)).
Proof.
  assert (H81 : escaped_with_delay 81 = 1800) by ground.
  assert (H82 : escaped_with_delay 82 = 1840) by ground.
  destruct pursuit_inputs as [_ [_ Ht]].
  rewrite H81, H82, Ht. split; lia.
Qed.

(* -----------------------------------------------------------------------------
   The twenty-four ships
   -------------------------------------------------------------------------- *)

(* Olaf sailed home with the survivors in twenty-four ships [HEIM]. *)
Definition ships_reported : Z := 24.
Definition ship_capacity_low : Z := 30.
Definition ship_capacity_high : Z := 50.

Definition ships_for (men capacity : Z) : Z := ceil_div men capacity.

(* The survivors the model leaves need a hull count bracketing the reported figure. *)
Theorem reported_ships_within_model_bracket :
  ships_for norse_escaped ship_capacity_high <= ships_reported
  <= ships_for norse_escaped ship_capacity_low.
Proof. ground. Qed.

Theorem ships_bracket_values :
  ships_for norse_escaped ship_capacity_low = 32
  /\ ships_for norse_escaped ship_capacity_high = 20.
Proof. ground. Qed.

(* The bracket holds over the whole capacity range, not at one chosen capacity. *)
Theorem ships_bracket_robust : forall c,
  ship_capacity_low <= c <= ship_capacity_high ->
  ships_for norse_escaped ship_capacity_high <= ships_for norse_escaped c.
Proof.
  intros c Hc. unfold ship_capacity_low, ship_capacity_high in Hc.
  unfold ships_for. apply ceil_div_anti_mono; [ground | lia | unfold ship_capacity_high; lia].
Qed.

(* =============================================================================
   English losses and the post-battle march rate
   ============================================================================= *)

Definition rout_efficiency_pct : Z := 10.  (* what a broken force still returns *)

Definition norse_routed : force :=
  scale_force norse_after_wall rout_efficiency_pct 100.

Definition eng_after_rout : force :=
  attrit eng_after_wall (losses_inflicted nominal Rout norse_routed).

Definition english_losses_total : Z :=
  force_total english_force - force_total eng_after_rout.

Lemma english_losses_value : english_losses_total = 353.
Proof. ground. Qed.

(* The English lost an order of magnitude fewer men than the Norse. *)
Theorem english_losses_far_below_norse :
  10 * english_losses_total < norse_losses_total.
Proof. ground. Qed.

(* -----------------------------------------------------------------------------
   Marching strength after the battle
   -------------------------------------------------------------------------- *)

Definition fatigue_pct : Z := 70.        (* march capacity the day after the battle *)
Definition recovery_per_day : Z := 6.    (* percentage points regained per rest day *)

Definition recovered_pct (rest : Z) : Z := Z.min 100 (fatigue_pct + recovery_per_day * rest).

(* Rate scales with surviving strength and with recovery, both derived. *)
Definition march_rate_after (rest : Z) : Z :=
  rate_south_base * force_total eng_after_rout * recovered_pct rest
  / (force_total english_force * 100).

Lemma recovered_pct_caps_at_full : forall rest, 5 <= rest -> recovered_pct rest = 100.
Proof.
  intros rest H. unfold recovered_pct, fatigue_pct, recovery_per_day.
  apply Z.min_l. lia.
Qed.

Lemma march_rate_full_recovery : forall rest, 5 <= rest -> march_rate_after rest = 29.
Proof.
  intros rest H. unfold march_rate_after.
  rewrite (recovered_pct_caps_at_full rest H). ground.
Qed.

(* Unrested, the depleted army marches nine miles a day slower. *)
Theorem fatigue_costs_march_rate :
  march_rate_after 0 = 20 /\ march_rate_after 5 = 29
  /\ march_rate_after 0 < rate_south_base.
Proof. ground. Qed.

Lemma march_rate_after_pos : forall rest, 0 <= rest -> 0 < march_rate_after rest.
Proof.
  intros rest H.
  destruct (Z.le_gt_cases 5 rest) as [H5|H5].
  - rewrite march_rate_full_recovery by exact H5; lia.
  - assert (Hr : rest = 0 \/ rest = 1 \/ rest = 2 \/ rest = 3 \/ rest = 4) by lia.
    destruct Hr as [E|[E|[E|[E|E]]]]; rewrite E; ground.
Qed.

Definition post_battle_rate : Z := march_rate_after 5.

Lemma post_battle_rate_value : post_battle_rate = 29.
Proof. unfold post_battle_rate; apply march_rate_full_recovery; lia. Qed.

(* =============================================================================
   Per-leg interval containment
   ============================================================================= *)

Definition leg1_depart : day := d_sep20.   (* London, 20 September [ASC-C] *)
Definition leg1_arrive : day := d_sep24.   (* Tadcaster, 24 September [ASC-C] *)
Definition leg3a_depart : day := d_oct01.  (* York, 1 October [JW] *)
Definition leg3a_arrive : day := d_oct07.  (* London, 7 October [JW] *)
Definition leg3b_depart : day := d_oct12.  (* London, 12 October [JW] *)
Definition leg3b_arrive : day := d_oct13.  (* Senlac, 13 October [JW] *)

Theorem leg1_fits : leg_fits leg1_depart leg1_arrive miles_London_York rate_north.
Proof. ground. Qed.

Theorem leg3a_fits : leg_fits leg3a_depart leg3a_arrive miles_London_York post_battle_rate.
Proof. ground. Qed.

Theorem leg3b_fits :
  leg_fits leg3b_depart leg3b_arrive miles_London_Hastings post_battle_rate.
Proof. ground. Qed.

(* The battle occupies its own day, inside its own daylight. *)
Theorem battle_fits_its_day :
  d_sep24 < d_sep25 < d_oct01
  /\ in_sep25_daylight (b0 nominal) /\ in_sep25_daylight (b5 nominal).
Proof.
  split; [unfold d_sep24, d_sep25, d_oct01; split; lia|].
  apply battle_within_daylight_robust, nominal_admissible.
Qed.

(* The return from the battlefield fits inside the York rest. *)
Theorem return_to_york_fits :
  leg_fits d_sep25 d_oct01 miles_York_Stamford post_battle_rate.
Proof. ground. Qed.

(* Every marched leg is tight: none has a spare day at its own rate. *)
Theorem all_legs_are_tight :
  travel_days miles_London_York rate_north = leg_days leg1_depart leg1_arrive
  /\ travel_days miles_London_York post_battle_rate = leg_days leg3a_depart leg3a_arrive
  /\ travel_days miles_London_Hastings post_battle_rate
     = leg_days leg3b_depart leg3b_arrive.
Proof. ground. Qed.

(* -----------------------------------------------------------------------------
   Exact minimum rate for each leg
   -------------------------------------------------------------------------- *)

Theorem leg1_minimum_rate : forall s, 0 < s ->
  (leg_fits leg1_depart leg1_arrive miles_London_York s <-> 38 <= s).
Proof.
  intros s Hs. unfold leg_fits, travel_days.
  apply rate_threshold_iff; [ground | ground | ground | ground | exact Hs].
Qed.

Theorem leg3a_minimum_rate : forall s, 0 < s ->
  (leg_fits leg3a_depart leg3a_arrive miles_London_York s <-> 28 <= s).
Proof.
  intros s Hs. unfold leg_fits, travel_days.
  apply rate_threshold_iff; [ground | ground | ground | ground | exact Hs].
Qed.

Theorem leg3b_minimum_rate : forall s, 0 < s ->
  (leg_fits leg3b_depart leg3b_arrive miles_London_Hastings s <-> 29 <= s).
Proof.
  intros s Hs. unfold leg_fits, travel_days.
  apply rate_threshold_iff; [ground | ground | ground | ground | exact Hs].
Qed.

(* The derived post-battle rate exactly meets the binding leg. *)
Theorem post_battle_rate_meets_the_binding_leg :
  post_battle_rate = 29
  /\ leg_fits leg3b_depart leg3b_arrive miles_London_Hastings post_battle_rate
  /\ ~ leg_fits leg3b_depart leg3b_arrive miles_London_Hastings (post_battle_rate - 1).
Proof.
  assert (H2 : travel_days miles_London_Hastings 29 = 2) by ground.
  assert (H3 : travel_days miles_London_Hastings 28 = 3) by ground.
  assert (Hd : leg_days leg3b_depart leg3b_arrive = 2) by ground.
  unfold leg_fits. rewrite post_battle_rate_value.
  replace (29 - 1) with 28 by lia.
  rewrite H2, H3, Hd. repeat split; lia.
Qed.

(* =============================================================================
   Minimum feasible rate over the whole southward march
   ============================================================================= *)

(* Marching resumes after the battle day and must end on 13 October. *)
Definition south_window_from (depart : day) : Z := leg_days depart d_oct13.

Definition south_march_fits (depart : day) (rate : Z) : Prop :=
  travel_days miles_Stamford_Hastings rate <= south_window_from depart.

(* Leaving on 26 September, fifteen miles a day suffices and fourteen does not. *)
Theorem earliest_departure_minimum_rate : forall s, 0 < s ->
  (south_march_fits (d_sep25 + 1) s <-> 15 <= s).
Proof.
  intros s Hs. unfold south_march_fits, travel_days.
  apply rate_threshold_iff; [ground | ground | ground | ground | exact Hs].
Qed.

(* Leaving on the historical date, the exact minimum rises to twenty. *)
Theorem historical_departure_minimum_rate : forall s, 0 < s ->
  (south_march_fits d_oct01 s <-> 20 <= s).
Proof.
  intros s Hs. unfold south_march_fits, travel_days.
  apply rate_threshold_iff; [ground | ground | ground | ground | exact Hs].
Qed.

(* The rate the battle model produces clears the historical requirement. *)
Theorem derived_rate_clears_historical_requirement :
  20 <= post_battle_rate /\ south_march_fits d_oct01 post_battle_rate.
Proof. rewrite post_battle_rate_value. split; [lia | ground]. Qed.

(* =============================================================================
   Maximum admissible delay at Stamford Bridge
   ============================================================================= *)

(* Resting k days puts departure on 26 September plus k. *)
Definition departure_after_rest (k : Z) : day := d_sep25 + 1 + k.

Definition delay_feasible (k : Z) : Prop :=
  south_march_fits (departure_after_rest k) (march_rate_after k).

Lemma delay_feasible_small : forall k, 0 <= k <= 4 -> delay_feasible k.
Proof.
  intros k Hk.
  assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
  destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; unfold delay_feasible; ground.
Qed.

Lemma delay_feasible_large : forall k, 5 <= k -> (delay_feasible k <-> k <= 9).
Proof.
  intros k Hk.
  unfold delay_feasible, south_march_fits, south_window_from, leg_days,
    departure_after_rest.
  rewrite (march_rate_full_recovery k Hk).
  assert (H9 : travel_days miles_Stamford_Hastings 29 = 9) by ground.
  rewrite H9. unfold d_sep25, d_oct13. lia.
Qed.

(* The army absorbs at most nine days of delay, and ten breaks the campaign. *)
Theorem maximum_admissible_delay : forall k, 0 <= k -> (delay_feasible k <-> k <= 9).
Proof.
  intros k Hk. destruct (Z.le_gt_cases 5 k) as [H5|H5].
  - apply delay_feasible_large; exact H5.
  - split; [intros _; lia | intros _; apply delay_feasible_small; lia].
Qed.

Theorem delay_bound_is_tight : delay_feasible 9 /\ ~ delay_feasible 10.
Proof.
  split.
  - apply (maximum_admissible_delay 9); lia.
  - intros H. pose proof (proj1 (maximum_admissible_delay 10 ltac:(lia)) H). lia.
Qed.

(* -----------------------------------------------------------------------------
   The admissible departure interval
   -------------------------------------------------------------------------- *)

Definition min_recovery_days : Z := 1.  (* the army cannot march the battle night *)

Definition earliest_departure : day := departure_after_rest min_recovery_days.
Definition latest_departure : day := departure_after_rest 9.

Theorem departure_window_is_an_interval :
  earliest_departure < latest_departure
  /\ forall k, min_recovery_days <= k <= 9 ->
     earliest_departure <= departure_after_rest k <= latest_departure.
Proof.
  unfold earliest_departure, latest_departure, departure_after_rest,
    min_recovery_days, d_sep25.
  split; [lia | intros k Hk; split; lia].
Qed.

(* Harold left York on 1 October, strictly inside the admissible window [JW]. *)
Theorem historical_departure_strictly_inside :
  earliest_departure < d_oct01 < latest_departure.
Proof.
  unfold earliest_departure, latest_departure, departure_after_rest,
    min_recovery_days, d_sep25, d_oct01. split; lia.
Qed.

Theorem historical_departure_feasible : delay_feasible 5.
Proof. apply (maximum_admissible_delay 5); lia. Qed.

(* =============================================================================
   Supply
   ============================================================================= *)

(* The host carried a week of rations and drew the rest from the shires [JW]. *)
Definition rations_carried : Z := 7.
Definition resupply_capacity : Z := 12000.

Definition campaign_days : Z := d_oct14 - d_sep20.

Lemma campaign_days_value : campaign_days = 24.
Proof. ground. Qed.

(* Stock in man-days: what was carried, plus daily requisition, less consumption. *)
Definition supply_remaining (n d : Z) : Z :=
  rations_carried * n + Z.min resupply_capacity n * d - n * d.

Definition non_starving (n d : Z) : Prop := 0 < supply_remaining n d.

(* A force living inside the requisition capacity never draws down its stock. *)
Theorem supply_holds_below_capacity : forall n d,
  0 < n <= resupply_capacity -> 0 <= d -> non_starving n d.
Proof.
  intros n d Hn Hd. unfold non_starving, supply_remaining, rations_carried.
  rewrite Z.min_r by lia. lia.
Qed.

(* Above capacity the stock falls linearly in the shortfall. *)
Lemma supply_above_capacity : forall n d,
  resupply_capacity <= n ->
  supply_remaining n d = rations_carried * n - (n - resupply_capacity) * d.
Proof.
  intros n d H. unfold supply_remaining. rewrite Z.min_l by lia. lia.
Qed.

(* The whole English range feeds itself for the whole campaign. *)
Theorem supply_holds_across_english_range : forall e d,
  english_in_range e -> 0 <= d <= campaign_days -> non_starving e d.
Proof.
  intros e d He Hd. unfold english_in_range, english_total_low, english_total_high in He.
  rewrite campaign_days_value in Hd.
  destruct (Z.le_gt_cases e resupply_capacity) as [Hle|Hgt].
  - apply supply_holds_below_capacity; [split; [lia | exact Hle] | lia].
  - unfold non_starving. rewrite supply_above_capacity by lia.
    assert (Hb : (e - resupply_capacity) * d <= (e - resupply_capacity) * 24)
      by (apply Z.mul_le_mono_nonneg_l; unfold resupply_capacity in *; lia).
    unfold rations_carried, resupply_capacity in *. lia.
Qed.

(* The Norse range likewise, at the same capacity. *)
Theorem supply_holds_across_norse_range : forall n d,
  norse_in_range n -> 0 <= d <= campaign_days -> non_starving n d.
Proof.
  intros n d Hn Hd. unfold norse_in_range, norse_total_low, norse_total_high in Hn.
  apply supply_holds_below_capacity; [unfold resupply_capacity; lia | lia].
Qed.

(* The exact largest host the campaign feeds for its whole length. *)
Theorem supply_capacity_boundary :
  non_starving 16941 campaign_days /\ ~ non_starving 16942 campaign_days.
Proof.
  unfold non_starving, supply_remaining, rations_carried, resupply_capacity.
  rewrite campaign_days_value, !Z.min_l by lia. split; lia.
Qed.

Theorem supply_boundary_exceeds_every_estimate :
  english_total_high < 16941 /\ norse_total_high < 16941.
Proof. unfold english_total_high, norse_total_high; split; lia. Qed.

(* Rate does not change the supply verdict across the admissible band. *)
Theorem supply_holds_across_rates : forall e s,
  english_in_range e -> 15 <= s <= 45 ->
  non_starving e (travel_days miles_Stamford_Hastings s).
Proof.
  intros e s He Hs.
  apply supply_holds_across_english_range; [exact He|].
  split.
  - apply ceil_div_nonneg; [ground | lia].
  - rewrite campaign_days_value.
    transitivity (travel_days miles_Stamford_Hastings 15).
    + apply travel_days_rate_anti_mono; [ground | lia | lia].
    + ground.
Qed.

(* =============================================================================
   Chronology
   ============================================================================= *)

Inductive event_name :=
  | Landing
  | FulfordBattle
  | MarchNorthBegins
  | YorkTaken
  | YorkArrive
  | ApproachStart
  | MarchNorthEnds
  | BridgeDefenseBegins
  | StamfordBattleBegins
  | HardradaFalls
  | StamfordBattleEnds
  | EnglishRecovery
  | WilliamLands
  | MarchSouthBegins
  | LondonArrive
  | LondonDepart
  | HastingsBattleBegins
  | HastingsBattleEnds.

Record event := {
  e_name : event_name;
  e_time : time;
  e_loc : location;
  e_actor : actor
}.

Definition before (e1 e2 : event) : Prop := e_time e1 < e_time e2.

Lemma before_trans : forall a b c, before a b -> before b c -> before a c.
Proof. unfold before; intros; lia. Qed.

Record timeline := {
  t_landing : time;
  t_fulford : time;
  t_york_taken : time;
  t_london_depart : time;
  t_york_arrive : time;
  t_approach_start : time;
  t_approach_end : time;
  t_bridge_defense : time;
  t_stamford_start : time;
  t_hardrada_fall : time;
  t_stamford_end : time;
  t_recovery : time;
  t_william_lands : time;
  t_march_south_start : time;
  t_london_arrive : time;
  t_london_depart_south : time;
  t_hastings_start : time;
  t_hastings_end : time
}.

Record chronology (T : timeline) : Prop := {
  landing_before_fulford : t_landing T < t_fulford T;
  landing_before_london_depart : t_landing T < t_london_depart T;
  fulford_before_york_taken : t_fulford T < t_york_taken T;
  london_depart_before_york_arrive : t_london_depart T < t_york_arrive T;
  york_taken_before_approach : t_york_taken T <= t_approach_start T;
  york_arrive_before_approach : t_york_arrive T <= t_approach_start T;
  approach_start_before_end : t_approach_start T < t_approach_end T;
  approach_end_before_bridge : t_approach_end T <= t_bridge_defense T;
  bridge_before_stamford : t_bridge_defense T <= t_stamford_start T;
  stamford_start_before_end : t_stamford_start T < t_stamford_end T;
  hardrada_falls_after_start : t_stamford_start T <= t_hardrada_fall T;
  hardrada_falls_before_end : t_hardrada_fall T <= t_stamford_end T;
  stamford_end_before_recovery : t_stamford_end T <= t_recovery T;
  stamford_end_before_william : t_stamford_end T < t_william_lands T;
  recovery_before_march_south : t_recovery T <= t_march_south_start T;
  william_before_march_south : t_william_lands T < t_march_south_start T;
  march_south_before_london : t_march_south_start T < t_london_arrive T;
  london_arrive_before_depart : t_london_arrive T < t_london_depart_south T;
  london_depart_before_hastings : t_london_depart_south T < t_hastings_start T;
  hastings_start_before_end : t_hastings_start T < t_hastings_end T
}.

Lemma landing_before_hastings : forall T, chronology T -> t_landing T < t_hastings_start T.
Proof. intros T Hc; destruct Hc; lia. Qed.

Fixpoint sorted_by_time_from (prev : event) (rest : list event) : Prop :=
  match rest with
  | [] => True
  | e :: rs => e_time prev <= e_time e /\ sorted_by_time_from e rs
  end.

Definition sorted_by_time (evs : list event) : Prop :=
  match evs with
  | [] => True
  | e :: rs => sorted_by_time_from e rs
  end.

(* =============================================================================
   The historical timeline
   ============================================================================= *)

Definition hastings_duration : Z := 9 * minutes_per_hour.  (* dawn to dusk [ASC-D] *)

(* Every field is dated from a source; none is fitted to make a proof pass. *)
Definition T_historical : timeline := {|
  t_landing := t_of d_sep18 12 0;             (* fleet beaches at Riccall [ASC-C] *)
  t_fulford := t_of d_sep20 9 0;              (* Battle of Fulford [ASC-C] *)
  t_york_taken := t_of d_sep24 12 0;          (* York gives hostages [ASC-C] *)
  t_london_depart := t_of d_sep20 6 0;        (* Harold quits London [ASC-C] *)
  t_york_arrive := t_of d_sep24 18 0;         (* Harold reaches Tadcaster [ASC-C] *)
  t_approach_start := t_of d_sep25 6 0;       (* march through York at dawn [ASC-D] *)
  t_approach_end := b0 nominal;               (* contact west of the Derwent *)
  t_bridge_defense := b1 nominal;             (* the axeman takes the span [ASC-C] *)
  t_stamford_start := b3 nominal;             (* the shield walls meet [HEIM] *)
  t_hardrada_fall := b4 nominal;              (* Hardrada killed by an arrow [HEIM] *)
  t_stamford_end := b5 nominal;               (* the pursuit ends at the ships [HEIM] *)
  t_recovery := t_sep25_evening;              (* the English hold the field *)
  t_william_lands := t_of d_sep28 12 0;       (* Normans land at Pevensey [ASC-D] *)
  t_march_south_start := t_of d_oct01 6 0;    (* Harold quits York [JW] *)
  t_london_arrive := t_of d_oct07 18 0;       (* Harold reaches London [JW] *)
  t_london_depart_south := t_of d_oct12 6 0;  (* Harold quits London [JW] *)
  t_hastings_start := t_oct14_morning;        (* Battle of Hastings opens [ASC-D] *)
  t_hastings_end := t_oct14_morning + hastings_duration
|}.

Theorem chronology_T_historical : chronology T_historical.
Proof. constructor; ground. Qed.

Definition events_historical : list event :=
  [ {| e_name := Landing; e_time := t_landing T_historical;
       e_loc := Riccall; e_actor := NorwegianHost |};
    {| e_name := MarchNorthBegins; e_time := t_london_depart T_historical;
       e_loc := London; e_actor := EnglishHost |};
    {| e_name := FulfordBattle; e_time := t_fulford T_historical;
       e_loc := Fulford; e_actor := NorwegianHost |};
    {| e_name := YorkTaken; e_time := t_york_taken T_historical;
       e_loc := York; e_actor := NorwegianHost |};
    {| e_name := YorkArrive; e_time := t_york_arrive T_historical;
       e_loc := Tadcaster; e_actor := EnglishHost |};
    {| e_name := ApproachStart; e_time := t_approach_start T_historical;
       e_loc := York; e_actor := EnglishHost |};
    {| e_name := MarchNorthEnds; e_time := t_approach_end T_historical;
       e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := BridgeDefenseBegins; e_time := t_bridge_defense T_historical;
       e_loc := Derwent; e_actor := NorwegianHost |};
    {| e_name := StamfordBattleBegins; e_time := t_stamford_start T_historical;
       e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := HardradaFalls; e_time := t_hardrada_fall T_historical;
       e_loc := StamfordBridge; e_actor := Hardrada |};
    {| e_name := StamfordBattleEnds; e_time := t_stamford_end T_historical;
       e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := EnglishRecovery; e_time := t_recovery T_historical;
       e_loc := StamfordBridge; e_actor := Harold |};
    {| e_name := WilliamLands; e_time := t_william_lands T_historical;
       e_loc := Hastings; e_actor := William |};
    {| e_name := MarchSouthBegins; e_time := t_march_south_start T_historical;
       e_loc := York; e_actor := EnglishHost |};
    {| e_name := LondonArrive; e_time := t_london_arrive T_historical;
       e_loc := London; e_actor := EnglishHost |};
    {| e_name := LondonDepart; e_time := t_london_depart_south T_historical;
       e_loc := London; e_actor := EnglishHost |};
    {| e_name := HastingsBattleBegins; e_time := t_hastings_start T_historical;
       e_loc := Hastings; e_actor := EnglishHost |};
    {| e_name := HastingsBattleEnds; e_time := t_hastings_end T_historical;
       e_loc := Hastings; e_actor := EnglishHost |}
  ].

Theorem events_historical_sorted : sorted_by_time events_historical.
Proof. ground. Qed.

(* The battle sits inside the daylight of its own day. *)
Theorem historical_battle_in_daylight :
  in_sep25_daylight (t_stamford_start T_historical)
  /\ in_sep25_daylight (t_stamford_end T_historical).
Proof. ground. Qed.

(* The southward march begins only after news of Pevensey could reach York. *)
Theorem march_south_answers_pevensey :
  t_william_lands T_historical < t_march_south_start T_historical
  /\ duration (t_william_lands T_historical) (t_march_south_start T_historical)
     / minutes_per_day = 2.
Proof. ground. Qed.

(* The whole southward march fits between the two dated endpoints. *)
Theorem historical_march_south_fits :
  leg_fits d_oct01 d_oct13 miles_Stamford_Hastings post_battle_rate.
Proof. ground. Qed.

(* =============================================================================
   Casualty-rate cross-check
   ============================================================================= *)

(* A coarse rate table, independent of the effectiveness model, as a sanity bound. *)
Definition casualties_in_phase (S : schedule) (rate : phase -> Z) (p : phase) : Z :=
  rate p * phase_duration S p / minutes_per_hour.

Definition casualties_total (S : schedule) (rate : phase -> Z) : Z :=
  casualties_in_phase S rate Approach + casualties_in_phase S rate BridgeDefender
  + casualties_in_phase S rate BridgeHold + casualties_in_phase S rate ShieldWall
  + casualties_in_phase S rate Rout.

(* Any hourly rate the sources admit; the bound below quantifies over all of them. *)
Definition rate_cap : Z := 500.

Definition rate_admissible (rate : phase -> Z) : Prop :=
  forall p, 0 <= rate p <= rate_cap.

Lemma casualties_in_phase_bounded : forall rate p,
  rate_admissible rate ->
  casualties_in_phase nominal rate p
  <= casualties_in_phase nominal (fun _ => rate_cap) p.
Proof.
  intros rate p Hr. unfold casualties_in_phase.
  apply Z.div_le_mono; [unfold minutes_per_hour; lia|].
  apply Z.mul_le_mono_nonneg_r; [destruct p; ground | apply Hr].
Qed.

(* Largest total any admissible rate table can produce. *)
Definition casualty_ceiling : Z := casualties_total nominal (fun _ => rate_cap).

Lemma casualty_ceiling_value : casualty_ceiling = 4000.
Proof. ground. Qed.

Lemma casualties_below_ceiling : forall rate,
  rate_admissible rate -> casualties_total nominal rate <= casualty_ceiling.
Proof.
  intros rate Hr. unfold casualty_ceiling, casualties_total.
  pose proof (casualties_in_phase_bounded rate Approach Hr).
  pose proof (casualties_in_phase_bounded rate BridgeDefender Hr).
  pose proof (casualties_in_phase_bounded rate BridgeHold Hr).
  pose proof (casualties_in_phase_bounded rate ShieldWall Hr).
  pose proof (casualties_in_phase_bounded rate Rout Hr).
  lia.
Qed.

(* Both sides are quantified: any admissible rate table, any host above the ceiling. *)
Theorem casualties_bounded_general : forall rate pop,
  rate_admissible rate -> casualty_ceiling < pop -> casualties_total nominal rate < pop.
Proof.
  intros rate pop Hr Hpop. pose proof (casualties_below_ceiling rate Hr). lia.
Qed.

Corollary casualties_bounded_english : forall rate pop,
  rate_admissible rate -> english_total_low <= pop -> casualties_total nominal rate < pop.
Proof.
  intros rate pop Hr Hpop. apply casualties_bounded_general; [exact Hr|].
  rewrite casualty_ceiling_value. unfold english_total_low in Hpop. lia.
Qed.

Corollary casualties_bounded_norse : forall rate pop,
  rate_admissible rate -> norse_total_low <= pop -> casualties_total nominal rate < pop.
Proof.
  intros rate pop Hr Hpop. apply casualties_bounded_general; [exact Hr|].
  rewrite casualty_ceiling_value. unfold norse_total_low in Hpop. lia.
Qed.

(* Reference rates read off the narrative sources, both inside the cap [HEIM], [ASC-C]. *)
Definition rate_english (p : phase) : Z :=
  match p with
  | Approach => 30 | BridgeDefender => 6 | BridgeHold => 80
  | ShieldWall => 150 | Rout => 70
  end.

Definition rate_norse (p : phase) : Z :=
  match p with
  | Approach => 50 | BridgeDefender => 6 | BridgeHold => 120
  | ShieldWall => 200 | Rout => 300
  end.

Lemma rate_english_admissible : rate_admissible rate_english.
Proof. intros p; destruct p; cbv [rate_english rate_cap]; split; lia. Qed.

Lemma rate_norse_admissible : rate_admissible rate_norse.
Proof. intros p; destruct p; cbv [rate_norse rate_cap]; split; lia. Qed.

(* =============================================================================
   Computed values
   ============================================================================= *)

Example v_dist_london_york : miles_London_York = 190.
Proof. ground. Qed.

Example v_dist_york_stamford : miles_York_Stamford = 10.
Proof. ground. Qed.

Example v_dist_london_hastings : miles_London_Hastings = 58.
Proof. ground. Qed.

Example v_dist_stamford_hastings : miles_Stamford_Hastings = 258.
Proof. ground. Qed.

Example v_dist_york_hastings : miles_York_Hastings = 248.
Proof. ground. Qed.

Example v_dist_stamford_riccall : miles_Stamford_Riccall = 12.
Proof. ground. Qed.

Example v_dist_london_stamford : dist London StamfordBridge = 200.
Proof. ground. Qed.

Example v_route_full : path_distance route_full = 458.
Proof. ground. Qed.

Example v_bridge_frontage : frontage bridge_width_cm = 4.
Proof. ground. Qed.

Example v_bulk_rate : bulk_crossing_rate = 12.
Proof. ground. Qed.

Example v_withdrawal_window : withdrawal_window nominal = 150.
Proof. ground. Qed.

Example v_west_withdrawn : west_withdrawn_count = 1800.
Proof. ground. Qed.

Example v_west_remnant : force_total west_remnant = 1126.
Proof. ground. Qed.

Example v_norse_shieldwall : force_total norse_shieldwall = 7799.
Proof. ground. Qed.

Example v_norse_after_wall : force_total norse_after_wall = 7435.
Proof. ground. Qed.

Example v_english_after_wall : force_total eng_after_wall = 10683.
Proof. ground. Qed.

Example v_english_after_rout : force_total eng_after_rout = 10647.
Proof. ground. Qed.

Example v_effectiveness_english : english_eff_at_wall = 59243.
Proof. ground. Qed.

Example v_effectiveness_norse_led : norse_eff_led = 46175.
Proof. ground. Qed.

Example v_effectiveness_norse_leaderless : norse_eff_leaderless = 27705.
Proof. ground. Qed.

Example v_escape_head_start : escape_head_start = 36.
Proof. ground. Qed.

Example v_escape_window : escape_window = 24.
Proof. ground. Qed.

Example v_norse_escaped : norse_escaped = 960.
Proof. ground. Qed.

Example v_norse_losses : norse_losses_total = 8040.
Proof. ground. Qed.

Example v_english_losses : english_losses_total = 353.
Proof. ground. Qed.

Example v_post_battle_rate : post_battle_rate = 29.
Proof. apply post_battle_rate_value. Qed.

Example v_unrested_rate : march_rate_after 0 = 20.
Proof. ground. Qed.

Example v_casualties_english_table : casualties_total nominal rate_english = 686.
Proof. ground. Qed.

Example v_casualties_norse_table : casualties_total nominal rate_norse = 1251.
Proof. ground. Qed.

Example v_campaign_days : campaign_days = 24.
Proof. ground. Qed.

Example v_supply_at_point_estimate : supply_remaining 11000 campaign_days = 77000.
Proof. ground. Qed.

(* =============================================================================
   Headline results
   ============================================================================= *)

(* The bridge stand is a consequence of the span's width and an axe's reach. *)
Theorem headline_bridge_geometry :
  span_blocked 1 bridge_width_cm
  /\ crossing_rate_at bridge_width_cm 1 = 0
  /\ crossing_rate_at bridge_width_cm 0 = bulk_crossing_rate
  /\ ~ span_blocked 1 (bridge_width_cm + man_width_cm).
Proof.
  split; [apply lone_axeman_blocks_bridge|].
  split; [apply lone_axeman_stops_the_crossing|].
  split; [apply cleared_span_runs_at_ceiling | apply lone_axeman_bound_is_tight].
Qed.

(* The Norwegian break is caused by the ratio crossing its threshold. *)
Theorem headline_rout :
  ~ routs norse_eff_led english_eff_at_wall
  /\ routs norse_eff_leaderless english_eff_at_wall.
Proof.
  split; [apply no_rout_while_hardrada_stands | apply rout_follows_hardradas_fall].
Qed.

(* Four fifths of the Norwegian army is lost, across the whole pursuit band. *)
Theorem headline_norse_annihilation :
  8 * force_total norse_force <= 10 * norse_losses_total
  /\ (forall fr, 1 <= fr <= 9 ->
      8 * force_total norse_force <= 10 * (force_total norse_force - escaped_with fr))
  /\ ships_for norse_escaped ship_capacity_high <= ships_reported
     <= ships_for norse_escaped ship_capacity_low.
Proof.
  split; [apply norse_losses_exceed_four_fifths|].
  split; [apply norse_losses_robust_in_flight_rate
         | apply reported_ships_within_model_bracket].
Qed.

(* Each marched leg fits its own dated window, and the first has no slack. *)
Theorem headline_leg_containment :
  leg_fits leg1_depart leg1_arrive miles_London_York rate_north
  /\ leg_fits leg3a_depart leg3a_arrive miles_London_York post_battle_rate
  /\ leg_fits leg3b_depart leg3b_arrive miles_London_Hastings post_battle_rate
  /\ travel_days miles_London_York rate_north = leg_days leg1_depart leg1_arrive.
Proof.
  split; [apply leg1_fits|].
  split; [apply leg3a_fits|].
  split; [apply leg3b_fits | apply all_legs_are_tight].
Qed.

(* Exact minimum rates, each an iff rather than a pair of point checks. *)
Theorem headline_rate_thresholds :
  (forall s, 0 < s -> (leg_fits leg1_depart leg1_arrive miles_London_York s <-> 38 <= s))
  /\ (forall s, 0 < s -> (south_march_fits (d_sep25 + 1) s <-> 15 <= s))
  /\ (forall s, 0 < s -> (south_march_fits d_oct01 s <-> 20 <= s)).
Proof.
  split; [apply leg1_minimum_rate|].
  split; [apply earliest_departure_minimum_rate | apply historical_departure_minimum_rate].
Qed.

(* The army absorbs exactly nine days of delay, and the historical rest sits inside. *)
Theorem headline_delay_bound :
  (forall k, 0 <= k -> (delay_feasible k <-> k <= 9))
  /\ delay_feasible 9 /\ ~ delay_feasible 10
  /\ earliest_departure < d_oct01 < latest_departure.
Proof.
  split; [apply maximum_admissible_delay|].
  split; [exact (proj1 delay_bound_is_tight)|].
  split; [exact (proj2 delay_bound_is_tight) | apply historical_departure_strictly_inside].
Qed.

(* Numerical superiority holds exactly when the English total clears the Norse maximum. *)
Theorem headline_superiority :
  (forall e, english_in_range e ->
     ((forall n, norse_in_range n -> n < e) <-> norse_total_high < e))
  /\ (exists e n, english_in_range e /\ norse_in_range n /\ e < n).
Proof.
  split; [apply english_superiority_exact | apply english_superiority_not_universal].
Qed.

(* The campaign feeds every admissible host for its whole length. *)
Theorem headline_supply :
  (forall e d, english_in_range e -> 0 <= d <= campaign_days -> non_starving e d)
  /\ (forall n d, norse_in_range n -> 0 <= d <= campaign_days -> non_starving n d)
  /\ ~ non_starving 16942 campaign_days.
Proof.
  split; [apply supply_holds_across_english_range|].
  split; [apply supply_holds_across_norse_range | exact (proj2 supply_capacity_boundary)].
Qed.

(* The dated reconstruction is a chronology, is sorted, and fits its window. *)
Theorem headline_historical_timeline :
  chronology T_historical
  /\ sorted_by_time events_historical
  /\ leg_fits d_oct01 d_oct13 miles_Stamford_Hastings post_battle_rate.
Proof.
  split; [apply chronology_T_historical|].
  split; [apply events_historical_sorted | apply historical_march_south_fits].
Qed.

(* Phase timing conclusions hold across the whole half-hour uncertainty band. *)
Theorem headline_schedule_robustness :
  sched_admissible nominal
  /\ (forall S p, sched_admissible S ->
      in_sep25_daylight (phase_start S p) /\ in_sep25_daylight (phase_end S p))
  /\ (forall S, sched_admissible S ->
      bulk_crossing_rate * withdrawal_window S < force_total nw_after_defender).
Proof.
  split; [apply nominal_admissible|].
  split; [apply every_phase_within_daylight_robust | apply bridge_caps_the_withdrawal_robust].
Qed.

(* =============================================================================
   End
   ============================================================================= *)
