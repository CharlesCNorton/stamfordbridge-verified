(******************************************************************************)
(*                                                                            *)
(*               Battle of Stamford Bridge: Tactical Chronology               *)
(*                                                                            *)
(*   Formal model of the 25 September 1066 engagement and the Hastings march. *)
(*                                                                            *)
(*   Seofon fota Engliscre eorþan gife ic him, oþþe swa micle mare            *)
(*   swa he hierra bið þonne oþre menn.                                       *)
(*   - Harold's offer to Tostig for Harald Hardrada, after Heimskringla       *)
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
   Sources and tags
   =============================================================================

   [ASC-C]   Anglo-Saxon Chronicle, MS C, anno 1066.
   [ASC-C+]  The twelfth-century addition to MS C describing the bridge fight.
   [ASC-D]   Anglo-Saxon Chronicle, MS D, anno 1066.
   [HEIM]    Snorri Sturluson, Heimskringla, Saga of Harald Sigurdarson.
   [JW]      John of Worcester, Chronicon ex chronicis, anno 1066.

   [GEO]     Approximate mileage on modern maps along the Roman and medieval
             roads, or across country where the text says so.
   [ASTRO]   Sunrise and sunset computed for the Julian date at the site, in
             local apparent solar time.
   [RECON]   A date or figure from modern reconstruction that no primary
             source states.
   [MODEL]   A modelling assumption with no source.

   Where a [MODEL] constant carries a range, the theorems below quantify over
   it and name the range's end points.
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

(* The least q with ceil_div n d <= q is exactly the bound n <= q * d. *)
Lemma ceil_div_le_iff : forall n d q, 0 < d -> (ceil_div n d <= q <-> n <= q * d).
Proof.
  intros n d q Hd. split.
  - intros H. transitivity (ceil_div n d * d); [apply ceil_div_spec; exact Hd|].
    apply Z.mul_le_mono_nonneg_r; lia.
  - apply ceil_div_le; exact Hd.
Qed.

(* A threshold on an antitone function is exact when it succeeds and its predecessor fails. *)
Lemma threshold_antitone : forall (f : Z -> Z) bound lo,
  (forall s1 s2, 0 < s1 -> s1 <= s2 -> f s2 <= f s1) ->
  0 < lo - 1 -> f lo <= bound -> bound < f (lo - 1) ->
  forall s, 0 < s -> (f s <= bound <-> lo <= s).
Proof.
  intros f bound lo Hmono Hlo Hok Hbad s Hs. split.
  - intros H. destruct (Z.le_gt_cases lo s) as [Hge|Hlt]; [exact Hge|].
    assert (f (lo - 1) <= f s) by (apply Hmono; lia). lia.
  - intros H. transitivity (f lo); [apply Hmono; lia | exact Hok].
Qed.

Lemma rate_threshold_iff : forall n bound lo,
  0 <= n -> 0 < lo - 1 ->
  ceil_div n lo <= bound ->
  bound < ceil_div n (lo - 1) ->
  forall s, 0 < s -> (ceil_div n s <= bound <-> lo <= s).
Proof.
  intros n bound lo Hn Hlo Hok Hbad s Hs.
  refine (threshold_antitone (fun s => ceil_div n s) bound lo _ Hlo Hok Hbad s Hs).
  intros s1 s2 H1 H12. apply ceil_div_anti_mono; lia.
Qed.

(* A boolean property checked at every integer of a range holds on the range. *)
Fixpoint all_in (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f lo && all_in f (lo + 1) n'
  end.

Lemma all_in_spec : forall f n lo,
  all_in f lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|n IH]; intros lo H x Hx.
  - simpl in Hx. lia.
  - simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
    destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|].
    apply (IH (lo + 1) H2). rewrite Nat2Z.inj_succ in Hx. lia.
Qed.

Lemma all_in_range : forall f lo hi,
  all_in f lo (Z.to_nat (hi - lo + 1)) = true -> forall x, lo <= x <= hi -> f x = true.
Proof.
  intros f lo hi H x Hx.
  apply (all_in_spec f (Z.to_nat (hi - lo + 1)) lo H x).
  rewrite Z2Nat.id by lia. lia.
Qed.

(* =============================================================================
   Time
   ============================================================================= *)

Definition minutes_per_hour : Z := 60.
Definition hours_per_day : Z := 24.
Definition minutes_per_day : Z := hours_per_day * minutes_per_hour.

Definition day : Type := Z.
Definition time : Type := Z. (* minutes since 00:00 on 1 September 1066, Julian *)

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
  | William
  | EnglishHost
  | NorwegianHost.

Inductive location :=
  | London
  | Tadcaster
  | York
  | Fulford
  | Riccall
  | StamfordBridge
  | Hastings      (* the Senlac position at Battle *)
  | Pevensey.

Definition loc_eqb (a b : location) : bool :=
  match a, b with
  | London, London | Tadcaster, Tadcaster | York, York | Fulford, Fulford
  | Riccall, Riccall | StamfordBridge, StamfordBridge | Hastings, Hastings
  | Pevensey, Pevensey => true
  | _, _ => false
  end.

Lemma loc_eqb_refl : forall a, loc_eqb a a = true.
Proof. destruct a; reflexivity. Qed.

Lemma loc_eqb_eq : forall a b, loc_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; intros H; congruence. Qed.

Definition all_locations_list : list location :=
  [London; Tadcaster; York; Fulford; Riccall; StamfordBridge; Hastings; Pevensey].

Lemma all_locations_complete : forall l, In l all_locations_list.
Proof. destruct l; simpl; tauto. Qed.

(* Sentinel exceeding any sum of edges on this graph. *)
Definition INF : Z := 100000.

(* Direct edges only; every longer distance is a shortest path over them. *)
Definition direct_edges : list (location * location * Z) := [
  (London, Tadcaster, 180);      (* Ermine Street and the road north [GEO] *)
  (Tadcaster, York, 10);         (* the Roman road into York [GEO] *)
  (York, Fulford, 2);            (* Fulford lies just south of York [GEO] *)
  (York, Riccall, 10);           (* down the Ouse to the beached fleet [GEO] *)
  (York, StamfordBridge, 8);     (* east to the Derwent crossing [GEO] *)
  (Riccall, StamfordBridge, 13); (* across country, the line of flight [GEO] *)
  (London, Hastings, 58);        (* London to the Senlac position [GEO] *)
  (Pevensey, Hastings, 10)       (* the Norman beachhead to Senlac [GEO] *)
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

Definition loc_idx (l : location) : nat :=
  match l with
  | London => 0 | Tadcaster => 1 | York => 2 | Fulford => 3
  | Riccall => 4 | StamfordBridge => 5 | Hastings => 6 | Pevensey => 7
  end%nat.

Definition loc_of_idx (i : nat) : location :=
  match i with
  | 0 => London | 1 => Tadcaster | 2 => York | 3 => Fulford
  | 4 => Riccall | 5 => StamfordBridge | 6 => Hastings
  | _ => Pevensey
  end%nat.

Lemma loc_of_idx_inverse : forall l, loc_of_idx (loc_idx l) = l.
Proof. destruct l; reflexivity. Qed.

Definition n_locations : nat := 8%nat.

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

(* The closure never exceeds a direct edge. *)
Lemma dist_le_base : forall a b, dist a b <= base_dist a b.
Proof. destruct a, b; ground. Qed.

(* Every pair is connected: no distance is the sentinel. *)
Lemma dist_finite : forall a b, dist a b < INF.
Proof. destruct a, b; ground. Qed.

Definition miles_London_Tadcaster : Z := dist London Tadcaster.
Definition miles_London_York : Z := dist London York.
Definition miles_York_Stamford : Z := dist York StamfordBridge.
Definition miles_Tadcaster_Stamford : Z := dist Tadcaster StamfordBridge.
Definition miles_London_Hastings : Z := dist London Hastings.
Definition miles_Stamford_London : Z := dist StamfordBridge London.
Definition miles_Stamford_Hastings : Z := dist StamfordBridge Hastings.
Definition miles_Stamford_Riccall : Z := dist StamfordBridge Riccall.
Definition miles_Pevensey_York : Z := dist Pevensey York.

(* The southward distance is the via-London route. *)
Theorem stamford_hastings_via_london :
  miles_Stamford_Hastings
  = miles_York_Stamford + miles_London_York + miles_London_Hastings.
Proof. ground. Qed.

(* The line of flight to the ships is shorter than the road back through York. *)
Theorem flight_line_beats_road :
  miles_Stamford_Riccall < dist StamfordBridge York + dist York Riccall.
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

Definition route_north : list location := [London; Tadcaster; York; StamfordBridge].
Definition route_south : list location := [StamfordBridge; York; London; Hastings].
Definition route_full : list location :=
  [London; Tadcaster; York; StamfordBridge; York; London; Hastings].

Lemma route_north_distance : path_distance route_north = 198.
Proof. ground. Qed.

Lemma route_north_is_shortest : path_distance route_north = dist London StamfordBridge.
Proof. ground. Qed.

Lemma route_south_distance : path_distance route_south = miles_Stamford_Hastings.
Proof. ground. Qed.

Lemma route_full_distance : path_distance route_full = 454.
Proof. ground. Qed.

(* =============================================================================
   Calendar anchors, days since 1 September 1066
   ============================================================================= *)

Definition d_sep18 : day := 17.  (* Norwegian fleet beaches at Riccall [RECON] *)
Definition d_sep20 : day := 19.  (* Fulford, St Matthew's vigil [JW]; Harold quits London [RECON] *)
Definition d_sep24 : day := 23.  (* Harold reaches Tadcaster on the Sunday [ASC-C] *)
Definition d_sep25 : day := 24.  (* Stamford Bridge, the Monday [ASC-C] *)
Definition d_sep28 : day := 27.  (* William at Pevensey on Michaelmas eve [ASC-D] *)
Definition d_oct01 : day := 30.  (* Harold quits York for the south [RECON] *)
Definition d_oct07 : day := 36.  (* Harold reaches London [RECON] *)
Definition d_oct12 : day := 41.  (* Harold quits London [RECON] *)
Definition d_oct13 : day := 42.  (* Harold reaches the Senlac position [RECON] *)
Definition d_oct14 : day := 43.  (* Hastings, the feast of Pope Calixtus [ASC-D] *)

Lemma day_ordering :
  d_sep18 < d_sep20 /\ d_sep20 < d_sep24 /\ d_sep24 < d_sep25 /\ d_sep25 < d_sep28
  /\ d_sep28 < d_oct01 /\ d_oct01 < d_oct07 /\ d_oct07 < d_oct12
  /\ d_oct12 < d_oct13 /\ d_oct13 < d_oct14.
Proof.
  unfold d_sep18, d_sep20, d_sep24, d_sep25, d_sep28, d_oct01, d_oct07, d_oct12,
    d_oct13, d_oct14; repeat split; lia.
Qed.

(* 25 September Julian is 1 October Gregorian; York, latitude 54 N [ASTRO]. *)
Definition t_sep25_sunrise : time := t_of d_sep25 6 25.
Definition t_sep25_sunset : time := t_of d_sep25 17 35.
Definition t_sep25_first_light : time := t_of d_sep25 6 0.

(* 14 October Julian is 20 October Gregorian; Battle, latitude 51 N [ASTRO]. *)
Definition t_oct14_sunset : time := t_of d_oct14 17 0.

Definition in_sep25_daylight (t : time) : Prop :=
  t_sep25_sunrise <= t <= t_sep25_sunset.

(* =============================================================================
   Marching days
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

(* =============================================================================
   Forces
   ============================================================================= *)

Record force := {
  heavy : Z;    (* housecarls and hirdmen, the professional core *)
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

(* No source counts either army; the point estimates are modern [RECON]. *)
Definition english_force : force := {| heavy := 3000; light := 7000; archers := 1000 |}.

(* The army of some three hundred ships [ASC-D], at a strength of [RECON]. *)
Definition norse_force : force := {| heavy := 3600; light := 4500; archers := 900 |}.

(* Hardrada left a third of the army at the ships under Eystein Orre [HEIM]. *)
Definition norse_reserve : force := scale_force norse_force 1 3.
Definition norse_field : force := sub_force norse_force norse_reserve.

(* The field army stood on both banks when the English came on [ASC-C+]; halves [MODEL]. *)
Definition norse_west : force := scale_force norse_field 1 2.
Definition norse_east : force := sub_force norse_field norse_west.

Lemma norse_partition :
  add_force (add_force norse_west norse_east) norse_reserve = norse_force.
Proof. ground. Qed.

Lemma norse_partition_totals :
  force_total norse_west = 3000 /\ force_total norse_east = 3000
  /\ force_total norse_reserve = 3000 /\ force_total norse_force = 9000.
Proof. ground. Qed.

Lemma english_force_total : force_total english_force = 11000.
Proof. ground. Qed.

Lemma english_force_wf : force_wf english_force.
Proof. ground. Qed.

Lemma norse_west_wf : force_wf norse_west.
Proof. ground. Qed.

(* Modern ranges for the whole of each army [RECON]. *)
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
   Numerical superiority over the ranges
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

(* Some admissible pair of totals has the Norse the larger. *)
Theorem english_superiority_not_universal :
  exists e n, english_in_range e /\ norse_in_range n /\ e < n.
Proof.
  exists english_total_low, norse_total_high.
  unfold english_in_range, norse_in_range,
    english_total_low, english_total_high, norse_total_low, norse_total_high.
  repeat split; lia.
Qed.

(* With a third of the Norse at the ships, no admissible field army outnumbers an
   admissible English host. *)
Theorem english_outnumber_the_field : forall e n,
  english_in_range e -> norse_in_range n -> n - n / 3 <= e.
Proof.
  intros e n He Hn.
  unfold english_in_range, norse_in_range, english_total_low, english_total_high,
    norse_total_low, norse_total_high in *.
  pose proof (Z.div_mod n 3 ltac:(lia)). pose proof (Z.mod_pos_bound n 3 ltac:(lia)).
  lia.
Qed.

Theorem english_superiority_at_estimates :
  force_total norse_field < force_total english_force.
Proof. ground. Qed.

(* =============================================================================
   Phase schedule
   ============================================================================= *)

Inductive phase :=
  | Approach        (* English deployment west of the Derwent [ASC-C+] *)
  | BridgeDefender  (* the lone Norseman holds the span [ASC-C+] *)
  | BridgeHold      (* the English force the crossing [ASC-C+] *)
  | ShieldWall      (* the main action at the shield ring [HEIM] *)
  | Rout.           (* the Norse collapse and Orre's storm [HEIM] *)

(* Six boundaries delimiting five consecutive phases. *)
Record schedule := {
  b0 : time;  (* contact west of the river *)
  b1 : time;  (* the Norseman takes the bridge *)
  b2 : time;  (* he falls and the English force the span *)
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

(* No source times the phases; the nominal reconstruction is [MODEL]. *)
Definition nominal : schedule := {|
  b0 := t_of d_sep25 10 30;
  b1 := t_of d_sep25 11 15;
  b2 := t_of d_sep25 12 0;
  b3 := t_of d_sep25 12 30;
  b4 := t_of d_sep25 15 30;
  b5 := t_of d_sep25 16 45
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

Lemma nominal_phase_durations :
  phase_duration nominal Approach = 45 /\
  phase_duration nominal BridgeDefender = 45 /\
  phase_duration nominal BridgeHold = 30 /\
  phase_duration nominal ShieldWall = 180 /\
  phase_duration nominal Rout = 75.
Proof. ground. Qed.

(* -----------------------------------------------------------------------------
   Uncertainty band on the schedule
   -------------------------------------------------------------------------- *)

(* Each boundary is admitted within half an hour of its nominal time [MODEL]. *)
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

Ltac admissible_bounds HS :=
  destruct HS as [Hord [H0 [H1 [H2 [H3 [H4 H5]]]]]];
  unfold near, sched_tolerance, nominal, t_of, d_sep25, minutes_per_day,
    hours_per_day, minutes_per_hour in H0, H1, H2, H3, H4, H5;
  cbn [b0 b1 b2 b3 b4 b5] in H0, H1, H2, H3, H4, H5;
  unfold sched_ordered in Hord.

Theorem every_phase_within_daylight_robust : forall S p,
  sched_admissible S ->
  in_sep25_daylight (phase_start S p) /\ in_sep25_daylight (phase_end S p).
Proof.
  intros S p HS. admissible_bounds HS.
  unfold in_sep25_daylight, t_sep25_sunrise, t_sep25_sunset, t_of, d_sep25,
    minutes_per_day, hours_per_day, minutes_per_hour.
  destruct p; simpl; split; lia.
Qed.

(* -----------------------------------------------------------------------------
   The approach march from Tadcaster
   -------------------------------------------------------------------------- *)

(* Harold went through York on the Monday [ASC-C], leaving Tadcaster at first light [MODEL]. *)
Definition approach_minutes (mph : Z) : Z := ceil_div (60 * miles_Tadcaster_Stamford) mph.

Definition approach_arrives_by (mph : Z) (t : time) : Prop :=
  t_sep25_first_light + approach_minutes mph <= t.

(* Contact at the nominal hour needs four miles an hour, and three is too slow. *)
Theorem approach_pace_nominal : forall v, 0 < v ->
  (approach_arrives_by v (b0 nominal) <-> 4 <= v).
Proof.
  intros v Hv. unfold approach_arrives_by.
  assert (Hd : b0 nominal - t_sep25_first_light = 270) by ground.
  assert (Hiff : approach_minutes v <= 270 <-> 4 <= v).
  { unfold approach_minutes.
    apply rate_threshold_iff; [ground | lia | ground | ground | exact Hv]. }
  rewrite <- Hiff. lia.
Qed.

(* At five miles an hour the march reaches the field before every admissible contact. *)
Theorem approach_pace_robust : forall S,
  sched_admissible S -> approach_arrives_by 5 (b0 S).
Proof.
  intros S HS.
  assert (Hm : approach_minutes 5 = 216) by ground.
  unfold approach_arrives_by. rewrite Hm.
  admissible_bounds HS.
  unfold t_sep25_first_light, t_of, d_sep25, minutes_per_day, hours_per_day,
    minutes_per_hour. lia.
Qed.

(* Four miles an hour misses the earliest admissible contact. *)
Theorem approach_pace_robust_is_tight :
  exists S, sched_admissible S /\ ~ approach_arrives_by 4 (b0 S).
Proof.
  exists {| b0 := t_of d_sep25 10 0; b1 := b1 nominal; b2 := b2 nominal;
            b3 := b3 nominal; b4 := b4 nominal; b5 := b5 nominal |}.
  split; [unfold sched_admissible, near, sched_tolerance; ground|].
  assert (Hm : approach_minutes 4 = 270) by ground.
  unfold approach_arrives_by. rewrite Hm.
  unfold t_sep25_first_light, t_of, d_sep25, minutes_per_day, hours_per_day,
    minutes_per_hour. cbn [b0]. lia.
Qed.

(* =============================================================================
   Phase-specific combat effectiveness
   ============================================================================= *)

(* Weights out of ten for what each troop type is worth in each phase [MODEL]. *)
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

(* Equal totals differ in effectiveness by phase. *)
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

Definition man_width_cm : Z := 60.        (* frontage of one man under arms [MODEL] *)
Definition bridge_width_cm : Z := 240.    (* a narrow timber span [MODEL] *)
Definition axe_reach_cm : Z := 250.       (* arc swept by a two-handed axe [MODEL] *)
Definition file_rate : Z := 3.            (* men per minute per file, contested [MODEL] *)

(* Men who fit abreast on a span of the given width. *)
Definition frontage (w : Z) : Z := w / man_width_cm.

Lemma frontage_mono : forall w1 w2, w1 <= w2 -> frontage w1 <= frontage w2.
Proof. intros; unfold frontage; apply Z.div_le_mono; [unfold man_width_cm; lia|lia]. Qed.

Lemma frontage_nonneg : forall w, 0 <= w -> 0 <= frontage w.
Proof. intros; unfold frontage; apply Z.div_pos; [lia | unfold man_width_cm; lia]. Qed.

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

(* One axeman covers the span, as the one Norseman of [ASC-C+] held it. *)
Theorem lone_axeman_blocks_bridge : span_blocked 1 bridge_width_cm.
Proof. unfold span_blocked, bridge_width_cm, axe_reach_cm; lia. Qed.

(* The same man could not block a span one file wider. *)
Theorem lone_axeman_bound_is_tight :
  ~ span_blocked 1 (bridge_width_cm + man_width_cm).
Proof. unfold span_blocked, bridge_width_cm, man_width_cm, axe_reach_cm; lia. Qed.

(* Crossing rate is the product of frontage and per-file pace. *)
Definition max_crossing_rate (w : Z) : Z := frontage w * file_rate.

Definition bulk_crossing_rate : Z := max_crossing_rate bridge_width_cm.

Lemma bulk_crossing_rate_value : bulk_crossing_rate = 12.
Proof. ground. Qed.

Theorem crossing_rate_from_width : forall w1 w2,
  w1 <= w2 -> max_crossing_rate w1 <= max_crossing_rate w2.
Proof.
  intros w1 w2 H. unfold max_crossing_rate.
  apply Z.mul_le_mono_nonneg_r; [unfold file_rate; lia | apply frontage_mono; exact H].
Qed.

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

Theorem crossing_rate_bounded : forall w d,
  0 <= w -> 0 <= d -> crossing_rate_at w d <= max_crossing_rate w.
Proof.
  intros w d Hw Hd. unfold crossing_rate_at, max_crossing_rate.
  pose proof (frontage_nonneg w Hw) as Hfr.
  destruct (Z.leb w (d * axe_reach_cm)) eqn:E.
  - apply Z.mul_nonneg_nonneg; [exact Hfr | unfold file_rate; lia].
  - apply Z.mul_le_mono_nonneg_r; [unfold file_rate; lia | lia].
Qed.

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

Theorem blocked_span_admits_none : forall w d,
  span_blocked d w -> crossing_rate_at w d = 0.
Proof.
  intros w d H. unfold crossing_rate_at, span_blocked in *.
  destruct (Z.leb w (d * axe_reach_cm)) eqn:E; [reflexivity|].
  apply Z.leb_gt in E. lia.
Qed.

Corollary lone_axeman_stops_the_crossing : crossing_rate_at bridge_width_cm 1 = 0.
Proof. apply blocked_span_admits_none, lone_axeman_blocks_bridge. Qed.

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
  0 < force_total f -> force_total f - n <= force_total (attrit f n).
Proof.
  intros f n Ht. unfold attrit.
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

(* Attrition never raises effectiveness in any phase. *)
Lemma attrit_effectiveness_le : forall p f n,
  force_wf f -> 0 <= n -> effectiveness p (attrit f n) <= effectiveness p f.
Proof.
  intros p f n [Hh [Hl Ha]] Hn. unfold attrit, force_total. cbv zeta.
  destruct (Z.leb (heavy f + light f + archers f) 0) eqn:E; [lia|].
  apply Z.leb_gt in E.
  unfold effectiveness; cbn [heavy light archers].
  assert (0 <= n * heavy f / (heavy f + light f + archers f))
    by (apply Z.div_pos; nia).
  assert (0 <= n * light f / (heavy f + light f + archers f))
    by (apply Z.div_pos; nia).
  assert (0 <= n * archers f / (heavy f + light f + archers f))
    by (apply Z.div_pos; nia).
  destruct p; cbv [w_heavy w_light w_archers]; lia.
Qed.

(* Losses a force inflicts across a phase, from its effectiveness, the clock and a divisor. *)
Definition losses_at (div : Z) (S : schedule) (p : phase) (attacker : force) : Z :=
  effectiveness p attacker * phase_duration S p / div.

(* Divisors for the opening phases and the rout [MODEL]. *)
Definition lethality (p : phase) : Z :=
  match p with
  | Approach => 60000        (* skirmish and missile exchange *)
  | BridgeDefender => 400000 (* the blocked span costs almost nothing *)
  | BridgeHold => 40000      (* forcing the span *)
  | ShieldWall => 3500       (* losses the English take at the shield ring *)
  | Rout => 12000            (* broken men and Orre's storm *)
  end.

Lemma lethality_pos : forall p, 0 < lethality p.
Proof. destruct p; unfold lethality; lia. Qed.

Definition losses_inflicted (S : schedule) (p : phase) (attacker : force) : Z :=
  losses_at (lethality p) S p attacker.

Lemma losses_at_nonneg : forall div S p f,
  0 < div -> force_wf f -> 0 <= phase_duration S p -> 0 <= losses_at div S p f.
Proof.
  intros div S p f Hdiv Hf Hd. unfold losses_at.
  apply Z.div_pos; [| exact Hdiv].
  apply Z.mul_nonneg_nonneg; [apply effectiveness_nonneg; exact Hf | exact Hd].
Qed.

(* Losses are bounded by any bound on the attacker's effectiveness and on the clock. *)
Lemma losses_at_bounded : forall div S p f e0 d0,
  0 < div -> effectiveness p f <= e0 -> 0 <= e0 ->
  0 <= phase_duration S p <= d0 ->
  losses_at div S p f <= e0 * d0 / div.
Proof.
  intros div S p f e0 d0 Hdiv He He0 Hd. unfold losses_at.
  apply Z.div_le_mono; [exact Hdiv|]. nia.
Qed.

Theorem losses_monotone_in_effectiveness : forall div S p f g,
  0 < div -> 0 <= phase_duration S p ->
  effectiveness p f <= effectiveness p g ->
  losses_at div S p f <= losses_at div S p g.
Proof.
  intros div S p f g Hdiv Hd Hfg. unfold losses_at.
  apply Z.div_le_mono; [exact Hdiv|].
  apply Z.mul_le_mono_nonneg_r; assumption.
Qed.

(* =============================================================================
   The bridge and the withdrawal
   ============================================================================= *)

(* The west-bank force withdraws while the approach and the stand run. *)
Definition withdrawal_window (S : schedule) : Z :=
  phase_duration S Approach + phase_duration S BridgeDefender.

Definition eng_after_approach (S : schedule) : force :=
  attrit english_force (losses_inflicted S Approach norse_west).
Definition nw_after_approach (S : schedule) : force :=
  attrit norse_west (losses_inflicted S Approach english_force).

Definition eng_after_defender (S : schedule) : force :=
  attrit (eng_after_approach S)
         (losses_inflicted S BridgeDefender (nw_after_approach S)).
Definition nw_after_defender (S : schedule) : force :=
  attrit (nw_after_approach S)
         (losses_inflicted S BridgeDefender (eng_after_approach S)).

(* The span's crossing rate caps how many west-bank men reach the east bank. *)
Definition west_withdrawn_count (S : schedule) : Z :=
  Z.min (force_total (nw_after_defender S)) (bulk_crossing_rate * withdrawal_window S).

Definition west_withdrawn (S : schedule) : force :=
  scale_force (nw_after_defender S) (west_withdrawn_count S)
              (force_total (nw_after_defender S)).

Definition west_remnant (S : schedule) : force :=
  sub_force (nw_after_defender S) (west_withdrawn S).

Definition eng_after_hold (S : schedule) : force :=
  attrit (eng_after_defender S) (losses_inflicted S BridgeHold (west_remnant S)).

(* The men who crossed joined the shield ring Hardrada formed east of the river [HEIM]. *)
Definition norse_shieldwall (S : schedule) : force :=
  add_force norse_east (west_withdrawn S).

Theorem bridge_caps_the_withdrawal :
  west_withdrawn_count nominal < force_total (nw_after_defender nominal).
Proof. ground. Qed.

(* Every admissible schedule leaves the withdrawal window at most two and a half hours. *)
Lemma withdrawal_window_bounded : forall S,
  sched_admissible S -> 0 <= withdrawal_window S <= 150.
Proof.
  intros S HS. admissible_bounds HS.
  unfold withdrawal_window, phase_duration, duration, phase_start, phase_end. lia.
Qed.

Lemma withdrawal_window_bound_is_tight :
  exists S, sched_admissible S /\ withdrawal_window S = 150.
Proof.
  exists {| b0 := t_of d_sep25 10 0; b1 := b1 nominal; b2 := t_of d_sep25 12 30;
            b3 := t_of d_sep25 12 45; b4 := b4 nominal; b5 := b5 nominal |}.
  split; [unfold sched_admissible, near, sched_tolerance; ground | ground].
Qed.

(* The west bank keeps at least 2906 men through the stand under every admissible schedule. *)
Lemma west_bank_strength_robust : forall S,
  sched_admissible S -> 2906 <= force_total (nw_after_defender S).
Proof.
  intros S HS.
  assert (HA : 0 <= phase_duration S Approach <= 105 /\
               0 <= phase_duration S BridgeDefender <= 105).
  { admissible_bounds HS. unfold phase_duration, duration, phase_start, phase_end. lia. }
  destruct HA as [HA HD].
  assert (HlA : losses_inflicted S Approach english_force <= 82).
  { unfold losses_inflicted.
    pose proof (losses_at_bounded (lethality Approach) S Approach english_force
                  (effectiveness Approach english_force) 105
                  ltac:(ground) ltac:(lia) ltac:(ground) HA) as H.
    assert (Hc : effectiveness Approach english_force * 105 / lethality Approach = 82)
      by ground.
    lia. }
  assert (Hnw1 : 2918 <= force_total (nw_after_approach S)).
  { unfold nw_after_approach.
    pose proof (attrit_total_lower_bound norse_west
                  (losses_inflicted S Approach english_force) ltac:(ground)).
    assert (force_total norse_west = 3000) by ground. lia. }
  assert (He1 : effectiveness BridgeDefender (eng_after_approach S)
                <= effectiveness BridgeDefender english_force).
  { unfold eng_after_approach. apply attrit_effectiveness_le; [exact english_force_wf|].
    apply losses_at_nonneg; [ground | exact norse_west_wf | lia]. }
  assert (HlD : losses_inflicted S BridgeDefender (eng_after_approach S) <= 12).
  { unfold losses_inflicted.
    pose proof (losses_at_bounded (lethality BridgeDefender) S BridgeDefender
                  (eng_after_approach S) (effectiveness BridgeDefender english_force) 105
                  ltac:(ground) He1 ltac:(ground) HD) as H.
    assert (Hc : effectiveness BridgeDefender english_force * 105
                 / lethality BridgeDefender = 12) by ground.
    lia. }
  unfold nw_after_defender.
  pose proof (attrit_total_lower_bound (nw_after_approach S)
                (losses_inflicted S BridgeDefender (eng_after_approach S))
                ltac:(lia)).
  lia.
Qed.

(* The span binds for every admissible schedule: the west bank cannot all withdraw. *)
Theorem bridge_caps_the_withdrawal_robust : forall S,
  sched_admissible S ->
  bulk_crossing_rate * withdrawal_window S < force_total (nw_after_defender S).
Proof.
  intros S HS.
  pose proof (withdrawal_window_bounded S HS).
  pose proof (west_bank_strength_robust S HS).
  rewrite bulk_crossing_rate_value. lia.
Qed.

(* =============================================================================
   The shield ring
   ============================================================================= *)

(* Divisors for the losses each side takes at the ring [MODEL]: the defenders on the
   rise take one man for every three the same effectiveness costs the attackers. *)
Definition wall_div_english : Z := lethality ShieldWall.
Definition wall_div_norse : Z := 3 * wall_div_english.

(* The two forces that meet at the ring under the nominal schedule, evaluated once. *)
Definition english_at_ring : force := Eval vm_compute in eng_after_hold nominal.
Definition norse_at_ring : force := Eval vm_compute in norse_shieldwall nominal.

Lemma english_at_ring_eq : english_at_ring = eng_after_hold nominal.
Proof. vm_compute; reflexivity. Qed.

Lemma norse_at_ring_eq : norse_at_ring = norse_shieldwall nominal.
Proof. vm_compute; reflexivity. Qed.

Definition eng_after_wall_with (de : Z) : force :=
  attrit english_at_ring (losses_at de nominal ShieldWall norse_at_ring).

Definition norse_after_wall_with (dn : Z) : force :=
  attrit norse_at_ring (losses_at dn nominal ShieldWall english_at_ring).

Definition eng_after_wall : force := eng_after_wall_with wall_div_english.
Definition norse_after_wall : force := norse_after_wall_with wall_div_norse.

(* =============================================================================
   The rout
   ============================================================================= *)

(* A force breaks when the enemy's effectiveness reaches q per cent of its own. *)
Definition breaks (q own enemy : Z) : Prop := q * own <= 100 * enemy.
Definition breaksb (q own enemy : Z) : bool := q * own <=? 100 * enemy.

Lemma breaksb_spec : forall q own enemy, breaksb q own enemy = true <-> breaks q own enemy.
Proof. intros; unfold breaksb, breaks; apply Z.leb_le. Qed.

(* Hardrada's fall cost the line part of its cohesion [HEIM]; the share kept [MODEL]. *)
Definition leaderless_pct : Z := 60.

Definition led_effectiveness (pct : Z) (f : force) : Z :=
  effectiveness ShieldWall f * pct / 100.

Definition norse_eff_led_with (dn : Z) : Z := effectiveness ShieldWall (norse_after_wall_with dn).
Definition norse_eff_leaderless_with (dn pct : Z) : Z :=
  led_effectiveness pct (norse_after_wall_with dn).
Definition english_eff_at_wall_with (de : Z) : Z :=
  effectiveness ShieldWall (eng_after_wall_with de).

Definition norse_eff_led : Z := norse_eff_led_with wall_div_norse.
Definition norse_eff_leaderless : Z := norse_eff_leaderless_with wall_div_norse leaderless_pct.
Definition english_eff_at_wall : Z := english_eff_at_wall_with wall_div_english.

(* The narrative at the ring: the Norse hold while Hardrada stands, break when he falls,
   and the English never break. *)
Definition narrative_at (q nled nll e : Z) : Prop :=
  ~ breaks q nled e /\ breaks q nll e /\ ~ breaks q e nled.

Definition narrative_atb (q nled nll e : Z) : bool :=
  negb (breaksb q nled e) && breaksb q nll e && negb (breaksb q e nled).

Lemma narrative_atb_spec : forall q nled nll e,
  narrative_atb q nled nll e = true -> narrative_at q nled nll e.
Proof.
  intros q nled nll e H. unfold narrative_atb in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1, H3.
  unfold narrative_at, breaks. unfold breaksb in *.
  apply Z.leb_le in H2. apply Z.leb_gt in H1, H3. lia.
Qed.

Lemma rout_inputs :
  norse_eff_led = 19120 /\ norse_eff_leaderless = 11472
  /\ english_eff_at_wall = 53596.
Proof. ground. Qed.

(* The thresholds that reproduce the narrative form exactly one interval. *)
Theorem rout_threshold_band : forall q,
  narrative_at q norse_eff_led norse_eff_leaderless english_eff_at_wall
  <-> 281 <= q <= 467.
Proof.
  intros q. destruct rout_inputs as [H1 [H2 H3]].
  rewrite H1, H2, H3. unfold narrative_at, breaks. lia.
Qed.

(* The threshold used below, the middle of that band [MODEL]. *)
Definition rout_q : Z := 374.

Lemma rout_q_in_band : 281 <= rout_q <= 467.
Proof. unfold rout_q; lia. Qed.

Theorem no_rout_while_hardrada_stands : ~ breaks rout_q norse_eff_led english_eff_at_wall.
Proof. exact (proj1 (proj2 (rout_threshold_band rout_q) rout_q_in_band)). Qed.

Theorem rout_follows_hardradas_fall : breaks rout_q norse_eff_leaderless english_eff_at_wall.
Proof. exact (proj1 (proj2 (proj2 (rout_threshold_band rout_q) rout_q_in_band))). Qed.

Theorem english_never_rout : ~ breaks rout_q english_eff_at_wall norse_eff_led.
Proof. exact (proj2 (proj2 (proj2 (rout_threshold_band rout_q) rout_q_in_band))). Qed.

(* At that threshold the break follows the fall for every retained share up to 74%,
   and a share of 75% or more keeps the line standing. *)
Theorem leaderless_share_band : forall pct, 0 <= pct <= 100 ->
  (breaks rout_q (norse_eff_leaderless_with wall_div_norse pct) english_eff_at_wall
   <-> pct <= 74).
Proof.
  intros pct Hp.
  assert (Hc : all_in (fun p => Bool.eqb
                  (breaksb rout_q (norse_eff_leaderless_with wall_div_norse p)
                           english_eff_at_wall)
                  (p <=? 74)) 0 (Z.to_nat (100 - 0 + 1)) = true) by (vm_compute; reflexivity).
  pose proof (all_in_range _ 0 100 Hc pct Hp) as H. simpl in H.
  apply Bool.eqb_prop in H. rewrite <- breaksb_spec, H. apply Z.leb_le.
Qed.

(* =============================================================================
   Pursuit, Orre's storm, and the returning ships
   ============================================================================= *)

Definition flight_miles : Z := miles_Stamford_Riccall.
Definition flight_speed_mph : Z := 4.                   (* broken men, part in mail [MODEL] *)
Definition pursuit_speed_mph : Z := 5.                  (* English light foot [MODEL] *)

(* Head start, in minutes, at which a fugitive reaches the ships uncaught. *)
Definition escape_head_start : Z :=
  60 * flight_miles * (pursuit_speed_mph - flight_speed_mph)
  / (flight_speed_mph * pursuit_speed_mph).

(* Eystein Orre's men came up from the ships and held the pursuit [HEIM]; delay [MODEL]. *)
Definition pursuit_delay : Z := 60.

Definition escape_window_with (d : Z) : Z := Z.max 0 (d - escape_head_start).

Definition road_width_cm : Z := 480.   (* the track out of the field [MODEL] *)
Definition flight_file_rate : Z := 5.  (* men per minute per file, running [MODEL] *)

Definition break_rate (fr : Z) : Z := frontage road_width_cm * fr.

(* Olaf stayed with the ships [HEIM]; the guard left with him [MODEL]. *)
Definition ship_guard : Z := 150.

(* Orre's men were for the most part killed [HEIM]; only the ship guard survives them. *)
Definition orre_force : force :=
  scale_force norse_reserve (force_total norse_reserve - ship_guard) (force_total norse_reserve).

Definition survivors_with (fr d : Z) : Z :=
  Z.min (force_total norse_after_wall) (break_rate fr * escape_window_with d) + ship_guard.

Definition norse_survivors : Z := survivors_with flight_file_rate pursuit_delay.
Definition norse_losses_total : Z := force_total norse_force - norse_survivors.

Lemma escape_head_start_value : escape_head_start = 39.
Proof. ground. Qed.

Lemma pursuit_inputs :
  force_total norse_after_wall = 3035 /\ frontage road_width_cm = 8
  /\ force_total norse_force = 9000.
Proof. ground. Qed.

(* While the fugitives the road lets through number fewer than the survivors of the ring,
   the survivors are linear in the flight rate and the delay. *)
Lemma survivors_formula : forall fr d,
  0 <= fr -> 39 <= d -> 8 * fr * (d - 39) <= 3035 ->
  survivors_with fr d = 8 * fr * (d - 39) + 150.
Proof.
  intros fr d Hfr Hd Hcap. destruct pursuit_inputs as [Hn [Hf _]].
  unfold survivors_with, escape_window_with, break_rate, ship_guard.
  rewrite Hn, Hf, escape_head_start_value.
  rewrite Z.max_r by lia. rewrite Z.min_r by lia. ring.
Qed.

Lemma norse_survivors_value : norse_survivors = 990.
Proof. ground. Qed.

(* Pursuit faster than flight is what makes the head start finite. *)
Theorem escape_needs_a_head_start :
  flight_speed_mph < pursuit_speed_mph /\ 0 < escape_head_start.
Proof. ground. Qed.

Theorem norse_losses_exceed_four_fifths :
  8 * force_total norse_force <= 10 * norse_losses_total.
Proof. ground. Qed.

Definition four_fifths_lost (s : Z) : Prop := 8 * 9000 <= 10 * (9000 - s).

(* Four fifths are lost for every flight rate up to nine men per file per minute. *)
Theorem norse_losses_band_in_flight_rate : forall fr,
  0 <= fr <= 10 -> (four_fifths_lost (survivors_with fr pursuit_delay) <-> fr <= 9).
Proof.
  intros fr Hfr. unfold pursuit_delay.
  rewrite survivors_formula by lia. unfold four_fifths_lost. lia.
Qed.

(* Four fifths are lost for every pursuit delay up to 80 minutes. *)
Theorem norse_losses_band_in_pursuit_delay : forall d,
  39 <= d <= 90 -> (four_fifths_lost (survivors_with flight_file_rate d) <-> d <= 80).
Proof.
  intros d Hd. unfold flight_file_rate.
  rewrite survivors_formula by lia. unfold four_fifths_lost. lia.
Qed.

(* -----------------------------------------------------------------------------
   The twenty-four ships
   -------------------------------------------------------------------------- *)

(* The king let the survivors go home with twenty-four ships [ASC-D]. *)
Definition ships_reported : Z := 24.
Definition ship_capacity_low : Z := 30.   (* [MODEL] *)
Definition ship_capacity_high : Z := 50.  (* [MODEL] *)

Definition ships_for (men capacity : Z) : Z := ceil_div men capacity.

(* The reported fleet is between the fewest and the most hulls the survivors need. *)
Definition ships_bracket (men : Z) : Prop :=
  ships_for men ship_capacity_high <= ships_reported <= ships_for men ship_capacity_low.

(* The bracket holds for exactly the survivor counts from 691 to 1200. *)
Theorem ships_bracket_iff : forall men, (ships_bracket men <-> 691 <= men <= 1200).
Proof.
  intros men. unfold ships_bracket, ships_for, ships_reported,
    ship_capacity_low, ship_capacity_high.
  rewrite (ceil_div_le_iff men 50 24) by lia.
  assert (Hlow : 24 <= ceil_div men 30 <-> 691 <= men).
  { split.
    - intros H. destruct (Z.le_gt_cases 691 men) as [Hge|Hlt]; [exact Hge|].
      assert (ceil_div men 30 <= 23) by (apply ceil_div_le; lia). lia.
    - intros H. destruct (Z.le_gt_cases 24 (ceil_div men 30)) as [Hge|Hlt]; [exact Hge|].
      assert (men <= 23 * 30) by (apply (ceil_div_le_iff men 30 23); lia). lia. }
  rewrite <- Hlow. lia.
Qed.

Theorem reported_ships_within_model_bracket : ships_bracket norse_survivors.
Proof. apply ships_bracket_iff. rewrite norse_survivors_value. lia. Qed.

(* The ships fix the flight rate: they fit flight rates four to six and no others. *)
Theorem ships_fix_the_flight_rate : forall fr,
  0 <= fr <= 10 -> (ships_bracket (survivors_with fr pursuit_delay) <-> 4 <= fr <= 6).
Proof.
  intros fr Hfr. rewrite ships_bracket_iff. unfold pursuit_delay.
  rewrite survivors_formula by lia. lia.
Qed.

(* The ships fix the pursuit delay to between 53 and 65 minutes. *)
Theorem ships_fix_the_pursuit_delay : forall d,
  39 <= d <= 90 -> (ships_bracket (survivors_with flight_file_rate d) <-> 53 <= d <= 65).
Proof.
  intros d Hd. rewrite ships_bracket_iff. unfold flight_file_rate.
  rewrite survivors_formula by lia. lia.
Qed.

(* =============================================================================
   English losses
   ============================================================================= *)

Definition rout_efficiency_pct : Z := 10.  (* what a broken line still returns [MODEL] *)
(* Orre's men ran from the ships in mail [HEIM]; the share of effectiveness kept [MODEL]. *)
Definition orre_efficiency_pct : Z := 50.

(* Orre's contribution to the rout, evaluated once. *)
Definition orre_in_rout : force :=
  Eval vm_compute in scale_force orre_force orre_efficiency_pct 100.

Lemma orre_in_rout_eq : orre_in_rout = scale_force orre_force orre_efficiency_pct 100.
Proof. vm_compute; reflexivity. Qed.

Definition rout_attackers_with (dn : Z) : force :=
  add_force (scale_force (norse_after_wall_with dn) rout_efficiency_pct 100) orre_in_rout.

Definition eng_after_rout_with (de dn : Z) : force :=
  attrit (eng_after_wall_with de) (losses_inflicted nominal Rout (rout_attackers_with dn)).

Definition english_losses_with (de dn : Z) : Z :=
  force_total english_force - force_total (eng_after_rout_with de dn).

Definition english_losses_total : Z := english_losses_with wall_div_english wall_div_norse.

Lemma english_losses_value : english_losses_total = 1406.
Proof. ground. Qed.

(* The tradition calls the English losses heavy; heavy is a tenth to a third [MODEL]. *)
Definition english_heavy_low : Z := 1100.
Definition english_heavy_high : Z := 3666.

Theorem english_losses_heavy :
  english_heavy_low <= english_losses_total <= english_heavy_high.
Proof. ground. Qed.

Theorem norse_losses_exceed_english_fivefold :
  5 * english_losses_total < norse_losses_total.
Proof. ground. Qed.

(* -----------------------------------------------------------------------------
   Robustness in the shield-ring divisors
   -------------------------------------------------------------------------- *)

(* Every headline conclusion of the battle, as one boolean check on the two divisors. *)
Definition battle_outcome_ok (de dn : Z) : bool :=
  let el := english_losses_with de dn in
  (english_heavy_low <=? el) && (el <=? english_heavy_high)
  && narrative_atb rout_q (norse_eff_led_with dn)
       (norse_eff_leaderless_with dn leaderless_pct) (english_eff_at_wall_with de)
  && (8 * force_total norse_force <=? 10 * (force_total norse_force
        - (Z.min (force_total (norse_after_wall_with dn))
                 (break_rate flight_file_rate * escape_window_with pursuit_delay)
           + ship_guard))).

Lemma battle_outcome_ok_spec : forall de dn,
  battle_outcome_ok de dn = true ->
  english_heavy_low <= english_losses_with de dn <= english_heavy_high
  /\ narrative_at rout_q (norse_eff_led_with dn)
       (norse_eff_leaderless_with dn leaderless_pct) (english_eff_at_wall_with de).
Proof.
  intros de dn H. unfold battle_outcome_ok in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hn].
  apply andb_true_iff in H as [Hl Hh].
  apply Z.leb_le in Hl, Hh.
  split; [lia | apply narrative_atb_spec; exact Hn].
Qed.

Lemma battle_outcome_nominal : battle_outcome_ok wall_div_english wall_div_norse = true.
Proof. vm_compute; reflexivity. Qed.

(* The English divisor may range over 1424..4551 with the Norse divisor fixed. *)
Theorem battle_robust_in_english_divisor : forall de,
  1424 <= de <= 4551 -> battle_outcome_ok de wall_div_norse = true.
Proof.
  apply (all_in_range (fun de => battle_outcome_ok de wall_div_norse)).
  vm_compute; reflexivity.
Qed.

(* The Norse divisor may range over 6072..38072 with the English divisor fixed. *)
Theorem battle_robust_in_norse_divisor : forall dn,
  6072 <= dn <= 38072 -> battle_outcome_ok wall_div_english dn = true.
Proof.
  apply (all_in_range (fun dn => battle_outcome_ok wall_div_english dn)).
  vm_compute; reflexivity.
Qed.

Theorem battle_divisor_bands_are_tight :
  battle_outcome_ok 1423 wall_div_norse = false
  /\ battle_outcome_ok 4552 wall_div_norse = false
  /\ battle_outcome_ok wall_div_english 6071 = false
  /\ battle_outcome_ok wall_div_english 38073 = false.
Proof. vm_compute; repeat split; reflexivity. Qed.

(* =============================================================================
   The southward march, with the London halt
   ============================================================================= *)

(* The host's march rate, fresh, in miles a day [MODEL]. *)
Definition rate_south_base : Z := 30.
Definition rate_north : Z := 40.   (* the forced march to Tadcaster [MODEL] *)

(* March capacity after r rest days, recovering from the battle [MODEL]. *)
Definition fatigue_pct : Z := 70.
Definition recovery_per_day : Z := 6.

Definition recovered_pct (rest : Z) : Z := Z.min 100 (fatigue_pct + recovery_per_day * rest).

Definition march_rate_after (base rest : Z) : Z := base * recovered_pct rest / 100.

Lemma recovered_pct_caps_at_full : forall rest, 5 <= rest -> recovered_pct rest = 100.
Proof.
  intros rest H. unfold recovered_pct, fatigue_pct, recovery_per_day.
  apply Z.min_l. lia.
Qed.

Lemma march_rate_full_recovery : forall base rest,
  5 <= rest -> march_rate_after base rest = base.
Proof.
  intros base rest H. unfold march_rate_after.
  rewrite (recovered_pct_caps_at_full rest H). apply Z.div_mul. lia.
Qed.

(* The host leaves York after r rest days, halts h whole days in London, and must
   stand at Senlac by 13 October. *)
Definition york_departure (rest : Z) : day := d_sep25 + 1 + rest.

Definition london_arrival (base rest : Z) : day :=
  york_departure rest + travel_days miles_London_York (march_rate_after base rest) - 1.

Definition london_departure (base rest halt : Z) : day :=
  london_arrival base rest + 1 + halt.

Definition senlac_arrival (base rest halt : Z) : day :=
  london_departure base rest halt
  + travel_days miles_London_Hastings (march_rate_after base rest) - 1.

Definition itinerary_feasible (base rest halt : Z) : Prop :=
  senlac_arrival base rest halt <= d_oct13.

(* The historical plan: five rest days at York, four whole days in London. *)
Definition historical_rest : Z := 5.
Definition historical_halt : Z := 4.

Theorem historical_itinerary_matches_dates :
  york_departure historical_rest = d_oct01
  /\ london_arrival rate_south_base historical_rest = d_oct07
  /\ london_departure rate_south_base historical_rest historical_halt = d_oct12
  /\ senlac_arrival rate_south_base historical_rest historical_halt = d_oct13.
Proof. ground. Qed.

(* The whole London halt that each choice of rest leaves, at the base rate. *)
Definition halt_budget (rest : Z) : Z :=
  if rest <? 3 then 5 else if rest <? 5 then 4 else 9 - rest.

Lemma senlac_arrival_halt : forall base rest halt,
  senlac_arrival base rest halt = senlac_arrival base rest 0 + halt.
Proof. intros. unfold senlac_arrival, london_departure. lia. Qed.

(* The feasible region is exactly the halts within the budget. *)
Theorem itinerary_region : forall rest halt,
  0 <= rest -> 0 <= halt ->
  (itinerary_feasible rate_south_base rest halt <-> halt <= halt_budget rest).
Proof.
  intros rest halt Hr Hh. unfold itinerary_feasible.
  rewrite senlac_arrival_halt.
  destruct (Z.le_gt_cases 5 rest) as [H5|H5].
  - assert (Hb : senlac_arrival rate_south_base rest 0 = 33 + rest).
    { unfold senlac_arrival, london_departure, london_arrival, york_departure.
      rewrite (march_rate_full_recovery rate_south_base rest H5).
      assert (travel_days miles_London_York rate_south_base = 7) by ground.
      assert (travel_days miles_London_Hastings rate_south_base = 2) by ground.
      unfold d_sep25. lia. }
    rewrite Hb. unfold halt_budget, d_oct13.
    destruct (rest <? 3) eqn:E3; [apply Z.ltb_lt in E3; lia|].
    destruct (rest <? 5) eqn:E5; [apply Z.ltb_lt in E5; lia|]. lia.
  - assert (Hc : rest = 0 \/ rest = 1 \/ rest = 2 \/ rest = 3 \/ rest = 4) by lia.
    destruct Hc as [E|[E|[E|[E|E]]]]; subst rest;
      [ assert (Hb : senlac_arrival rate_south_base 0 0 = 37) by ground
      | assert (Hb : senlac_arrival rate_south_base 1 0 = 37) by ground
      | assert (Hb : senlac_arrival rate_south_base 2 0 = 37) by ground
      | assert (Hb : senlac_arrival rate_south_base 3 0 = 38) by ground
      | assert (Hb : senlac_arrival rate_south_base 4 0 = 38) by ground ];
      rewrite Hb; unfold d_oct13;
      match goal with
      | |- context [halt_budget ?r] =>
          let v := eval vm_compute in (halt_budget r) in change (halt_budget r) with v
      end; lia.
Qed.

(* The historical plan lies on the boundary: one more day at York or in London fails. *)
Theorem historical_itinerary_has_no_slack :
  itinerary_feasible rate_south_base historical_rest historical_halt
  /\ ~ itinerary_feasible rate_south_base (historical_rest + 1) historical_halt
  /\ ~ itinerary_feasible rate_south_base historical_rest (historical_halt + 1).
Proof.
  unfold historical_rest, historical_halt.
  rewrite !itinerary_region by lia.
  unfold halt_budget; cbn. lia.
Qed.

(* No choice of rest buys a London halt longer than five days. *)
Theorem london_halt_at_most_five : forall rest halt,
  0 <= rest -> 0 <= halt -> itinerary_feasible rate_south_base rest halt -> halt <= 5.
Proof.
  intros rest halt Hr Hh H. apply itinerary_region in H; [|lia|lia].
  unfold halt_budget in H.
  destruct (rest <? 3); [lia|].
  destruct (rest <? 5) eqn:E5; [lia|]. apply Z.ltb_ge in E5. lia.
Qed.

(* -----------------------------------------------------------------------------
   Rates the dated itinerary demands
   -------------------------------------------------------------------------- *)

(* Marching days for the two southward legs at a sustained rate. *)
Definition south_legs_days (s : Z) : Z :=
  travel_days miles_London_York s + travel_days miles_London_Hastings s.

(* On the dated itinerary the host needs at least 29 miles a day, and 28 fails. *)
Theorem itinerary_minimum_rate : forall s, 0 < s ->
  (south_legs_days s <= leg_days d_oct01 d_oct07 + leg_days d_oct12 d_oct13 <-> 29 <= s).
Proof.
  intros s Hs.
  refine (threshold_antitone south_legs_days
            (leg_days d_oct01 d_oct07 + leg_days d_oct12 d_oct13) 29 _
            ltac:(lia) ltac:(ground) ltac:(ground) s Hs).
  intros s1 s2 H1 H12. unfold south_legs_days.
  pose proof (travel_days_rate_anti_mono miles_London_York s1 s2 ltac:(ground) H1 H12).
  pose proof (travel_days_rate_anti_mono miles_London_Hastings s1 s2 ltac:(ground) H1 H12).
  lia.
Qed.

(* With the historical rest the plan is feasible iff the base rate reaches 29. *)
Theorem historical_plan_needs_base_rate : forall base, 0 < base ->
  (itinerary_feasible base historical_rest historical_halt <-> 29 <= base).
Proof.
  intros base Hb. unfold itinerary_feasible, senlac_arrival, london_departure,
    london_arrival, historical_rest, historical_halt.
  rewrite (march_rate_full_recovery base 5) by lia.
  rewrite <- (itinerary_minimum_rate base Hb).
  unfold south_legs_days, york_departure, leg_days, d_sep25, d_oct01, d_oct07,
    d_oct12, d_oct13. lia.
Qed.

Definition leg1_depart : day := d_sep20.
Definition leg1_arrive : day := d_sep24.
Definition leg3a_depart : day := d_oct01.
Definition leg3a_arrive : day := d_oct07.
Definition leg3b_depart : day := d_oct12.
Definition leg3b_arrive : day := d_oct13.

Theorem leg1_minimum_rate : forall s, 0 < s ->
  (leg_fits leg1_depart leg1_arrive miles_London_Tadcaster s <-> 36 <= s).
Proof.
  intros s Hs. unfold leg_fits, travel_days.
  apply rate_threshold_iff; [ground | lia | ground | ground | exact Hs].
Qed.

Theorem leg3a_minimum_rate : forall s, 0 < s ->
  (leg_fits leg3a_depart leg3a_arrive miles_London_York s <-> 28 <= s).
Proof.
  intros s Hs. unfold leg_fits, travel_days.
  apply rate_threshold_iff; [ground | lia | ground | ground | exact Hs].
Qed.

Theorem leg3b_minimum_rate : forall s, 0 < s ->
  (leg_fits leg3b_depart leg3b_arrive miles_London_Hastings s <-> 29 <= s).
Proof.
  intros s Hs. unfold leg_fits, travel_days.
  apply rate_threshold_iff; [ground | lia | ground | ground | exact Hs].
Qed.

Theorem leg1_fits : leg_fits leg1_depart leg1_arrive miles_London_Tadcaster rate_north.
Proof. apply leg1_minimum_rate; unfold rate_north; lia. Qed.

(* -----------------------------------------------------------------------------
   News of the landing
   -------------------------------------------------------------------------- *)

Definition t_william_lands : time := t_of d_sep28 12 0.  (* hour [MODEL] *)
Definition t_march_south : time := t_of d_oct01 6 0.     (* hour [MODEL] *)

(* Minutes a rider at the given miles a day needs from Pevensey to York. *)
Definition news_minutes (miles_per_day : Z) : Z :=
  ceil_div (miles_Pevensey_York * minutes_per_day) miles_per_day.

(* The march south answers the landing only if news ran at least 94 miles a day. *)
Theorem news_minimum_rate : forall v, 0 < v ->
  (t_william_lands + news_minutes v <= t_march_south <-> 94 <= v).
Proof.
  intros v Hv.
  assert (Hd : t_march_south - t_william_lands = 3960) by ground.
  assert (Hiff : news_minutes v <= 3960 <-> 94 <= v).
  { unfold news_minutes. apply rate_threshold_iff; [ground | lia | ground | ground | exact Hv]. }
  rewrite <- Hiff. lia.
Qed.

(* =============================================================================
   Supply
   ============================================================================= *)

(* A week of rations carried and the rest requisitioned from the shires [MODEL]. *)
Definition rations_carried : Z := 7.
Definition resupply_capacity : Z := 12000.

Definition campaign_days : Z := d_oct14 - d_sep20.

Lemma campaign_days_value : campaign_days = 24.
Proof. ground. Qed.

(* Stock in man-days: what was carried, plus daily requisition, less consumption. *)
Definition supply_remaining (n d : Z) : Z :=
  rations_carried * n + Z.min resupply_capacity n * d - n * d.

Definition non_starving (n d : Z) : Prop := 0 < supply_remaining n d.

Theorem supply_holds_below_capacity : forall n d,
  0 < n <= resupply_capacity -> 0 <= d -> non_starving n d.
Proof.
  intros n d Hn Hd. unfold non_starving, supply_remaining, rations_carried.
  rewrite Z.min_r by lia. lia.
Qed.

Lemma supply_above_capacity : forall n d,
  resupply_capacity <= n ->
  supply_remaining n d = rations_carried * n - (n - resupply_capacity) * d.
Proof.
  intros n d H. unfold supply_remaining. rewrite Z.min_l by lia. lia.
Qed.

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

Theorem supply_holds_across_norse_range : forall n d,
  norse_in_range n -> 0 <= d <= campaign_days -> non_starving n d.
Proof.
  intros n d Hn Hd. unfold norse_in_range, norse_total_low, norse_total_high in Hn.
  apply supply_holds_below_capacity; [unfold resupply_capacity; lia | lia].
Qed.

(* The largest host the campaign feeds for its whole length. *)
Theorem supply_capacity_boundary :
  non_starving 16941 campaign_days /\ ~ non_starving 16942 campaign_days.
Proof.
  unfold non_starving, supply_remaining, rations_carried, resupply_capacity.
  rewrite campaign_days_value, !Z.min_l by lia. split; lia.
Qed.

Theorem supply_boundary_exceeds_every_estimate :
  english_total_high < 16941 /\ norse_total_high < 16941.
Proof. unfold english_total_high, norse_total_high; split; lia. Qed.

(* =============================================================================
   Chronology
   ============================================================================= *)

Inductive event_name :=
  | Landing
  | MarchNorthBegins
  | FulfordBattle
  | YorkTaken
  | TadcasterArrive
  | ApproachStart
  | Contact
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

Record timeline := {
  t_landing : time;
  t_london_depart : time;
  t_fulford : time;
  t_york_taken : time;
  t_tadcaster_arrive : time;
  t_approach_start : time;
  t_contact : time;
  t_bridge_defense : time;
  t_stamford_start : time;
  t_hardrada_fall : time;
  t_stamford_end : time;
  t_recovery : time;
  t_william_lands_at : time;
  t_march_south_start : time;
  t_london_arrive : time;
  t_london_depart_south : time;
  t_hastings_start : time;
  t_hastings_end : time
}.

(* The causal order the narrative fixes; a partial order on the events. *)
Record chronology (T : timeline) : Prop := {
  landing_before_fulford : t_landing T < t_fulford T;
  landing_before_london_depart : t_landing T < t_london_depart T;
  fulford_before_york_taken : t_fulford T < t_york_taken T;
  london_depart_before_tadcaster : t_london_depart T < t_tadcaster_arrive T;
  york_taken_before_approach : t_york_taken T <= t_approach_start T;
  tadcaster_before_approach : t_tadcaster_arrive T <= t_approach_start T;
  approach_before_contact : t_approach_start T < t_contact T;
  contact_before_bridge : t_contact T <= t_bridge_defense T;
  bridge_before_stamford : t_bridge_defense T <= t_stamford_start T;
  stamford_start_before_end : t_stamford_start T < t_stamford_end T;
  hardrada_falls_after_start : t_stamford_start T <= t_hardrada_fall T;
  hardrada_falls_before_end : t_hardrada_fall T <= t_stamford_end T;
  stamford_end_before_recovery : t_stamford_end T <= t_recovery T;
  stamford_end_before_william : t_stamford_end T < t_william_lands_at T;
  recovery_before_march_south : t_recovery T <= t_march_south_start T;
  william_before_march_south : t_william_lands_at T < t_march_south_start T;
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

Definition events_of (T : timeline) : list event :=
  [ {| e_name := Landing; e_time := t_landing T;
       e_loc := Riccall; e_actor := NorwegianHost |};
    {| e_name := MarchNorthBegins; e_time := t_london_depart T;
       e_loc := London; e_actor := EnglishHost |};
    {| e_name := FulfordBattle; e_time := t_fulford T;
       e_loc := Fulford; e_actor := NorwegianHost |};
    {| e_name := YorkTaken; e_time := t_york_taken T;
       e_loc := York; e_actor := NorwegianHost |};
    {| e_name := TadcasterArrive; e_time := t_tadcaster_arrive T;
       e_loc := Tadcaster; e_actor := EnglishHost |};
    {| e_name := ApproachStart; e_time := t_approach_start T;
       e_loc := Tadcaster; e_actor := EnglishHost |};
    {| e_name := Contact; e_time := t_contact T;
       e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := BridgeDefenseBegins; e_time := t_bridge_defense T;
       e_loc := StamfordBridge; e_actor := NorwegianHost |};
    {| e_name := StamfordBattleBegins; e_time := t_stamford_start T;
       e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := HardradaFalls; e_time := t_hardrada_fall T;
       e_loc := StamfordBridge; e_actor := Hardrada |};
    {| e_name := StamfordBattleEnds; e_time := t_stamford_end T;
       e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := EnglishRecovery; e_time := t_recovery T;
       e_loc := StamfordBridge; e_actor := Harold |};
    {| e_name := WilliamLands; e_time := t_william_lands_at T;
       e_loc := Pevensey; e_actor := William |};
    {| e_name := MarchSouthBegins; e_time := t_march_south_start T;
       e_loc := York; e_actor := EnglishHost |};
    {| e_name := LondonArrive; e_time := t_london_arrive T;
       e_loc := London; e_actor := EnglishHost |};
    {| e_name := LondonDepart; e_time := t_london_depart_south T;
       e_loc := London; e_actor := EnglishHost |};
    {| e_name := HastingsBattleBegins; e_time := t_hastings_start T;
       e_loc := Hastings; e_actor := EnglishHost |};
    {| e_name := HastingsBattleEnds; e_time := t_hastings_end T;
       e_loc := Hastings; e_actor := EnglishHost |}
  ].

(* The listed order is a linear extension of the chronology once the three pairs it
   leaves unordered are fixed. *)
Theorem chronology_orders_events : forall T,
  chronology T ->
  t_london_depart T <= t_fulford T ->
  t_york_taken T <= t_tadcaster_arrive T ->
  t_recovery T <= t_william_lands_at T ->
  sorted_by_time (events_of T).
Proof.
  intros T Hc H1 H2 H3. destruct Hc. simpl. repeat split; lia.
Qed.

(* =============================================================================
   The historical timeline
   ============================================================================= *)

Definition T_historical : timeline := {|
  t_landing := t_of d_sep18 12 0;             (* fleet beaches at Riccall [RECON] *)
  t_london_depart := t_of d_sep20 6 0;        (* Harold quits London [RECON] *)
  t_fulford := t_of d_sep20 9 0;              (* Fulford [JW]; hour [MODEL] *)
  t_york_taken := t_of d_sep24 12 0;          (* York gives hostages [ASC-C]; date [RECON] *)
  t_tadcaster_arrive := t_of d_sep24 18 0;    (* Harold at Tadcaster [ASC-C]; hour [MODEL] *)
  t_approach_start := t_sep25_first_light;    (* the march through York [ASC-C] *)
  t_contact := b0 nominal;                    (* contact west of the Derwent *)
  t_bridge_defense := b1 nominal;             (* the Norseman takes the span [ASC-C+] *)
  t_stamford_start := b3 nominal;             (* the shield walls meet [HEIM] *)
  t_hardrada_fall := b4 nominal;              (* Hardrada, an arrow in the throat [HEIM] *)
  t_stamford_end := b5 nominal;               (* the pursuit ends *)
  t_recovery := t_sep25_sunset;               (* the English hold the field *)
  t_william_lands_at := t_william_lands;      (* Normans at Pevensey [ASC-D] *)
  t_march_south_start := t_march_south;       (* Harold quits York [RECON] *)
  t_london_arrive := t_of d_oct07 18 0;       (* Harold reaches London [RECON] *)
  t_london_depart_south := t_of d_oct12 6 0;  (* Harold quits London [RECON] *)
  t_hastings_start := t_of d_oct14 9 0;       (* from the third hour [JW] *)
  t_hastings_end := t_oct14_sunset            (* until dusk [JW] *)
|}.

Theorem chronology_T_historical : chronology T_historical.
Proof. constructor; ground. Qed.

Definition events_historical : list event := events_of T_historical.

Theorem events_historical_sorted : sorted_by_time events_historical.
Proof.
  apply chronology_orders_events; [exact chronology_T_historical | ground | ground | ground].
Qed.

(* The dated days of the timeline are the days of the itinerary model. *)
Theorem timeline_matches_itinerary :
  t_march_south_start T_historical / minutes_per_day
    = york_departure historical_rest
  /\ t_london_arrive T_historical / minutes_per_day
    = london_arrival rate_south_base historical_rest
  /\ t_london_depart_south T_historical / minutes_per_day
    = london_departure rate_south_base historical_rest historical_halt.
Proof. ground. Qed.

Theorem historical_battle_in_daylight :
  in_sep25_daylight (t_stamford_start T_historical)
  /\ in_sep25_daylight (t_stamford_end T_historical).
Proof. ground. Qed.

(* =============================================================================
   Computed values
   ============================================================================= *)

Example v_dist_london_tadcaster : miles_London_Tadcaster = 180.
Proof. ground. Qed.

Example v_dist_london_york : miles_London_York = 190.
Proof. ground. Qed.

Example v_dist_tadcaster_stamford : miles_Tadcaster_Stamford = 18.
Proof. ground. Qed.

Example v_dist_stamford_hastings : miles_Stamford_Hastings = 256.
Proof. ground. Qed.

Example v_dist_stamford_riccall : miles_Stamford_Riccall = 13.
Proof. ground. Qed.

Example v_dist_pevensey_york : miles_Pevensey_York = 258.
Proof. ground. Qed.

Example v_bridge_frontage : frontage bridge_width_cm = 4.
Proof. ground. Qed.

Example v_withdrawal_window : withdrawal_window nominal = 90.
Proof. ground. Qed.

Example v_west_after_defender : force_total (nw_after_defender nominal) = 2963.
Proof. ground. Qed.

Example v_west_withdrawn : west_withdrawn_count nominal = 1080.
Proof. ground. Qed.

Example v_norse_shieldwall : force_total (norse_shieldwall nominal) = 4078.
Proof. ground. Qed.

Example v_norse_after_wall : force_total norse_after_wall = 3035.
Proof. ground. Qed.

Example v_english_after_wall : force_total eng_after_wall = 9665.
Proof. ground. Qed.

Example v_escape_window : escape_window_with pursuit_delay = 21.
Proof. ground. Qed.

Example v_norse_survivors : norse_survivors = 990.
Proof. ground. Qed.

Example v_norse_losses : norse_losses_total = 8010.
Proof. ground. Qed.

Example v_english_losses : english_losses_total = 1406.
Proof. ground. Qed.

Example v_supply_at_point_estimate : supply_remaining 11000 campaign_days = 77000.
Proof. ground. Qed.

(* =============================================================================
   Headline results
   ============================================================================= *)

(* The bridge stand follows from the span's width and an axe's reach. *)
Theorem headline_bridge_geometry :
  span_blocked 1 bridge_width_cm
  /\ crossing_rate_at bridge_width_cm 1 = 0
  /\ crossing_rate_at bridge_width_cm 0 = bulk_crossing_rate
  /\ ~ span_blocked 1 (bridge_width_cm + man_width_cm)
  /\ (forall S, sched_admissible S ->
      bulk_crossing_rate * withdrawal_window S < force_total (nw_after_defender S)).
Proof.
  split; [apply lone_axeman_blocks_bridge|].
  split; [apply lone_axeman_stops_the_crossing|].
  split; [apply cleared_span_runs_at_ceiling|].
  split; [apply lone_axeman_bound_is_tight | apply bridge_caps_the_withdrawal_robust].
Qed.

(* The narrative at the ring holds for exactly one interval of break thresholds. *)
Theorem headline_rout :
  (forall q, narrative_at q norse_eff_led norse_eff_leaderless english_eff_at_wall
             <-> 281 <= q <= 467)
  /\ (forall pct, 0 <= pct <= 100 ->
      (breaks rout_q (norse_eff_leaderless_with wall_div_norse pct) english_eff_at_wall
       <-> pct <= 74)).
Proof. split; [apply rout_threshold_band | apply leaderless_share_band]. Qed.

(* Heavy English losses and the narrative hold across both shield-ring divisor bands. *)
Theorem headline_battle_robustness :
  (forall de, 1424 <= de <= 4551 ->
     english_heavy_low <= english_losses_with de wall_div_norse <= english_heavy_high
     /\ narrative_at rout_q (norse_eff_led_with wall_div_norse)
          (norse_eff_leaderless_with wall_div_norse leaderless_pct)
          (english_eff_at_wall_with de))
  /\ (forall dn, 6072 <= dn <= 38072 ->
     english_heavy_low <= english_losses_with wall_div_english dn <= english_heavy_high
     /\ narrative_at rout_q (norse_eff_led_with dn)
          (norse_eff_leaderless_with dn leaderless_pct)
          (english_eff_at_wall_with wall_div_english)).
Proof.
  split; intros x Hx; apply battle_outcome_ok_spec;
    [apply battle_robust_in_english_divisor | apply battle_robust_in_norse_divisor]; exact Hx.
Qed.

(* Four fifths of the army is lost, and the twenty-four ships pin the pursuit. *)
Theorem headline_norse_annihilation :
  8 * force_total norse_force <= 10 * norse_losses_total
  /\ ships_bracket norse_survivors
  /\ (forall men, ships_bracket men <-> 691 <= men <= 1200)
  /\ (forall fr, 0 <= fr <= 10 ->
      (ships_bracket (survivors_with fr pursuit_delay) <-> 4 <= fr <= 6)).
Proof.
  split; [apply norse_losses_exceed_four_fifths|].
  split; [apply reported_ships_within_model_bracket|].
  split; [apply ships_bracket_iff | apply ships_fix_the_flight_rate].
Qed.

(* With the London halt the historical plan has no spare day, and needs 29 miles a day. *)
Theorem headline_itinerary :
  (forall rest halt, 0 <= rest -> 0 <= halt ->
     (itinerary_feasible rate_south_base rest halt <-> halt <= halt_budget rest))
  /\ ~ itinerary_feasible rate_south_base (historical_rest + 1) historical_halt
  /\ ~ itinerary_feasible rate_south_base historical_rest (historical_halt + 1)
  /\ (forall base, 0 < base ->
      (itinerary_feasible base historical_rest historical_halt <-> 29 <= base)).
Proof.
  split; [apply itinerary_region|].
  destruct historical_itinerary_has_no_slack as [_ [H1 H2]].
  split; [exact H1|]. split; [exact H2 | apply historical_plan_needs_base_rate].
Qed.

(* Exact minimum rates the dated legs, the approach and the news of Pevensey demand. *)
Theorem headline_rate_thresholds :
  (forall s, 0 < s -> (leg_fits leg1_depart leg1_arrive miles_London_Tadcaster s <-> 36 <= s))
  /\ (forall s, 0 < s -> (leg_fits leg3a_depart leg3a_arrive miles_London_York s <-> 28 <= s))
  /\ (forall s, 0 < s -> (leg_fits leg3b_depart leg3b_arrive miles_London_Hastings s <-> 29 <= s))
  /\ (forall v, 0 < v -> (approach_arrives_by v (b0 nominal) <-> 4 <= v))
  /\ (forall v, 0 < v -> (t_william_lands + news_minutes v <= t_march_south <-> 94 <= v)).
Proof.
  split; [apply leg1_minimum_rate|].
  split; [apply leg3a_minimum_rate|].
  split; [apply leg3b_minimum_rate|].
  split; [apply approach_pace_nominal | apply news_minimum_rate].
Qed.

Theorem headline_superiority :
  (forall e, english_in_range e ->
     ((forall n, norse_in_range n -> n < e) <-> norse_total_high < e))
  /\ (exists e n, english_in_range e /\ norse_in_range n /\ e < n).
Proof.
  split; [apply english_superiority_exact | apply english_superiority_not_universal].
Qed.

Theorem headline_supply :
  (forall e d, english_in_range e -> 0 <= d <= campaign_days -> non_starving e d)
  /\ (forall n d, norse_in_range n -> 0 <= d <= campaign_days -> non_starving n d)
  /\ ~ non_starving 16942 campaign_days.
Proof.
  split; [apply supply_holds_across_english_range|].
  split; [apply supply_holds_across_norse_range | exact (proj2 supply_capacity_boundary)].
Qed.

Theorem headline_historical_timeline :
  chronology T_historical
  /\ sorted_by_time events_historical
  /\ senlac_arrival rate_south_base historical_rest historical_halt = d_oct13.
Proof.
  split; [apply chronology_T_historical|].
  split; [apply events_historical_sorted | ground].
Qed.

Theorem headline_schedule_robustness :
  sched_admissible nominal
  /\ (forall S p, sched_admissible S ->
      in_sep25_daylight (phase_start S p) /\ in_sep25_daylight (phase_end S p))
  /\ (forall S, sched_admissible S -> approach_arrives_by 5 (b0 S))
  /\ (exists S, sched_admissible S /\ ~ approach_arrives_by 4 (b0 S)).
Proof.
  split; [apply nominal_admissible|].
  split; [apply every_phase_within_daylight_robust|].
  split; [apply approach_pace_robust | apply approach_pace_robust_is_tight].
Qed.

(* =============================================================================
   End
   ============================================================================= *)
