(******************************************************************************)
(*                                                                            *)
(*               Battle of Stamford Bridge: Tactical Chronology               *)
(*                                                                            *)
(*     Formalizes the engagement of 25 September 1066: Harold Godwinson's     *)
(*     forced march from London, Norwegian army disposition across the        *)
(*     River Derwent, bridge chokepoint defense, and rout of Harald           *)
(*     Hardrada's forces. Proves timeline constraints on the Hastings march.  *)
(*                                                                            *)
(*     Seofon fot Engliscre eorthan ic him gife, oththe mare, swa micel       *)
(*     swa he hierra bith thonne othre menn.                                  *)
(*     - Harold Godwinson's offer to Harald Hardrada, 1066                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 7, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith Bool Lia List PeanoNat.
Import ListNotations.

(* Large nat literals are interpreted via Init.Nat.of_num_uint to avoid stack
   overflow during typechecking; this is intentional and not a defect. *)
Set Warnings "-abstract-large-number".

Open Scope nat_scope.

(* =============================================================================
   Time model
   ============================================================================= *)

Definition minutes_per_hour : nat := 60.
Definition hours_per_day : nat := 24.
Definition minutes_per_day : nat := hours_per_day * minutes_per_hour.

Definition day : Type := nat.
Definition time : Type := nat. (* minutes since epoch *)

Definition t_of (d h m : nat) : time :=
  d * minutes_per_day + h * minutes_per_hour + m.

Definition duration (t1 t2 : time) : nat := t2 - t1.

Lemma minutes_per_day_pos : minutes_per_day > 0.
Proof. unfold minutes_per_day, hours_per_day, minutes_per_hour; lia. Qed.

Lemma t_of_day_mono : forall d1 d2 h1 h2 m1 m2,
  h1 < hours_per_day -> m1 < minutes_per_hour ->
  h2 < hours_per_day -> m2 < minutes_per_hour ->
  d1 < d2 -> t_of d1 h1 m1 < t_of d2 h2 m2.
Proof.
  intros d1 d2 h1 h2 m1 m2 Hh1 Hm1 Hh2 Hm2 Hd.
  unfold t_of, minutes_per_day, hours_per_day, minutes_per_hour in *.
  nia.
Qed.

Lemma duration_pos : forall t1 t2, t1 < t2 -> duration t1 t2 > 0.
Proof.
  intros; unfold duration; lia.
Qed.

(* WARNING: duration uses nat subtraction. Calling duration t2 t1 when t2 > t1
   silently returns 0, not a negative value. Always ensure t1 <= t2. *)
Lemma duration_reversed_zero : forall t1 t2, t2 <= t1 -> duration t1 t2 = 0.
Proof.
  intros; unfold duration; lia.
Qed.

Lemma duration_order_matters : forall t1 t2,
  t1 < t2 -> duration t1 t2 > 0 /\ duration t2 t1 = 0.
Proof.
  intros; unfold duration; split; lia.
Qed.

(* =============================================================================
   Logistics and travel
   ============================================================================= *)

Definition ceil_div (n d : nat) : nat := (n + d - 1) / d.

Definition travel_days (distance speed : nat) : nat := ceil_div distance speed.
Definition travel_minutes (distance speed : nat) : nat := travel_days distance speed * minutes_per_day.

Lemma travel_days_zero : forall speed, speed > 0 -> travel_days 0 speed = 0.
Proof.
  intros speed Hs.
  unfold travel_days, ceil_div.
  destruct speed as [|s]; [lia|].
  replace (0 + S s - 1) with s by lia.
  apply Nat.div_small; lia.
Qed.

Lemma travel_days_monotone : forall d1 d2 s,
  s > 0 -> d1 <= d2 -> travel_days d1 s <= travel_days d2 s.
Proof.
  intros d1 d2 s Hs Hle.
  unfold travel_days, ceil_div.
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma travel_minutes_monotone : forall d1 d2 s,
  s > 0 -> d1 <= d2 -> travel_minutes d1 s <= travel_minutes d2 s.
Proof.
  intros; unfold travel_minutes.
  apply Nat.mul_le_mono_r.
  now apply travel_days_monotone.
Qed.

(* =============================================================================
   Actors and locations
   ============================================================================= *)

Inductive actor :=
  | Harold
  | Hardrada
  | Tostig
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

(* Sentinel value for "no path"; larger than any plausible sum of edges. *)
Definition INF : nat := 100000.

(* Direct edges of the campaign graph. Land routes between the eight English
   locations, plus naval-access edges to NorthSea: the Humber-Ouse approach
   to Riccall (where the Norwegian fleet beached) and the Channel approach to
   Hastings (which became William's landing area at Pevensey). All other
   distances are computed by Floyd-Warshall over this edge list. *)
Definition direct_edges : list (location * location * nat) := [
  (London, York, 190);
  (York, Fulford, 2);
  (York, Riccall, 8);
  (York, Tadcaster, 10);
  (York, StamfordBridge, 10);
  (Riccall, StamfordBridge, 12);
  (StamfordBridge, Derwent, 1);
  (StamfordBridge, Hastings, 210);
  (NorthSea, Riccall, 60);
  (NorthSea, Hastings, 200)
].

Fixpoint find_edge_dist (es : list (location * location * nat)) (a b : location) : nat :=
  match es with
  | [] => INF
  | (x, y, d) :: rest =>
      if (loc_eqb a x && loc_eqb b y) || (loc_eqb a y && loc_eqb b x)
      then d
      else find_edge_dist rest a b
  end.

Definition base_dist (a b : location) : nat :=
  if loc_eqb a b then 0 else find_edge_dist direct_edges a b.

(* Index each location for matrix-based Floyd-Warshall. The matrix-of-lists
   representation avoids the closure-chain blow-up that a function-typed
   relaxation would suffer at vm_compute time on a 9-node graph. *)
Definition loc_idx (l : location) : nat :=
  match l with
  | London => 0 | York => 1 | StamfordBridge => 2 | Hastings => 3
  | Tadcaster => 4 | Derwent => 5 | Riccall => 6 | Fulford => 7
  | NorthSea => 8
  end.

Definition loc_of_idx (i : nat) : location :=
  match i with
  | 0 => London | 1 => York | 2 => StamfordBridge | 3 => Hastings
  | 4 => Tadcaster | 5 => Derwent | 6 => Riccall | 7 => Fulford
  | _ => NorthSea
  end.

Definition n_locations : nat := 9.

Definition mat_get (m : list (list nat)) (i j : nat) : nat :=
  nth j (nth i m []) INF.

Definition init_matrix : list (list nat) :=
  map (fun i => map (fun j => base_dist (loc_of_idx i) (loc_of_idx j))
                    (seq 0 n_locations))
      (seq 0 n_locations).

(* One Floyd-Warshall pass: relax all pairs (i,j) through intermediate k. *)
Definition mat_relax (m : list (list nat)) (k : nat) : list (list nat) :=
  map (fun i => map (fun j => Nat.min (mat_get m i j)
                                      (mat_get m i k + mat_get m k j))
                    (seq 0 n_locations))
      (seq 0 n_locations).

Definition mat_fw (m : list (list nat)) : list (list nat) :=
  fold_left mat_relax (seq 0 n_locations) m.

Definition dist_table : list (list nat) :=
  Eval vm_compute in mat_fw init_matrix.

Definition dist (a b : location) : nat :=
  mat_get dist_table (loc_idx a) (loc_idx b).

Lemma dist_zero : forall a, dist a a = 0.
Proof. destruct a; vm_compute; reflexivity. Qed.

Lemma dist_sym : forall a b, dist a b = dist b a.
Proof. destruct a, b; vm_compute; reflexivity. Qed.

Lemma dist_triangle : forall a b c, dist a c <= dist a b + dist b c.
Proof. intros a b c; destruct a, b, c; vm_compute; lia. Qed.

(* =============================================================================
   Calendar anchors (days since Sep 1, 1066)
   ============================================================================= *)

Definition d_sep18 : day := 17.  (* Norwegian fleet lands at Riccall *)
Definition d_sep20 : day := 19.  (* Battle of Fulford *)
Definition d_sep24 : day := 23.  (* York submits *)
Definition d_sep25 : day := 24.  (* Battle of Stamford Bridge *)
Definition d_sep26 : day := 25.
Definition d_sep27 : day := 26.
Definition d_oct01 : day := 30.
Definition d_oct14 : day := 43.

Definition t_sep25_noon : time := t_of d_sep25 12 0.
Definition t_sep25_evening : time := t_of d_sep25 18 0.
Definition t_oct14_dawn : time := t_of d_oct14 6 0.
Definition t_oct14_morning : time := t_of d_oct14 9 0.

Lemma day_ordering :
  d_sep18 < d_sep20 /\ d_sep20 < d_sep24 /\ d_sep24 < d_sep25 /\
  d_sep25 < d_sep26 /\ d_sep26 < d_sep27 /\ d_sep27 < d_oct01 /\ d_oct01 < d_oct14.
Proof.
  unfold d_sep18, d_sep20, d_sep24, d_sep25, d_sep26, d_sep27, d_oct01, d_oct14; lia.
Qed.

Lemma sep25_before_oct14 : t_sep25_noon < t_oct14_dawn.
Proof.
  unfold t_sep25_noon, t_oct14_dawn, t_of, d_sep25, d_oct14;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

Lemma sep25_evening_before_oct14_morning : t_sep25_evening < t_oct14_morning.
Proof.
  unfold t_sep25_evening, t_oct14_morning, t_of, d_sep25, d_oct14;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

Lemma days_between_sep25_oct14 :
  duration t_sep25_noon t_oct14_dawn / minutes_per_day = 18.
Proof.
  unfold duration, t_sep25_noon, t_oct14_dawn, t_of, d_sep25, d_oct14;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; reflexivity.
Qed.

(* =============================================================================
   Tactical chronology (events and ordering)
   ============================================================================= *)

Inductive event_name :=
  | Landing
  | FulfordBattle
  | YorkTaken
  | MarchNorthBegins
  | YorkArrive
  | ApproachStart
  | MarchNorthEnds
  | BridgeDefenseBegins
  | StamfordBattleBegins
  | StamfordBattleEnds
  | HardradaFalls
  | EnglishRecovery
  | MarchSouthBegins
  | HastingsBattleBegins
  | HastingsBattleEnds.

Record event := {
  e_name : event_name;
  e_time : time;
  e_loc : location;
  e_actor : actor
}.

Definition before (e1 e2 : event) : Prop := e1.(e_time) < e2.(e_time).

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
  t_stamford_end : time;
  t_hardrada_fall : time;
  t_recovery : time;
  t_march_south_start : time;
  t_hastings_start : time;
  t_hastings_end : time
}.

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

Record chronology (T : timeline) : Prop := {
  landing_before_fulford : t_landing T < t_fulford T;
  fulford_before_york : t_fulford T < t_york_taken T;
  london_depart_before_york : t_london_depart T < t_york_arrive T;
  york_arrive_before_approach : t_york_arrive T <= t_approach_start T;
  york_before_approach : t_york_taken T <= t_approach_start T;
  approach_start_before_end : t_approach_start T < t_approach_end T;
  approach_end_before_bridge : t_approach_end T <= t_bridge_defense T;
  bridge_before_stamford : t_bridge_defense T <= t_stamford_start T;
  stamford_start_before_end : t_stamford_start T < t_stamford_end T;
  stamford_end_before_hardrada : t_stamford_end T <= t_hardrada_fall T;
  hardrada_before_recovery : t_hardrada_fall T <= t_recovery T;
  recovery_before_march_south : t_recovery T <= t_march_south_start T;
  march_south_before_hastings : t_march_south_start T < t_hastings_start T;
  hastings_start_before_end : t_hastings_start T < t_hastings_end T
}.

Lemma landing_before_hastings : forall T, chronology T -> t_landing T < t_hastings_start T.
Proof.
  intros T Hc.
  destruct Hc; lia.
Qed.

(* =============================================================================
   Historical distances and marching speeds (canonicalized for proofs)
   ============================================================================= *)

Definition miles_London_York : nat := 190.
Definition miles_York_Stamford : nat := 10.
Definition miles_Stamford_Hastings : nat := 210.
Definition miles_York_Fulford : nat := 2.
Definition miles_York_Riccall : nat := 8.
Definition miles_York_Tadcaster : nat := 10.
Definition miles_Riccall_Stamford : nat := 12.
Definition miles_Stamford_Derwent : nat := 1.

Lemma dist_London_York : dist London York = miles_London_York.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_York_Stamford : dist York StamfordBridge = miles_York_Stamford.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_Stamford_Hastings : dist StamfordBridge Hastings = miles_Stamford_Hastings.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_York_Fulford : dist York Fulford = miles_York_Fulford.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_York_Riccall : dist York Riccall = miles_York_Riccall.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_York_Tadcaster : dist York Tadcaster = miles_York_Tadcaster.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_Riccall_Stamford : dist Riccall StamfordBridge = miles_Riccall_Stamford.
Proof. vm_compute; reflexivity. Qed.

Lemma dist_Stamford_Derwent : dist StamfordBridge Derwent = miles_Stamford_Derwent.
Proof. vm_compute; reflexivity. Qed.

Fixpoint path_distance_from (prev : location) (rest : list location) : nat :=
  match rest with
  | [] => 0
  | b :: rs => dist prev b + path_distance_from b rs
  end.

Definition path_distance (path : list location) : nat :=
  match path with
  | [] => 0
  | a :: rest => path_distance_from a rest
  end.

Definition route_north : list location := [London; York; StamfordBridge].
Definition route_south : list location := [StamfordBridge; Hastings].
Definition route_full : list location := [London; York; StamfordBridge; Hastings].
Definition route_riccall_bridge : list location := [Riccall; StamfordBridge].
Definition route_york_fulford : list location := [York; Fulford].

Lemma route_north_distance : path_distance route_north = miles_London_York + miles_York_Stamford.
Proof. vm_compute; reflexivity. Qed.

Lemma route_south_distance : path_distance route_south = miles_Stamford_Hastings.
Proof. vm_compute; reflexivity. Qed.

Lemma route_full_distance :
  path_distance route_full =
  miles_London_York + miles_York_Stamford + miles_Stamford_Hastings.
Proof. vm_compute; reflexivity. Qed.

Lemma route_full_distance_value : path_distance route_full = 410.
Proof. vm_compute; reflexivity. Qed.

Lemma route_full_distance_decompose :
  path_distance route_full = path_distance route_north + path_distance route_south.
Proof. vm_compute; reflexivity. Qed.

Lemma route_north_le_full :
  path_distance route_north <= path_distance route_full.
Proof. vm_compute; lia. Qed.

Lemma route_riccall_bridge_distance :
  path_distance route_riccall_bridge = miles_Riccall_Stamford.
Proof. vm_compute; reflexivity. Qed.

Lemma route_york_fulford_distance :
  path_distance route_york_fulford = miles_York_Fulford.
Proof. vm_compute; reflexivity. Qed.

Definition harold_speed_forced : nat := 30.   (* miles per day *)
Definition norse_speed : nat := 15.           (* miles per day *)

Lemma harold_speed_pos : harold_speed_forced > 0.
Proof. unfold harold_speed_forced; lia. Qed.

Lemma norse_speed_pos : norse_speed > 0.
Proof. unfold norse_speed; lia. Qed.

Lemma forced_march_London_York_days : travel_days miles_London_York harold_speed_forced = 7.
Proof. vm_compute; reflexivity. Qed.

Lemma forced_march_York_Stamford_days : travel_days miles_York_Stamford harold_speed_forced = 1.
Proof. vm_compute; reflexivity. Qed.

Lemma forced_march_Stamford_Hastings_days : travel_days miles_Stamford_Hastings harold_speed_forced = 7.
Proof. vm_compute; reflexivity. Qed.

Lemma forced_march_total_days :
  travel_days miles_London_York harold_speed_forced +
  travel_days miles_York_Stamford harold_speed_forced +
  travel_days miles_Stamford_Hastings harold_speed_forced = 15.
Proof. vm_compute; reflexivity. Qed.

Lemma norse_riccall_bridge_days :
  travel_days miles_Riccall_Stamford norse_speed = 1.
Proof. vm_compute; reflexivity. Qed.

Lemma norse_york_fulford_days :
  travel_days miles_York_Fulford norse_speed = 1.
Proof. vm_compute; reflexivity. Qed.

Lemma travel_days_full_route :
  travel_days (path_distance route_full) harold_speed_forced = 14.
Proof. vm_compute; reflexivity. Qed.

Lemma travel_minutes_full_route :
  travel_minutes (path_distance route_full) harold_speed_forced = 14 * minutes_per_day.
Proof. vm_compute; reflexivity. Qed.

Lemma segment_rounding_penalty :
  travel_days miles_London_York harold_speed_forced +
  travel_days miles_York_Stamford harold_speed_forced +
  travel_days miles_Stamford_Hastings harold_speed_forced
  = travel_days (path_distance route_full) harold_speed_forced + 1.
Proof. vm_compute; reflexivity. Qed.

Definition march_minutes_London_York : nat :=
  travel_minutes miles_London_York harold_speed_forced.

Definition march_minutes_York_Stamford : nat :=
  travel_minutes miles_York_Stamford harold_speed_forced.

Definition march_minutes_Stamford_Hastings : nat :=
  travel_minutes miles_Stamford_Hastings harold_speed_forced.

Lemma march_minutes_London_York_value : march_minutes_London_York = 10080.
Proof. vm_compute; reflexivity. Qed.

Lemma march_minutes_York_Stamford_value : march_minutes_York_Stamford = 1440.
Proof. vm_compute; reflexivity. Qed.

Lemma march_minutes_Stamford_Hastings_value : march_minutes_Stamford_Hastings = 10080.
Proof. vm_compute; reflexivity. Qed.

Lemma march_total_minutes :
  march_minutes_London_York + march_minutes_York_Stamford + march_minutes_Stamford_Hastings
  = 15 * minutes_per_day.
Proof. vm_compute; reflexivity. Qed.

Definition stamford_window_slack_days : nat :=
  (d_oct14 - d_sep25) - travel_days miles_Stamford_Hastings harold_speed_forced.

Lemma stamford_window_slack_days_value : stamford_window_slack_days = 12.
Proof. vm_compute; reflexivity. Qed.

Lemma speed_11_insufficient :
  travel_days miles_Stamford_Hastings 11 = 20.
Proof. vm_compute; reflexivity. Qed.

Lemma speed_12_sufficient :
  travel_days miles_Stamford_Hastings 12 = 18.
Proof. vm_compute; reflexivity. Qed.

(* =============================================================================
   Bridge chokepoint model
   ============================================================================= *)

Section Bridge.
  Variable west_bank_troops : nat.
  Variable crossing_rate0 : nat.
  Definition crossing_rate : nat := S crossing_rate0. (* troops per minute, positive *)
  Variable t_cross_start : time.

  Definition crossing_minutes : nat := ceil_div west_bank_troops crossing_rate.
  Definition crossing_complete_time : time := t_cross_start + crossing_minutes.

  Definition all_west_across (t : time) : Prop := crossing_complete_time <= t.

  Definition troops_crossed (t : time) : nat :=
    Nat.min west_bank_troops (crossing_rate * (t - t_cross_start)).

  Definition troops_remaining (t : time) : nat :=
    west_bank_troops - troops_crossed t.

  Lemma troops_crossed_le_total : forall t, troops_crossed t <= west_bank_troops.
  Proof.
    intro t; unfold troops_crossed.
    destruct (le_dec west_bank_troops (crossing_rate * (t - t_cross_start))) as [Hle|Hgt].
    - rewrite Nat.min_l by exact Hle; lia.
    - rewrite Nat.min_r; lia.
  Qed.

  Lemma troops_crossed_before_start : forall t, t <= t_cross_start -> troops_crossed t = 0.
  Proof.
    intros t Hle.
    unfold troops_crossed.
    replace (t - t_cross_start) with 0 by lia.
    unfold crossing_rate; simpl; rewrite Nat.mul_0_r.
    rewrite Nat.min_r; [reflexivity|lia].
  Qed.

  Lemma crossing_not_complete_before : forall t,
    t < crossing_complete_time -> ~ all_west_across t.
  Proof.
    intros t Hlt Hall.
    unfold all_west_across in Hall.
    lia.
  Qed.
End Bridge.

(* =============================================================================
   Daylight window and battle phases (Sep 25)
   ============================================================================= *)

Definition t_sep25_sunrise : time := t_of d_sep25 6 0.
Definition t_sep25_sunset : time := t_of d_sep25 18 0.

Definition in_sep25_daylight (t : time) : Prop :=
  t_sep25_sunrise <= t <= t_sep25_sunset.

Lemma sep25_noon_in_daylight : in_sep25_daylight t_sep25_noon.
Proof.
  unfold in_sep25_daylight, t_sep25_sunrise, t_sep25_sunset, t_sep25_noon, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

Lemma sep25_evening_in_daylight : in_sep25_daylight t_sep25_evening.
Proof.
  unfold in_sep25_daylight, t_sep25_sunrise, t_sep25_sunset, t_sep25_evening, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

Inductive phase :=
  | Approach
  | BridgeDefender
  | BridgeHold
  | ShieldWall
  | Rout.

Definition phase_start (p : phase) : time :=
  match p with
  | Approach => t_of d_sep25 8 0
  | BridgeDefender => t_of d_sep25 9 30
  | BridgeHold => t_of d_sep25 10 30
  | ShieldWall => t_of d_sep25 11 30
  | Rout => t_of d_sep25 14 30
  end.

Definition phase_end (p : phase) : time :=
  match p with
  | Approach => t_of d_sep25 9 30
  | BridgeDefender => t_of d_sep25 10 30
  | BridgeHold => t_of d_sep25 11 30
  | ShieldWall => t_of d_sep25 14 30
  | Rout => t_of d_sep25 16 0
  end.

Lemma phase_chain_1 : phase_end Approach = phase_start BridgeDefender.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_chain_2 : phase_end BridgeDefender = phase_start BridgeHold.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_chain_3 : phase_end BridgeHold = phase_start ShieldWall.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_chain_4 : phase_end ShieldWall = phase_start Rout.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_ordered : phase_start Approach < phase_end Rout.
Proof. vm_compute; lia. Qed.

Lemma shieldwall_in_daylight :
  in_sep25_daylight (phase_start ShieldWall) /\
  in_sep25_daylight (phase_end ShieldWall).
Proof.
  split; unfold in_sep25_daylight, phase_start, phase_end, t_sep25_sunrise, t_sep25_sunset, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

Definition phase_duration (p : phase) : nat :=
  duration (phase_start p) (phase_end p).

Lemma phase_duration_approach : phase_duration Approach = 90.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_duration_defender : phase_duration BridgeDefender = 60.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_duration_bridge : phase_duration BridgeHold = 60.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_duration_shield : phase_duration ShieldWall = 180.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_duration_rout : phase_duration Rout = 90.
Proof. vm_compute; reflexivity. Qed.

Definition battle_duration_from_phases : nat :=
  phase_duration Approach + phase_duration BridgeDefender +
  phase_duration BridgeHold + phase_duration ShieldWall +
  phase_duration Rout.

Lemma battle_duration_from_phases_value : battle_duration_from_phases = 480.
Proof. vm_compute; reflexivity. Qed.

Lemma battle_window_within_daylight :
  in_sep25_daylight (phase_start Approach) /\
  in_sep25_daylight (phase_end Rout).
Proof.
  split; unfold in_sep25_daylight, phase_start, phase_end, t_sep25_sunrise, t_sep25_sunset, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
Qed.

(* Attrition model. The BridgeDefender phase covers the lone Norse axeman's
   stand on the bridge: very few casualties on either side as the defender
   blocks bulk crossing. *)

Definition casualty_rate_english (p : phase) : nat :=
  match p with
  | Approach => 30
  | BridgeDefender => 6
  | BridgeHold => 80
  | ShieldWall => 150
  | Rout => 70
  end.

Definition casualty_rate_norse (p : phase) : nat :=
  match p with
  | Approach => 50
  | BridgeDefender => 6
  | BridgeHold => 120
  | ShieldWall => 200
  | Rout => 300
  end.

Definition casualties_in_phase (rate : phase -> nat) (p : phase) : nat :=
  rate p * phase_duration p / minutes_per_hour.

Definition english_casualties_total : nat :=
  casualties_in_phase casualty_rate_english Approach +
  casualties_in_phase casualty_rate_english BridgeDefender +
  casualties_in_phase casualty_rate_english BridgeHold +
  casualties_in_phase casualty_rate_english ShieldWall +
  casualties_in_phase casualty_rate_english Rout.

Definition norse_casualties_total : nat :=
  casualties_in_phase casualty_rate_norse Approach +
  casualties_in_phase casualty_rate_norse BridgeDefender +
  casualties_in_phase casualty_rate_norse BridgeHold +
  casualties_in_phase casualty_rate_norse ShieldWall +
  casualties_in_phase casualty_rate_norse Rout.

Lemma english_casualties_total_value : english_casualties_total = 686.
Proof. vm_compute; reflexivity. Qed.

Lemma norse_casualties_total_value : norse_casualties_total = 1251.
Proof. vm_compute; reflexivity. Qed.


(* =============================================================================
   Stamford Bridge forces and bridge timing
   ============================================================================= *)

Record host_split := {
  host_total : nat;
  host_east : nat;
  host_west : nat
}.

Definition split_ok (s : host_split) : Prop :=
  host_east s + host_west s = host_total s.

Definition norse_split : host_split :=
  {| host_total := 9000; host_east := 6000; host_west := 3000 |}.

Lemma norse_split_ok : split_ok norse_split.
Proof. vm_compute; reflexivity. Qed.

(* Force composition (coarse) *)

Record force := {
  heavy : nat;
  light : nat;
  archers : nat
}.

Definition force_total (f : force) : nat :=
  heavy f + light f + archers f.

Definition english_force : force :=
  {| heavy := 3000; light := 7000; archers := 1000 |}.

Definition norse_force : force :=
  {| heavy := 3500; light := 4500; archers := 1000 |}.

Lemma english_force_total : force_total english_force = 11000.
Proof. vm_compute; reflexivity. Qed.

Lemma norse_force_total : force_total norse_force = 9000.
Proof. vm_compute; reflexivity. Qed.

Lemma english_norse_ratio : force_total english_force > force_total norse_force.
Proof. vm_compute; lia. Qed.

Lemma west_bank_subset : host_west norse_split <= force_total norse_force.
Proof. vm_compute; lia. Qed.

Lemma english_casualties_bounded :
  english_casualties_total < force_total english_force.
Proof. vm_compute; lia. Qed.

Lemma norse_casualties_bounded :
  norse_casualties_total < force_total norse_force.
Proof. vm_compute; lia. Qed.

(* Force size ranges — plausible estimates *)

Definition english_total_low : nat := 8000.
Definition english_total_high : nat := 15000.
Definition norse_total_low : nat := 6000.
Definition norse_total_high : nat := 12000.

Lemma english_point_in_range :
  english_total_low <= force_total english_force <= english_total_high.
Proof. vm_compute; lia. Qed.

Lemma norse_point_in_range :
  norse_total_low <= force_total norse_force <= norse_total_high.
Proof. vm_compute; lia. Qed.

Theorem english_superiority_at_estimates :
  force_total norse_force < force_total english_force.
Proof. vm_compute; lia. Qed.

Theorem english_superiority_worst_case :
  norse_total_high - english_total_low = 4000.
Proof. vm_compute; reflexivity. Qed.

Theorem english_superiority_best_case :
  english_total_high - norse_total_low = 9000.
Proof. vm_compute; reflexivity. Qed.

Lemma english_casualties_lt_low :
  english_casualties_total < english_total_low.
Proof. vm_compute; lia. Qed.

Theorem casualties_bounded_robust : forall e,
  english_total_low <= e ->
  english_casualties_total < e.
Proof.
  intros e He. pose proof english_casualties_lt_low. lia.
Qed.

Lemma norse_casualties_lt_low :
  norse_casualties_total < norse_total_low.
Proof. vm_compute; lia. Qed.

Theorem norse_casualties_bounded_robust : forall n,
  norse_total_low <= n ->
  norse_casualties_total < n.
Proof.
  intros n Hn. pose proof norse_casualties_lt_low. lia.
Qed.

(* Bridge frontage constraints (coarse geometry) *)

Definition man_width_cm : nat := 60.
Definition bridge_width_cm : nat := 500.
Definition guard_front : nat := 10.

Lemma guard_front_covers_bridge :
  guard_front * man_width_cm >= bridge_width_cm.
Proof. vm_compute; lia. Qed.

Lemma guard_front_available :
  guard_front <= host_west norse_split.
Proof. vm_compute; lia. Qed.

Definition bridge_defense_start : time := phase_start BridgeDefender.

Definition bridge_crossing_rate0 : nat := 9. (* yields 10 troops/min *)

(* Constant-rate model: averaged over the entire crossing window. The actual
   dynamics are staged (see staged_* below) but the constant-rate view is
   convenient for boundary lemmas. *)
Definition bridge_crossing_minutes : nat :=
  crossing_minutes (host_west norse_split) bridge_crossing_rate0.

Definition bridge_clear_time : time :=
  crossing_complete_time (host_west norse_split) bridge_crossing_rate0 bridge_defense_start.

Definition bridge_troops_crossed (t : time) : nat :=
  troops_crossed (host_west norse_split) bridge_crossing_rate0 bridge_defense_start t.

Definition bridge_troops_remaining (t : time) : nat :=
  troops_remaining (host_west norse_split) bridge_crossing_rate0 bridge_defense_start t.

Definition bridge_crossing_rate : nat := crossing_rate bridge_crossing_rate0.

Lemma bridge_crossing_minutes_value : bridge_crossing_minutes = 300.
Proof. vm_compute; reflexivity. Qed.

Definition bridge_crossing_rate_per_hour : nat :=
  bridge_crossing_rate * minutes_per_hour.

Lemma bridge_crossing_rate_per_hour_value : bridge_crossing_rate_per_hour = 600.
Proof. vm_compute; reflexivity. Qed.

Lemma bridge_crossing_hours :
  bridge_crossing_minutes / minutes_per_hour = 5.
Proof. vm_compute; reflexivity. Qed.

Lemma bridge_clear_at_rout : bridge_clear_time = phase_start Rout.
Proof. vm_compute; reflexivity. Qed.

Lemma bridge_crossed_by_shieldwall :
  bridge_troops_crossed (phase_start ShieldWall) = 1200.
Proof. vm_compute; reflexivity. Qed.

Lemma bridge_remaining_by_shieldwall :
  bridge_troops_remaining (phase_start ShieldWall) = 1800.
Proof. vm_compute; reflexivity. Qed.

Lemma bridge_crossed_by_rout :
  bridge_troops_crossed (phase_start Rout) = host_west norse_split.
Proof. vm_compute; reflexivity. Qed.

Lemma bridge_not_complete_by_shieldwall :
  bridge_troops_crossed (phase_start ShieldWall) < host_west norse_split.
Proof. vm_compute; lia. Qed.

Lemma shieldwall_before_bridge_clear :
  phase_start ShieldWall < bridge_clear_time.
Proof. vm_compute; lia. Qed.

Lemma bridge_clear_in_daylight : in_sep25_daylight bridge_clear_time.
Proof.
  rewrite bridge_clear_at_rout.
  unfold in_sep25_daylight, phase_start, t_sep25_sunrise, t_sep25_sunset, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

(* =============================================================================
   Staged crossing: defender holds, then bulk crossing
   ============================================================================= *)

(* The defender phase models Snorri's lone Norse axeman who held the bridge
   until killed by an English soldier with a spear from below the planks.
   During this window the crossing rate is a trickle; once the defender
   falls, the rate jumps to bulk_crossing_rate (= bridge_crossing_rate). *)

Definition defender_minutes : nat := phase_duration BridgeDefender.
Definition defender_crossing_rate : nat := 1.
Definition bulk_crossing_rate : nat := bridge_crossing_rate.

Definition troops_through_defender : nat :=
  defender_crossing_rate * defender_minutes.

Definition west_after_defender : nat :=
  host_west norse_split - troops_through_defender.

Definition staged_bulk_minutes : nat :=
  ceil_div west_after_defender bulk_crossing_rate.

Definition staged_bridge_total_minutes : nat :=
  defender_minutes + staged_bulk_minutes.

Definition staged_bridge_clear_time : time :=
  phase_start BridgeDefender + staged_bridge_total_minutes.

Definition staged_troops_crossed (t : time) : nat :=
  let t_offset := t - phase_start BridgeDefender in
  if Nat.leb t_offset defender_minutes then
    Nat.min (host_west norse_split) (defender_crossing_rate * t_offset)
  else
    Nat.min (host_west norse_split)
      (troops_through_defender + bulk_crossing_rate * (t_offset - defender_minutes)).

Lemma defender_minutes_value : defender_minutes = 60.
Proof. vm_compute; reflexivity. Qed.

Lemma troops_through_defender_value : troops_through_defender = 60.
Proof. vm_compute; reflexivity. Qed.

Lemma west_after_defender_value : west_after_defender = 2940.
Proof. vm_compute; reflexivity. Qed.

Lemma staged_bulk_minutes_value : staged_bulk_minutes = 294.
Proof. vm_compute; reflexivity. Qed.

Lemma staged_bridge_total_minutes_value : staged_bridge_total_minutes = 354.
Proof. vm_compute; reflexivity. Qed.

(* Defender stand is short relative to total crossing; even with the
   bottleneck, the bulk phase dominates the total minutes. *)
Lemma defender_minutes_lt_bulk : defender_minutes < staged_bulk_minutes.
Proof. vm_compute; lia. Qed.

Lemma staged_crossed_during_defender :
  staged_troops_crossed (phase_end BridgeDefender) = troops_through_defender.
Proof. vm_compute; reflexivity. Qed.

Lemma staged_crossed_at_bridgehold_start :
  staged_troops_crossed (phase_start BridgeHold) = 60.
Proof. vm_compute; reflexivity. Qed.

Lemma staged_crossed_by_shieldwall :
  staged_troops_crossed (phase_start ShieldWall) = 660.
Proof. vm_compute; reflexivity. Qed.

Lemma staged_crossed_by_rout :
  staged_troops_crossed (phase_start Rout) = 2460.
Proof. vm_compute; reflexivity. Qed.

Lemma staged_bridge_not_clear_at_rout :
  staged_troops_crossed (phase_start Rout) < host_west norse_split.
Proof. vm_compute; lia. Qed.

(* The defender's stand pushes the bridge clear time into the Rout phase. *)
Lemma staged_bridge_clear_during_rout :
  phase_start Rout < staged_bridge_clear_time /\
  staged_bridge_clear_time <= phase_end Rout.
Proof. split; vm_compute; lia. Qed.

(* The staged model clears later than the constant-rate model: the defender
   delays bulk crossing by defender_minutes - troops_through_defender / bulk_rate. *)
Lemma staged_clear_after_constant :
  bridge_clear_time < staged_bridge_clear_time.
Proof. vm_compute; lia. Qed.

Lemma staged_bridge_clear_in_daylight :
  in_sep25_daylight staged_bridge_clear_time.
Proof.
  unfold in_sep25_daylight, staged_bridge_clear_time, staged_bridge_total_minutes,
    defender_minutes, staged_bulk_minutes, west_after_defender,
    troops_through_defender, defender_crossing_rate, bulk_crossing_rate,
    bridge_crossing_rate, crossing_rate, bridge_crossing_rate0,
    phase_duration, phase_start, phase_end, t_sep25_sunrise, t_sep25_sunset,
    norse_split, host_west, ceil_div, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
Qed.

(* =============================================================================
   Robustness: bridge bottleneck across crossing rates
   ============================================================================= *)

Definition crossing_rate_low : nat := 5.
Definition crossing_rate_high : nat := 20.

Lemma div_ge : forall a b q,
  b > 0 -> q * b <= a -> q <= a / b.
Proof.
  intros a b q Hb Hle.
  pose proof (Nat.div_mod_eq a b).
  pose proof (Nat.mod_bound_pos a b ltac:(lia) ltac:(lia)).
  assert (q * b <= a / b * b + a mod b) by lia.
  destruct (Nat.le_gt_cases q (a / b)) as [|Hgt]; [lia|].
  assert (a / b + 1 <= q) by lia.
  assert ((a / b + 1) * b <= q * b) by (apply Nat.mul_le_mono_r; lia).
  nia.
Qed.

Lemma bridge_bottleneck_duration_lower_bound : forall r,
  crossing_rate_low <= S r -> S r <= crossing_rate_high ->
  crossing_minutes (host_west norse_split) r >= 150.
Proof.
  intros r Hlo Hhi.
  unfold crossing_rate_low, crossing_rate_high in *.
  unfold crossing_minutes, crossing_rate, ceil_div.
  assert (Hw : host_west norse_split = 150 * 20) by (vm_compute; reflexivity).
  rewrite Hw.
  assert (H1 : 150 <= 150 * 20 / S r).
  { apply div_ge; [lia|].
    apply Nat.mul_le_mono_l. lia. }
  assert (H2 : 150 * 20 / S r <= (150 * 20 + S r - 1) / S r).
  { apply Nat.Div0.div_le_mono; lia. }
  lia.
Qed.

Theorem bridge_incomplete_at_shieldwall_robust : forall r,
  crossing_rate_low <= S r -> S r <= crossing_rate_high ->
  phase_start ShieldWall <
    crossing_complete_time (host_west norse_split) r (phase_start BridgeDefender).
Proof.
  intros r Hlo Hhi.
  unfold crossing_complete_time.
  pose proof (bridge_bottleneck_duration_lower_bound r Hlo Hhi).
  assert (Hps : phase_start ShieldWall = phase_start BridgeDefender + 120)
    by (vm_compute; reflexivity).
  lia.
Qed.

(* =============================================================================
   Hastings constraint
   ============================================================================= *)

Definition battle_duration_minutes : nat := 6 * minutes_per_hour.

Lemma battle_duration_pos : battle_duration_minutes > 0.
Proof. unfold battle_duration_minutes, minutes_per_hour; lia. Qed.

Definition earliest_depart_stamford : time := t_sep25_noon + battle_duration_minutes.

Lemma earliest_depart_after_battle : t_sep25_noon < earliest_depart_stamford.
Proof.
  unfold earliest_depart_stamford.
  pose proof battle_duration_pos.
  lia.
Qed.

Definition earliest_hastings_arrival : time :=
  earliest_depart_stamford + travel_minutes miles_Stamford_Hastings harold_speed_forced.

Lemma earliest_hastings_after_stamford : t_sep25_noon < earliest_hastings_arrival.
Proof.
  unfold earliest_hastings_arrival.
  pose proof earliest_depart_after_battle.
  lia.
Qed.

Lemma hastings_window_sufficient_days :
  travel_days miles_Stamford_Hastings harold_speed_forced <= 18.
Proof. vm_compute; lia. Qed.

(* =============================================================================
   Concrete timeline instance (fully specified, Sep 18 -> Oct 14)
   ============================================================================= *)

Definition T_sep25 : timeline := {|
  t_landing := t_of d_sep18 12 0;            (* Norwegian fleet lands at Riccall, Sep 18 *)
  t_fulford := t_of d_sep20 9 0;             (* Battle of Fulford, Sep 20 *)
  t_york_taken := t_of d_sep24 12 0;         (* York submits, Sep 24 *)
  t_london_depart := t_of d_sep18 18 0;      (* Harold departs London, ~Sep 18 evening. *)
  t_york_arrive := t_of d_sep24 18 0;        (* Harold reaches York area, ~Sep 24 evening. *)
  t_approach_start := t_of d_sep25 6 0;      (* Final approach from Tadcaster begins at dawn. *)
  t_approach_end := t_of d_sep25 8 0;        (* Harold reaches Stamford Bridge area. *)
  t_bridge_defense := phase_start BridgeDefender;
  t_stamford_start := phase_start ShieldWall;
  t_stamford_end := phase_end Rout;
  t_hardrada_fall := t_of d_sep25 16 0;
  t_recovery := t_of d_sep25 16 30;
  t_march_south_start := t_sep25_evening;
  t_hastings_start := t_oct14_morning;
  t_hastings_end := t_oct14_morning + battle_duration_minutes
|}.

Lemma chronology_T_sep25 : chronology T_sep25.
Proof.
  unfold T_sep25, phase_start, phase_end, t_sep25_evening, t_oct14_morning, t_of,
    battle_duration_minutes;
  unfold minutes_per_day, hours_per_day, minutes_per_hour.
  constructor.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; lia.
Qed.

Definition events_T_sep25 : list event :=
  [ {| e_name := Landing; e_time := t_landing T_sep25; e_loc := Riccall; e_actor := NorwegianHost |};
    {| e_name := MarchNorthBegins; e_time := t_london_depart T_sep25; e_loc := London; e_actor := EnglishHost |};
    {| e_name := FulfordBattle; e_time := t_fulford T_sep25; e_loc := Fulford; e_actor := NorwegianHost |};
    {| e_name := YorkTaken; e_time := t_york_taken T_sep25; e_loc := York; e_actor := NorwegianHost |};
    {| e_name := YorkArrive; e_time := t_york_arrive T_sep25; e_loc := York; e_actor := EnglishHost |};
    {| e_name := ApproachStart; e_time := t_approach_start T_sep25; e_loc := Tadcaster; e_actor := EnglishHost |};
    {| e_name := MarchNorthEnds; e_time := t_approach_end T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := BridgeDefenseBegins; e_time := t_bridge_defense T_sep25; e_loc := StamfordBridge; e_actor := NorwegianHost |};
    {| e_name := StamfordBattleBegins; e_time := t_stamford_start T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := HardradaFalls; e_time := t_hardrada_fall T_sep25; e_loc := StamfordBridge; e_actor := Hardrada |};
    {| e_name := StamfordBattleEnds; e_time := t_stamford_end T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := EnglishRecovery; e_time := t_recovery T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := MarchSouthBegins; e_time := t_march_south_start T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := HastingsBattleBegins; e_time := t_hastings_start T_sep25; e_loc := Hastings; e_actor := EnglishHost |};
    {| e_name := HastingsBattleEnds; e_time := t_hastings_end T_sep25; e_loc := Hastings; e_actor := EnglishHost |}
  ].

Lemma events_T_sep25_sorted : sorted_by_time events_T_sep25.
Proof.
  unfold events_T_sep25, sorted_by_time, sorted_by_time_from, T_sep25, phase_start, phase_end,
    t_sep25_evening, t_oct14_morning, t_of, battle_duration_minutes;
  simpl; repeat split; vm_compute; lia.
Qed.

Lemma T_sep25_bridge_matches_phase :
  t_bridge_defense T_sep25 = phase_start BridgeDefender.
Proof. reflexivity. Qed.

Lemma T_sep25_battle_window_daylight :
  in_sep25_daylight (t_stamford_start T_sep25) /\
  in_sep25_daylight (t_stamford_end T_sep25).
Proof.
  split.
  - unfold in_sep25_daylight, T_sep25, phase_start, phase_end,
      t_sep25_sunrise, t_sep25_sunset, t_of;
    unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
  - unfold in_sep25_daylight, T_sep25, phase_start, phase_end,
      t_sep25_sunrise, t_sep25_sunset, t_of;
    unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
Qed.

Lemma march_south_window_T_sep25 :
  t_march_south_start T_sep25 + travel_minutes miles_Stamford_Hastings harold_speed_forced
  <= t_oct14_morning.
Proof.
  unfold T_sep25, t_sep25_evening, t_oct14_morning, travel_minutes, travel_days, ceil_div;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
Qed.

Lemma bridge_clear_before_battle_end :
  bridge_clear_time <= t_stamford_end T_sep25.
Proof. unfold bridge_clear_time, T_sep25, phase_end; vm_compute; lia. Qed.

Lemma hardrada_fall_within_battle :
  t_stamford_start T_sep25 <= t_hardrada_fall T_sep25 <= t_stamford_end T_sep25.
Proof.
  unfold T_sep25, phase_start, phase_end, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
Qed.

Lemma recovery_after_battle :
  t_stamford_end T_sep25 <= t_recovery T_sep25.
Proof. unfold T_sep25, phase_end, t_of; vm_compute; lia. Qed.

Definition march_south_duration_minutes : nat :=
  duration (t_march_south_start T_sep25) (t_hastings_start T_sep25).

Lemma march_south_duration_value : march_south_duration_minutes = 26820.
Proof. vm_compute; reflexivity. Qed.

Lemma march_south_duration_days_floor :
  march_south_duration_minutes / minutes_per_day = 18.
Proof. vm_compute; reflexivity. Qed.

(* =============================================================================
   Supply model (campaign-level)
   ============================================================================= *)

Definition campaign_days_available : nat :=
  duration t_sep25_noon t_oct14_morning / minutes_per_day.

Lemma campaign_days_available_value : campaign_days_available = 18.
Proof. vm_compute; reflexivity. Qed.

Definition supply_days_available : nat := campaign_days_available.

Definition supply_days_needed : nat :=
  travel_days (path_distance route_full) harold_speed_forced + 1.

Lemma supply_days_needed_value : supply_days_needed = 15.
Proof. vm_compute; reflexivity. Qed.

Lemma supply_sufficient : supply_days_needed <= supply_days_available.
Proof. vm_compute; lia. Qed.

Definition supply_margin_days : nat :=
  supply_days_available - supply_days_needed.

Lemma supply_margin_days_value : supply_margin_days = 3.
Proof. vm_compute; reflexivity. Qed.

(* =============================================================================
   Robustness: march speed range [25, 35] mi/day
   ============================================================================= *)

Definition speed_low : nat := 25.
Definition speed_high : nat := 35.

Lemma speed_low_pos : speed_low > 0.
Proof. unfold speed_low; lia. Qed.

Lemma harold_speed_in_range :
  speed_low <= harold_speed_forced <= speed_high.
Proof. unfold speed_low, speed_high, harold_speed_forced; lia. Qed.

Theorem stamford_hastings_fits_at_low_speed :
  travel_days miles_Stamford_Hastings speed_low <= d_oct14 - d_sep25.
Proof. vm_compute; lia. Qed.

Theorem full_march_fits_at_low_speed :
  travel_days miles_London_York speed_low +
  travel_days miles_York_Stamford speed_low +
  travel_days miles_Stamford_Hastings speed_low <= d_oct14 - d_sep25.
Proof. vm_compute; lia. Qed.

Lemma ceil_div_spec : forall n d, d > 0 -> n <= ceil_div n d * d.
Proof.
  intros n d Hd. unfold ceil_div.
  pose proof (Nat.div_mod_eq (n + d - 1) d).
  pose proof (Nat.mod_bound_pos (n + d - 1) d ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma ceil_div_alt : forall n d, d > 0 -> n > 0 ->
  ceil_div n d = (n - 1) / d + 1.
Proof.
  intros n d Hd Hn. unfold ceil_div.
  replace (n + d - 1) with ((n - 1) + 1 * d) by lia.
  rewrite Nat.div_add; lia.
Qed.

Lemma ceil_div_zero : forall d, d > 0 -> ceil_div 0 d = 0.
Proof.
  intros d Hd. unfold ceil_div. simpl.
  apply Nat.div_small. lia.
Qed.

Lemma ceil_div_anti_mono : forall n d1 d2,
  d1 > 0 -> d2 > 0 -> d1 <= d2 -> ceil_div n d2 <= ceil_div n d1.
Proof.
  intros n d1 d2 Hd1 Hd2 Hle.
  destruct (Nat.eq_dec n 0) as [->|Hn].
  - rewrite !ceil_div_zero by lia. lia.
  - rewrite !ceil_div_alt by lia.
    assert (H : (n - 1) / d2 <= (n - 1) / d1) by (apply Nat.div_le_compat_l; lia).
    lia.
Qed.

Theorem march_fits_for_all_speeds : forall s,
  speed_low <= s -> s <= speed_high ->
  travel_days miles_Stamford_Hastings s <= d_oct14 - d_sep25.
Proof.
  intros s Hlo Hhi.
  unfold travel_days.
  transitivity (ceil_div miles_Stamford_Hastings speed_low).
  - apply ceil_div_anti_mono; unfold speed_low in *; lia.
  - vm_compute; lia.
Qed.

Theorem full_march_fits_for_all_speeds : forall s,
  speed_low <= s -> s <= speed_high ->
  travel_days (path_distance route_full) s + 1 <= campaign_days_available.
Proof.
  intros s Hlo Hhi.
  unfold travel_days.
  assert (Hbound : ceil_div (path_distance route_full) s <=
                   ceil_div (path_distance route_full) speed_low).
  { apply ceil_div_anti_mono; unfold speed_low in *; lia. }
  assert (Hlow : ceil_div (path_distance route_full) speed_low = 17)
    by (vm_compute; reflexivity).
  assert (Hcamp : campaign_days_available = 18)
    by (vm_compute; reflexivity).
  lia.
Qed.

(* =============================================================================
   Fatigue model: degraded march speed after Stamford Bridge
   ============================================================================= *)

Definition fatigued_speed_low : nat := 15.
Definition fatigued_speed_high : nat := 25.

Lemma fatigued_speed_low_pos : fatigued_speed_low > 0.
Proof. unfold fatigued_speed_low; lia. Qed.

Theorem hastings_reachable_fatigued :
  travel_days miles_Stamford_Hastings fatigued_speed_low <= d_oct14 - d_sep25.
Proof. vm_compute; lia. Qed.

Theorem hastings_reachable_all_fatigued_speeds : forall s,
  fatigued_speed_low <= s -> s <= fatigued_speed_high ->
  travel_days miles_Stamford_Hastings s <= d_oct14 - d_sep25.
Proof.
  intros s Hlo Hhi.
  unfold travel_days.
  transitivity (ceil_div miles_Stamford_Hastings fatigued_speed_low).
  - apply ceil_div_anti_mono; unfold fatigued_speed_low in *; lia.
  - vm_compute; lia.
Qed.

Definition fatigue_penalty : nat := harold_speed_forced - fatigued_speed_low.

Lemma fatigue_penalty_value : fatigue_penalty = 15.
Proof. vm_compute; reflexivity. Qed.

Definition fatigued_march_days : nat :=
  travel_days miles_Stamford_Hastings fatigued_speed_low.

Lemma fatigued_march_days_value : fatigued_march_days = 14.
Proof. vm_compute; reflexivity. Qed.

Definition fatigued_slack : nat := (d_oct14 - d_sep25) - fatigued_march_days.

Lemma fatigued_slack_value : fatigued_slack = 5.
Proof. vm_compute; reflexivity. Qed.

(* =============================================================================
   Derived narrative theorems
   ============================================================================= *)

Theorem hastings_begins_after_stamford : t_sep25_noon < t_oct14_morning.
Proof.
  unfold t_sep25_noon, t_oct14_morning, t_of, d_sep25, d_oct14;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; nia.
Qed.

Theorem march_window_nontrivial : duration t_sep25_noon t_oct14_morning > 0.
Proof.
  apply duration_pos.
  apply hastings_begins_after_stamford.
Qed.

Theorem forced_march_days_fit_window :
  travel_days miles_Stamford_Hastings harold_speed_forced < d_oct14.
Proof. unfold d_oct14; vm_compute; lia. Qed.

Theorem london_to_hastings_upper_bound :
  travel_days miles_London_York harold_speed_forced +
  travel_days miles_York_Stamford harold_speed_forced +
  travel_days miles_Stamford_Hastings harold_speed_forced <= d_oct14.
Proof. unfold d_oct14; rewrite forced_march_total_days; lia. Qed.

(* =============================================================================
   End
   ============================================================================= *)
