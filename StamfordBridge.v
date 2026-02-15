(******************************************************************************)
(*                                                                            *)
(*               Battle of Stamford Bridge: Tactical Chronology               *)
(*                                                                            *)
(*     Formalizes the engagement of 25 September 1066: Harold Godwinson's     *)
(*     forced march from London, Norwegian army disposition across the        *)
(*     River Derwent, bridge chokepoint defense, and rout of Harald           *)
(*     Hardrada's forces. Proves timeline constraints on the Hastings march.  *)
(*                                                                            *)
(*     Seven feet of English ground, or as much more as he is taller than     *)
(*     other men.                                                             *)
(*     - Harold Godwinson's offer to Harald Hardrada, 1066                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 7, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Arith Lia List PeanoNat.
Import ListNotations.

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
  apply Nat.div_le_mono; lia.
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

Definition dist (a b : location) : nat :=
  match a, b with
  (* identity *)
  | London, London => 0 | York, York => 0 | StamfordBridge, StamfordBridge => 0
  | Hastings, Hastings => 0 | Tadcaster, Tadcaster => 0 | Derwent, Derwent => 0
  | Riccall, Riccall => 0 | Fulford, Fulford => 0 | NorthSea, NorthSea => 0
  (* direct edges *)
  | London, York | York, London => 190
  | York, Fulford | Fulford, York => 2
  | York, Riccall | Riccall, York => 8
  | York, Tadcaster | Tadcaster, York => 10
  | York, StamfordBridge | StamfordBridge, York => 10
  | Riccall, StamfordBridge | StamfordBridge, Riccall => 12
  | StamfordBridge, Derwent | Derwent, StamfordBridge => 1
  | StamfordBridge, Hastings | Hastings, StamfordBridge => 210
  (* shortest paths (Mathematica-computed) *)
  | London, StamfordBridge | StamfordBridge, London => 200
  | London, Hastings | Hastings, London => 410
  | London, Tadcaster | Tadcaster, London => 200
  | London, Derwent | Derwent, London => 201
  | London, Riccall | Riccall, London => 198
  | London, Fulford | Fulford, London => 192
  | York, Hastings | Hastings, York => 220
  | York, Derwent | Derwent, York => 11
  | Tadcaster, StamfordBridge | StamfordBridge, Tadcaster => 20
  | Tadcaster, Hastings | Hastings, Tadcaster => 230
  | Tadcaster, Derwent | Derwent, Tadcaster => 21
  | Tadcaster, Riccall | Riccall, Tadcaster => 18
  | Tadcaster, Fulford | Fulford, Tadcaster => 12
  | Derwent, Hastings | Hastings, Derwent => 211
  | Derwent, Riccall | Riccall, Derwent => 13
  | Derwent, Fulford | Fulford, Derwent => 13
  | Riccall, Fulford | Fulford, Riccall => 10
  | Riccall, Hastings | Hastings, Riccall => 222
  | Fulford, StamfordBridge | StamfordBridge, Fulford => 12
  | Fulford, Hastings | Hastings, Fulford => 222
  (* NorthSea: conventional sea distance, satisfies triangle inequality *)
  | NorthSea, _ | _, NorthSea => 1000
  end.

Lemma dist_sym : forall a b, dist a b = dist b a.
Proof. intros a b; destruct a, b; reflexivity. Qed.

Lemma dist_zero : forall a, dist a a = 0.
Proof. intros a; destruct a; reflexivity. Qed.

Lemma dist_triangle : forall a b c,
  dist a c <= dist a b + dist b c.
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
  t_march_north_start : time;
  t_march_north_end : time;
  t_bridge_defense : time;
  t_stamford_start : time;
  t_stamford_end : time;
  t_hardrada_fall : time;
  t_recovery : time;
  t_march_south_start : time;
  t_hastings_start : time
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
  york_before_march_north_end : t_york_taken T <= t_march_north_end T;
  march_north_start_before_end : t_march_north_start T < t_march_north_end T;
  march_north_end_before_bridge : t_march_north_end T <= t_bridge_defense T;
  bridge_before_stamford : t_bridge_defense T <= t_stamford_start T;
  stamford_start_before_end : t_stamford_start T < t_stamford_end T;
  stamford_end_before_hardrada : t_stamford_end T <= t_hardrada_fall T;
  hardrada_before_recovery : t_hardrada_fall T <= t_recovery T;
  recovery_before_march_south : t_recovery T <= t_march_south_start T;
  march_south_before_hastings : t_march_south_start T < t_hastings_start T
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
Proof. reflexivity. Qed.

Lemma dist_York_Stamford : dist York StamfordBridge = miles_York_Stamford.
Proof. reflexivity. Qed.

Lemma dist_Stamford_Hastings : dist StamfordBridge Hastings = miles_Stamford_Hastings.
Proof. reflexivity. Qed.

Lemma dist_York_Fulford : dist York Fulford = miles_York_Fulford.
Proof. reflexivity. Qed.

Lemma dist_York_Riccall : dist York Riccall = miles_York_Riccall.
Proof. reflexivity. Qed.

Lemma dist_York_Tadcaster : dist York Tadcaster = miles_York_Tadcaster.
Proof. reflexivity. Qed.

Lemma dist_Riccall_Stamford : dist Riccall StamfordBridge = miles_Riccall_Stamford.
Proof. reflexivity. Qed.

Lemma dist_Stamford_Derwent : dist StamfordBridge Derwent = miles_Stamford_Derwent.
Proof. reflexivity. Qed.

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
  | BridgeHold
  | ShieldWall
  | Rout.

Definition phase_start (p : phase) : time :=
  match p with
  | Approach => t_of d_sep25 8 0
  | BridgeHold => t_of d_sep25 9 30
  | ShieldWall => t_of d_sep25 11 30
  | Rout => t_of d_sep25 14 30
  end.

Definition phase_end (p : phase) : time :=
  match p with
  | Approach => t_of d_sep25 9 30
  | BridgeHold => t_of d_sep25 11 30
  | ShieldWall => t_of d_sep25 14 30
  | Rout => t_of d_sep25 16 0
  end.

Lemma phase_chain_1 : phase_end Approach = phase_start BridgeHold.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_chain_2 : phase_end BridgeHold = phase_start ShieldWall.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_chain_3 : phase_end ShieldWall = phase_start Rout.
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

Lemma phase_duration_bridge : phase_duration BridgeHold = 120.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_duration_shield : phase_duration ShieldWall = 180.
Proof. vm_compute; reflexivity. Qed.

Lemma phase_duration_rout : phase_duration Rout = 90.
Proof. vm_compute; reflexivity. Qed.

Definition battle_duration_from_phases : nat :=
  phase_duration Approach + phase_duration BridgeHold +
  phase_duration ShieldWall + phase_duration Rout.

Lemma battle_duration_from_phases_value : battle_duration_from_phases = 480.
Proof. vm_compute; reflexivity. Qed.

Lemma battle_window_within_daylight :
  in_sep25_daylight (phase_start Approach) /\
  in_sep25_daylight (phase_end Rout).
Proof.
  split; unfold in_sep25_daylight, phase_start, phase_end, t_sep25_sunrise, t_sep25_sunset, t_of;
  unfold minutes_per_day, hours_per_day, minutes_per_hour; vm_compute; lia.
Qed.

(* Attrition model (coarse) *)

Definition casualty_rate_english (p : phase) : nat :=
  match p with
  | Approach => 30
  | BridgeHold => 80
  | ShieldWall => 150
  | Rout => 70
  end.

Definition casualty_rate_norse (p : phase) : nat :=
  match p with
  | Approach => 50
  | BridgeHold => 120
  | ShieldWall => 200
  | Rout => 300
  end.

Definition casualties_in_phase (rate : phase -> nat) (p : phase) : nat :=
  rate p * phase_duration p / minutes_per_hour.

Definition english_casualties_total : nat :=
  casualties_in_phase casualty_rate_english Approach +
  casualties_in_phase casualty_rate_english BridgeHold +
  casualties_in_phase casualty_rate_english ShieldWall +
  casualties_in_phase casualty_rate_english Rout.

Definition norse_casualties_total : nat :=
  casualties_in_phase casualty_rate_norse Approach +
  casualties_in_phase casualty_rate_norse BridgeHold +
  casualties_in_phase casualty_rate_norse ShieldWall +
  casualties_in_phase casualty_rate_norse Rout.

Lemma english_casualties_total_value : english_casualties_total = 760.
Proof. vm_compute; reflexivity. Qed.

Lemma norse_casualties_total_value : norse_casualties_total = 1365.
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

Definition bridge_defense_start : time := phase_start BridgeHold.

Definition bridge_crossing_rate0 : nat := 9. (* yields 10 troops/min *)

(* Instantiate parameterized Bridge section *)
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

Lemma bridge_delay_after_shieldwall :
  phase_start ShieldWall < bridge_clear_time.
Proof. vm_compute; lia. Qed.

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
  t_landing := t_of d_sep18 12 0;        (* Norwegian fleet lands at Riccall, Sep 18 *)
  t_fulford := t_of d_sep20 9 0;         (* Battle of Fulford, Sep 20 *)
  t_york_taken := t_of d_sep24 12 0;     (* York submits, Sep 24 *)
  t_march_north_start := t_of d_sep18 18 0;  (* Harold departs London, ~Sep 18 evening *)
  t_march_north_end := t_of d_sep25 8 0;     (* Harold reaches Tadcaster/Stamford area *)
  t_bridge_defense := phase_start BridgeHold;
  t_stamford_start := phase_start ShieldWall;
  t_stamford_end := phase_end Rout;
  t_hardrada_fall := t_of d_sep25 16 0;
  t_recovery := t_of d_sep25 16 30;
  t_march_south_start := t_sep25_evening;
  t_hastings_start := t_oct14_morning
|}.

Lemma chronology_T_sep25 : chronology T_sep25.
Proof.
  unfold T_sep25, phase_start, phase_end, t_sep25_evening, t_oct14_morning, t_of;
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
Qed.

Definition events_T_sep25 : list event :=
  [ {| e_name := Landing; e_time := t_landing T_sep25; e_loc := Riccall; e_actor := NorwegianHost |};
    {| e_name := FulfordBattle; e_time := t_fulford T_sep25; e_loc := Fulford; e_actor := NorwegianHost |};
    {| e_name := YorkTaken; e_time := t_york_taken T_sep25; e_loc := York; e_actor := NorwegianHost |};
    {| e_name := BridgeDefenseBegins; e_time := t_bridge_defense T_sep25; e_loc := StamfordBridge; e_actor := NorwegianHost |};
    {| e_name := StamfordBattleBegins; e_time := t_stamford_start T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := HardradaFalls; e_time := t_hardrada_fall T_sep25; e_loc := StamfordBridge; e_actor := Hardrada |};
    {| e_name := StamfordBattleEnds; e_time := t_stamford_end T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := MarchSouthBegins; e_time := t_march_south_start T_sep25; e_loc := StamfordBridge; e_actor := EnglishHost |};
    {| e_name := HastingsBattleBegins; e_time := t_hastings_start T_sep25; e_loc := Hastings; e_actor := EnglishHost |}
  ].

Lemma events_T_sep25_sorted : sorted_by_time events_T_sep25.
Proof.
  unfold events_T_sep25, sorted_by_time, sorted_by_time_from, T_sep25, phase_start, phase_end,
    t_sep25_evening, t_oct14_morning, t_of;
  simpl; repeat split; vm_compute; lia.
Qed.

Lemma T_sep25_bridge_matches_phase :
  t_bridge_defense T_sep25 = phase_start BridgeHold.
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
