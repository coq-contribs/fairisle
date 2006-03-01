(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                Solange Coupet-Grimal & Line Jakubiec-Jamet               *)
(*                                                                          *)
(*                                                                          *)
(*             Laboratoire d'Informatique Fondamentale de Marseille         *)
(*                   CMI et Faculté des Sciences de Luminy                  *)
(*                                                                          *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lif.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                            Developped in Coq v6                          *)
(*                            Ported to Coq v7                              *)
(*                            Translated to Coq v8                          *)
(*                                                                          *)
(*                             July 12nd 2005                               *)
(*                                                                          *)
(****************************************************************************)
(*                             Arbiter4_Specif.v                            *)
(****************************************************************************)


Require Export Arbiter4_Proof_lemmas.
Require Export Moore_Mealy.

Set Implicit Arguments.
Unset Strict Implicit.


Section Four_Arbiters_Specif.

  Let Input_type := (bool * (bool * d_list (d_list bool 4) 4))%type.


  Let Output_type :=
    (d_list bool 3 * d_list bool 3 * (d_list bool 3 * d_list bool 3))%type.


      (**** Description of the global automaton (at a high level) ****)


  Inductive label_a4 : Set :=
    | START_a4 : label_a4
    | AT_LEAST_ONE_IS_ACTIVE_a4 : label_a4
    | WAIT_a4 : label_a4. 

  Definition STATE_a4 : Set :=
    (label_a4 * (d_list (bool * bool) 4 * d_list bool 4))%type.


(** Automaton describing the transitions from a state to another **)


  Definition Output_requested (n m : nat)
    (l : d_list (d_list bool (S n)) m) := d_map negb (d_map (Ackor (n:=n)) l).


  Definition d_Map_List2_pdt_Grant (l : d_list (d_list bool 4) 2)
    (g : d_list (bool * bool) 2) :=
    d_map (List2_pdt (A:=bool))
      (d_map2 Grant_for_Out l
         (List2 (List2 (fst (Fst_of_l2 g)) (snd (Fst_of_l2 g)))
            (List2 (fst (Scd_of_l2 g)) (snd (Scd_of_l2 g))))).


  Definition Trans_Four_Arbiters (i : Input_type) (s : STATE_a4) :
    STATE_a4 :=
    let (fs, p) := i in
    let (RouteE, ltReq) := p in
    let (s', p') := s in
    let (g, o) := p' in
    match s' with
    | START_a4 =>
        match RouteE with
        | true =>
            match Ackor (d_map (Ackor (n:=3)) ltReq) with
            | true =>
                (AT_LEAST_ONE_IS_ACTIVE_a4,
                (d_Map_List4_pdt_Grant ltReq g, Output_requested ltReq))
            | false => (START_a4, (g, l4_tttt))
            end
        | false => (START_a4, (g, l4_tttt))
        end
    | AT_LEAST_ONE_IS_ACTIVE_a4 =>
        match fs with
        | true => (START_a4, (g, l4_tttt))
        | false => (WAIT_a4, (g, o))
        end
    | WAIT_a4 =>
        match fs with
        | true => (START_a4, (g, l4_tttt))
        | false => (WAIT_a4, (g, o))
        end
    end.


(** The output function returns the result of FOUR_ARBITERS **)

  Definition Out_Four_Arbiters (s : STATE_a4) : Output_type :=
    let (_, p) := s in
    let (g, o) := p in
    (List3 (fst (Fst_of_l4 g)) (snd (Fst_of_l4 g)) (Fst_of_l4 o),
    List3 (fst (Scd_of_l4 g)) (snd (Scd_of_l4 g)) (Scd_of_l4 o),
    (List3 (fst (Thd_of_l4 g)) (snd (Thd_of_l4 g)) (Thd_of_l4 o),
    List3 (fst (Fth_of_l4 g)) (snd (Fth_of_l4 g)) (Fth_of_l4 o))).


(** States stream **)

  Definition States_FOUR_ARBITERS :
    Stream Input_type -> STATE_a4 -> Stream STATE_a4 :=
    States_Mealy Trans_Four_Arbiters.



(** Intented behaviour **)

  Definition Behaviour_FOUR_ARBITERS :=
    Moore Trans_Four_Arbiters Out_Four_Arbiters.


(** Transformation of Behaviour_FOUR_ARBITERS to a Mealy automaton **)

  Definition Out_Four_Arbiters_Mealy :=
    Out_Mealy (Input_type:=Input_type) Out_Four_Arbiters.

  Lemma equiv_out_Four_Arbiters_Moore_Mealy :
   forall (i : Input_type) (s : STATE_a4),
   Out_Four_Arbiters s = Out_Four_Arbiters_Mealy i s.
  auto.
  Qed.


  Lemma Equiv_Four_Arbiters_Moore_Mealy :
   forall (s : STATE_a4) (i : Stream Input_type),
   EqS (Behaviour_FOUR_ARBITERS i s)
     (Mealy Trans_Four_Arbiters Out_Four_Arbiters_Mealy i s).
  intros s i.
  unfold Behaviour_FOUR_ARBITERS in |- *;
   unfold Out_Four_Arbiters_Mealy in |- *; apply Equiv_Moore_Mealy.
  Qed.


(** Invariant definition **)


  Let Reg_type :=
    (d_list bool 2 * bool * (d_list bool 2 * bool) *
     (d_list bool 2 * bool * (d_list bool 2 * bool)))%type.


(** Property of Timing, hypothesis here : RouteE must be low when we are  **)
(** in an active cycle (AT_LEAST_ONE_IS_ACTIVE_a4 or WAIT_a4) **)


  Definition P_a4 (i : Input_type) (s_a4 : STATE_a4) 
    (_ : Reg_type) :=
    let (sa4, _) := s_a4 in
    let (_, p) := i in
    let (routeE, _) := p in
    sa4 = AT_LEAST_ONE_IS_ACTIVE_a4 \/ sa4 = WAIT_a4 -> routeE = false.



  Definition At_least_one_of_2_active (o : d_list bool 4) :=
    o = l4_tftf \/
    o = l4_ftft \/
    o = l4_ffff \/
    o = l4_tfft \/
    o = l4_fttf \/ o = l4_ffft \/ o = l4_tfff \/ o = l4_fftf \/ o = l4_ftff.


  Definition R_a4 (s_a4 : STATE_a4) (old : Reg_type) : Prop :=
    let (sa4, p) := s_a4 in
    let (g, o) := p in
    let (old1, old2) := old in
    let (old11, old12) := old1 in
    let (old21, old22) := old2 in
    let (g11, o11) := old11 in
    let (g12, o12) := old12 in
    let (g21, o21) := old21 in
    let (g22, o22) := old22 in
    (sa4 = START_a4 /\ o = l4_tttt \/
     sa4 = AT_LEAST_ONE_IS_ACTIVE_a4 /\
     (o = l4_tttf \/ o = l4_ttft \/ o = l4_ttff) \/
     sa4 = AT_LEAST_ONE_IS_ACTIVE_a4 /\
     (o = l4_tftt \/ o = l4_fttt \/ o = l4_fftt) \/
     sa4 = AT_LEAST_ONE_IS_ACTIVE_a4 /\ At_least_one_of_2_active o \/
     sa4 = WAIT_a4 /\ (o = l4_tttf \/ o = l4_ttft \/ o = l4_ttff) \/
     sa4 = WAIT_a4 /\ (o = l4_tftt \/ o = l4_fttt \/ o = l4_fftt) \/
     sa4 = WAIT_a4 /\ At_least_one_of_2_active o) /\
    Out_Four_Arbiters s_a4 =
    (List3 (Fst_of_l2 g11) (Scd_of_l2 g11) o11,
    List3 (Fst_of_l2 g12) (Scd_of_l2 g12) o12,
    (List3 (Fst_of_l2 g21) (Scd_of_l2 g21) o21,
    List3 (Fst_of_l2 g22) (Scd_of_l2 g22) o22)).


  
End Four_Arbiters_Specif.