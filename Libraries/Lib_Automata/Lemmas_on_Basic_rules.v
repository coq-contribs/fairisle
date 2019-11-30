(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

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
(*                         Lemmas_on_Basic_rules.v                          *)
(****************************************************************************)
 
Require Export Basic_composition_rules.

Set Implicit Arguments.
Unset Strict Implicit.


Section Equiv_on_rule_PC.

  Variable Input_type_1 Input_type_2 Input_type : Set.
  Variable Output_type_1 Output_type_2 : Set.
  Variable State_type_a1 State_type_a2 State_type_b1 State_type_b2 : Set.

  Variable Transa1 : Input_type_1 -> State_type_a1 -> State_type_a1.
  Variable Transa2 : Input_type_2 -> State_type_a2 -> State_type_a2.

  Variable Outa1 : Input_type_1 -> State_type_a1 -> Output_type_1.
  Variable Outa2 : Input_type_2 -> State_type_a2 -> Output_type_2.

  Variable Transb1 : Input_type_1 -> State_type_b1 -> State_type_b1.
  Variable Transb2 : Input_type_2 -> State_type_b2 -> State_type_b2.

  Variable Outb1 : Input_type_1 -> State_type_b1 -> Output_type_1.
  Variable Outb2 : Input_type_2 -> State_type_b2 -> Output_type_2.

  Let A1 := Mealy Transa1 Outa1.
  Let A2 := Mealy Transa2 Outa2.

  Let B1 := Mealy Transb1 Outb1.
  Let B2 := Mealy Transb2 Outb2.

  Variable f : Input_type -> Input_type_1 * Input_type_2.
  Variable
    output : Output_type_1 * Output_type_2 -> Output_type_1 * Output_type_2.

  Lemma equiv_PC :
   forall (i i' : Stream Input_type) (sa1 : State_type_a1)
     (sa2 : State_type_a2) (sb1 : State_type_b1) (sb2 : State_type_b2),
   EqS i i' ->
   EqS (A1 (S_map fstS (S_map f i)) sa1)
     (B1 (S_map fstS (S_map f i)) sb1) ->
   EqS (A2 (S_map sndS (S_map f i')) sa2)
     (B2 (S_map sndS (S_map f i')) sb2) ->
   EqS (PC Transa1 Transa2 Outa1 Outa2 f output i (sa1, sa2))
     (PC Transb1 Transb2 Outb1 Outb2 f output i' (sb1, sb2)).
  Proof.
  cofix equiv_PC.
  unfold fstS, sndS.
  intros i i' sa1 sa2 sb1 sb2 H1 H2 H3.
  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H3.
  simpl in H1; simpl in H2.
  apply eqS.
  simpl in |- *.
  rewrite H1; elim H2; elim H; auto.
  unfold PC in |- *; rewrite S_tail_Mealy; rewrite S_tail_Mealy.
  unfold PC in equiv_PC.
  unfold Trans_PC at 2 4 in |- *.
  apply equiv_PC; try trivial.
  elim H; auto.
  rewrite H; auto.
  Qed.


End Equiv_on_rule_PC.


Section Equiv_on_rule_SC.

  Variable Input_type Output_type_1 Output_type_2 : Set.
  Variable State_type_a1 State_type_a2 State_type_b1 State_type_b2 : Set.

  Variable Transa1 : Input_type -> State_type_a1 -> State_type_a1.
  Variable Transa2 : Output_type_1 -> State_type_a2 -> State_type_a2.

  Variable Outa1 : Input_type -> State_type_a1 -> Output_type_1.
  Variable Outa2 : Output_type_1 -> State_type_a2 -> Output_type_2.

  Variable Transb1 : Input_type -> State_type_b1 -> State_type_b1.
  Variable Transb2 : Output_type_1 -> State_type_b2 -> State_type_b2.

  Variable Outb1 : Input_type -> State_type_b1 -> Output_type_1.
  Variable Outb2 : Output_type_1 -> State_type_b2 -> Output_type_2.

  Let A1 := Mealy Transa1 Outa1.
  Let A2 := Mealy Transa2 Outa2.

  Let B1 := Mealy Transb1 Outb1.
  Let B2 := Mealy Transb2 Outb2.


 Lemma equiv_SC :
  forall (i : Stream Input_type) (sa1 : State_type_a1) 
    (sa2 : State_type_a2) (sb1 : State_type_b1) (sb2 : State_type_b2),
  EqS (A2 (A1 i sa1) sa2) (B2 (B1 i sb1) sb2) ->
  EqS (SC Transa1 Transa2 Outa1 Outa2 i (sa1, sa2))
    (SC Transb1 Transb2 Outb1 Outb2 i (sb1, sb2)).
  Proof.
  cofix equiv_SC.
  intros i sa1 sa2 sb1 sb2 H.
  inversion_clear H.
  simpl in H0.
  apply eqS.
  simpl in |- *.
  try trivial.
  simpl in |- *; auto.
  Qed.


  Lemma equiv_SC' :
   forall (sa1 : State_type_a1) (sa2 : State_type_a2) 
     (sb1 : State_type_b1) (sb2 : State_type_b2),
   (forall i i' : Stream Input_type,
    EqS i i' ->
    forall (sa1 : State_type_a1) (sb1 : State_type_b1),
    EqS (A1 i sa1) (B1 i' sb1)) ->
   (forall j j' : Stream Output_type_1,
    EqS j j' ->
    forall (sa2 : State_type_a2) (sb2 : State_type_b2),
    EqS (A2 j sa2) (B2 j' sb2)) ->
   forall k k' : Stream Input_type,
   EqS k k' ->
   EqS (SC Transa1 Transa2 Outa1 Outa2 k (sa1, sa2))
     (SC Transb1 Transb2 Outb1 Outb2 k' (sb1, sb2)).
  Proof.
  cofix equiv_SC'.
  intros sa1 sa2 sb1 sb2 H0 H1 k k' H2.
  apply eqS.
  simpl in |- *.
  generalize (H0 k k' H2 sa1 sb1).
  intro H3; generalize (H1 (A1 k sa1) (B1 k' sb1) H3 sa2 sb2).
  intro H4; clear H0 H1.
  inversion_clear H3.
  simpl in H.
  inversion_clear H4.
  simpl in H1.
  inversion_clear H2.
  try trivial.
  unfold SC in |- *; rewrite S_tail_Mealy; rewrite S_tail_Mealy.
  unfold SC in equiv_SC'.
  unfold Trans_SC at 2 4 in |- *.
  apply equiv_SC'; try trivial.
  inversion_clear H2; try trivial.
  Qed.

End Equiv_on_rule_SC.




(* In the case where output is the identity function *)

Section output_is_identity.

  Variable Input_type_1 Input_type_2 Input_type : Set.
  Variable Output_type_1 Output_type_2 : Set.
  Variable State_type_a1 State_type_a2 : Set.

  Variable Trans1 : Input_type_1 -> State_type_a1 -> State_type_a1.
  Variable Trans2 : Input_type_2 -> State_type_a2 -> State_type_a2.

  Variable Out1 : Input_type_1 -> State_type_a1 -> Output_type_1.
  Variable Out2 : Input_type_2 -> State_type_a2 -> Output_type_2.

  Let A1 := Mealy Trans1 Out1.
  Let A2 := Mealy Trans2 Out2.

  Let States_A1 := States_Mealy Trans1.
  Let States_A2 := States_Mealy Trans2.

  Variable f : Input_type -> Input_type_1 * Input_type_2.
  Variable
    output : Output_type_1 * Output_type_2 -> Output_type_1 * Output_type_2.

  Hypothesis
    H_output : forall o : Output_type_1 * Output_type_2, output o = o.

  Lemma Compact_PC_id :
   forall (i : Stream Input_type) (s1 : State_type_a1) (s2 : State_type_a2),
   EqS
     (Compact (A1 (S_map fstS (S_map f i)) s1)
        (A2 (S_map sndS (S_map f i)) s2))
     (PC Trans1 Trans2 Out1 Out2 f output i (s1, s2)).
  Proof.
  intros i s1 s2.
  apply
   EqS_trans
    with
      (S_map output
         (Compact
            (A1 (S_map (fst (A:=Input_type_1) (B:=Input_type_2)) (S_map f i))
               s1)
            (A2 (S_map (snd (A:=Input_type_1) (B:=Input_type_2)) (S_map f i))
               s2))).
  apply eqS; simpl in |- *.
  auto.
  apply S_map_id.
  auto.
  unfold A1 in |- *; unfold A2 in |- *.
  apply Equiv_A1A2_PC.
  Qed.


  Lemma S_map_output :
   forall s1 s2 : Stream (Output_type_1 * Output_type_2),
   EqS s1 s2 -> EqS (S_map output s1) (S_map output s2).
  Proof.
  cofix S_map_output.
  intros s1 s2 H.
  inversion_clear H.
  apply eqS; simpl in |- *.
  elim H0; auto.
  apply S_map_output; auto.
  Qed.

 
End output_is_identity.


Lemma S_tail_States_PC :
 forall
   (Input_type_1 Input_type_2 Input_type State_type_a1 State_type_a2 : Set)
   (t1 : Input_type_1 -> State_type_a1 -> State_type_a1)
   (t2 : Input_type_2 -> State_type_a2 -> State_type_a2)
   (f : Input_type -> Input_type_1 * Input_type_2) 
   (i : Stream Input_type) (spc : State_type_a1 * State_type_a2),
 S_tail (States_PC t1 t2 f i spc) =
 States_PC t1 t2 f (S_tail i) (Trans_PC t1 t2 f (S_head i) spc).
Proof.
auto.
Qed.


Lemma S_head_States_PC :
 forall
   (Input_type_1 Input_type_2 Input_type State_type_a1 State_type_a2 : Set)
   (t1 : Input_type_1 -> State_type_a1 -> State_type_a1)
   (t2 : Input_type_2 -> State_type_a2 -> State_type_a2)
   (f : Input_type -> Input_type_1 * Input_type_2) 
   (i : Stream Input_type) (spc : State_type_a1 * State_type_a2),
 S_head (States_PC t1 t2 f i spc) = spc.
Proof.
auto.
Qed.


Lemma Equiv_States_PC :
 forall
   (Input_type_1 Input_type_2 Input_type State_type_a1 State_type_a2 : Set)
   (t1 : Input_type_1 -> State_type_a1 -> State_type_a1)
   (t2 : Input_type_2 -> State_type_a2 -> State_type_a2)
   (f : Input_type -> Input_type_1 * Input_type_2) 
   (i i' : Stream Input_type) (spc spc' : State_type_a1 * State_type_a2),
 spc = spc' ->
 EqS i i' -> EqS (States_PC t1 t2 f i spc) (States_PC t1 t2 f i' spc').
Proof.
cofix Equiv_States_PC.
intros.
inversion_clear H0.
apply eqS.
simpl in |- *; trivial.
rewrite S_tail_States_PC; rewrite S_tail_States_PC.
apply Equiv_States_PC.
rewrite H1; rewrite H; auto.
auto.
Qed.



Lemma S_tail_States_SC :
 forall (Input_type Output_type_1 State_type_a1 State_type_a2 : Set)
   (t1 : Input_type -> State_type_a1 -> State_type_a1)
   (t2 : Output_type_1 -> State_type_a2 -> State_type_a2)
   (out1 : Input_type -> State_type_a1 -> Output_type_1)
   (i : Stream Input_type) (ssc : State_type_a1 * State_type_a2),
 S_tail (States_SC t1 t2 out1 i ssc) =
 States_SC t1 t2 out1 (S_tail i) (Trans_SC t1 t2 out1 (S_head i) ssc).
Proof.
auto.
Qed.


Lemma S_head_States_SC :
 forall (Input_type Output_type_1 State_type_a1 State_type_a2 : Set)
   (t1 : Input_type -> State_type_a1 -> State_type_a1)
   (t2 : Output_type_1 -> State_type_a2 -> State_type_a2)
   (out1 : Input_type -> State_type_a1 -> Output_type_1)
   (i : Stream Input_type) (ssc : State_type_a1 * State_type_a2),
 S_head (States_SC t1 t2 out1 i ssc) = ssc.
Proof.
auto.
Qed.


Lemma States_SC_simpl :
 forall (Input_type Output_type_1 State_type_a1 State_type_a2 : Set)
   (t1 : Input_type -> State_type_a1 -> State_type_a1)
   (t2 : Output_type_1 -> State_type_a2 -> State_type_a2)
   (out1 : Input_type -> State_type_a1 -> Output_type_1)
   (i : Stream Input_type) (s1 : State_type_a1) (s2 : State_type_a2),
 EqS (S_map fstS (States_SC t1 t2 out1 i (s1, s2)))
   (States_Mealy t1 i s1).
Proof.
cofix States_SC_simpl.
intros.
apply eqS.
simpl in |- *; auto.
rewrite S_tail_S_map.
rewrite S_tail_States_Mealy.
rewrite S_tail_States_SC.
unfold Trans_SC in |- *; auto.
Qed.



Section Tool_about_Lemma_on_rules.

  Variable Input_type_1 Input_type_2 Input_type : Set.
  Variable Output_type_1 Output_type_2 : Set.
  Variable State_type_a1 State_type_a2 State_type_b1 State_type_b2 : Set.

  Variable Transa1 : Input_type_1 -> State_type_a1 -> State_type_a1.
  Variable Transa2 : Input_type_2 -> State_type_a2 -> State_type_a2.

  Variable Outa1 : Input_type_1 -> State_type_a1 -> Output_type_1.
  Variable Outa2 : Input_type_2 -> State_type_a2 -> Output_type_2.

  Variable Transb1 : Input_type_1 -> State_type_b1 -> State_type_b1.
  Variable Transb2 : Input_type_2 -> State_type_b2 -> State_type_b2.

  Variable Outb1 : Input_type_1 -> State_type_b1 -> Output_type_1.
  Variable Outb2 : Input_type_2 -> State_type_b2 -> Output_type_2.

  Let A1 := Mealy Transa1 Outa1.
  Let A2 := Mealy Transa2 Outa2.

  Let B1 := Mealy Transb1 Outb1.
  Let B2 := Mealy Transb2 Outb2.

  Variable f : Input_type -> Input_type_1 * Input_type_2.
  Variable
    output : Output_type_1 * Output_type_2 -> Output_type_1 * Output_type_2.

  Lemma PC_Mealy :
   forall (i i' : Stream Input_type) (sa1 : State_type_a1)
     (sa2 : State_type_a2) (sb1 : State_type_b1) (sb2 : State_type_b2),
   EqS i i' ->
   EqS (PC Transa1 Transa2 Outa1 Outa2 f output i (sa1, sa2))
     (PC Transb1 Transb2 Outb1 Outb2 f output i' (sb1, sb2)) ->
   EqS
     (Mealy (Trans_PC Transa1 Transa2 f) (Out_PC Outa1 Outa2 f output) i
        (sa1, sa2))
     (Mealy (Trans_PC Transb1 Transb2 f) (Out_PC Outb1 Outb2 f output) i'
        (sb1, sb2)).
  Proof.
  auto.
  Qed.


End Tool_about_Lemma_on_rules.
