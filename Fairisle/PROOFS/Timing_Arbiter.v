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
(*                             Timing_Arbiter.v                             *)
(****************************************************************************)


Require Export Tools_Inf.
Require Export Behaviour_Struct_lemmas.



Set Implicit Arguments.
Unset Strict Implicit.

Section Timing_Arbiter_Proof.

  Variable Fs : Stream bool.
  Variable Act : Stream (d_list bool 4).

(** Hypothesis on the input signals fs and act **)

  Hypothesis fs_0 : S_head Fs = false.

  Hypothesis
    fs_act_signals : EqS sig_false (S_map2 andb (S_tail Fs) (S_Ackor Act)).   
  

  Definition P_Timing (fs : bool) (st : label_t) :=
    false = fs && Out_Timing st.


 CoInductive Inv_P_Timing : Stream bool -> Stream label_t -> Prop :=
     C_Inv_t :
       forall (i : Stream bool) (s : Stream label_t),
       P_Timing (S_head i) (S_head s) ->
       Inv_P_Timing (S_tail i) (S_tail s) -> Inv_P_Timing i s.


 Lemma eqS_Inv_P_Timing :
  forall (i i' : Stream bool) (s s' : Stream label_t),
  EqS i i' -> EqS s s' -> Inv_P_Timing i' s' -> Inv_P_Timing i s.
  cofix.
  intros i i' s s' H_i H_s H_P.
  inversion_clear H_i.
  inversion_clear H_s.
  inversion_clear H_P.
  apply C_Inv_t.
  rewrite H; rewrite H1; try trivial.
  apply eqS_Inv_P_Timing with (S_tail i') (S_tail s'); trivial.
  Qed.


(** P_Timing is an invariant property **)

  Lemma eq_fs_and_RouteE_false :
   forall (e : bool * d_list bool 4) (s : label_t),
   P_Timing (fst e) (Trans_Timing e s).
 unfold P_Timing in |- *.
 intros e s; elim e; clear e; intros fs act.
 elim (bool_dec fs); intros H_fs.
 rewrite H_fs; simpl in |- *.
 case s; case (Ackor act); simpl in |- *; auto.
 rewrite H_fs; simpl in |- *; auto.
 Qed.


 Lemma Is_Inv_P_Timing :
  forall s : label_t, Inv_P_Timing Fs (States_TIMING (Compact Fs Act) s).
 intro s.
 apply C_Inv_t.
 simpl in |- *; rewrite fs_0; unfold P_Timing in |- *; auto.
 generalize Fs Act s fs_act_signals.
 clear fs_act_signals fs_0 s Act Fs.
 cofix.
 intros fs act s H_sig.
 inversion_clear H_sig.
 apply C_Inv_t.
 simpl in |- *.
 specialize
  (eq_fs_and_RouteE_false (S_head (S_tail fs), S_head (S_tail act))
     (Trans_Timing (S_head fs, S_head act) s)); simpl in |- *; 
  auto.
 simpl in H.
 generalize H.
 case (S_head (S_tail fs)); simpl in |- *.
 intros h; elim h; simpl in |- *.
 intros h'; clear h'.
 case s; case (S_head fs); unfold P_Timing in |- *; simpl in |- *; auto.
 unfold P_Timing in |- *; auto.
 simpl in Is_Inv_P_Timing; simpl in |- *.
 apply Is_Inv_P_Timing.
 apply H0.

 Qed.



(* Proof that the property P_a4 taken for the FOUR_ARBITERS proof holds *)
(* for the output of TIMING : we exhibit an invariant Inv_t_a4 *)
(* Proof that : sa=AT_LEAST_ONE_IS_ACTIVE_a4 \/ sa=WAIT_a4 -> RouteE=false *)
(* Avec RouteE=(Out_Timing st) *)

Definition Inv_t_a4 (s_a4 : STATE_a4) (st : label_t) :=
  let (sa4, _) := s_a4 in
  sa4 = START_a4 /\ st = START_t \/
  sa4 = START_a4 /\ st = WAIT_t \/
  sa4 = START_a4 /\ st = ROUTE_t \/
  sa4 = AT_LEAST_ONE_IS_ACTIVE_a4 /\ st = START_t \/
  sa4 = WAIT_a4 /\ st = START_t.



(** Inv_t_a4 is an invariant **)

Lemma Inv_Init_states_t_a4 :
 forall (g : d_list (bool * bool) 4) (o : d_list bool 4),
 Inv_t_a4 (WAIT_a4, (g, o)) START_t.
unfold Inv_t_a4 in |- *; intros g o; do 3 right; auto.
Qed.


Lemma Inv_t_a4_Ok :
 forall (sa4 : STATE_a4) (st : label_t) (fs : bool) 
   (act : d_list bool 4) (ltReq : d_list (d_list bool 4) 4),
 P_Timing fs st ->
 Inv_t_a4 sa4 st ->
 Inv_t_a4 (Trans_Four_Arbiters (fs, (Out_Timing st, ltReq)) sa4)
   (Trans_Timing (fs, act) st).
unfold Inv_t_a4 at 1 in |- *.
intros sa4 st fs' act' ltReq'; elim sa4; clear sa4.
intros sa4 g P H.
elim g; clear g; intros g o.
elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *.
case fs'; simpl in |- *; auto.

elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *.
case (Ackor act'); simpl in |- *; auto.
case fs'; simpl in |- *; auto.

elim H; clear H; intros H.
generalize P; clear P.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *.
case fs'; simpl in |- *.
unfold P_Timing in |- *; simpl in |- *; intros Abs.
absurd (false = true); auto.

intro H0; clear H0.
case (Ackor (d_map (Ackor (n:=3)) ltReq')); simpl in |- *; auto.
right; right; right; auto.

elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *.
case fs'; simpl in |- *; auto.
right; right; right; right; auto.

elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *.
case fs'; simpl in |- *; auto.
right; right; right; right; auto.

Qed.


Lemma P_a4_inv :
 forall (sa4 : STATE_a4) (st : label_t) (fs : bool)
   (ltReq : d_list (d_list bool 4) 4)
   (old_a4 : d_list bool 2 * bool * (d_list bool 2 * bool) *
             (d_list bool 2 * bool * (d_list bool 2 * bool))),
 Inv_t_a4 sa4 st -> P_a4 (fs, (Out_Timing st, ltReq)) sa4 old_a4.
unfold Inv_t_a4 in |- *; unfold P_a4 in |- *.
intros sa4 st fs' ltReq' old_a4; clear fs' ltReq' old_a4.
elim sa4; clear sa4; simpl in |- *.
intros sa4 g H.
elim g; clear g; intros g o.

elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *; auto.

elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *; auto.

elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *; auto.
intro H; elim H; clear H; intro Abs.
absurd (START_a4 = AT_LEAST_ONE_IS_ACTIVE_a4); auto.
discriminate.
absurd (START_a4 = WAIT_a4); auto.
discriminate.

elim H; clear H; intros H.
elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *; auto.

elim H; clear H; intros H1 H2; rewrite H1; rewrite H2; simpl in |- *; auto.

Qed.



(* Proof that P_a4 is invariant *)


Lemma Inv_a4 :
 forall (sa4 : STATE_a4) (st : label_t)
   (old_a4 : d_list bool 2 * bool * (d_list bool 2 * bool) *
             (d_list bool 2 * bool * (d_list bool 2 * bool)))
   (ltReq : Stream (d_list (d_list bool 4) 4)),
 Inv_t_a4 sa4 st ->
 Inv P_a4 (Compact Fs (Compact (Behaviour_TIMING (Compact Fs Act) st) ltReq))
   (States_FOUR_ARBITERS
      (Compact Fs (Compact (Behaviour_TIMING (Compact Fs Act) st) ltReq)) sa4)
   (Structure_States_FOUR_ARBITERS
      (Compact Fs (Compact (Behaviour_TIMING (Compact Fs Act) st) ltReq))
      old_a4).
intros sa st old_a4 ltReq H_I.
specialize (Is_Inv_P_Timing st).
generalize sa st old_a4 Fs Act ltReq H_I.
cofix.
intros sa' st' old_a4' fs' act' ltReq' H_I' H_P'.
inversion_clear H_P'.
apply C_Inv.
simpl in H.
rewrite S_head_Compact.
rewrite S_head_Compact.
rewrite S_head_Behaviour_TIMING.
apply P_a4_inv; try trivial.

generalize
 (Inv_a4
    (Trans_Four_Arbiters
       (S_head
          (Compact fs'
             (Compact (Behaviour_TIMING (Compact fs' act') st') ltReq'))) sa')
    (Trans_Timing (S_head (Compact fs' act')) st')
    (Trans_Struct_four_arbiters
       (S_head
          (Compact fs'
             (Compact (Behaviour_TIMING (Compact fs' act') st') ltReq')))
       old_a4') (S_tail fs') (S_tail act') (S_tail ltReq')).
clear Inv_a4.
intro a4_I; apply a4_I.
rewrite S_head_Compact.
rewrite S_head_Compact.
rewrite S_head_Behaviour_TIMING.
rewrite S_head_Compact.
apply Inv_t_a4_Ok; try trivial.
try trivial.
Qed.


End Timing_Arbiter_Proof.



Require Import Arbitration_beh_sc.


Lemma S_tail_Behaviour_TIMINGPDECODE_ID :
 forall
   (i : Stream
          (bool *
           (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))))
   (s : state_id * (label_t * STATE_p)),
 S_tail (Behaviour_TIMINGPDECODE_ID i s) =
 Behaviour_TIMINGPDECODE_ID (S_tail i) (Trans_TimingPDecode_Id (S_head i) s).
auto.
Qed.


Lemma Equiv_Behaviour_TIMINGPDECODE_ID :
 forall
   (i : Stream
          (bool *
           (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))))
   (si : state_id) (st : label_t) (sp : STATE_p),
 EqS (Behaviour_TIMINGPDECODE_ID i (si, (st, sp)))
   (Compact (S_map (fst (B:=_)) i)
      (Compact
         (Behaviour_TIMING
            (Compact (S_map (fst (B:=_)) i)
               (S_map (fst (B:=_)) (S_map (snd (B:=_)) i))) st)
         (Behaviour_PRIORITY_DECODE
            (Compact (S_map (fst (B:=_)) (S_map (snd (B:=_)) i))
               (Compact
                  (S_map (fst (B:=_))
                     (S_map (snd (B:=_)) (S_map (snd (B:=_)) i)))
                  (S_map (snd (B:=_))
                     (S_map (snd (B:=_)) (S_map (snd (B:=_)) i))))) sp))).
cofix.
intros i si st sp.
apply eqS.
clear Equiv_Behaviour_TIMINGPDECODE_ID; simpl in |- *.
unfold Out_id in |- *; unfold Out_Timing_Mealy in |- *;
 unfold Out_PriorityDecode_Mealy in |- *.
elim (S_head i); simpl in |- *.
intros y y0; elim y0; simpl in |- *.
intros y1 y2; elim y2; simpl in |- *; auto.

rewrite S_tail_Behaviour_TIMINGPDECODE_ID.
unfold Trans_TimingPDecode_Id in |- *.
unfold Trans_Timing_PDecode in |- *; unfold Trans_PC in |- *.
do 2 rewrite S_tail_Compact.
rewrite S_tail_Behaviour_TIMING; rewrite S_tail_Behaviour_PDECODE.
simpl in |- *.
elim (S_head i); intros y y0.
elim y0; intros y1 y2.
elim y2; intros y3 y4.
simpl in |- *.

specialize
 (Equiv_Behaviour_TIMINGPDECODE_ID (S_tail i) (Trans_id y si)
    (Trans_Timing (y, y1) st) (Trans_PriorityDecode (y1, (y3, y4)) sp)).
clear Equiv_Behaviour_TIMINGPDECODE_ID. 
intro H; apply H.

Qed.


Section Verif_hyp.

  Let Input_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

  Variable i : Stream Input_type.

  Let Fs := S_map (fst (B:=_)) i.

  Let Act := S_map (fst (B:=_)) (S_map (snd (B:=_)) i).

  Let Pri := S_map (fst (B:=_)) (S_map (snd (B:=_)) (S_map (snd (B:=_)) i)).

  Let Route := S_map (snd (B:=_)) (S_map (snd (B:=_)) (S_map (snd (B:=_)) i)).


  (** Hypothesis on the input signals fs and act **)

  Hypothesis fs_0 : S_head Fs = false.

  Hypothesis
    fs_act_signals : EqS sig_false (S_map2 andb (S_tail Fs) (S_Ackor Act)).   
  

Lemma Inv_a4' :
 forall (si : state_id) (st : label_t) (sp : STATE_p) 
   (sa4 : STATE_a4)
   (ra4 : d_list bool 2 * bool * (d_list bool 2 * bool) *
          (d_list bool 2 * bool * (d_list bool 2 * bool))),
 Inv_t_a4 sa4 st ->
 Inv P_a4 (Behaviour_TIMINGPDECODE_ID i (si, (st, sp)))
   (States_FOUR_ARBITERS (Behaviour_TIMINGPDECODE_ID i (si, (st, sp))) sa4)
   (Structure_States_FOUR_ARBITERS
      (Behaviour_TIMINGPDECODE_ID i (si, (st, sp))) ra4).
intros si st sp sa4 ra4 HI.

generalize
 (Inv_a4 fs_0 fs_act_signals (sa4:=sa4) (st:=st) ra4
    (Behaviour_PRIORITY_DECODE (Compact Act (Compact Pri Route)) sp)).
intro P.
apply
 eqS_about_P
  with
    (i' := Compact Fs
             (Compact (Behaviour_TIMING (Compact Fs Act) st)
                (Behaviour_PRIORITY_DECODE (Compact Act (Compact Pri Route))
                   sp)))
    (s1' := States_FOUR_ARBITERS
              (Compact Fs
                 (Compact (Behaviour_TIMING (Compact Fs Act) st)
                    (Behaviour_PRIORITY_DECODE
                       (Compact Act (Compact Pri Route)) sp))) sa4)
    (s2' := Structure_States_FOUR_ARBITERS
              (Compact Fs
                 (Compact (Behaviour_TIMING (Compact Fs Act) st)
                    (Behaviour_PRIORITY_DECODE
                       (Compact Act (Compact Pri Route)) sp))) ra4).
unfold Fs in |- *; unfold Act in |- *; unfold Pri in |- *;
 unfold Route in |- *; apply Equiv_Behaviour_TIMINGPDECODE_ID.
unfold States_FOUR_ARBITERS in |- *.
apply EqS_States_Mealy; auto.
unfold Fs in |- *; unfold Act in |- *; unfold Pri in |- *;
 unfold Route in |- *; apply Equiv_Behaviour_TIMINGPDECODE_ID.
unfold Structure_States_FOUR_ARBITERS in |- *; unfold States_PC in |- *.
apply EqS_States_Mealy; auto.
unfold Fs in |- *; unfold Act in |- *; unfold Pri in |- *;
 unfold Route in |- *; apply Equiv_Behaviour_TIMINGPDECODE_ID.
apply P.
try trivial.
Qed.


End Verif_hyp.


Section From_init_states.

  Let Input_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

  Variable i : Stream Input_type.

  Let Fs := S_map (fst (B:=_)) i.

  Let Act := S_map (fst (B:=_)) (S_map (snd (B:=_)) i).

  Let Pri := S_map (fst (B:=_)) (S_map (snd (B:=_)) (S_map (snd (B:=_)) i)).

  Let Route := S_map (snd (B:=_)) (S_map (snd (B:=_)) (S_map (snd (B:=_)) i)).


  (** Hypothesis on the input signals fs and act **)

  Hypothesis fs_0 : S_head Fs = false.

  Hypothesis
    fs_act_signals : EqS sig_false (S_map2 andb (S_tail Fs) (S_Ackor Act)).   
  

 (* P_a4 is an invariant (from the initial states) *)

  Variable g11_0 g12_0 g21_0 g22_0 : bool * bool.      (* lasts *)
  Variable p_0 : d_list (d_list bool 4) 4.    (* ltReq *)

Lemma P_a4_Ok :
 Inv P_a4
   (Behaviour_TIMINGPDECODE_ID i (IDENTITY, (START_t, (START_p, p_0))))
   (States_FOUR_ARBITERS
      (Behaviour_TIMINGPDECODE_ID i (IDENTITY, (START_t, (START_p, p_0))))
      (WAIT_a4, (List4 g11_0 g12_0 g21_0 g22_0, l4_ffff)))
   (Structure_States_FOUR_ARBITERS
      (Behaviour_TIMINGPDECODE_ID i (IDENTITY, (START_t, (START_p, p_0))))
      (pdt_List2 g11_0, false, (pdt_List2 g12_0, false),
      (pdt_List2 g21_0, false, (pdt_List2 g22_0, false)))).

apply Inv_a4'; auto.
apply Inv_Init_states_t_a4.
Qed.


End From_init_states.
