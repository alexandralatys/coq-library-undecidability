
From Undecidability.StackMachines Require Import BSM BSM.bsm_defs.
From Undecidability.TM Require Import SBTM Util.SBTM_facts.
From Undecidability.Shared.Libs.DLW Require Import vec subcode sss.


Require Import PeanoNat List Lia.
Import Vector.VectorNotations ListNotations SBTMNotations.
#[local] Open Scope list_scope.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
#[local] Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
#[local] Notation CURR := (@Fin.FS 3 (@Fin.F1 2)).
#[local] Notation LEFT := (@Fin.F1 3).
#[local] Notation RIGHT := (@Fin.FS 3 (@Fin.FS 2 (@Fin.F1 1))).
#[local] Notation ZERO := (@Fin.FS 3 (@Fin.FS 2 (@Fin.FS 1 (@Fin.F1 0)))).

Section Construction.

  (* Shift by shift to the right*)
  Context (M : SBTM) (q0 : state M) (shift : nat).

  #[local] Notation δ := (trans' M).

  Definition c := 13.

  #[local] Arguments Vector.cons {A} _ {n}.

  Definition encode_tape (t : tape) : Vector.t (list bool) 4 := 
    match t with
    | (ls, a, rs) => [ ls ; [a]%list ; rs ; []%list ]%vector
    end.

    Print proj1_sig.
    Print sval.

  (* Shift everything back by one*)
  Definition encode_state (q : state M) := (1 + shift + sval (Fin.to_nat q) * c).


  #[local] Arguments encode_state : simpl never.
  #[local] Notation "! p" := (encode_state p) (at level 1).

  Definition encode_config '(q, t) : bsm_state 4 := (!q, encode_tape t).

  #[local] Notation JMP i := (POP ZERO i i).

  (* Jump after Program now*)
  Notation END := (1 + shift + c * (num_states M)).
  
  (* THIS needs to be adapted somehow, but how to deal with length? -> Keep length at 2 *)
  (* Definition box '(q, a) (f : (state M * bool * direction) -> list (bsm_instr 4)) : bsm_instr 4 :=
    match δ (q, a) with
    | None => PUSH CURR a :: JMP END :: []
    | Some t => DUMMY INSTRUCTION :: f t :: []
    end. *)

  Definition box '(q, a) (f : (state M * bool * direction) -> bsm_instr 4) : bsm_instr 4 :=
  match δ (q, a) with
  | None => JMP END
  | Some t => f t
  end.

  Definition CURR' := CURR. (* to distinguish duplicate operations for subcode_tac *)

  (* TODO does this even retain outputs ?  -> IT DOES NOT*)
  Definition PROG (q : state M) :=
    let off := !q in
  (*      off *) POP CURR (7 + off) (7 + off) ::

  (*  1 + off *) box (q, true) (fun '(q', a', d) => PUSH (match d with go_left => RIGHT | go_right => LEFT end) a') ::
  (*  2 + off *) box (q, true) (fun '(q', a', d) => POP (match d with go_left => LEFT | go_right => RIGHT end) (5+off) (5+off)) ::
  (*  3 + off *) PUSH CURR true ::
  (*  4 + off *) JMP (6 + off) ::
  (*  5 + off *) PUSH CURR false ::
  (*  6 + off *) box (q, true) (fun '(q', a', d) => JMP (!q')) :: 

  (*  7 + off *) box (q, false) (fun '(q', a', d) => PUSH (match d with go_left => RIGHT | go_right => LEFT end) a') ::
  (*  8 + off *) box (q, false) (fun '(q', a', d) => POP (match d with go_left => LEFT | go_right => RIGHT end) (11+off) (11+off)) ::
  (*  9 + off *) PUSH CURR' true ::
  (* 10 + off *) JMP (12 + off) ::
  (* 11 + off *) PUSH CURR' false ::
  (* 12 + off *) box (q, false) (fun '(q', a', d) => JMP (!q')) :: [].

  Lemma PROG_length q : length (PROG q) = c.
  Proof. reflexivity. Qed.

  Opaque c.

  Fixpoint all_fins (n : nat) : list (Fin.t n) :=
    if n is S n' then Fin.F1 :: map Fin.FS (all_fins n') else nil.

  (* constructed BSM *)
  Definition P : list (bsm_instr 4) :=
    JMP (!q0) :: flat_map PROG (all_fins (num_states M)).

  Lemma P_length : length P = 1 + num_states M * c.
  Proof.
    simpl.
    congr S.
    have := PROG_length.
    elim: (num_states M) (PROG). (* Works like induction ?*)
    - done.
    - intros n IH PROG' H.
      have ->: S n * c = n * c + c by lia.
      simpl.
      rewrite length_app.
      rewrite flat_map_concat_map.
      rewrite map_map.
      rewrite <- flat_map_concat_map.
      rewrite H.
      rewrite IH.
      + done.
      + lia.
  Qed.

  Lemma P_length' : shift + length P = END.
  Proof.
    rewrite P_length.
    cbn.
    lia.
  Qed.

  Lemma P_length'' : S (length (flat_map (PROG) (all_fins (num_states M)))) =
S (c * num_states M).
  Proof.
    congr S.
    have := PROG_length.
    elim: (num_states M) (PROG).
    - done.
    - intros n IH PROG' H.
      simpl.
      rewrite length_app.
      rewrite flat_map_concat_map.
      rewrite map_map.
      rewrite <- flat_map_concat_map.
      rewrite H.
      rewrite IH.
      + done.
      + lia.
  Qed.


  Definition Q_step (Q : list (bsm_instr 4)) offset i v : option (bsm_state 4) :=
    match nth_error Q i with
    | None => None
    | Some (bsm_pop x p' q') => Some (
        match vec_pos v x with
        | [] => (q', v)
        | false :: l => (p', vec_change v x l)
        | true :: l => ((S i) + offset, vec_change v x l)
        end)
    | Some (bsm_push x b) => Some ((S i) + offset, vec_change v x (b :: vec_pos v x))
    end.

  Arguments Q_step : simpl never.

  Print sss_step.

  (* If Q_Step returns Some, then the step is valid according to sss_step *)
  Lemma Q_step_spec (Q : list (bsm_instr 4)) offset i v j w : 
    Q_step Q offset i v = Some (j, w) ->
    sss_step (bsm_sss (n:=4)) (offset, Q) (i + offset, v) (j, w).
  Proof.
    unfold Q_step.
    case E: (nth_error Q i) => [t|].
    - move: E => /(@nth_error_split (bsm_instr 4)) => - [l] [r] [-> <-].
      intros Ht.
      exists offset, l, t, r, v. 
      split.
      + done.
      + split.
        * congr pair.
          lia.
        * move: t Ht => [].
          -- move=> x p' q' [<-].
             move Ex: (vec_pos v x) => [|[] ?].
             ++ auto using bsm_sss.
             ++ auto using bsm_sss.
             ++ auto using bsm_sss.
          -- move=> x b [<-] <-.
             auto using bsm_sss. 
    - done.
  Qed.

  Arguments nth_error : simpl never.

  (* If SBTM does a step, then BSM does the same step encoded
     k?*)
  Lemma PROG_spec_Some q t q' t' : step M (q, t) = Some (q', t') ->
    exists k, (!q, PROG q) // (encode_config (q, t)) -[S k]-> (encode_config (q', t')).
  Proof.
    move: t => [[ls a] rs] /=. rewrite /step.
    case E: (δ (q, a)) => [[[??]d]|]; last done.
    move=> [<- <-]. have ->: !q = 0 + !q by done.
    move: d a ls rs E => [] [] [|[] ls] [|[] rs] E.
    all: eexists; rewrite /PROG /box E.

    1: do ? ((by apply: in_sss_steps_0) || (apply: in_sss_steps_S; [by apply: Q_step_spec|])).


    all: do ? ((by apply: in_sss_steps_0) || (apply: in_sss_steps_S; [by apply: Q_step_spec|])).
  Qed.

  Lemma PROG_spec_None q t : step M (q, t) = None ->
    exists v, (!q, PROG q) // (encode_config (q, t)) ->> (shift + length P, v).
  Proof.
    rewrite P_length'.
    move: t => [[ls a] rs] /=. rewrite /step.
    case E: (δ (q, a)) => [[[??]d]|]; first done.
    move=> _. have ->: !q = 0 + !q by done.
    move: a E => [] E.
    all: exists [ ls ; []%list ; rs ; []%list ]%vector.
    all: eexists; rewrite /PROG /box E.
    all: do ? ((by apply: in_sss_steps_0) || (apply: in_sss_steps_S; [by apply: Q_step_spec|])).
  Qed.

  Lemma PROG_spec_None_output q t : step M (q, t) = None ->
    (!q, PROG q) // (encode_config (q, t)) ->> (shift + length P, encode_tape t).
  Proof.
    (* rewrite P_length'.
    move: t => [[ls a] rs] /=. rewrite /step.
    case E: (δ (q, a)) => [[[??]d]|]; first done.
    (* move=> _. have ->: !q = 0 + !q by done. *)
    intros.

    eexists (1 + _).
    destruct a.
    -
    -
    unfold PROG.








    move: a E => [] E.
    





    (* all: exists [ ls ; []%list ; rs ; []%list ]%vector. *)
    (* all: eexists; rewrite /PROG /box E.  *)
    all: do ? ((by apply: in_sss_steps_0) || (apply: in_sss_steps_S; [by apply: Q_step_spec|])). *)
  Admitted.

  Lemma PROG_sc (q : state M) : (!q, PROG q) <sc (shift, P).
  Proof.
    apply: subcode_cons. rewrite /P /encode_state [1+shift]/=.
    suff: forall n, (n + sval (Fin.to_nat q) * c, PROG q) <sc
      (n, flat_map PROG (all_fins (num_states M))) by done.
    have := PROG_length. move: (num_states M) q (PROG) => ?.
    elim. { move=> /= *. by eexists [], _. }
    move=> m q IH PROG' H' n.
    have := IH (fun q => PROG' (Fin.FS q)) => /(_ ltac:(done) (n+c)).
    rewrite /= !flat_map_concat_map map_map -!flat_map_concat_map.
    move=> [l] [r] [{}IH {}IH']. exists (PROG' Fin.F1 ++ l), r. split.
    - by rewrite IH -app_assoc.
    - move: (Fin.to_nat q) IH' => [? ?] /=. rewrite length_app H'. lia.
  Qed.

  (* Opaque P. *)

  Lemma simulation_step_Some q t q' t' : step M (q, t) = Some (q', t') ->
    exists k, (shift, P) // (encode_config (q, t)) -[S k]-> (encode_config (q', t')).
  Proof.
    move=> /PROG_spec_Some [k] H. exists k.
    apply: subcode_sss_steps; [|by eassumption].
    by apply: PROG_sc.
  Qed.

  Lemma simulation_step_None q t : step M (q, t) = None ->
    exists v, (shift, P) // (encode_config (q, t)) ->> (shift + length P, v).
  Proof.
    move=> /PROG_spec_None [v Hv]. exists v.
    by apply: subcode_sss_compute; [apply: PROG_sc|].
  Qed.

    Lemma simulation_step_None_output q t : step M (q, t) = None ->
    (shift, P) // (encode_config (q, t)) ->> (shift + length P, encode_tape t).
  Proof.
    move=> /PROG_spec_None_output Hv.

    assert (H1 := PROG_sc q).
    assert (H2 := subcode_sss_compute).
    specialize (H2 _ _ _ _ _ _ _ H1 Hv).
    apply H2.
  Qed.

  Lemma simulation q t k :
    steps M k (q, t) = None ->
    exists v, (shift, P) // (encode_config (q, t)) ->> (shift + length P, v).
  Proof.
    elim: k q t; first done.
    move=> k IH q t. rewrite (steps_plus 1) /=.
    case E: (step M (q, t)) => [[q' t']|].
    - move=> /IH [v] Hv. exists v.
      move: E => /simulation_step_Some [?] /sss_steps_compute /sss_compute_trans.
      by apply.
    - by move: E => /simulation_step_None.
  Qed.


  Lemma simulation_output q q' t t' k :
    steps M k (q, t) = Some (q', t') ->
    (shift, P) // (encode_config (q, t)) ->> (encode_config (q', t')).
  Proof.
    elim: k q t.
    + intros.
      injection H.
      intros.
      subst.
      simpl.
      unfold sss_compute.
      exists 0.
      constructor.
    +
    move=> k IH q t. rewrite (steps_plus 1) /=.
    case E: (step M (q, t)) => [[q'' t'']|].
    - move=> /IH [v] Hv.

      assert (Y := simulation_step_Some).
      specialize (Y _ _ _ _ E).
      destruct Y.

      exists ((S x) + v).

      assert (X := sss_steps_trans).
      specialize (X _ _ _ _ _ _ _ _ _ H Hv).
      simpl in X.
      apply X.

    - by move: E => /simulation_step_None.
  Qed.

  Lemma simulation_output'' q q' t t' k :
    steps M k (q, t) = Some (q', t') ->
    steps M (S k) (q, t) = None ->
    (shift, P) // (encode_config (q, t)) ->> (shift + length P, encode_tape t').
  Proof.
    elim: k q t.
    + intros.

      assert (H2 := simulation_output).
      specialize (H2 _ _ _ _ _ H).
      unfold sss_compute in H2.
      destruct H2 as [k H2].

      assert (X := simulation_step_None_output).
      specialize (X _ _ H0).

      inversion H.
      subst.
      apply X.

    +
    move=> k IH q t.
    intros. 
    replace (S k) with (1 + k) in H by lia.
    replace (S (S k)) with (1 + (S k)) in H0 by lia.
    rewrite steps_plus in H.
    rewrite steps_plus in H0.
    case E: (step M (q, t)) => [[q'' t'']|].
    - 
      
      simpl in H.
      rewrite E in H.

      replace (steps M 1 (q, t)) with (step M (q,t)) in H0 by easy.
      rewrite E in H0.

      simpl in H.
      simpl in H0.

      replace (SBTM.obind (step M) (steps M k (q'', t''))) with (steps M (S k) (q'', t'')) in H0 by easy.
      
      specialize (IH _ _ H H0).

      destruct IH as [k0 IH].


      assert (Y := simulation_step_Some).
      specialize (Y _ _ _ _ E).
      destruct Y.

      exists ((S x) + k0).

      assert (X := sss_steps_trans).
      specialize (X _ _ _ _ _ _ _ _ _ H1 IH).
      apply X.

    - simpl in H.
      rewrite E in H.
      simpl in H.
      inversion H.
  Qed.



    Lemma simulation' t k :
    steps M k (q0, t) = None ->
    exists v, (shift, P) // (shift, encode_tape t) ->> (shift + length P, v).
  Proof.
    intros H0.
    destruct k.
    - inversion H0.
    - assert (H1 := simulation).
      specialize (H1 q0 t (S k) H0).
      destruct H1 as [v H1].
      exists v.
      unfold sss_compute in H1.
      destruct H1 as [k0 H1].
      unfold sss_compute.
      exists (S k0).

      assert (H5 := in_sss_steps_S).
      specialize (H5 _ _ (bsm_sss (n:= 4)) (shift, P) k0 (shift, encode_tape t) (!q0, encode_tape t) (shift + length P, v)).
      apply H5.
      + unfold P.
        unfold sss_step. 
        exists shift.
        exists [].
        exists (JMP ! q0).
        exists (flat_map PROG (all_fins (num_states M))).
        exists (encode_tape t).
        split.
        * auto.
        * split.
          -- simpl.
            replace (shift + 0) with shift by lia.
            reflexivity.
          -- apply in_bsm_sss_pop_E.
            unfold encode_tape.
            destruct t as [p rs].
            destruct p as [ls a].
            reflexivity.
      + apply H1.
  Qed.


      Lemma simulation_output' q' t t' k :
    steps M k (q0, t) = Some (q', t') ->
    steps M (S k) (q0, t) = None ->
    (shift, P) // (shift, encode_tape t) ->> (shift + length P, encode_tape t').
  Proof.
    intros H0 H1.

    assert (H2 := simulation_output'').
    specialize (H2 q0 q' t t' k H0 H1).
    unfold sss_compute in H2.
    destruct H2 as [k0 H2].
    unfold sss_compute.
    exists (1 + k0).

    assert (A : (shift, P) // (shift, encode_tape t) -[1]-> encode_config (q0, t)).
    - apply sss_steps_1.
      unfold sss_step.
      unfold P.
      exists shift.
      eexists [].
      eexists (JMP ! q0).
      eexists (flat_map PROG (all_fins (num_states M))).
      eexists (encode_tape t).
      split.
      +  cbn. reflexivity.
      + split.
        * cbn. replace (shift + 0) with shift by lia. reflexivity.
        * apply in_bsm_sss_pop_E.
            unfold encode_tape.
            destruct t.
            destruct p.
            reflexivity.
    - assert (T := sss_steps_trans).
      specialize (T _ _ _ _ _ _ _ _ _ A H2).
      apply T.
  Qed.


  Lemma inverse_simulation q t n i v :
    (shift, P) // (encode_config (q, t)) -[n]-> (shift + i, v) ->
    out_code (shift + i) (shift, P) ->
    exists k, steps M k (q, t) = None.
  Proof.
    elim /(Nat.measure_induction _ id) : n q t => - [|n] IH q t.
    { move=> /sss_steps_0_inv [] /= <- _.
      rewrite /encode_state P_length'' (ltac:(done) : c = (S (c-1))).
      have := svalP (Fin.to_nat q). nia. }
    case E: (step M (q, t)) => [[q' t']|]; last by (move=> _; exists 1).
    move: (E) => /simulation_step_Some [m].
    move=> Hn Hm Hi. have := (IH (n - m) ltac:(lia) q' t' _ Hi).
    case.
    { move: Hn Hm Hi => /subcode_sss_subcode_inv /[apply] /[apply].
      case.
      - by exact: bsm_sss_fun.
      - by apply: subcode_refl.
      - move=> n' [?]. by have ->: n' = n - m by lia. }
    move=> k Hk. exists (1+k). by rewrite (steps_plus 1) /= E.
  Qed.

  Lemma inverse_simulation' t n i v :
    (shift, P) // (shift , encode_tape t) -[n]-> (shift + i, v) ->
    out_code (shift + i) (shift, P) ->
    exists k, steps M k (q0, t) = None.
  Proof.
    intros H0 H1.
    induction n.
    - destruct i.
      + inversion H1; cbn in H; lia.
      + inversion H0. lia.
    - assert (H2 := inverse_simulation).
      specialize (H2 q0 t n i v).
      apply H2.
      + assert (H3 := sss_steps_S_inv').
        specialize (H3 _ _ (bsm_sss (n:= 4)) (shift, P) (shift, encode_tape t) (shift + i, v) n H0).
        destruct H3 as [str2 H3].
        destruct H3 as [H3A H3B].
        unfold sss_step in H3A.
        destruct H3A.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H3.
        injection H.
        injection H3.
        intros.
        assert (H9 : x0 = []).
        * rewrite H8 in H6. 
          assert (length x0 = 0) by lia.
          apply length_zero_iff_nil.
          apply H9.
        *
        rewrite H9 in H7.
        replace ([] ++ x1 :: x2) with (x1 :: x2) in H7 by auto.
        unfold P in H7.
        inversion H7.
        rewrite <- H11 in H4.
        inversion H4.
        -- rewrite <- H13 in H3B. apply H3B.
        -- unfold encode_tape in H18.
          destruct t in H18.
          destruct p0 in H18.
          simpl in H18.
          inversion H18.
        -- unfold encode_tape in H18.
          destruct t in H18.
          destruct p0 in H18.
          simpl in H18.
          inversion H18.
      + apply H1.
Qed.


    
      




End Construction.

Require Import Undecidability.Synthetic.Definitions.

Arguments mult _ _ : simpl never.

Theorem reduction :
  SBTM_HALT ⪯ BSM_HALTING.
Proof.
  exists (fun '(existT _ M (q, t)) =>
    existT _ 4 (existT _ 0 (existT _ (@P M q 0) (encode_tape t)))).
  move=> [M [q [[ls a] rs]]]. split.
  - move=> [k] /simulation => /(_ q 0) [v Hv] /=.
    exists ((1 + c * (num_states M)), v). split => /=.
    + rewrite /P.
      rewrite P_length' in Hv.
      bsm sss POP empty with ZERO (encode_state M 0 q ) (encode_state M 0 q).
    + right.
      rewrite <- (P_length'' M 0).
      constructor.
  - move=> [] [i v] [] [?] H /= ?.
    rewrite /P in H.
    bsm inv POP empty with H ZERO (encode_state M 0 q) (encode_state M 0 q).
    + move: H => [?] [?] /inverse_simulation. by apply.
    + move=> []. lia.
Qed.
