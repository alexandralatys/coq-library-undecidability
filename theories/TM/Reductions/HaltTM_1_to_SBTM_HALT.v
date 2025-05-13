From Undecidability Require TM.TM TM.Util.TM_facts.
From Undecidability Require Import TM.SBTM TM.Util.SBTM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

Require Import PeanoNat Lia.


#[local] Unset Implicit Arguments.
#[local] Unset Strict Implicit.

Require Import List ssreflect ssrbool ssrfun.
Import ListNotations SBTMNotations.

Set Default Goal Selector "!".

Module SBTM_facts.

  (* remove redundante false symbol *)
  Definition truncate (l : list bool) : list bool :=
    match l with
    | [false] => []
    | [a; false] => if a then [a] else []
    | _ => l
    end.

  Definition truncate_tape (t : tape) : tape :=
    match t with
    | (ls, a, rs) => (truncate ls, a, truncate rs)
    end.

  Lemma almost_eq_truncate l : almost_eq (truncate l) l. 
  Proof.
    have ? := almost_eq_refl.
    have ? := almost_eq_false 0 0.
    have ? := almost_eq_false 0 1.
    have ? := almost_eq_false 0 2.
    move: l => [|[] [|[] [|??]]] /=; by do ? constructor.
  Qed.

  Lemma almost_eq_tape_truncate_tape t : almost_eq_tape (truncate_tape t) t.
  Proof.
    move: t => [[ls a] rs]. constructor; by apply: almost_eq_truncate.
  Qed.

  #[local] Opaque step.

  Lemma steps_truncate {M k q t} :
    steps M k (q, truncate_tape t) = None <-> (steps M k (q, t) = None).
  Proof.
    apply: almost_eq_tape_steps_None.
    apply: almost_eq_tape_truncate_tape.
  Qed.

(* TODO MOVE *)
  Lemma almost_eq_tape_steps_Some M k q q1 q2 t1 t'1 t2 t'2 :
  almost_eq_tape t1 t2 -> 
  steps M k (q, t1) = Some (q1, t'1) ->
  steps M k (q, t2) = Some (q2, t'2) ->
  q1 = q2 /\ almost_eq_tape t'1 t'2.
Proof.
  revert q q1 q2 t1 t'1 t2 t'2.
  induction k.
  - intros.
    split.
    + injection H0. injection H1. intros. rewrite <- H3. rewrite <- H5. reflexivity.
    + injection H0. injection H1. intros. rewrite <- H2. rewrite <- H4. apply H.
  - intros.
    replace (S k) with (1 + k) in H0 by lia.
    replace (S k) with (1 + k) in H1 by lia.
    rewrite steps_plus in H0.
    rewrite steps_plus in H1.
    remember (steps M 1 (q, t1)) as s1.
    remember (steps M 1 (q, t2)) as s2.
    destruct s1; destruct s2.
    + simpl in H0. simpl in H1.
      destruct p as [q''1 t''1]. destruct p0 as [q''2 t''2].
      specialize (IHk q''1 q1 q2 t''1 t'1 t''2 t'2).
      assert (E := almost_eq_tape_step_Some).
      specialize (E M q q''1 q''2 t1 t''1 t2 t''2 H).
      simpl in Heqs1.
      simpl in Heqs2.
      symmetry in Heqs1.
      symmetry in Heqs2.
      specialize (E Heqs1).
      specialize (E Heqs2).
      destruct E.
      rewrite <- H2 in H1.
      specialize (IHk H3 H0 H1).
      destruct IHk.
      split.
      * apply H4.
      * apply H5.
    + simpl in H1. inversion H1.
    + simpl in H0. inversion H0.
    + simpl in H1. inversion H1.
Qed.






End SBTM_facts.

(* translate between Fin and a listable type *)
Module ListFin.
  Fixpoint decode {X : Type} (L : list X) (i : Fin.t (length L)) : X :=
    (match L return Fin.t (length L) -> X with
    | [] => fun j => Fin.case0 (fun=> X) j
    | x :: L' => fun j => Fin.caseS' j (fun=> X) x (fun j' => decode L' j')
    end) i.

  Definition encode_sig
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L) (x : X) :
      {i : Fin.t (length L) | decode L i = x }.
  Proof.
    elim: L {HL} (HL x); first done.
    move=> y L IH /=. case: (HX y x).
    - move=> -> _. by exists Fin.F1.
    - move=> ??. have /IH [i Hi] : In x L by tauto.
      by exists (Fin.FS i).
  Qed.

  Definition encode
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L) (x : X) :
      Fin.t (length L) := sval (encode_sig HX HL x).

  Lemma decode_encode 
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L)
    (x : X) : decode L (encode HX HL x) = x.
  Proof. exact: (svalP (encode_sig HX HL x)). Qed.
End ListFin.

Import SBTM_facts.

Section Construction.
  (* input TM *)
  Context (M : TM.TM (finType_CS bool) 1).

  (* symbols are "01", "11" *)
  Definition encode_symbol (a : finType_CS bool) : list bool := [a; true].

  (* blank is 00 *)
  Definition encode_tape (t : TM.tape (finType_CS bool)) : tape :=
    match t with
    | TM.niltape => ([], false, [])
    | TM.leftof a rs => ([], false, flat_map encode_symbol (a :: rs))
    | TM.rightof a ls => (false :: flat_map (fun a' => rev (encode_symbol a')) (a :: ls), false, [])
    | TM.midtape ls a rs => (a :: flat_map (fun a' => rev (encode_symbol a')) ls, true, flat_map encode_symbol rs)
    end.

  Inductive space : Type :=
  (* corresponds to q *)
  | space_base (q : TM.state M) : space
  (* reading symbol *)
  | space_read (q : TM.state M) : space
  (* stepping twice in direction d *)
  | space_move (q : TM.state M) (d : direction) (t : bool) : space 
  (* test next symbol in direction d: on false return, on true q *)
  | space_test (q : TM.state M) (d : direction) (t : bool) : space
  (* write b then move in direction *)
  | space_write (q : TM.state M) (a : bool) (d : TM.move) : space.
  
  Lemma listable_space : {L : list space | forall x, In x L}.
  Proof.
    have : {L' | forall (d : direction) (t : bool) (m : TM.move), In (d, t, m) L'}.
    { exists (list_prod (list_prod [go_left; go_right] [true; false]) [TM.Lmove; TM.Rmove; TM.Nmove]).
      move=> [] [] [] /=; tauto. }
    move=> [L' HL'].
    exists (
      flat_map (fun '(q, (d, t, m)) =>
        [space_base q; space_read q; space_move q d t; space_test q d t; space_write q t m]) 
        (list_prod (elem (TM.state M)) L')).
    move=> [].
    - move=> q. apply /in_flat_map.
      exists (q, (go_left, true, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q. apply /in_flat_map.
      exists (q, (go_left, true, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q d t. apply /in_flat_map.
      exists (q, (d, t, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q d t. apply /in_flat_map.
      exists (q, (d, t, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q a m. apply /in_flat_map.
      exists (q, (go_left, a, m)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
  Qed.

  Lemma eqdec_space : forall (x y : space), {x = y} + {x <> y}.
  Proof.
    have := @eqType_dec (TM.state M). move=> H.
    intros. do ? decide equality; by apply: H.
  Qed.

  #[local] Notation size := (length (sval listable_space)).

  Definition encode_space : space -> Fin.t size :=
    fun x => ListFin.encode eqdec_space (svalP listable_space) x.

  Definition decode_space : Fin.t size -> space :=
    fun x => ListFin.decode (sval listable_space) x.

  Lemma decode_encode_space (x : space) : decode_space (encode_space x) = x.
  Proof. by apply: ListFin.decode_encode. Qed.

  #[local] Notation "| a |" := (Vector.cons _ a 0 (Vector.nil _)).

  #[local] Notation encode_state q := (encode_space (space_base q)).

  Definition go_back (d : direction) :=
    match d with
    | go_left => go_right
    | go_right => go_left
    end.

  Definition M' : SBTM.
  Proof using M.
    refine (Build_SBTM size
      (construct_trans (fun '(q, a) => _))).
    (* in state q reading symbol a *)
    refine (
      match decode_space q with
      | space_base q_base => _
      | space_read q_read => _
      (* move d twice *)
      | space_move q' d true => 
          Some (encode_space (space_move q' d false), a, d)
      (* move d once *)
      | space_move q' d false => 
          Some (encode_state q', a, d)
      (* test d in distance 1 *)
      | space_test q' d true => 
          Some (encode_space (space_test q' d false), a, d)
      (* test *)
      | space_test q' d false => 
          match a with
          | true => Some (encode_space (space_move q' go_right false), a, go_left)
          | false => Some (encode_space (space_move q' (go_back d) false), a, go_back d)
          end
      (* write *)
      | space_write q' b TM.Lmove =>
          Some (encode_state q', b, go_left)
      | space_write q' b TM.Rmove =>
          Some (encode_space (space_move q' go_right true), b, go_right)
      | space_write q' b TM.Nmove =>
          Some (encode_state q', b, go_right)
      end).
    + (* case space_base *)
      refine (
        match TM.halt M q_base with
        (* halting condition *)
        | true => None
        | false =>
            match a with
            (* a = true, read actual symbol *)
            | true => Some (encode_space (space_read q_base), true, go_left)
            (* case a = false, no symbol *)
            | false => 
              match TM.trans M (q_base, | None |) with
              | (q_next, result) =>
                  match Vector.hd result with
                  (* case write b, move *)
                  | (Some b, m) => Some (encode_space (space_write q_next b m), true, go_left)
                  (* case no write *)
                  | (None, TM.Lmove) => Some (encode_space (space_test q_next go_left true), a, go_left)
                  | (None, TM.Rmove) => Some (encode_space (space_test q_next go_right true), a, go_right)
                  | (None, TM.Nmove) =>  Some (encode_space (space_move q_next go_right false), a, go_left)
                  end
              end
            end
        end).
    + (* case space_read *)
      refine ( 
        match TM.trans M (q_read, | Some a |) with
        | (q_next, result) =>
          match Vector.hd result with
          (* case write bL, Lmove *)
          | (Some bL, TM.Lmove) => Some (encode_state q_next, bL, go_left)
          (* case write bR, Rmove *)
          | (Some bR, TM.Rmove) => Some (encode_space (space_move q_next go_right true), bR, go_right)
          (* case write bN, Nmove *)
          | (Some bN, TM.Nmove) => Some (encode_state q_next, bN, go_right)
          (* case no write *)
          | (None, TM.Lmove) => Some (encode_state q_next, a, go_left)
          | (None, TM.Rmove) => Some (encode_space (space_move q_next go_right true), a, go_right)
          | (None, TM.Nmove) => Some (encode_state q_next, a, go_right)
          end
        end).
  Defined.

  Print M'.

  #[local] Notation step := (step M').
  #[local] Notation steps := (steps M').
  #[local] Notation state := (state M').
  #[local] Notation config := (config M').

  #[local] Notation TM_step x := (@TM_facts.step _ _ M x).
  #[local] Notation TM_config := (@TM_facts.mconfig (finType_CS bool) (TM.state M) 1).

  Definition encode_config : TM_config -> config :=
    fun '(TM_facts.mk_mconfig q ctapes) =>
      (encode_state q, truncate_tape (encode_tape (Vector.hd ctapes))).

  (* simulation up to truncation *)
  Lemma simulation_step q t : TM.halt M q = false ->
    exists k,
      (omap (fun '(q', t') => (q', truncate_tape t')) (steps (S k) (encode_state q, encode_tape t))) =
        Some (encode_config (TM_step (TM_facts.mk_mconfig q (| t |)))).
  Proof.
    move=> Hq. case: t.
    - (* case niltape *)
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
    - (* case leftof *)
      move=> a rs.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          by case: a.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
    - (* case rightof *)
      move=> a ls.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
    - (* case midtape *)
      move=> ls a rs.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: ls => [|l ls]; by do ? rewrite construct_trans_spec decode_encode_space.
        * exists 1. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: ls => [|l ls]; by do ? rewrite /= construct_trans_spec decode_encode_space.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: rs => [|r rs]; by do ? rewrite /= construct_trans_spec decode_encode_space.
        * exists 3. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: rs => [|r rs]; by do ? rewrite /= construct_trans_spec decode_encode_space.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
  Qed.


  Lemma simulation_halt q t : TM.halt M q = true ->
    step (encode_state q, t) = None.
  Proof.
    move: t => [[? ?] ?] /= Hq.
    by rewrite /= /step /= construct_trans_spec decode_encode_space ?Hq.
  Qed.

  Lemma simulation q t :
    (exists q' t', TM.eval M q t q' t') ->
    exists k, steps k ((encode_state q), (encode_tape (Vector.hd t))) = None.
  Proof.
    move=> [q'] [t'] /TM_facts.TM_eval_iff [n].
    elim: n q t.
    { move=> q t. rewrite /= /TM_facts.haltConf /=.
      case E: (TM.halt q) => [|]; last done.
      move: E => /simulation_halt H _.
      exists 1. by apply: H. }
    move=> n IH q t. rewrite /= /TM_facts.haltConf /=.
    case E: (TM.halt q) => [|].
    { move: E => /simulation_halt H _. exists 1. by apply: H. }
    rewrite (Vector.eta t).
    move: E => /simulation_step => /(_ (Vector.hd t)) [k1].
    move: (VectorDef.tl t). apply: Vector.case0.
    move: (TM_step _) => [q'' ts''] Hk1 /IH [k2 Hk2] /=.
    exists ((S k1) + k2). rewrite (steps_plus).
    move: (encode_state q, _) Hk1 Hk2 => x.
    move Hk1: (steps (S k1) x) => [[q''' t''']|] /=; last done.
    move=> [] <- Ht''' /(@steps_truncate M').
    rewrite -Ht'''. by move=> /steps_truncate.
  Qed.



Lemma h1 l1 l2 l3 b:
almost_eq_tape ([], b, l1) (true :: l3, b, l2) -> False.
Proof.
  intros.
  inversion H.
  inversion H2.
  induction n2.
  - inversion H9.
  - simpl in H9.
    inversion H9.
Qed.


Lemma h2 l1 l2 l3 b:
almost_eq_tape (l1, b, []) (l2, b, true :: l3) -> False.
Proof.
  intros.
  inversion H.
  inversion H6.
  induction n2.
  - inversion H9.
  - simpl in H9.
    inversion H9.
Qed.

Lemma h3 l1 l2 l1' l2' b:
almost_eq_tape (l1, b, l2) (l1', b, l2') -> almost_eq l1 l1' /\ almost_eq l2 l2'.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Lemma h4 l:
almost_eq [] (false :: l) -> exists n, l = repeat false n.
Proof.
  intros.
  inversion H.
  induction n2.
  - inversion H2.
  - simpl in H2.
    injection H2.
    intros.
    rewrite <- H0.
    exists n2.
    reflexivity.
Qed.

Lemma h5 l1 l2:
almost_eq (true :: l1) (false :: l2) -> False.
Proof.
  intros.
  inversion H.
  induction n1; inversion H1.
Qed.

Lemma h6 l1 l2 b:
almost_eq (b :: l1) (b :: l2) -> almost_eq l1 l2.
Proof.
  intros.
  inversion H.
  - apply H1.
  - induction n1, n2.
    + inversion H1.
    + inversion H1.
    + inversion H2.
    + simpl in H1.
      simpl in H2.
      inversion H1.
      inversion H2.
      subst.
      constructor.
Qed.

Lemma h7 l1 l2 l3 l3' b:
almost_eq_tape (l1, b, true :: l3) (l2, b, false :: l3') -> False.
Proof.
  intros.
  inversion H.
  inversion H6.
  destruct n1; inversion H8.
Qed.

Lemma hft1 l1 l2 l3 l3' b:
almost_eq_tape (l1, b, false :: l3) (l2, b, true :: l3') -> False.
Proof.
  intros.
  inversion H.
  inversion H6.
  destruct n2; inversion H9.
Qed.

Lemma htf1 l1 l2 l3 l3' b:
almost_eq_tape (l1, b, true :: l3) (l2, b, false :: l3') -> False.
  intros.
  inversion H.
  inversion H6.
  destruct n1; inversion H8.
Qed.

Lemma htf2 l1 l2 l3 l3' b:
almost_eq_tape (true :: l1, b, l3) (false :: l2, b, l3') -> False.
  intros.
  inversion H.
  inversion H2.
  destruct n1; inversion H8.
Qed.

Lemma hft2 l1 l2 l3 l3' b:
almost_eq_tape (false :: l1, b, l3) (true :: l2, b, l3') -> False.
  intros.
  inversion H.
  inversion H2.
  destruct n2; inversion H9.
Qed.

Lemma htn l1:
almost_eq (true :: l1) [] -> False.
  intros.
  inversion H.
  destruct n1; inversion H1.
Qed.



Lemma almost_eq_step q q' t1 t t' :
              almost_eq_tape t' t ->
              step (q, t) = Some (q', t1) ->
              exists t0, step (q, t') = Some (q', t0) /\ almost_eq_tape t0 t1.
Proof.
  intros.
  destruct (step (q, t')) eqn:H1.
  - destruct p. 
    apply almost_eq_tape_sym in H.
    assert (H2 := almost_eq_tape_step_Some M' _ _ _ _ _ _ _ H H0 H1).
    destruct H2.
    rewrite <- H2.
    exists p.
    split.
    + reflexivity.
    + apply almost_eq_tape_sym in H3. apply H3.
  - assert (H2 := almost_eq_tape_step_None M' _ _ _ H H1). congruence.


  (* intros.
  unfold step in H0.
  destruct t.
  destruct p.
  destruct (trans' M' (q, b)) eqn:E.
  - destruct p.
    destruct p.
    injection H0.
    intros.
    destruct t'.
    destruct p.
    destruct b1, b. 2,3: inversion H.
    + induction l2, l0.
      * induction l1, l.
        -- destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 1,2,3,4: constructor; apply almost_eq_refl.
        -- destruct b. 1: destruct (h2 [] [] l true H).
           destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
           1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 1,3,5,7: repeat constructor; apply H'. 1,2: constructor; apply H''. 1,2:   apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct a. 1: apply almost_eq_tape_sym in H. 1: destruct (h2 [] [] l1 true H).
           destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
           1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 1,3,5,7: repeat constructor; apply H'. 1,2,3,4: repeat constructor. 1,2: apply H''. 1,2: apply almost_eq_sym in H''; apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 
        1,2,3,4: apply h3 in H; destruct H as [H' H'']; destruct a, b. 2,6,10,14: apply h5 in H''; destruct H''. 2,5,8,11: apply almost_eq_sym in H''; apply h5 in H''; destruct H''. 1,2,3,4,5,6,7,8: constructor. 1,3,5,7,9,11,13, 15: repeat constructor; apply H'. 1,2,3,4: constructor; apply H''. 1,2,3,4: apply h6 in H''; apply H''.
        
           
    * induction l1, l.
      -- destruct b. 1: destruct (h1 [] [] l0 true H). destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,6,8: repeat constructor; apply H''. 1,2: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: constructor; apply H'.
      -- destruct b, b1. 1,2: apply h1 in H; destruct H. 1: apply h2 in H; destruct H. destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
      1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4: repeat constructor; apply H''. 3,5: repeat constructor; apply H'. 1,2: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
      -- destruct a, b. 1,3: apply h1 in H; destruct H. 1: apply almost_eq_tape_sym in H; apply h2 in H; destruct H.
        destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4: repeat constructor; apply H''. 3,5: repeat constructor; apply H'. 1,2: apply h4 in H'; destruct H'; rewrite H;replace [] with (repeat false 0) by easy; constructor. 1,2: apply almost_eq_sym in H''; apply h4 in H''; destruct H''; rewrite H;replace [] with (repeat false 0) by easy; constructor.
      -- destruct a,b,b1. 1,2,5,6: apply h1 in H; destruct H. 2: apply h7 in H; destruct H. 2: apply hft1 in H; destruct H.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity.
        1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,10,12: constructor; apply H''. 3,5,9,11: constructor; apply H'. 1,2,5,6: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2,3,4: apply h6 in H''; apply H''.
  
    * induction l1, l.
      --   destruct a. 1: apply almost_eq_tape_sym in H; apply h1 in H; destruct H.
        1: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 
        1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,6,8: repeat constructor; apply H''. 1,2: apply almost_eq_sym in H'; apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: constructor; apply H'.
      -- destruct a, b. 1,3: apply h2 in H; destruct H. 1: apply almost_eq_tape_sym in H; apply h1 in H; destruct H.
        destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
         1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4: constructor; apply H''. 3,5: constructor; apply H'. 1,2: apply almost_eq_sym in H'; apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
      -- destruct a, a0; apply almost_eq_tape_sym in H. 1,2: apply h1 in H; destruct H. 1: apply h2 in H; destruct H.
        1: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 
        1,2,3,4: apply h3 in H; destruct H as [H' H'']; apply almost_eq_tape_sym; constructor. 2,4: constructor; apply H''. 3,5: constructor; apply H'. 1,2: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
      -- destruct a, a0, b. 2,3,4: apply almost_eq_tape_sym in H; apply h1 in H; destruct H. 1: apply almost_eq_tape_sym in H; apply h1 in H; destruct H. 2: apply h3 in H; destruct H as [H' H'']; apply h5 in H''; destruct H''. 2: apply almost_eq_tape_sym in H; apply h3 in H; destruct H as [H' H'']; apply h5 in H''; destruct H''.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity. 
         1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,10,12: constructor; apply H''. 3,5,9,11: constructor; apply H'. 1,2,5,6: apply almost_eq_sym in H'; apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2,3,4: apply h6 in H''; apply H''.

    * induction l1, l.
      -- destruct a, b. 2: apply htf2 in H; destruct H. 2: apply hft2 in H; destruct H.
         1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity. 
         1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor.
         2,4,10,12: repeat constructor; apply H''. 3,5,9,11: constructor; apply H'. 3,4,7,8: apply H''. 1,2,3,4: apply h6 in H'; apply H'.
      -- destruct a,b,b1. 1,3,5,7: apply h2 in H; destruct H. 2: apply htf2 in H; destruct H. 2: apply hft2 in H; destruct H.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity. 
        1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor.
        2,4,10,12: constructor; apply H''. 3,5,9,11: constructor; apply H'. 1,2,5,6: apply h6 in H'; apply H'. 1,2,3,4: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
      -- destruct a, a0, b. 2,4: apply htf2 in H; destruct H. 3,5: apply hft2 in H; destruct H. 1,3: apply almost_eq_tape_sym in H; apply h2 in H; destruct H.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity.
        1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor.
         2,4,10,12: repeat constructor; apply H''. 3,5,9,11: constructor; apply H'. 3,4,7,8: apply almost_eq_sym in H''; apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
         1,2,3,4: apply h6 in H'; apply H'.
      --  destruct a, a0, b, b1. 2,4,10,12: apply htf1 in H; destruct H. 2,5,6: apply htf2 in H; destruct H. 2: apply hft1 in H; destruct H. 3,5,6: apply hft2 in H; destruct H. 4: apply hft1 in H; destruct H.
        1,2,3,4: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31: now reflexivity.
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16:
        apply h3 in H; destruct H as [H' H'']; constructor.
        2,4,10,12,18,20,26,28: constructor; apply H''.
        3,5,9,11,15,17,21,23: constructor; apply H'.
        1,2,5,6,9,10,13,14: apply h6 in H'; apply H'.
        1,2,3,4,5,6,7,8: apply h6 in H''; apply H''.



    + induction l2, l0.
      * induction l1, l.
        -- destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 1,2,3,4: constructor; apply almost_eq_refl.
        -- destruct b. 1: apply h2 in H; destruct H.
           destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
           1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 1,3,5,7: repeat constructor; apply H'. 1,2: constructor; apply H''. 1,2:   apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct a. 1: apply almost_eq_tape_sym in H. 1: apply h2 in H; destruct H.
           destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
           1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 1,3,5,7: repeat constructor; apply H'. 1,2,3,4: repeat constructor. 1,2: apply H''. 1,2: apply almost_eq_sym in H''; apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 
        1,2,3,4: apply h3 in H; destruct H as [H' H'']; destruct a, b. 2,6,10,14: apply h5 in H''; destruct H''. 2,5,8,11: apply almost_eq_sym in H''; apply h5 in H''; destruct H''. 1,2,3,4,5,6,7,8: constructor. 1,3,5,7,9,11,13, 15: repeat constructor; apply H'. 1,2,3,4: constructor; apply H''. 1,2,3,4: apply h6 in H''; apply H''.
      * induction l1, l.
        -- destruct b. 1: apply h1 in H; destruct H. destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,6,8: repeat constructor; apply H''. 1,2: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: constructor; apply H'.
        -- destruct b, b1. 1,2: apply h1 in H; destruct H. 1: apply h2 in H; destruct H. destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
      1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4: repeat constructor; apply H''. 3,5: repeat constructor; apply H'. 1,2: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct a, b. 1,3: apply h1 in H; destruct H. 1: apply almost_eq_tape_sym in H; apply h2 in H; destruct H.
        destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4: repeat constructor; apply H''. 3,5: repeat constructor; apply H'. 1,2: apply h4 in H'; destruct H'; rewrite H;replace [] with (repeat false 0) by easy; constructor. 1,2: apply almost_eq_sym in H''; apply h4 in H''; destruct H''; rewrite H;replace [] with (repeat false 0) by easy; constructor.
        --  destruct a,b,b1. 1,2,5,6: apply h1 in H; destruct H. 2: apply h7 in H; destruct H. 2: apply hft1 in H; destruct H.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity.
        1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,10,12: constructor; apply H''. 3,5,9,11: constructor; apply H'. 1,2,5,6: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2,3,4: apply h6 in H''; apply H''.
      * induction l1, l.
        -- destruct a. 1: apply almost_eq_tape_sym in H; apply h1 in H; destruct H.
        1: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 
        1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,6,8: repeat constructor; apply H''. 1,2: apply almost_eq_sym in H'; apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: constructor; apply H'.
        -- destruct a, b. 1,3: apply h2 in H; destruct H. 1: apply almost_eq_tape_sym in H; apply h1 in H; destruct H.
        destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity.
         1,2,3,4: apply h3 in H; destruct H as [H' H'']; constructor. 2,4: constructor; apply H''. 3,5: constructor; apply H'. 1,2: apply almost_eq_sym in H'; apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct a, a0; apply almost_eq_tape_sym in H. 1,2: apply h1 in H; destruct H. 1: apply h2 in H; destruct H.
        1: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7: now reflexivity. 
        1,2,3,4: apply h3 in H; destruct H as [H' H'']; apply almost_eq_tape_sym; constructor. 2,4: constructor; apply H''. 3,5: constructor; apply H'. 1,2: apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct a, a0, b. 2,3,4: apply almost_eq_tape_sym in H; apply h1 in H; destruct H. 1: apply almost_eq_tape_sym in H; apply h1 in H; destruct H. 2: apply h3 in H; destruct H as [H' H'']; apply h5 in H''; destruct H''. 2: apply almost_eq_tape_sym in H; apply h3 in H; destruct H as [H' H'']; apply h5 in H''; destruct H''.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity. 
         1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor. 2,4,10,12: constructor; apply H''. 3,5,9,11: constructor; apply H'. 1,2,5,6: apply almost_eq_sym in H'; apply h4 in H'; destruct H'; rewrite H; replace [] with (repeat false 0) by easy; constructor. 1,2,3,4: apply h6 in H''; apply H''.
      * induction l1, l.
        -- destruct a, b. 2: apply htf2 in H; destruct H. 2: apply hft2 in H; destruct H.
         1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity. 
         1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor.
         2,4,10,12: repeat constructor; apply H''. 3,5,9,11: constructor; apply H'. 3,4,7,8: apply H''. 1,2,3,4: apply h6 in H'; apply H'.
        -- destruct a,b,b1. 1,3,5,7: apply h2 in H; destruct H. 2: apply htf2 in H; destruct H. 2: apply hft2 in H; destruct H.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity. 
        1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor.
        2,4,10,12: constructor; apply H''. 3,5,9,11: constructor; apply H'. 1,2,5,6: apply h6 in H'; apply H'. 1,2,3,4: apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
        -- destruct a, a0, b. 2,4: apply htf2 in H; destruct H. 3,5: apply hft2 in H; destruct H. 1,3: apply almost_eq_tape_sym in H; apply h2 in H; destruct H.
        1,2: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15: now reflexivity.
        1,2,3,4,5,6,7,8: apply h3 in H; destruct H as [H' H'']; constructor.
         2,4,10,12: repeat constructor; apply H''. 3,5,9,11: constructor; apply H'. 3,4,7,8: apply almost_eq_sym in H''; apply h4 in H''; destruct H''; rewrite H; replace [] with (repeat false 0) by easy; constructor.
         1,2,3,4: apply h6 in H'; apply H'.
        -- destruct a, a0, b, b1. 2,4,10,12: apply htf1 in H; destruct H. 2,5,6: apply htf2 in H; destruct H. 2: apply hft1 in H; destruct H. 3,5,6: apply hft2 in H; destruct H. 4: apply hft1 in H; destruct H.
        1,2,3,4: destruct d; simpl in H1; rewrite <- H1; destruct b0; unfold step; rewrite E; rewrite H2; simpl; eexists _; split. 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31: now reflexivity.

        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16:
        apply h3 in H; destruct H as [H' H'']; constructor.
        2,4,10,12,18,20,26,28: constructor; apply H''.
        3,5,9,11,15,17,21,23: constructor; apply H'.
        1,2,5,6,9,10,13,14: apply h6 in H'; apply H'.
        1,2,3,4,5,6,7,8: apply h6 in H''; apply H''.

    

    - inversion H0. *)

Qed.





      
    



Lemma almost_eq_steps  k q q' t1 t t' :
              almost_eq_tape t' t ->
              steps k (q, t) = Some (q', t1) ->
              exists t0, steps k (q, t') = Some (q', t0) /\ almost_eq_tape t0 t1.
Proof.
  revert q q' t1 t t'.
  induction k.
  - intros.
    simpl.
    simpl in H0.
    injection H0.
    intros.
    exists t'.
    rewrite <- H1.
    rewrite H2.
    split.
    + reflexivity. 
    + apply H.
  - intros.
    replace (S k) with (1 + k) in H0 by lia.
    rewrite steps_plus in H0.
    destruct (steps 1 (q,t)) eqn:E.
    2: inversion H0.

    destruct p.

    assert (E2 := almost_eq_step).

  
    unfold obind in H0.
    unfold oapp in H0.



    specialize (E2 q t0 p t t' H E).

    destruct E2. destruct H1.

    specialize (IHk t0 q' t1 p x H2 H0).
    destruct IHk.

    eexists _.
    replace (S k) with (1 + k) by lia.
    rewrite steps_plus.
    simpl ((steps 1 (q, t'))).
    rewrite H1.

    unfold obind.
    unfold oapp.

    apply H3.
Qed.



Lemma almost_eq_spec x l:
almost_eq (repeat false x) l -> exists n, l = repeat false n.
Proof.
  intros.
  revert H.
  revert x.
  induction l.
  - exists 0. reflexivity.
  - induction x.
    + destruct a; intros.
      * inversion H. destruct n2; inversion H2.
      * simpl in H. apply h4 in H. destruct H. rewrite H. exists (S x). easy.
    + destruct a; intros.
      * inversion H. destruct n2; inversion H2.
      * simpl in H. apply h6 in H. specialize (IHl _ H). destruct IHl. rewrite H0. exists (S x0). easy.
Qed.

Lemma almost_eq_elim l1 l2 :
  almost_eq l1 l2 -> 
  match l1 with
  | [] => l2 = repeat false (length l2)
  | a :: l1' =>
      match l2 with
      | [] => l1 = repeat false (length l1)
      | b :: l2' => a = b /\ almost_eq l1' l2'
      end
  end.
Proof.
  intros H.
  induction H. 1: done.
  destruct n1,n2; cbn.
  - reflexivity.
  - rewrite repeat_length. reflexivity.
  - rewrite repeat_length. reflexivity.
  - repeat constructor.
Qed.


Lemma almost_eq_trans l1 l2 l3 :
  almost_eq l1 l2 -> almost_eq l2 l3 -> almost_eq l1 l3.
Proof.
  intros H.
  revert l3.
  induction H.
  - induction l3.
    + intros. apply almost_eq_elim in H0. simpl in H0. injection H0. intros. subst. rewrite H1 in H. apply almost_eq_sym in H. apply almost_eq_spec in H. destruct H. rewrite H. replace (false :: repeat false x) with (repeat false (S x)) by easy. replace [] with (repeat false 0) by easy. constructor.
    + intros. apply almost_eq_elim in H0. destruct H0. subst. constructor. apply IHalmost_eq. apply H1.
  - intros. apply almost_eq_spec in H. destruct H. rewrite H. constructor.

  (* revert l1 l2 l3.
  induction l1, l2, l3; intros.
  - apply H.
  - apply H0.
  - replace ([]) with (repeat false 0) by easy.
    constructor.
  - destruct b. 1: inversion H; destruct n2; inversion H3.
    destruct b0. 1: inversion H0; destruct n2; inversion H3.
    apply h4 in H. destruct H. rewrite H in H0. inversion H0. 2: replace ([]) with (repeat false 0) by easy; constructor.

    apply almost_eq_spec in H2. destruct H2. rewrite H2. replace (false :: repeat false x0) with (repeat false (S x0)) by easy. replace ([]) with (repeat false 0) by easy. constructor.
  
  - apply H.
  - destruct a. 1: inversion H; destruct n1; inversion H2.
    destruct b. 1: inversion H0; destruct n2; inversion H3.
    apply almost_eq_cons.
    apply h4 in H0. destruct H0. apply almost_eq_sym in H. apply h4 in H. destruct H. rewrite H H0. constructor.
  - destruct a, b. 1,3: inversion H0; destruct n1; inversion H2.
    1: inversion H; destruct n1; inversion H2.
    apply almost_eq_sym in H0. apply h4 in H0. destruct H0. rewrite H0 in H. apply h6 in H. apply almost_eq_sym in H. apply almost_eq_spec in H. destruct H. rewrite H. replace (false :: repeat false x0) with (repeat false (S x0)) by easy. replace ([]) with (repeat false 0) by easy. constructor.
  - destruct a, b, b0. 2,6: inversion H0; destruct n1; inversion H2. 2,5: inversion H0; destruct n2; inversion H3. 2: inversion H; destruct n1; inversion H2. 2: inversion H; destruct n2; inversion H3.
    1,2: apply h6 in H; apply h6 in H0; constructor; specialize (IHl1 _ _ H H0); apply IHl1. *)
Qed.
    
    
Lemma almost_eq_tape_trans t1 t2 t3 :
  almost_eq_tape t1 t2 -> almost_eq_tape t2 t3 -> almost_eq_tape t1 t3.
Proof.
  intros.
  destruct t1, t2, t3; destruct p, p0, p1.
  destruct b, b0, b1.
  2,3,6,7: inversion H0. 2,3: inversion H. 1,2: apply h3 in H; destruct H; apply h3 in H0; destruct H0; assert (T1 := almost_eq_trans _ _ _ H H0); assert (T2 := almost_eq_trans _ _ _ H1 H2); constructor. 1,3: apply T1. 1,2: apply T2.
Qed.



(* TODO used dependent destruction here*)
Require Import Coq.Program.Equality.

Lemma vector_rewrite (t : Vector.t (TM.tape (finType_CS bool)) 1) : | Vector.hd t | = t.
Proof.
  dependent destruction t.
  cbn.
  dependent destruction t.
  reflexivity.
Qed.

  


Lemma truncate_almost_eq t1 t2:
truncate_tape t1 = truncate_tape t2 -> almost_eq_tape t1 t2.
Proof.
  intros.
  assert (H1 := almost_eq_tape_truncate_tape t1).
  assert (H2 := almost_eq_tape_truncate_tape t2).
  rewrite H in H1.
  apply almost_eq_tape_sym in H1.
  assert (T := almost_eq_tape_trans).
  specialize (T _ _ _ H1 H2).
  apply T.
Qed.


Lemma simulation_output q q' t t' t''':
  TM.eval M q t q' t' ->
  almost_eq_tape t''' (encode_tape (Vector.hd t)) ->
  (exists k l, steps k ((encode_state q), t''') = Some (encode_state q', l)
  /\
  steps (S k) ((encode_state q), t''') = None /\
  almost_eq_tape l ((encode_tape (Vector.hd t')))
  ).
Proof.
  intros H.

  (* destruct H as [q' H]. *)
  rewrite TM_facts.TM_eval_iff in H.
  destruct H as [n H].

  revert q q' t t' t''' H.

  induction n.
  - intros.
    simpl in H.
    destruct (TM_facts.haltConf (TM_facts.mk_mconfig q t)) eqn:H1.
    + inversion H.
      exists 0.
      (* exists (encode_state q'). *)
      exists (t''').
      simpl.
      split.
      * reflexivity.
      * split.
        -- assert (X := simulation_halt).
           unfold TM_facts.haltConf in H1.
           unfold TM_facts.cstate in H1.
           specialize (X _ t''' H1).
           rewrite <- H3.
           apply X.
        -- rewrite <- H4. apply H0. 
    + inversion H.
  - intros.

      destruct (TM.halt q) eqn:H1.
      
      + simpl in H.
        unfold TM_facts.haltConf in H.
        unfold TM_facts.cstate in H.
        rewrite H1 in H.
        injection H.
        intros.
        
        exists 0.
        (* exists (encode_state q). *)
        exists (t''').
        simpl.
        split.
        * rewrite H3. reflexivity.
        * split.
          -- assert (X := simulation_halt).
            specialize (X _ t''' H1).
            apply X.

          -- rewrite <- H2. apply H0.
      
      +

        assert (U4 : TM_facts.loopM (TM_facts.mk_mconfig q t) (S n) =
        TM_facts.loopM (TM_step (TM_facts.mk_mconfig q t)) n).
        
        * unfold TM_facts.loopM.
          unfold Prelim.loop.
          unfold TM_facts.haltConf.
          unfold TM_facts.cstate.
          rewrite H1.
          reflexivity.

        *
          rewrite U4 in H.
    
          assert (H2 := simulation_step).
          specialize (H2 q (Vector.hd t) H1).
          destruct H2 as [k H2].

          rewrite (vector_rewrite t) in H2.

    
          destruct (TM_step (TM_facts.mk_mconfig q t)) as [q'' t''].

          unfold omap in H2.
          unfold obind in H2.
          unfold oapp in H2.
          unfold encode_config in H2.


          destruct (steps (S k) (encode_state q, encode_tape (Vector.hd t))) eqn:Heq in H.
            -- 

            rewrite Heq in H2.
            
            destruct p.
            inversion H2.
            subst.
            (* injection H4. *)
            intros.
            (* rewrite H5 in Heq. *)
            
            simpl.

            (* assert (Y :
              almost_eq_tape t''' (encode_tape (Vector.hd t)) ->
              almost_eq_tape p (encode_tape (Vector.hd t'')) ->
              steps (S k) (encode_state q, encode_tape (Vector.hd t)) =
Some (encode_state q'', p) ->


              exists t0, steps (S k) (encode_state q, t''') = Some (encode_state q'', t0) /\ almost_eq_tape t0 p
              
            
            
            ). *)

            assert (Y := almost_eq_steps).
            specialize (Y _ _ _ _ _ _ H0 Heq).
            destruct Y.
            destruct H3.

            assert (T1 := truncate_almost_eq _ _ H5).
            assert (Z := almost_eq_tape_trans _ _ _ H4 T1).

            specialize (IHn q'' q' t'' t' x H Z).

            destruct IHn as [k0 IHn].
            (* destruct IHn as [q'0 IHn]. *)
            destruct IHn as [l IHn].
            destruct IHn as [IHn1 IHn2].
            destruct IHn2 as [IHn2 IHn3].

            exists ((S k) + k0).
            (* exists q'0. *)
            exists l.

            split.
            ++ assert (U := @SBTM_facts.steps_plus).
            specialize (U M' (S k) k0 ((encode_state q, t'''))).

            rewrite U.

            (* rewrite Heq. But these are almost_eq by H0 *)



            rewrite H3.
            simpl.

            apply IHn1.
            ++ split.
              ** unfold steps.
                rewrite <- Nat.iter_succ.
                replace (S (S k + k0)) with (S k + S k0) by lia.

               
               assert (U := @SBTM_facts.steps_plus).
            specialize (U M' (S k) (S k0) ((encode_state q, t'''))).
              

              replace (steps (S k + S k0) (encode_state q, t''')) with (Nat.iter (S k + S k0) (SBTM.obind step) (Some (encode_state q, t'''))) in U by easy.
              rewrite U.
              rewrite H3.
              unfold obind.
              unfold oapp.
              apply IHn2.








              ** apply IHn3.


            

            -- 
            
            
               rewrite Heq in H2.
               inversion H2.


Qed.

  





  Lemma inverse_simulation q t k :
    steps k ((encode_state q), (encode_tape (Vector.hd t))) = None ->
    exists q' t', TM.eval M q t q' t'.
  Proof.
    elim: k q t; first done.
    move=> k IH q t.
    move Hq: (TM.halt q) => [|].
    { move=> _. exists q, t. by apply: TM.eval_halt. }
    move: (Hq) => /simulation_step => /(_ (Vector.hd t)).
    move=> [k1].
    move Hk1: (steps (S k1) _) => [[q' t']|]; last done.
    move=> [] Hq't'.
    move: Hk1 => /steps_sync H /H{H} /steps_truncate.
    move E: (TM_step _) Hq't' => [q'' t''].
    move=> [] -> -> /steps_truncate /IH.
    move=> [q'''] [t'''] /TM_facts.TM_eval_iff [n Hn].
    exists q''', t'''. apply /TM_facts.TM_eval_iff. exists (S n).
    rewrite /= /TM_facts.haltConf Hq -Hn -E (Vector.eta t) /=.
    move: (Vector.tl t). by apply: Vector.case0.
  Qed.







(* Lemma test q q' (t : Vector.t (TM.tape (finType_CS bool)) 1) t'' t''' k :
  let (q'', t_step) := (TM_step (TM_facts.mk_mconfig q t)) in
  steps k ((encode_state q), t'') = Some (encode_state q', t''') ->
  steps (S k) ((encode_state q), t'') = None -> 
  almost_eq_tape t'' (encode_tape (Vector.hd t)) ->
  exists t2' k1 k2,
  steps k1 ((encode_state q), t'') = Some ((encode_state q''), t2') /\ 
  almost_eq_tape t2' (encode_tape (Vector.hd t_step)) /\
  steps k2 ((encode_state q''), t2') = Some (encode_state q', t''') /\
  steps (S k2) ((encode_state q''), t2') = None /\
  k1 + k2 = k.
Proof.
  revert q q' t t'' t'''.
  assert (I := ax_nat_lt_ind).
  specialize ( I (fun k => 
    forall (q q' : TM.state M)
  (t : Vector.t (TM.tape (finType_CS bool)) 1)
  (t'' t''' : tape),
let (q'', t_step) :=
  TM_step (TM_facts.mk_mconfig q t) in
steps k (encode_state q, t'') =
Some (encode_state q', t''') ->
steps (S k) (encode_state q, t'') = None ->
almost_eq_tape t'' (encode_tape (Vector.hd t)) ->
exists (t2' : tape) (k1 k2 : nat),
  steps k1 (encode_state q, t'') =
Some (encode_state q'', t2') /\
almost_eq_tape t2' (encode_tape (Vector.hd t_step)) /\
steps k2 (encode_state q'', t2') =
Some (encode_state q', t''') /\
steps (S k2) (encode_state q'', t2') = None /\
k1 + k2 = k
  )).

  apply I.
  clear I.
  intros.
  destruct n.
  - admit.
  - destruct (TM_step (TM_facts.mk_mconfig q t)) as [q'' t_step] eqn:Y.
    intros.

    assert (X := simulation_step).
    specialize (X q (Vector.hd t)).
    assert (TM.halt q = false) by admit.
    specialize (X H3).
    rewrite vector_rewrite in X.
    rewrite Y in X.
    unfold encode_config in X.
    destruct X as [k0 X].

    eexists _.
    eexists (S k0).
    eexists _.

    destruct (steps (S k0)
  (encode_state q, encode_tape (Vector.hd t))) eqn:N.
    2: admit.





Admitted. *)

Print TM_config.

(* Lemma t n k0 q q' t t':
  steps n (encode_state q, encode_tape t) = Some (q', t') ->
  steps (S n) (encode_state q, encode_tape t) = None ->
  steps (S k0) (encode_state q, encode_tape t) = Some (encode_config (TM_step (TM_facts.mk_mconfig q (| t |)))) -> S k0 <= n.
Proof.
  revert q q' t t' k0.

  assert (I := ax_nat_lt_ind).
  specialize ( I (fun n => 

  forall (q : TM.state M) (q' : state)
  (t : TM.tape (finType_CS bool)) (t' : tape) (k0 : nat),
steps n (encode_state q, encode_tape t) = Some (q', t') ->
steps (S n) (encode_state q, encode_tape t) = None ->
steps (S k0) (encode_state q, encode_tape t) =
Some
  (encode_config
  (TM_step (TM_facts.mk_mconfig q (| t |)))) ->
S k0 <= n

  )).

  apply I.
  clear I.
  intros.
  destruct n0.
  + admit.
Admitted. *)

  
  

  
(* Axiom (ax_nat_lt_ind : forall (P : nat -> Prop),
       (forall (n : nat), (forall m, m < n -> P m) -> P n) ->
       forall (n : nat), P n).


Lemma inverse_simulation_output q q' t t'' t''' k :

  steps k (encode_state q, t'') = Some (encode_state q', t''') ->
  steps (S k) (encode_state q, t'') = None ->
  almost_eq_tape t'' (encode_tape (Vector.hd t)) ->
  exists t', (TM.eval M q t q' t' /\ almost_eq_tape t''' (encode_tape (Vector.hd t'))).
Proof.

  revert q q' t t'' t'''.


  induction k1 using (Nat.measure_induction _ (fun x => x)).
  induction k1 using lt_wf_ind. (* Arith importieren *)

  assert (I := ax_nat_lt_ind).
  specialize ( I (fun k => 
  
    forall (q q' : TM.state M)
  (t : Vector.t (TM.tape (finType_CS bool)) 1)
  (t'' t''' : tape),
steps k (encode_state q, t'') =
Some (encode_state q', t''') ->
steps (S k) (encode_state q, t'') = None ->
almost_eq_tape t'' (encode_tape (Vector.hd t)) ->
exists t' : Vector.t (TM.tape (finType_CS bool)) 1,
  TM.eval M q t q' t' /\
almost_eq_tape t''' (encode_tape (Vector.hd t'))
  
  )).

  apply I.
  clear I.
  intros.
  destruct n.
  - clear H.

    destruct (TM.halt q) eqn:H3.
    + simpl in H0.
      injection H0.
      intros.
      exists t.
      assert (q = q') by admit.
      rewrite <- H5.
      split.
      * constructor. apply H3.
      * rewrite <- H. apply H2.









    + 
      assert (Y := @almost_eq_tape_steps_None).
      specialize (Y M' 1 (encode_state q) _ _ H2).
      rewrite Y in H1.
    
      assert (X := simulation_step).
      specialize (X q (Vector.hd t) H3).
      destruct X.
      rewrite vector_rewrite in H.

      assert (Z := @steps_None_mono).
      specialize (Z M' (encode_state q, encode_tape (Vector.hd t)) (S x) 1 H1).
      assert (1 <= S x) by lia.
      specialize (Z H4).
      rewrite Z in H.
      cbn in H.
      inversion H.










  -
    assert (X := simulation_step).
    specialize (X q (Vector.hd t)).
    destruct (TM.halt q) eqn:H3.
    + 
    assert (J := simulation_halt).
    specialize (J q t'' H3).
    assert (P := @steps_None_mono).
    specialize (P M' (encode_state q, t'') (S n) 1 J).
    assert (U : 1 <= S n) by lia.
    specialize (P U).
    rewrite P in H0.
    inversion H0.

    +
    specialize (X eq_refl).
    destruct X as [k0 X].
    rewrite vector_rewrite in X.





    destruct (TM_step (TM_facts.mk_mconfig q t)) as [q_step t_step] eqn:V.
    unfold encode_config in X.

    destruct ((steps (S k0)
  (encode_state q, encode_tape (Vector.hd t)))) eqn:B. 
  
    2: cbn in X; inversion X.


    destruct p as [q_des t_des].
    simpl in X.
    inversion X.




    rewrite H5 in B.









  assert (Y := almost_eq_steps).

  specialize (Y (S k0) (encode_state q) (encode_state q_step) t_des (encode_tape (Vector.hd t)) t'' H2 B).

  destruct Y as [t_step' Y].
  destruct Y as [Y1 Y2].


        remember (S n - S k0) as k1 eqn:Ek1.
    
    assert (k1 < S n) by lia.
    assert (S k0 <= S n) by admit.
    assert (S k0 + k1 = S n) by lia.
    specialize (H k1).
    specialize (H H4).

        rewrite <- H8 in H0.
    rewrite steps_plus in H0.

  rewrite Y1 in H0.
  simpl in H0.

  specialize (H q_step q' t_step t_step' t''' H0).


  rewrite <- H8 in H1.
  replace (S (S k0 + k1)) with (S k0 + S k1) in H1 by lia.
  rewrite steps_plus in H1.
  rewrite Y1 in H1.
  unfold obind in H1.
  unfold oapp in H1.

  assert (C := truncate_almost_eq _ _ H6).
  assert (D := almost_eq_tape_trans _ _ _ Y2 C).




  specialize (H H1 D).

  destruct H as [t_end H].
  destruct H as [IH1 IH2].

  exists t_end.

  split.
  2: apply IH2.

  rewrite TM_facts.TM_eval_iff.
  rewrite TM_facts.TM_eval_iff in IH1.

  destruct IH1 as [n0 IH1].

  exists (S n0).

  simpl.
  unfold TM_facts.haltConf.
  cbn.
  rewrite H3.
  rewrite V.
  apply IH1. *)





(* 

  assert (T := test).
  specialize (T q q' t t'' t''' (S n)).
  destruct (TM_step (TM_facts.mk_mconfig q t)) as [q'' t_step] eqn:E.
  specialize (T H0 H1 H2).
  destruct T as [t2' T].
  destruct T as [k1 T].
  destruct T as [k2 T].
  destruct T as [T1 T2].
  destruct T2 as [T2 T3].
  destruct T3 as [T3 T4]. 
  destruct T4 as [T4 T5]. 

  specialize (H k2).
  assert (k2 < S n) by admit.
  specialize (H H3).

  specialize (H _ _ _ _ _ T3 T4 T2).

  destruct H as [t' H].
  destruct H as [HA HB].

  eexists t'.

  split.
  + 
  rewrite TM_facts.TM_eval_iff.
  rewrite TM_facts.TM_eval_iff in HA.

  destruct HA as [n0 HA].

  exists (S n0).

  simpl.

  destruct (TM_facts.haltConf (TM_facts.mk_mconfig q t)).
  * admit.
  * rewrite E.
    apply HA.

  + apply HB.





    




  
















  revert q q' t t'' t'''.
  induction k.
  - intros.
    simpl in H0.
    simpl in H.
    injection H. intros.
    assert (q = q') by admit.
    exists t.
    subst.
    destruct (TM.halt q') eqn:H5.
    + split. 2: apply H1. constructor. apply H5.
    + assert (H6 := simulation_step).
      specialize (H6 _ (Vector.hd t) H5).
      destruct H6.
      assert (H7 := @almost_eq_tape_steps_None).
      rewrite (H7 M' 1 (encode_state q') _ _ H1) in H0.
      assert (H8 := @steps_None_mono).
      assert (1 <= S x) by lia.
      specialize (H8 M' _ (S x) _ H0 H4).
      rewrite H8 in H2.
      simpl in H2.
      inversion H2.
  - intros.
    destruct (TM.halt q) eqn:H2.
    + eexists _.
      assert (H4 := simulation_halt q t'' H2).
      replace (S k) with (1 + k) in H by lia.
      rewrite steps_plus in H.
      simpl in H.
      rewrite H4 in H.
      cbn in H.
      inversion H.
    + assert (H4 := simulation_step).
      specialize (H4 q (Vector.hd t) H2).
      destruct H4.
      rewrite vector_rewrite in H3.

      destruct (TM_step (TM_facts.mk_mconfig q t)) as [q'' tx] eqn:E.

      unfold omap in H3.
      unfold obind in H3.
      unfold oapp in H3.
      unfold encode_config in H3.



      destruct (steps (S x) (encode_state q, encode_tape (Vector.hd t))) eqn:Heq in H.
      -- rewrite Heq in H3.
         destruct p.
         inversion H3.
         clear H3.
         clear E.







      -- rewrite Heq in H3. inversion H3.
    
      

















  - intros.
    simpl in H.
    injection H.
    intros.
    eexists t.
    assert (q = q') by admit.
    subst.
    split. 2: apply H0.
    destruct (TM.halt q') eqn:H3.
    + constructor. apply H3.
    + assert (H4 := simulation_step _ (Vector.hd t) H3).
      destruct H4 as [k H4].

      rewrite (vector_rewrite t) in H4.

      destruct (TM_step (TM_facts.mk_mconfig q' t)) as [q'' t''] eqn:E.

      unfold omap in H4.
      unfold obind in H4.
      unfold oapp in H4.
      unfold encode_config in H4.
      admit.





  - intros.
    destruct (TM.halt q) eqn:H1.
    + eexists _.
      assert (H4 := simulation_halt q t'' H1).
      replace (S k) with (1 + k) in H by lia.
      rewrite steps_plus in H.
      simpl in H.
      rewrite H4 in H.
      cbn in H.
      inversion H.
    + assert (H4 := simulation_step q (Vector.hd t) H1).
      destruct H4 as [x H4].

      rewrite (vector_rewrite t) in H4.

      destruct (TM_step (TM_facts.mk_mconfig q t)) as [q'' tx] eqn:E.

      unfold omap in H4.
      unfold obind in H4.
      unfold oapp in H4.
      unfold encode_config in H4.



      destruct (steps (S x) (encode_state q, encode_tape (Vector.hd t))) eqn:Heq in H.
      -- rewrite Heq in H4.
         destruct p.
         inversion H4.





      -- rewrite Heq in H4. inversion H4. *)



  (* Admitted. *)
    
    


    


End Construction.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Undecidability.TM.Reductions.Arbitrary_to_Binary.


(* TODO existentially quantified q' *)
Lemma SBTM_simulation (M : TM.TM (finType_CS bool) 1) :
  {M' : SBTM & 
    { q_start : SBTMNotations.state M' |
        ((forall q t t' t'', TM.eval M (TM.start M) t q t' ->
         SBTM_facts.almost_eq_tape t'' (encode_tape (Vector.hd t)) ->
         exists k q' t''', (SBTM.steps M' k (q_start, t'') = Some (q', t''') /\
         SBTM.steps M' (S k) (q_start, t'') = None /\
         almost_eq_tape t'''  (encode_tape (Vector.hd t')))))
        
        /\
        (forall t, (exists k, SBTM.steps M' k (q_start, (encode_tape (Vector.hd t))) = None) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}}.
Proof.
  exists (M' M).
  exists ((encode_space M (space_base M (TM.start M)))).
  split.
  - intros.
    assert (U := simulation_output).
    specialize (U M (TM.start M) q t t' t'' H H0).
    destruct U.
    destruct H1.
    eexists _.
    eexists _.
    eexists _.
    apply H1.

  - intros.
    destruct H as [k H].
    assert (U := inverse_simulation).
    specialize (U M (TM.start M) t k H).
    apply U.
Qed.


Theorem reduction :
  TM.HaltTM 1 ⪯ SBTM_HALT.
Proof.
  apply: (reduces_transitive Arbitrary_to_Binary.reduction).
  exists (fun '(M, t) =>
    existT _ (M' M) (encode_config M (TM_facts.mk_mconfig (TM.start M) t))).
  move=> [M t]. split.
  - cbn.
  move=> /simulation [k Hk]. exists k.
    by move: Hk => /steps_truncate.
  - by move=> [k] /steps_truncate /inverse_simulation.
Qed.
