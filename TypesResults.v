Require Import Types.
Require Import Tactics.

Fixpoint remove x G :=
match G with
| env_Nil => env_Nil
| env_Cons G' x' A => if eq_termvar x' x then G' else env_Cons (remove x G') x' A
end.

Lemma env_type_eq: forall {x A A' G},
  Env x A G ->
  Env x A' G ->
  A = A'.
induction G.
* intro ENV. inversion ENV.
* intros ENV1 ENV2.
  inversion ENV1; subst; inversion ENV2; subst; auto; congruence.
Qed.

Lemma env_remove: forall {x x' A G},
  Env x A G ->
  x <> x' ->
  Env x A (remove x' G).
induction G.
* inversion 1.
* intros ENV NE. simpl. destruct (eq_termvar x0 x').
  + subst. inversion ENV; subst. congruence. assumption.
  + inversion ENV; subst. constructor. constructor. auto. apply IHG; auto.
Qed.

Lemma env_remove_cons: forall {x1 x2 A1 A2 G},
  Env x1 A1 (env_Cons G x2 A2) ->
  Env x1 A1 (env_Cons (remove x2 G) x2 A2).
intros. inversion H; subst; eauto using Env, env_remove.
Qed.

Lemma env_remove_cons2: forall {x1 x2 x3 A1 A2 A3 G},
  Env x1 A1 (env_Cons (env_Cons G x2 A2) x3 A3) ->
  Env x1 A1 (env_Cons (env_Cons (remove x3 G) x2 A2) x3 A3).
intros. inversion H; subst; eauto using Env, env_remove.
constructor; auto; inversion H6; subst; eauto using Env, env_remove.
Qed.


Scheme vtyp_ind := Minimality for vtyp Sort Prop
  with ctyp_ind := Minimality for ctyp Sort Prop
  with handle_ind := Minimality for handle Sort Prop.
Combined Scheme typ_comb_ind from vtyp_ind, ctyp_ind, handle_ind.

Lemma env_extend: forall G G',
 (forall x A, Env x A G -> Env x A G') ->
 forall x' A', forall x A, Env x A (env_Cons G x' A') -> Env x A (env_Cons G' x' A').
intros G G' H x' A' x A ENV.
inversion ENV; subst; eauto using Env.
Qed.

Lemma env_variant:
  (forall G v A', vtyp G v A' -> forall G', (forall x A, Env x A G -> Env x A G') -> vtyp G' v A') /\
  (forall G e m C, ctyp G e m C -> forall G', (forall x A, Env x A G -> Env x A G') -> ctyp G' e m C) /\
  (forall G h A' E E' C, handle G h A' E E' C -> forall G', (forall x A, Env x A G -> Env x A G') -> handle G' h A' E E' C).
apply typ_comb_ind; eauto 10 using vtyp, ctyp, handle, env_extend.
Qed.

Corollary env_vtyp:
  forall {G v A'}, vtyp G v A' -> forall G', (forall x A, Env x A G -> Env x A G') ->  vtyp G' v A'.
apply (proj1 env_variant).
Qed.

Corollary env_ctyp:
  forall {G E m C}, ctyp G E m C -> forall G', (forall x A, Env x A G -> Env x A G') -> ctyp G' E m C.
apply (proj1 (proj2 env_variant)).
Qed.

Lemma eq_termvar_eq: forall {x} {A:Type} {P Q:A},
  (if eq_termvar x x then P else Q) = P.
intros. apply (decide_left (eq_termvar x x)); auto.
Qed.

Lemma eq_termvar_neq: forall {x x'} {A:Type} {P Q:A},
  x <> x' ->
  (if eq_termvar x x' then P else Q) = Q.
intros. apply (decide_right (eq_termvar x x')); auto.
Qed.

Lemma neq_sym: forall {A} {x x':A},
  x <> x' <-> x' <> x.
intuition.
Qed.

Lemma closed_vtyp_extend: forall {G v A},
  vtyp env_Nil v A ->
  vtyp G v A.
intros. apply (env_vtyp H).
intros. inversion H0.
Qed.

(* NB: Our substitution is only capture avoiding for closed values. *)

Lemma substitution: forall v A x,
  (forall G v' A', vtyp G v' A' -> Env x A G -> vtyp env_Nil v A -> vtyp (remove x G) (subst_value v x v') A') /\
  (forall G e m C, ctyp G e m C -> Env x A G -> vtyp env_Nil v A -> ctyp (remove x G) e (subst_comp v x m) C) /\
  (forall G h a e e' c, handle G h a e e' c -> Env x A G -> vtyp env_Nil v A -> handle (remove x G) (subst_handlers v x h) a e e' c).
intros v A x.
apply typ_comb_ind; eauto using vtyp, ctyp.
(* Value typings *)
* intros G x' A' ENV' ENV VT'.
  destruct (eq_termvar x x').
  + subst. simpl. apply (decide_left (eq_termvar x' x')). reflexivity. rewrite (env_type_eq ENV' ENV). auto using closed_vtyp_extend.
  + simpl. apply (decide_right (eq_termvar x' x)). auto. intro. constructor. auto using env_remove.

(* Computation typings *)
* intros G E v' x1 x2 m C A1 A2 VT' IH1 CT IH2 ENV VT. simpl in IH2 |- *.
  apply Split with (A1:=A1) (A2:=A2); auto.
  destruct (eq_termvar x1 x); subst.
  + apply (env_ctyp CT). apply env_extend. intros xx AA. apply env_remove_cons.
  + destruct (eq_termvar x2 x); subst.
    - apply (env_ctyp CT). intros xx AA. apply env_remove_cons2.
    - apply IH2; eauto using Env.
* intros G E v' x1 m1 x2 m2 C A1 A2 VT' VIH C1 C1IH C2 C2IH ENV VT.
  simpl in C1IH, C2IH |- *.
  econstructor; auto.
  + destruct (eq_termvar x1 x); subst.
    - apply (env_ctyp C1). intros xx AA. apply env_remove_cons.
    - apply C1IH; eauto using Env.
  + destruct (eq_termvar x2 x); subst.
    - apply (env_ctyp C2). intros xx AA. apply env_remove_cons.
    - apply C2IH; eauto using Env.
* intros G E x' m m' C A' C1 C1IH C2 C2IH ENV VT.
  simpl. econstructor; auto.
  simpl in C2IH |- *.
  destruct (eq_termvar x' x); subst.
  + apply (env_ctyp C2). intros xx AA. apply env_remove_cons.
  + apply C2IH; eauto using Env.
* intros G E x' m A' C CT CTIH ENV VT.
  simpl. econstructor; auto.
  simpl in CTIH |- *.
  destruct (eq_termvar x' x); subst.
  + apply (env_ctyp CT). intros xx AA. apply env_remove_cons.
  + apply CTIH; eauto using Env.
* intros G E m v' C A' CT CTIH VT' VIH ENV VT.
  simpl. econstructor; auto.
* intros G E m C1 C2 CT CTIH ENV VT.
  simpl. econstructor; auto.
* intros G E m C2 C1 CT CIH ENV VT.
  econstructor; auto.
* intros G E op v' x' m C A1 A2 EFF VT' VIH CT CIH ENV VT.
  simpl in CIH |- *. econstructor; eauto.
  destruct (eq_termvar x' x); subst.
  + apply (env_ctyp CT). intros xx AA. apply env_remove_cons.
  + apply CIH; eauto using Env.
* intros G E' m h C E A' CT CIH H HIH ENV VT.
  simpl. econstructor; eauto.

(* Handlers *)
* intros G x' m A' E E' C CT CIH ENV VT.
  simpl in CIH |- *. econstructor; auto.
  destruct (eq_termvar x' x); subst.
  + apply (env_ctyp CT). intros xx AA. apply env_remove_cons.
  + apply CIH; eauto using Env.
* intros G h op p k m A1 E A' B' E' C B H HIH CT CIH ENV VT.
  simpl in CIH |- *. econstructor; auto.
  destruct (eq_termvar p x); subst.
  + apply (env_ctyp CT). apply env_extend. intros xx AA. apply env_remove_cons.
  + destruct (eq_termvar k x); subst.
    - apply (env_ctyp CT). intros xx AA. apply env_remove_cons2.
    - apply CIH; eauto using Env.

Qed.


