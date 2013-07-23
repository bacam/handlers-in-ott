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

Corollary env_handle:
  forall {G h A' E E' C}, handle G h A' E E' C -> forall G', (forall x A, Env x A G -> Env x A G') -> handle G' h A' E E' C.
apply (proj2 (proj2 env_variant)).
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
  (forall G e m C, ctyp G e m C -> Env x A G -> vtyp env_Nil v A -> ctyp (remove x G) e (subst_compt v x m) C) /\
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
  + apply (env_ctyp CT). intros xx AA. apply env_remove_cons2.
  + destruct (eq_termvar x2 x); subst.
    - apply (env_ctyp CT). apply env_extend. intros xx AA. apply env_remove_cons.
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
* intros G x' m A' E' C CT CIH ENV VT.
  simpl in CIH |- *. econstructor; auto.
  destruct (eq_termvar x' x); subst.
  + apply (env_ctyp CT). intros xx AA. apply env_remove_cons.
  + apply CIH; eauto using Env.
* intros G h op p k m A1 E A' E' B C H HIH CT CIH ENV VT.
  simpl in CIH |- *. econstructor; auto.
  destruct (eq_termvar p x); subst.
  + apply (env_ctyp CT). intros xx AA. apply env_remove_cons2.
  + destruct (eq_termvar k x); subst.
    - apply (env_ctyp CT). apply env_extend. intros xx AA. apply env_remove_cons.
    - apply CIH; eauto using Env.

Qed.

Lemma comp_substitution1: forall v A x E m C,
  ctyp (env_Cons env_Nil x A) E m C ->
  vtyp env_Nil v A ->
  ctyp env_Nil E (subst_compt v x m) C.
intros. 
cut (env_Nil = (remove x (env_Cons env_Nil x A))).
intro EQ; rewrite EQ.
apply (proj1 (proj2 (substitution v A x))); eauto using Env.
simpl. rewrite eq_termvar_eq. reflexivity.
Qed.

Scheme value_ind := Induction for value Sort Prop
  with comp_ind := Induction for compt Sort Prop
  with handlers_ind := Induction for handlers Sort Prop.
Combined Scheme term_ind from value_ind, comp_ind, handlers_ind.

Lemma double_subst: forall v w x,
  (forall u, subst_value w x (subst_value v x u) = subst_value (subst_value w x v) x u) /\
  (forall m, subst_compt w x (subst_compt v x m) = subst_compt (subst_value w x v) x m) /\
  (forall h, subst_handlers w x (subst_handlers v x h) = subst_handlers (subst_value w x v) x h).
intros v w x. apply term_ind; simpl; eauto; try congruence.
* intros. destruct (eq_termvar x0 x); subst; simpl; auto. rewrite eq_termvar_neq; auto.
* intros.
   destruct (eq_termvar x1 x). congruence.
   destruct (eq_termvar x2 x); congruence.
* intros.
   destruct (eq_termvar x1 x); destruct (eq_termvar x2 x); congruence.
* intros. destruct (eq_termvar x0 x); congruence.
* intros. destruct (eq_termvar x0 x); congruence.
* intros. destruct (eq_termvar x0 x); congruence.
* intros. destruct (eq_termvar x0 x); congruence.
* intros. destruct (eq_termvar p x); destruct (eq_termvar k x); congruence.
Qed.

Lemma not_env_Cons: forall {x x' A' G},
  (forall A, ~ Env x A G) ->
  x <> x' ->
  (forall A, ~ Env x A (env_Cons G x' A')).
intros. intro ENV. inversion ENV; subst.
* congruence.
* apply (H A H7).
Qed.


Lemma fresh_subst: forall w x,
  (forall G v A, vtyp G v A -> (forall A', not (Env x A' G)) -> subst_value w x v = v) /\
  (forall G E m C, ctyp G E m C -> (forall A', not (Env x A' G)) -> subst_compt w x m = m) /\
  (forall G h A E E' C, handle G h A E E' C -> (forall A', not (Env x A' G)) -> subst_handlers w x h = h).
intros w x.
apply typ_comb_ind; simpl; intros;
repeat match goal with |- context [ eq_termvar ?x ?y ] => destruct (eq_termvar x y); subst end;
repeat match goal with H1 : _ -> subst_value _ _ _ = ?v1 |- _ => rewrite H1; auto end;
repeat match goal with H1 : _ -> subst_compt _ _ _ = ?m1 |- _ => rewrite H1; auto end;
repeat match goal with H1 : _ -> subst_handlers _ _ _ = ?h1 |- _ => rewrite H1; auto end;
try congruence;
auto using not_env_Cons.
* case (H0 _ H).
Qed.

Lemma closed_subst: forall {v A w x},
  vtyp env_Nil v A -> subst_value w x v = v.
intros. apply (proj1 (fresh_subst w x) env_Nil v A H).
intros A' ENV. inversion ENV.
Qed.

Lemma comp_substitution2: forall v A x w B y E m C,
  ctyp (env_Cons (env_Cons env_Nil y B) x A) E m C ->
  vtyp env_Nil v A ->
  vtyp env_Nil w B ->
  ctyp env_Nil E (subst_compt w y (subst_compt v x m)) C.
intros.
destruct (eq_termvar x y).
* subst. rewrite (proj1 (proj2 (double_subst v w y))).
  rewrite (closed_subst H0).
  eapply comp_substitution1; eauto.
  apply (env_ctyp H).
  clear. intros. inversion H; subst; eauto using Env.
  inversion H6; subst; eauto using Env.
  congruence.
* cut (env_Nil = (remove y (remove x (env_Cons (env_Cons env_Nil y B) x A)))).
  intro EQ; rewrite EQ.
  apply (proj1 (proj2 (substitution w B y))); eauto.
  apply (proj1 (proj2 (substitution v A x))); eauto using Env.
  simpl. rewrite eq_termvar_eq. eauto using Env.
  simpl. rewrite eq_termvar_eq. simpl. rewrite eq_termvar_eq. reflexivity.
Qed.

Require Import ott_list.
Require Import List.

Lemma not_In_list_minus :
  forall {l l' x}, List.In x (list_minus eq_termvar l l') -> List.In x l' -> False.
induction l.
* tauto.
* intros. simpl in H. destruct (list_mem eq_termvar a l') eqn:E.
  + apply (IHl _ _ H). assumption.
  + inversion H; subst.
    - absurd (In x l'); eauto using list_mem_false_implies_not_In.
    - apply (IHl l' x H1 H0).
Qed.

Lemma adjust_extended_env1: forall {x x1 A1 l G},
  (In x l -> exists A, Env x A (env_Cons G x1 A1)) ->
  In x (list_minus eq_termvar l (x1::nil)%list) -> exists A, Env x A G.
intros.
destruct (H (In_list_plus _ _ _ _ H0)) as [A ENV].
inversion ENV; subst.
* exfalso. apply (not_In_list_minus H0). auto with datatypes.
* exists A. assumption.
Qed.

Lemma adjust_extended_env2: forall {x x1 A1 x2 A2 l G},
  (In x l -> exists A, Env x A (env_Cons (env_Cons G x2 A1) x1 A2)) ->
  In x (list_minus eq_termvar l (x1::x2::nil)%list) -> exists A, Env x A G.
intros.
destruct (H (In_list_plus _ _ _ _ H0)) as [A ENV].
inversion ENV; subst.
* exfalso. apply (not_In_list_minus H0). auto with datatypes.
* inversion H7; subst.
  + exfalso. apply (not_In_list_minus H0). auto with datatypes.
  + exists A. assumption.
Qed.

Lemma fv_in_env:
  (forall G v A', vtyp G v A' -> forall x, List.In x (fv_value v) -> exists A, Env x A G) /\
  (forall G e m C, ctyp G e m C -> forall x, List.In x (fv_compt m) -> exists A, Env x A G) /\
  (forall G h A' E E' C, handle G h A' E E' C -> forall x, List.In x (fv_handlers h) -> exists A, Env x A G).
apply typ_comb_ind; eauto using adjust_extended_env1.
* intros; subst. simpl in H0. inversion H0. subst. eexists; eassumption. case H1.
* intros. simpl in H. case H.
* intros. simpl in H3. case (List.in_app_or _ _ _ H3); auto.
* intros. simpl in H3. case (List.in_app_or _ _ _ H3); eauto using adjust_extended_env2.
* intros. simpl in H5. case (List.in_app_or _ _ _ H5); auto.
  intro IN. case (List.in_app_or _ _ _ IN); eauto using adjust_extended_env1.
* intros. simpl in H3. case (List.in_app_or _ _ _ H3); eauto using adjust_extended_env1.
* intros. case (List.in_app_or _ _ _ H3); eauto using adjust_extended_env1.
* intros. case H.
* intros. case (List.in_app_or _ _ _ H3); eauto.
* intros. simpl in H4. case (List.in_app_or _ _ _ H4); eauto using adjust_extended_env1.
* intros. simpl in H3. case (List.in_app_or _ _ _ H3); eauto.
* intros. simpl in H3. case (List.in_app_or _ _ _ H3); eauto using adjust_extended_env2.
Qed.

Lemma no_fv_value_in_env_Nil: forall v A,
  vtyp env_Nil v A -> forall x, ~In x (fv_value v).
intros v A VT x IN.
destruct (proj1 fv_in_env _ _ _ VT _ IN) as [A' ENV].
inversion ENV.
Qed.

Lemma hreturns_exists:
  forall h, exists x m, hreturns h x m.
induction h; eauto using hreturns.
destruct IHh as [x [m' H]]. eauto using hreturns.
Qed.

Lemma hfor_exists: forall {G h A E E' C oper A' B},
  handle G h A E E' C ->
  eff oper A' B E ->
  exists p k m, hfor h oper p k m.
intros until B. induction 1; inversion 1; subst.
* exists p,k,m. constructor.
* destruct (IHhandle H10) as [p' [k' [m' HFOR]]]. exists p',k',m'. eauto using hfor.
Qed.

(* Note the extra case to deal with variable capture. *)

Inductive progress_result : compt -> Prop :=
| pr_canonical : forall m, canonical m -> progress_result m
| pr_step : forall m m', reduce m m' -> progress_result m
| pr_alpha : forall m, needs_alpha_conv m -> progress_result m.

Lemma progress:
  forall E m C, ctyp env_Nil E m C -> progress_result m.
intros E m C CTYP.
assert (env_Nil = env_Nil) by reflexivity. revert CTYP H.
generalize env_Nil at 1 2. induction 1; intro E1; subst; eauto using canonical, progress_result.
* inversion H; subst. inversion H0.
  eapply pr_step. constructor.
* inversion H; subst. inversion H0.
* inversion H; subst; [ inversion H0 | .. ]; eapply pr_step; constructor.
* inversion H; subst; [ inversion H0 | .. ].
  eapply pr_step; constructor.
* cut (progress_result m); auto. intro H.
  destruct H as [m CAN | m m'' R | m AN ].
  + inversion CAN; subst; inversion CTYP1; subst.
    - eapply pr_step; constructor.
    - case (List.in_dec eq_termvar x0 (fv_hoisting_frame (H_Let x m'))).
      intro BAD. apply pr_alpha. apply AC_hoistop with (H:=H_Let _ _). apply BAD.
      intro GOOD. eapply pr_step; apply hoistop with (H:=H_Let _ _). apply GOOD.
  + eapply pr_step. eapply frame with (CC:=CC_Let _ _). apply R.
  + apply pr_alpha. apply AC_frame with (CC:=CC_Let _ _). assumption.
* cut (progress_result m); auto. intro H'.
  destruct H' as [m CAN | m m'' R | m AN ].
  + inversion CAN; subst; inversion CTYP; subst.
    - eapply pr_step; econstructor.
    - eapply pr_step; apply hoistop with (H:=H_App _). apply (no_fv_value_in_env_Nil _ _ H x).
  + eapply pr_step; eapply frame with (CC:=CC_App _). eassumption.
  + apply pr_alpha. apply AC_frame with (CC:=CC_App _). assumption.
* cut (progress_result m); auto. intro H'.
  destruct H' as [m CAN | m m'' R | m AN ].
  + inversion CAN; subst; inversion CTYP; subst.
    - eapply pr_step; econstructor.
    - eapply pr_step; apply hoistop with (H:=H_ProjL). auto with datatypes.
  + eapply pr_step; eapply frame with (CC:=CC_ProjL). eassumption.
  + apply pr_alpha. apply AC_frame with (CC:=CC_ProjL). assumption.
* cut (progress_result m); auto. intro H'.
  destruct H' as [m CAN | m m'' R | m AN ].
  + inversion CAN; subst; inversion CTYP; subst.
    - eapply pr_step; econstructor.
    - eapply pr_step; apply hoistop with (H:=H_ProjR). auto with datatypes.
  + eapply pr_step; eapply frame with (CC:=CC_ProjR). eassumption.
  + apply pr_alpha. apply AC_frame with (CC:=CC_ProjR). assumption.
* cut (progress_result m); auto. intro H'.
  destruct H' as [m CAN | m m'' R | m AN ].
  + inversion CAN; subst; inversion CTYP; subst.
    - destruct (hreturns_exists h) as [x [m HR]]. eapply pr_step; econstructor. apply HR.
    - destruct (List.in_dec eq_termvar x (fv_handlers h)).
      apply pr_alpha. constructor. apply i.
      destruct (hfor_exists H H7) as [p [k [m HF]]]. eapply pr_step; econstructor; eauto.
  + eapply pr_step; eapply frame with (CC:=CC_Handle _). eassumption.
  + apply pr_alpha. apply AC_frame with (CC:=CC_Handle _). assumption.
Qed.

Lemma hreturns_ctyp: forall {G h A E E' C x m},
  handle G h A E E' C ->
  hreturns h x m ->
  ctyp (env_Cons G x A) E' m C.
intros. induction H.
* inversion H0; subst; assumption.
* inversion H0; subst; auto.
Qed.

Lemma hfor_ctyp: forall {G h A E E' C A' B oper p k m},
  handle G h A E E' C ->
  eff oper A' B E ->
  hfor h oper p k m ->
  ctyp (env_Cons (env_Cons G k (vt_Thunk E' (ct_Function B C))) p A') E' m C.
intros until m. induction 1.
* inversion 1.
* inversion 1; subst.
  + inversion 1; subst.
      - assumption.
      - congruence.
  + inversion 1; subst.
      - congruence.
      - auto.
Qed.

(* Again, stick to closed values *)

Lemma preservation:
  forall E m C,
    ctyp env_Nil E m C ->
  forall m',
    reduce m m' ->
    ctyp env_Nil E m' C.
intros E m C CTYP.
assert (env_Nil = env_Nil) by reflexivity. revert CTYP H.
generalize env_Nil at 1 2.
induction 1; intro E1; subst; intros m'' RED; inversion RED; subst;
match goal with H : appctx_hoisting_frame_compt ?HF _ = _ |- _ => destruct HF; simpl in H; simplify_eq H; intros; subst | _ => idtac end;
match goal with H : appctx_compt_frame_compt ?CC _ = _ |- _ => destruct CC; simpl in H; simplify_eq H; intros; subst | _ => idtac end;
simpl;
try solve [eauto using ctyp | inversion H; subst; eauto using comp_substitution1, comp_substitution2].
* inversion CTYP1; subst; eapply comp_substitution1; eauto.
* inversion CTYP1; subst.
   econstructor; eauto.
   econstructor; eauto.
   eapply env_ctyp; eauto.
   clear. intros. inversion H; subst; eauto using Env. inversion H6.
* inversion CTYP; subst. eapply comp_substitution1; eauto.
* inversion CTYP; subst; econstructor; eauto. econstructor; eauto.
   apply (env_vtyp H).
   clear; intros; inversion H; subst; eauto using Env.
* inversion CTYP; subst; eauto.
* inversion CTYP; subst; econstructor; eauto. econstructor; eauto.
* inversion CTYP; subst; eauto.
* inversion CTYP; subst; econstructor; eauto. econstructor; eauto.
* inversion CTYP; subst. eapply comp_substitution1; eauto.
  eauto using hreturns_ctyp.
* inversion CTYP; subst. eapply comp_substitution2; eauto.
  + eapply hfor_ctyp; eauto.
  + constructor; auto. constructor; auto. econstructor; eauto.
      eapply env_handle; eauto.
      clear; intros; inversion H.
Qed.

