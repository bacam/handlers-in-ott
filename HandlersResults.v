Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Handlers.
Require Import HandlersEx.
Open Scope string_scope.


Example runStateComp : reds (outer (runState computation)) expectedResult.
eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply handleOp.
    tauto.
    apply hFor2. discriminate. apply hFor1.

simpl. eapply r_step.
  eapply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply frame with (CC:=CC_App _).
  apply betaU.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply handleOp.
    tauto.
    apply hFor1.

simpl. eapply r_step.
  apply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply frame with (CC:=CC_App _).
  apply betaU.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply handleOp.
    tauto.
    apply hFor2. discriminate. apply hFor1.

simpl. eapply r_step.
  apply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply frame with (CC:=CC_App _).
  apply betaU.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply handleOp.
    tauto.
    apply hFor1.

simpl. eapply r_step.
  apply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply frame with (CC:=CC_App _).
  apply betaU.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply handleOp.
    tauto.
    apply hFor2. discriminate. apply hFor1.

simpl. eapply r_step.
  apply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply frame with (CC:=CC_App _).
  apply betaU.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply betaApp.

simpl. eapply r_step.
  eapply frame with (CC:=CC_App _).
  eapply handleF.
    apply hReturns2. apply hReturns2. apply hReturns1.

simpl. eapply r_step.
  apply betaApp.

simpl. apply r_zero.
Qed.

