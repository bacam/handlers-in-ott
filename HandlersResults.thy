theory HandlersResults
imports Main "~~/src/HOL/Library/Transitive_Closure_Table" Handlers HandlersEx
begin

inductive
ind_appctx_H_m :: "H => m => m => bool"
where
"ind_appctx_H_m (H_Let x m) m5 ((m_Let x m5 m))"
| "ind_appctx_H_m (H_App v) m5 ((m_App m5 v))"
| "ind_appctx_H_m H_ProjL m5 ((m_ProjL m5))"
| "ind_appctx_H_m H_ProjR m5 ((m_ProjR m5))"

lemma altH: "ind_appctx_H_m H m m' \<Longrightarrow> m' = appctx_H_m H m"
apply (induct rule: ind_appctx_H_m.induct)
apply simp_all
done

inductive
ind_appctx_CC_m :: "CC => m => m => bool"
where
"ind_appctx_CC_m (CC_Let x m) m5 ((m_Let x m5 m))"
| "ind_appctx_CC_m (CC_App v) m5 ((m_App m5 v))"
| "ind_appctx_CC_m CC_ProjL m5 ((m_ProjL m5))"
| "ind_appctx_CC_m CC_ProjR m5 ((m_ProjR m5))"
| "ind_appctx_CC_m (CC_Handle h) m5 ((m_Handle m5 h))"

lemma altC: "ind_appctx_CC_m CC m m' \<Longrightarrow> m' = appctx_CC_m CC m"
apply (induct rule: ind_appctx_CC_m.induct)
apply simp_all
done

definition reduces1 :: "m \<Rightarrow> m \<Rightarrow> bool" where "reduces1 = reduce^**"

lemma "reduces1 (m_Force (v_Thunk m)) m"
  apply (simp add: reduces1_def)
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaUI)

  apply (rule rtranclp.rtrancl_refl)
done

lemma frameApp: "reduce m m' \<Longrightarrow> reduce (m_App m v) (m_App m' v)"
proof -
  assume "reduce m m'"
  hence "reduce (appctx_CC_m (CC_App v) m) (appctx_CC_m (CC_App v) m')" apply (rule frameI) done
  thus "reduce (m_App m v) (m_App m' v)" by simp
qed

lemma runStateComp: "reduces1 (outer (runState comp)) expectedResult"
  apply (simp add: reduces1_def outer_def runState_def comp_def)
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleOpI)
      apply simp
      apply (rule_tac i="1" in hForI) apply simp apply (rule hForAuxI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule frameApp)
    apply (rule betaUI)

  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleOpI)
      apply simp
      apply (rule_tac i="2" in hForI) apply simp apply (rule hForAuxI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule frameApp)
    apply (rule betaUI)

  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleOpI)
      apply simp
      apply (rule_tac i="1" in hForI) apply simp apply (rule hForAuxI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule frameApp)
    apply (rule betaUI)

  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleOpI)
      apply simp
      apply (rule_tac i="2" in hForI) apply simp apply (rule hForAuxI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule frameApp)
    apply (rule betaUI)

  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleOpI)
      apply simp
      apply (rule_tac i="1" in hForI) apply simp apply (rule hForAuxI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule frameApp)
    apply (rule betaUI)

  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule betaAppI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleFI)
      apply (rule hReturnsI)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply (simp add: expectedResult_def)
done

lemma altFrameI: "\<lbrakk>reduce (m) (m')\<rbrakk> \<Longrightarrow>
  ind_appctx_CC_m CC m m1  \<Longrightarrow>
  ind_appctx_CC_m CC m' m2 \<Longrightarrow>
  reduce m1 m2"
proof -
  (* TODO: I should be able to name these above? *)
  assume 1: "reduce (m) (m')"
  assume 2: "ind_appctx_CC_m CC m m1"
  assume 3: "ind_appctx_CC_m CC m' m2"
  from 2 have 4: "m1 = appctx_CC_m CC m" by (rule altC)
  from 3 have 5: "m2 = appctx_CC_m CC m'" by (rule altC)
  from 1 4 5 frameI show ?thesis by simp
qed

lemma altHoistopI: "\<lbrakk> \<not> (x : set (fv_H  H )) \<rbrakk> \<Longrightarrow>
  ind_appctx_H_m  H (m_Op oper v x m) m1  \<Longrightarrow>
  ind_appctx_H_m  H m m2 \<Longrightarrow>
reduce m1 (m_Op oper v x m2)"
proof -
  assume 1: "\<not> (x : set (fv_H  H ))"
  assume 2: "ind_appctx_H_m  H (m_Op oper v x m) m1"
  assume 3: "ind_appctx_H_m  H m m2"
  from 2 have 4: "m1 = appctx_H_m H (m_Op oper v x m)" by (rule altH)
  from 3 have 5: "m2 = appctx_H_m H m" by (rule altH)
  from 1 4 5 hoistopI show ?thesis by simp
qed

(* Attempting to use hs!i = h or h \<in> set hs seems to get me into trouble with code_pred, but
   this indirect approach seems to work. *)
definition hinhs :: "haux \<Rightarrow> haux list \<Rightarrow> bool" where "hinhs h hs = (h : set hs)"

lemma altListII [code_pred_intro]:
  "hinhs h (h#t)"
  "hinhs x t \<Longrightarrow> hinhs x (h#t)"
 by (auto simp add: hinhs_def)

code_pred [show_modes] hinhs
unfolding hinhs_def
by (metis all_not_in_conv in_set_remove1 list.exhaust remove1.simps(2) set_empty)

lemma altHForI:
  assumes 1: "hinhs h hs"
  assumes 2: "hauxfor h oper p k m"
  shows "hfor (h_Handlers x m' hs) oper p k m"
proof -
  from 1 obtain i where "hs ! i = h" by (auto simp add: in_set_conv_nth hinhs_def)
  from this 2 have "hauxfor (hs ! i) oper p k m" by simp
  hence "hauxfor (hs ! (Suc i - 1)) oper p k m" by simp
  thus "hfor (h_Handlers x m' hs) oper p k m" by (metis hForI)
qed


lemmas [code_pred_intro] =
  betatimesI betapluslI betaplusrI betaUI betaFI betaAppI betaAmpLI betaAmpRI
  handleFI handleOpI altFrameI altHoistopI altHForI

lemma altHauxfor:
  "hauxfor (hs!i) oper p k m \<Longrightarrow> \<exists>h. h : set hs \<and> hauxfor h oper p k m"
proof
  assume "hauxfor (hs!i) oper p k m"
  hence "hs!i \<in> set hs"
  proof
    show ?thesis oops

(* Broken!  We can produce the code, but we can't do the completeness proofs unless we have some
   magic way to show that handler lookups hs!i are defined. *)

code_pred hreturns .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) hauxfor .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) hfor
  apply (induct rule: hfor.cases)
  apply (simp add: hinhs_def)
  oops

code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) reduce sorry(*
  apply (induct rule: reduce.cases)
  apply (metis)+
  apply (metis H.exhaust appctx_H_m.simps ind_appctx_H_m.intros)
  apply (metis)+
  apply (metis CC.exhaust appctx_CC_m.simps ind_appctx_CC_m.intros)
done*)

export_code reduce_i_o in SML file -

value "Predicate.the (reduce_i_o (outer (runState comp)))"
values "{m. reduce (outer (runState comp)) m}"

inductive reduces :: "m \<Rightarrow> m \<Rightarrow> bool" where
  "\<not>(\<exists>m'. reduce m m') \<Longrightarrow> reduces m m"
| "reduce m m' \<Longrightarrow> reduces m' m'' \<Longrightarrow> reduces m m''"

code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) [inductify] reduces .

values "{m. reduce (m_Force (v_Thunk (m_Force v_Unit))) m}"
values "{m. reduces (m_Force (v_Thunk (m_Force v_Unit))) m}"
values "{m. reduce^** (m_Force (v_Thunk (m_Force v_Unit))) m}"

export_code reduces_i_o outer runState comp Predicate.the in SML file -

value "Predicate.the (reduces_i_o (outer (runState comp)))"

values "{m. reduce^** (outer (runState comp)) m}"

end



