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
ind_appctx_C_m :: "C => m => m => bool"
where
"ind_appctx_C_m (C_Let x m) m5 ((m_Let x m5 m))"
| "ind_appctx_C_m (C_App v) m5 ((m_App m5 v))"
| "ind_appctx_C_m C_ProjL m5 ((m_ProjL m5))"
| "ind_appctx_C_m C_ProjR m5 ((m_ProjR m5))"
| "ind_appctx_C_m (C_Handle h) m5 ((m_Handle m5 h))"

lemma altC: "ind_appctx_C_m C m m' \<Longrightarrow> m' = appctx_C_m C m"
apply (induct rule: ind_appctx_C_m.induct)
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
  hence "reduce (appctx_C_m (C_App v) m) (appctx_C_m (C_App v) m')" apply (rule frameI) done
  thus "reduce (m_App m v) (m_App m' v)" by simp
qed

lemma runStateComp: "reduces1 (outer (runState comp)) expectedResult"
  apply (simp add: reduces1_def outer_def runState_def comp_def)
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule frameApp)
    apply (rule handleOpI)
      apply simp
      apply (rule hFor2I)  apply (rule hFor1I)

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
      apply (rule hFor1I)

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
      apply (rule hFor2I)  apply (rule hFor1I)

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
      apply (rule hFor1I)

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
      apply (rule hFor2I)  apply (rule hFor1I)

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
      apply (rule hReturns2I)  apply (rule hReturns2I) apply (rule hReturns1I)

  apply simp
  apply (rule rtranclp_trans)
    apply (rule r_into_rtranclp)
    apply (rule betaAppI)

  apply (simp add: expectedResult_def)
done

lemma altFrameI: "\<lbrakk>reduce (m) (m')\<rbrakk> \<Longrightarrow>
  ind_appctx_C_m  C   m m1  \<Longrightarrow>
  ind_appctx_C_m  C   m' m2 \<Longrightarrow>
  reduce m1 m2"
proof -
  (* TODO: I should be able to name these above? *)
  assume 1: "reduce (m) (m')"
  assume 2: "ind_appctx_C_m  C m m1"
  assume 3: "ind_appctx_C_m  C   m' m2"
  from 2 have 4: "m1 = appctx_C_m C m" by (rule altC)
  from 3 have 5: "m2 = appctx_C_m C m'" by (rule altC)
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

lemmas [code_pred_intro] =
  betatimesI betapluslI betaplusrI betaUI betaFI betaAppI betaAmpLI betaAmpRI
  handleFI handleOpI altFrameI altHoistopI

code_pred hreturns .
code_pred hfor .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) reduce
  apply (induct rule: reduce.cases)
  apply (metis)+
  apply (metis H.exhaust appctx_H_m.simps ind_appctx_H_m.intros)
  apply (metis)+
  apply (metis C.exhaust appctx_C_m.simps ind_appctx_C_m.intros)
done

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



