theory Design2_JudgeStackInstantiation
  imports Design1_RestrictedFragmentBridge
begin

section \<open>Design 2 judge-stack instantiation\<close>

record ('task,'payload) design_judge_stack =
  design_bridge :: "('task,'payload) design_fragment_bridge"
  design_fast_abstain_prob :: "'task \<Rightarrow> real"
  design_effective_accept_prob :: "'task \<Rightarrow> real"
  design_audit_radius :: real
  design_operational_lower_bound :: "'task \<Rightarrow> real"

definition design_judge_stack_wf ::
  "('task,'payload) design_judge_stack \<Rightarrow> bool"
where
  "design_judge_stack_wf J \<longleftrightarrow>
     0 \<le> design_audit_radius J \<and>
     (\<forall>task. 0 \<le> design_fast_abstain_prob J task) \<and>
     (\<forall>task. design_fast_abstain_prob J task \<le> 1) \<and>
     (\<forall>task. 0 \<le> design_effective_accept_prob J task) \<and>
     (\<forall>task. design_effective_accept_prob J task \<le> 1) \<and>
     (\<forall>task. design_operational_lower_bound J task \<le>
        design_effective_accept_prob J task)"

lemma design_operational_lower_bound_sound:
  assumes "design_judge_stack_wf J"
  shows "design_operational_lower_bound J task \<le> design_effective_accept_prob J task"
  using assms unfolding design_judge_stack_wf_def by simp

lemma design_effective_accept_prob_nonneg:
  assumes "design_judge_stack_wf J"
  shows "0 \<le> design_effective_accept_prob J task"
  using assms unfolding design_judge_stack_wf_def by simp

lemma design_effective_accept_prob_le1:
  assumes "design_judge_stack_wf J"
  shows "design_effective_accept_prob J task \<le> 1"
  using assms unfolding design_judge_stack_wf_def by simp

end
