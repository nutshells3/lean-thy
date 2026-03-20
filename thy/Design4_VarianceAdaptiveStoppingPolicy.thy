theory Design4_VarianceAdaptiveStoppingPolicy
  imports Design3_OperationalStoppingPolicy
begin

section \<open>Design 4 variance-adaptive stopping policy\<close>

definition design_first_exclusion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat" where
  "design_first_exclusion upper thr = (LEAST T. upper T < thr)"

lemma design_first_exclusion_attains:
  assumes "\<exists>T. upper T < thr"
  shows "upper (design_first_exclusion upper thr) < thr"
  unfolding design_first_exclusion_def using assms by (rule LeastI_ex)

lemma design_first_exclusion_le:
  assumes "upper T < thr"
  shows "design_first_exclusion upper thr \<le> T"
  unfolding design_first_exclusion_def using assms by (rule Least_le)

theorem design_first_exclusion_no_later:
  assumes dom: "\<And>T. adaptive_upper T \<le> baseline_upper T"
    and baseline_stops: "\<exists>T. baseline_upper T < thr"
  shows "design_first_exclusion adaptive_upper thr \<le>
         design_first_exclusion baseline_upper thr"
proof -
  let ?T = "design_first_exclusion baseline_upper thr"
  have base_at: "baseline_upper ?T < thr"
    by (rule design_first_exclusion_attains[OF baseline_stops])
  have "adaptive_upper ?T \<le> baseline_upper ?T"
    by (rule dom)
  with base_at have "adaptive_upper ?T < thr" by linarith
  then show ?thesis
    by (rule design_first_exclusion_le)
qed

record ('task,'payload) design_variance_policy =
  design_base_policy :: "('task,'payload) design_operational_policy"
  design_adaptive_upper :: "nat \<Rightarrow> real"
  design_baseline_upper :: "nat \<Rightarrow> real"

definition design_variance_policy_wf ::
  "('task,'payload) design_variance_policy \<Rightarrow> bool"
where
  "design_variance_policy_wf P \<longleftrightarrow>
     design_operational_policy_wf (design_base_policy P) \<and>
     (\<forall>T. design_adaptive_upper P T \<le> design_baseline_upper P T) \<and>
     (\<exists>T. design_baseline_upper P T <
        design_eta_max (design_base_policy P))"

theorem design_variance_policy_no_later:
  assumes "design_variance_policy_wf P"
  shows "design_first_exclusion (design_adaptive_upper P)
           (design_eta_max (design_base_policy P)) \<le>
         design_first_exclusion (design_baseline_upper P)
           (design_eta_max (design_base_policy P))"
  using assms unfolding design_variance_policy_wf_def
  by (blast intro: design_first_exclusion_no_later)

end
