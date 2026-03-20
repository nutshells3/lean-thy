theory Design3_OperationalStoppingPolicy
  imports Design2_JudgeStackInstantiation
begin

section \<open>Design 3 operational stopping policy\<close>

record design_conf_seq =
  design_cs_lower :: "nat \<Rightarrow> real"
  design_cs_upper :: "nat \<Rightarrow> real"

datatype design_stopping_decision =
    DesignContinueSampling
  | DesignStopBelowThreshold
  | DesignStopAboveThreshold

definition design_cs_covers_at ::
  "design_conf_seq \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool"
where
  "design_cs_covers_at cs theta T \<longleftrightarrow>
     design_cs_lower cs T \<le> theta \<and> theta \<le> design_cs_upper cs T"

definition design_stopping_policy ::
  "design_conf_seq \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> design_stopping_decision"
where
  "design_stopping_policy cs eta_min eta_max T =
     (if design_cs_upper cs T < eta_max then DesignStopBelowThreshold
      else if eta_min < design_cs_lower cs T then DesignStopAboveThreshold
      else DesignContinueSampling)"

theorem design_stopping_policy_below_sound:
  assumes cover: "design_cs_covers_at cs theta T"
    and decide: "design_stopping_policy cs eta_min eta_max T = DesignStopBelowThreshold"
  shows "theta < eta_max"
proof -
  from cover have upper: "theta \<le> design_cs_upper cs T"
    unfolding design_cs_covers_at_def by simp
  from decide have "design_cs_upper cs T < eta_max"
    unfolding design_stopping_policy_def by (auto split: if_splits)
  with upper show ?thesis by linarith
qed

theorem design_stopping_policy_above_sound:
  assumes cover: "design_cs_covers_at cs theta T"
    and decide: "design_stopping_policy cs eta_min eta_max T = DesignStopAboveThreshold"
  shows "eta_min < theta"
proof -
  from cover have lower: "design_cs_lower cs T \<le> theta"
    unfolding design_cs_covers_at_def by simp
  from decide have "eta_min < design_cs_lower cs T"
    unfolding design_stopping_policy_def by (auto split: if_splits)
  with lower show ?thesis by linarith
qed

record ('task,'payload) design_operational_policy =
  design_stack :: "('task,'payload) design_judge_stack"
  design_seq :: design_conf_seq
  design_true_error :: real
  design_eta_min :: real
  design_eta_max :: real

definition design_operational_policy_wf ::
  "('task,'payload) design_operational_policy \<Rightarrow> bool"
where
  "design_operational_policy_wf P \<longleftrightarrow>
     design_judge_stack_wf (design_stack P) \<and>
     (\<forall>T. design_cs_covers_at (design_seq P) (design_true_error P) T)"

theorem design_operational_policy_certifies_below:
  assumes "design_operational_policy_wf P"
    and "design_stopping_policy (design_seq P) (design_eta_min P) (design_eta_max P) T =
         DesignStopBelowThreshold"
  shows "design_true_error P < design_eta_max P"
  using assms
  unfolding design_operational_policy_wf_def
  by (blast intro: design_stopping_policy_below_sound)

end
