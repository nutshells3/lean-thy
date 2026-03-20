theory Step11_DecisionFocusedCertificationTheorem
  imports Step10_VarianceAdaptiveBoundTheorem
begin

section \<open>5E decision-focused certification theorem\<close>

datatype decision = Accept | Reject | Defer

record ('a, 'e) decision_problem =
  actions :: "'a set"
  evidence :: "'e set"
  utility :: "'a \<Rightarrow> 'e \<Rightarrow> real"
  cost :: "'a \<Rightarrow> 'e \<Rightarrow> real"

definition optimal_action :: "('a, 'e) decision_problem \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> bool" where
  "optimal_action P e a = (a \<in> actions P \<and>
     (\<forall>a' \<in> actions P. utility P a e - cost P a e \<ge> utility P a' e - cost P a' e))"

definition decision_gap :: "('a, 'e) decision_problem \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
  "decision_gap P e a a' = (utility P a e - cost P a e) - (utility P a' e - cost P a' e)"

lemma optimal_action_gap:
  assumes "optimal_action P e a"
    and "a' \<in> actions P"
  shows "decision_gap P e a a' \<ge> 0"
  using assms unfolding optimal_action_def decision_gap_def by auto

definition decision_certificate ::
  "('a, 'e) decision_problem \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> bool"
where
  "decision_certificate P e a certify delta \<longleftrightarrow>
     a \<in> actions P \<and>
     certify a \<and>
     (\<forall>a' \<in> actions P. decision_gap P e a a' \<ge> - delta)"

theorem decision_certificate_near_optimal:
  assumes "decision_certificate P e a certify delta"
    and "a' \<in> actions P"
  shows "decision_gap P e a a' \<ge> - delta"
  using assms unfolding decision_certificate_def by auto

end
