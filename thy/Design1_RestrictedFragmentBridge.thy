theory Design1_RestrictedFragmentBridge
  imports Main
begin

section \<open>Design 1 restricted fragment bridge\<close>

record ('task,'payload) design_fragment_bridge =
  design_support :: "'task set"
  design_payload :: "'task \<Rightarrow> 'payload option"

definition design_obstruction_free_fragment :: "'task set \<Rightarrow> bool" where
  "design_obstruction_free_fragment Tasks \<longleftrightarrow> True"

definition design_fragment_admissible ::
  "('task,'payload) design_fragment_bridge \<Rightarrow> 'task set \<Rightarrow> bool"
where
  "design_fragment_admissible B Tasks \<longleftrightarrow> Tasks \<subseteq> design_support B"

definition design_exported_tasks ::
  "('task,'payload) design_fragment_bridge \<Rightarrow> 'task set"
where
  "design_exported_tasks B =
     {task \<in> design_support B. design_payload B task \<noteq> None}"

lemma design_support_is_admissible:
  "design_fragment_admissible B (design_support B)"
  unfolding design_fragment_admissible_def by simp

lemma design_fragment_admissible_subset:
  assumes "design_fragment_admissible B Tasks"
  shows "Tasks \<subseteq> design_support B"
  using assms unfolding design_fragment_admissible_def by simp

lemma design_exported_tasks_subset_support:
  "design_exported_tasks B \<subseteq> design_support B"
  unfolding design_exported_tasks_def by blast

end
