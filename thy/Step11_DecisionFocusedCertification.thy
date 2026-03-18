theory Step11_DecisionFocusedCertification
  imports Step10_VarianceAdaptiveBounds
begin

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

record ('a, 'e) staged_policy =
  refute_cost :: real
  confirm_cost :: real
  refute_test :: "'a \<Rightarrow> 'e \<Rightarrow> bool"
  confirm_test :: "'a \<Rightarrow> 'e \<Rightarrow> bool"

definition survivors :: "('a, 'e) staged_policy \<Rightarrow> 'a set \<Rightarrow> 'e \<Rightarrow> 'a set" where
  "survivors pol candidates e = {a \<in> candidates. refute_test pol a e}"

definition certified :: "('a, 'e) staged_policy \<Rightarrow> 'a set \<Rightarrow> 'e \<Rightarrow> 'a set" where
  "certified pol candidates e = {a \<in> survivors pol candidates e. confirm_test pol a e}"

definition staged_budget :: "('a, 'e) staged_policy \<Rightarrow> 'a set \<Rightarrow> 'e \<Rightarrow> real" where
  "staged_budget pol candidates e =
     real (card candidates) * refute_cost pol +
     real (card (survivors pol candidates e)) * confirm_cost pol"

lemma staged_budget_saving:
  assumes "finite candidates"
    and "confirm_cost pol > 0"
    and "refute_cost pol \<ge> 0"
    and "survivors pol candidates e \<subset> candidates"
  shows "staged_budget pol candidates e <
         real (card candidates) * confirm_cost pol + real (card candidates) * refute_cost pol"
proof -
  have surv_sub: "survivors pol candidates e \<subseteq> candidates"
    using assms(4) by auto
  have "card (survivors pol candidates e) < card candidates"
    using assms(1,4) psubset_card_mono by auto
  then have "real (card (survivors pol candidates e)) < real (card candidates)"
    by simp
  then have "real (card (survivors pol candidates e)) * confirm_cost pol <
             real (card candidates) * confirm_cost pol"
    using assms(2) by (intro mult_strict_right_mono) auto
  then show ?thesis
    unfolding staged_budget_def by linarith
qed

definition refutation_sound :: "('a, 'e) staged_policy \<Rightarrow> ('a, 'e) decision_problem \<Rightarrow> 'e \<Rightarrow> bool" where
  "refutation_sound pol P e =
    (\<forall>a. optimal_action P e a \<longrightarrow> a \<in> actions P \<longrightarrow> refute_test pol a e)"

definition confirmation_sound :: "('a, 'e) staged_policy \<Rightarrow> ('a, 'e) decision_problem \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> bool" where
  "confirmation_sound pol P e delta =
    (\<forall>a \<in> actions P. confirm_test pol a e \<longrightarrow>
       (\<forall>a' \<in> actions P. decision_gap P e a a' \<ge> - delta))"

theorem decision_focused_guarantee:
  assumes "optimal_action P e a_star"
    and "a_star \<in> actions P"
    and "refutation_sound pol P e"
  shows "a_star \<in> survivors pol (actions P) e"
  using assms unfolding refutation_sound_def survivors_def optimal_action_def
  by auto

theorem certified_near_optimal:
  assumes "confirmation_sound pol P e delta"
    and "a \<in> certified pol (actions P) e"
    and "a' \<in> actions P"
  shows "decision_gap P e a a' \<ge> - delta"
  using assms unfolding confirmation_sound_def certified_def survivors_def
  by auto

theorem staged_certification_summary:
  assumes "finite (actions P)"
    and "optimal_action P e a_star"
    and "a_star \<in> actions P"
    and "refutation_sound pol P e"
    and "confirmation_sound pol P e delta"
    and "confirm_cost pol > 0"
    and "refute_cost pol \<ge> 0"
    and "survivors pol (actions P) e \<subset> actions P"
  shows "a_star \<in> survivors pol (actions P) e
       \<and> (\<forall>a \<in> certified pol (actions P) e.
            \<forall>a' \<in> actions P. decision_gap P e a a' \<ge> - delta)
       \<and> staged_budget pol (actions P) e <
           real (card (actions P)) * confirm_cost pol +
           real (card (actions P)) * refute_cost pol"
proof (intro conjI ballI)
  show "a_star \<in> survivors pol (actions P) e"
    using assms(2,3,4) by (rule decision_focused_guarantee)
next
  fix a a'
  assume "a \<in> certified pol (actions P) e" "a' \<in> actions P"
  then show "- delta \<le> decision_gap P e a a'"
    using assms(5) by (intro certified_near_optimal)
next
  show "staged_budget pol (actions P) e <
        real (card (actions P)) * confirm_cost pol +
        real (card (actions P)) * refute_cost pol"
    using assms(1,6,7,8) by (rule staged_budget_saving)
qed

end
