theory Design5_FalsificationFirstPolicy
  imports Design4_VarianceAdaptiveStoppingPolicy
begin

section \<open>Design 5 falsification-first policy\<close>

datatype design_decision = DesignAccept | DesignReject | DesignDefer

record ('a,'e) design_decision_problem =
  design_actions :: "'a set"
  design_utility :: "'a \<Rightarrow> 'e \<Rightarrow> real"
  design_cost :: "'a \<Rightarrow> 'e \<Rightarrow> real"

record ('a,'e) design_staged_policy =
  design_refute_cost :: real
  design_confirm_cost :: real
  design_refute_test :: "'a \<Rightarrow> 'e \<Rightarrow> bool"
  design_confirm_test :: "'a \<Rightarrow> 'e \<Rightarrow> bool"

definition design_survivors ::
  "('a,'e) design_staged_policy \<Rightarrow> 'a set \<Rightarrow> 'e \<Rightarrow> 'a set"
where
  "design_survivors pol candidates e =
     {a \<in> candidates. design_refute_test pol a e}"

definition design_certified ::
  "('a,'e) design_staged_policy \<Rightarrow> 'a set \<Rightarrow> 'e \<Rightarrow> 'a set"
where
  "design_certified pol candidates e =
     {a \<in> design_survivors pol candidates e. design_confirm_test pol a e}"

definition design_gap ::
  "('a,'e) design_decision_problem \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
where
  "design_gap P e a a' =
     (design_utility P a e - design_cost P a e) -
     (design_utility P a' e - design_cost P a' e)"

definition design_certificate ::
  "('a,'e) design_decision_problem \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> bool"
where
  "design_certificate P e a certify delta \<longleftrightarrow>
     a \<in> design_actions P \<and>
     certify a \<and>
     (\<forall>a' \<in> design_actions P. - delta \<le> design_gap P e a a')"

definition design_refutation_sound ::
  "('a,'e) design_staged_policy \<Rightarrow> ('a,'e) design_decision_problem \<Rightarrow> 'e \<Rightarrow> bool"
where
  "design_refutation_sound pol P e \<longleftrightarrow>
     (\<forall>a \<in> design_actions P. design_refute_test pol a e)"

definition design_confirmation_sound ::
  "('a,'e) design_staged_policy \<Rightarrow> ('a,'e) design_decision_problem \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> bool"
where
  "design_confirmation_sound pol P e delta \<longleftrightarrow>
     (\<forall>a \<in> design_actions P. design_confirm_test pol a e \<longrightarrow>
        (\<forall>a' \<in> design_actions P. - delta \<le> design_gap P e a a'))"

definition design_staged_budget ::
  "('a,'e) design_staged_policy \<Rightarrow> 'a set \<Rightarrow> 'e \<Rightarrow> real"
where
  "design_staged_budget pol candidates e =
     real (card candidates) * design_refute_cost pol +
     real (card (design_survivors pol candidates e)) * design_confirm_cost pol"

lemma design_staged_budget_saving:
  assumes "finite candidates"
    and "design_confirm_cost pol > 0"
    and "design_refute_cost pol \<ge> 0"
    and "design_survivors pol candidates e \<subset> candidates"
  shows "design_staged_budget pol candidates e <
         real (card candidates) * design_confirm_cost pol +
         real (card candidates) * design_refute_cost pol"
proof -
  have "card (design_survivors pol candidates e) < card candidates"
    using assms(1,4) psubset_card_mono by auto
  then have "real (card (design_survivors pol candidates e)) < real (card candidates)"
    by simp
  then have "real (card (design_survivors pol candidates e)) * design_confirm_cost pol <
             real (card candidates) * design_confirm_cost pol"
    using assms(2) by (intro mult_strict_right_mono) auto
  then show ?thesis unfolding design_staged_budget_def by linarith
qed

theorem design_decision_focused_guarantee:
  assumes "a_star \<in> design_actions P"
    and "design_refutation_sound pol P e"
  shows "a_star \<in> design_survivors pol (design_actions P) e"
  using assms unfolding design_refutation_sound_def design_survivors_def by auto

theorem design_certified_near_optimal:
  assumes "design_confirmation_sound pol P e delta"
    and "a \<in> design_certified pol (design_actions P) e"
    and "a' \<in> design_actions P"
  shows "- delta \<le> design_gap P e a a'"
  using assms
  unfolding design_confirmation_sound_def design_certified_def design_survivors_def
  by auto

theorem design_staged_policy_instantiates_certificate:
  assumes "design_confirmation_sound pol P e delta"
    and "a \<in> design_certified pol (design_actions P) e"
  shows "design_certificate P e a
           (\<lambda>x. x \<in> design_certified pol (design_actions P) e) delta"
proof -
  have a_mem: "a \<in> design_actions P"
    using assms(2) unfolding design_certified_def design_survivors_def by auto
  have gaps: "\<forall>a' \<in> design_actions P. - delta \<le> design_gap P e a a'"
    using assms(1,2)
    unfolding design_confirmation_sound_def design_certified_def design_survivors_def
    by auto
  show ?thesis
    unfolding design_certificate_def using a_mem assms(2) gaps by auto
qed

theorem design_staged_certification_summary:
  assumes "finite (design_actions P)"
    and "a_star \<in> design_actions P"
    and "design_refutation_sound pol P e"
    and "design_confirmation_sound pol P e delta"
    and "design_confirm_cost pol > 0"
    and "design_refute_cost pol \<ge> 0"
    and "design_survivors pol (design_actions P) e \<subset> design_actions P"
  shows "a_star \<in> design_survivors pol (design_actions P) e \<and>
         (\<forall>a \<in> design_certified pol (design_actions P) e.
            design_certificate P e a
              (\<lambda>x. x \<in> design_certified pol (design_actions P) e) delta) \<and>
         design_staged_budget pol (design_actions P) e <
           real (card (design_actions P)) * design_confirm_cost pol +
           real (card (design_actions P)) * design_refute_cost pol"
proof (intro conjI ballI)
  show "a_star \<in> design_survivors pol (design_actions P) e"
    using assms(2,3) by (rule design_decision_focused_guarantee)
next
  fix a
  assume "a \<in> design_certified pol (design_actions P) e"
  then show "design_certificate P e a
               (\<lambda>x. x \<in> design_certified pol (design_actions P) e) delta"
    using assms(4) by (rule design_staged_policy_instantiates_certificate)
next
  show "design_staged_budget pol (design_actions P) e <
        real (card (design_actions P)) * design_confirm_cost pol +
        real (card (design_actions P)) * design_refute_cost pol"
    using assms(1,5,6,7) by (rule design_staged_budget_saving)
qed

end
