theory Step6_MainClaims
  imports Step5_NLTranslationBarrier
begin

theorem claim_1_substantive_outcome_separation:
  "((\<not> (\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H_monobird Wtw c \<Gamma> \<phi> \<and>
                      \<not> a_derives H_monobird Wtw c (\<Gamma> \<union> \<Delta>) \<phi>)) \<and>
    standard_monotone_target F_tweety Wtw \<and>
    task_restricted_translatable H_monobird F_tweety Wtw (agent_task_envelope H_monobird Wtw)) \<and>
   (defeasible_nl_agent H_tweety Wtw \<and>
    standard_monotone_target F_tweety Wtw \<and>
    \<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw))"
  by (rule substantive_axioms_separate_translation_outcomes)

corollary claim_1_same_target_opposite_outcomes:
  "task_restricted_translatable H_monobird F_tweety Wtw (agent_task_envelope H_monobird Wtw) \<and>
   \<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw)"
  using claim_1_substantive_outcome_separation by blast

theorem claim_2_prior_bound:
  assumes "finite (set_pmf D)"
    and "\<And>k. k \<in> set_pmf D \<Longrightarrow> utterance_admissible I k w n"
    and "pairwise_key_conflict_on I \<tau> w n (set_pmf D)"
  shows "key_conditioned_success_prob D I \<tau> T w n \<le> max_supported_key_mass D"
  by (rule pairwise_conflict_prior_bound[OF assms])

theorem claim_2_prior_tight:
  assumes "finite (set_pmf D)"
    and "set_pmf D \<noteq> {}"
    and "\<And>k. k \<in> set_pmf D \<Longrightarrow> utterance_admissible I k w n"
    and "pairwise_key_conflict_on I \<tau> w n (set_pmf D)"
    and "k0 \<in> set_pmf D"
    and "task_compatible_with_key I \<tau> k0 w n t0"
    and "pmf D k0 = max_supported_key_mass D"
    and "T n = t0"
  shows "key_conditioned_success_prob D I \<tau> T w n = max_supported_key_mass D"
proof (rule pairwise_conflict_prior_tight)
  show "finite (set_pmf D)" by (rule assms(1))
  show "\<And>k. k \<in> set_pmf D \<Longrightarrow> utterance_admissible I k w n" by (rule assms(3))
  show "pairwise_key_conflict_on I \<tau> w n (set_pmf D)" by (rule assms(4))
  show "k0 \<in> set_pmf D" by (rule assms(5))
  show "pmf D k0 = max_supported_key_mass D" by (rule assms(7))
  show "task_compatible_with_key I \<tau> k0 w n t0" by (rule assms(6))
  show "T n = t0" by (rule assms(8))
qed

theorem claim_2_uniform_bound:
  assumes "finite K" "K \<noteq> {}"
    and "\<And>k. k \<in> K \<Longrightarrow> utterance_admissible I k w n"
    and "pairwise_key_conflict_on I \<tau> w n K"
  shows "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
  by (rule pairwise_conflict_uniform_bound[OF assms])

theorem claim_2_uniform_tight:
  assumes "finite K" "K \<noteq> {}"
    and "\<And>k. k \<in> K \<Longrightarrow> utterance_admissible I k w n"
    and "pairwise_key_conflict_on I \<tau> w n K"
    and "k0 \<in> K"
    and "task_compatible_with_key I \<tau> k0 w n t0"
    and "T n = t0"
  shows "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n = 1 / card K"
proof (rule pairwise_conflict_uniform_tight)
  show "finite K" by (rule assms(1))
  show "K \<noteq> {}" by (rule assms(2))
  show "\<And>k. k \<in> K \<Longrightarrow> utterance_admissible I k w n" by (rule assms(3))
  show "pairwise_key_conflict_on I \<tau> w n K" by (rule assms(4))
  show "k0 \<in> K" by (rule assms(5))
  show "task_compatible_with_key I \<tau> k0 w n t0" by (rule assms(6))
  show "T n = t0" by (rule assms(7))
qed

theorem claim_2_key_revealed_recovery:
  assumes "\<And>k n. utterance_admissible I k w n \<Longrightarrow> \<exists>t. task_compatible_with_key I \<tau> k w n t"
  shows "\<exists>T. interactive_task_translator I \<tau> T w"
  by (rule key_revealed_interaction_recovers_translation[OF assms])

theorem claim_2_substantive_witness:
  "\<not> (\<exists>T. single_shot_task_translator I_amb \<tau>_toy T ()) \<and>
   key_conditioned_success_prob (pmf_of_set {KLeft, KRight}) I_amb \<tau>_toy T () NAmb \<le> 1 / 2 \<and>
   (\<exists>T. key_revealed_task_translator_on I_amb \<tau>_toy T () NAmb {KLeft, KRight})"
  using I_amb_substantive_no_single_shot_translation
        I_amb_substantive_binary_success_le_half
        I_amb_substantive_key_revealed_translation
  by blast

theorem claim_2_main_line_core:
  assumes B: "nl_translation_barrier H w F I \<tau> n K"
  shows "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
         key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
proof -
  interpret B: nl_translation_barrier H w F I \<tau> n K
    by (rule B)
  show ?thesis
    by (rule B.core_translation_barrier)
qed

theorem claim_2_main_line_strong_core:
  assumes B: "genuinely_ambiguous_nl_translation_barrier H w F I \<tau> n K"
  shows "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
         \<not> (\<exists>T. single_shot_task_translator I \<tau> T w) \<and>
         key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1"
proof -
  interpret B: genuinely_ambiguous_nl_translation_barrier H w F I \<tau> n K
    by (rule B)
  show ?thesis
    by (rule B.strong_core_translation_barrier)
qed

end
