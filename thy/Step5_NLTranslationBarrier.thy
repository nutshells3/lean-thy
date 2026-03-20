theory Step5_NLTranslationBarrier
  imports Step4_AmbiguousSourceAxiomatics
begin

section \<open>Unified natural-language translation barrier\<close>

text \<open>
  Combined barrier:

    \<^item> exact envelope translation fails under defeasible source-side
      derivability and monotone target derivability;
    \<^item> single-shot translation on an ambiguous utterance is bounded by
      @{term "1 / card K"} under a uniform key prior;
    \<^item> if @{term "2 \<le> card K"}, then single-shot translation is
      impossible and the success ceiling is strictly below @{term 1}.
\<close>

locale nl_translation_barrier =
  defeasible_nl_to_monotone_target H w F +
  ambiguous_nl_source I \<tau> w n K
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and I :: "('k,'w,'n,'c,'u) keyed_reg"
    and \<tau> :: "('u,'f) trans"
    and n :: 'n
    and K :: "'k set"
begin

theorem envelope_translation_impossible:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w)"
  using no_exact_envelope_translation .

theorem single_shot_success_uniform_bound:
  "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
  using single_shot_uniform_success_bound .

theorem clarification_recovers_relative_translation:
  "\<exists>T. key_revealed_task_translator_on I \<tau> T w n K"
  using key_revealed_translation_on .

theorem core_translation_barrier:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
   key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
  using envelope_translation_impossible single_shot_success_uniform_bound by simp

end

locale genuinely_ambiguous_nl_translation_barrier =
  defeasible_nl_to_monotone_target H w F +
  genuinely_ambiguous_nl_source I \<tau> w n K
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and I :: "('k,'w,'n,'c,'u) keyed_reg"
    and \<tau> :: "('u,'f) trans"
    and n :: 'n
    and K :: "'k set"
begin

theorem envelope_translation_impossible:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w)"
  using no_exact_envelope_translation .

theorem single_shot_translation_impossible:
  "\<not> (\<exists>T. single_shot_task_translator I \<tau> T w)"
  using no_single_shot_translation_on .

theorem single_shot_success_strictly_subperfect:
  "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1"
  using single_shot_uniform_success_strict_lt_one .

theorem strong_core_translation_barrier:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
   \<not> (\<exists>T. single_shot_task_translator I \<tau> T w) \<and>
   key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1"
  using envelope_translation_impossible single_shot_translation_impossible single_shot_success_strictly_subperfect
  by simp

end

section \<open>Reading guide\<close>

text \<open>
  Main theorem packages:

    \<^item> @{locale nl_translation_barrier};
    \<^item> @{locale genuinely_ambiguous_nl_translation_barrier};
    \<^item> @{thm nl_translation_barrier.core_translation_barrier};
    \<^item> @{thm genuinely_ambiguous_nl_translation_barrier.strong_core_translation_barrier}.
\<close>

end
