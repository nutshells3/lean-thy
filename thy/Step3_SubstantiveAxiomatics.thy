theory Step3_SubstantiveAxiomatics
  imports Step2_WeakTranslation
begin

locale defeasible_nl_agent =
  fixes H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
  assumes defeasible_witness:
    "\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
begin

lemma witness_pair_in_envelope:
  "contains_nonmono_witness_pair H w (agent_task_envelope H w)"
proof -
  obtain c \<Gamma> \<Delta> \<phi>
    where H1: "a_derives H w c \<Gamma> \<phi>"
      and H2: "\<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    using defeasible_witness by blast
  show ?thesis
    by (rule witness_pair_lives_in_agent_task_envelope[OF H1 H2])
qed

end

locale standard_monotone_target =
  fixes F :: "('w,'c,'f,'p) formal_system"
    and w :: 'w
  assumes monotone_target:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"

locale defeasible_nl_to_monotone_target =
  defeasible_nl_agent H w + standard_monotone_target F w
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
begin

theorem no_exact_envelope_translation:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w)"
  by (rule nonmono_pair_blocks_task_restricted_translation[OF monotone_target witness_pair_in_envelope])

theorem no_exact_envelope_tr1_on:
  "\<forall>\<tau>. \<not> tr1_on H F \<tau> w (agent_task_envelope H w)"
proof (intro allI notI)
  fix \<tau>
  assume T: "tr1_on H F \<tau> w (agent_task_envelope H w)"
  from no_exact_envelope_translation
  show False
    unfolding task_restricted_translatable_def
    using T by blast
qed

theorem no_global_tr1_at_world:
  "\<forall>\<tau>. \<not> tr1 H F \<tau> w"
  by (rule nonmono_pair_blocks_global_tr1[OF monotone_target witness_pair_in_envelope])

end

interpretation tweety_substantive_agent:
  defeasible_nl_agent H_tweety Wtw
proof
  show "\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H_tweety Wtw c \<Gamma> \<phi> \<and>
                      \<not> a_derives H_tweety Wtw c (\<Gamma> \<union> \<Delta>) \<phi>"
    unfolding H_tweety_def
    by (intro exI[of _ Ctw] exI[of _ "{UBird}"] exI[of _ "{UPenguin}"] exI[of _ UFlies]) simp
qed

interpretation tweety_monotone_target:
  standard_monotone_target F_tweety Wtw
proof
  show "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F_tweety Wtw c \<Gamma> \<psi> \<Longrightarrow> f_derives F_tweety Wtw c (\<Gamma> \<union> \<Delta>) \<psi>"
    by (rule mono_F_tweety)
qed

theorem tweety_substantive_envelope_barrier:
  "\<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw)"
proof -
  have W: "contains_nonmono_witness_pair H_tweety Wtw (agent_task_envelope H_tweety Wtw)"
    by (rule tweety_substantive_agent.witness_pair_in_envelope)
  show ?thesis
    by (rule nonmono_pair_blocks_task_restricted_translation[OF mono_F_tweety W])
qed

theorem tweety_substantive_no_global_tr1:
  "\<forall>\<tau>. \<not> tr1 H_tweety F_tweety \<tau> Wtw"
proof - 
  have W: "contains_nonmono_witness_pair H_tweety Wtw (agent_task_envelope H_tweety Wtw)"
    by (rule tweety_substantive_agent.witness_pair_in_envelope)
  show ?thesis
    by (rule nonmono_pair_blocks_global_tr1[OF mono_F_tweety W])
qed

definition H_monobird :: "(W_tw,C_tw,U_tw,P_tw) stochastic_agent"
where
  "H_monobird =
     \<lparr> a_derives = (\<lambda>w c \<Gamma> \<phi>. \<phi> = UFlies \<and> UBird \<in> \<Gamma>),
       a_prefers = (\<lambda>w c \<pi>1 \<pi>2. True),
       a_gen     = (\<lambda>w c \<Gamma> \<phi>. return_pmf Ptw) \<rparr>"

lemma H_monobird_not_defeasible:
  "\<not> (\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H_monobird Wtw c \<Gamma> \<phi> \<and>
                    \<not> a_derives H_monobird Wtw c (\<Gamma> \<union> \<Delta>) \<phi>)"
  unfolding H_monobird_def by auto

lemma tau_tweety_eq_FFlies_iff [simp]:
  "\<tau>_tweety u = FFlies \<longleftrightarrow> u = UFlies"
  by (cases u) simp_all

lemma FBird_in_tau_tweety_image_iff [simp]:
  "FBird \<in> \<tau>_tweety ` \<Gamma> \<longleftrightarrow> UBird \<in> \<Gamma>"
proof
  assume "FBird \<in> \<tau>_tweety ` \<Gamma>"
  then obtain u where "u \<in> \<Gamma>" and "\<tau>_tweety u = FBird"
    by force
  then show "UBird \<in> \<Gamma>"
    by (cases u) simp_all
next
  assume "UBird \<in> \<Gamma>"
  then have "\<tau>_tweety UBird \<in> \<tau>_tweety ` \<Gamma>"
    by blast
  then show "FBird \<in> \<tau>_tweety ` \<Gamma>"
    by simp
qed

lemma tr1_monobird:
  "tr1 H_monobird F_tweety \<tau>_tweety Wtw"
  unfolding tr1_def H_monobird_def F_tweety_def by auto

theorem monobird_substantive_success:
  "(\<not> (\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H_monobird Wtw c \<Gamma> \<phi> \<and>
                     \<not> a_derives H_monobird Wtw c (\<Gamma> \<union> \<Delta>) \<phi>)) \<and>
   standard_monotone_target F_tweety Wtw \<and>
   tr1 H_monobird F_tweety \<tau>_tweety Wtw \<and>
   task_restricted_translatable H_monobird F_tweety Wtw (agent_task_envelope H_monobird Wtw)"
proof (intro conjI)
  show "\<not> (\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H_monobird Wtw c \<Gamma> \<phi> \<and>
                        \<not> a_derives H_monobird Wtw c (\<Gamma> \<union> \<Delta>) \<phi>)"
    by (rule H_monobird_not_defeasible)
next
  show "standard_monotone_target F_tweety Wtw"
    by unfold_locales (rule mono_F_tweety)
next
  show "tr1 H_monobird F_tweety \<tau>_tweety Wtw"
    by (rule tr1_monobird)
next
  show "task_restricted_translatable H_monobird F_tweety Wtw (agent_task_envelope H_monobird Wtw)"
    unfolding task_restricted_translatable_def
    using tr1_imp_tr1_on[OF tr1_monobird] by blast
qed

theorem tweety_substantive_failure_package:
  "defeasible_nl_agent H_tweety Wtw \<and>
   standard_monotone_target F_tweety Wtw \<and>
   \<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw)"
proof (intro conjI)
  show "defeasible_nl_agent H_tweety Wtw"
    by unfold_locales (rule tweety_substantive_agent.defeasible_witness)
next
  show "standard_monotone_target F_tweety Wtw"
    by unfold_locales (rule mono_F_tweety)
next
  show "\<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw)"
    by (rule tweety_substantive_envelope_barrier)
qed

theorem substantive_axioms_separate_translation_outcomes:
  "((\<not> (\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H_monobird Wtw c \<Gamma> \<phi> \<and>
                      \<not> a_derives H_monobird Wtw c (\<Gamma> \<union> \<Delta>) \<phi>)) \<and>
    standard_monotone_target F_tweety Wtw \<and>
    task_restricted_translatable H_monobird F_tweety Wtw (agent_task_envelope H_monobird Wtw)) \<and>
   (defeasible_nl_agent H_tweety Wtw \<and>
    standard_monotone_target F_tweety Wtw \<and>
    \<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw))"
  using monobird_substantive_success tweety_substantive_failure_package by blast

end
