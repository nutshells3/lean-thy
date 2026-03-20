theory Step7_ExactCheckerBarrier
  imports Step6_MainClaims
begin

section \<open>Enriched target-side package with checker/derivability linkage\<close>

text \<open>
  Target-side checker packages. If checker acceptance implies derivability from
  empty premises, target monotonicity lifts acceptance to derivability from
  arbitrary premise sets.

  This theory is the exact/perfect checker line. It is the \<eta> = 0 special case
  of the later audited-surrogate program, where checker acceptance and formal
  derivability line up without disagreement or abstention. The nondegenerate
  fast/gold judge generalization now splits across
  Step8_AuditedSurrogateTheoremSchema and Design2_JudgeStackInstantiation.
\<close>

subsection \<open>Verified-search support and boundary notions\<close>

definition verified_success_at_least ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> real \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> bool"
where
  "verified_success_at_least H F \<tau> p w c \<Gamma> \<phi> \<longleftrightarrow>
     p \<le> success_prob H F \<tau> w c \<Gamma> \<phi>"

definition verified_success_on ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> real \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> bool"
where
  "verified_success_on H F \<tau> p w Tasks \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> Tasks \<longrightarrow> verified_success_at_least H F \<tau> p w c \<Gamma> \<phi>)"

definition agent_task_support ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set"
where
  "agent_task_support H w = {(c,\<Gamma>,\<phi>). a_derives H w c \<Gamma> \<phi>}"

definition verified_success_on_distribution ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> real \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) pmf \<Rightarrow> bool"
where
  "verified_success_on_distribution H F \<tau> p w D \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> set_pmf D \<longrightarrow> verified_success_at_least H F \<tau> p w c \<Gamma> \<phi>)"

definition task_success_prob ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) \<Rightarrow> real"
where
  "task_success_prob H F \<tau> w t =
     (case t of (c,\<Gamma>,\<phi>) \<Rightarrow> success_prob H F \<tau> w c \<Gamma> \<phi>)"

definition expected_success ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) pmf \<Rightarrow> real"
where
  "expected_success H F \<tau> w D =
     measure_pmf.expectation D (task_success_prob H F \<tau> w)"

definition finite_task_distribution :: "(('c,'u) task) pmf \<Rightarrow> bool"
where
  "finite_task_distribution D \<longleftrightarrow> finite (set_pmf D)"

definition verified_complete_on_agent ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "verified_complete_on_agent H F \<tau> w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. a_derives H w c \<Gamma> \<phi> \<longrightarrow> success_prob H F \<tau> w c \<Gamma> \<phi> = 1)"

definition verified_reflective_on_agent ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "verified_reflective_on_agent H F \<tau> w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. success_prob H F \<tau> w c \<Gamma> \<phi> = 1 \<longrightarrow> a_derives H w c \<Gamma> \<phi>)"

definition verified_sound_to_formal ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "verified_sound_to_formal H F \<tau> w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. 0 < success_prob H F \<tau> w c \<Gamma> \<phi> \<longrightarrow> f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>))"

definition verified_complete_from_formal ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "verified_complete_from_formal H F \<tau> w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>) \<longrightarrow> success_prob H F \<tau> w c \<Gamma> \<phi> = 1)"

definition uniform_verified_solver ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "uniform_verified_solver H F \<tau> w \<longleftrightarrow>
     verified_complete_on_agent H F \<tau> w \<and>
     verified_reflective_on_agent H F \<tau> w \<and>
     verified_sound_to_formal H F \<tau> w \<and>
     verified_complete_from_formal H F \<tau> w"

lemma task_success_prob_le1:
  "task_success_prob H F \<tau> w t \<le> 1"
  unfolding task_success_prob_def
  by (cases t) (simp add: success_prob_le1)

lemma verified_success_on_support_one_imp_complete_on_agent:
  assumes V: "verified_success_on H F \<tau> 1 w (agent_task_support H w)"
  shows "verified_complete_on_agent H F \<tau> w"
proof (unfold verified_complete_on_agent_def, intro allI impI)
  fix c \<Gamma> \<phi>
  assume Hder: "a_derives H w c \<Gamma> \<phi>"
  from V have "verified_success_at_least H F \<tau> 1 w c \<Gamma> \<phi>"
    using Hder unfolding verified_success_on_def agent_task_support_def by blast
  then have lower: "1 \<le> success_prob H F \<tau> w c \<Gamma> \<phi>"
    unfolding verified_success_at_least_def by simp
  have upper: "success_prob H F \<tau> w c \<Gamma> \<phi> \<le> 1"
    by (rule success_prob_le1)
  from lower upper show "success_prob H F \<tau> w c \<Gamma> \<phi> = 1"
    by simp
qed

theorem uniform_verified_solver_imp_tr1:
  assumes U: "uniform_verified_solver H F \<tau> w"
  shows "tr1 H F \<tau> w"
proof (unfold tr1_def, intro allI iffI)
  fix c \<Gamma> \<phi>
  assume Hder: "a_derives H w c \<Gamma> \<phi>"
  from U have C: "verified_complete_on_agent H F \<tau> w"
    and S: "verified_sound_to_formal H F \<tau> w"
    unfolding uniform_verified_solver_def by simp_all
  from C Hder have "success_prob H F \<tau> w c \<Gamma> \<phi> = 1"
    unfolding verified_complete_on_agent_def by blast
  hence "0 < success_prob H F \<tau> w c \<Gamma> \<phi>" by simp
  with S show "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
    unfolding verified_sound_to_formal_def by blast
next
  fix c \<Gamma> \<phi>
  assume Fder: "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
  from U have R: "verified_reflective_on_agent H F \<tau> w"
    and C: "verified_complete_from_formal H F \<tau> w"
    unfolding uniform_verified_solver_def by simp_all
  from C Fder have "success_prob H F \<tau> w c \<Gamma> \<phi> = 1"
    unfolding verified_complete_from_formal_def by blast
  with R show "a_derives H w c \<Gamma> \<phi>"
    unfolding verified_reflective_on_agent_def by blast
qed

theorem nonmono_at_world_blocks_uniform_verified_solver:
  assumes mono_F: "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and nonmono_H: "\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
  shows "\<forall>\<tau>. \<not> uniform_verified_solver H F \<tau> w"
proof (intro allI notI)
  fix \<tau>
  assume U: "uniform_verified_solver H F \<tau> w"
  obtain c \<Gamma> \<Delta> \<phi>
    where H1: "a_derives H w c \<Gamma> \<phi>"
      and H2: "\<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    using nonmono_H by blast
  have W: "contains_nonmono_witness_pair H w (agent_task_envelope H w)"
    by (rule witness_pair_lives_in_agent_task_envelope[OF H1 H2])
  from uniform_verified_solver_imp_tr1[OF U]
  have "tr1 H F \<tau> w" .
  with nonmono_pair_blocks_global_tr1[OF mono_F W, rule_format, of \<tau>]
  show False by blast
qed

theorem nonmono_at_world_blocks_perfect_support_success:
  assumes mono_F: "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and nonmono_H: "\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    and R: "verified_reflective_on_agent H F \<tau> w"
    and S: "verified_sound_to_formal H F \<tau> w"
    and C: "verified_complete_from_formal H F \<tau> w"
  shows "\<not> verified_success_on H F \<tau> 1 w (agent_task_support H w)"
proof
  assume V: "verified_success_on H F \<tau> 1 w (agent_task_support H w)"
  from verified_success_on_support_one_imp_complete_on_agent[OF V]
  have A: "verified_complete_on_agent H F \<tau> w" .
  from A R S C have U: "uniform_verified_solver H F \<tau> w"
    unfolding uniform_verified_solver_def by simp
  from nonmono_at_world_blocks_uniform_verified_solver[OF mono_F nonmono_H, rule_format, of \<tau>] U
  show False by contradiction
qed

theorem nonmono_at_world_forces_subperfect_support_task:
  assumes mono_F: "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and nonmono_H: "\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    and R: "verified_reflective_on_agent H F \<tau> w"
    and S: "verified_sound_to_formal H F \<tau> w"
    and C: "verified_complete_from_formal H F \<tau> w"
  shows "\<exists>t \<in> agent_task_support H w. task_success_prob H F \<tau> w t < 1"
proof -
  have not_all: "\<not> verified_success_on H F \<tau> 1 w (agent_task_support H w)"
    by (rule nonmono_at_world_blocks_perfect_support_success[OF mono_F nonmono_H R S C])
  then obtain c \<Gamma> \<phi>
    where mem: "(c,\<Gamma>,\<phi>) \<in> agent_task_support H w"
      and fail: "\<not> verified_success_at_least H F \<tau> 1 w c \<Gamma> \<phi>"
    unfolding verified_success_on_def by blast
  have not_one_le: "\<not> 1 \<le> success_prob H F \<tau> w c \<Gamma> \<phi>"
    using fail unfolding verified_success_at_least_def by simp
  have task_eq:
    "task_success_prob H F \<tau> w (c,\<Gamma>,\<phi>) = success_prob H F \<tau> w c \<Gamma> \<phi>"
    unfolding task_success_prob_def by simp
  have "task_success_prob H F \<tau> w (c,\<Gamma>,\<phi>) < 1"
    using not_one_le task_eq by linarith
  with mem show ?thesis by blast
qed

theorem full_support_distribution_expected_success_lt_one:
  assumes Fin: "finite_task_distribution D"
    and mono_F: "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and nonmono_H: "\<exists>c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    and R: "verified_reflective_on_agent H F \<tau> w"
    and S: "verified_sound_to_formal H F \<tau> w"
    and C: "verified_complete_from_formal H F \<tau> w"
    and supp: "set_pmf D = agent_task_support H w"
  shows "expected_success H F \<tau> w D < 1"
proof -
  let ?S = "set_pmf D"
  obtain t where tmem: "t \<in> ?S" and tlt: "task_success_prob H F \<tau> w t < 1"
    using nonmono_at_world_forces_subperfect_support_task[OF mono_F nonmono_H R S C] supp by blast
  have finS: "finite ?S"
    using Fin unfolding finite_task_distribution_def by simp
  have exp_sum:
    "expected_success H F \<tau> w D = (\<Sum>a\<in>?S. pmf D a * task_success_prob H F \<tau> w a)"
  proof -
    have "expected_success H F \<tau> w D = (\<Sum>a\<in>?S. task_success_prob H F \<tau> w a * pmf D a)"
      using Fin unfolding expected_success_def finite_task_distribution_def
      by (subst integral_measure_pmf_real[of ?S]) auto
    also have "\<dots> = (\<Sum>a\<in>?S. pmf D a * task_success_prob H F \<tau> w a)"
      by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have rest_le:
    "(\<Sum>a\<in>?S - {t}. pmf D a * task_success_prob H F \<tau> w a) \<le> (\<Sum>a\<in>?S - {t}. pmf D a)"
  proof (rule sum_mono)
    fix a
    assume "a \<in> ?S - {t}"
    have "task_success_prob H F \<tau> w a \<le> 1"
      by (rule task_success_prob_le1)
    then have "pmf D a * task_success_prob H F \<tau> w a \<le> pmf D a * 1"
      by (intro mult_left_mono) simp_all
    then show "pmf D a * task_success_prob H F \<tau> w a \<le> pmf D a"
      by simp
  qed
  have tpos: "0 < pmf D t"
    using tmem by (rule pmf_positive)
  have term_lt:
    "pmf D t * task_success_prob H F \<tau> w t < pmf D t"
    using mult_strict_left_mono[OF tlt tpos] by simp
  have split_sum:
    "(\<Sum>a\<in>?S. pmf D a * task_success_prob H F \<tau> w a) =
     (\<Sum>a\<in>?S - {t}. pmf D a * task_success_prob H F \<tau> w a) +
     pmf D t * task_success_prob H F \<tau> w t"
    using finS tmem by (simp add: sum.remove)
  have pmf_split:
    "(\<Sum>a\<in>?S. pmf D a) = (\<Sum>a\<in>?S - {t}. pmf D a) + pmf D t"
    using finS tmem by (simp add: sum.remove)
  have sum_one: "(\<Sum>a\<in>?S. pmf D a) = 1"
    by (rule sum_pmf_eq_1) (use finS in auto)
  have
    "(\<Sum>a\<in>?S - {t}. pmf D a * task_success_prob H F \<tau> w a) +
     pmf D t * task_success_prob H F \<tau> w t <
     (\<Sum>a\<in>?S - {t}. pmf D a) + pmf D t"
    using rest_le term_lt by linarith
  then have "(\<Sum>a\<in>?S. pmf D a * task_success_prob H F \<tau> w a) < (\<Sum>a\<in>?S. pmf D a)"
    using split_sum pmf_split by simp
  with exp_sum sum_one show ?thesis by simp
qed

subsection \<open>Target-side checker packages\<close>

locale checker_sound_target =
  standard_monotone_target F w
  for F :: "('w,'c,'f,'p) formal_system"
    and w :: 'w +
  assumes checker_soundness:
    "\<And>\<pi> c \<psi>. f_check F w \<pi> c \<psi> \<Longrightarrow> f_derives F w c {} \<psi>"
begin

lemma checker_sound_any_premises:
  assumes "f_check F w \<pi> c \<psi>"
  shows "f_derives F w c \<Gamma> \<psi>"
proof -
  from checker_soundness[OF assms] have "f_derives F w c {} \<psi>" .
  from monotone_target[OF this] show ?thesis by simp
qed

end

locale checker_complete_target =
  standard_monotone_target F w
  for F :: "('w,'c,'f,'p) formal_system"
    and w :: 'w +
  assumes checker_completeness:
    "\<And>c \<Gamma> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> \<exists>\<pi>. f_check F w \<pi> c \<psi>"

locale checkable_monotone_target =
  checker_sound_target F w + checker_complete_target F w
  for F :: "('w,'c,'f,'p) formal_system"
    and w :: 'w
begin

lemma derivability_iff_checkable:
  "f_derives F w c \<Gamma> \<psi> \<longleftrightarrow> (\<exists>\<pi>. f_check F w \<pi> c \<psi>)"
proof
  assume "f_derives F w c \<Gamma> \<psi>"
  then show "\<exists>\<pi>. f_check F w \<pi> c \<psi>"
    by (rule checker_completeness)
next
  assume "\<exists>\<pi>. f_check F w \<pi> c \<psi>"
  then obtain \<pi> where "f_check F w \<pi> c \<psi>" by blast
  then show "f_derives F w c \<Gamma> \<psi>"
    by (rule checker_sound_any_premises)
qed

end

subsection \<open>Derived verified-search linkage\<close>

lemma positive_success_prob_witness:
  assumes "0 < success_prob H F \<tau> w c \<Gamma> \<phi>"
  shows "\<exists>\<pi>\<in>set_pmf (a_gen H w c \<Gamma> \<phi>). f_check F w \<pi> c (\<tau> \<phi>)"
proof (rule ccontr)
  assume neg: "\<not> (\<exists>\<pi>\<in>set_pmf (a_gen H w c \<Gamma> \<phi>). f_check F w \<pi> c (\<tau> \<phi>))"
  then have empty:
    "{\<pi>. f_check F w \<pi> c (\<tau> \<phi>)} \<inter> set_pmf (a_gen H w c \<Gamma> \<phi>) = {}"
    by auto
  have "measure_pmf.prob (a_gen H w c \<Gamma> \<phi>) {\<pi>. f_check F w \<pi> c (\<tau> \<phi>)} =
        measure_pmf.prob (a_gen H w c \<Gamma> \<phi>)
          ({\<pi>. f_check F w \<pi> c (\<tau> \<phi>)} \<inter> set_pmf (a_gen H w c \<Gamma> \<phi>))"
    by (rule measure_Int_set_pmf[symmetric])
  also have "\<dots> = 0"
    using empty by simp
  finally have "success_prob H F \<tau> w c \<Gamma> \<phi> = 0"
    unfolding success_prob_def .
  with assms show False by simp
qed

locale defeasible_agent_with_sound_target =
  defeasible_nl_agent H w + checker_sound_target F w
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
begin

theorem derived_verified_sound_to_formal:
  "verified_sound_to_formal H F \<tau> w"
proof (unfold verified_sound_to_formal_def, intro allI impI)
  fix c \<Gamma> \<phi>
  assume "0 < success_prob H F \<tau> w c \<Gamma> \<phi>"
  from positive_success_prob_witness[OF this]
  obtain \<pi> where "\<pi> \<in> set_pmf (a_gen H w c \<Gamma> \<phi>)"
    and chk: "f_check F w \<pi> c (\<tau> \<phi>)"
    by blast
  from checker_sound_any_premises[OF chk]
  show "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)" .
qed

theorem envelope_translation_impossible:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w)"
  by (rule nonmono_pair_blocks_task_restricted_translation[OF monotone_target witness_pair_in_envelope])

theorem uniform_verified_solver_blocked:
  assumes R: "verified_reflective_on_agent H F \<tau> w"
    and C: "verified_complete_from_formal H F \<tau> w"
  shows "\<not> verified_success_on H F \<tau> 1 w (agent_task_support H w)"
proof (rule nonmono_at_world_blocks_perfect_support_success
           [OF monotone_target defeasible_witness])
  show "verified_reflective_on_agent H F \<tau> w" by (rule R)
  show "verified_sound_to_formal H F \<tau> w"
    by (rule derived_verified_sound_to_formal)
  show "verified_complete_from_formal H F \<tau> w" by (rule C)
qed

theorem expected_success_boundary:
  assumes R: "verified_reflective_on_agent H F \<tau> w"
    and C: "verified_complete_from_formal H F \<tau> w"
    and Fin: "finite_task_distribution D"
    and supp: "set_pmf D = agent_task_support H w"
  shows "expected_success H F \<tau> w D < 1"
  by (rule full_support_distribution_expected_success_lt_one
          [OF Fin monotone_target defeasible_witness R
              derived_verified_sound_to_formal C supp])

end

subsection \<open>Coverage turns completeness into an axiom package\<close>

definition agent_covers_derivable ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "agent_covers_derivable H F \<tau> w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>) \<longrightarrow>
        measure_pmf.prob (a_gen H w c \<Gamma> \<phi>) {\<pi>. f_check F w \<pi> c (\<tau> \<phi>)} = 1)"

locale defeasible_agent_with_checkable_target =
  defeasible_nl_agent H w + checkable_monotone_target F w
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
begin

theorem derived_verified_sound_to_formal:
  "verified_sound_to_formal H F \<tau> w"
proof (unfold verified_sound_to_formal_def, intro allI impI)
  fix c \<Gamma> \<phi>
  assume "0 < success_prob H F \<tau> w c \<Gamma> \<phi>"
  from positive_success_prob_witness[OF this]
  obtain \<pi> where "\<pi> \<in> set_pmf (a_gen H w c \<Gamma> \<phi>)"
    and chk: "f_check F w \<pi> c (\<tau> \<phi>)"
    by blast
  from checker_sound_any_premises[OF chk]
  show "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)" .
qed

theorem agent_coverage_yields_complete_from_formal:
  assumes cov: "agent_covers_derivable H F \<tau> w"
  shows "verified_complete_from_formal H F \<tau> w"
proof (unfold verified_complete_from_formal_def, intro allI impI)
  fix c \<Gamma> \<phi>
  assume "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
  from cov this
  show "success_prob H F \<tau> w c \<Gamma> \<phi> = 1"
    unfolding agent_covers_derivable_def success_prob_def by blast
qed

theorem full_barrier_with_coverage:
  assumes R: "verified_reflective_on_agent H F \<tau> w"
    and cov: "agent_covers_derivable H F \<tau> w"
    and Fin: "finite_task_distribution D"
    and supp: "set_pmf D = agent_task_support H w"
  shows "expected_success H F \<tau> w D < 1"
  by (rule full_support_distribution_expected_success_lt_one
          [OF Fin monotone_target defeasible_witness R
              derived_verified_sound_to_formal
              agent_coverage_yields_complete_from_formal[OF cov] supp])

end

subsection \<open>Combined barrier\<close>

locale nl_checkable_translation_barrier =
  defeasible_agent_with_checkable_target H w F +
  genuinely_ambiguous_nl_translation_barrier H w F I \<tau> n K
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and I :: "('k,'w,'n,'c,'u) keyed_reg"
    and \<tau> :: "('u,'f) trans"
    and n :: 'n
    and K :: "'k set"
begin

theorem full_checkable_barrier:
  "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
   \<not> (\<exists>T. single_shot_task_translator I \<tau> T w) \<and>
   key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1"
  by (rule strong_core_translation_barrier)

theorem full_checkable_barrier_with_performance:
  assumes R: "verified_reflective_on_agent H F \<tau> w"
    and cov: "agent_covers_derivable H F \<tau> w"
    and Fin: "finite_task_distribution D"
    and supp: "set_pmf D = agent_task_support H w"
  shows "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
         \<not> (\<exists>T. single_shot_task_translator I \<tau> T w) \<and>
         key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1 \<and>
         expected_success H F \<tau> w D < 1"
proof -
  have B4: "expected_success H F \<tau> w D < 1"
    by (rule full_barrier_with_coverage[OF R cov Fin supp])
  with full_checkable_barrier show ?thesis by simp
qed

end
