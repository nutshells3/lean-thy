theory Step8_AuditedSurrogateJudge
  imports Step7_CheckerBarrier
begin

definition judge_accept_prob ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> real"
where
  "judge_accept_prob H J \<tau> w c \<Gamma> \<phi> =
     measure_pmf.prob (a_gen H w c \<Gamma> \<phi>) {\<pi>. J w \<pi> c (\<tau> \<phi>)}"

definition judge_disagree_prob ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> real"
where
  "judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi> =
     measure_pmf.prob (a_gen H w c \<Gamma> \<phi>)
       {\<pi>. J_fast w \<pi> c (\<tau> \<phi>) \<noteq> J_gold w \<pi> c (\<tau> \<phi>)}"

definition audit_error_at_most ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> real \<Rightarrow> bool"
where
  "audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta> \<longleftrightarrow>
     judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<le> \<eta>"

lemma judge_accept_prob_nonneg:
  "0 \<le> judge_accept_prob H J \<tau> w c \<Gamma> \<phi>"
  unfolding judge_accept_prob_def by simp

lemma judge_accept_prob_le1:
  "judge_accept_prob H J \<tau> w c \<Gamma> \<phi> \<le> 1"
  unfolding judge_accept_prob_def by simp

lemma judge_disagree_prob_nonneg:
  "0 \<le> judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi>"
  unfolding judge_disagree_prob_def by simp

lemma judge_disagree_prob_le1:
  "judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<le> 1"
  unfolding judge_disagree_prob_def by simp

lemma judge_disagree_symmetric:
  "judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi> =
   judge_disagree_prob H J_gold J_fast \<tau> w c \<Gamma> \<phi>"
  unfolding judge_disagree_prob_def by (auto intro: arg_cong[where f="measure_pmf.prob _"])

definition fast_abstain_prob ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow>
   'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> real"
where
  "fast_abstain_prob H abstains w c \<Gamma> \<phi> =
     measure_pmf.prob (a_gen H w c \<Gamma> \<phi>) (Collect (abstains w))"

definition effective_accept_prob ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> real"
where
  "effective_accept_prob H J_fast J_gold abstains \<tau> w c \<Gamma> \<phi> =
     measure_pmf.prob (a_gen H w c \<Gamma> \<phi>)
       {\<pi>. (\<not> abstains w \<pi> \<and> J_fast w \<pi> c (\<tau> \<phi>)) \<or>
            (abstains w \<pi> \<and> J_gold w \<pi> c (\<tau> \<phi>))}"

lemma effective_accept_prob_nonneg:
  "0 \<le> effective_accept_prob H J_fast J_gold abstains \<tau> w c \<Gamma> \<phi>"
  unfolding effective_accept_prob_def by simp

lemma effective_accept_prob_le1:
  "effective_accept_prob H J_fast J_gold abstains \<tau> w c \<Gamma> \<phi> \<le> 1"
  unfolding effective_accept_prob_def by simp

theorem degraded_fast_to_gold_lower_bound:
  "judge_accept_prob H J_gold \<tau> w c \<Gamma> \<phi> \<ge>
   judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> -
   judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi>"
proof -
  let ?D = "a_gen H w c \<Gamma> \<phi>"
  let ?\<psi> = "\<tau> \<phi>"
  let ?A = "{\<pi>. J_fast w \<pi> c ?\<psi>}"
  let ?B = "{\<pi>. J_gold w \<pi> c ?\<psi>}"
  let ?E = "{\<pi>. J_fast w \<pi> c ?\<psi> \<noteq> J_gold w \<pi> c ?\<psi>}"
  have sub: "?A \<subseteq> ?B \<union> ?E" by auto
  have mono: "measure_pmf.prob ?D ?A \<le> measure_pmf.prob ?D (?B \<union> ?E)"
    by (rule measure_pmf.finite_measure_mono[OF sub]) simp
  have subad: "measure_pmf.prob ?D (?B \<union> ?E) \<le>
               measure_pmf.prob ?D ?B + measure_pmf.prob ?D ?E"
    by (rule measure_subadditive) (simp_all add: measure_pmf.emeasure_eq_measure)
  from mono subad show ?thesis
    unfolding judge_accept_prob_def judge_disagree_prob_def by linarith
qed

corollary degraded_with_audit_bound:
  assumes "audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta>"
  shows "judge_accept_prob H J_gold \<tau> w c \<Gamma> \<phi> \<ge>
         judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>"
proof -
  from degraded_fast_to_gold_lower_bound
  have "judge_accept_prob H J_gold \<tau> w c \<Gamma> \<phi> \<ge>
        judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> -
        judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi>" .
  moreover from assms have "judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<le> \<eta>"
    unfolding audit_error_at_most_def by simp
  ultimately show ?thesis by linarith
qed

locale audited_surrogate_judge =
  fixes H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and J_fast :: "'w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool"
    and \<tau> :: "('u,'f) trans"
    and \<eta> :: real
  assumes eta_pos: "0 < \<eta>"
    and nondegen: "\<exists>w' \<pi> c \<psi>. J_fast w' \<pi> c \<psi> \<noteq> f_check F w' \<pi> c \<psi>"
begin

abbreviation J_gold where
  "J_gold \<equiv> f_check F"

lemma gold_accept_is_success_prob:
  "judge_accept_prob H J_gold \<tau> w c \<Gamma> \<phi> = success_prob H F \<tau> w c \<Gamma> \<phi>"
  unfolding judge_accept_prob_def success_prob_def by simp

theorem success_prob_lower_bound_from_fast:
  assumes "audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta>"
  shows "success_prob H F \<tau> w c \<Gamma> \<phi> \<ge>
         judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>"
  using degraded_with_audit_bound[OF assms] gold_accept_is_success_prob by simp

theorem nondegen_bound_strictly_weaker:
  "judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta> <
   judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi>"
  using eta_pos by simp

end

definition task_audit_error_at_most ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> real \<Rightarrow> bool"
where
  "task_audit_error_at_most H J_fast J_gold \<tau> w Tasks \<eta> \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> Tasks \<longrightarrow>
        audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta>)"

lemma task_audit_bound_imp_gold_lower:
  assumes "task_audit_error_at_most H J_fast J_gold \<tau> w Tasks \<eta>"
    and "(c,\<Gamma>,\<phi>) \<in> Tasks"
  shows "judge_accept_prob H J_gold \<tau> w c \<Gamma> \<phi> \<ge>
         judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>"
proof -
  from assms have "audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta>"
    unfolding task_audit_error_at_most_def by blast
  then show ?thesis by (rule degraded_with_audit_bound)
qed

locale audited_obstruction_package =
  obstruction_package H w F I \<tau> n K +
  audited_surrogate_judge H w F J_fast \<tau> \<eta>
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and I :: "('k,'w,'n,'c,'u) keyed_reg"
    and \<tau> :: "('u,'f) trans"
    and n :: 'n
    and K :: "'k set"
    and J_fast :: "'w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool"
    and \<eta> :: real
begin

theorem audited_barrier_with_degraded_bound:
  assumes R: "verified_reflective_on_agent H F \<tau> w"
    and cov: "agent_covers_derivable H F \<tau> w"
    and Fin: "finite_task_distribution D"
    and supp: "set_pmf D = agent_task_support H w"
    and audit: "task_audit_error_at_most H J_fast J_gold \<tau> w (agent_task_support H w) \<eta>"
  shows "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
         expected_success H F \<tau> w D < 1 \<and>
         (\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> agent_task_support H w \<longrightarrow>
            success_prob H F \<tau> w c \<Gamma> \<phi> \<ge>
            judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>)"
proof -
  have barrier: "\<not> task_restricted_translatable H F w (agent_task_envelope H w) \<and>
                 \<not> (\<exists>T. single_shot_task_translator I \<tau> T w) \<and>
                 key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1 \<and>
                 expected_success H F \<tau> w D < 1"
    by (rule complete_obstruction_line[OF R cov Fin supp])
  have degraded: "\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> agent_task_support H w \<longrightarrow>
                    success_prob H F \<tau> w c \<Gamma> \<phi> \<ge>
                    judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>"
  proof (intro allI impI)
    fix c \<Gamma> \<phi>
    assume mem: "(c,\<Gamma>,\<phi>) \<in> agent_task_support H w"
    from audit mem have "audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta>"
      unfolding task_audit_error_at_most_def by blast
    then show "success_prob H F \<tau> w c \<Gamma> \<phi> \<ge>
               judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>"
      by (rule success_prob_lower_bound_from_fast)
  qed
  from barrier degraded show ?thesis by simp
qed

end

end
