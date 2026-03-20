theory Step8_AuditedSurrogateTheoremSchema
  imports Step7_ExactCheckerBarrier
begin

section \<open>5A audited surrogate theorem schema\<close>

text \<open>
  This theory contains the mathematical core of the audited-surrogate line:
  judge acceptance, judge disagreement, audit-error bounds, and the degraded
  fast-to-gold lower-bound theorem.

  The design-side judge-stack instantiation lives in
  @{theory Design2_JudgeStackInstantiation}.
\<close>

subsection \<open>Judge acceptance and disagreement probabilities\<close>

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
  unfolding judge_disagree_prob_def by (auto intro: arg_cong[where f = "measure_pmf.prob _"])

subsection \<open>Core degradation bound\<close>

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
  have subad:
    "measure_pmf.prob ?D (?B \<union> ?E) \<le>
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
  moreover from assms
  have "judge_disagree_prob H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<le> \<eta>"
    unfolding audit_error_at_most_def by simp
  ultimately show ?thesis by linarith
qed

subsection \<open>Task-level audited bound\<close>

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

end
