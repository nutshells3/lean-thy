theory Step9_AnytimeValidStopping
  imports Step8_AuditedSurrogateJudge
begin

record conf_seq =
  cs_lower :: "nat \<Rightarrow> real"
  cs_upper :: "nat \<Rightarrow> real"

definition cs_well_formed :: "conf_seq \<Rightarrow> bool" where
  "cs_well_formed cs \<longleftrightarrow> (\<forall>n. cs_lower cs n \<le> cs_upper cs n)"

definition cs_covers_at :: "conf_seq \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "cs_covers_at cs \<theta> n \<longleftrightarrow> cs_lower cs n \<le> \<theta> \<and> \<theta> \<le> cs_upper cs n"

definition fixed_time_valid ::
  "conf_seq \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool"
where
  "fixed_time_valid cs \<theta> \<alpha> n \<longleftrightarrow> cs_covers_at cs \<theta> n"

definition anytime_valid ::
  "conf_seq \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
where
  "anytime_valid cs \<theta> \<alpha> \<longleftrightarrow> (\<forall>n. cs_covers_at cs \<theta> n)"

lemma anytime_valid_imp_fixed:
  assumes "anytime_valid cs \<theta> \<alpha>"
  shows "fixed_time_valid cs \<theta> \<alpha> n"
  using assms unfolding anytime_valid_def fixed_time_valid_def by simp

lemma anytime_valid_bounds:
  assumes "anytime_valid cs \<theta> \<alpha>"
  shows "cs_lower cs n \<le> \<theta>" and "\<theta> \<le> cs_upper cs n"
  using assms unfolding anytime_valid_def cs_covers_at_def by auto

definition cs_excludes_above :: "conf_seq \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "cs_excludes_above cs thr n \<longleftrightarrow> cs_upper cs n < thr"

definition cs_excludes_below :: "conf_seq \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "cs_excludes_below cs thr n \<longleftrightarrow> cs_lower cs n > thr"

theorem cs_stop_upper_bound_safe:
  assumes valid: "anytime_valid cs \<theta> \<alpha>"
    and stop: "cs_upper cs T < \<eta>_max"
  shows "\<theta> < \<eta>_max"
proof -
  from valid have "\<theta> \<le> cs_upper cs T"
    by (rule anytime_valid_bounds(2))
  with stop show ?thesis by linarith
qed

theorem cs_stop_lower_bound_safe:
  assumes valid: "anytime_valid cs \<theta> \<alpha>"
    and stop: "cs_lower cs T > \<eta>_min"
  shows "\<theta> > \<eta>_min"
proof -
  from valid have "cs_lower cs T \<le> \<theta>"
    by (rule anytime_valid_bounds(1))
  with stop show ?thesis by linarith
qed

locale cs_audited_stopping =
  audited_surrogate_judge H w F J_fast \<tau> \<eta>
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and J_fast :: "'w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool"
    and \<tau> :: "('u,'f) trans"
    and \<eta> :: real +
  fixes cs :: conf_seq
    and \<alpha> :: real
    and \<eta>_max :: real
  assumes cs_valid: "anytime_valid cs \<eta> \<alpha>"
    and alpha_range: "0 < \<alpha>" "\<alpha> < 1"
    and threshold_pos: "0 < \<eta>_max"
begin

theorem stopped_audit_error_bound:
  assumes "cs_upper cs T < \<eta>_max"
  shows "\<eta> < \<eta>_max"
  using cs_valid assms by (rule cs_stop_upper_bound_safe)

theorem stopped_success_lower_bound:
  assumes stop: "cs_upper cs T < \<eta>_max"
    and audit: "audit_error_at_most H J_fast J_gold \<tau> w c \<Gamma> \<phi> \<eta>"
  shows "success_prob H F \<tau> w c \<Gamma> \<phi> \<ge>
         judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>_max"
proof -
  from stopped_audit_error_bound[OF stop] have "\<eta> < \<eta>_max" .
  from success_prob_lower_bound_from_fast[OF audit]
  have "success_prob H F \<tau> w c \<Gamma> \<phi> \<ge>
        judge_accept_prob H J_fast \<tau> w c \<Gamma> \<phi> - \<eta>" .
  moreover have "\<eta> \<le> \<eta>_max" using \<open>\<eta> < \<eta>_max\<close> by simp
  ultimately show ?thesis by linarith
qed

end

definition cs_width :: "conf_seq \<Rightarrow> nat \<Rightarrow> real" where
  "cs_width cs n = cs_upper cs n - cs_lower cs n"

definition cs_width_nonincreasing :: "conf_seq \<Rightarrow> bool" where
  "cs_width_nonincreasing cs \<longleftrightarrow>
     (\<forall>m n. m \<le> n \<longrightarrow> cs_width cs n \<le> cs_width cs m)"

definition cs_width_vanishing :: "conf_seq \<Rightarrow> bool" where
  "cs_width_vanishing cs \<longleftrightarrow>
     (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. cs_width cs n < \<epsilon>)"

lemma vanishing_cs_eventually_stops:
  assumes valid: "anytime_valid cs \<theta> \<alpha>"
    and vanish: "cs_width_vanishing cs"
    and below: "\<theta> < \<eta>_max"
  shows "\<exists>T. cs_upper cs T < \<eta>_max"
proof -
  let ?\<epsilon> = "\<eta>_max - \<theta>"
  from below have eps_pos: "?\<epsilon> > 0" by simp
  from vanish eps_pos obtain N where
    width_small: "\<forall>n\<ge>N. cs_width cs n < ?\<epsilon>"
    unfolding cs_width_vanishing_def by blast
  have "cs_upper cs N < \<eta>_max"
  proof -
    from valid have "\<theta> \<le> cs_upper cs N"
      by (rule anytime_valid_bounds(2))
    from valid have "cs_lower cs N \<le> \<theta>"
      by (rule anytime_valid_bounds(1))
    from width_small have "cs_width cs N < ?\<epsilon>" by simp
    then have "cs_upper cs N - cs_lower cs N < \<eta>_max - \<theta>"
      unfolding cs_width_def .
    with \<open>cs_lower cs N \<le> \<theta>\<close> show ?thesis by linarith
  qed
  then show ?thesis by blast
qed

end
