theory Step9_AnytimeValidStoppingTheorem
  imports Step8_AuditedSurrogateTheoremSchema
begin

section \<open>5C anytime-valid stopping theorem\<close>

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
