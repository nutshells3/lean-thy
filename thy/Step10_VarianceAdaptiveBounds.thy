theory Step10_VarianceAdaptiveBounds
  imports Step9_AnytimeValidStopping
begin

lemma le_nat_ceiling_real:
  assumes "0 \<le> x"
  shows "x \<le> real (nat \<lceil>x\<rceil>)"
proof -
  have "\<lceil>x\<rceil> \<ge> 0" using assms by (simp add: ceiling_mono)
  then have "real (nat \<lceil>x\<rceil>) = of_int \<lceil>x\<rceil>" by simp
  also have "of_int \<lceil>x\<rceil> \<ge> x" by (rule le_of_int_ceiling)
  finally show ?thesis by linarith
qed

lemma sqrt_ge_one:
  assumes "1 \<le> (x :: real)"
  shows "1 \<le> sqrt x"
  using assms real_sqrt_le_mono[of 1 x] by simp

type_synonym half_width_fn = "nat \<Rightarrow> real"

definition hw_nonneg :: "half_width_fn \<Rightarrow> bool" where
  "hw_nonneg h \<longleftrightarrow> (\<forall>n. 0 \<le> h n)"

definition hw_vanishing :: "half_width_fn \<Rightarrow> bool" where
  "hw_vanishing h \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. h n < \<epsilon>)"

definition hoeffding_hw :: "real \<Rightarrow> real \<Rightarrow> half_width_fn" where
  "hoeffding_hw b c = (\<lambda>n. b * c / sqrt (real (n + 1)))"

definition eb_hw :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> half_width_fn" where
  "eb_hw b c1 c2 s = (\<lambda>n. s n * c1 / sqrt (real (n + 1)) + b * c2 / real (n + 1))"

lemma sqrt_le_self_nat: "sqrt (real (n + 1)) \<le> real (n + 1)"
proof -
  have "1 \<le> real (n + 1)" by simp
  then have s: "sqrt (real (n + 1)) * sqrt (real (n + 1)) = real (n + 1)"
    by simp
  have "1 \<le> sqrt (real (n + 1))"
    using \<open>1 \<le> real (n + 1)\<close> by (rule sqrt_ge_one)
  then have "sqrt (real (n + 1)) * 1 \<le> sqrt (real (n + 1)) * sqrt (real (n + 1))"
    by (intro mult_left_mono) auto
  then show ?thesis using s by simp
qed

lemma eb_hw_le_hoeffding_hw:
  assumes b_pos: "0 < b"
    and c_pos: "0 < c"
    and c_sum_le: "c1 + c2 \<le> c"
    and c1_pos: "0 \<le> c1"
    and c2_pos: "0 \<le> c2"
    and s_bound: "\<And>n. 0 \<le> s n" "\<And>n. s n \<le> b"
  shows "eb_hw b c1 c2 s n \<le> hoeffding_hw b c n"
proof -
  have n1_pos: "0 < real (n + 1)" by simp
  have sqrt_pos: "0 < sqrt (real (n + 1))"
    using n1_pos by simp
  have sqrt_le: "sqrt (real (n + 1)) \<le> real (n + 1)"
    by (rule sqrt_le_self_nat)
  have "s n * c1 / sqrt (real (n + 1)) \<le> b * c1 / sqrt (real (n + 1))"
    using s_bound c1_pos sqrt_pos b_pos
    by (intro divide_right_mono mult_right_mono) auto
  moreover have "b * c2 / real (n + 1) \<le> b * c2 / sqrt (real (n + 1))"
  proof -
    have "0 \<le> b * c2" using b_pos c2_pos by auto
    then show ?thesis using sqrt_le sqrt_pos n1_pos
      by (intro frac_le) auto
  qed
  ultimately have "eb_hw b c1 c2 s n \<le> b * c1 / sqrt (real (n + 1)) + b * c2 / sqrt (real (n + 1))"
    unfolding eb_hw_def by linarith
  also have "\<dots> = b * (c1 + c2) / sqrt (real (n + 1))"
    by (simp add: algebra_simps add_divide_distrib)
  also have "\<dots> \<le> b * c / sqrt (real (n + 1))"
    using c_sum_le b_pos sqrt_pos
    by (intro divide_right_mono mult_left_mono) auto
  also have "\<dots> = hoeffding_hw b c n"
    unfolding hoeffding_hw_def ..
  finally show ?thesis .
qed

lemma eb_hw_strict_improvement:
  assumes b_pos: "0 < b"
    and c_pos: "0 < c"
    and c1_pos: "0 < c1"
    and c1_le: "c1 \<le> c"
    and s_small: "s n < b"
    and s_nonneg: "0 \<le> s n"
  shows "s n * c1 / sqrt (real (n + 1)) < b * c / sqrt (real (n + 1))"
proof -
  have sqrt_pos: "0 < sqrt (real (n + 1))" by simp
  have "s n * c1 < b * c"
  proof -
    have "s n * c1 \<le> s n * c" using c1_le s_nonneg by (intro mult_left_mono) auto
    also have "\<dots> < b * c" using s_small c_pos by (intro mult_strict_right_mono) auto
    finally show ?thesis .
  qed
  then show ?thesis
    using sqrt_pos by (intro divide_strict_right_mono) auto
qed

definition hw_conf_seq :: "(nat \<Rightarrow> real) \<Rightarrow> half_width_fn \<Rightarrow> conf_seq" where
  "hw_conf_seq mu h = \<lparr> cs_lower = (\<lambda>n. mu n - h n),
                         cs_upper = (\<lambda>n. mu n + h n) \<rparr>"

lemma hw_conf_seq_well_formed:
  assumes "hw_nonneg h"
  shows "cs_well_formed (hw_conf_seq mu h)"
  using assms unfolding cs_well_formed_def hw_conf_seq_def hw_nonneg_def
  by auto

lemma hw_conf_seq_width:
  "cs_width (hw_conf_seq mu h) n = 2 * h n"
  unfolding cs_width_def hw_conf_seq_def by simp

lemma hw_vanishing_imp_cs_vanishing:
  assumes "hw_vanishing h"
  shows "cs_width_vanishing (hw_conf_seq mu h)"
  unfolding cs_width_vanishing_def
proof (intro allI impI)
  fix \<epsilon> :: real assume eps: "0 < \<epsilon>"
  then have "0 < \<epsilon> / 2" by simp
  from assms[unfolded hw_vanishing_def] this
  obtain N where "\<forall>n\<ge>N. h n < \<epsilon> / 2" by blast
  then have "\<forall>n\<ge>N. cs_width (hw_conf_seq mu h) n < \<epsilon>"
    using hw_conf_seq_width by auto
  then show "\<exists>N. \<forall>n\<ge>N. cs_width (hw_conf_seq mu h) n < \<epsilon>" by blast
qed

definition first_exclusion :: "conf_seq \<Rightarrow> real \<Rightarrow> nat" where
  "first_exclusion cs thr = (LEAST T. cs_upper cs T < thr)"

lemma first_exclusion_attains:
  assumes "\<exists>T. cs_upper cs T < thr"
  shows "cs_upper cs (first_exclusion cs thr) < thr"
  unfolding first_exclusion_def using assms by (rule LeastI_ex)

lemma first_exclusion_le:
  assumes "cs_upper cs T < thr"
  shows "first_exclusion cs thr \<le> T"
  unfolding first_exclusion_def using assms by (rule Least_le)

lemma narrower_hw_narrower_cs:
  assumes "\<And>n. h1 n \<le> h2 n"
  shows "cs_width (hw_conf_seq mu h1) n \<le> cs_width (hw_conf_seq mu h2) n"
  using assms unfolding hw_conf_seq_width by auto

lemma narrower_cs_earlier_exclusion:
  assumes narrow: "\<And>n. h_eb n \<le> h_H n"
    and hw_nn: "hw_nonneg h_eb"
    and covers: "\<And>n. cs_covers_at (hw_conf_seq mu h_eb) \<theta> n"
    and excl: "cs_upper (hw_conf_seq mu h_H) T < thr"
  shows "cs_upper (hw_conf_seq mu h_eb) T < thr"
proof -
  have "cs_upper (hw_conf_seq mu h_eb) T \<le> cs_upper (hw_conf_seq mu h_H) T"
    using narrow[of T] unfolding hw_conf_seq_def by simp
  with excl show ?thesis by linarith
qed

lemma eb_hw_vanishing:
  assumes "0 < b" "0 \<le> c1" "0 \<le> c2"
    and s_bound: "\<And>n. s n \<le> b"
    and s_nonneg: "\<And>n. 0 \<le> s n"
  shows "hw_vanishing (eb_hw b c1 c2 s)"
  unfolding hw_vanishing_def eb_hw_def
proof (intro allI impI)
  fix \<epsilon> :: real assume eps: "0 < \<epsilon>"
  define M where "M = b * (c1 + c2)"
  have M_nonneg: "0 \<le> M" unfolding M_def using assms by (intro mult_nonneg_nonneg add_nonneg_nonneg) auto
  show "\<exists>N. \<forall>n\<ge>N. s n * c1 / sqrt (real (n + 1)) + b * c2 / real (n + 1) < \<epsilon>"
  proof (cases "M = 0")
    case True
    then have "c1 = 0 \<and> c2 = 0" using assms M_def by (auto simp: mult_eq_0_iff)
    then show ?thesis using eps by (intro exI[of _ 0]) auto
  next
    case False
    then have M_pos: "0 < M" using M_nonneg by linarith
    define N where "N = nat \<lceil>(M / \<epsilon>)\<^sup>2\<rceil>"
    show ?thesis
    proof (intro exI allI impI)
      fix n assume nN: "n \<ge> N"
      have n1_pos: "0 < real (n + 1)" by simp
      have sqrt_pos: "0 < sqrt (real (n + 1))" by simp
      have s1: "s n * c1 / sqrt (real (n + 1)) \<le> b * c1 / sqrt (real (n + 1))"
        using s_bound[of n] s_nonneg[of n] assms(2) sqrt_pos
        by (intro divide_right_mono mult_right_mono) auto
      have s2: "b * c2 / real (n + 1) \<le> b * c2 / sqrt (real (n + 1))"
      proof -
        have "0 \<le> b * c2" using assms(1,3) by auto
        then show ?thesis using sqrt_le_self_nat sqrt_pos n1_pos
          by (intro frac_le) auto
      qed
      have sum_le: "s n * c1 / sqrt (real (n + 1)) + b * c2 / real (n + 1)
                    \<le> M / sqrt (real (n + 1))"
      proof -
        have "b * c1 / sqrt (real (n + 1)) + b * c2 / sqrt (real (n + 1))
              = (b * c1 + b * c2) / sqrt (real (n + 1))"
          by (simp add: add_divide_distrib)
        also have "\<dots> = b * (c1 + c2) / sqrt (real (n + 1))"
          by (simp add: algebra_simps)
        also have "\<dots> = M / sqrt (real (n + 1))"
          unfolding M_def ..
        finally show ?thesis using s1 s2 by linarith
      qed
      have "M / sqrt (real (n + 1)) < \<epsilon>"
      proof -
        have me: "0 < M / \<epsilon>" using M_pos eps by simp
        have sq_nn: "0 \<le> (M / \<epsilon>)\<^sup>2" by simp
        have N_ge: "real N \<ge> (M / \<epsilon>)\<^sup>2"
        proof -
          have "real (nat \<lceil>(M / \<epsilon>)\<^sup>2\<rceil>) \<ge> (M / \<epsilon>)\<^sup>2"
            using sq_nn le_nat_ceiling_real by auto
          then show ?thesis unfolding N_def .
        qed
        have "(M / \<epsilon>)\<^sup>2 < real (n + 1)"
          using N_ge nN by linarith
        then have "M / \<epsilon> < sqrt (real (n + 1))"
          by (rule real_less_rsqrt)
        then have "M < sqrt (real (n + 1)) * \<epsilon>"
          using eps by (simp add: field_simps)
        then show ?thesis using sqrt_pos eps
          by (simp add: field_simps)
      qed
      with sum_le show "s n * c1 / sqrt (real (n + 1)) + b * c2 / real (n + 1) < \<epsilon>"
        by linarith
    qed
  qed
qed

lemma eb_hw_nonneg:
  assumes "0 \<le> c1" "0 \<le> c2" "0 < b"
    and "\<And>n. 0 \<le> s n"
  shows "hw_nonneg (eb_hw b c1 c2 s)"
  unfolding hw_nonneg_def eb_hw_def
proof (intro allI)
  fix n
  have "0 \<le> s n * c1 / sqrt (real (n + 1))"
    using assms by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
  moreover have "0 \<le> b * c2 / real (n + 1)"
    using assms by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
  ultimately show "0 \<le> s n * c1 / sqrt (real (n + 1)) + b * c2 / real (n + 1)"
    by linarith
qed

lemma eb_cs_well_formed:
  assumes "0 \<le> c1" "0 \<le> c2" "0 < b"
    and "\<And>n. 0 \<le> s n"
  shows "cs_well_formed (hw_conf_seq mu (eb_hw b c1 c2 s))"
  by (rule hw_conf_seq_well_formed[OF eb_hw_nonneg[OF assms]])

lemma eb_cs_eventually_stops:
  assumes "0 < b" "0 \<le> c1" "0 \<le> c2"
    and "\<And>n. 0 \<le> s n" "\<And>n. s n \<le> b"
    and "anytime_valid (hw_conf_seq mu (eb_hw b c1 c2 s)) \<theta> \<alpha>"
    and "\<theta> < \<eta>_max"
  shows "\<exists>T. cs_upper (hw_conf_seq mu (eb_hw b c1 c2 s)) T < \<eta>_max"
proof -
  have "hw_vanishing (eb_hw b c1 c2 s)"
    using assms(1-3,5,4) by (rule eb_hw_vanishing)
  then have wv: "cs_width_vanishing (hw_conf_seq mu (eb_hw b c1 c2 s))"
    by (rule hw_vanishing_imp_cs_vanishing)
  show ?thesis
    by (rule vanishing_cs_eventually_stops[OF assms(6) wv assms(7)])
qed

lemma hoeffding_hw_nonneg:
  assumes "0 \<le> b" "0 \<le> c"
  shows "hw_nonneg (hoeffding_hw b c)"
  unfolding hw_nonneg_def hoeffding_hw_def
  using assms by (auto intro: mult_nonneg_nonneg divide_nonneg_pos)

lemma hoeffding_cs_well_formed:
  assumes "0 \<le> b" "0 \<le> c"
  shows "cs_well_formed (hw_conf_seq mu (hoeffding_hw b c))"
  by (rule hw_conf_seq_well_formed[OF hoeffding_hw_nonneg[OF assms]])

lemma hoeffding_hw_vanishing:
  assumes "0 < b" "0 < c"
  shows "hw_vanishing (hoeffding_hw b c)"
  unfolding hw_vanishing_def hoeffding_hw_def
proof (intro allI impI)
  fix \<epsilon> :: real assume eps: "0 < \<epsilon>"
  define N where "N = nat \<lceil>(b * c / \<epsilon>)\<^sup>2\<rceil>"
  show "\<exists>N. \<forall>n\<ge>N. b * c / sqrt (real (n + 1)) < \<epsilon>"
  proof (intro exI allI impI)
    fix n assume "n \<ge> N"
    have bc_pos: "0 < b * c" using assms by simp
    have sqrt_pos: "0 < sqrt (real (n + 1))" by simp
    have "sqrt (real (N + 1)) \<le> sqrt (real (n + 1))"
      using \<open>n \<ge> N\<close> by (intro real_sqrt_le_mono) simp
    then have "b * c / sqrt (real (n + 1)) \<le> b * c / sqrt (real (N + 1))"
      using bc_pos sqrt_pos by (intro divide_left_mono mult_pos_pos) auto
    also have "\<dots> < \<epsilon>"
    proof -
      have bc_eps: "0 < b * c / \<epsilon>" using bc_pos eps by simp
      have sq_nonneg: "0 \<le> (b * c / \<epsilon>)\<^sup>2" by simp
      have N_ge: "real N \<ge> (b * c / \<epsilon>)\<^sup>2"
      proof -
        have "real (nat \<lceil>(b * c / \<epsilon>)\<^sup>2\<rceil>) \<ge> (b * c / \<epsilon>)\<^sup>2"
          using sq_nonneg le_nat_ceiling_real by auto
        then show ?thesis unfolding N_def .
      qed
      have "(b * c / \<epsilon>)\<^sup>2 < real (N + 1)"
        using N_ge by simp
      then have "b * c / \<epsilon> < sqrt (real (N + 1))"
        by (rule real_less_rsqrt)
      then have "b * c < sqrt (real (N + 1)) * \<epsilon>"
        using eps by (simp add: field_simps)
      then show ?thesis
        using sqrt_pos eps bc_pos by (simp add: field_simps pos_divide_less_eq)
    qed
    finally show "b * c / sqrt (real (n + 1)) < \<epsilon>" .
  qed
qed

lemma hoeffding_cs_eventually_stops:
  assumes "0 < b" "0 < c"
    and "anytime_valid (hw_conf_seq mu (hoeffding_hw b c)) \<theta> \<alpha>"
    and "\<theta> < \<eta>_max"
  shows "\<exists>T. cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T < \<eta>_max"
proof -
  have "hw_vanishing (hoeffding_hw b c)"
    using assms(1,2) by (rule hoeffding_hw_vanishing)
  then have wv: "cs_width_vanishing (hw_conf_seq mu (hoeffding_hw b c))"
    by (rule hw_vanishing_imp_cs_vanishing)
  show ?thesis
    by (rule vanishing_cs_eventually_stops[OF assms(3) wv assms(4)])
qed

locale eb_audited_stopping =
  audited_surrogate_judge H w F J_fast \<tau> \<eta>
  for H :: "('w,'c,'u,'p) stochastic_agent"
    and w :: 'w
    and F :: "('w,'c,'f,'p) formal_system"
    and J_fast :: "'w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool"
    and \<tau> :: "('u,'f) trans"
    and \<eta> :: real +
  fixes b :: real
    and c1 :: real
    and c2 :: real
    and s :: "nat \<Rightarrow> real"
    and mu :: "nat \<Rightarrow> real"
    and \<alpha> :: real
    and \<eta>_max :: real
  assumes b_pos: "0 < b"
    and c1_nonneg: "0 \<le> c1"
    and c2_nonneg: "0 \<le> c2"
    and s_nonneg: "\<And>n. 0 \<le> s n"
    and s_bounded: "\<And>n. s n \<le> b"
    and eb_valid: "anytime_valid (hw_conf_seq mu (eb_hw b c1 c2 s)) \<eta> \<alpha>"
    and alpha_range: "0 < \<alpha>" "\<alpha> < 1"
    and threshold_pos: "0 < \<eta>_max"
begin

abbreviation eb_cs where
  "eb_cs \<equiv> hw_conf_seq mu (eb_hw b c1 c2 s)"

sublocale cs_audited_stopping H w F J_fast \<tau> \<eta> eb_cs \<alpha> \<eta>_max
  by (unfold_locales) (simp_all add: eb_valid alpha_range threshold_pos)

lemma eb_cs_wf: "cs_well_formed eb_cs"
  using b_pos c1_nonneg c2_nonneg s_nonneg
  by (intro eb_cs_well_formed) auto

lemma eb_stops_when_below:
  assumes "\<eta> < \<eta>_max"
  shows "\<exists>T. cs_upper eb_cs T < \<eta>_max"
  using b_pos c1_nonneg c2_nonneg s_nonneg s_bounded eb_valid assms
  by (intro eb_cs_eventually_stops) auto

theorem eb_stops_no_later_than_hoeffding:
  assumes c_pos: "0 < c"
    and c_sum_le: "c1 + c2 \<le> c"
    and hoeff_excl: "cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T < \<eta>_max"
  shows "cs_upper eb_cs T < \<eta>_max"
proof -
  have "eb_hw b c1 c2 s T \<le> hoeffding_hw b c T"
    using b_pos c_pos c_sum_le c1_nonneg c2_nonneg s_nonneg s_bounded
    by (intro eb_hw_le_hoeffding_hw) auto
  then have "cs_upper eb_cs T \<le> cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T"
    unfolding hw_conf_seq_def by simp
  with hoeff_excl show ?thesis by linarith
qed

lemma eb_strictly_narrower_at:
  assumes c_pos: "0 < c"
    and c1_pos: "0 < c1"
    and c_sum_le: "c1 + c2 \<le> c"
    and s_small: "s T < b"
  shows "cs_upper eb_cs T < cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T"
proof -
  have sqrt_pos: "0 < sqrt (real (T + 1))" by simp
  have n1_pos: "0 < real (T + 1)" by simp
  have t1: "s T * c1 / sqrt (real (T + 1)) < b * c1 / sqrt (real (T + 1))"
    using s_small c1_pos s_nonneg[of T] sqrt_pos b_pos
    by (intro divide_strict_right_mono mult_strict_right_mono) auto
  have "0 \<le> b * c2" using b_pos c2_nonneg by auto
  then have t2: "b * c2 / real (T + 1) \<le> b * c2 / sqrt (real (T + 1))"
    using sqrt_le_self_nat sqrt_pos n1_pos by (intro frac_le) auto
  have "eb_hw b c1 c2 s T < b * c1 / sqrt (real (T + 1)) + b * c2 / sqrt (real (T + 1))"
    unfolding eb_hw_def using t1 t2 by linarith
  also have "\<dots> = b * (c1 + c2) / sqrt (real (T + 1))"
    by (simp add: algebra_simps add_divide_distrib)
  also have "\<dots> \<le> b * c / sqrt (real (T + 1))"
    using c_sum_le b_pos sqrt_pos
    by (intro divide_right_mono mult_left_mono) auto
  also have "\<dots> = hoeffding_hw b c T"
    unfolding hoeffding_hw_def ..
  finally show ?thesis unfolding hw_conf_seq_def by simp
qed

theorem eb_first_exclusion_no_later:
  assumes c_pos: "0 < c"
    and c_sum_le: "c1 + c2 \<le> c"
    and hoeff_stops: "\<exists>T. cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T < \<eta>_max"
  shows "first_exclusion eb_cs \<eta>_max \<le> first_exclusion (hw_conf_seq mu (hoeffding_hw b c)) \<eta>_max"
proof -
  define T_H where "T_H = first_exclusion (hw_conf_seq mu (hoeffding_hw b c)) \<eta>_max"
  have hoeff_at_TH: "cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T_H < \<eta>_max"
    unfolding T_H_def by (rule first_exclusion_attains[OF hoeff_stops])
  from eb_stops_no_later_than_hoeffding[OF c_pos c_sum_le hoeff_at_TH]
  have "cs_upper eb_cs T_H < \<eta>_max" .
  then have "first_exclusion eb_cs \<eta>_max \<le> T_H"
    by (rule first_exclusion_le)
  then show ?thesis unfolding T_H_def .
qed

theorem eb_5B_upgrade_summary:
  assumes c_pos: "0 < c"
    and c_sum_le: "c1 + c2 \<le> c"
    and below: "\<eta> < \<eta>_max"
    and hoeff_stops: "\<exists>T. cs_upper (hw_conf_seq mu (hoeffding_hw b c)) T < \<eta>_max"
  shows "cs_well_formed eb_cs
       \<and> (\<exists>T. cs_upper eb_cs T < \<eta>_max)
       \<and> first_exclusion eb_cs \<eta>_max \<le> first_exclusion (hw_conf_seq mu (hoeffding_hw b c)) \<eta>_max"
proof (intro conjI)
  show "cs_well_formed eb_cs"
    by (rule eb_cs_wf)
next
  show "\<exists>T. cs_upper eb_cs T < \<eta>_max"
    using below by (rule eb_stops_when_below)
next
  show "first_exclusion eb_cs \<eta>_max \<le> first_exclusion (hw_conf_seq mu (hoeffding_hw b c)) \<eta>_max"
    using c_pos c_sum_le hoeff_stops by (rule eb_first_exclusion_no_later)
qed

end

end
