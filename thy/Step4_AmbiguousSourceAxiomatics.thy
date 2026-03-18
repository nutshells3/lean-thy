theory Step4_AmbiguousSourceAxiomatics
  imports Step3_SubstantiveAxiomatics
begin

type_synonym ('k,'w,'n,'c,'u) keyed_reg = "'k \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> bool"
type_synonym ('c,'f) formal_task = "'c \<times> 'f set \<times> 'f"

definition formal_task_of ::
  "('u,'f) trans \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> ('c,'f) formal_task"
where
  "formal_task_of \<tau> c \<Gamma> \<phi> = (c, \<tau> ` \<Gamma>, \<tau> \<phi>)"

definition utterance_admissible ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow> 'k \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> bool"
where
  "utterance_admissible I k w n \<longleftrightarrow> (\<exists>c \<Gamma> \<phi>. I k w n c \<Gamma> \<phi>)"

definition task_compatible_with_key ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'k \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> ('c,'f) formal_task \<Rightarrow> bool"
where
  "task_compatible_with_key I \<tau> k w n t \<longleftrightarrow>
     (\<exists>c \<Gamma> \<phi>. I k w n c \<Gamma> \<phi> \<and> t = formal_task_of \<tau> c \<Gamma> \<phi>)"

definition single_shot_task_translator ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> ('n \<Rightarrow> ('c,'f) formal_task) \<Rightarrow> 'w \<Rightarrow> bool"
where
  "single_shot_task_translator I \<tau> T w \<longleftrightarrow>
     (\<forall>k n. utterance_admissible I k w n \<longrightarrow> task_compatible_with_key I \<tau> k w n (T n))"

definition interactive_task_translator ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> ('k \<Rightarrow> 'n \<Rightarrow> ('c,'f) formal_task) \<Rightarrow> 'w \<Rightarrow> bool"
where
  "interactive_task_translator I \<tau> T w \<longleftrightarrow>
     (\<forall>k n. utterance_admissible I k w n \<longrightarrow> task_compatible_with_key I \<tau> k w n (T k n))"

definition key_task_conflict ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool"
where
  "key_task_conflict I \<tau> w n k1 k2 \<longleftrightarrow>
     (\<forall>t. \<not> (task_compatible_with_key I \<tau> k1 w n t \<and>
                task_compatible_with_key I \<tau> k2 w n t))"

definition key_conditioned_success_prob ::
  "'k pmf \<Rightarrow>
   ('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> ('n \<Rightarrow> ('c,'f) formal_task) \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> real"
where
  "key_conditioned_success_prob D I \<tau> T w n =
     measure_pmf.prob D {k. utterance_admissible I k w n \<and>
                            task_compatible_with_key I \<tau> k w n (T n)}"

definition pairwise_key_conflict_on ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "pairwise_key_conflict_on I \<tau> w n K \<longleftrightarrow>
     (\<forall>k1\<in>K. \<forall>k2\<in>K. k1 \<noteq> k2 \<longrightarrow> key_task_conflict I \<tau> w n k1 k2)"

definition max_supported_key_mass :: "'k pmf \<Rightarrow> real"
where
  "max_supported_key_mass D = Max (pmf D ` set_pmf D)"

lemma single_shot_task_translatorD:
  assumes "single_shot_task_translator I \<tau> T w"
    and "utterance_admissible I k w n"
  shows "task_compatible_with_key I \<tau> k w n (T n)"
  using assms unfolding single_shot_task_translator_def by blast

lemma finite_card_le1_cases:
  assumes fin: "finite A" and card_le: "card A \<le> 1"
  shows "A = {} \<or> (\<exists>a. A = {a})"
proof (cases "A = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain a where aA: "a \<in> A" by blast
  have "\<forall>a1\<in>A. \<forall>a2\<in>A. a1 = a2"
    using fin card_le by (simp add: card_le_Suc0_iff_eq)
  then have "A = {a}"
    using aA by auto
  then show ?thesis by blast
qed

lemma pairwise_conflict_event_card_le1:
  assumes finK: "finite K"
    and PW: "pairwise_key_conflict_on I \<tau> w n K"
  shows "card (K \<inter> {k. utterance_admissible I k w n \<and>
                        task_compatible_with_key I \<tau> k w n (T n)}) \<le> 1"
proof -
  let ?E = "{k. utterance_admissible I k w n \<and> task_compatible_with_key I \<tau> k w n (T n)}"
  have "\<forall>a1\<in>K \<inter> ?E. \<forall>a2\<in>K \<inter> ?E. a1 = a2"
  proof (intro ballI)
    fix a1 a2
    assume A1: "a1 \<in> K \<inter> ?E" and A2: "a2 \<in> K \<inter> ?E"
    show "a1 = a2"
    proof (rule ccontr)
      assume neq: "a1 \<noteq> a2"
      from PW A1 A2 neq have C: "key_task_conflict I \<tau> w n a1 a2"
        unfolding pairwise_key_conflict_on_def by blast
      from A1 have C1: "task_compatible_with_key I \<tau> a1 w n (T n)" by auto
      from A2 have C2: "task_compatible_with_key I \<tau> a2 w n (T n)" by auto
      from C have "\<not> (task_compatible_with_key I \<tau> a1 w n (T n) \<and>
                         task_compatible_with_key I \<tau> a2 w n (T n))"
        unfolding key_task_conflict_def by blast
      with C1 C2 show False by blast
    qed
  qed
  moreover have "finite (K \<inter> ?E)"
    using finK by simp
  ultimately show ?thesis
    by (simp add: card_le_Suc0_iff_eq)
qed

lemma max_supported_key_mass_ge:
  assumes fin: "finite (set_pmf D)" and k: "k \<in> set_pmf D"
  shows "pmf D k \<le> max_supported_key_mass D"
  unfolding max_supported_key_mass_def
  by (rule Max_ge) (use assms in auto)

theorem conflicting_keys_refute_single_shot_existence:
  assumes "utterance_admissible I k1 w n"
    and "utterance_admissible I k2 w n"
    and "key_task_conflict I \<tau> w n k1 k2"
  shows "\<not> (\<exists>T. single_shot_task_translator I \<tau> T w)"
proof
  assume "\<exists>T. single_shot_task_translator I \<tau> T w"
  then obtain T where T: "single_shot_task_translator I \<tau> T w" by blast
  from single_shot_task_translatorD[OF T assms(1)]
  have C1: "task_compatible_with_key I \<tau> k1 w n (T n)" .
  from single_shot_task_translatorD[OF T assms(2)]
  have C2: "task_compatible_with_key I \<tau> k2 w n (T n)" .
  from assms(3) have "\<not> (task_compatible_with_key I \<tau> k1 w n (T n) \<and>
                            task_compatible_with_key I \<tau> k2 w n (T n))"
    unfolding key_task_conflict_def by blast
  with C1 C2 show False by blast
qed

theorem key_revealed_interaction_recovers_translation:
  assumes Cover:
    "\<And>k n. utterance_admissible I k w n \<Longrightarrow> \<exists>t. task_compatible_with_key I \<tau> k w n t"
  shows "\<exists>T. interactive_task_translator I \<tau> T w"
proof -
  define T where "T k n = (SOME t. task_compatible_with_key I \<tau> k w n t)" for k n
  have "interactive_task_translator I \<tau> T w"
  proof (unfold interactive_task_translator_def, intro allI impI)
    fix k n
    assume A: "utterance_admissible I k w n"
    from Cover[OF A] have "\<exists>t. task_compatible_with_key I \<tau> k w n t" .
    then show "task_compatible_with_key I \<tau> k w n (T k n)"
      unfolding T_def by (rule someI_ex)
  qed
  then show ?thesis by blast
qed

theorem pairwise_conflict_uniform_bound:
  assumes finK: "finite K"
    and nonemptyK: "K \<noteq> {}"
    and adm: "\<And>k. k \<in> K \<Longrightarrow> utterance_admissible I k w n"
    and PW: "pairwise_key_conflict_on I \<tau> w n K"
  shows "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
proof -
  let ?E = "{k. utterance_admissible I k w n \<and> task_compatible_with_key I \<tau> k w n (T n)}"
  have card_le: "card (K \<inter> ?E) \<le> 1"
    by (rule pairwise_conflict_event_card_le1[OF finK PW])
  have prob_eq:
    "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n = card (K \<inter> ?E) / card K"
    unfolding key_conditioned_success_prob_def
    by (subst measure_pmf_of_set[of K ?E]) (use finK nonemptyK in auto)
  also have "\<dots> \<le> 1 / card K"
  proof -
    have Kpos: "0 < card K"
      using finK nonemptyK by (simp add: card_gt_0_iff)
    from card_le have "real (card (K \<inter> ?E)) \<le> 1"
      by simp
    with Kpos show ?thesis
      by (simp add: divide_right_mono)
  qed
  finally show ?thesis .
qed

theorem pairwise_conflict_uniform_tight:
  assumes finK: "finite K"
    and nonemptyK: "K \<noteq> {}"
    and adm: "\<And>k. k \<in> K \<Longrightarrow> utterance_admissible I k w n"
    and PW: "pairwise_key_conflict_on I \<tau> w n K"
    and k0: "k0 \<in> K"
    and comp0: "task_compatible_with_key I \<tau> k0 w n t0"
    and Tn: "T n = t0"
  shows "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n = 1 / card K"
proof -
  let ?E = "{k. utterance_admissible I k w n \<and> task_compatible_with_key I \<tau> k w n (T n)}"
  have Eeq: "K \<inter> ?E = {k0}"
  proof
    show "K \<inter> ?E \<subseteq> {k0}"
    proof
      fix k
      assume kE: "k \<in> K \<inter> ?E"
      show "k \<in> {k0}"
      proof (cases "k = k0")
        case True
        then show ?thesis by simp
      next
        case False
        from PW kE k0 False have C: "key_task_conflict I \<tau> w n k k0"
          unfolding pairwise_key_conflict_on_def by blast
        from kE have Ck: "task_compatible_with_key I \<tau> k w n (T n)" by auto
        from comp0 Tn have C0: "task_compatible_with_key I \<tau> k0 w n (T n)" by simp
        from C have "\<not> (task_compatible_with_key I \<tau> k w n (T n) \<and>
                           task_compatible_with_key I \<tau> k0 w n (T n))"
          unfolding key_task_conflict_def by blast
        with Ck C0 show ?thesis by blast
      qed
    qed
  next
    show "{k0} \<subseteq> K \<inter> ?E"
      using k0 adm[OF k0] comp0 Tn by auto
  qed
  have
    "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n = card (K \<inter> ?E) / card K"
    unfolding key_conditioned_success_prob_def
    by (subst measure_pmf_of_set[of K ?E]) (use finK nonemptyK in auto)
  also have "\<dots> = 1 / card K"
    using Eeq nonemptyK by simp
  finally show ?thesis .
qed

theorem pairwise_conflict_prior_bound:
  assumes finD: "finite (set_pmf D)"
    and adm: "\<And>k. k \<in> set_pmf D \<Longrightarrow> utterance_admissible I k w n"
    and PW: "pairwise_key_conflict_on I \<tau> w n (set_pmf D)"
  shows "key_conditioned_success_prob D I \<tau> T w n \<le> max_supported_key_mass D"
proof -
  let ?E = "{k. utterance_admissible I k w n \<and> task_compatible_with_key I \<tau> k w n (T n)}"
  let ?A = "set_pmf D \<inter> ?E"
  have card_le: "card ?A \<le> 1"
    by (rule pairwise_conflict_event_card_le1[OF finD PW])
  have finA: "finite ?A"
    using finD by simp
  from finite_card_le1_cases[OF finA card_le]
  show ?thesis
  proof
    assume "?A = {}"
    then have Eempty: "?E \<inter> set_pmf D = {}" by auto
    have ProbInt: "measure_pmf.prob D (?E \<inter> set_pmf D) = measure_pmf.prob D ?E"
      by (simp add: measure_Int_set_pmf)
    then have "measure_pmf.prob D ?E = measure_pmf.prob D (?E \<inter> set_pmf D)"
      by simp
    also have "\<dots> = 0"
      using Eempty by (simp add: measure_measure_pmf_finite)
    finally have Prob0: "measure_pmf.prob D ?E = 0" .
    have "key_conditioned_success_prob D I \<tau> T w n = measure_pmf.prob D ?E"
      unfolding key_conditioned_success_prob_def by simp
    also have "\<dots> = 0"
      by (rule Prob0)
    finally have "key_conditioned_success_prob D I \<tau> T w n = 0" .
    moreover have "0 \<le> max_supported_key_mass D"
    proof -
      obtain k where kS: "k \<in> set_pmf D"
        using set_pmf_not_empty[of D] by blast
      have "0 \<le> pmf D k" by simp
      also have "\<dots> \<le> max_supported_key_mass D"
        by (rule max_supported_key_mass_ge[OF finD kS])
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  next
    assume "\<exists>a. ?A = {a}"
    then obtain a where Aeq: "?A = {a}" by blast
    have aS: "a \<in> set_pmf D"
      using Aeq by auto
    have Eone: "?E \<inter> set_pmf D = {a}"
      using Aeq by auto
    have ProbInt: "measure_pmf.prob D (?E \<inter> set_pmf D) = measure_pmf.prob D ?E"
      by (simp add: measure_Int_set_pmf)
    then have "measure_pmf.prob D ?E = measure_pmf.prob D (?E \<inter> set_pmf D)"
      by simp
    also have "\<dots> = measure_pmf.prob D {a}"
      using Eone by simp
    also have "\<dots> = pmf D a"
      by (simp add: measure_measure_pmf_finite)
    also have "\<dots> \<le> max_supported_key_mass D"
      by (rule max_supported_key_mass_ge[OF finD aS])
    finally show ?thesis
      unfolding key_conditioned_success_prob_def by simp
  qed
qed

theorem pairwise_conflict_prior_tight:
  assumes finD: "finite (set_pmf D)"
    and adm: "\<And>k. k \<in> set_pmf D \<Longrightarrow> utterance_admissible I k w n"
    and PW: "pairwise_key_conflict_on I \<tau> w n (set_pmf D)"
    and k0: "k0 \<in> set_pmf D"
    and max0: "pmf D k0 = max_supported_key_mass D"
    and comp0: "task_compatible_with_key I \<tau> k0 w n t0"
    and Tn: "T n = t0"
  shows "key_conditioned_success_prob D I \<tau> T w n = max_supported_key_mass D"
proof -
  let ?E = "{k. utterance_admissible I k w n \<and> task_compatible_with_key I \<tau> k w n (T n)}"
  have Eeq: "set_pmf D \<inter> ?E = {k0}"
  proof
    show "set_pmf D \<inter> ?E \<subseteq> {k0}"
    proof
      fix k
      assume kE: "k \<in> set_pmf D \<inter> ?E"
      show "k \<in> {k0}"
      proof (cases "k = k0")
        case True
        then show ?thesis by simp
      next
        case False
        from PW kE k0 False have C: "key_task_conflict I \<tau> w n k k0"
          unfolding pairwise_key_conflict_on_def by blast
        from kE have Ck: "task_compatible_with_key I \<tau> k w n (T n)" by auto
        from comp0 Tn have C0: "task_compatible_with_key I \<tau> k0 w n (T n)" by simp
        from C have "\<not> (task_compatible_with_key I \<tau> k w n (T n) \<and>
                           task_compatible_with_key I \<tau> k0 w n (T n))"
          unfolding key_task_conflict_def by blast
        with Ck C0 show ?thesis by blast
      qed
    qed
  next
    show "{k0} \<subseteq> set_pmf D \<inter> ?E"
      using k0 adm[OF k0] comp0 Tn by auto
  qed
  have Eone: "?E \<inter> set_pmf D = {k0}"
    using Eeq by auto
  have ProbInt: "measure_pmf.prob D (?E \<inter> set_pmf D) = measure_pmf.prob D ?E"
    by (simp add: measure_Int_set_pmf)
  then have "measure_pmf.prob D ?E = measure_pmf.prob D (?E \<inter> set_pmf D)"
    by simp
  also have "\<dots> = measure_pmf.prob D {k0}"
    using Eone by simp
  also have "\<dots> = pmf D k0"
    by (simp add: measure_measure_pmf_finite)
  also have "\<dots> = max_supported_key_mass D"
    by (rule max0)
  finally show ?thesis
    unfolding key_conditioned_success_prob_def by simp
qed

datatype K_amb = KLeft | KRight
datatype N_amb = NAmb

definition I_amb :: "(K_amb, unit, N_amb, C_t, U_t) keyed_reg"
where
  "I_amb k w n c \<Gamma> \<phi> \<longleftrightarrow>
     w = () \<and> n = NAmb \<and> c = Ct \<and> \<Gamma> = {} \<and>
     ((k = KLeft \<and> \<phi> = Ua) \<or> (k = KRight \<and> \<phi> = Ub))"

lemma I_amb_left_admissible:
  "utterance_admissible I_amb KLeft () NAmb"
  unfolding utterance_admissible_def I_amb_def
  by (intro exI[of _ Ct] exI[of _ "{}"] exI[of _ Ua]) simp

lemma I_amb_right_admissible:
  "utterance_admissible I_amb KRight () NAmb"
  unfolding utterance_admissible_def I_amb_def
  by (intro exI[of _ Ct] exI[of _ "{}"] exI[of _ Ub]) simp

lemma I_amb_key_conflict:
  "key_task_conflict I_amb \<tau>_toy () NAmb KLeft KRight"
proof (unfold key_task_conflict_def, intro allI notI)
  fix t
  assume
    "task_compatible_with_key I_amb \<tau>_toy KLeft () NAmb t \<and>
     task_compatible_with_key I_amb \<tau>_toy KRight () NAmb t"
  then obtain c1 \<Gamma>1 \<phi>1 c2 \<Gamma>2 \<phi>2
    where L: "I_amb KLeft () NAmb c1 \<Gamma>1 \<phi>1"
      and Lt: "t = formal_task_of \<tau>_toy c1 \<Gamma>1 \<phi>1"
      and R: "I_amb KRight () NAmb c2 \<Gamma>2 \<phi>2"
      and Rt: "t = formal_task_of \<tau>_toy c2 \<Gamma>2 \<phi>2"
    unfolding task_compatible_with_key_def by blast
  from L have c1: "c1 = Ct" and g1: "\<Gamma>1 = {}" and p1: "\<phi>1 = Ua"
    unfolding I_amb_def by simp_all
  from R have c2: "c2 = Ct" and g2: "\<Gamma>2 = {}" and p2: "\<phi>2 = Ub"
    unfolding I_amb_def by simp_all
  from Lt Rt c1 g1 p1 c2 g2 p2 have "\<tau>_toy Ua = \<tau>_toy Ub"
    unfolding formal_task_of_def by simp
  then show False by simp
qed

definition key_revealed_task_translator_on ::
  "('k,'w,'n,'c,'u) keyed_reg \<Rightarrow>
   ('u,'f) trans \<Rightarrow> ('k \<Rightarrow> ('c,'f) formal_task) \<Rightarrow> 'w \<Rightarrow> 'n \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "key_revealed_task_translator_on I \<tau> T w n K \<longleftrightarrow>
     (\<forall>k\<in>K. utterance_admissible I k w n \<longrightarrow> task_compatible_with_key I \<tau> k w n (T k))"

lemma key_task_conflict_sym:
  "key_task_conflict I \<tau> w n k1 k2 \<longleftrightarrow> key_task_conflict I \<tau> w n k2 k1"
  unfolding key_task_conflict_def by blast

locale ambiguous_nl_source =
  fixes I :: "('k,'w,'n,'c,'u) keyed_reg"
    and \<tau> :: "('u,'f) trans"
    and w :: 'w
    and n :: 'n
    and K :: "'k set"
  assumes finite_keys: "finite K"
    and nonempty_keys: "K \<noteq> {}"
    and admissible_keys: "\<And>k. k \<in> K \<Longrightarrow> utterance_admissible I k w n"
    and pairwise_conflict: "pairwise_key_conflict_on I \<tau> w n K"
begin

lemma admissible_key_has_task:
  assumes "k \<in> K"
  shows "\<exists>t. task_compatible_with_key I \<tau> k w n t"
proof -
  from admissible_keys[OF assms]
  obtain c \<Gamma> \<phi> where "I k w n c \<Gamma> \<phi>"
    unfolding utterance_admissible_def by blast
  then show ?thesis
    unfolding task_compatible_with_key_def
    by (intro exI[of _ "formal_task_of \<tau> c \<Gamma> \<phi>"] exI[of _ c] exI[of _ "\<Gamma>"] exI[of _ "\<phi>"]) simp
qed

theorem single_shot_uniform_success_bound:
  "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
  by (rule pairwise_conflict_uniform_bound[OF finite_keys nonempty_keys admissible_keys pairwise_conflict])

theorem key_revealed_translation_on:
  "\<exists>T. key_revealed_task_translator_on I \<tau> T w n K"
proof -
  define T where "T k = (SOME t. task_compatible_with_key I \<tau> k w n t)" for k
  have "key_revealed_task_translator_on I \<tau> T w n K"
  proof (unfold key_revealed_task_translator_on_def, intro ballI impI)
    fix k
    assume "k \<in> K"
    then have "\<exists>t. task_compatible_with_key I \<tau> k w n t"
      by (rule admissible_key_has_task)
    then show "task_compatible_with_key I \<tau> k w n (T k)"
      unfolding T_def by (rule someI_ex)
  qed
  then show ?thesis by blast
qed

end

locale genuinely_ambiguous_nl_source =
  ambiguous_nl_source I \<tau> w n K
  for I :: "('k,'w,'n,'c,'u) keyed_reg"
    and \<tau> :: "('u,'f) trans"
    and w :: 'w
    and n :: 'n
    and K :: "'k set" +
  assumes at_least_two_keys: "2 \<le> card K"
begin

lemma distinct_keys:
  obtains k1 k2 where "k1 \<in> K" "k2 \<in> K" "k1 \<noteq> k2"
proof -
  have "\<exists>k1\<in>K. \<exists>k2\<in>K. k1 \<noteq> k2"
  proof (rule ccontr)
    assume H: "\<not> (\<exists>k1\<in>K. \<exists>k2\<in>K. k1 \<noteq> k2)"
    have all_eq: "\<forall>k1\<in>K. \<forall>k2\<in>K. k1 = k2"
      using H by blast
    have "card K \<le> 1"
    proof (cases "K = {}")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain a where aK: "a \<in> K" by blast
      have "K = {a}"
        using all_eq aK by blast
      then show ?thesis by simp
    qed
    with at_least_two_keys show False by simp
  qed
  then obtain k1 k2 where "k1 \<in> K" "k2 \<in> K" "k1 \<noteq> k2" by blast
  then show thesis by (rule that)
qed

theorem no_single_shot_translation_on:
  "\<not> (\<exists>T. single_shot_task_translator I \<tau> T w)"
proof -
  obtain k1 k2 where k1: "k1 \<in> K" and k2: "k2 \<in> K" and neq: "k1 \<noteq> k2"
    by (rule distinct_keys)
  from pairwise_conflict k1 k2 neq
  have C: "key_task_conflict I \<tau> w n k1 k2"
    unfolding pairwise_key_conflict_on_def by blast
  show ?thesis
    by (rule conflicting_keys_refute_single_shot_existence[OF admissible_keys[OF k1] admissible_keys[OF k2] C])
qed

theorem single_shot_uniform_success_strict_lt_one:
  "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n < 1"
proof -
  have "key_conditioned_success_prob (pmf_of_set K) I \<tau> T w n \<le> 1 / card K"
    by (rule single_shot_uniform_success_bound)
  moreover have "(1 / card K :: real) \<le> 1 / 2"
  proof -
    have cpos: "(0 :: real) < card K"
      using at_least_two_keys by simp
    have "(1 / card K :: real) \<le> 1 / 2 \<longleftrightarrow> 2 \<le> card K"
      using cpos by (simp add: field_simps)
    then show ?thesis
      using at_least_two_keys by simp
  qed
  moreover have "(1 / 2 :: real) < 1" by simp
  ultimately show ?thesis by linarith
qed

end

definition W_amb :: unit
where
  "W_amb = ()"

definition K_amb_set :: "K_amb set"
where
  "K_amb_set = {KLeft, KRight}"

interpretation amb_substantive_source:
  genuinely_ambiguous_nl_source I_amb \<tau>_toy W_amb NAmb K_amb_set
proof
  show "finite K_amb_set"
    unfolding K_amb_set_def by simp
  show "K_amb_set \<noteq> {}"
    unfolding K_amb_set_def by simp
  show "\<And>k. k \<in> K_amb_set \<Longrightarrow> utterance_admissible I_amb k W_amb NAmb"
    unfolding K_amb_set_def W_amb_def
    using I_amb_left_admissible I_amb_right_admissible by auto
  show "pairwise_key_conflict_on I_amb \<tau>_toy W_amb NAmb K_amb_set"
  proof (unfold pairwise_key_conflict_on_def, intro ballI impI)
    fix k1 k2
    assume "k1 \<in> K_amb_set" "k2 \<in> K_amb_set" "k1 \<noteq> k2"
    then show "key_task_conflict I_amb \<tau>_toy W_amb NAmb k1 k2"
    proof (unfold K_amb_set_def W_amb_def)
      assume H: "k1 \<in> {KLeft, KRight}" "k2 \<in> {KLeft, KRight}" "k1 \<noteq> k2"
      then have Cases:
        "(k1 = KLeft \<and> k2 = KRight) \<or> (k1 = KRight \<and> k2 = KLeft)"
        by auto
      then show "key_task_conflict I_amb \<tau>_toy () NAmb k1 k2"
      proof
        assume "k1 = KLeft \<and> k2 = KRight"
        then show ?thesis
          using I_amb_key_conflict by simp
      next
        assume "k1 = KRight \<and> k2 = KLeft"
        moreover have "key_task_conflict I_amb \<tau>_toy () NAmb KRight KLeft"
          using I_amb_key_conflict by (simp add: key_task_conflict_sym)
        ultimately show ?thesis by simp
      qed
    qed
  qed
  show "2 \<le> card K_amb_set"
    unfolding K_amb_set_def by simp
qed

theorem I_amb_substantive_no_single_shot_translation:
  "\<not> (\<exists>T. single_shot_task_translator I_amb \<tau>_toy T ())"
  using amb_substantive_source.no_single_shot_translation_on
  unfolding W_amb_def K_amb_set_def by simp

theorem I_amb_substantive_binary_success_le_half:
  "key_conditioned_success_prob (pmf_of_set {KLeft, KRight}) I_amb \<tau>_toy T () NAmb \<le> 1 / 2"
proof -
  have "key_conditioned_success_prob (pmf_of_set {KLeft, KRight}) I_amb \<tau>_toy T () NAmb \<le> 1 / card {KLeft, KRight}"
    using amb_substantive_source.single_shot_uniform_success_bound
    unfolding W_amb_def K_amb_set_def by simp
  then show ?thesis by simp
qed

theorem I_amb_substantive_binary_success_lt_one:
  "key_conditioned_success_prob (pmf_of_set {KLeft, KRight}) I_amb \<tau>_toy T () NAmb < 1"
  using amb_substantive_source.single_shot_uniform_success_strict_lt_one
  unfolding W_amb_def K_amb_set_def by simp

theorem I_amb_substantive_key_revealed_translation:
  "\<exists>T. key_revealed_task_translator_on I_amb \<tau>_toy T () NAmb {KLeft, KRight}"
  using amb_substantive_source.key_revealed_translation_on
  unfolding W_amb_def K_amb_set_def by simp

end
