theory Step1_Foundation
  imports Main "HOL-Probability.Probability_Mass_Function" "HOL-Eisbach.Eisbach"
begin

section \<open>Abstract scaffold\<close>

text \<open>
  Typed scaffold separating regimentation, probabilistic generation,
  formal derivability and checking, and modal operators.
\<close>

record ('w,'c,'f,'p) formal_system =
  f_derives :: "'w \<Rightarrow> 'c \<Rightarrow> 'f set \<Rightarrow> 'f \<Rightarrow> bool"
  f_prefers :: "'w \<Rightarrow> 'c \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  f_check   :: "'w \<Rightarrow> 'p \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool"

record ('w,'c,'u,'p) stochastic_agent =
  a_derives :: "'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> bool"
  a_prefers :: "'w \<Rightarrow> 'c \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  a_gen     :: "'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> 'p pmf"

type_synonym ('u,'f) trans = "'u \<Rightarrow> 'f"

consts reg :: "'w \<Rightarrow> 'n \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> bool"

section \<open>Natural-language side\<close>

definition interpretively_flexible ::
  "('w \<Rightarrow> 'n \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> bool) \<Rightarrow> 'n \<Rightarrow> 'w \<Rightarrow> bool"
where
  "interpretively_flexible I n w \<longleftrightarrow>
     (\<exists>c1 \<Gamma>1 \<phi>1 c2 \<Gamma>2 \<phi>2.
        I w n c1 \<Gamma>1 \<phi>1 \<and> I w n c2 \<Gamma>2 \<phi>2 \<and>
        (c1 \<noteq> c2 \<or> \<Gamma>1 \<noteq> \<Gamma>2 \<or> \<phi>1 \<noteq> \<phi>2))"

definition determinate_regimentation ::
  "('w \<Rightarrow> 'n \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> bool) \<Rightarrow> 'n \<Rightarrow> 'w \<Rightarrow> bool"
where
  "determinate_regimentation I n w \<longleftrightarrow>
     (\<exists>c \<Gamma> \<phi>. I w n c \<Gamma> \<phi>) \<and>
     (\<forall>c1 \<Gamma>1 \<phi>1 c2 \<Gamma>2 \<phi>2.
        I w n c1 \<Gamma>1 \<phi>1 \<longrightarrow> I w n c2 \<Gamma>2 \<phi>2 \<longrightarrow>
        c1 = c2 \<and> \<Gamma>1 = \<Gamma>2 \<and> \<phi>1 = \<phi>2)"

lemma determinate_imp_not_flexible:
  assumes "determinate_regimentation I n w"
  shows "\<not> interpretively_flexible I n w"
  using assms unfolding determinate_regimentation_def interpretively_flexible_def by blast

section \<open>Translation relations\<close>

definition tr0 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "tr0 A F \<tau> w \<longleftrightarrow>
     (\<forall>c \<phi>. a_derives A w c {} \<phi> \<longleftrightarrow> f_derives F w c {} (\<tau> \<phi>))"

lemma tr0_forward:
  assumes "tr0 A F \<tau> w" "a_derives A w c {} \<phi>"
  shows "f_derives F w c {} (\<tau> \<phi>)"
  using assms unfolding tr0_def by blast

lemma tr0_backward:
  assumes "tr0 A F \<tau> w" "f_derives F w c {} (\<tau> \<phi>)"
  shows "a_derives A w c {} \<phi>"
  using assms unfolding tr0_def by blast

definition tr1 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> bool"
where
  "tr1 A F \<tau> w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. a_derives A w c \<Gamma> \<phi> \<longleftrightarrow> f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>))"

definition tr2 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> 'w \<Rightarrow> bool"
where
  "tr2 A F \<tau> \<Theta> w \<longleftrightarrow>
     tr1 A F \<tau> w \<and>
     inj \<Theta> \<and>
     (\<forall>c \<pi>1 \<pi>2.
        a_prefers A w c \<pi>1 \<pi>2 \<longleftrightarrow> f_prefers F w c (\<Theta> \<pi>1) (\<Theta> \<pi>2))"

definition proc_translatable ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow> 'w \<Rightarrow> bool"
where
  "proc_translatable A F w \<longleftrightarrow> (\<exists>\<tau> \<Theta>. tr2 A F \<tau> \<Theta> w)"

lemma proc_translatable_witness:
  assumes "proc_translatable A F w"
  obtains \<tau> \<Theta> where "tr2 A F \<tau> \<Theta> w"
  using assms unfolding proc_translatable_def by blast

lemma proc_translatable_intro:
  assumes "tr2 A F \<tau> \<Theta> w"
  shows "proc_translatable A F w"
  unfolding proc_translatable_def using assms by blast

definition TI2 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   (('w,'c,'f,'p) formal_system) set \<Rightarrow> 'w \<Rightarrow> bool"
where
  "TI2 A Fs w \<longleftrightarrow> (\<forall>F\<in>Fs. \<not> proc_translatable A F w)"

lemma tr1_forward:
  assumes "tr1 A F \<tau> w" "a_derives A w c \<Gamma> \<phi>"
  shows "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
  using assms unfolding tr1_def by blast

lemma tr1_backward:
  assumes "tr1 A F \<tau> w" "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
  shows "a_derives A w c \<Gamma> \<phi>"
  using assms unfolding tr1_def by blast

lemma tr1_imp_tr0:
  assumes "tr1 A F \<tau> w"
  shows "tr0 A F \<tau> w"
  using assms unfolding tr1_def tr0_def by simp

lemma tr2_imp_tr1:
  assumes "tr2 A F \<tau> \<Theta> w"
  shows "tr1 A F \<tau> w"
  using assms unfolding tr2_def by blast

lemma tr2_imp_inj:
  assumes "tr2 A F \<tau> \<Theta> w"
  shows "inj \<Theta>"
  using assms unfolding tr2_def by blast

lemma tr2_pref_forward:
  assumes "tr2 A F \<tau> \<Theta> w" "a_prefers A w c \<pi>1 \<pi>2"
  shows "f_prefers F w c (\<Theta> \<pi>1) (\<Theta> \<pi>2)"
  using assms unfolding tr2_def by blast

lemma tr2_pref_backward:
  assumes "tr2 A F \<tau> \<Theta> w" "f_prefers F w c (\<Theta> \<pi>1) (\<Theta> \<pi>2)"
  shows "a_prefers A w c \<pi>1 \<pi>2"
  using assms unfolding tr2_def by blast

lemma tr2_pref_iff:
  assumes "tr2 A F \<tau> \<Theta> w"
  shows "a_prefers A w c \<pi>1 \<pi>2 \<longleftrightarrow> f_prefers F w c (\<Theta> \<pi>1) (\<Theta> \<pi>2)"
  using assms unfolding tr2_def by blast

lemma tr2_decompose:
  "tr2 A F \<tau> \<Theta> w \<longleftrightarrow>
   tr1 A F \<tau> w \<and> inj \<Theta> \<and>
   (\<forall>c \<pi>1 \<pi>2. a_prefers A w c \<pi>1 \<pi>2 \<longleftrightarrow> f_prefers F w c (\<Theta> \<pi>1) (\<Theta> \<pi>2))"
  unfolding tr2_def by auto

lemma TI2_member:
  assumes "TI2 A Fs w" "F \<in> Fs"
  shows "\<not> proc_translatable A F w"
  using assms unfolding TI2_def by blast

lemma TI2_antimono:
  assumes "TI2 A Fs' w" "Fs \<subseteq> Fs'"
  shows "TI2 A Fs w"
  using assms unfolding TI2_def by blast

lemma TI2_intro:
  assumes "\<And>F. F \<in> Fs \<Longrightarrow> \<not> proc_translatable A F w"
  shows "TI2 A Fs w"
  unfolding TI2_def using assms by blast

lemma TI2_empty_system: "TI2 A {} w"
  unfolding TI2_def by simp

lemma TI2_iff:
  "TI2 A Fs w \<longleftrightarrow> (\<forall>F\<in>Fs. \<not> proc_translatable A F w)"
  unfolding TI2_def by simp

lemma proc_translatable_imp_not_TI2:
  assumes "proc_translatable A F w" "F \<in> Fs"
  shows "\<not> TI2 A Fs w"
  using assms unfolding TI2_def by blast

section \<open>Human-likeness\<close>

definition HL0 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> bool"
where
  "HL0 A H w \<longleftrightarrow>
     (\<forall>c \<phi>. a_derives A w c {} \<phi> \<longleftrightarrow> a_derives H w c {} \<phi>)"

definition HL1 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> bool"
where
  "HL1 A H w \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. a_derives A w c \<Gamma> \<phi> \<longleftrightarrow> a_derives H w c \<Gamma> \<phi>)"

definition HL2 ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> bool"
where
  "HL2 A H w \<longleftrightarrow>
     HL1 A H w \<and>
     (\<exists>\<Xi>. inj \<Xi> \<and> (\<forall>c \<pi>1 \<pi>2.
         a_prefers H w c \<pi>1 \<pi>2 \<longleftrightarrow> a_prefers A w c (\<Xi> \<pi>1) (\<Xi> \<pi>2)))"

lemma HL2_imp_HL1:
  assumes "HL2 A H w"
  shows "HL1 A H w"
  using assms unfolding HL2_def by blast

lemma HL1_imp_HL0:
  assumes "HL1 A H w"
  shows "HL0 A H w"
  using assms unfolding HL1_def HL0_def by blast

lemma HL2_imp_HL0:
  assumes "HL2 A H w"
  shows "HL0 A H w"
  using HL1_imp_HL0[OF HL2_imp_HL1[OF assms]] .

section \<open>Probabilistic search + formal checking\<close>

definition success_prob ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow>
   'w \<Rightarrow> 'c \<Rightarrow> 'u set \<Rightarrow> 'u \<Rightarrow> real"
where
  "success_prob A F \<tau> w c \<Gamma> \<phi> =
     measure_pmf.prob (a_gen A w c \<Gamma> \<phi>) {\<pi>. f_check F w \<pi> c (\<tau> \<phi>)}"

lemma success_prob_nonneg: "0 \<le> success_prob A F \<tau> w c \<Gamma> \<phi>"
  unfolding success_prob_def by simp

lemma success_prob_le1: "success_prob A F \<tau> w c \<Gamma> \<phi> \<le> 1"
  unfolding success_prob_def by simp

section \<open>Named theorem bundles\<close>

named_theorems tr_simps "Translation relation simplification rules"
declare tr0_def [tr_simps] tr1_def [tr_simps] tr2_def [tr_simps]
        proc_translatable_def [tr_simps] TI2_def [tr_simps]

method tr_unfold = (simp only: tr_simps)

section \<open>Modal overlay\<close>

typedecl i

type_synonym \<sigma> = "i \<Rightarrow> bool"

consts R :: "i \<Rightarrow> i \<Rightarrow> bool"

definition mbox :: "\<sigma> \<Rightarrow> \<sigma>"
where
  "mbox P = (\<lambda>w. \<forall>v. R w v \<longrightarrow> P v)"

definition mdia :: "\<sigma> \<Rightarrow> \<sigma>"
where
  "mdia P = (\<lambda>w. \<exists>v. R w v \<and> P v)"

definition mvalid :: "\<sigma> \<Rightarrow> bool"
where
  "mvalid P \<longleftrightarrow> (\<forall>w. P w)"

lemma mbox_K:
  assumes "mbox (\<lambda>w. P w \<longrightarrow> Q w) w" "mbox P w"
  shows "mbox Q w"
  using assms unfolding mbox_def by blast

lemma mbox_mono:
  assumes "\<And>w. P w \<Longrightarrow> Q w" "mbox P w"
  shows "mbox Q w"
  using assms unfolding mbox_def by blast

lemma mbox_conj:
  assumes "mbox P w" "mbox Q w"
  shows "mbox (\<lambda>w. P w \<and> Q w) w"
  using assms unfolding mbox_def by blast

lemma mdia_dual:
  "mdia P w \<longleftrightarrow> \<not> mbox (\<lambda>w. \<not> P w) w"
  unfolding mdia_def mbox_def by blast

lemma mdia_witness:
  assumes "mdia P w"
  obtains v where "R w v" "P v"
  using assms unfolding mdia_def by blast

lemma mdia_mono:
  assumes "\<And>w. P w \<Longrightarrow> Q w" "mdia P w"
  shows "mdia Q w"
  using assms unfolding mdia_def by blast

lemma mbox_imp:
  assumes "mbox (\<lambda>w. P w \<longrightarrow> Q w) w" "P v" "R w v"
  shows "Q v"
  using assms unfolding mbox_def by blast

lemma mvalid_mbox:
  assumes "mvalid P"
  shows "mbox P w"
  using assms unfolding mvalid_def mbox_def by blast

lemma mvalid_imp:
  assumes "mvalid (\<lambda>w. P w \<longrightarrow> Q w)" "mvalid P"
  shows "mvalid Q"
  using assms unfolding mvalid_def by blast

lemma mvalid_conj:
  assumes "mvalid P" "mvalid Q"
  shows "mvalid (\<lambda>w. P w \<and> Q w)"
  using assms unfolding mvalid_def by blast

lemma mvalid_disj_left:
  assumes "mvalid P"
  shows "mvalid (\<lambda>w. P w \<or> Q w)"
  using assms unfolding mvalid_def by blast

locale S4_frame =
  assumes R_refl: "\<And>w. R w w"
    and R_trans: "\<And>w u v. R w u \<Longrightarrow> R u v \<Longrightarrow> R w v"
begin

lemma mbox_T:
  assumes "mbox P w"
  shows "P w"
  using assms R_refl unfolding mbox_def by blast

lemma mbox_4:
  assumes "mbox P w"
  shows "mbox (mbox P) w"
  using assms R_trans unfolding mbox_def by blast

lemma mdia_refl:
  assumes "P w"
  shows "mdia P w"
  using assms R_refl unfolding mdia_def by blast

lemma mbox_mdia:
  assumes "mbox P w"
  shows "\<not> mdia (\<lambda>w. \<not> P w) w"
  using assms unfolding mbox_def mdia_def by blast

lemma mvalid_imp_mbox_everywhere:
  assumes "mvalid P"
  shows "mbox P w"
  using assms unfolding mvalid_def mbox_def by blast

end

definition Nec_TI2 ::
  "(i,'c,'u,'p) stochastic_agent \<Rightarrow>
   ((i,'c,'f,'p) formal_system) set \<Rightarrow> \<sigma>"
where
  "Nec_TI2 H Fs = mbox (TI2 H Fs)"

definition Poss_HL2 ::
  "(i,'c,'u,'p) stochastic_agent \<Rightarrow>
   (i,'c,'u,'p) stochastic_agent \<Rightarrow> \<sigma>"
where
  "Poss_HL2 A H = mdia (HL2 A H)"

section \<open>Decomposed locale hierarchy: monotone and nonmonotone systems\<close>

locale monotone_derivation =
  fixes F :: "('w,'c,'f,'p) formal_system"
  assumes mono: "\<And>w c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
begin

lemma mono_superset:
  assumes "f_derives F w c \<Gamma> \<psi>" "\<Gamma> \<subseteq> \<Gamma>'"
  shows "f_derives F w c \<Gamma>' \<psi>"
proof -
  from mono[OF assms(1), of \<Gamma>']
  have "f_derives F w c (\<Gamma> \<union> \<Gamma>') \<psi>" .
  moreover from assms(2) have "\<Gamma> \<union> \<Gamma>' = \<Gamma>'" by blast
  ultimately show ?thesis by simp
qed

lemma mono_empty_premise:
  assumes "f_derives F w c {} \<psi>"
  shows "f_derives F w c \<Gamma> \<psi>"
  using mono[OF assms] by simp

end

locale nonmonotone_derivation =
  fixes H :: "('w,'c,'u,'p) stochastic_agent"
  assumes nonmono: "\<exists>w c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
begin

lemma not_universally_monotone:
  "\<not> (\<forall>w c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<longrightarrow> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>)"
  using nonmono by blast

end

section \<open>Key structural lemma: monotonicity transfer via tr1\<close>

lemma tr1_transfers_monotonicity:
  assumes "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and "tr1 H F \<tau> w"
    and "a_derives H w c \<Gamma> \<phi>"
  shows "a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
proof -
  from assms(2,3) have "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
    unfolding tr1_def by blast
  from assms(1)[OF this] have "f_derives F w c ((\<tau> ` \<Gamma>) \<union> (\<tau> ` \<Delta>)) (\<tau> \<phi>)" .
  moreover have "(\<tau> ` \<Gamma>) \<union> (\<tau> ` \<Delta>) = \<tau> ` (\<Gamma> \<union> \<Delta>)" by blast
  ultimately have "f_derives F w c (\<tau> ` (\<Gamma> \<union> \<Delta>)) (\<tau> \<phi>)" by simp
  with assms(2) show ?thesis unfolding tr1_def by blast
qed

section \<open>A genuine impossibility schema\<close>

locale monotone_vs_nonmonotone =
  fixes H :: "('w,'c,'u,'p) stochastic_agent"
    and F :: "('w,'c,'f,'p) formal_system"
    and \<tau> :: "('u,'f) trans"
  assumes mono_F:
    "\<And>w c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
  assumes nonmono_H:
    "\<exists>w c \<Gamma> \<Delta> \<phi>. a_derives H w c \<Gamma> \<phi> \<and> \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
begin

sublocale mono: monotone_derivation F
  by unfold_locales (rule mono_F)

sublocale nonmono: nonmonotone_derivation H
  by unfold_locales (rule nonmono_H)

theorem no_global_tr1:
  shows "\<not> (\<forall>w. tr1 H F \<tau> w)"
proof
  assume all_tr1: "\<forall>w. tr1 H F \<tau> w"
  from nonmono_H obtain w c \<Gamma> \<Delta> \<phi>
    where H_pos: "a_derives H w c \<Gamma> \<phi>"
      and H_neg: "\<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    by blast
  have mono_w: "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    using mono_F by blast
  from tr1_transfers_monotonicity[OF mono_w all_tr1[rule_format] H_pos]
  have "a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>" .
  with H_neg show False by contradiction
qed

end

section \<open>Bridge theorem: TI2 blocks HL2 once the bridge principle is assumed\<close>

proposition anti_ai_schema:
  fixes A :: "(i,'c,'u,'p) stochastic_agent"
    and H :: "(i,'c,'u,'p) stochastic_agent"
    and Fs :: "((i,'c,'f,'p) formal_system) set"
  assumes TI: "mvalid (TI2 H Fs)"
  assumes Bridge:
    "mvalid (\<lambda>w. HL2 A H w \<longrightarrow> (\<exists>F\<in>Fs. proc_translatable H F w))"
  shows "mvalid (\<lambda>w. \<not> HL2 A H w)"
proof (unfold mvalid_def, intro allI)
  fix w
  show "\<not> HL2 A H w"
  proof
    assume H2: "HL2 A H w"
    from Bridge have B:
      "HL2 A H w \<longrightarrow> (\<exists>F\<in>Fs. proc_translatable H F w)"
      unfolding mvalid_def by blast
    from B H2 obtain F where Fmem: "F \<in> Fs" and FT: "proc_translatable H F w"
      by blast
    from TI have Tiw: "TI2 H Fs w"
      unfolding mvalid_def by blast
    from TI2_member[OF Tiw Fmem] FT show False by contradiction
  qed
qed

corollary anti_ai_excludes_Poss_HL2:
  fixes A :: "(i,'c,'u,'p) stochastic_agent"
    and H :: "(i,'c,'u,'p) stochastic_agent"
    and Fs :: "((i,'c,'f,'p) formal_system) set"
  assumes "mvalid (TI2 H Fs)"
    and "mvalid (\<lambda>w. HL2 A H w \<longrightarrow> (\<exists>F\<in>Fs. proc_translatable H F w))"
  shows "\<not> Poss_HL2 A H w"
proof -
  from anti_ai_schema[OF assms] have "mvalid (\<lambda>w. \<not> HL2 A H w)" .
  then have "\<forall>v. \<not> HL2 A H v" unfolding mvalid_def by blast
  then show ?thesis unfolding Poss_HL2_def mdia_def by blast
qed

section \<open>Toy model witnessing satisfiability of the mismatch locale\<close>

datatype W_t = Wt
datatype C_t = Ct
datatype U_t = Ua | Ub
datatype F_t = Fa | Fb
datatype P_t = P0

definition H_toy :: "(W_t,C_t,U_t,P_t) stochastic_agent"
where
  "H_toy =
     \<lparr> a_derives = (\<lambda>w c \<Gamma> \<phi>. \<Gamma> = {} \<and> \<phi> = Ua),
       a_prefers = (\<lambda>w c \<pi>1 \<pi>2. True),
       a_gen     = (\<lambda>w c \<Gamma> \<phi>. return_pmf P0) \<rparr>"

definition F_toy :: "(W_t,C_t,F_t,P_t) formal_system"
where
  "F_toy =
     \<lparr> f_derives = (\<lambda>w c \<Gamma> \<psi>. \<psi> = Fa),
       f_prefers = (\<lambda>w c \<pi>1 \<pi>2. True),
       f_check   = (\<lambda>w \<pi> c \<psi>. \<psi> = Fa) \<rparr>"

fun \<tau>_toy :: "U_t \<Rightarrow> F_t"
where
  "\<tau>_toy Ua = Fa"
| "\<tau>_toy Ub = Fb"

lemma mono_F_toy:
  "\<And>w c \<Gamma> \<Delta> \<psi>. f_derives F_toy w c \<Gamma> \<psi> \<Longrightarrow> f_derives F_toy w c (\<Gamma> \<union> \<Delta>) \<psi>"
  unfolding F_toy_def by simp

lemma nonmono_H_toy:
  "\<exists>w c \<Gamma> \<Delta> \<phi>. a_derives H_toy w c \<Gamma> \<phi> \<and> \<not> a_derives H_toy w c (\<Gamma> \<union> \<Delta>) \<phi>"
  unfolding H_toy_def
  by (intro exI[of _ Wt] exI[of _ Ct] exI[of _ "{}"] exI[of _ "{Ua}"] exI[of _ Ua]) simp

interpretation toy: monotone_vs_nonmonotone H_toy F_toy \<tau>_toy
proof unfold_locales
  fix w c \<Gamma> \<Delta> \<psi>
  assume "f_derives F_toy w c \<Gamma> \<psi>"
  then show "f_derives F_toy w c (\<Gamma> \<union> \<Delta>) \<psi>"
    unfolding F_toy_def by simp
next
  show "\<exists>w c \<Gamma> \<Delta> \<phi>. a_derives H_toy w c \<Gamma> \<phi> \<and> \<not> a_derives H_toy w c (\<Gamma> \<union> \<Delta>) \<phi>"
    unfolding H_toy_def
    by (intro exI[of _ Wt] exI[of _ Ct] exI[of _ "{}"] exI[of _ "{Ua}"] exI[of _ Ua]) simp
qed

lemma not_global_tr1_toy:
  shows "\<not> (\<forall>w. tr1 H_toy F_toy \<tau>_toy w)"
  by (rule toy.no_global_tr1)

end
