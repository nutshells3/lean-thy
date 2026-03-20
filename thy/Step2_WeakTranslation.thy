theory Step2_WeakTranslation
  imports Step1_Foundation
begin

section \<open>Weaker translation notions on task slices\<close>

text \<open>
  Task-restricted exact translation notions. Exact bidirectional translation
  on a task family fails whenever that family contains a non-monotonic witness
  pair and the target derivability relation is monotone. Narrow safe slices
  may remain translatable.
\<close>

type_synonym ('c,'u) task = "'c \<times> 'u set \<times> 'u"

definition agent_derivable_support ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set"
where
  "agent_derivable_support H w = {(c,\<Gamma>,\<phi>). a_derives H w c \<Gamma> \<phi>}"

definition tr1_sound_on ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> bool"
where
  "tr1_sound_on H F \<tau> w Tasks \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> Tasks \<longrightarrow>
        (a_derives H w c \<Gamma> \<phi> \<longrightarrow> f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)))"

definition tr1_complete_on ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> bool"
where
  "tr1_complete_on H F \<tau> w Tasks \<longleftrightarrow>
     (\<forall>c \<Gamma> \<phi>. (c,\<Gamma>,\<phi>) \<in> Tasks \<longrightarrow>
        (f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>) \<longrightarrow> a_derives H w c \<Gamma> \<phi>))"

definition tr1_on ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow>
   ('u,'f) trans \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> bool"
where
  "tr1_on H F \<tau> w Tasks \<longleftrightarrow>
     tr1_sound_on H F \<tau> w Tasks \<and> tr1_complete_on H F \<tau> w Tasks"

definition task_restricted_translatable ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow>
   ('w,'c,'f,'p) formal_system \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> bool"
where
  "task_restricted_translatable H F w Tasks \<longleftrightarrow> (\<exists>\<tau>. tr1_on H F \<tau> w Tasks)"

definition contains_nonmono_witness_pair ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set \<Rightarrow> bool"
where
  "contains_nonmono_witness_pair H w Tasks \<longleftrightarrow>
     (\<exists>c \<Gamma> \<Delta> \<phi>.
        (c,\<Gamma>,\<phi>) \<in> Tasks \<and>
        (c,\<Gamma> \<union> \<Delta>,\<phi>) \<in> Tasks \<and>
        a_derives H w c \<Gamma> \<phi> \<and>
        \<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>)"

definition agent_support_contains_witness ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> bool"
where
  "agent_support_contains_witness H w \<longleftrightarrow>
     contains_nonmono_witness_pair H w (agent_derivable_support H w)"

definition agent_task_envelope ::
  "('w,'c,'u,'p) stochastic_agent \<Rightarrow> 'w \<Rightarrow> (('c,'u) task) set"
where
  "agent_task_envelope H w =
     {(c,\<Sigma>,\<phi>). \<exists>\<Gamma>. \<Gamma> \<subseteq> \<Sigma> \<and> a_derives H w c \<Gamma> \<phi>}"

lemma tr1_imp_sound_on:
  assumes "tr1 H F \<tau> w"
  shows "tr1_sound_on H F \<tau> w Tasks"
  using assms unfolding tr1_sound_on_def tr1_def by blast

lemma tr1_imp_complete_on:
  assumes "tr1 H F \<tau> w"
  shows "tr1_complete_on H F \<tau> w Tasks"
  using assms unfolding tr1_complete_on_def tr1_def by blast

lemma tr1_imp_tr1_on:
  assumes "tr1 H F \<tau> w"
  shows "tr1_on H F \<tau> w Tasks"
  using tr1_imp_sound_on[OF assms] tr1_imp_complete_on[OF assms]
  unfolding tr1_on_def by simp

lemma tr1_onD_sound:
  assumes "tr1_on H F \<tau> w Tasks"
  shows "tr1_sound_on H F \<tau> w Tasks"
  using assms unfolding tr1_on_def by simp

lemma tr1_onD_complete:
  assumes "tr1_on H F \<tau> w Tasks"
  shows "tr1_complete_on H F \<tau> w Tasks"
  using assms unfolding tr1_on_def by simp

lemma agent_derivable_support_excludes_nonmono_witness_pair:
  "\<not> contains_nonmono_witness_pair H w (agent_derivable_support H w)"
  unfolding contains_nonmono_witness_pair_def agent_derivable_support_def
  by blast

lemma agent_support_contains_witness_iff_false:
  "\<not> agent_support_contains_witness H w"
  unfolding agent_support_contains_witness_def
  by (rule agent_derivable_support_excludes_nonmono_witness_pair)

lemma derivable_task_in_agent_task_envelope:
  assumes "a_derives H w c \<Gamma> \<phi>"
  shows "(c,\<Gamma>,\<phi>) \<in> agent_task_envelope H w"
  using assms unfolding agent_task_envelope_def by blast

lemma witness_pair_lives_in_agent_task_envelope:
  assumes H1: "a_derives H w c \<Gamma> \<phi>"
    and H2: "\<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
  shows "contains_nonmono_witness_pair H w (agent_task_envelope H w)"
proof -
  have T1: "(c,\<Gamma>,\<phi>) \<in> agent_task_envelope H w"
    using H1 by (rule derivable_task_in_agent_task_envelope)
  have T2: "(c,\<Gamma> \<union> \<Delta>,\<phi>) \<in> agent_task_envelope H w"
    using H1 unfolding agent_task_envelope_def by blast
  show ?thesis
    unfolding contains_nonmono_witness_pair_def
    using T1 T2 H1 H2 by blast
qed

theorem nonmono_pair_blocks_tr1_on:
  assumes mono_F:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and S: "tr1_sound_on H F \<tau> w Tasks"
    and C: "tr1_complete_on H F \<tau> w Tasks"
    and W: "contains_nonmono_witness_pair H w Tasks"
  shows False
proof -
  obtain c \<Gamma> \<Delta> \<phi>
    where T1: "(c,\<Gamma>,\<phi>) \<in> Tasks"
      and T2: "(c,\<Gamma> \<union> \<Delta>,\<phi>) \<in> Tasks"
      and H1: "a_derives H w c \<Gamma> \<phi>"
      and H2: "\<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    using W unfolding contains_nonmono_witness_pair_def by blast
  from S T1 H1 have F1: "f_derives F w c (\<tau> ` \<Gamma>) (\<tau> \<phi>)"
    unfolding tr1_sound_on_def by blast
  from mono_F[OF F1, of "\<tau> ` \<Delta>"] have
    "f_derives F w c ((\<tau> ` \<Gamma>) \<union> (\<tau> ` \<Delta>)) (\<tau> \<phi>)" .
  hence F2: "f_derives F w c (\<tau> ` (\<Gamma> \<union> \<Delta>)) (\<tau> \<phi>)"
    by (simp add: image_Un)
  from C T2 F2 have "a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
    unfolding tr1_complete_on_def by blast
  with H2 show False by contradiction
qed

theorem nonmono_pair_blocks_task_restricted_translation:
  assumes mono_F:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and W: "contains_nonmono_witness_pair H w Tasks"
  shows "\<not> task_restricted_translatable H F w Tasks"
proof
  assume "task_restricted_translatable H F w Tasks"
  then obtain \<tau> where T: "tr1_on H F \<tau> w Tasks"
    unfolding task_restricted_translatable_def by blast
  from nonmono_pair_blocks_tr1_on[OF mono_F tr1_onD_sound[OF T] tr1_onD_complete[OF T] W]
  show False .
qed

theorem nonmono_pair_blocks_global_tr1:
  assumes mono_F:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and W: "contains_nonmono_witness_pair H w Tasks"
  shows "\<forall>\<tau>. \<not> tr1 H F \<tau> w"
proof (intro allI notI)
  fix \<tau>
  assume T: "tr1 H F \<tau> w"
  from nonmono_pair_blocks_tr1_on[OF mono_F tr1_imp_sound_on[OF T] tr1_imp_complete_on[OF T] W]
  show False .
qed

theorem nonmono_witness_blocks_envelope_translation:
  assumes mono_F:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F w c \<Gamma> \<psi> \<Longrightarrow> f_derives F w c (\<Gamma> \<union> \<Delta>) \<psi>"
    and H1: "a_derives H w c \<Gamma> \<phi>"
    and H2: "\<not> a_derives H w c (\<Gamma> \<union> \<Delta>) \<phi>"
  shows "\<not> task_restricted_translatable H F w (agent_task_envelope H w)"
proof -
  have W: "contains_nonmono_witness_pair H w (agent_task_envelope H w)"
    by (rule witness_pair_lives_in_agent_task_envelope[OF H1 H2])
  show ?thesis
    by (rule nonmono_pair_blocks_task_restricted_translation[OF mono_F W])
qed

section \<open>Concrete weak-translation witnesses\<close>

definition toy_nonmono_tasks :: "(C_t,U_t) task set"
where
  "toy_nonmono_tasks = {(Ct,{},Ua), (Ct,{Ua},Ua)}"

lemma toy_contains_nonmono_witness_pair:
  "contains_nonmono_witness_pair H_toy Wt toy_nonmono_tasks"
  unfolding contains_nonmono_witness_pair_def toy_nonmono_tasks_def H_toy_def
  by (intro exI[of _ Ct] exI[of _ "{}"] exI[of _ "{Ua}"] exI[of _ Ua]) auto

lemma toy_sound_on_nonmono_tasks:
  "tr1_sound_on H_toy F_toy \<tau>_toy Wt toy_nonmono_tasks"
  unfolding tr1_sound_on_def toy_nonmono_tasks_def H_toy_def F_toy_def
  by auto

lemma toy_not_complete_on_nonmono_tasks:
  "\<not> tr1_complete_on H_toy F_toy \<tau>_toy Wt toy_nonmono_tasks"
proof
  assume C: "tr1_complete_on H_toy F_toy \<tau>_toy Wt toy_nonmono_tasks"
  have "(Ct,{Ua},Ua) \<in> toy_nonmono_tasks"
    unfolding toy_nonmono_tasks_def by simp
  moreover have "f_derives F_toy Wt Ct (\<tau>_toy ` {Ua}) (\<tau>_toy Ua)"
    unfolding F_toy_def by simp
  ultimately have "a_derives H_toy Wt Ct {Ua} Ua"
    using C unfolding tr1_complete_on_def by blast
  thus False
    unfolding H_toy_def by simp
qed

theorem toy_nonmono_tasks_not_translatable:
  "\<not> task_restricted_translatable H_toy F_toy Wt toy_nonmono_tasks"
proof -
  have mono_Fw:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F_toy Wt c \<Gamma> \<psi> \<Longrightarrow> f_derives F_toy Wt c (\<Gamma> \<union> \<Delta>) \<psi>"
    unfolding F_toy_def by simp
  show ?thesis
    by (rule nonmono_pair_blocks_task_restricted_translation[OF mono_Fw toy_contains_nonmono_witness_pair])
qed

theorem toy_not_tr1_from_local_witness:
  "\<not> tr1 H_toy F_toy \<tau>_toy Wt"
proof
  assume "tr1 H_toy F_toy \<tau>_toy Wt"
  have mono_Fw:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F_toy Wt c \<Gamma> \<psi> \<Longrightarrow> f_derives F_toy Wt c (\<Gamma> \<union> \<Delta>) \<psi>"
    unfolding F_toy_def by simp
  from nonmono_pair_blocks_global_tr1[OF mono_Fw toy_contains_nonmono_witness_pair, rule_format, of \<tau>_toy]
  show False using \<open>tr1 H_toy F_toy \<tau>_toy Wt\<close> by contradiction
qed

lemma toy_support_has_no_witness:
  "\<not> agent_support_contains_witness H_toy Wt"
  by (rule agent_support_contains_witness_iff_false)

lemma toy_tr1_on_support:
  "tr1_on H_toy F_toy \<tau>_toy Wt (agent_derivable_support H_toy Wt)"
proof -
  have S: "agent_derivable_support H_toy Wt = {(Ct,{},Ua)}"
  proof
    show "agent_derivable_support H_toy Wt \<subseteq> {(Ct,{},Ua)}"
    proof
      fix x
      assume "x \<in> agent_derivable_support H_toy Wt"
      then obtain c \<Gamma> \<phi> where X: "x = (c,\<Gamma>,\<phi>)"
        and D: "a_derives H_toy Wt c \<Gamma> \<phi>"
        unfolding agent_derivable_support_def by auto
      from D have "\<Gamma> = {}" and "\<phi> = Ua"
        unfolding H_toy_def by simp_all
      moreover have "c = Ct"
        by (cases c) simp
      ultimately show "x \<in> {(Ct,{},Ua)}"
        using X by auto
    qed
  next
    show "{(Ct,{},Ua)} \<subseteq> agent_derivable_support H_toy Wt"
      unfolding agent_derivable_support_def H_toy_def by auto
  qed
  have Sound: "tr1_sound_on H_toy F_toy \<tau>_toy Wt (agent_derivable_support H_toy Wt)"
  proof (unfold tr1_sound_on_def, intro allI impI)
    fix c \<Gamma> \<phi>
    assume T: "(c,\<Gamma>,\<phi>) \<in> agent_derivable_support H_toy Wt"
      and H: "a_derives H_toy Wt c \<Gamma> \<phi>"
    from T S have "\<Gamma> = {}" "\<phi> = Ua"
      by auto
    moreover have "c = Ct"
      by (cases c) simp
    ultimately show "f_derives F_toy Wt c (\<tau>_toy ` \<Gamma>) (\<tau>_toy \<phi>)"
      unfolding F_toy_def by simp
  qed
  have Complete: "tr1_complete_on H_toy F_toy \<tau>_toy Wt (agent_derivable_support H_toy Wt)"
  proof (unfold tr1_complete_on_def, intro allI impI)
    fix c \<Gamma> \<phi>
    assume T: "(c,\<Gamma>,\<phi>) \<in> agent_derivable_support H_toy Wt"
      and F: "f_derives F_toy Wt c (\<tau>_toy ` \<Gamma>) (\<tau>_toy \<phi>)"
    from T S have "\<Gamma> = {}" "\<phi> = Ua"
      by auto
    moreover have "c = Ct"
      by (cases c) simp
    ultimately show "a_derives H_toy Wt c \<Gamma> \<phi>"
      unfolding H_toy_def by simp
  qed
  show ?thesis
    using Sound Complete unfolding tr1_on_def by simp
qed

theorem toy_support_is_translatable:
  "task_restricted_translatable H_toy F_toy Wt (agent_derivable_support H_toy Wt)"
  unfolding task_restricted_translatable_def
  using toy_tr1_on_support by blast

lemma toy_envelope_contains_nonmono_witness_pair:
  "contains_nonmono_witness_pair H_toy Wt (agent_task_envelope H_toy Wt)"
proof -
  have H1: "a_derives H_toy Wt Ct {} Ua"
    unfolding H_toy_def by simp
  have H2: "\<not> a_derives H_toy Wt Ct ({} \<union> {Ua}) Ua"
    unfolding H_toy_def by simp
  show ?thesis
    by (rule witness_pair_lives_in_agent_task_envelope[OF H1 H2])
qed

theorem toy_envelope_not_translatable:
  "\<not> task_restricted_translatable H_toy F_toy Wt (agent_task_envelope H_toy Wt)"
proof -
  have mono_Fw:
    "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F_toy Wt c \<Gamma> \<psi> \<Longrightarrow> f_derives F_toy Wt c (\<Gamma> \<union> \<Delta>) \<psi>"
    unfolding F_toy_def by simp
  show ?thesis
    by (rule nonmono_pair_blocks_task_restricted_translation[OF mono_Fw toy_envelope_contains_nonmono_witness_pair])
qed

theorem weak_translation_can_succeed_while_global_tr1_fails:
  "task_restricted_translatable H_toy F_toy Wt (agent_derivable_support H_toy Wt) \<and>
   \<not> task_restricted_translatable H_toy F_toy Wt toy_nonmono_tasks"
  using toy_support_is_translatable toy_nonmono_tasks_not_translatable by blast

theorem support_vs_envelope_boundary:
  "task_restricted_translatable H_toy F_toy Wt (agent_derivable_support H_toy Wt) \<and>
   \<not> task_restricted_translatable H_toy F_toy Wt (agent_task_envelope H_toy Wt)"
  using toy_support_is_translatable toy_envelope_not_translatable by blast

section \<open>Content-sensitive defeasible witness\<close>

datatype W_tw = Wtw
datatype C_tw = Ctw
datatype U_tw = UBird | UPenguin | UFlies
datatype F_tw = FBird | FPenguin | FFlies
datatype P_tw = Ptw

definition H_tweety :: "(W_tw,C_tw,U_tw,P_tw) stochastic_agent"
where
  "H_tweety =
     \<lparr> a_derives = (\<lambda>w c \<Gamma> \<phi>. \<phi> = UFlies \<and> UBird \<in> \<Gamma> \<and> UPenguin \<notin> \<Gamma>),
       a_prefers = (\<lambda>w c \<pi>1 \<pi>2. True),
       a_gen     = (\<lambda>w c \<Gamma> \<phi>. return_pmf Ptw) \<rparr>"

definition F_tweety :: "(W_tw,C_tw,F_tw,P_tw) formal_system"
where
  "F_tweety =
     \<lparr> f_derives = (\<lambda>w c \<Gamma> \<psi>. \<psi> = FFlies \<and> FBird \<in> \<Gamma>),
       f_prefers = (\<lambda>w c \<pi>1 \<pi>2. True),
       f_check   = (\<lambda>w \<pi> c \<psi>. \<psi> = FFlies) \<rparr>"

fun \<tau>_tweety :: "U_tw \<Rightarrow> F_tw"
where
  "\<tau>_tweety UBird = FBird"
| "\<tau>_tweety UPenguin = FPenguin"
| "\<tau>_tweety UFlies = FFlies"

lemma mono_F_tweety:
  "\<And>c \<Gamma> \<Delta> \<psi>. f_derives F_tweety Wtw c \<Gamma> \<psi> \<Longrightarrow> f_derives F_tweety Wtw c (\<Gamma> \<union> \<Delta>) \<psi>"
  unfolding F_tweety_def by auto

definition tweety_nonmono_tasks :: "(C_tw,U_tw) task set"
where
  "tweety_nonmono_tasks = {(Ctw,{UBird},UFlies), (Ctw,{UBird,UPenguin},UFlies)}"

lemma tweety_contains_nonmono_witness_pair:
  "contains_nonmono_witness_pair H_tweety Wtw tweety_nonmono_tasks"
  unfolding contains_nonmono_witness_pair_def tweety_nonmono_tasks_def H_tweety_def
  by (intro exI[of _ Ctw] exI[of _ "{UBird}"] exI[of _ "{UPenguin}"] exI[of _ UFlies]) auto

lemma tweety_sound_on_nonmono_tasks:
  "tr1_sound_on H_tweety F_tweety \<tau>_tweety Wtw tweety_nonmono_tasks"
  unfolding tr1_sound_on_def tweety_nonmono_tasks_def H_tweety_def F_tweety_def
  by auto

lemma tweety_not_complete_on_nonmono_tasks:
  "\<not> tr1_complete_on H_tweety F_tweety \<tau>_tweety Wtw tweety_nonmono_tasks"
proof
  assume C: "tr1_complete_on H_tweety F_tweety \<tau>_tweety Wtw tweety_nonmono_tasks"
  have T: "(Ctw,{UBird,UPenguin},UFlies) \<in> tweety_nonmono_tasks"
    unfolding tweety_nonmono_tasks_def by simp
  have F: "f_derives F_tweety Wtw Ctw (\<tau>_tweety ` {UBird,UPenguin}) (\<tau>_tweety UFlies)"
    unfolding F_tweety_def by simp
  from C T F have "a_derives H_tweety Wtw Ctw {UBird,UPenguin} UFlies"
    unfolding tr1_complete_on_def by blast
  thus False
    unfolding H_tweety_def by simp
qed

theorem tweety_nonmono_tasks_not_translatable:
  "\<not> task_restricted_translatable H_tweety F_tweety Wtw tweety_nonmono_tasks"
  by (rule nonmono_pair_blocks_task_restricted_translation[OF mono_F_tweety tweety_contains_nonmono_witness_pair])

lemma tweety_support_has_no_witness:
  "\<not> agent_support_contains_witness H_tweety Wtw"
  by (rule agent_support_contains_witness_iff_false)

lemma tweety_tr1_on_support:
  "tr1_on H_tweety F_tweety \<tau>_tweety Wtw (agent_derivable_support H_tweety Wtw)"
proof -
  have Sound: "tr1_sound_on H_tweety F_tweety \<tau>_tweety Wtw (agent_derivable_support H_tweety Wtw)"
  proof (unfold tr1_sound_on_def, intro allI impI)
    fix c \<Gamma> \<phi>
    assume T: "(c,\<Gamma>,\<phi>) \<in> agent_derivable_support H_tweety Wtw"
      and H: "a_derives H_tweety Wtw c \<Gamma> \<phi>"
    from H have Phi: "\<phi> = UFlies" and Bird: "UBird \<in> \<Gamma>"
      unfolding H_tweety_def by auto
    have BirdF: "FBird \<in> \<tau>_tweety ` \<Gamma>"
      by (rule image_eqI[where x = UBird], use Bird in simp_all)
    show "f_derives F_tweety Wtw c (\<tau>_tweety ` \<Gamma>) (\<tau>_tweety \<phi>)"
      using Phi BirdF unfolding F_tweety_def by simp
  qed
  have Complete: "tr1_complete_on H_tweety F_tweety \<tau>_tweety Wtw (agent_derivable_support H_tweety Wtw)"
  proof (unfold tr1_complete_on_def, intro allI impI)
    fix c \<Gamma> \<phi>
    assume T: "(c,\<Gamma>,\<phi>) \<in> agent_derivable_support H_tweety Wtw"
      and F: "f_derives F_tweety Wtw c (\<tau>_tweety ` \<Gamma>) (\<tau>_tweety \<phi>)"
    from T show "a_derives H_tweety Wtw c \<Gamma> \<phi>"
      unfolding agent_derivable_support_def by blast
  qed
  show ?thesis
    using Sound Complete unfolding tr1_on_def by simp
qed

theorem tweety_support_is_translatable:
  "task_restricted_translatable H_tweety F_tweety Wtw (agent_derivable_support H_tweety Wtw)"
  unfolding task_restricted_translatable_def
  using tweety_tr1_on_support by blast

lemma tweety_envelope_contains_nonmono_witness_pair:
  "contains_nonmono_witness_pair H_tweety Wtw (agent_task_envelope H_tweety Wtw)"
proof -
  have H1: "a_derives H_tweety Wtw Ctw {UBird} UFlies"
    unfolding H_tweety_def by simp
  have H2: "\<not> a_derives H_tweety Wtw Ctw ({UBird} \<union> {UPenguin}) UFlies"
    unfolding H_tweety_def by simp
  show ?thesis
    by (rule witness_pair_lives_in_agent_task_envelope[OF H1 H2])
qed

theorem tweety_envelope_not_translatable:
  "\<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw)"
proof -
  have H1: "a_derives H_tweety Wtw Ctw {UBird} UFlies"
    unfolding H_tweety_def by simp
  have H2: "\<not> a_derives H_tweety Wtw Ctw ({UBird} \<union> {UPenguin}) UFlies"
    unfolding H_tweety_def by simp
  show ?thesis
    by (rule nonmono_witness_blocks_envelope_translation[OF mono_F_tweety H1 H2])
qed

theorem tweety_support_vs_envelope_boundary:
  "task_restricted_translatable H_tweety F_tweety Wtw (agent_derivable_support H_tweety Wtw) \<and>
   \<not> task_restricted_translatable H_tweety F_tweety Wtw (agent_task_envelope H_tweety Wtw)"
  using tweety_support_is_translatable tweety_envelope_not_translatable by blast

section \<open>Reading guide\<close>

text \<open>
  Main consequences:

    \<^item> soundness plus completeness is the activating combination;
    \<^item> @{term agent_derivable_support} may remain translatable;
    \<^item> @{term agent_task_envelope} can reactivate the obstruction;
    \<^item> the same threshold appears in both the toy witness and the
      Tweety witness.
\<close>

end
