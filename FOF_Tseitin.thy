theory FOF_Tseitin
  imports Main FOF_Base
begin

lemma "(x \<longleftrightarrow> \<phi>\<^sub>1) = ((\<not> x \<or> \<phi>\<^sub>1) \<and> (\<not> \<phi>\<^sub>1 \<or> x))"
  by satx

lemma "(x \<longleftrightarrow> \<not> \<phi>\<^sub>1) = ((\<not> x \<or> \<not> \<phi>\<^sub>1) \<and> (\<phi>\<^sub>1 \<or> x))"
  by satx

lemma "(x \<longleftrightarrow> \<phi>\<^sub>1 \<and> \<phi>\<^sub>2) = ((\<not> x \<or> \<phi>\<^sub>1) \<and> (\<not> x \<or> \<phi>\<^sub>2) \<and> (\<not> \<phi>\<^sub>1 \<or> \<not> \<phi>\<^sub>2 \<or> x))"
  by satx

lemma "(x \<longleftrightarrow> \<phi>\<^sub>1 \<or> \<phi>\<^sub>2) = ((\<not> x \<or> \<phi>\<^sub>1 \<or> \<phi>\<^sub>2) \<and> (\<not> \<phi>\<^sub>1 \<or> x) \<and> (\<not> \<phi>\<^sub>2 \<or> x))"
  by satx

datatype 'a literal = Pos (atom: 'a) | Neg (atom: 'a)

type_synonym 'a clause = "'a literal list"

fun tseitin ::
  "('p set \<Rightarrow> 'p) \<Rightarrow> 'p set \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow>
    'p \<times> ('v, 'f) fof_term list \<times> ('p \<times> ('v, 'f) fof_term list) literal list list \<times> 'p set" where
  \<comment> \<open>The arguments are
    a function \<^term>\<open>fresh :: 'p set \<Rightarrow> 'p\<close> to generate fresh variables,
    a finite set \<^term>\<open>\<V> :: 'p set\<close> of variable not to use, and
    a formula \<^term>\<open>\<phi> :: ('v, 'f, 'p) formula\<close> to expand.\<close>
  \<comment> \<open>The result is a 4-tuple \<^term>\<open>((v, ts, \<C>, \<V>'))\<close>, where
    \<^term>\<open>v :: 'p\<close> is the variable representing the formula,
    \<^term>\<open>ts :: ('v, 'f) fof_term list\<close> are the arguments to the variable representing the formula,
    \<^term>\<open>\<C> :: ('p \<times> ('v, 'f) fof_term list) clause list\<close> is the clause list specifying the formula, and
    \<^term>\<open>\<V>' :: 'p set\<close> is the finite set of fresh variables generated for this formula.\<close>
  "tseitin fresh \<V> (Pred p ts) = (p, ts, [], {})" |
  "tseitin fresh \<V> (Not \<phi>\<^sub>1) =
    (let
      (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1) = tseitin fresh \<V> \<phi>\<^sub>1;
      v = fresh (\<V> \<union> \<V>\<^sub>1);
      C\<^sub>1 = [Neg (v, []), Neg (v\<^sub>1, ts\<^sub>1)];
      C\<^sub>2 = [Pos (v, []), Pos (v\<^sub>1, ts\<^sub>1)]
     in (v, [], C\<^sub>1 # C\<^sub>2 # \<C>\<^sub>1, insert v \<V>\<^sub>1))" |
  "tseitin fresh \<V> (And \<phi>\<^sub>1 \<phi>\<^sub>2) = 
    (let
      (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1) = tseitin fresh \<V> \<phi>\<^sub>1;
      (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2) = tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2;
      v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2);
      C\<^sub>1 = [Neg (v, []), Pos (v\<^sub>1, ts\<^sub>1)];
      C\<^sub>2 = [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2)];
      C\<^sub>3 = [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1), Neg (v\<^sub>2, ts\<^sub>2)]
     in (v, [], C\<^sub>1 # C\<^sub>2 # C\<^sub>3 # \<C>\<^sub>1 @ \<C>\<^sub>2, insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)))" |
  "tseitin fresh \<V> (Or \<phi>\<^sub>1 \<phi>\<^sub>2) =
    (let
      (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1) = tseitin fresh \<V> \<phi>\<^sub>1;
      (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2) = tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2;
      v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2);
      C\<^sub>1 = [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1)];
      C\<^sub>2 = [Pos (v, []), Neg (v\<^sub>2, ts\<^sub>2)];
      C\<^sub>3 = [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2), Pos (v\<^sub>1, ts\<^sub>1)]
     in (v, [], C\<^sub>1 # C\<^sub>2 # C\<^sub>3 # \<C>\<^sub>1 @ \<C>\<^sub>2, insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)))"

inductive is_nnf where
  PosPred: "is_nnf (Pred p ts)" |
  NegPred: "is_nnf (Not (Pred p ts))" |
  And: "is_nnf \<phi>\<^sub>1 \<Longrightarrow> is_nnf \<phi>\<^sub>2 \<Longrightarrow> is_nnf (And \<phi>\<^sub>1 \<phi>\<^sub>2)" |
  Or: "is_nnf \<phi>\<^sub>1 \<Longrightarrow> is_nnf \<phi>\<^sub>2 \<Longrightarrow> is_nnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2)"

lemma predicates_of_formula_finite: 
  "finite (predicates_of_formula \<phi>)"
proof (induction \<phi>)
  case (Pred p args)
  then show ?case
    by simp
next
  case (And \<phi>1 \<phi>2)
  then show ?case
    by simp
next
  case (Or \<phi>1 \<phi>2)
  then show ?case
    by simp
next
  case (Not \<phi>)
  then show ?case
    by simp
next
  case (Equal t1 t2)
  then show ?case
    by simp
next
  case (Forall v1 \<phi>)
  then show ?case
    by simp
next
  case (Exists v1 \<phi>)
  then show ?case
    by simp
next
  case T
  then show ?case
    by simp
next
  case F
  then show ?case
    by simp
qed

lemma tseitin_finite_var_set:
  assumes "is_nnf \<phi>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  shows "finite \<V>'"
  using assms
proof (induction \<phi> arbitrary: \<V> v ts \<C> \<V>' rule: is_nnf.induct)
  case (PosPred p ts)

  have "\<V>' = {}"
    using tseitin local.PosPred 
    by auto

  show ?case
    by (simp add: \<open>\<V>' = {}\<close>)
next
  case (NegPred p ts)

  have "v = fresh \<V>" and
       "\<V>' = insert v {}"
    unfolding atomize_conj
    using NegPred.prems[simplified]
    by (metis prod.inject)

  show ?case
    by (simp add: \<open>\<V>' = {v}\<close>)
next
  case (And \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 
    by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 
    by blast

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
    using And.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (metis Pair_inject)

  have "finite \<V>\<^sub>1"
    using And.IH(1) te_\<phi>1 
    by auto

  have "finite \<V>\<^sub>2"
    using And.IH(2) te_\<phi>2 
    by blast

  show ?case
    by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>finite \<V>\<^sub>1\<close> \<open>finite \<V>\<^sub>2\<close>)
next
  case (Or \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 
    by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 
    by blast

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
    using Or.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (metis Pair_inject) 

  have "finite \<V>\<^sub>1"
    using Or.IH(1) te_\<phi>1
    by auto

  have "finite \<V>\<^sub>2"
    using Or.IH(2) te_\<phi>2
    by auto

  show ?case
    by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>finite \<V>\<^sub>1\<close> \<open>finite \<V>\<^sub>2\<close>)
qed

lemma tseitin_fresh_vars:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>"
  assumes "is_nnf \<phi>"
  assumes "finite \<V>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  shows "\<V> \<inter> \<V>' = {}"
  using \<open>is_nnf \<phi>\<close> assms
proof (induction \<phi> arbitrary: \<V> v ts \<C> \<V>' rule: is_nnf.induct)
  case (PosPred p ts)

  have "\<V>' = {}"
    using tseitin PosPred.prems(4) 
    by auto

  show ?case
    by (simp add: \<open>\<V>' = {}\<close>)
next
  case (NegPred p ts)

  have "v = fresh \<V>" and
       "\<V>' = insert v {}"
    unfolding atomize_conj
    using NegPred.prems[simplified]
    by (metis Pair_inject)

  have "v \<notin> \<V>"
    using \<open>v = fresh \<V>\<close> fresh_spec
    by (simp add: NegPred.prems(3))

  show ?case
    by (simp add: \<open>\<V>' = {v}\<close> \<open>v \<notin> \<V>\<close>)
next
  case (And \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 
    by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 
    by blast

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
    using And.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (metis Pair_inject)

  have "v \<notin> \<V>"
    using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> fresh_spec
    by (metis And.hyps(1,2) And.prems(3) Un_iff
        finite_Un te_\<phi>1 te_\<phi>2 tseitin_finite_var_set)

  have IH1: "\<V> \<inter> \<V>\<^sub>1 = {}" 
    using And.IH(1) te_\<phi>1
    by (simp add: And.hyps(1) And.prems(3) fresh_spec)

  have IH2: "(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}"
    using And.IH(2) te_\<phi>2
    by (metis And.hyps(1,2) And.prems(3)
        finite_Un fresh_spec te_\<phi>1
        tseitin_finite_var_set)

  show ?case
    using IH1 IH2 \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>v \<notin> \<V>\<close>
    by auto
next
  case (Or \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 
    by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 
    by blast

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
    using Or.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (metis Pair_inject)

  have "v \<notin> \<V>"
    using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> fresh_spec
    by (metis Or.hyps(1,2) Or.prems(3) Un_iff
        finite_Un te_\<phi>1 te_\<phi>2 tseitin_finite_var_set)

  have IH1: "\<V> \<inter> \<V>\<^sub>1 = {}" 
    using Or.IH(1) te_\<phi>1
    by (simp add: Or.hyps(1) Or.prems(3) fresh_spec)

  have IH2: "(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}"
    using Or.IH(2) te_\<phi>2
    by (metis Or.hyps(1,2) Or.prems(3) finite_Un
        fresh_spec te_\<phi>1 tseitin_finite_var_set)

  show ?case
    using IH1 IH2 \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>v \<notin> \<V>\<close>
    by auto
qed

lemma
  fixes \<phi> :: "('v, 'f, 'p) formula"
  assumes "is_nnf \<phi>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  shows
    tseitin_generated_var: "v \<in> predicates_of_formula \<phi> \<union> \<V>'" and
    tseitin_generated_vars: 
      "insert v (\<Union>C \<in> set \<C>. fst ` atom ` set C) = predicates_of_formula \<phi> \<union> \<V>'"
  unfolding atomize_conj
  using assms
proof (induction \<phi> arbitrary: \<V> v ts \<C> \<V>' rule: "is_nnf.induct")
  case (PosPred p ts\<^sub>p)

  have "v = p" and
       "\<C> = []" and
       "\<V>' = {}"
    unfolding atomize_conj
    using PosPred.prems[simplified]
    by simp

  have gen_var: 
      "v \<in> predicates_of_formula (Pred p ts\<^sub>p) \<union> \<V>'"
    by (simp add: \<open>v = p\<close>)

  have gen_vars: 
      "insert v (\<Union>C \<in> set \<C>. fst ` atom ` set C) = predicates_of_formula (Pred p ts\<^sub>p) \<union> \<V>'"
    unfolding \<open>\<C> = []\<close> \<open>\<V>' = {}\<close>
    by (simp add: \<open>v = p\<close>)

  show ?case
    using gen_var gen_vars
    by simp
next
  case (NegPred p ts\<^sub>p)

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [
      [Neg (v, []), Neg (p, ts\<^sub>p)],
      [Pos (v, []), Pos (p, ts\<^sub>p)]]"

  have "v = fresh \<V>" and
       "\<C> = \<C>\<^sub>0" and
       "\<V>' = insert v {}"
    unfolding atomize_conj
    using NegPred.prems[simplified]
    by (metis Pair_inject \<C>\<^sub>0_def)

  have gen_var: 
      "v \<in> predicates_of_formula (Not (Pred p ts\<^sub>p)) \<union> \<V>'"
    by (simp add: \<open>\<V>' = {v}\<close>)

  have gen_vars: 
      "insert v (\<Union>C \<in> set \<C>. fst ` atom ` set C) = predicates_of_formula (Not (Pred p ts\<^sub>p)) \<union> \<V>'"
    unfolding \<open>\<C> = \<C>\<^sub>0\<close> \<C>\<^sub>0_def \<open>\<V>' = insert v {}\<close>
    by simp

  show ?case 
    using gen_var gen_vars
    by simp
next
  case (And \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 by blast

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [
      [Neg (v, []), Pos (v\<^sub>1, ts\<^sub>1)], 
      [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2)], 
      [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1), Neg (v\<^sub>2, ts\<^sub>2)]]"

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    using And.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified] 
    by (auto simp add: \<C>\<^sub>0_def Let_def)

  have gen_var: 
      "v \<in> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<union> \<V>'"
    by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)

  have gen_vars_\<phi>1: 
      "insert v\<^sub>1 (\<Union>C \<in> set \<C>\<^sub>1. fst ` atom ` set C) = predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
    using And.IH(1)[OF te_\<phi>1]
    by simp

  have gen_vars_\<phi>2: 
      "insert v\<^sub>2 (\<Union>C \<in> set \<C>\<^sub>2. fst ` atom ` set C) = predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
    using And.IH(2)[OF te_\<phi>2]
    by simp

  have gen_vars: 
      "insert v (\<Union>C \<in> set \<C>. fst ` atom ` set C) = predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<union> \<V>'"
    unfolding \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close> \<C>\<^sub>0_def \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
    using gen_vars_\<phi>1 gen_vars_\<phi>2
    by fastforce

  show ?case
    using gen_var gen_vars
    by simp
next
  case (Or \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 by blast

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [
      [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1)],
      [Pos (v, []), Neg (v\<^sub>2, ts\<^sub>2)],
      [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2), Pos (v\<^sub>1, ts\<^sub>1)]]"

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    using Or.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (auto simp add: \<C>\<^sub>0_def Let_def)

  have gen_var: 
      "v \<in> predicates_of_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<union> \<V>'"
    by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)

  have gen_vars_\<phi>1: 
      "insert v\<^sub>1 (\<Union>C \<in> set \<C>\<^sub>1. fst ` atom ` set C) = predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
    using Or.IH(1)[OF te_\<phi>1]
    by simp

  have gen_vars_\<phi>2: 
      "insert v\<^sub>2 (\<Union>C \<in> set \<C>\<^sub>2. fst ` atom ` set C) = predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
    using Or.IH(2)[OF te_\<phi>2]
    by simp

  have gen_vars: 
      "insert v (\<Union>C \<in> set \<C>. fst ` atom ` set C) = predicates_of_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<union> \<V>'"
    unfolding \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close> \<C>\<^sub>0_def \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
    using gen_vars_\<phi>1 gen_vars_\<phi>2
    by fastforce

  show ?case
    using gen_var gen_vars
    by simp
qed

fun formula_of_literal :: "('p \<times> ('v, 'f) fof_term list) literal \<Rightarrow> ('v, 'f, 'p) formula" where
  "formula_of_literal (Pos (p, ts)) = Pred p ts" |
  "formula_of_literal (Neg (p, ts)) = Not (Pred p ts)"

definition formula_of_clause ::
  "('p \<times> ('v, 'f) fof_term list) literal list \<Rightarrow> ('v, 'f, 'p) formula" where
  "formula_of_clause Ls = fold (\<lambda>L. Or (formula_of_literal L)) Ls F"

definition formula_of_clause_list ::
  "('p \<times> ('v, 'f) fof_term list) literal list list \<Rightarrow> ('v, 'f, 'p) formula" where
  "formula_of_clause_list Cs = fold (\<lambda>C. And (formula_of_clause C)) Cs T"

lemma formula_of_clause_eq_fold_Or:
  "formula_of_clause C = fold Or (map formula_of_literal C) F"
  by (metis (no_types, lifting) ext comp_apply
      fold_map formula_of_clause_def)

lemma formula_of_clause_list_eq_fold_And:
  "formula_of_clause_list Cs = fold And (map formula_of_clause Cs) T"
  by (metis (no_types, lifting) ext comp_apply
      fold_map formula_of_clause_list_def)

lemma eval_formula_fold_And_iff:
  "eval_formula (fold And xs \<phi>) vI fI pI \<longleftrightarrow>
    eval_formula (fold And xs T) vI fI pI \<and> eval_formula \<phi> vI fI pI"
proof (induction xs arbitrary: \<phi>)
  case Nil
  show ?case
    by simp
next
  case (Cons a xs)
  show ?case
    by (metis eval_formula.simps(2)
        fold_simps(2) local.Cons)
qed

lemma eval_formula_fold_And_append_iff:
  "eval_formula (fold And (xs @ ys) \<phi>) vI fI pI \<longleftrightarrow>
    eval_formula (fold And xs T) vI fI pI \<and>
    eval_formula (fold And ys T) vI fI pI \<and>
    eval_formula \<phi> vI fI pI"
proof (induction xs)
  case Nil
  show ?case
    by (metis append_self_conv2
        eval_formula_fold_And_iff
        fold_simps(1))
next
  case (Cons a xs)
  show ?case
    by (metis comp_apply
        eval_formula_fold_And_iff
        fold_append)
qed

lemma eval_formula_formula_of_clause_list_append_iff:
  "eval_formula (formula_of_clause_list (xs @ ys)) vI fI pI \<longleftrightarrow>
    eval_formula (formula_of_clause_list xs) vI fI pI \<and>
    eval_formula (formula_of_clause_list ys) vI fI pI"
proof (induction xs)
  case Nil
  show ?case
    unfolding formula_of_clause_list_def formula_of_clause_def
    by simp
next
  case (Cons a xs)

  let ?xs = "map formula_of_clause xs"
  let ?ys = "map formula_of_clause ys"
  let ?a = "formula_of_clause a"

  have "eval_formula (formula_of_clause_list ((a # xs) @ ys)) vI fI pI
    \<longleftrightarrow> eval_formula (fold And (?xs @ ?ys) (And ?a T)) vI fI pI"
    unfolding formula_of_clause_list_eq_fold_And
    by simp
  also have 
      "... \<longleftrightarrow> eval_formula (fold And ?xs T) vI fI pI \<and> eval_formula (fold And ?ys T) vI fI pI \<and>
               eval_formula (And ?a T) vI fI pI"
    unfolding eval_formula_fold_And_append_iff
    by simp
  also have 
      "... \<longleftrightarrow> (eval_formula (formula_of_clause_list (a # xs)) vI fI pI \<and>
                    eval_formula (formula_of_clause_list ys) vI fI pI)"
    by (metis calculation
        eval_formula_fold_And_append_iff
        eval_formula_fold_And_iff
        formula_of_clause_list_eq_fold_And
        map_append)
  finally show ?case .
qed

lemma eval_formula_cong_wrt_predicate_evaluation:
  assumes "\<And>x. x \<in> predicates_of_formula \<phi> \<Longrightarrow> pI x = pI' x"
  shows "eval_formula \<phi> vI fI pI = eval_formula \<phi> vI fI pI'"
  using assms
proof (induction \<phi> arbitrary: vI)
  case (Pred p args)
  show ?case
    by (simp add: Pred)
next
  case (And \<phi>1 \<phi>2)
  show ?case 
    by (simp add: And)
next
  case (Or \<phi>1 \<phi>2)
  show ?case 
    by (simp add: Or)
next
  case (Not \<phi>)
  show ?case 
    by (simp add: Not)
next
  case (Equal t1 t2)
  show ?case 
    by (simp add: Equal)
next
  case (Forall v \<phi>)
  have preds_of_\<phi>: "\<And>p. p \<in> predicates_of_formula \<phi> \<Longrightarrow> pI p = pI' p"
    by (simp add: Forall.prems)
  show ?case
    using Forall.IH preds_of_\<phi> 
    by auto
next
  case (Exists v \<phi>)
  have preds_of_\<phi>: "\<And>p. p \<in> predicates_of_formula \<phi> \<Longrightarrow> pI p = pI' p"
    by (simp add: Exists.prems)
  show ?case
    using Exists.IH preds_of_\<phi> 
    by auto
next
  case T
  show ?case
    by simp
next
  case F
  show ?case
    by simp
qed

lemma predicates_of_formula_of_literal:
  "predicates_of_formula (formula_of_literal l) = fst ` atom ` {l}"
proof (cases l)
  case (Pos pred)
  obtain p ts where "pred = (p, ts)"
    by fastforce
  show ?thesis
    by (simp add: Pos \<open>pred = (p, ts)\<close>)
next
  case (Neg pred)
  obtain p ts where "pred = (p, ts)"
    by fastforce
  show ?thesis
    using Neg \<open>pred = (p, ts)\<close> by auto
qed

lemma predicates_of_formula_fold_Or_map_formula_of_literal:
  "predicates_of_formula (fold Or (map formula_of_literal C) \<phi>) =
  fst ` atom ` set C \<union> predicates_of_formula \<phi>"
proof (induction C arbitrary: \<phi>)
  case Nil
  show ?case
    by simp
next
  case (Cons a C)

  have clause_simp: "fold Or (map formula_of_literal (a # C)) \<phi>
    = fold Or (map formula_of_literal C) (Or (formula_of_literal a) \<phi>)"
    by simp

  have "predicates_of_formula (fold Or (map formula_of_literal (a # C)) \<phi>)
    = fst ` atom ` set C \<union> predicates_of_formula (Or (formula_of_literal a) \<phi>)"
    unfolding clause_simp
    using Cons.IH
    by simp
  also have "... = fst ` atom ` set C \<union> 
    predicates_of_formula (formula_of_literal a) \<union> predicates_of_formula \<phi>"
    by auto
  also have "... = fst ` atom ` set C \<union> fst ` atom ` {a} \<union> predicates_of_formula \<phi>"
    by (simp add: predicates_of_formula_of_literal)
  also have "... = fst ` atom ` set (a # C) \<union> predicates_of_formula \<phi>"
    by simp
  finally show ?case .
qed

lemma predicates_of_formula_of_clause:
  "predicates_of_formula (formula_of_clause C) = fst ` atom ` set C"
proof (induction C)
  case Nil
  show ?case
    unfolding formula_of_clause_def
    by simp
next
  case (Cons a C)
  have "predicates_of_formula (formula_of_clause (a # C))
    = predicates_of_formula (fold Or (map formula_of_literal C) (Or (formula_of_literal a) F))"
    unfolding formula_of_clause_eq_fold_Or
    by simp
  also have "... = predicates_of_formula (formula_of_clause C) \<union> 
                   predicates_of_formula (formula_of_literal a) "
    unfolding predicates_of_formula_fold_Or_map_formula_of_literal
    by (simp add: local.Cons)
  also have "... = fst ` atom ` set C \<union> fst ` atom ` {a}"
    by (simp add: local.Cons predicates_of_formula_of_literal)
  also have "... = fst ` atom ` set (a # C)"
    by simp
  finally show ?case .
qed

lemma predicates_of_formula_fold_And_map_formula_of_clause:
  "predicates_of_formula (fold And (map formula_of_clause Cs) \<phi>) =
  (\<Union> C \<in> set Cs. predicates_of_formula (formula_of_clause C)) \<union> predicates_of_formula \<phi>"
proof (induction Cs arbitrary: \<phi>)
  case Nil
  show ?case
    by simp
next
  case (Cons a Cs)

  have clause_list_simp: "fold And (map formula_of_clause (a # Cs)) \<phi>
    = (fold And (map formula_of_clause Cs) (And (formula_of_clause a) \<phi>))"
    by simp

  have "predicates_of_formula (fold And (map formula_of_clause (a # Cs)) \<phi>)
    = (\<Union> C \<in> set Cs. predicates_of_formula (formula_of_clause C)) \<union>
      predicates_of_formula (And (formula_of_clause a) \<phi>)"
    unfolding clause_list_simp
    using Cons.IH
    by simp
  also have "... = (\<Union> C \<in> set Cs. predicates_of_formula (formula_of_clause C)) \<union>
      predicates_of_formula (formula_of_clause a) \<union>
      predicates_of_formula  \<phi>"
    by auto
  also have "... = (\<Union>C\<in>set (a # Cs). 
      predicates_of_formula (formula_of_clause C)) \<union> predicates_of_formula \<phi>"
    by auto
  finally show ?case .
qed

lemma predicates_of_formula_of_clause_list:
  "predicates_of_formula (formula_of_clause_list Cs) =
    (\<Union> C \<in> set Cs. predicates_of_formula (formula_of_clause C))"
proof (induction Cs)
  case Nil
  show ?case
    unfolding formula_of_clause_list_def formula_of_clause_def
    by simp
next
  case (Cons a Cs)
  have "predicates_of_formula (formula_of_clause_list (a # Cs))
    = predicates_of_formula (fold And (map formula_of_clause Cs) (And (formula_of_clause a) T))"
    unfolding formula_of_clause_list_eq_fold_And
    by simp
  also have "... = (\<Union>C\<in>set (a # Cs). predicates_of_formula (formula_of_clause C))"
    unfolding predicates_of_formula_fold_And_map_formula_of_clause
    by auto
  finally show ?case .
qed

theorem tseitin_spec:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>"
  fixes \<phi> :: "('v, 'f, 'p) formula"
  assumes "is_nnf \<phi>"
  assumes "finite \<V>" and "predicates_of_formula \<phi> \<subseteq> \<V>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  fixes pI :: "'p \<Rightarrow> 'd list \<Rightarrow> bool"
  shows "\<exists>pI'.
    (\<forall>x \<in> predicates_of_formula \<phi>. pI' x = pI x) \<and>
    eval_formula (formula_of_clause_list \<C>) vI fI pI' \<and>
    (eval_formula (Pred v ts) vI fI pI' \<longleftrightarrow> eval_formula \<phi> vI fI pI)"
  using \<open>is_nnf \<phi>\<close> \<open>finite \<V>\<close> \<open>predicates_of_formula \<phi> \<subseteq> \<V>\<close> tseitin
proof (induction \<phi> arbitrary: \<V> v ts \<C> \<V>' rule: is_nnf.induct)
  case (PosPred p ts\<^sub>p)

  have  "v = p" and
        "ts = ts\<^sub>p" and
        "\<C> = []" and
        "\<V>' = {}"
    unfolding atomize_conj
    using PosPred.prems[simplified]
    by (auto simp add: Let_def)

  define pI' :: "'p \<Rightarrow> 'd list \<Rightarrow> bool" where
    "pI' = pI"

  show ?case
  proof (intro exI conjI ballI)
    show "\<And>x. x \<in> predicates_of_formula (Pred p ts\<^sub>p) \<Longrightarrow> pI' x = pI x"
      unfolding pI'_def
      by simp
  next
    show "eval_formula (formula_of_clause_list \<C>) vI fI pI'"
      unfolding \<open>\<C> = []\<close> formula_of_clause_list_def
      by simp
  next
    show "eval_formula (Pred v ts) vI fI pI' \<longleftrightarrow> eval_formula (Pred p ts\<^sub>p) vI fI pI"
      unfolding pI'_def \<open>v = p\<close> \<open>ts = ts\<^sub>p\<close>
      by simp
  qed
next
  case (NegPred p ts\<^sub>p)

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [
      [Neg (v, []), Neg (p, ts\<^sub>p)],
      [Pos (v, []), Pos (p, ts\<^sub>p)]]"

  have "v = fresh \<V>" and
       "ts = []" and
       "\<C> = \<C>\<^sub>0" and
       "\<V>' = insert v {}"
    unfolding atomize_conj
    using NegPred.prems[simplified]
    by (metis Pair_inject \<C>\<^sub>0_def)

  define pI' :: "'p \<Rightarrow> 'd list \<Rightarrow> bool" where
    "pI' = (\<lambda>x ds. if x = v then \<not> pI p (map (\<lambda>t. eval_term t vI fI) ts\<^sub>p) else pI x ds)"

  have "v \<in> \<V>'" and "v \<notin> \<V>"
    unfolding atomize_conj
  proof (rule conjI)
    show "v \<in> \<V>'"
      by (simp add: \<open>\<V>' = {v}\<close>)
  next
    show "v \<notin> \<V>"
      unfolding \<open>v = fresh \<V>\<close>
      using fresh_spec[OF \<open>finite \<V>\<close>]
      by simp
  qed

  show ?case
  proof (intro exI conjI ballI)
    fix x
    assume \<open>x \<in> predicates_of_formula (Not (Pred p ts\<^sub>p))\<close>
    then have "x \<in> \<V>"
      using NegPred.prems(2) 
      by auto
    have "x \<noteq> v"
      using \<open>x \<in> \<V>\<close> \<open>v \<notin> \<V>\<close>
      by auto
    show "pI' x = pI x"
      unfolding pI'_def
      using \<open>x \<in> \<V>\<close> \<open>x \<noteq> v\<close>
      by simp
  next
    show "eval_formula (formula_of_clause_list \<C>) vI fI pI'"
      unfolding \<open>\<C> = \<C>\<^sub>0\<close>
    proof -
      have simp1: "formula_of_clause_list \<C>\<^sub>0
        = And (Or (Pred p ts\<^sub>p) (Or (Pred v ts) F))
              (And (Or (Not (Pred p ts\<^sub>p)) (Or (Not (Pred v ts)) F)) T)"
        unfolding \<C>\<^sub>0_def formula_of_clause_list_def formula_of_clause_def \<open>ts = []\<close>
        by simp
      have simp2: "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'
        = eval_formula 
          (And (Or (Pred p ts\<^sub>p) (Pred v ts)) 
               (Or (Not (Pred p ts\<^sub>p)) (Not (Pred v ts)))) vI fI pI'"
        using \<open>ts = []\<close>
        by (simp add: simp1)

      have posv: "eval_formula (Pred v ts) vI fI pI'
        = (\<not> pI p (map (\<lambda>t. eval_term t vI fI) ts\<^sub>p))"
        unfolding pI'_def
        by simp
      have negv: "eval_formula (Not (Pred v ts)) vI fI pI'
        = pI p (map (\<lambda>t. eval_term t vI fI) ts\<^sub>p)"
        unfolding pI'_def
        by simp
      have pospred: "eval_formula (Pred p ts\<^sub>p) vI fI pI'
        = pI p (map (\<lambda>t. eval_term t vI fI) ts\<^sub>p)"
        unfolding eval_formula.simps pI'_def
        using NegPred.prems(1,2) \<open>v = fresh \<V>\<close> fresh_spec 
        by force
      have negpred: "eval_formula (Not (Pred p ts\<^sub>p)) vI fI pI'
        = (\<not> pI p (map (\<lambda>t. eval_term t vI fI) ts\<^sub>p))"
        unfolding eval_formula.simps pI'_def
        using NegPred.prems(1,2) \<open>v = fresh \<V>\<close> fresh_spec 
        by force

      show "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'"
        using simp2 pospred posv negpred negv
        by auto
    qed
  next
    show "eval_formula (Pred v ts) vI fI pI' \<longleftrightarrow> eval_formula (formula.Not (Pred p ts\<^sub>p)) vI fI pI"
      unfolding eval_formula.simps pI'_def
      by simp
  qed
next
  case Connective: (And \<phi>\<^sub>1 \<phi>\<^sub>2)
  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 by blast

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [
      [Neg (v, []), Pos (v\<^sub>1, ts\<^sub>1)], 
      [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2)], 
      [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1), Neg (v\<^sub>2, ts\<^sub>2)]]"

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    using Connective.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (auto simp add: \<C>\<^sub>0_def Let_def)

  have "finite (\<V> \<union> \<V>\<^sub>1)"
  proof -
    have "finite \<V>\<^sub>1"
      using tseitin_finite_var_set[OF \<open>is_nnf \<phi>\<^sub>1\<close> te_\<phi>1]
      by simp
    show ?thesis
      using \<open>finite \<V>\<close> \<open>finite \<V>\<^sub>1\<close>
      by simp
  qed

  have "finite (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
  proof -
    have "finite \<V>\<^sub>2"
      using tseitin_finite_var_set[OF \<open>is_nnf \<phi>\<^sub>2\<close> te_\<phi>2]
      by simp
    show ?thesis
      using \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> \<open>finite \<V>\<^sub>2\<close>
      by simp
  qed

  have \<phi>1_subset: "predicates_of_formula \<phi>\<^sub>1 \<subseteq> \<V>"
    using Connective.prems(2)
    by simp

  have \<phi>2_subset: "predicates_of_formula \<phi>\<^sub>2 \<subseteq> \<V> \<union> \<V>\<^sub>1"
    using Connective.prems(2)
    by auto

  obtain pI1 where
    pI1_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>1. pI1 x = pI x" and
    pI1_model: "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1" and
    v\<^sub>1_equisat_\<phi>\<^sub>1: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI1 \<longleftrightarrow> eval_formula \<phi>\<^sub>1 vI fI pI"
    using Connective.IH(1)[OF \<open>finite \<V>\<close> \<phi>1_subset te_\<phi>1]
    by auto

  obtain pI2 where
    pI2_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>2. pI2 x = pI x" and
    pI2_model: "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI2" and
    v\<^sub>2_equisat_\<phi>\<^sub>2: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI2 \<longleftrightarrow> eval_formula \<phi>\<^sub>2 vI fI pI"
    using Connective.IH(2)[OF \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> \<phi>2_subset te_\<phi>2]
    by auto

  define pI' :: "'p \<Rightarrow> 'd list \<Rightarrow> bool" where
    "pI' = (\<lambda>x ds. 
      if x = v 
      then pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<and> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2) 
      else (if x \<in> \<V>\<^sub>1 then pI1 x ds 
      else (if x \<in> \<V>\<^sub>2 then pI2 x ds 
      else pI x ds)))"

  have "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
    using tseitin_generated_var[OF _ te_\<phi>1]
    by (simp add: Connective.hyps(1))

  have "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
    using tseitin_generated_var[OF _ te_\<phi>2]
    by (simp add: Connective.hyps(2))

  have "\<V> \<inter> \<V>\<^sub>1 = {}"
    using tseitin_fresh_vars[OF fresh_spec \<open>is_nnf \<phi>\<^sub>1\<close> \<open>finite \<V>\<close> te_\<phi>1]
    by simp

  have "(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}"
    using tseitin_fresh_vars[OF fresh_spec \<open>is_nnf \<phi>\<^sub>2\<close> \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> te_\<phi>2]
    by simp

  have "v \<in> \<V>'" and "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
  proof (rule conjI)
    show "v \<in> \<V>'"
      by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)
  next
    show "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
      unfolding \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
      using fresh_spec[OF \<open>finite (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>]
      by simp
  qed

  show ?case
  proof (intro exI conjI ballI)
    fix x
    assume "x \<in> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
    then have "x \<in> \<V>"
      using Connective.prems(2)
      by auto
    have "x \<noteq> v"
      using \<open>x \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
      by auto
    have "x \<notin> \<V>\<^sub>1" and "x \<notin> \<V>\<^sub>2"
      using \<open>x \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
      by auto
    show "pI' x = pI x"
      unfolding pI'_def
      using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> \<open>x \<notin> \<V>\<^sub>2\<close>
      by simp
  next
    show "eval_formula (formula_of_clause_list \<C>) vI fI pI'"
      unfolding \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close> eval_formula_formula_of_clause_list_append_iff
    proof(intro conjI)

      have simp1: "formula_of_clause_list \<C>\<^sub>0 = 
        And (Or (Not (Pred v\<^sub>2 ts\<^sub>2)) (Or (Not (Pred v\<^sub>1 ts\<^sub>1)) (Or (Pred v []) F)))
            (And (Or (Pred v\<^sub>2 ts\<^sub>2) (Or (Not (Pred v [])) F))
                 (And (Or (Pred v\<^sub>1 ts\<^sub>1) (Or (Not (Pred v [])) F)) T))" 
        unfolding \<C>\<^sub>0_def formula_of_clause_list_def formula_of_clause_def
        by simp

      have simp2: "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'
        = eval_formula
          (And (Or (Not (Pred v\<^sub>2 ts\<^sub>2)) (Or (Not (Pred v\<^sub>1 ts\<^sub>1)) (Pred v [])))
               (And (Or (Pred v\<^sub>2 ts\<^sub>2) (Not (Pred v [])))
                    (Or (Pred v\<^sub>1 ts\<^sub>1) (Not (Pred v []))))) vI fI pI'"
        unfolding simp1
        by simp

      have posv: "eval_formula (Pred v []) vI fI pI'
        = (pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<and> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
        unfolding pI'_def
        by simp
      have negv: "eval_formula (Not (Pred v [])) vI fI pI'
        = (\<not> (pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<and> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2)))"
        using posv
        by simp

      have posv1: "v\<^sub>1 \<in> \<V>\<^sub>1 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI' = pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1))"
        unfolding eval_formula.simps pI'_def
        using \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
        by auto
      have negv1: "v\<^sub>1 \<in> \<V>\<^sub>1 \<Longrightarrow> 
        (eval_formula (Not (Pred v\<^sub>1 ts\<^sub>1)) vI fI pI' = (\<not> pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1)))" 
        using posv1 
        by auto

      have posv2: "v\<^sub>2 \<in> \<V>\<^sub>2 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI' = pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
      proof -
        assume "v\<^sub>2 \<in> \<V>\<^sub>2"
        have "v\<^sub>2 \<notin> \<V>" and "v\<^sub>2 \<notin> \<V>\<^sub>1"
          unfolding atomize_conj
          using \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close> 
          by auto
        have "v\<^sub>2 \<noteq> v"
          using \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
          by auto
        show ?thesis
          unfolding eval_formula.simps pI'_def
          by (simp add: \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>v\<^sub>2 \<noteq> v\<close> \<open>v\<^sub>2 \<notin> \<V>\<^sub>1\<close>)
      qed
      have negv2: "v\<^sub>2 \<in> \<V>\<^sub>2 \<Longrightarrow> 
        (eval_formula (Not (Pred v\<^sub>2 ts\<^sub>2)) vI fI pI' = (\<not> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2)))"
        using posv2 
        by auto

      have posv1_pred: "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI' = pI v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1))"
      proof -
        assume assumption: "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1"
        have pred_\<phi>1_in_\<V>: "predicates_of_formula \<phi>\<^sub>1 \<subseteq> \<V>"
          using Connective.prems(2) 
          by auto
        have "v\<^sub>1 \<in> \<V>"
          using assumption pred_\<phi>1_in_\<V>
          by auto
        have "v\<^sub>1 \<notin> \<V>\<^sub>1"
          using \<open>v\<^sub>1 \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close>
          by auto
        have "v\<^sub>1 \<notin> \<V>\<^sub>2"
          using \<open>v\<^sub>1 \<in> \<V>\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
          by auto
        have "v\<^sub>1 \<noteq> v"
          using \<open>v\<^sub>1 \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
          by auto
        show ?thesis
          unfolding eval_formula.simps pI'_def
          by (simp add: \<open>v\<^sub>1 \<noteq> v\<close> \<open>v\<^sub>1 \<notin> \<V>\<^sub>1\<close> \<open>v\<^sub>1 \<notin> \<V>\<^sub>2\<close>)
      qed
      have negv1_pred: "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> 
        (eval_formula (Not (Pred v\<^sub>1 ts\<^sub>1)) vI fI pI' = (\<not> pI v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1)))"
        using posv1_pred 
        by auto

      have posv2_pred: "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI' = pI v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
      proof -
        assume assumption: "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2"
        have pred_\<phi>2_in_\<V>: "predicates_of_formula \<phi>\<^sub>2 \<subseteq> \<V>"
          using Connective.prems(2)
          by auto
        have "v\<^sub>2 \<in> \<V>"
          using assumption pred_\<phi>2_in_\<V>
          by auto
        have "v\<^sub>2 \<notin> \<V>\<^sub>1"
          using \<open>v\<^sub>2 \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close>
          by auto
        have "v\<^sub>2 \<notin> \<V>\<^sub>2"
          using \<open>v\<^sub>2 \<in> \<V>\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
          by auto
        have "v\<^sub>2 \<noteq> v"
          using \<open>v\<^sub>2 \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
          by auto
        show ?thesis
          unfolding eval_formula.simps pI'_def
          by (simp add: \<open>v\<^sub>2 \<noteq> v\<close> \<open>v\<^sub>2 \<notin> \<V>\<^sub>1\<close> \<open>v\<^sub>2 \<notin> \<V>\<^sub>2\<close>)
      qed
      have negv2_pred: "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> 
        (eval_formula (Not (Pred v\<^sub>2 ts\<^sub>2)) vI fI pI' = (\<not> pI v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2)))"
        using posv2_pred 
        by auto

      consider
        (A) "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<and> (v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2)" |
        (B) "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<and> (v\<^sub>2 \<in> \<V>\<^sub>2)" |
        (C) "v\<^sub>1 \<in> \<V>\<^sub>1 \<and> (v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2)" |
        (D) "v\<^sub>1 \<in> \<V>\<^sub>1 \<and> (v\<^sub>2 \<in> \<V>\<^sub>2)"
        using
          \<open>v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1\<close>
          \<open>v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2\<close>
        by blast

      then show "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'"
      proof cases
        case A
        then show ?thesis
          unfolding simp2
          using posv posv1_pred posv2_pred pI1_extends_pI pI2_extends_pI
          by simp
      next
        case B
        then show ?thesis
          unfolding simp2
          using posv negv2 posv1_pred pI1_extends_pI
          by simp
      next
        case C
        then show ?thesis 
          unfolding simp2
          using posv negv1 posv2_pred pI2_extends_pI
          by simp
      next
        case D
        then show ?thesis
          unfolding simp2
          using posv posv1 posv2
          by simp
      qed
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1, of _ pI1])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>1)"

        have ins_v: "insert v\<^sub>1 (predicates_of_formula (formula_of_clause_list \<C>\<^sub>1))
          = predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
          unfolding predicates_of_formula_of_clause_list
          unfolding predicates_of_formula_of_clause
          using tseitin_generated_vars[OF \<open>is_nnf \<phi>\<^sub>1\<close> te_\<phi>1]
          by simp

        have x_in: "x \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
          using assumption ins_v
          by auto

        have x_in_preds: "x \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> pI1 x = pI' x" 
        proof -
          assume assm: "x \<in> predicates_of_formula \<phi>\<^sub>1"
          have "x \<in> \<V>"
          proof -
            have "predicates_of_formula \<phi>\<^sub>1 \<subseteq> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
              by simp
            also have subset: "... \<subseteq> \<V>"
              using \<open>predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq> \<V>\<close>
              by simp
            show ?thesis
              using subset assm
              by auto
          qed
          have "x \<notin> \<V>\<^sub>2"
            using \<open>x \<in> \<V>\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
            by auto
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>2\<close> assm pI1_extends_pI 
            by simp
        qed

        have x_in_\<V>1: "x \<in> \<V>\<^sub>1 \<Longrightarrow> pI1 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>1"
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<^sub>1\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<in> \<V>\<^sub>1\<close>
            by simp
        qed

        show "pI1 x = pI' x"
          using x_in x_in_preds x_in_\<V>1
          by blast
      next
        show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1"
          by (simp add: pI1_model)
      qed
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1, of _ pI2])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>2)"

        have ins_v: "insert v\<^sub>2 (predicates_of_formula (formula_of_clause_list \<C>\<^sub>2))
          = predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
          unfolding predicates_of_formula_of_clause_list
          unfolding predicates_of_formula_of_clause
          using tseitin_generated_vars[OF \<open>is_nnf \<phi>\<^sub>2\<close> te_\<phi>2]
          by simp

        have x_in: "x \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
          using assumption ins_v
          by auto

        have x_in_preds: "x \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> pI2 x = pI' x" 
        proof -
          assume assm: "x \<in> predicates_of_formula \<phi>\<^sub>2"
          have "x \<in> \<V>"
          proof -
            have "predicates_of_formula \<phi>\<^sub>2 \<subseteq> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
              by simp
            also have subset: "... \<subseteq> \<V>"
              using \<open>predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq> \<V>\<close>
              by simp
            show ?thesis
              using subset assm
              by auto
          qed
          have "x \<notin> \<V>\<^sub>1"
            using \<open>x \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close>
            by auto
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> assm pI2_extends_pI
            by simp
        qed

        have x_in_\<V>2: "x \<in> \<V>\<^sub>2 \<Longrightarrow> pI2 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>2"
          have "x \<notin> \<V>\<^sub>1"
            using \<open>x \<in> \<V>\<^sub>2\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
            by auto
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<^sub>2\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> \<open>x \<in> \<V>\<^sub>2\<close>
            by simp
        qed

        show "pI2 x = pI' x"
          using x_in x_in_preds x_in_\<V>2
          by auto
      next
        show "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI2"
          by (simp add: pI2_model)
      qed
    qed
  next
    show "eval_formula (Pred v ts) vI fI pI' \<longleftrightarrow> eval_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2) vI fI pI"
      unfolding eval_formula.simps pI'_def
      using v\<^sub>1_equisat_\<phi>\<^sub>1 v\<^sub>2_equisat_\<phi>\<^sub>2
      by simp
  qed
next
  case Connective: (Or \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 by blast

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [
      [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1)],
      [Pos (v, []), Neg (v\<^sub>2, ts\<^sub>2)],
      [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2), Pos (v\<^sub>1, ts\<^sub>1)]]"

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    using Connective.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (auto simp add: \<C>\<^sub>0_def Let_def)

  have "finite (\<V> \<union> \<V>\<^sub>1)"
  proof -
    have "finite \<V>\<^sub>1"
      using tseitin_finite_var_set[OF \<open>is_nnf \<phi>\<^sub>1\<close> te_\<phi>1]
      by simp
    show ?thesis
      using \<open>finite \<V>\<close> \<open>finite \<V>\<^sub>1\<close>
      by simp
  qed

  have "finite (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
  proof -
    have "finite \<V>\<^sub>2"
      using tseitin_finite_var_set[OF \<open>is_nnf \<phi>\<^sub>2\<close> te_\<phi>2]
      by simp
    show ?thesis
      using \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> \<open>finite \<V>\<^sub>2\<close>
      by simp
  qed

  have \<phi>1_subset: "predicates_of_formula \<phi>\<^sub>1 \<subseteq> \<V>"
    using Connective.prems(2)
    by simp

  have \<phi>2_subset: "predicates_of_formula \<phi>\<^sub>2 \<subseteq> \<V> \<union> \<V>\<^sub>1"
    using Connective.prems(2)
    by auto

  obtain pI1 where
    pI1_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>1. pI1 x = pI x" and
    pI1_model: "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1" and
    v\<^sub>1_equisat_\<phi>\<^sub>1: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI1 \<longleftrightarrow> eval_formula \<phi>\<^sub>1 vI fI pI"
    using Connective.IH(1)[OF \<open>finite \<V>\<close> \<phi>1_subset te_\<phi>1]
    by auto

  obtain pI2 where
    pI2_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>2. pI2 x = pI x" and
    pI2_model: "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI2" and
    v\<^sub>2_equisat_\<phi>\<^sub>2: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI2 \<longleftrightarrow> eval_formula \<phi>\<^sub>2 vI fI pI"
    using Connective.IH(2)[OF \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> \<phi>2_subset te_\<phi>2]
    by auto

  define pI' :: "'p \<Rightarrow> 'd list \<Rightarrow> bool" where
    "pI' = (\<lambda>x ds. 
      if x = v 
      then pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<or> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2) 
      else (if x \<in> \<V>\<^sub>1 then pI1 x ds 
      else (if x \<in> \<V>\<^sub>2 then pI2 x ds 
      else pI x ds)))"

  have "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
    using tseitin_generated_var[OF _ te_\<phi>1]
    by (simp add: Connective.hyps(1))

  have "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
    using tseitin_generated_var[OF _ te_\<phi>2]
    by (simp add: Connective.hyps(2))

  have "\<V> \<inter> \<V>\<^sub>1 = {}"
    using tseitin_fresh_vars[OF fresh_spec \<open>is_nnf \<phi>\<^sub>1\<close> \<open>finite \<V>\<close> te_\<phi>1]
    by simp

  have "(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}"
    using tseitin_fresh_vars[OF fresh_spec \<open>is_nnf \<phi>\<^sub>2\<close> \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> te_\<phi>2]
    by simp

  have "v \<in> \<V>'" and "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
  proof (rule conjI)
    show "v \<in> \<V>'"
      by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)
  next
    show "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
      unfolding \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
      using fresh_spec[OF \<open>finite (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>]
      by simp
  qed

  show ?case
  proof (intro exI conjI ballI)
    fix x
    assume "x \<in> predicates_of_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2)"
    then have "x \<in> \<V>" 
      using Connective.prems(2)
      by auto
    have "x \<noteq> v"
      using \<open>x \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
      by auto
    have "x \<notin> \<V>\<^sub>1" and "x \<notin> \<V>\<^sub>2"
      using \<open>x \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
      by auto
    show "pI' x = pI x"
      unfolding pI'_def
      using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> \<open>x \<notin> \<V>\<^sub>2\<close>
      by simp
  next
    show "eval_formula (formula_of_clause_list \<C>) vI fI pI'"
      unfolding \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close> eval_formula_formula_of_clause_list_append_iff
    proof(intro conjI)
      have simp1: "formula_of_clause_list \<C>\<^sub>0 = 
        And (Or (Pred v\<^sub>1 ts\<^sub>1) (Or (Pred v\<^sub>2 ts\<^sub>2) (Or (Not (Pred v [])) F)))
            (And (Or (Not (Pred v\<^sub>2 ts\<^sub>2)) (Or (Pred v []) F))
                 (And (Or (Not (Pred v\<^sub>1 ts\<^sub>1)) (Or (Pred v []) F)) T))"
        unfolding \<C>\<^sub>0_def formula_of_clause_list_def formula_of_clause_def
        by simp

      have simp2: "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'
        = eval_formula
          (And (Or (Pred v\<^sub>1 ts\<^sub>1) (Or (Pred v\<^sub>2 ts\<^sub>2) (Not (Pred v []))))
               (And (Or (Not (Pred v\<^sub>2 ts\<^sub>2)) (Pred v []))
                    (Or (Not (Pred v\<^sub>1 ts\<^sub>1)) (Pred v [])))) vI fI pI'"
        unfolding simp1
        by simp

      have posv: "eval_formula (Pred v []) vI fI pI'
        = (pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<or> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
        unfolding pI'_def
        by simp

      have posv1: "v\<^sub>1 \<in> \<V>\<^sub>1 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI' = pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1))"
        unfolding eval_formula.simps pI'_def
        using \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
        by auto

      have posv2: "v\<^sub>2 \<in> \<V>\<^sub>2 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI' = pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
      proof -
        assume "v\<^sub>2 \<in> \<V>\<^sub>2"
        have "v\<^sub>2 \<notin> \<V>" and "v\<^sub>2 \<notin> \<V>\<^sub>1"
          unfolding atomize_conj
          using \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close> 
          by auto
        have "v\<^sub>2 \<noteq> v"
          using \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
          by auto
        show ?thesis
          unfolding eval_formula.simps pI'_def
          by (simp add: \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>v\<^sub>2 \<noteq> v\<close> \<open>v\<^sub>2 \<notin> \<V>\<^sub>1\<close>)
      qed

      have posv1_pred: "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI' = pI v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1))"
      proof -
        assume assumption: "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1"
        have pred_\<phi>1_in_\<V>: "predicates_of_formula \<phi>\<^sub>1 \<subseteq> \<V>"
          using Connective.prems(2) 
          by auto
        have "v\<^sub>1 \<in> \<V>"
          using assumption pred_\<phi>1_in_\<V>
          by auto
        have "v\<^sub>1 \<notin> \<V>\<^sub>1"
          using \<open>v\<^sub>1 \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close>
          by auto
        have "v\<^sub>1 \<notin> \<V>\<^sub>2"
          using \<open>v\<^sub>1 \<in> \<V>\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
          by auto
        have "v\<^sub>1 \<noteq> v"
          using \<open>v\<^sub>1 \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
          by auto
        show ?thesis
          unfolding eval_formula.simps pI'_def
          by (simp add: \<open>v\<^sub>1 \<noteq> v\<close> \<open>v\<^sub>1 \<notin> \<V>\<^sub>1\<close> \<open>v\<^sub>1 \<notin> \<V>\<^sub>2\<close>)
      qed

      have posv2_pred: "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> 
        (eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI' = pI v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
      proof -
        assume assumption: "v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2"
        have pred_\<phi>2_in_\<V>: "predicates_of_formula \<phi>\<^sub>2 \<subseteq> \<V>"
          using Connective.prems(2)
          by auto
        have "v\<^sub>2 \<in> \<V>"
          using assumption pred_\<phi>2_in_\<V>
          by auto
        have "v\<^sub>2 \<notin> \<V>\<^sub>1"
          using \<open>v\<^sub>2 \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close>
          by auto
        have "v\<^sub>2 \<notin> \<V>\<^sub>2"
          using \<open>v\<^sub>2 \<in> \<V>\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
          by auto
        have "v\<^sub>2 \<noteq> v"
          using \<open>v\<^sub>2 \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
          by auto
        show ?thesis
          unfolding eval_formula.simps pI'_def
          by (simp add: \<open>v\<^sub>2 \<noteq> v\<close> \<open>v\<^sub>2 \<notin> \<V>\<^sub>1\<close> \<open>v\<^sub>2 \<notin> \<V>\<^sub>2\<close>)
      qed

      consider
        (A) "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<and> (v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2)" |
        (B) "v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<and> (v\<^sub>2 \<in> \<V>\<^sub>2)" |
        (C) "v\<^sub>1 \<in> \<V>\<^sub>1 \<and> (v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2)" |
        (D) "v\<^sub>1 \<in> \<V>\<^sub>1 \<and> (v\<^sub>2 \<in> \<V>\<^sub>2)"
        using
          \<open>v\<^sub>1 \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1\<close>
          \<open>v\<^sub>2 \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2\<close>
        by blast

      then show "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'"
      proof cases
        case A
        then show ?thesis
          unfolding simp2
          using posv posv1_pred posv2_pred pI1_extends_pI pI2_extends_pI
          by auto
      next
        case B
        then show ?thesis
          unfolding simp2
          using posv posv2 posv1_pred pI1_extends_pI
          by auto
      next
        case C
        then show ?thesis 
          unfolding simp2
          using posv posv1 posv2_pred pI2_extends_pI
          by auto
      next
        case D
        then show ?thesis
          unfolding simp2
          using posv posv1 posv2
          by auto
      qed
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1, of _ pI1])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>1)"

        have ins_v: "insert v\<^sub>1 (predicates_of_formula (formula_of_clause_list \<C>\<^sub>1))
          = predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
          unfolding predicates_of_formula_of_clause_list
          unfolding predicates_of_formula_of_clause
          using tseitin_generated_vars[OF \<open>is_nnf \<phi>\<^sub>1\<close> te_\<phi>1]
          by simp

        have x_in: "x \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
          using assumption ins_v
          by auto

        have x_in_preds: "x \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> pI1 x = pI' x" 
        proof -
          assume assm: "x \<in> predicates_of_formula \<phi>\<^sub>1"
          have "x \<in> \<V>"
          proof -
            have "predicates_of_formula \<phi>\<^sub>1 \<subseteq> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
              by simp
            also have subset: "... \<subseteq> \<V>"
              using \<open>predicates_of_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq> \<V>\<close>
              by simp
            show ?thesis
              using subset assm
              by auto
          qed
          have "x \<notin> \<V>\<^sub>2"
            using \<open>x \<in> \<V>\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
            by auto
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>2\<close> assm pI1_extends_pI 
            by simp
        qed

        have x_in_\<V>1: "x \<in> \<V>\<^sub>1 \<Longrightarrow> pI1 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>1"
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<^sub>1\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<in> \<V>\<^sub>1\<close>
            by simp
        qed

        show "pI1 x = pI' x"
          using x_in x_in_preds x_in_\<V>1
          by blast
      next
        show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1"
          by (simp add: pI1_model)
      qed
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1, of _ pI2])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>2)"

        have ins_v: "insert v\<^sub>2 (predicates_of_formula (formula_of_clause_list \<C>\<^sub>2))
          = predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
          unfolding predicates_of_formula_of_clause_list
          unfolding predicates_of_formula_of_clause
          using tseitin_generated_vars[OF \<open>is_nnf \<phi>\<^sub>2\<close> te_\<phi>2]
          by simp

        have x_in: "x \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
          using assumption ins_v
          by auto

        have x_in_preds: "x \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> pI2 x = pI' x" 
        proof -
          assume assm: "x \<in> predicates_of_formula \<phi>\<^sub>2"
          have "x \<in> \<V>"
          proof -
            have "predicates_of_formula \<phi>\<^sub>2 \<subseteq> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
              by simp
            also have subset: "... \<subseteq> \<V>"
              using \<open>predicates_of_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<subseteq> \<V>\<close>
              by simp
            show ?thesis
              using subset assm
              by auto
          qed
          have "x \<notin> \<V>\<^sub>1"
            using \<open>x \<in> \<V>\<close> \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close>
            by auto
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> 
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> assm pI2_extends_pI
            by simp
        qed

        have x_in_\<V>2: "x \<in> \<V>\<^sub>2 \<Longrightarrow> pI2 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>2"
          have "x \<notin> \<V>\<^sub>1"
            using \<open>x \<in> \<V>\<^sub>2\<close> \<open>(\<V> \<union> \<V>\<^sub>1) \<inter> \<V>\<^sub>2 = {}\<close>
            by auto
          have "x \<noteq> v"
            using \<open>x \<in> \<V>\<^sub>2\<close> \<open>v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by auto
          show ?thesis
            unfolding pI'_def
            using \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> \<open>x \<in> \<V>\<^sub>2\<close>
            by simp
        qed

        show "pI2 x = pI' x"
          using x_in x_in_preds x_in_\<V>2
          by auto
      next
        show "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI2"
          by (simp add: pI2_model)
      qed
    qed
  next
    show "eval_formula (Pred v ts) vI fI pI' \<longleftrightarrow> eval_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2) vI fI pI"
      unfolding eval_formula.simps pI'_def
      using v\<^sub>1_equisat_\<phi>\<^sub>1 v\<^sub>2_equisat_\<phi>\<^sub>2
      by simp
  qed
qed

lemma model_for_tseitin_is_model_for_formula:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>"
  fixes \<phi> :: "('v, 'f, 'p) formula" and pI :: "'p \<Rightarrow> 'd list \<Rightarrow> bool"
  assumes "is_nnf \<phi>"
  assumes "finite \<V>" and "predicates_of_formula \<phi> \<subseteq> \<V>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  assumes eval_te: "eval_formula (And (Pred v ts) (formula_of_clause_list \<C>)) vI fI pI"
  shows "eval_formula \<phi> vI fI pI"
  using \<open>is_nnf \<phi>\<close> \<open>finite \<V>\<close> \<open>predicates_of_formula \<phi> \<subseteq> \<V>\<close> tseitin eval_te
proof (induction \<phi> arbitrary: \<V> v ts \<C> \<V>' rule: is_nnf.induct)
  case (PosPred p ts\<^sub>p)
  show ?case
    using PosPred.prems(3,4)
    by fastforce
next
  case (NegPred p ts\<^sub>p)

  define C\<^sub>1 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>1 = [Neg (v, []), Neg (p, ts\<^sub>p)]"
  define C\<^sub>2 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>2 = [Pos (v, []), Pos (p, ts\<^sub>p)]"

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [C\<^sub>1, C\<^sub>2]"

  have "ts = []" and
       "\<C> = \<C>\<^sub>0"
    unfolding atomize_conj
    using NegPred.prems[simplified] \<C>\<^sub>0_def C\<^sub>1_def C\<^sub>2_def
    by (metis prod.inject)

  have eval_te1: "eval_formula (Pred v ts) vI fI pI"
    using NegPred.prems(4) 
    by auto

  have eval_te2: "eval_formula (formula_of_clause_list \<C>) vI fI pI"
    using NegPred.prems(4) 
    by auto

  have C_split: "eval_formula (formula_of_clause_list [C\<^sub>1]) vI fI pI
    \<and> eval_formula (formula_of_clause_list [C\<^sub>2]) vI fI pI"
    using eval_formula_formula_of_clause_list_append_iff
    by (metis \<C>\<^sub>0_def \<open>\<C> = \<C>\<^sub>0\<close>
        append.left_neutral append_Cons
        eval_te2)

  have cl1: "eval_formula (formula_of_clause_list [C\<^sub>1]) vI fI pI"
    by (simp add: C_split)

  have cl1_simp: "(formula_of_clause_list [C\<^sub>1])
    = (And (Or (Not (Pred p ts\<^sub>p)) (Or (Not (Pred v [])) F)) T)"
    unfolding formula_of_clause_list_def formula_of_clause_def formula_of_literal.simps C\<^sub>1_def
    by simp

  have final_c1: "eval_formula (And (Or (Not (Pred p ts\<^sub>p)) (Or (Not (Pred v [])) F)) T) vI fI pI"
    using cl1 cl1_simp
    by auto

  show ?case
    using \<open>ts = []\<close> eval_te1 final_c1
    by auto
next
  case Connective: (And \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    by (metis prod.exhaust)

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    by (metis prod.exhaust)

  define C\<^sub>1 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>1 = [Neg (v, []), Pos (v\<^sub>1, ts\<^sub>1)]"
  define C\<^sub>2 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>2 = [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2)]"
  define C\<^sub>3 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>3 = [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1), Neg (v\<^sub>2, ts\<^sub>2)]"

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [C\<^sub>1, C\<^sub>2, C\<^sub>3]"

  have "ts = []" and
    "\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2"
    unfolding atomize_conj
    using Connective.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (smt (verit) C\<^sub>1_def C\<^sub>2_def C\<^sub>3_def
        \<C>\<^sub>0_def append_Cons append_self_conv2
        old.prod.inject)

  have eval_te1: "eval_formula (Pred v ts) vI fI pI"
    using Connective.prems(4) 
    by auto

  have eval_te2: "eval_formula (formula_of_clause_list \<C>) vI fI pI"
    using Connective.prems(4)
    by auto

  have C_split: "eval_formula (formula_of_clause_list [C\<^sub>1]) vI fI pI
    \<and> eval_formula (formula_of_clause_list [C\<^sub>2]) vI fI pI
    \<and> eval_formula (formula_of_clause_list [C\<^sub>3]) vI fI pI"
    using eval_formula_formula_of_clause_list_append_iff
    by (metis \<C>\<^sub>0_def \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
        append.left_neutral append_Cons
        eval_te2)

  have "finite (\<V> \<union> \<V>\<^sub>1)"
  proof -
    have "finite \<V>\<^sub>1"
      using tseitin_finite_var_set[OF \<open>is_nnf \<phi>\<^sub>1\<close> te_\<phi>1]
      by simp
    show ?thesis
      using \<open>finite \<V>\<close> \<open>finite \<V>\<^sub>1\<close>
      by simp
  qed

  have \<phi>1_subset: "predicates_of_formula \<phi>\<^sub>1 \<subseteq> \<V>"
    using Connective.prems(2)
    by simp

  have \<phi>2_subset: "predicates_of_formula \<phi>\<^sub>2 \<subseteq> \<V> \<union> \<V>\<^sub>1"
    using Connective.prems(2)
    by auto

  have \<phi>1_true: "eval_formula \<phi>\<^sub>1 vI fI pI"
  proof -
    have simp1: "eval_formula (And (formula_of_clause C\<^sub>1) T) vI fI pI"
      using formula_of_clause_list_def
      by (metis C_split fold_simps(1,2))
    have simp2: "formula_of_clause C\<^sub>1 = (Or (Pred v\<^sub>1 ts\<^sub>1) (Or (Not (Pred v ts)) F))"
      unfolding formula_of_clause_def
      by (simp add: C\<^sub>1_def \<open>ts = []\<close>)
    have v1_true: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI"
      using eval_te1 simp1 simp2
      by auto
    show ?thesis
      using Connective.IH(1)[OF \<open>finite \<V>\<close> \<phi>1_subset te_\<phi>1 _]
      by (metis \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
          eval_formula.simps(2)
          eval_formula_formula_of_clause_list_append_iff
          eval_te2 v1_true)
  qed

  have \<phi>2_true: "eval_formula \<phi>\<^sub>2 vI fI pI"
    proof -
    have simp1: "eval_formula (And (formula_of_clause C\<^sub>2) T) vI fI pI"
      using formula_of_clause_list_def
      by (metis C_split fold_simps(1,2))
    have simp2: "formula_of_clause C\<^sub>2 = (Or (Pred v\<^sub>2 ts\<^sub>2) (Or (Not (Pred v ts)) F))"
      unfolding formula_of_clause_def
      by (simp add: C\<^sub>2_def \<open>ts = []\<close>)
    have v2_true: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI"
      using eval_te1 simp1 simp2
      by auto
    show ?thesis
      using Connective.IH(2)[OF \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> \<phi>2_subset te_\<phi>2 _]
      by (metis \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
          eval_formula.simps(2)
          eval_formula_formula_of_clause_list_append_iff
          eval_te2 v2_true)
  qed

  show ?case
    by (simp add: \<phi>1_true \<phi>2_true)
next
  case Connective: (Or \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    by (metis prod.exhaust)

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    by (metis prod.exhaust)

  define C\<^sub>1 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>1 = [Pos (v, []), Neg (v\<^sub>1, ts\<^sub>1)]"
  define C\<^sub>2 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>2 = [Pos (v, []), Neg (v\<^sub>2, ts\<^sub>2)]"
  define C\<^sub>3 :: "('p \<times> ('v, 'f) fof_term list) literal list" where
    "C\<^sub>3 = [Neg (v, []), Pos (v\<^sub>2, ts\<^sub>2), Pos (v\<^sub>1, ts\<^sub>1)]"

  define \<C>\<^sub>0 :: "('p \<times> ('v, 'f) fof_term list) literal list list" where
    "\<C>\<^sub>0 = [C\<^sub>1, C\<^sub>2, C\<^sub>3]"

  have "ts = []" and
    "\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2"
    unfolding atomize_conj
    using Connective.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (smt (verit) C\<^sub>1_def C\<^sub>2_def C\<^sub>3_def
        \<C>\<^sub>0_def append_Cons append_self_conv2
        old.prod.inject)

  have eval_te1: "eval_formula (Pred v ts) vI fI pI"
    using Connective.prems(4) 
    by auto

  have eval_te2: "eval_formula (formula_of_clause_list \<C>) vI fI pI"
    using Connective.prems(4)
    by auto

  have C_split: "eval_formula (formula_of_clause_list [C\<^sub>1]) vI fI pI
    \<and> eval_formula (formula_of_clause_list [C\<^sub>2]) vI fI pI
    \<and> eval_formula (formula_of_clause_list [C\<^sub>3]) vI fI pI"
    using eval_formula_formula_of_clause_list_append_iff
    by (metis \<C>\<^sub>0_def \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
        append.left_neutral append_Cons
        eval_te2)

  have simp1: "eval_formula (And (formula_of_clause C\<^sub>3) T) vI fI pI"
    unfolding atomize_conj
    using formula_of_clause_list_def
    by (metis C_split fold_simps(1,2))

  have simp2: "formula_of_clause C\<^sub>3 = Or (Pred v\<^sub>1 ts\<^sub>1) (Or (Pred v\<^sub>2 ts\<^sub>2) (Or (Not (Pred v ts)) F))"
    unfolding formula_of_clause_def
    by (simp add: C\<^sub>3_def \<open>ts = []\<close>)

  have v1_or_v2_true: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI \<or> eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI"
    using eval_te1 simp1 simp2 
    by force

  have "finite (\<V> \<union> \<V>\<^sub>1)"
  proof -
    have "finite \<V>\<^sub>1"
      using tseitin_finite_var_set[OF \<open>is_nnf \<phi>\<^sub>1\<close> te_\<phi>1]
      by simp
    show ?thesis
      using \<open>finite \<V>\<close> \<open>finite \<V>\<^sub>1\<close>
      by simp
  qed

  have \<phi>1_subset: "predicates_of_formula \<phi>\<^sub>1 \<subseteq> \<V>"
    using Connective.prems(2)
    by simp

  have \<phi>2_subset: "predicates_of_formula \<phi>\<^sub>2 \<subseteq> \<V> \<union> \<V>\<^sub>1"
    using Connective.prems(2)
    by auto

  have \<phi>1_or_\<phi>2_true: "eval_formula \<phi>\<^sub>1 vI fI pI \<or> eval_formula \<phi>\<^sub>2 vI fI pI"
    using Connective.IH(1)[OF \<open>finite \<V>\<close> \<phi>1_subset te_\<phi>1 _] 
    using Connective.IH(2)[OF \<open>finite (\<V> \<union> \<V>\<^sub>1)\<close> \<phi>2_subset te_\<phi>2 _]
    by (metis \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
        eval_formula.simps(2)
        eval_formula_formula_of_clause_list_append_iff
        eval_te2 v1_or_v2_true)

  show ?case 
    using \<phi>1_or_\<phi>2_true 
    by auto
qed

definition tseitin_expansion where
  "tseitin_expansion fresh \<phi> =
    (let (v, ts, \<C>, _) = tseitin fresh (predicates_of_formula \<phi>) \<phi>
     in And (Pred v ts) (formula_of_clause_list \<C>))"

theorem tseitin_expansion_equisat:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>"
  fixes \<phi> :: "('v, 'f, 'p) formula"
  assumes "is_nnf \<phi>"
  shows "(\<exists>pI. eval_formula \<phi> vI fI pI) \<longleftrightarrow>
    (\<exists>pI. eval_formula (tseitin_expansion fresh \<phi>) vI fI pI)"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof (rule iffI)

  define \<V> where
    "\<V> = predicates_of_formula \<phi>"

  have "predicates_of_formula \<phi> = \<V>"
    by (simp add: \<V>_def)

  have "finite \<V>"
    unfolding \<V>_def
    by (simp add: predicates_of_formula_finite)

  have "predicates_of_formula \<phi> \<subseteq> \<V>"
    unfolding \<V>_def
    by simp

  obtain v ts \<C> \<V>' where tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
    by (metis prod.exhaust)

  show "?LHS \<Longrightarrow> ?RHS"
    unfolding tseitin_expansion_def \<open>predicates_of_formula \<phi> = \<V>\<close> tseitin Let_def prod.case
  proof -
    assume assumption: "\<exists>pI. eval_formula \<phi> vI fI pI"
    obtain pI where \<phi>_pI: "eval_formula \<phi> vI fI pI"
      using assumption 
      by auto
    obtain pI' where
      pI'_model: "eval_formula (formula_of_clause_list \<C>) vI fI pI'" and
      v_equisat_\<phi>: "eval_formula (Pred v ts) vI fI pI' \<longleftrightarrow> eval_formula \<phi> vI fI pI"
      using tseitin_spec[OF fresh_spec \<open>is_nnf \<phi>\<close> \<open>finite \<V>\<close> \<open>predicates_of_formula \<phi> \<subseteq> \<V>\<close> tseitin]
      by blast
    have eval_tseitin_\<phi>: "eval_formula (And (Pred v ts) (formula_of_clause_list \<C>)) vI fI pI'"
      using \<phi>_pI pI'_model v_equisat_\<phi>
      by auto
    show "\<exists>pI. eval_formula (And (Pred v ts) (formula_of_clause_list \<C>)) vI fI pI"
      using eval_tseitin_\<phi> 
      by auto
  qed
  
  show "?RHS \<Longrightarrow> ?LHS"
    unfolding tseitin_expansion_def \<open>predicates_of_formula \<phi> = \<V>\<close> tseitin Let_def prod.case
  proof -
    assume assumption: "\<exists>pI. eval_formula (And (Pred v ts) (formula_of_clause_list \<C>)) vI fI pI"
    obtain pI where te_pI: "eval_formula (And (Pred v ts) (formula_of_clause_list \<C>)) vI fI pI"
      using assumption
      by auto
    have eval_\<phi>: "eval_formula \<phi> vI fI pI"
      using model_for_tseitin_is_model_for_formula
        [OF fresh_spec \<open>is_nnf \<phi>\<close> \<open>finite \<V>\<close> \<open>predicates_of_formula \<phi> \<subseteq> \<V>\<close> tseitin te_pI]
      by simp
    show "?LHS"
      using eval_\<phi>
      by auto
  qed
qed

(*Proved but not used*)
lemma tseitin_fresh_var_in_fresh_var_set:
  assumes "is_nnf \<phi>"
  assumes "predicates_of_formula \<phi> \<subseteq> \<V>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  shows "v \<in> (if \<V>' = {} then \<V> else \<V>')"
  using assms
proof (induction \<phi>  arbitrary: \<V> v ts \<C> \<V>' rule: is_nnf.induct)
  case (PosPred p ts\<^sub>p)

  have  "v = p" and
        "ts = ts\<^sub>p" and
        "\<C> = []" and
        "\<V>' = {}"
    unfolding atomize_conj
    using PosPred.prems[simplified]
    by simp

  have "p \<in> \<V>"
    using PosPred.prems(1) 
    by auto

  show ?case
    by (simp add: \<open>\<V>' = {}\<close> \<open>p \<in> \<V>\<close> \<open>v = p\<close>)
next
  case (NegPred p ts\<^sub>p)

  have "v = fresh \<V>" and
       "ts = []" and
       "\<V>' = insert v {}"
    unfolding atomize_conj
    using NegPred.prems[simplified]
    by (metis prod.inject)

  show ?case
    by (simp add: \<open>\<V>' = {v}\<close>)
next
  case (And \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 
    by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 
    by blast

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
    using And.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (metis Pair_inject)

  show ?case
    by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)
next
  case (Or \<phi>\<^sub>1 \<phi>\<^sub>2)

  obtain v\<^sub>1 ts\<^sub>1 \<C>\<^sub>1 \<V>\<^sub>1 where
    te_\<phi>1: "tseitin fresh \<V> \<phi>\<^sub>1 = (v\<^sub>1, ts\<^sub>1, \<C>\<^sub>1, \<V>\<^sub>1)"
    using prod_cases4 
    by blast

  obtain v\<^sub>2 ts\<^sub>2 \<C>\<^sub>2 \<V>\<^sub>2 where
    te_\<phi>2: "tseitin fresh (\<V> \<union> \<V>\<^sub>1) \<phi>\<^sub>2 = (v\<^sub>2, ts\<^sub>2, \<C>\<^sub>2, \<V>\<^sub>2)"
    using prod_cases4 
    by blast

  have
    "v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)" and
    "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
    unfolding atomize_conj
    using Or.prems[simplified, unfolded te_\<phi>1, simplified, unfolded te_\<phi>2, simplified]
    by (metis Pair_inject)

  show ?case
    by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)
qed

end