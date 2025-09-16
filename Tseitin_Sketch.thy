theory Tseitin_Sketch
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

fun formula_of_literal :: "('p \<times> ('v, 'f) fof_term list) literal \<Rightarrow> ('v, 'f, 'p) formula" where
  "formula_of_literal (Pos (p, ts)) = Pred p ts" |
  "formula_of_literal (Neg (p, ts)) = Not (Pred p ts)"

definition formula_of_clause ::
  "('p \<times> ('v, 'f) fof_term list) literal list \<Rightarrow> ('v, 'f, 'p) formula" where
  "formula_of_clause Ls = fold (\<lambda>L. Or (formula_of_literal L)) Ls F"

definition formula_of_clause_list ::
  "('p \<times> ('v, 'f) fof_term list) literal list list \<Rightarrow> ('v, 'f, 'p) formula" where
  "formula_of_clause_list Cs = fold (\<lambda>C. And (formula_of_clause C)) Cs T"

inductive is_nnf where
  PosPred: "is_nnf (Pred p ts)" |
  NegPred: "is_nnf (Not (Pred p ts))" |
  And: "is_nnf \<phi>\<^sub>1 \<Longrightarrow> is_nnf \<phi>\<^sub>2 \<Longrightarrow> is_nnf (And \<phi>\<^sub>1 \<phi>\<^sub>2)" |
  Or: "is_nnf \<phi>\<^sub>1 \<Longrightarrow> is_nnf \<phi>\<^sub>2 \<Longrightarrow> is_nnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2)"

lemma predicates_of_formula_finite: "finite (predicates_of_formula \<phi>)"
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
       "ts = []" and
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
    \<V>'_def: "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
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
    using IH1 IH2 \<V>'_def \<open>v \<notin> \<V>\<close>
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
    \<V>'_def: "\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)"
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
    using IH1 IH2 \<V>'_def \<open>v \<notin> \<V>\<close>
    by auto
qed

(**) (*TODO*)
lemma tseitin_fresh_var_in_fresh_var_set:
  assumes "is_nnf \<phi>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
(*  
  assumes "\<V>' \<noteq> {}"
*)
  shows "v \<in> \<V>'"
  using assms
proof (induction \<phi> rule: is_nnf.induct)
  case (PosPred p ts)
  show ?case 
    sorry
next
  case (NegPred p ts)
  show ?case 
    sorry
next
  case (And \<phi>\<^sub>1 \<phi>\<^sub>2)
  show ?case 
    sorry
next
  case (Or \<phi>\<^sub>1 \<phi>\<^sub>2)
  show ?case 
    sorry
qed

(*TODO*)
lemma eval_formula_formula_of_clause_list_append_iff:
  "eval_formula (formula_of_clause_list (xs @ ys)) vI fI pI \<longleftrightarrow>
    eval_formula (formula_of_clause_list xs) vI fI pI \<and>
    eval_formula (formula_of_clause_list ys) vI fI pI"
  sorry

(*TODO*)
lemma eval_formula_cong_wrt_predicate_evaluation:
  assumes "\<And>x. x \<in> predicates_of_formula \<phi> \<Longrightarrow> pI x = pI' x"
  shows "eval_formula \<phi> vI fI pI = eval_formula \<phi> vI fI pI'"
  sorry

(**) (*TODO*)
lemma predicates_of_clause_list:
  fixes \<phi> :: "('v, 'f, 'p) formula"
  assumes "is_nnf \<phi>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
(*
  assumes "\<C> \<noteq> []"
*)
  shows "predicates_of_formula (formula_of_clause_list \<C>)
    = (predicates_of_formula \<phi>) \<union> \<V>' \<union> {v\<^sub>1}"
  using assms
proof (induction \<phi> rule: is_nnf.induct)
  case (PosPred p ts)
  show ?case 
    sorry
next
  case (NegPred p ts)
  show ?case 
    sorry
next
  case (And \<phi>\<^sub>1 \<phi>\<^sub>2)
  show ?case 
    sorry
next
  case (Or \<phi>\<^sub>1 \<phi>\<^sub>2)
  show ?case 
    sorry
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

  show ?case
  proof (intro exI conjI ballI)
    show "\<And>x. x \<in> predicates_of_formula (formula.Not (Pred p ts\<^sub>p)) \<Longrightarrow> pI' x = pI x"
      unfolding pI'_def fun_eq_iff
      using NegPred.prems(1,2) \<open>v = fresh \<V>\<close> fresh_spec 
      by auto
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

  obtain pI1 where
    pI1_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>1. pI1 x = pI x" and
    pI1_model: "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1" and
    v\<^sub>1_equisat_\<phi>\<^sub>1: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI1 \<longleftrightarrow> eval_formula \<phi>\<^sub>1 vI fI pI"
    using Connective.IH(1)[OF _ _ te_\<phi>1] Connective.prems(1,2) 
    by auto

  obtain pI2 where
    pI2_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>2. pI2 x = pI x" and
    pI2_model: "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI2" and
    v\<^sub>2_equisat_\<phi>\<^sub>2: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI2 \<longleftrightarrow> eval_formula \<phi>\<^sub>2 vI fI pI"
    using Connective.IH(2)[OF _ _ te_\<phi>2] te_\<phi>1 Connective.prems(1,2)
    by (metis (no_types, lifting) Connective.hyps(1)
        finite_Un formula.simps(207) le_sup_iff
        sup.coboundedI2 sup_commute
        tseitin_finite_var_set)

  define pI' :: "'p \<Rightarrow> 'd list \<Rightarrow> bool" where
    "pI' = (\<lambda>x ds. 
      if x = v then pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<and> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2) 
      else (if x \<in> \<V>\<^sub>1 then pI1 x ds 
      else (if x \<in> \<V>\<^sub>2 then pI2 x ds 
      else pI x ds)))"

  show ?case
  proof (intro exI conjI ballI)
    fix x
    assume preds: "x \<in> predicates_of_formula (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
    have "x \<in> \<V>"
      using preds Connective.prems(2)
      by blast
    have x_ne_v: "x \<noteq> v"
      using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>x \<in> \<V>\<close> fresh_spec
      by (meson Connective.hyps(1,2)
          Connective.prems(1) UnCI finite_UnI te_\<phi>1
          te_\<phi>2 tseitin_finite_var_set)
    have x_ni_\<V>': "x \<in> \<V> \<Longrightarrow> x \<notin> \<V>'"
      by (metis And Connective.hyps(1,2)
          Connective.prems(1,3) IntI empty_iff 
          fresh_spec tseitin_fresh_vars)
    have x_ni_\<V>1: "x \<notin> \<V>\<^sub>1" and x_ni_\<V>2: "x \<notin> \<V>\<^sub>2"
      using \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>x \<in> \<V>\<close> x_ni_\<V>'
      by auto
    show "pI' x = pI x"
      unfolding pI'_def fun_eq_iff
      using x_ne_v x_ni_\<V>1 x_ni_\<V>2
      by auto 
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

      have "v \<in> \<V>'" and v_not_in: "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
        unfolding atomize_conj
      proof (rule conjI)
        show "v \<in> \<V>'"
          by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)
      next 
        have "v \<notin> \<V> \<and> v \<notin> \<V>\<^sub>1 \<and> v \<notin> \<V>\<^sub>2"
          by (metis Connective.hyps(1,2)
              Connective.prems(1) Un_iff
              \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> finite_Un
              fresh_spec te_\<phi>1 te_\<phi>2
              tseitin_finite_var_set)
        then show "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
          by simp
      qed
(*
      have "\<V>\<^sub>1 \<noteq> {} \<or> \<V>\<^sub>1 = {}"
        by simp
*)
      have "v\<^sub>1 \<in> \<V>\<^sub>1" and "v\<^sub>1 \<notin> \<V>" and "v\<^sub>2 \<in> \<V>\<^sub>2" and "v\<^sub>2 \<notin> (\<V> \<union> \<V>\<^sub>1)"
        unfolding atomize_conj
        by (metis Connective.hyps(1,2)
            Connective.prems(1) disjoint_iff
            finite_UnI fresh_spec te_\<phi>1 te_\<phi>2
            tseitin_finite_var_set
            tseitin_fresh_var_in_fresh_var_set
            tseitin_fresh_vars)

      have posv: "eval_formula (Pred v []) vI fI pI'
        = (pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<and> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
        unfolding pI'_def
        by simp
      have negv: "eval_formula (Not (Pred v [])) vI fI pI'
        = (\<not> (pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<and> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2)))"
        using posv
        by simp

      have posv1: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI' 
        = pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1)"
        unfolding eval_formula.simps pI'_def
        using \<open>v\<^sub>1 \<in> \<V>\<^sub>1\<close> v_not_in
        by auto
      have negv1: "eval_formula (Not (Pred v\<^sub>1 ts\<^sub>1)) vI fI pI'
        = (\<not> pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1))"
        using posv1 
        by auto

      have posv2: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI'
        = pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2)"
        unfolding eval_formula.simps pI'_def
        using \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>v\<^sub>2 \<notin> \<V> \<union> \<V>\<^sub>1\<close> v_not_in
        by auto
      have negv2: "eval_formula (Not (Pred v\<^sub>2 ts\<^sub>2)) vI fI pI'
        = (\<not> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
        using posv2 
        by auto

      show "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'"
        using simp2 posv negv posv1 negv1 posv2 negv2
        by simp
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>1)"
(*
        have "\<C>\<^sub>1 \<noteq> [] \<or> \<C>\<^sub>1 = []"
          by simp
*)
        have \<C>1_preds: "predicates_of_formula (formula_of_clause_list \<C>\<^sub>1)
          = predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1 \<union> {v\<^sub>1}"
          using predicates_of_clause_list[OF _ te_\<phi>1]
          by (simp add: Connective.hyps(1))

        have "\<V>\<^sub>1 \<union> {v\<^sub>1} = \<V>\<^sub>1"
          using Connective.hyps(1) te_\<phi>1 tseitin_fresh_var_in_fresh_var_set
          by fastforce

        have "x \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
          using \<C>1_preds assumption \<open>\<V>\<^sub>1 \<union> {v\<^sub>1} = \<V>\<^sub>1\<close>
          by auto

        have x_in_pred_of_\<phi>1: "x \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> pI1 x = pI' x" 
        proof -
          assume assumption: "x \<in> predicates_of_formula \<phi>\<^sub>1"

          have "x \<in> \<V>"
            using Connective.prems(2) assumption
            by fastforce
          have "v \<notin> \<V>"
            using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> fresh_spec
            by (metis Connective.hyps(1,2)
                Connective.prems(1) Un_iff finite_Un
                te_\<phi>1 te_\<phi>2 tseitin_finite_var_set)
          have "x \<noteq> v"
            using \<open>v \<notin> \<V>\<close> \<open>x \<in> \<V>\<close> 
            by auto
          have "\<V> \<inter> \<V>\<^sub>2 = {}"
            using tseitin_fresh_vars[OF _ _ _ te_\<phi>2]
            by (metis Connective.hyps(2)
                Connective.prems(1) Int_assoc Un_Int_eq(4)
                Un_commute \<C>1_preds fresh_spec
                inf_compl_bot_right infinite_Un
                predicates_of_formula_finite)
          have "x \<notin> \<V>\<^sub>2"
            using \<open>\<V> \<inter> \<V>\<^sub>2 = {}\<close> \<open>x \<in> \<V>\<close>
            by auto

          show ?thesis
            unfolding pI'_def
            by (simp add: \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>2\<close> assumption pI1_extends_pI)
        qed

        have x_in_\<V>1: "x \<in> \<V>\<^sub>1 \<Longrightarrow> pI1 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>1"

          have "v \<notin> \<V>\<^sub>1"
            unfolding \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by (metis And Connective.hyps(1,2)
                Connective.prems(1,3) UnI1 UnI2
                \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> finite_insert
                fresh_spec infinite_Un tseitin_finite_var_set)

          show ?thesis
            unfolding pI'_def
            using \<open>v \<notin> \<V>\<^sub>1\<close> \<open>x \<in> \<V>\<^sub>1\<close> 
            by auto
        qed

        show "pI1 x = pI' x"
          using \<open>x \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1\<close> x_in_\<V>1 x_in_pred_of_\<phi>1 
          by auto
      next
        show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1"
          by (simp add: pI1_model)
      qed
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>2)"

        have \<C>2_preds: "predicates_of_formula (formula_of_clause_list \<C>\<^sub>2)
          = predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2 \<union> {v\<^sub>2}"
          using predicates_of_clause_list[OF _ te_\<phi>2]
          by (simp add: Connective.hyps(2))

        have "\<V>\<^sub>2 \<union> {v\<^sub>2} = \<V>\<^sub>2"
          using Connective.hyps(2) te_\<phi>2 tseitin_fresh_var_in_fresh_var_set
          by fastforce

        have "x \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
          using \<C>2_preds assumption \<open>\<V>\<^sub>2 \<union> {v\<^sub>2} = \<V>\<^sub>2\<close>
          by auto

        have x_in_pred_of_\<phi>2: "x \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> pI2 x = pI' x" 
        proof -
          assume assumption: "x \<in> predicates_of_formula \<phi>\<^sub>2"

          have "x \<in> \<V>"
            using Connective.prems(2) assumption
            by fastforce
          have "v \<notin> \<V>"
            using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> fresh_spec
            by (metis Connective.hyps(1,2)
                Connective.prems(1) Un_iff finite_Un
                te_\<phi>1 te_\<phi>2 tseitin_finite_var_set)
          have "x \<noteq> v"
            using \<open>v \<notin> \<V>\<close> \<open>x \<in> \<V>\<close> 
            by auto
          have "\<V> \<inter> \<V>\<^sub>1 = {}"
            using tseitin_fresh_vars[OF _ _ _ te_\<phi>1]
            by (simp add: Connective.hyps(1)
                Connective.prems(1) fresh_spec)
          have "x \<notin> \<V>\<^sub>1"
            using \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close> \<open>x \<in> \<V>\<close>
            by auto

          show ?thesis
            unfolding pI'_def
            by (simp add: \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> assumption pI2_extends_pI)
        qed

        have x_in_\<V>2: "x \<in> \<V>\<^sub>2 \<Longrightarrow> pI2 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>2"

          have "x \<notin> \<V>\<^sub>1"
            using fresh_spec
            by (meson PosPred all_not_in_conv
                tseitin.simps(1)
                tseitin_fresh_var_in_fresh_var_set)

          have "v \<notin> \<V>\<^sub>2"
            unfolding \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by (metis Connective.hyps(1)
                Connective.prems(1) UnCI \<C>2_preds
                finite_Un fresh_spec
                predicates_of_formula_finite te_\<phi>1
                tseitin_finite_var_set)

          show ?thesis
            unfolding pI'_def
            using \<open>v \<notin> \<V>\<^sub>2\<close> \<open>x \<in> \<V>\<^sub>2\<close> \<open>x \<notin> \<V>\<^sub>1\<close>
            by auto
        qed

        show "pI2 x = pI' x"
          using \<open>x \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2\<close> x_in_\<V>2 x_in_pred_of_\<phi>2 
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

  obtain pI1 where
    pI1_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>1. pI1 x = pI x" and
    pI1_model: "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1" and
    v\<^sub>1_equisat_\<phi>\<^sub>1: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI1 \<longleftrightarrow> eval_formula \<phi>\<^sub>1 vI fI pI"
    using Connective.IH(1)[OF _ _ te_\<phi>1] Connective.prems(1,2)
    by auto

  obtain pI2 where
    pI2_extends_pI: "\<forall>x\<in>predicates_of_formula \<phi>\<^sub>2. pI2 x = pI x" and
    pI2_model: "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI2" and
    v\<^sub>2_equisat_\<phi>\<^sub>2: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI2 \<longleftrightarrow> eval_formula \<phi>\<^sub>2 vI fI pI"
    using Connective.IH(2)[OF _ _ te_\<phi>2] te_\<phi>1 Connective.prems(1,2)
    by (metis (no_types, lifting) Connective.hyps(1)
        finite_Un formula.simps(208) le_sup_iff
        sup.coboundedI2 sup_commute
        tseitin_finite_var_set)

  define pI' :: "'p \<Rightarrow> 'd list \<Rightarrow> bool" where
    "pI' = (\<lambda>x ds. 
      if x = v then pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<or> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2) 
      else (if x \<in> \<V>\<^sub>1 then pI1 x ds 
      else (if x \<in> \<V>\<^sub>2 then pI2 x ds 
      else pI x ds)))"

  show ?case
  proof (intro exI conjI ballI)
    fix x
    assume preds: "x \<in> predicates_of_formula (Or \<phi>\<^sub>1 \<phi>\<^sub>2)"
    have "x \<in> \<V>"
      using preds Connective.prems(2)
      by blast
    have x_ne_v: "x \<noteq> v"
      using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>x \<in> \<V>\<close> fresh_spec
      by (meson Connective.hyps(1,2)
          Connective.prems(1) UnCI finite_UnI te_\<phi>1
          te_\<phi>2 tseitin_finite_var_set)
    have x_ni_\<V>': "x \<in> \<V> \<Longrightarrow> x \<notin> \<V>'"
      by (metis Connective.hyps(1,2)
          Connective.prems(1,3) IntI Or empty_iff
          fresh_spec tseitin_fresh_vars)
    have x_ni_\<V>1: "x \<notin> \<V>\<^sub>1" and x_ni_\<V>2: "x \<notin> \<V>\<^sub>2"
      using \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> \<open>x \<in> \<V>\<close> x_ni_\<V>'
      by auto
    show "pI' x = pI x"
      unfolding pI'_def fun_eq_iff
      using x_ne_v x_ni_\<V>1 x_ni_\<V>2
      by auto  
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

      have "v \<in> \<V>'" and v_not_in: "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
        unfolding atomize_conj
      proof (rule conjI)
        show "v \<in> \<V>'"
          by (simp add: \<open>\<V>' = insert v (\<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>)
      next 
        have "v \<notin> \<V> \<and> v \<notin> \<V>\<^sub>1 \<and> v \<notin> \<V>\<^sub>2"
          by (metis Connective.hyps(1,2)
              Connective.prems(1) Un_iff
              \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> finite_Un
              fresh_spec te_\<phi>1 te_\<phi>2
              tseitin_finite_var_set)
        then show "v \<notin> (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)"
          by simp
      qed

      have "v\<^sub>1 \<in> \<V>\<^sub>1" and "v\<^sub>1 \<notin> \<V>" and "v\<^sub>2 \<in> \<V>\<^sub>2" and "v\<^sub>2 \<notin> (\<V> \<union> \<V>\<^sub>1)"
        unfolding atomize_conj
        by (metis Connective.hyps(1,2)
            Connective.prems(1) disjoint_iff
            finite_UnI fresh_spec te_\<phi>1 te_\<phi>2
            tseitin_finite_var_set
            tseitin_fresh_var_in_fresh_var_set
            tseitin_fresh_vars)

      have posv: "eval_formula (Pred v []) vI fI pI'
        = (pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1) \<or> pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2))"
        unfolding pI'_def
        by simp

      have posv1: "eval_formula (Pred v\<^sub>1 ts\<^sub>1) vI fI pI'
        = pI1 v\<^sub>1 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>1)"
        unfolding eval_formula.simps pI'_def
        using \<open>v\<^sub>1 \<in> \<V>\<^sub>1\<close> v_not_in
        by auto

      have posv2: "eval_formula (Pred v\<^sub>2 ts\<^sub>2) vI fI pI'
        = pI2 v\<^sub>2 (map (\<lambda>t. eval_term t vI fI) ts\<^sub>2)"
        unfolding eval_formula.simps pI'_def
        using \<open>v\<^sub>2 \<in> \<V>\<^sub>2\<close> \<open>v\<^sub>2 \<notin> \<V> \<union> \<V>\<^sub>1\<close> v_not_in
        by auto

      show "eval_formula (formula_of_clause_list \<C>\<^sub>0) vI fI pI'"
        using posv posv1 posv2 simp2
        by auto
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>1)"

        have \<C>1_preds: "predicates_of_formula (formula_of_clause_list \<C>\<^sub>1)
          = predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1 \<union> {v\<^sub>1}"
          using predicates_of_clause_list[OF _ te_\<phi>1]
          by (simp add: Connective.hyps(1))

        have "\<V>\<^sub>1 \<union> {v\<^sub>1} = \<V>\<^sub>1"
          using Connective.hyps(1) te_\<phi>1 tseitin_fresh_var_in_fresh_var_set
          by fastforce

        have "x \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1"
          using \<C>1_preds assumption \<open>\<V>\<^sub>1 \<union> {v\<^sub>1} = \<V>\<^sub>1\<close>
          by auto

        have x_in_pred_of_\<phi>1: "x \<in> predicates_of_formula \<phi>\<^sub>1 \<Longrightarrow> pI1 x = pI' x" 
        proof -
          assume assumption: "x \<in> predicates_of_formula \<phi>\<^sub>1"

          have "x \<in> \<V>"
            using Connective.prems(2) assumption
            by fastforce
          have "v \<notin> \<V>"
            using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> fresh_spec
            by (metis Connective.hyps(1,2)
                Connective.prems(1) Un_iff finite_Un
                te_\<phi>1 te_\<phi>2 tseitin_finite_var_set)
          have "x \<noteq> v"
            using \<open>v \<notin> \<V>\<close> \<open>x \<in> \<V>\<close> 
            by auto
          have "\<V> \<inter> \<V>\<^sub>2 = {}"
            using tseitin_fresh_vars[OF _ _ _ te_\<phi>2]
            by (metis Connective.hyps(2)
                Connective.prems(1) Int_assoc Un_Int_eq(4)
                Un_commute \<C>1_preds fresh_spec
                inf_compl_bot_right infinite_Un
                predicates_of_formula_finite)
          have "x \<notin> \<V>\<^sub>2"
            using \<open>\<V> \<inter> \<V>\<^sub>2 = {}\<close> \<open>x \<in> \<V>\<close>
            by auto

          show ?thesis
            unfolding pI'_def
            by (simp add: \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>2\<close> assumption pI1_extends_pI)
        qed

        have x_in_\<V>1: "x \<in> \<V>\<^sub>1 \<Longrightarrow> pI1 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>1"

          have "v \<notin> \<V>\<^sub>1"
            unfolding \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by (metis Connective.hyps(2)
                Connective.prems(1) UnCI \<C>1_preds
                finite_Un fresh_spec
                predicates_of_formula_finite te_\<phi>2
                tseitin_finite_var_set)

          show ?thesis
            unfolding pI'_def
            using \<open>v \<notin> \<V>\<^sub>1\<close> \<open>x \<in> \<V>\<^sub>1\<close> 
            by auto
        qed

        show "pI1 x = pI' x"
          using \<open>x \<in> predicates_of_formula \<phi>\<^sub>1 \<union> \<V>\<^sub>1\<close> x_in_\<V>1 x_in_pred_of_\<phi>1 
          by auto
      next
        show "eval_formula (formula_of_clause_list \<C>\<^sub>1) vI fI pI1"
          by (simp add: pI1_model)
      qed
    next
      show "eval_formula (formula_of_clause_list \<C>\<^sub>2) vI fI pI'"
      proof (rule eval_formula_cong_wrt_predicate_evaluation[THEN iffD1])
        fix x
        assume assumption: "x \<in> predicates_of_formula (formula_of_clause_list \<C>\<^sub>2)"

        have \<C>2_preds: "predicates_of_formula (formula_of_clause_list \<C>\<^sub>2)
          = predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2 \<union> {v\<^sub>2}"
          using predicates_of_clause_list[OF _ te_\<phi>2]
          by (simp add: Connective.hyps(2))

        have "\<V>\<^sub>2 \<union> {v\<^sub>2} = \<V>\<^sub>2"
          using Connective.hyps(2) te_\<phi>2 tseitin_fresh_var_in_fresh_var_set
          by fastforce

        have "x \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2"
          using \<C>2_preds assumption \<open>\<V>\<^sub>2 \<union> {v\<^sub>2} = \<V>\<^sub>2\<close>
          by auto

        have x_in_pred_of_\<phi>2: "x \<in> predicates_of_formula \<phi>\<^sub>2 \<Longrightarrow> pI2 x = pI' x" 
        proof -
          assume assumption: "x \<in> predicates_of_formula \<phi>\<^sub>2"

          have "x \<in> \<V>"
            using Connective.prems(2) assumption
            by fastforce
          have "v \<notin> \<V>"
            using \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close> fresh_spec
            by (metis Connective.hyps(1,2)
                Connective.prems(1) Un_iff finite_Un
                te_\<phi>1 te_\<phi>2 tseitin_finite_var_set)
          have "x \<noteq> v"
            using \<open>v \<notin> \<V>\<close> \<open>x \<in> \<V>\<close> 
            by auto
          have "\<V> \<inter> \<V>\<^sub>1 = {}"
            using tseitin_fresh_vars[OF _ _ _ te_\<phi>1]
            by (simp add: Connective.hyps(1)
                Connective.prems(1) fresh_spec)
          have "x \<notin> \<V>\<^sub>1"
            using \<open>\<V> \<inter> \<V>\<^sub>1 = {}\<close> \<open>x \<in> \<V>\<close>
            by auto

          show ?thesis
            unfolding pI'_def
            by (simp add: \<open>x \<noteq> v\<close> \<open>x \<notin> \<V>\<^sub>1\<close> assumption pI2_extends_pI)
        qed

        have x_in_\<V>2: "x \<in> \<V>\<^sub>2 \<Longrightarrow> pI2 x = pI' x"
        proof -
          assume "x \<in> \<V>\<^sub>2"

          have "x \<notin> \<V>\<^sub>1"
            using fresh_spec
            by (meson PosPred all_not_in_conv
                tseitin.simps(1)
                tseitin_fresh_var_in_fresh_var_set)

          have "v \<notin> \<V>\<^sub>2"
            unfolding \<open>v = fresh (\<V> \<union> \<V>\<^sub>1 \<union> \<V>\<^sub>2)\<close>
            by (metis Connective.hyps(1)
                Connective.prems(1) UnCI \<C>2_preds
                finite_Un fresh_spec
                predicates_of_formula_finite te_\<phi>1
                tseitin_finite_var_set)

          show ?thesis
            unfolding pI'_def
            using \<open>v \<notin> \<V>\<^sub>2\<close> \<open>x \<in> \<V>\<^sub>2\<close> \<open>x \<notin> \<V>\<^sub>1\<close>
            by auto
        qed

        show "pI2 x = pI' x"
          using \<open>x \<in> predicates_of_formula \<phi>\<^sub>2 \<union> \<V>\<^sub>2\<close> x_in_\<V>2 x_in_pred_of_\<phi>2 
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
      using Connective.IH(1)[OF _ _ te_\<phi>1] v1_true
      by (metis Connective.prems(1,2)
          \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
          equalityE eval_formula.simps(2)
          eval_formula_formula_of_clause_list_append_iff
          eval_te2 formula.simps(207) subset_trans
          sup.coboundedI1)
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
      using Connective.IH(2)[OF _ _ te_\<phi>2] v2_true
      by (metis Connective.hyps(1)
          Connective.prems(1,2)
          \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
          eval_formula.simps(2)
          eval_formula_formula_of_clause_list_append_iff
          eval_te2 finite_UnI formula.simps(207)
          le_supE le_supI1 te_\<phi>1
          tseitin_finite_var_set)
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

  have \<phi>1_or_\<phi>2_true: "eval_formula \<phi>\<^sub>1 vI fI pI \<or> eval_formula \<phi>\<^sub>2 vI fI pI"
    using Connective.IH(1)[OF _ _ te_\<phi>1] Connective.IH(2)[OF _ _ te_\<phi>2] v1_or_v2_true
    by (metis Connective.hyps(1)
        Connective.prems(1,2)
        \<open>\<C> = \<C>\<^sub>0 @ \<C>\<^sub>1 @ \<C>\<^sub>2\<close>
        eval_formula.simps(2)
        eval_formula_formula_of_clause_list_append_iff
        eval_te2 finite_UnI formula.simps(208)
        le_supE le_supI1 te_\<phi>1
        tseitin_finite_var_set)

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
      using tseitin_spec[OF _ \<open>is_nnf \<phi>\<close> \<open>finite \<V>\<close> \<open>predicates_of_formula \<phi> \<subseteq> \<V>\<close> tseitin]
      using fresh_spec 
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
        [OF _ \<open>is_nnf \<phi>\<close> \<open>finite \<V>\<close> \<open>predicates_of_formula \<phi> \<subseteq> \<V>\<close> tseitin te_pI]
      by (simp add: fresh_spec)
    show "?LHS"
      using eval_\<phi>
      by auto
  qed
qed

section \<open>Number of Introduced Fresh Variables\<close>

primrec branches :: "('v, 'f, 'p) formula \<Rightarrow> nat" where
  "branches T = 0" |
  "branches F = 0" |
  "branches (Pred _ _) = 0" |
  "branches (Equal _ _) = 0" |
  "branches (Not \<phi>) = Suc (branches \<phi>)" |
  "branches (And \<phi>\<^sub>1 \<phi>\<^sub>2) = Suc (branches \<phi>\<^sub>1 + branches \<phi>\<^sub>2)" |
  "branches (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Suc (branches \<phi>\<^sub>1 + branches \<phi>\<^sub>2)" |
  "branches (Forall _ \<phi>) = Suc (branches \<phi>)" |
  "branches (Exists _ \<phi>) = Suc (branches \<phi>)"

lemma tseitin_card_vars:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>"
  fixes \<phi> :: "('v, 'f, 'p) formula"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  assumes "finite \<V>" and "is_nnf \<phi>"
  shows "card \<V>' = branches \<phi>"
  sorry

theorem tseitin_expansion_card_vars:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>"
  assumes "is_nnf \<phi>"
  shows "card (predicates_of_formula (tseitin_expansion fresh \<phi>)) =
    card (predicates_of_formula \<phi>) + branches \<phi>"
  sorry



(**)

(*
lemma
  fixes \<phi> :: "('v, 'f, 'p) formula"
  assumes "is_nnf \<phi>"
  assumes tseitin: "tseitin fresh \<V> \<phi> = (v, ts, \<C>, \<V>')"
  shows
    tseitin_generated_var: "v \<in> predicates_of_formula \<phi> \<union> \<V>'" and
    tseitin_generated_vars: "insert v (\<Union>C \<in> set \<C>. fst ` atom ` set C) = predicates_of_formula \<phi> \<union> \<V>'"
  unfolding atomize_conj
  sorry
*)

(*
lemma formula_of_clause_eq_fold_Or:
  "formula_of_clause C = fold Or (map formula_of_literal C) F"
  by (metis (no_types, lifting) ext comp_apply
      fold_map formula_of_clause_def)
*)

(*
lemma formula_of_clause_list_eq_fold_And:
  "formula_of_clause_list Cs = fold And (map formula_of_clause Cs) T"
  by (metis (no_types, lifting) ext comp_apply
      fold_map formula_of_clause_list_def)
*)

(*
lemma eval_formula_fold_And_iff:
  "eval_formula (fold And xs \<phi>) vI fI pI \<longleftrightarrow>
    eval_formula (fold And xs T) vI fI pI \<and> eval_formula \<phi> vI fI pI"
  sorry
*)

(*
lemma eval_formula_fold_And_append_iff:
  "eval_formula (fold And (xs @ ys) \<phi>) vI fI pI \<longleftrightarrow>
    eval_formula (fold And xs T) vI fI pI \<and>
    eval_formula (fold And ys T) vI fI pI \<and>
    eval_formula \<phi> vI fI pI"
  sorry
*)

(*
lemma predicates_of_formula_fold_Or_map_formula_of_literal:
  "predicates_of_formula (fold Or (map formula_of_literal C) \<phi>) =
  fst ` atom ` set C \<union> predicates_of_formula \<phi>"
  sorry

lemma predicates_of_formula_of_clause:
  "predicates_of_formula (formula_of_clause C) = fst ` atom ` set C"
  sorry

lemma predicates_of_formula_fold_And_map_formula_of_clause:
  "predicates_of_formula (fold And (map formula_of_clause Cs) \<phi>) =
  (\<Union> C \<in> set Cs. predicates_of_formula (formula_of_clause C)) \<union> predicates_of_formula \<phi>"
  sorry

lemma predicates_of_formula_of_clause_list:
  "predicates_of_formula (formula_of_clause_list Cs) =
    (\<Union> C \<in> set Cs. predicates_of_formula (formula_of_clause C))"
  sorry
*)

end