theory FOF_Examples
  imports FOF_Base FOF_Simplify FOF_Tseitin
begin

section \<open>eval_formula\<close>

section \<open>tautology\<close>

definition f1 :: "(string, string, string) formula" where
"f1 = Or (Not (Pred ''a'' [Fun ''c'' []])) (Pred ''a'' [Fun ''c'' []])"

definition f2 :: "(string, string, string) formula" where
"f2 = Forall ''x'' (Equal (Fun ''f'' [Var ''x'']) (Fun  ''f'' [Var ''x'']))"

definition f3 :: "(string, string, string) formula" where
"f3 = Or (Imp (Pred ''a'' []) (Pred ''b'' [])) (Imp (Pred ''b'' []) (Pred ''a'' []))"

definition f4 :: "(string, string, string) formula" where
"f4 = Exists ''x'' (Exists ''y'' 
      (Or (Equal (Var ''x'') (Var ''y'')) (Not (Equal (Var ''x'') (Var ''y'')))))"

lemma f1_is_tautology:  "eval_formula f1 vI fI pI"
  unfolding f1_def
  by simp

lemma f2_is_tautology:  "eval_formula f2 vI fI pI"
  unfolding f2_def
  by simp

lemma f3_is_tautology:  "eval_formula f3 vI fI pI"
  unfolding f3_def Imp_def
  by simp

lemma f4_is_tautology:  "eval_formula f4 vI fI pI"
  unfolding f4_def
  by simp

section \<open>satisfiable\<close>

definition f5 :: "(string, string, string) formula" where
"f5 = Equiv (Pred ''a'' []) (Equiv (Pred ''b'' []) (Pred ''c'' []))"

definition f6 :: "(string, string, string) formula" where
"f6 = Forall ''x'' (Pred ''a'' [Var ''x''])"

definition f7 :: "(string, string, string) formula" where
"f7 = And (Forall ''x'' (Exists ''y'' (Equal (Var ''x'') (Var ''y'')))) (Pred ''a'' [])"

definition f8 :: "(string, string, string) formula" where
"f8 = And (Pred ''a''  []) (Or (Pred ''b'' []) (Not (Pred ''c'' [])))"

definition f9 :: "(string, string, string) formula" where
"f9 = Imp (Pred ''a'' []) (Pred ''b'' [])"

definition f10 :: "(string, string, string) formula" where
"f10 = Not (Pred ''a'' [Fun ''c'' []])"

lemma f5_is_satisfiable: "\<exists>vI fI pI. eval_formula f5 vI fI pI" 
  unfolding f5_def Equiv_def Imp_def
  by auto

lemma f5_is_not_tautology: "\<exists>pI vI fI. \<not> eval_formula f5 vI fI pI"
proof (rule exI) 
  let ?pI = "\<lambda> p args. (if p = ''b'' then False else True)"
  show "\<exists>vI fI. \<not> eval_formula f5 vI fI ?pI"
    unfolding f5_def Equiv_def Imp_def
    by simp
qed

lemma "a \<longleftrightarrow> (b \<longleftrightarrow> c) = 
  (\<not>a \<or> ((\<not>b \<or> c) \<and> (\<not>c \<or> b))) \<and> (\<not>((\<not>b \<or> c) \<and> (\<not>c \<or> b)) \<or> a)"
  by satx

lemma f6_is_satisfiable: "\<exists>pI. eval_formula f6 vI fI pI" 
  unfolding f6_def
  by auto

lemma f6_is_not_tautology: "\<exists>pI. \<not> eval_formula f6 vI fI pI"
  unfolding f6_def
  by auto

lemma f7_is_satisfiable: "\<exists>pI. eval_formula f7 vI fI pI" 
  unfolding f7_def
  by auto

lemma f7_is_not_tautology: "\<exists>pI. \<not> eval_formula f7 vI fI pI"
  unfolding f7_def
  by auto

lemma f8_is_satisfiable: "\<exists>pI. eval_formula f8 vI fI pI" 
  unfolding f8_def
  by auto

lemma f8_is_not_tautology: "\<exists>pI. \<not> eval_formula f8 vI fI pI"
  unfolding f8_def
  by auto

lemma f9_is_satisfiable: "\<exists>pI. eval_formula f9 vI fI pI" 
  unfolding f9_def Imp_def
  by auto

lemma f9_is_not_tautology: "\<exists>pI. \<not> eval_formula f9 vI fI pI"
proof (rule exI) 
  let ?pI = "\<lambda> p args. (if p = ''a'' then True else False)"
  show "\<not> eval_formula f9 vI fI ?pI"
    unfolding f9_def Imp_def
    by simp
qed

lemma f10_is_satisfiable: "\<exists>pI. eval_formula f10 vI fI pI" 
  unfolding f10_def
  by auto

lemma f10_is_not_tautology: "\<exists>pI. \<not> eval_formula f10 vI fI pI"
  unfolding f10_def
  by auto

section \<open>unsatisfiable\<close>

definition f11 :: "(string, string, string) formula" where
"f11 = And (Not (Pred ''a'' [])) (Pred ''a'' [])"

definition f12 :: "(string, string, string) formula" where
"f12 = Forall ''v'' (Not (Equal (Var ''v'') (Var ''v'')))"

definition f13 :: "(string, string, string) formula" where
"f13 = And (Pred ''a'' []) (And (Pred ''b'' []) (Not (Or (Pred ''a'' []) (Pred ''b'' []))))"

definition f14 :: "(string, string, string) formula" where
"f14 = Exists ''x'' (Exists ''y'' 
      (And (Equal (Var ''x'') (Var ''y'')) (Not (Equal (Var ''x'') (Var ''y'')))))"

lemma unsatisfiable_f11: "\<not> eval_formula f11 vI fI pI"
  unfolding f11_def
  by simp

lemma unsatisfiable_f12: "\<not> eval_formula f12 vI fI pI"
  unfolding f12_def
  by simp

lemma unsatisfiable_f13: "\<not> eval_formula f13 vI fI pI"
  unfolding f13_def
  by simp

lemma unsatisfiable_f14: "\<not> eval_formula f14 vI fI pI"
  unfolding f14_def
  by simp


section \<open>simp_formula\<close>

definition f15 :: "(string, string, string) formula" where
"f15 = Forall ''v'' (Or (And F (Pred ''a'' [])) (Not (Not (Pred ''b'' []))))"

definition f16 :: "(string, string, string) formula" where
"f16 = And (Pred ''a'' []) (Equal (Fun ''c1'' []) (Fun ''c2'' []))"

lemma "eval_formula f15 vI fI pI = eval_formula (simp_formula f15) vI fI pI"
  by (simp add: eval_formula_simp_formula_equiv_eval_formula)

lemma "eval_formula f16 vI fI pI = eval_formula (simp_formula f16) vI fI pI"
  by (simp add: eval_formula_simp_formula_equiv_eval_formula)

lemma "simp_formula f16 = f16"
  unfolding f16_def
  by simp


section \<open>tseitin_expansion\<close>

definition fresh :: "nat set \<Rightarrow> nat" where
  "fresh \<Sigma> = (if \<Sigma> = {} then 0 else Max \<Sigma> + 1)"

definition f17 :: "(string, string, nat) formula" where
"f17 = (Pred 0 [])"

definition f18 :: "(string, string, nat) formula" where
"f18 = (Not (Pred 0 []))"

lemma "(\<exists>pI. eval_formula f17 vI fI pI) \<longleftrightarrow> 
       (\<exists>pI. eval_formula (tseitin_expansion fresh f17) vI fI pI)"
proof -
  have fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>" 
    unfolding fresh_def
    by (metis Max.coboundedI add.commute
        add_cancel_left_left all_not_in_conv le0
        le_add_same_cancel1 order_antisym_conv
        zero_neq_one)

  have "is_nnf f17"
    unfolding f17_def
    by (simp add: PosPred)

  show ?thesis
    using tseitin_expansion_equisat[OF fresh_spec \<open>is_nnf f17\<close>]
    by blast
qed

lemma "(\<exists>pI. eval_formula f18 vI fI pI) \<longleftrightarrow> 
       (\<exists>pI. eval_formula (tseitin_expansion fresh f18) vI fI pI)"
proof -
  have fresh_spec: "\<And>\<V>. finite \<V> \<Longrightarrow> fresh \<V> \<notin> \<V>" 
    unfolding fresh_def
    by (metis Max.coboundedI add.commute
        add_cancel_left_left all_not_in_conv le0
        le_add_same_cancel1 order_antisym_conv
        zero_neq_one)

  have "is_nnf f18"
    unfolding f18_def
    by (simp add: NegPred)

  show ?thesis
    using tseitin_expansion_equisat[OF fresh_spec \<open>is_nnf f18\<close>]
    by blast
qed

end