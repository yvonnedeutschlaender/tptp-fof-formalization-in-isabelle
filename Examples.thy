theory Examples
  imports FOF_Base
begin

section \<open>tautology\<close>

definition f1 :: "(string, string, string) formula" where
"f1 = Or (Not (Pred ''A'' [Var ''x''])) (Pred ''A'' [Var ''x''])"

definition f2 :: "(string, string, string) formula" where
"f2 = Forall ''x'' (Equal (Fun ''f'' [Var ''x'']) (Fun  ''f'' [Var ''x'']))"

definition f3 :: "(string, string, string) formula" where
"f3 = And (Imp (Pred ''A'' []) (Pred ''A'' [])) (Imp (Pred ''B'' []) (Pred ''B'' []))"

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
"f5 = Equiv (Pred ''A'' [Fun ''f'' [Var ''x'']]) (Pred ''B'' [Fun ''f'' [Var ''x'']])"

definition f6 :: "(string, string, string) formula" where
"f6 = Forall ''x'' (Pred ''A'' [Var ''x''])"

definition f7 :: "(string, string, string) formula" where
"f7 = And (Forall ''x'' (Exists ''y'' (Equal (Var ''x'') (Var ''y'')))) (Pred ''A'' [Var ''z''])"

definition f8 :: "(string, string, string) formula" where
"f8 = Or (And (Pred ''A'' []) (Pred ''B'' [])) (And (Pred ''A'' []) (Not (Pred ''B'' [])))"

definition f9 :: "(string, string, string) formula" where
"f9 = Imp (Pred ''B'' []) (Pred ''A'' [])"

definition f10 :: "(string, string, string) formula" where
"f10 = Not (And (Pred ''A'' []) (Pred ''B'' []))"

lemma f5_is_satisfiable: "\<exists>vI fI pI. eval_formula f5 vI fI pI" 
  unfolding f5_def Equiv_def Imp_def
  by auto

lemma f5_is_not_tautology: "\<exists>pI vI fI. \<not> eval_formula f5 vI fI pI"
proof (rule exI) 
  let ?pI = "\<lambda> p args. (if p = ''A'' then True else False)"
  show "\<exists>vI fI. \<not> eval_formula f5 vI fI ?pI"
    unfolding f5_def Equiv_def Imp_def
    by simp
qed

lemma f6_is_satisfiable: "\<exists>vI pI. eval_formula f6 vI fI pI" 
  unfolding f6_def
  by auto

lemma f6_is_not_tautology: "\<exists>vI pI. \<not> eval_formula f6 vI fI pI"
  unfolding f6_def
  by auto

lemma f7_is_satisfiable: "\<exists>vI pI. eval_formula f7 vI fI pI" 
  unfolding f7_def
  by auto

lemma f7_is_not_tautology: "\<exists>vI pI. \<not> eval_formula f7 vI fI pI"
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
  let ?pI = "\<lambda> p args. (if p = ''B'' then True else False)"
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
"f11 = And (Not (Pred ''A'' [Var ''x''])) (Pred ''A'' [Var ''x''])"

definition f12 :: "(string, string, string) formula" where
"f12 = Forall ''x'' (Not (Equal (Var ''x'') (Var ''x'')))"

definition f13 :: "(string, string, string) formula" where
"f13 = And (Pred ''A'' []) (And (Pred ''B'' []) (Not (Or (Pred ''A'' []) (Pred ''B'' []))))"

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

end