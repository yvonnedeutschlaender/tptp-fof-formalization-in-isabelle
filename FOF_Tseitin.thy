theory FOF_Tseitin
  imports Main FOF_Base
begin

inductive is_prop :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Prop: "is_prop (Pred P [])" |
And: "is_prop f1 \<Longrightarrow> is_prop f2 \<Longrightarrow> is_prop (And f1 f2)" |
Or: "is_prop f1 \<Longrightarrow> is_prop f2 \<Longrightarrow> is_prop (Or f1 f2)" |
Not: "is_prop f \<Longrightarrow> is_prop (Not f)"

inductive is_literal :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
True: "is_literal T" |
False: "is_literal F" |
Prop: "is_literal (Pred p args)" |
Equal: "is_literal (Equal t1 t2)" |
NProp: "is_literal (Not (Pred p args))" |
NEqual: "is_literal (Not (Equal t1 t2))" 

inductive is_nnf :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_literal f \<Longrightarrow> is_nnf f" |
And: "is_nnf f1 \<Longrightarrow> is_nnf f2 \<Longrightarrow> is_nnf (And f1 f2)" |
Or: "is_nnf f1 \<Longrightarrow> is_nnf f2 \<Longrightarrow> is_nnf (Or f1 f2)" |
Forall: "is_nnf f \<Longrightarrow> is_nnf (Forall v f)" |
Exists: "is_nnf f \<Longrightarrow> is_nnf (Exists v f)"

(*
inductive is_clause :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_literal f \<Longrightarrow> is_clause f" |
Or: "is_literal f1 \<Longrightarrow> is_literal f2 \<Longrightarrow> is_clause (Or f1 f2)"

inductive is_cnf :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_literal f \<Longrightarrow> is_cnf f" |
And: "is_clause f1 \<Longrightarrow> is_clause f2 \<Longrightarrow> is_cnf (And f1 f2)" 
*)

type_synonym 'p fresh = "'p set \<Rightarrow> 'p"
type_synonym ('v, 'f, 'p) tseitin_asgnm = "'p \<times> ('v, 'f, 'p) formula"
type_synonym ('v, 'f, 'p) tseitin_asgnm_conv = "('v, 'f, 'p) formula \<times> ('v, 'f, 'p) formula"

fun tseitin_occup_var :: "('v, 'f, 'p) formula \<Rightarrow> 'p set" where
"tseitin_occup_var (Pred p []) = {p}" |
"tseitin_occup_var (Not (Pred p [])) = {p}" |
"tseitin_occup_var (And f1 f2) = tseitin_occup_var f1 \<union> tseitin_occup_var f2" |
"tseitin_occup_var (Or f1 f2) = tseitin_occup_var f1 \<union> tseitin_occup_var f2" |
"tseitin_occup_var _ = {}"

fun tseitin_list :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula list" where
"tseitin_list (Pred p []) = []" |
"tseitin_list (Not (Pred p [])) = [Not (Pred p [])]" |
"tseitin_list (And f1 f2) = [And f1 f2] @ tseitin_list f1 @ tseitin_list f2" |
"tseitin_list (Or f1 f2) = [Or f1 f2] @ tseitin_list f1 @ tseitin_list f2" |
"tseitin_list _ = []"

definition tseitin_fresh_var :: "'p fresh \<Rightarrow> 'p set \<Rightarrow> 'p set \<times> 'p" where
"tseitin_fresh_var \<xi> \<Sigma> = (let \<tau> = \<xi> \<Sigma> in (\<Sigma> \<union> {\<tau>}, \<tau>))"

definition tseitin_assign_var :: "'p \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm" where
"tseitin_assign_var \<tau> f = (\<tau>, f)"

fun tseitin_list_asgnm :: 
"'p fresh \<Rightarrow> 'p set \<Rightarrow> ('v, 'f, 'p) formula list \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list" where
"tseitin_list_asgnm \<xi> \<Sigma> [] = []" |
"tseitin_list_asgnm \<xi> \<Sigma> (f # fs) = 
  (let fresh_var = tseitin_fresh_var \<xi> \<Sigma>;
       assign_var = tseitin_assign_var (snd fresh_var) f
    in [assign_var] @ tseitin_list_asgnm \<xi> (fst fresh_var) fs)"

definition tseitin_conv_var :: "'p \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_conv_var \<tau> = Pred \<tau> []"

fun tseitin_subst_formula ::
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_subst_formula f [] = f" |
"tseitin_subst_formula f (a # as) = 
  (if (f = snd a) 
   then tseitin_conv_var (fst a)
   else tseitin_subst_formula f as)"

fun tseitin_subst_subformula :: 
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_subst_subformula f [] = f" |
"tseitin_subst_subformula (Pred p []) _ = Pred p []" |
"tseitin_subst_subformula (Not (Pred p [])) _ = Not (Pred p [])" |
"tseitin_subst_subformula (And f1 f2) as = 
  (let f1_subst = tseitin_subst_formula f1 as;
       f2_subst = tseitin_subst_formula f2 as
    in And f1_subst f2_subst)" |
"tseitin_subst_subformula (Or f1 f2) as =
  (let f1_subst = tseitin_subst_formula f1 as;
       f2_subst = tseitin_subst_formula f2 as
    in Or f1_subst f2_subst)" |
"tseitin_subst_subformula f _ = f"

fun tseitin_list_subst :: "('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list" where
"tseitin_list_subst [] = []" |
"tseitin_list_subst ((\<tau>, f) # as) =
  (let f' = tseitin_subst_subformula f as
    in (\<tau>, f') # tseitin_list_subst as)"

fun tseitin_conv_asgnm :: 
"('v, 'f, 'p) tseitin_asgnm \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm_conv" where
"tseitin_conv_asgnm (\<tau>, f) = (tseitin_conv_var \<tau>, f)"

fun tseitin_simp_formula :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_simp_formula (Pred p []) = Pred p []" |
"tseitin_simp_formula (And \<phi>1 \<phi>2) = And (tseitin_simp_formula \<phi>1) (tseitin_simp_formula \<phi>2)" |
"tseitin_simp_formula (Or \<phi>1 \<phi>2) = Or (tseitin_simp_formula \<phi>1) (tseitin_simp_formula \<phi>2)" |
"tseitin_simp_formula (Not \<phi>) = (case tseitin_simp_formula \<phi> of
  Pred p [] \<Rightarrow> Not (Pred p []) |
  Not (Pred p []) \<Rightarrow> Pred p []
)" |
"tseitin_simp_formula \<phi> = \<phi>"

fun tseitin_equiv_binding :: 
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_equiv_binding (Pred _ []) l r = And l r" |
"tseitin_equiv_binding (Not (Pred _ [])) l r = And l r" |
"tseitin_equiv_binding (And _ _) l r =
  (let l' = distribute_formula l;
       r' = demorg_formula r
    in And l' r')" |
"tseitin_equiv_binding (Or _ _) l r =
  (let r' = demorg_formula r;
       r'' = distribute_formula r'
    in And l r'')" |
"tseitin_equiv_binding _ l r = And l r"

fun tseitin_transform_to_clause :: "('v, 'f, 'p) tseitin_asgnm_conv \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_transform_to_clause (\<tau>_conv, \<phi>) =
  (let l = Imp \<tau>_conv \<phi>;
       r = Imp \<phi> \<tau>_conv;
       equiv = tseitin_equiv_binding \<phi> l r
    in tseitin_simp_formula equiv
)"

definition tseitin_get_head_var :: 
"('v, 'f, 'p) tseitin_asgnm_conv list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_get_head_var as = (if as \<noteq> [] then fst (hd as) else T)"

definition tseitin_conjunct_clauses :: 
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_conjunct_clauses start cls = fold And cls start"

fun tseitin_expansion :: "'p fresh \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_expansion \<xi> \<phi> = 
  (let \<Sigma> = tseitin_occup_var \<phi>;
       list = tseitin_list \<phi>;
       list_asgnm = tseitin_list_asgnm \<xi> \<Sigma> list;
       list_subst = tseitin_list_subst list_asgnm;
       list_conv = map tseitin_conv_asgnm list_subst;
       list_clause = map tseitin_transform_to_clause list_conv;
       head_var = tseitin_get_head_var list_conv;
       tseitin_\<phi>_cnf = tseitin_conjunct_clauses head_var list_clause
    in tseitin_\<phi>_cnf
)"

(*TODO:
theorem
  fixes fresh :: "'p set \<Rightarrow> 'p" and \<phi> :: "('v, 'f, 'p) formula"
  assumes "\<And>\<P>. finite \<P> \<Longrightarrow> fresh \<P> \<notin> \<P>"
  assumes "is_nnf \<phi>"
  assumes "is_prop \<phi>"
  shows "(\<exists>pI. eval_formula (tseitin_expansion fresh \<phi>) vI fI pI) \<longleftrightarrow> (\<exists>pI. eval_formula \<phi> vI fI pI)"
sorry
*)
end