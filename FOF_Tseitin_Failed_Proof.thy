theory FOF_Tseitin_Failed_Proof
  imports Main FOF_Base FOF_Simplify
begin

inductive is_prop :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Prop: "is_prop (Pred p [])" |
And: "is_prop \<phi>1 \<Longrightarrow> is_prop \<phi>2 \<Longrightarrow> is_prop (And \<phi>1 \<phi>2)" |
Or: "is_prop \<phi>1 \<Longrightarrow> is_prop \<phi>2 \<Longrightarrow> is_prop (Or \<phi>1 \<phi>2)" |
Not: "is_prop \<phi> \<Longrightarrow> is_prop (Not \<phi>)"

inductive is_prop_literal :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Prop: "is_prop_literal (Pred p [])" |
NProp: "is_prop_literal (Not (Pred p []))"

inductive is_prop_nnf :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Prop: "is_prop_nnf (Pred p [])" |
NProp: "is_prop_nnf (Not (Pred p []))" |
And: "is_prop_nnf \<phi>1 \<Longrightarrow> is_prop_nnf \<phi>2 \<Longrightarrow> is_prop_nnf (And \<phi>1 \<phi>2)" |
Or: "is_prop_nnf \<phi>1 \<Longrightarrow> is_prop_nnf \<phi>2 \<Longrightarrow> is_prop_nnf (Or \<phi>1 \<phi>2)"

inductive is_prop_clause :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_prop_literal \<phi> \<Longrightarrow> is_prop_clause \<phi>" |
Or: "is_prop_literal \<phi>1 \<Longrightarrow> is_prop_literal \<phi>2 \<Longrightarrow> is_prop_clause (Or \<phi>1 \<phi>2)"

inductive is_cnf :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_prop_literal \<phi> \<Longrightarrow> is_cnf \<phi>" |
And: "is_prop_clause \<phi>1 \<Longrightarrow> is_prop_clause \<phi>2 \<Longrightarrow> is_cnf (And \<phi>1 \<phi>2)" 

type_synonym 'p fresh = "'p set \<Rightarrow> 'p"
type_synonym ('v, 'f, 'p) tseitin_asgnm = "'p \<times> ('v, 'f, 'p) formula"

fun tseitin_occup_var :: "('v, 'f, 'p) formula \<Rightarrow> 'p set" where
"tseitin_occup_var (Pred p []) = {p}" |
"tseitin_occup_var (Not (Pred p [])) = {p}" |
"tseitin_occup_var (And \<phi>1 \<phi>2) = tseitin_occup_var \<phi>1 \<union> tseitin_occup_var \<phi>2" |
"tseitin_occup_var (Or \<phi>1 \<phi>2) = tseitin_occup_var \<phi>1 \<union> tseitin_occup_var \<phi>2" |
"tseitin_occup_var _ = {}"

fun tseitin_list :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula list" where
"tseitin_list (Pred p []) = []" |
"tseitin_list (Not (Pred p [])) = [Not (Pred p [])]" |
"tseitin_list (And \<phi>1 \<phi>2) = And \<phi>1 \<phi>2 # tseitin_list \<phi>1 @ tseitin_list \<phi>2" |
"tseitin_list (Or \<phi>1 \<phi>2) = Or \<phi>1 \<phi>2 # tseitin_list \<phi>1 @ tseitin_list \<phi>2" |
"tseitin_list _ = []"

definition tseitin_fresh_var :: "'p fresh \<Rightarrow> 'p set \<Rightarrow> 'p \<times> 'p set" where
"tseitin_fresh_var \<xi> \<Sigma> = (let \<tau> = \<xi> \<Sigma> in (\<tau>, \<Sigma> \<union> {\<tau>}))"

fun tseitin_list_asgnm :: 
"'p fresh \<Rightarrow> 'p set \<Rightarrow> ('v, 'f, 'p) formula list \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list" where
"tseitin_list_asgnm \<xi> \<Sigma> [] = []" |
"tseitin_list_asgnm \<xi> \<Sigma> (\<phi> # \<phi>s) = 
  (let fresh_var = tseitin_fresh_var \<xi> \<Sigma>;
       assign_var = ((fst fresh_var), \<phi>)
    in assign_var # tseitin_list_asgnm \<xi> (snd fresh_var) \<phi>s)"

fun tseitin_subst_formula ::
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_subst_formula \<phi> [] = \<phi>" |
"tseitin_subst_formula \<phi> (a # as) = 
  (if (\<phi> = snd a) 
   then Pred (fst a) []
   else tseitin_subst_formula \<phi> as)"

fun tseitin_subst_subformula :: 
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_subst_subformula \<phi> [] = \<phi>" |
"tseitin_subst_subformula (Pred p []) _ = Pred p []" |
"tseitin_subst_subformula (Not (Pred p [])) _ = Not (Pred p [])" |
"tseitin_subst_subformula (And \<phi>1 \<phi>2) as = 
  (let \<phi>1_subst = tseitin_subst_formula \<phi>1 as;
       \<phi>2_subst = tseitin_subst_formula \<phi>2 as
    in And \<phi>1_subst \<phi>2_subst)" |
"tseitin_subst_subformula (Or \<phi>1 \<phi>2) as =
  (let \<phi>1_subst = tseitin_subst_formula \<phi>1 as;
       \<phi>2_subst = tseitin_subst_formula \<phi>2 as
    in Or \<phi>1_subst \<phi>2_subst)" |
"tseitin_subst_subformula \<phi> _ = \<phi>"

fun tseitin_list_subst :: "('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list" where
"tseitin_list_subst [] = []" |
"tseitin_list_subst ((\<tau>, \<phi>) # as) =
  (let \<phi>' = tseitin_subst_subformula \<phi> as
    in (\<tau>, \<phi>') # tseitin_list_subst as)"

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

fun tseitin_transform_to_clause :: "('v, 'f, 'p) tseitin_asgnm \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_transform_to_clause (\<tau>, \<phi>) =
  (let \<tau>_conv = Pred \<tau> [];
       l = Imp \<tau>_conv \<phi>;
       r = Imp \<phi> \<tau>_conv;
       equiv = tseitin_equiv_binding \<phi> l r
    in simp_formula equiv
)"

fun tseitin_get_head_var :: 
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> 'p" where
"tseitin_get_head_var (Pred p []) [] = p" |
"tseitin_get_head_var _ as = fst (hd as)"

fun tseitin_get_new_vars :: "('v, 'f, 'p) tseitin_asgnm list \<Rightarrow> 'p set" where
"tseitin_get_new_vars [] = {}" |
"tseitin_get_new_vars (a # as) = {fst a} \<union> tseitin_get_new_vars as"

definition tseitin_decompose ::
"'p fresh \<Rightarrow> 'p set \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> 'p \<times> ('v, 'f, 'p) formula list \<times> 'p set" where
"tseitin_decompose \<xi> \<Sigma> \<phi> = 
  (let list = tseitin_list \<phi>;
       list_asgnm = tseitin_list_asgnm \<xi> \<Sigma> list;
       list_subst = tseitin_list_subst list_asgnm;
       list_clause = map tseitin_transform_to_clause list_subst;
       head_var = tseitin_get_head_var \<phi> list_asgnm;
       new_vars = tseitin_get_new_vars list_asgnm
    in (head_var, list_clause, new_vars)
)"

fun tseitin_conjunct_clauses :: 
"'p \<Rightarrow> ('v, 'f, 'p) formula list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_conjunct_clauses p [] = (Pred p [])" |
"tseitin_conjunct_clauses p cls = fold And cls (Pred p [])"

definition tseitin_expansion :: "'p fresh \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_expansion \<xi> \<phi> = 
  (let (\<tau>, \<C>, \<Sigma>') = tseitin_decompose \<xi> (tseitin_occup_var \<phi>) \<phi>
    in tseitin_conjunct_clauses \<tau> \<C>
)"

lemma tseitin_Prop_empty_args:
  fixes fresh :: "'p set \<Rightarrow> 'p"
  assumes "\<And>\<P>. finite \<P> \<Longrightarrow> fresh \<P> \<notin> \<P>"
  shows "tseitin_expansion fresh (Pred p []) = Pred p []" 
proof -
  have list_asgnm: "tseitin_list_asgnm fresh {p} [] = []"
    by simp
  have to_clause: "map tseitin_transform_to_clause [] = []"
    by simp
  have decompose: "tseitin_decompose fresh {p} (Pred p []) = (p, [], {})"
    unfolding tseitin_decompose_def Let_def tseitin_list.simps list_asgnm
              tseitin_get_head_var.simps tseitin_list_subst.simps
              to_clause tseitin_get_new_vars.simps
    by simp
  show ?thesis
    unfolding tseitin_expansion_def tseitin_occup_var.simps decompose Let_def
    by simp
qed 

end