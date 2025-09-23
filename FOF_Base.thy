theory FOF_Base
  imports Main
begin

datatype ('v, 'f) fof_term =
Var 'v |
Fun 'f "('v, 'f) fof_term list"

type_synonym ('v, 'd) I_var = "'v \<Rightarrow> 'd"
type_synonym ('f, 'd) I_fun = "'f \<Rightarrow> 'd list \<Rightarrow> 'd"

fun eval_term :: "('v, 'f) fof_term \<Rightarrow> ('v, 'd) I_var \<Rightarrow> ('f, 'd) I_fun \<Rightarrow> 'd" where
"eval_term (Var x) vI _ = vI x" |
"eval_term (Fun f args) vI fI = fI f (map (\<lambda>t. eval_term t vI fI) args)"

datatype ('v, 'f, predicates_of_formula: 'p) formula =
Pred 'p "('v, 'f) fof_term list" |
And "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Or "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Not "('v, 'f, 'p) formula" |
Equal "('v, 'f) fof_term" "('v, 'f) fof_term" |
Forall 'v "('v, 'f, 'p) formula" |
Exists 'v "('v, 'f, 'p) formula" |
T | 
F

type_synonym ('p, 'd) I_pred = "'p \<Rightarrow> 'd list \<Rightarrow> bool"

fun eval_formula ::
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'd) I_var \<Rightarrow> ('f, 'd) I_fun \<Rightarrow> ('p, 'd) I_pred \<Rightarrow> bool" where
"eval_formula (Pred p args) vI fI pI = pI p (map (\<lambda>t. eval_term t vI fI) args) " |
"eval_formula (And f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) \<and> (eval_formula f2 vI fI pI))" |
"eval_formula (Or f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) \<or> (eval_formula f2 vI fI pI))" |
"eval_formula (Not f) vI fI pI = (\<not>(eval_formula f vI fI pI))" |
"eval_formula (Equal t1 t2) vI fI pI = ((eval_term t1 vI fI) = (eval_term t2 vI fI))" |
"eval_formula (Forall v f) vI fI pI = (\<forall>x. eval_formula f (vI(v := x)) fI pI)" |
"eval_formula (Exists v f) vI fI pI = (\<exists>x. eval_formula f (vI(v := x)) fI pI)" |
"eval_formula T _ _ _ = True" |
"eval_formula F _ _ _ = False"

definition Imp :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"Imp f1 f2 = Or (Not f1) f2"

definition Equiv :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"Equiv f1 f2 = And (Imp f1 f2) (Imp f2 f1)"

definition Xor :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"Xor f1 f2 = Or (And (Not f1) f2) (And f1 (Not f2))"

fun distribute_formula :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"distribute_formula (Pred p args) = Pred p args" |
"distribute_formula (And \<phi> \<psi>) = (case (distribute_formula \<phi>, distribute_formula \<psi>) of
  (Or \<phi>1 \<phi>2, \<psi>') \<Rightarrow> Or (And \<phi>1 \<psi>') (And \<phi>2 \<psi>') |
  (\<phi>', Or \<psi>1 \<psi>2) \<Rightarrow> Or (And \<phi>' \<psi>1) (And \<phi>' \<psi>2) |
  (\<phi>', \<psi>') \<Rightarrow> And \<phi>' \<psi>'
)" |
"distribute_formula (Or \<phi> \<psi>) = (case (distribute_formula \<phi>, distribute_formula \<psi>) of
  (And \<phi>1 \<phi>2, \<psi>') \<Rightarrow> And (Or \<phi>1 \<psi>') (Or \<phi>2 \<psi>') |
  (\<phi>', And \<psi>1 \<psi>2) \<Rightarrow> And (Or \<phi>' \<psi>1) (Or \<phi>' \<psi>2) |
  (\<phi>', \<psi>') \<Rightarrow> Or \<phi>' \<psi>'
)" |
"distribute_formula (Not \<phi>) = Not (distribute_formula \<phi>)" |
"distribute_formula (Equal t1 t2) = Equal t1 t2" |
"distribute_formula (Forall v \<phi>) = Forall v (distribute_formula \<phi>)" |
"distribute_formula (Exists v \<phi>) = Exists v (distribute_formula \<phi>)" |
"distribute_formula T = T" |
"distribute_formula F = F"

fun demorg_formula :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"demorg_formula (Pred p args) = Pred p args" |
"demorg_formula (And \<phi> \<psi>) = And (demorg_formula \<phi>) (demorg_formula \<psi>)" |
"demorg_formula (Or \<phi> \<psi>) = Or (demorg_formula \<phi>) (demorg_formula \<psi>)" |
"demorg_formula (Not \<phi>) = (case demorg_formula \<phi> of
  (And \<psi>1 \<psi>2) \<Rightarrow> Or (Not \<psi>1) (Not \<psi>2) |
  (Or \<psi>1 \<psi>2) \<Rightarrow> And (Not \<psi>1) (Not \<psi>2) |
  \<phi>' \<Rightarrow> Not \<phi>'
)" |
"demorg_formula (Equal t1 t2) = Equal t1 t2" |
"demorg_formula (Forall v \<phi>) = Forall v (demorg_formula \<phi>)" |
"demorg_formula (Exists v \<phi>) = Exists v (demorg_formula \<phi>)" |
"demorg_formula T = T" |
"demorg_formula F = F"

fun nnf_formula :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"nnf_formula (Pred p args) = Pred p args" |
"nnf_formula (And \<phi>1 \<phi>2) = And (nnf_formula \<phi>1) (nnf_formula \<phi>2)" |
"nnf_formula (Or \<phi>1 \<phi>2) = Or (nnf_formula \<phi>1) (nnf_formula \<phi>2)" |
"nnf_formula (Not \<phi>) = (case nnf_formula \<phi> of
  Pred p args \<Rightarrow> Not (Pred p args) |
  And \<psi>1 \<psi>2 \<Rightarrow> demorg_formula (Not (And \<psi>1 \<psi>2)) |
  Or \<psi>1 \<psi>2 \<Rightarrow> demorg_formula (Not (Or \<psi>1 \<psi>2)) |
  Not \<psi> \<Rightarrow> \<psi> |
  Equal t1 t2 \<Rightarrow> Not (Equal t1 t2) |
  Forall v \<psi> \<Rightarrow> Exists v (Not \<psi>) |
  Exists v \<psi> \<Rightarrow> Forall v (Not \<psi>) |
  T \<Rightarrow> F |
  F \<Rightarrow> T
)" |
"nnf_formula (Equal t1 t2) = Equal t1 t2" |
"nnf_formula (Forall v \<phi>) = Forall v (nnf_formula \<phi>)" |
"nnf_formula (Exists v \<phi>) = Exists v (nnf_formula \<phi>)" |
"nnf_formula T = T" |
"nnf_formula F = F"

lemma excluded_middle: "eval_formula (Or f (Not f)) vI fI pI"
  by auto

lemma and_de_morgan: "eval_formula (Not (And f1 f2)) vI fI pI = eval_formula (Or (Not f1) (Not f2)) vI fI pI"
  by auto

lemma or_de_morgan: "eval_formula (Not (Or f1 f2)) vI fI pI = eval_formula (And (Not f1) (Not f2)) vI fI pI"
  by auto

end                                          