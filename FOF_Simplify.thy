theory FOF_Simplify
  imports Main FOF_Base
begin

fun simp_formula :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"simp_formula (Pred p args) = Pred p args" |
"simp_formula (And \<phi>1 \<phi>2) = (case (simp_formula \<phi>1, simp_formula \<phi>2) of
  (T, T) \<Rightarrow> T |
  (F, _) \<Rightarrow> F |
  (_, F) \<Rightarrow> F |
  (T, \<phi>2') \<Rightarrow> \<phi>2' |
  (\<phi>1', T) \<Rightarrow> \<phi>1' |
  (\<phi>1', \<phi>2') \<Rightarrow> And \<phi>1' \<phi>2'
)" |
"simp_formula (Or \<phi>1 \<phi>2) = (case (simp_formula \<phi>1, simp_formula \<phi>2) of
  (F, F) \<Rightarrow> F |
  (T, _) \<Rightarrow> T |
  (_, T) \<Rightarrow> T |
  (F, \<phi>2') \<Rightarrow> \<phi>2' |
  (\<phi>1', F) \<Rightarrow> \<phi>1' |
  (\<phi>1', \<phi>2') \<Rightarrow> Or \<phi>1' \<phi>2'
)" |
"simp_formula (Not f) = (case simp_formula f of
  T \<Rightarrow> F |
  F \<Rightarrow> T |
  Not \<phi>1 \<Rightarrow> \<phi>1 |
  f' \<Rightarrow> Not f'
)" |
"simp_formula (Equal t1 t2) = Equal t1 t2" |
"simp_formula (Forall v f) = Forall v (simp_formula f)" |
"simp_formula (Exists v f) = Exists v (simp_formula f)" |
"simp_formula T = T" |
"simp_formula F = F"

lemma eval_formula_simp_formula_And_eq:
  assumes IH1: "eval_formula (simp_formula \<phi>1) vI fI pI = eval_formula \<phi>1 vI fI pI" 
      and IH2: "eval_formula (simp_formula \<phi>2) vI fI pI = eval_formula \<phi>2 vI fI pI"
    shows "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
proof (cases "simp_formula \<phi>1")
  case (Pred p1 args1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p2 args2)
    have "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI 
      = eval_formula (And (Pred p1 args1) (Pred p2 args2)) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Pred p2 args2)`
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<and> 
                      (eval_formula (Pred p2 args2) vI fI pI))"
      by simp
    also have "... = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Pred p2 args2)` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Equal t1 t1)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case T
    have "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI = eval_formula (Pred p1 args1) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = T` 
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<and> (eval_formula T vI fI pI))"
      by simp
    also have "... = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = T` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI = False"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = F`
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<and> (eval_formula F vI fI pI))"
      by simp
    also have "... = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = F` IH2
      by simp
    finally show ?thesis .
  qed
next
  case (And f1 f2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (And f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Or f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Equal t1 t1)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH2 by simp
  qed
next
  case (Or f1 f2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (And f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Or f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Equal t1 t1)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH2 by simp
  qed
next
  case (Not f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (And f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Or f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Not f2)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH2 by simp
  qed
next
  case (Equal t1 t2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Equal t3 t4)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH2 by simp
  qed
next
  case (Forall v1 f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (And f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Or f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Not f2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Forall v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Exists v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH2 by simp
  qed
next
  case (Exists v1 f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (And f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Or f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Not f2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Forall v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Exists v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH2 by simp
  qed
next
  case T
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI = eval_formula (Pred p args) vI fI pI"
      using `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Pred p args)` 
      by simp
    also have "... = ((eval_formula T vI fI pI) \<and> (eval_formula (Pred p args) vI fI pI))"
      by simp
    also have "... = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 IH2 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 IH2 by simp
  next
    case T
    have "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI = True"
      using `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = T`
      by simp
    also have "... = ((eval_formula T vI fI pI) \<and> (eval_formula T vI fI pI))"
      by simp
    also have "... = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = T` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = T` IH2 by simp
  qed
next
  case F
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (And \<phi>1 \<phi>2)) vI fI pI = False"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Pred p args)` 
      by simp
    also have "... = ((eval_formula F vI fI pI) \<and> (eval_formula (Pred p args) vI fI pI))"
      by simp
    also have "... = eval_formula (And \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 by simp
  qed
qed

lemma eval_formula_simp_formula_Or_eq:
  assumes IH1: "eval_formula (simp_formula \<phi>1) vI fI pI = eval_formula \<phi>1 vI fI pI" 
      and IH2: "eval_formula (simp_formula \<phi>2) vI fI pI = eval_formula \<phi>2 vI fI pI"
    shows "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
proof (cases "simp_formula \<phi>1")
  case (Pred p1 args1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p2 args2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI 
      = eval_formula (Or (Pred p1 args1) (Pred p2 args2)) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Pred p2 args2)`
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> 
                      (eval_formula (Pred p2 args2) vI fI pI))"
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Pred p2 args2)` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Equal t1 t1)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Pred p1 args1` IH1 IH2 by simp
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = T` 
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula T vI fI pI))"
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Pred p1 args1) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = F`
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula F vI fI pI))"
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = F` IH1 IH2
      by simp
    finally show ?thesis .
  qed
next
  case (And f1 f2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (And f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Or f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Equal t1 t1)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = And f1 f2` IH1 IH2 by simp
  qed
next
  case (Or f1 f2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (And f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Or f3 f4)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Equal t1 t1)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Or f1 f2` IH1 IH2 by simp
  qed
next
  case (Not f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (And f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Or f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Not f2)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Not f1` IH1 IH2 by simp
  qed
next
  case (Equal t1 t2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Equal t3 t4)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Equal t1 t2` IH1 IH2 by simp
  qed
next
  case (Forall v1 f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (And f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Or f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Not f2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Forall v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case (Exists v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Forall v1 f1` IH1 IH2 by simp
  qed
next
  case (Exists v1 f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (And f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Or f2 f3)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Not f2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Forall v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case (Exists v2 f2)
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH2 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = Exists v1 f1` IH1 IH2 by simp
  qed
next
  case T
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Pred p args)` 
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  next
    case F
    then show ?thesis using `simp_formula \<phi>1 = T` IH1 by simp
  qed
next
  case F
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Pred p args) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Pred p args)` 
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 IH2 by simp
  next
    case (Or f1 f2)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 IH2 by simp
  next
    case (Not f)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 IH2 by simp
  next
    case (Equal t1 t2)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 IH2 by simp
  next
    case (Forall v f)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 IH2 by simp
  next
    case (Exists v f)
    then show ?thesis using `simp_formula \<phi>1 = F` IH1 IH2 by simp
  next
    case T
    then show ?thesis using `simp_formula \<phi>1 = F` IH2 by simp
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = False"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = F` 
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula F vI fI pI))"
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = F` IH1 IH2
      by simp
    finally show ?thesis .
  qed
qed

lemma eval_formula_simp_formula_Not_eq:
  assumes IH: "eval_formula (simp_formula \<phi>) vI fI pI = eval_formula \<phi> vI fI pI"
  shows "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not \<phi>) vI fI pI"
proof (cases "simp_formula \<phi>")
  case (Pred p args)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (Pred p args)) vI fI pI"
    using `simp_formula \<phi> = (Pred p args)`
    by simp
  also have "... = (\<not>(eval_formula (Pred p args) vI fI pI))"
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (Pred p args)` IH
    by simp
  finally show ?thesis .
next
  case (And f1 f2)
  then show ?thesis using IH by simp
next
  case (Or f1 f2)
  then show ?thesis using IH by simp
next
  case (Not f)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula f vI fI pI"
    using `simp_formula \<phi> = (Not f)`
    by simp
  also have "... = (\<not>(\<not>(eval_formula f vI fI pI)))"
    by simp
  also have "... = (\<not>(eval_formula (Not f) vI fI pI))"
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (Not f)` IH
    by simp 
  finally show ?thesis .
next
  case (Equal t1 t2)
  then show ?thesis using IH by simp
next
  case (Forall v f)
  then show ?thesis using IH by simp
next
  case (Exists v f)
  then show ?thesis using IH by simp
next
  case T
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = False"
    using `simp_formula \<phi> = T`
    by simp
  also have "... = (\<not>(eval_formula T vI fI pI))"
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = T` IH
    by simp
  finally show ?thesis .
next
  case F
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = True"
    using `simp_formula \<phi> = F`
    by simp
  also have "... = (\<not>(eval_formula F vI fI pI))"
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = F` IH
    by simp
  finally show ?thesis .
qed

theorem eval_formula_simp_formula_eq_eval_formula: 
  "eval_formula (simp_formula \<phi>) vI fI pI = eval_formula \<phi> vI fI pI"
proof (induction \<phi> arbitrary: vI rule: simp_formula.induct)
  case (1 p args)
  then show ?case by simp
next
  case (2 f1 f2)
  then show ?case by (rule eval_formula_simp_formula_And_eq)
next
  case (3 f1 f2)
  then show ?case by (rule eval_formula_simp_formula_Or_eq)
next
  case (4 f)
  then show ?case by (rule eval_formula_simp_formula_Not_eq)
next
  case (5 t1 t2)
  then show ?case by simp
next
  case (6 v f)
  then show ?case by fastforce
next
  case (7 v f)
  then show ?case by fastforce
next
  case 8
  then show ?case by simp
next
  case 9
  then show ?case by simp
qed

end