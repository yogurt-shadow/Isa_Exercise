(* author: wzh *)

theory Exercise3
  imports Main

begin

type_synonym vname = string
type_synonym val = int

datatype aexp = N val | V vname | Plus aexp aexp
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> int" where
"aval (N n) s = n" |
"aval (V v) s = s v" |
"aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (V v) = V v" |
"asimp_const (N n) = N n" |
"asimp_const (Plus a1 a2) = 
(
case (asimp_const a1, asimp_const a2) of
  (N n1, N n2) \<Rightarrow> N (n1 + n2) |
(b1, b2) \<Rightarrow> Plus b1 b2
)"

(* Exer 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (V v) = True" |
"optimal (N n) = True" |
"optimal (Plus (N n1) (N n2)) = False" |
"optimal (Plus a1 a2) = conj (optimal a1) (optimal a2)"

theorem "optimal (asimp_const x)"
  apply(induction x)
    apply(auto split: aexp.split)
  done

(* Exer 3.2 *)
(* we make together the variable terms and constant terms *)
fun make_const :: "aexp \<Rightarrow> int" where
"make_const (N n) = n" |
"make_const (V v) = 0" |
"make_const (Plus a1 a2) = (make_const a1) + (make_const a2)"

fun make_var :: "aexp \<Rightarrow> aexp" where
"make_var (V v) = V v" |
"make_var (N n) = N 0" |
"make_var (Plus a1 a2) = Plus (make_var a1) (make_var a2) "

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = Plus (make_var a) (N (make_const a))"

value "full_asimp (Plus (N 12) (Plus (V a) (Plus (V b) (N 123))))"

theorem "aval (full_asimp a) s = aval a s"
  apply(induction a)
    apply(auto)
  done

(* Exer 3.3 *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst name a (N n) = N n" |
"subst name a (V v) = (if v = name then a else V v)" |
"subst name a (Plus a1 a2) = Plus (subst name a a1) (subst name a a2)"

value "subst ''x'' (N 10) (N 20)"
value "subst ''x'' (N 10) (V ''y'')"
value "subst ''x'' (N 10) (V ''x'')"
value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"

theorem "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
    apply(auto)
  done

(* \<Longrightarrow> is a  \<Longrightarrow> *)
theorem "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
    apply(auto)
  done

(* Exer 3.4 *)
datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Times2 aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> int" where
"aval2 (N2 n) s = n" |
"aval2 (V2 v) s = s v" |
"aval2 (Plus2 a1 a2) s = (aval2 a1 s) + (aval2 a2 s)" |
"aval2 (Times2 a1 a2) s = (aval2 a1 s) * (aval2 a2 s)"

fun asimp2 :: "aexp2 \<Rightarrow> aexp2" where
"asimp2 (N2 n) = N2 n" |
"asimp2 (V2 v) = V2 v" |
"asimp2 (Plus2 a1 a2) = (
case (asimp2 a1, asimp2 a2) of
(N2 n1, N2 n2) \<Rightarrow> N2 (n1+n2) |
(b1, b2) \<Rightarrow> Plus2 b1 b2
)" |
"asimp2 (Times2 a1 a2) = (
case (asimp2 a1, asimp2 a2) of
(N2 n1, N2 n2) \<Rightarrow> N2 (n1*n2) |
(N2 n1, b2) \<Rightarrow> (if n1 = 0 then N2 0 else (if n1 = 1 then b2 else Times2 (N2 n1) b2)) |
(b1, N2 n2) \<Rightarrow> (if n2 = 0 then N2 0 else (if n2 = 0 then b1 else Times2 b1 (N2 n2))) |
(b1, b2) \<Rightarrow> Times2 b1 b2
)"

theorem "aval2 (asimp2 a) s = aval2 a s"
  apply(induction a)
     apply(auto split: aexp2.split)
  done

(* Exer 3.5 *)
datatype aexp3 = N3 int | V3 vname | Plus3 aexp3 aexp3 | Times3 aexp3 aexp3 | Post3 vname | Div3 aexp3 aexp3

fun aval3 :: "aexp3 \<Rightarrow> state \<Rightarrow> (val* state)" where
"aval3 (N3 n) s = (n, s)" |
"aval3 (V3 v) s = (s v, s)" |
"aval3 (Plus3 a1 a2) s = (fst (aval3 a1 s) + fst (aval3 a2 s), (\<lambda> x. (snd (aval3 a1 s) x + snd (aval3 a2 s) x - s x)))" |
"aval3 (Times3 a1 a2) s = (fst (aval3 a1 s) * fst (aval3 a2 s), (\<lambda> x. (snd (aval3 a1 s) x + snd (aval3 a2 s) x - s x)))" |
"aval3 (Post3 v) s = (s v + 1, (s(v := s v + 1)))" |
"aval3 (Div3 a1 a2) s = (fst (aval3 a1 s) div fst (aval3 a2 s), (\<lambda> x. (snd (aval3 a1 s) x + snd (aval3 a2 s) x - s x)))"

value "aval3 (Div3 (N3 9) (V3 y))  (\<lambda> x. 3) "
value "aval3 (Post3 v)  (\<lambda> x. 12) "

end