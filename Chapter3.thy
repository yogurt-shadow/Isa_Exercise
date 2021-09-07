(* author: wzh *)

theory Chapter3 imports Main

begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int

type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V v) s = s v" |
"aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)"

value "aval (Plus (N 0) (V x)) (\<lambda> x.0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V v) = V v" |
"asimp_const (Plus a1 a2) = 
(
case (asimp_const a1, asimp_const a2) of
(N n1, N n2) \<Rightarrow> N (n1 + n2) |
(b1, b2) \<Rightarrow> Plus b1 b2
)"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply(auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction rule: plus.induct)
  apply(auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc b) s = b"
| "bval (Not b) s = (\<not> (bval b s))"
| "bval (And b1 b2) s = ((bval b1 s) \<and> (bval b2 s))"
| "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False"
| "not (Bc False) = Bc True"
| "not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b"
| "and b (Bc True) = b"
| "and (Bc False) b = (Bc False)"
| "and b (Bc False) = (Bc False)"
| "and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)"
| "less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc b) = Bc b"
| "bsimp (Not b) = Not (bsimp b)"
| "bsimp (And b1 b2) = And (bsimp b1) (bsimp b2)"
| "bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI v) s stk = (v # stk)"
| "exec1 (LOAD name) s stk = (s name # stk)"
| "exec1 ADD s (x#y#stk) = ((x+y)#stk) "

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk"
| "exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma [simp]: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply(induction is1 arbitrary: stk)
   apply(auto)
  done

lemma "exec (comp a) s stk = aval a s # stk"
  apply(induction a arbitrary: stk)
    apply(auto)
  done

end
