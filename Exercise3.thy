(* author: wzh *)

theory Exercise3
  imports Main

begin

type_synonym vname = string
type_synonym val = int

datatype aexp = N val | V vname | Plus aexp aexp
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (V v) = V v" |
"asimp_const (N n) = N n" |
"asimp_const (Plus a1 a2) = 
(
case (asimp_const a1, asimp_const a2) of
  (N n1, N n2) \<Rightarrow> N (n1 + n2) |
(b1, b2) \<Rightarrow> Plus b1 b2
)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N a) (N b) = N (a+b)" |
"plus p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N a) = N a" |
"asimp (V x) = V x" |
"asimp (Plus p q) = plus (asimp p) (asimp q)"


(* Exer 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (V v) = True" |
"optimal (N n) = True" |
"optimal (Plus (N n1) (N n2)) = False" |
"optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

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

(* this theorem should be set simp for future proofs in 3.6 *)
theorem [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
    apply(auto)
  done

(* \<Longrightarrow> is a  \<Longrightarrow> *)
theorem [simp]: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
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
"aval3 (N3 n) s = (n, s)"
| "aval3 (V3 v) s = (s v, s)"
| "aval3 (Post3 v) s = (s v, s(v := s v + 1))"
| "aval3 (Plus3 a1 a2) s = (fst (aval3 a1 s) + fst (aval3 a2 (snd (aval3 a1 s))), snd (aval3 a2 (snd (aval3 a1 s))))"
| "aval3 (Times3 a1 a2) s = (fst (aval3 a1 s) * fst (aval3 a2 (snd (aval3 a1 s))), snd (aval3 a2 (snd (aval3 a1 s))))"
| "aval3 (Div3 a1 a2) s = (fst (aval3 a1 s) div fst (aval3 a2 (snd (aval3 a1 s))), snd (aval3 a2 (snd (aval3 a1 s))))"

value "aval3 (Div3 (N3 9) (V3 y))  (\<lambda> x. 3) "
value "aval3 (Post3 v)  (\<lambda> x. 12) "

fun aval3_2 :: "aexp3 \<Rightarrow> state \<Rightarrow> (val * state) option" where
"aval3_2 (N3 n) s = Some (n, s)"
| "aval3_2 (V3 v) s = Some (s v, s)"
| "aval3_2 (Post3 v) s = Some (s v, s(v := s v + 1))"
| "aval3_2 (Plus3 a1 a2) s = (
   case (aval3_2 a1 s) of
   None \<Rightarrow> None
   | Some (v1, s1) \<Rightarrow>
     (case (aval3_2 a2 s1) of
      None \<Rightarrow> None
      | Some (v2, s2) \<Rightarrow> Some (v1 + v2, s2)))"
| "aval3_2 (Times3 a1 a2) s = (
   case (aval3_2 a1 s) of
   None \<Rightarrow> None 
   | Some (v1, s1) \<Rightarrow>
     (case (aval3_2 a2 s1) of
      None \<Rightarrow> None
      | Some (v2, s2) \<Rightarrow> Some (v1*v2, s2)))"
| "aval3_2 (Div3 a1 a2) s = (
   case (aval3_2 a1 s) of
   None \<Rightarrow> None
   | Some (v1, s1) \<Rightarrow>
     (case (aval3_2 a2 s1) of
      None \<Rightarrow> None
      | Some (v2, s2) \<Rightarrow> (if v2 = 0 then None else Some (v1 div v2, s2))))"

value "aval3_2 (Plus3 (Post3 x) (Post3 x)) (\<lambda> x. 0)"
value "aval3_2 (Div3 (Post3 x) (N3 1))  (\<lambda> x. 3) "
value "aval3_2 (Div3 (N3 9) (V3 y))  (\<lambda> x. 3) "
value "aval3_2 (Div3 (N3 9) (V3 y))  (\<lambda> x. 0) "
value "aval3_2 (Post3 v)  (\<lambda> x. 12) "
value "aval3_2 (Plus3 (Post3 v) (Post3 v))  (\<lambda> x. 12) "
value "aval3_2 (Times3 (Post3 v) (Post3 v))  (\<lambda> x. 12) "
value "aval3_2 (Times3 (N3 9) (Div3 (V3 t) (N3 0)))  (\<lambda> x. 10) "
value "aval3_2 (Times3 (N3 9) (Div3 (Post3 t) (Post3 z)))  (\<lambda> x. 10) "
value "aval3_2 (Times3 (Div3 (V3 z) (N3 0)) (Div3 (V3 t) (N3 0)))  (\<lambda> x. 10) "

(* Exer 3.6 *)
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl a) s = a" |
"lval (Vl x) s = s x" |
"lval (Plusl p q) s = lval p s + lval q s" |
"lval (LET x a e) s = lval e (s(x:=lval a s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl a) = (N a)" |
"inline (Vl x) = (V x)" |
"inline (Plusl p q) = Plus (inline p) (inline q)" |
"inline (LET x a e) = subst x (inline a) (inline e)"  

theorem "aval (inline e) s = lval e s"
apply (induction e arbitrary: s)
apply (auto)
done


(* Exer 3.7 *)
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (Less a2 a1)"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

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

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply (auto simp add: Eq_def)
  done  

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply (auto simp add: Le_def)
  done 

(* Exer 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 c) s = c"
| "ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"
| "ifval (If if1 if2 if3) s = (if (ifval if1 s) then (ifval if2 s) else (ifval if3 s))"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = Bc2 b"
| "b2ifexp (Less a1 a2) = Less2 a1 a2"
| "b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))"
| "b2ifexp (And b1 b2) = If (b2ifexp b1) (b2ifexp b2) (Bc2 False)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 c) = Bc c"
| "if2bexp (Less2 a1 a2) = Less a1 a2"
| "if2bexp (If if1 if2 if3) = Not (And (Not (And (if2bexp if1) (if2bexp if2))) (Not (And (Not (if2bexp if1)) (if2bexp if3))))"
(* (a&b) \<or> (\<not>a&c) = \<not>(\<not>(a&b) \<and> \<not>(\<not>a&c)) *)

theorem "bval b s = ifval (b2ifexp b) s"
  apply(induction b)
     apply(auto)
  done

theorem "bval (if2bexp f) s = ifval f s"
  apply(induction f)
     apply(auto)
  done

(* Exer 3.9 *)
datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  
| "pbval (NOT b) s = (\<not> (pbval b s))"
| "pbval (AND b1 b2) s = ((pbval b1 s) \<and> (pbval b2 s))" 
| "pbval (OR b1 b2) s = ((pbval b1 s) \<or> (pbval b2 s))"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR v) = True"
| "is_nnf (NOT (VAR v)) = True"
| "is_nnf (NOT p) = False"
| "is_nnf (AND p1 p2) = ((is_nnf p1) \<and> (is_nnf p2))"
| "is_nnf (OR p1 p2) = ((is_nnf p1) \<and> (is_nnf p2))"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR v) = VAR v"
| "nnf (NOT (VAR v)) = NOT (VAR v)"
| "nnf (AND p1 p2) = AND (nnf p1) (nnf p2)"
| "nnf (OR p1 p2) = OR (nnf p1) (nnf p2)"
| "nnf (NOT (NOT p)) = nnf p"
| "nnf (NOT (AND p1 p2)) = OR (nnf (NOT p1)) (nnf (NOT p2))"
| "nnf (NOT (OR p1 p2)) = AND (nnf (NOT p1)) (nnf (NOT p2))"

lemma [simp]: "pbval (nnf (NOT p)) s = (\<not> pbval (nnf p) s)"
  apply(induction p)
     apply(auto)
  done

theorem "pbval (nnf p) s = pbval p s"                                  
  apply(induction p)
     apply(auto)
  done

theorem "is_nnf (nnf p)"
  apply(induction p rule: nnf.induct)
     apply(auto)
  done

(* Exer 3.10 *)
datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

fun exec1_modi :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1_modi (LOADI v) s stk = Some (v#stk)"
| "exec1_modi (LOAD v) s stk = Some (s v # stk)"
| "exec1_modi ADD s (x#y#stk) = Some ((x+y)#stk)"
| "exec1_modi ADD s stk = None"

fun exec_modi :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec_modi [] s stk = Some stk"
| "exec_modi (x#xs) s stk = (
     case (exec1_modi x s stk) of
        None \<Rightarrow> None
        | Some stk2 \<Rightarrow> exec_modi xs s stk2)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma [simp]: "exec_modi s1 s stk = Some stk1 \<Longrightarrow> exec_modi (s1@s2) s stk = exec_modi s2 s stk1"
  apply(induction s1 arbitrary: stk)
   apply(auto split: option.split)
  done

theorem "exec_modi (comp a) s stk = Some ((aval a s) # stk)"
  apply(induction a arbitrary: stk)
    apply(auto)
  done

(* Exer 3.11 *)
type_synonym reg = nat
datatype instr2 = LDI int reg | LD vname reg | ADD reg reg

fun exec1 :: "instr2 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec1 (LDI n r) s1 s2 = s2(r := n)"
| "exec1 (LD n r) s1 s2 = s2(r := s1 n)"
| "exec1 (ADD r1 r2) s1 s2 = s2(r1 := s2 r1 + s2 r2)"

fun exec :: "instr2 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec [] s1 s2 = s2"
| "exec (x#xs) s1 s2 = exec xs s1 (exec1 x s1 s2)"

fun compiler :: "aexp \<Rightarrow> reg \<Rightarrow> instr2 list" where
"compiler (N n) r = [LDI n r]"
| "compiler (V v) r = [LD v r]"
| "compiler (Plus a1 a2) r = (compiler a1 r) @ (compiler a2 (r+1)) @ [ADD r (r+1)]"

lemma [simp]: "exec (a@b) s1 s2 = exec b s1 (exec a s1 s2)"
  apply(induction a arbitrary: s2)
   apply(auto)
  done


(* Meaning: compiler a q only affects those larger or equal to q, because in compiler we only mention q and q+1.
   Thus, we do not change the key_value pair for those less than q in rs.
 *)
lemma [simp]: "q > r \<Longrightarrow> exec (compiler a q) s rs r = rs r"
  apply(induction a arbitrary: r rs q)
    apply(auto)
  done

theorem "exec (compiler a r) s rs r = aval a s"
  apply(induction a arbitrary: r rs)
   apply(auto)
  done

(* Exer 3.12 *)
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec1_0 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> val) \<Rightarrow> reg \<Rightarrow> val" where
"exec1_0 (LDI0 v) s rs = rs(0 := v)"
| "exec1_0 (LD0 v) s rs = rs(0 := s v)"
| "exec1_0 (MV0 r) s rs = rs(r := rs 0)"
| "exec1_0 (ADD0 r1) s rs = rs(0 := rs 0 + rs r1)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> val) \<Rightarrow> reg \<Rightarrow> val" where
"exec0 [] s rs = rs "
| "exec0 (x#xs) s rs = exec0 xs s (exec1_0 x s rs)"

fun compiler0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"compiler0 (N n) r = [LDI0 n]"
| "compiler0 (V v) r = [LD0 v]"
| "compiler0 (Plus a1 a2) r = (compiler0 a1 (r+1)) @ [MV0 (r+1)] @ (compiler0 a2 (r+2)) @ [ADD0 (r+1)]"
(* Note that: r may be 0. 
 In this case, first put result a1 into 0
 Second do nothing.
 Third put result a2 into 0. Then data in 0 will be overwritten.
 *)

lemma [simp]: "exec0 (a@b) s rs = exec0 b s (exec0 a s rs)"
  apply(induction a arbitrary: s rs b)
   apply(auto)
  done

(* Meaning: compiler a q only affects those larger or equal to q, because in compiler we only mention q and q+1.
   Thus, we do not change the key_value pair for those less than q in rs unless r is 0.
 *)
lemma [simp]: "r > 0 \<Longrightarrow> q > r \<Longrightarrow> exec0 (compiler0 a q) s rs r = rs r"
  apply(induction a arbitrary: q s rs r)
    apply(auto)
  done

theorem "exec0 (compiler0 a r) s rs 0 = aval a s"
  apply(induction a arbitrary: r s rs)
    apply(auto)
  done

end