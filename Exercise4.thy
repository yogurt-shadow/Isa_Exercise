(* author: wzh *)

theory Exercise4 
  imports Main

begin

(* Exer 4.1 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}"
| "set (Node l x r) = (set l) \<union> {x} \<union> (set r)"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True"
| "ord (Node l x r) = ((ord l) \<and> (ord r) \<and> (\<forall> y \<in> (set l). x \<ge> y) \<and> (\<forall> z \<in> (set r). z \<ge> x))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = (Node Tip x Tip)"
| "ins x (Node l mid r) = (
    if x = mid then (Node l mid r) else
        (if x < mid then (Node (ins x l) mid r) else
         (Node l mid (ins x r))))"

theorem [simp]: "set (ins x t) = {x} \<union> (set t)"
  apply(induction t)
  apply(auto)
  done

theorem [simp]: "ord t \<Longrightarrow> ord (ins x t)"
  apply(induction t)
   apply(auto)
  done

(* Exer 4.2 *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
"palindrome []"
| "palindrome [x]"
| "palindrome xs \<Longrightarrow> palindrome (x#xs@[x])"

theorem palin_rev: "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
    apply(auto)
  done


(* Exer 4.3 *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x"
| step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_trans: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(auto intro: refl step)
  done

theorem star'_star: "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(auto intro: refl star_trans)
  done

(* star'.induct can only be applied in the first premise *)
lemma star'_trans: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(auto intro: refl' step')
  done

theorem star_star': "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(auto intro: refl' star'_trans)
  done

(* Exer 4.4 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl_iter: "iter r n x x"
| step_iter: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

theorem star_iter: "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply(induction rule: star.induct)
  apply(auto intro: refl_iter step_iter)
  done

(* Exer 4.5 *)
datatype alpha = Aa | Bb

inductive S :: "alpha list \<Rightarrow> bool" where
s_empty: "S []"
| s_con1: "S w \<Longrightarrow> S (a#w@[b])"
| s_con2: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1@w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
t_empty: "T []"
| t_con: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1@[a]@w2@[b])"

theorem T_S: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(auto intro: s_empty s_con1 s_con2)
  done


(* Exer 4.6 *)
type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n"
| "aval (V v) s = s v"
| "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

inductive aval2 :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
const: "aval2 (N n) s n"
| var: "aval2 (V v) s (s v)"
| plus: "aval2 a1 s x \<Longrightarrow> aval2 a2 s y \<Longrightarrow> aval2 (Plus a1 a2) s (x+y)"

lemma aval_aval2: "aval a s = v \<Longrightarrow> aval2 a s v"
  apply(induction a arbitrary: v)
    apply(auto intro: plus var const)
  done

lemma aval2_aval: "aval2 a s v \<Longrightarrow> aval a s = v"
  apply(induction rule: aval2.induct)
    apply(auto)
  done

theorem "(aval a s = v) = (aval2 a s v)"
  apply(auto intro: aval_aval2 aval2_aval)
  done

(* Exer 4.7 *)
datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

fun exec1_modi :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1_modi (LOADI v) s stk = (v#stk)"
| "exec1_modi (LOAD v) s stk = (s v # stk)"
| "exec1_modi ADD s (x#y#stk) = ((x+y)#stk)"

fun exec_modi :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec_modi [] s stk = stk"
| "exec_modi (x#xs) s stk = exec_modi xs s (exec1_modi x s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_cons [simp]: "exec_modi (s1@s2) s stk = exec_modi s2 s (exec_modi s1 s stk)"
  apply(induction s1 arbitrary: stk)
   apply(auto split: option.split)
  done

theorem "exec_modi (comp a) s stk = ((aval a s) # stk)"
  apply(induction a arbitrary: stk)
    apply(auto)
  done

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
empty: "ok n [] n"
| load: "ok n xs m \<Longrightarrow> ok n (xs@[LOAD v]) (m+1)"
| loadi: "ok n xs m \<Longrightarrow> ok n (xs@[LOADI v]) (m+1)"
| add: "ok n xs (m+2) \<Longrightarrow> ok n (xs@[ADD]) (m+1)"

end