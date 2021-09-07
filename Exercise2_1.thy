(* author: wzh*)

theory Exercise2_1
  imports Main

begin
(* Exer 2.1 *)
value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"

(* Exer 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

theorem add_assoc [simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done

lemma add_zero [simp]:  "add x 0 = x"
  apply(induction x)
   apply(auto)
  done

lemma add_suc1 [simp]: "add x (Suc(y)) = Suc(add x y) "
  apply(induction x)
  apply(auto)
  done

lemma add_suc2 [simp]: "add x (Suc(y)) = Suc(add y x) "
  apply(induction x)
  apply(auto)
  done

theorem add_commu [simp]: "add x y = add y x"
  apply(induction y)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double x = x*2"

theorem dou: "double x = add x x"
  apply(induction x)
   apply(auto)
  done

(* Exer 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0" |
"count x xs = (if x = (hd xs) then 1 + count x (tl xs) else count x (tl xs))"

theorem count_len: "count x xs \<le> length xs"
apply(induction xs)
  apply(auto)
  done

(* Exer 2.4 *)
fun snoc2 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc2 [] x = [x]" |
"snoc2 (x # xs) ys = (x # (snoc2 xs ys))"


fun reverse2 :: "'a list \<Rightarrow> 'a list" where
"reverse2 [] = []" |
"reverse2 (x#xs) = snoc2 (reverse2(xs)) x"

lemma [simp]: "reverse2 (snoc2 xs y) = y # (reverse2 xs)"
  apply(induction xs)
   apply(auto)
  done

theorem [simp]: "reverse2 (reverse2 xs) = xs"
  apply(induction xs)
  apply(auto)
  done


(* Exer 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto x = x + sum_upto (x-1)"

theorem sum: "sum_upto n*2 = n*(n+1)"
  apply(induction n)
   apply(auto)
  done

end