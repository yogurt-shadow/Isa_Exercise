(* author: wzh*)

theory Chapter2
  imports Main
begin

(* 'b option means None | Some 'b  *)
fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else (lookup ps x))"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0"|
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"

lemma "div2 n = n div 2"
  apply(induction n rule: div2.induct)
   apply(auto)
  done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

lemma "itrev xs ys = (rev xs) @ ys"
  apply(induction xs arbitrary: ys)
   apply(auto)
  done

end