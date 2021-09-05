(* author: wzh*)

theory MyList
  imports Main

begin

datatype 'a list = Nil | Cons 'a "'a list"

(*app means add two lists*)
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil xs = xs" |
"app (Cons x xs) ys = Cons x (app xs ys)"


(*rev means reverse a list*)
fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev(Cons True (Cons False Nil))"
value "rev(Cons a (Cons b Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply(induction xs)
   apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
   apply(auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
   apply(auto)
  done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply(induction xs)
   apply(auto)
  done


end