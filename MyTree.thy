(* author: wzh*)

theory MyTree
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirr: "mirror (mirror t) = t"
  apply(induction t)
   apply(auto)
  done

end