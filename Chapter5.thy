(* author:wzh *)

theory Chapter5
  imports Main

begin
lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof 
  assume 0: "surj f"
  from 0 have 1: "\<forall> y. \<exists> x. y = f x" by (simp add: surj_def)
  from 1 have 2: "\<exists> a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed     

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  from this have "\<exists> a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  from this show "False" by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a " using s
    by(auto simp: surj_def)
  thus "False" by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "(a \<notin> f a) = (a \<in> f a)" by blast
  thus "False" by blast
qed

lemma 
  fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof - 
  have "\<exists> k'. a = b*k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k-1)" using asm by (simp add: algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add: dvd_def)
  qed

value "0 - 1::nat"

lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0 "
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0
  show ?case by simp
next 
  case evSS
  thus ?case by simp
qed


end