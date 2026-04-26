theory T1_2026_1
  imports Main
begin

(* Andrei Rech, Carlos Moraes e Guilherme de Moraes *)

primrec pot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
poteq1: "pot x 0 = 1" |
poteq2: "pot x (Suc y) = x * pot x y"

lemma t1: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
proof (induction n)
  (* Caso Base *)
  show "\<forall>x m::nat. pot x (m + 0) = pot x m * pot x 0"
  proof (rule allI)+
    fix x m :: nat
    have "pot x (m + 0) = pot x m" by (simp only: add_0_right)
    also have "... = pot x m * 1" by (simp only: mult_1_right)
    also have "... = pot x m * pot x 0" by (simp only: poteq1)
    finally show "pot x (m + 0) = pot x m * pot x 0" .
  qed
next
  (* Passo Indutivo *)
  fix n :: nat
  assume hi: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
  
  show "\<forall>x m::nat. pot x (m + Suc n) = pot x m * pot x (Suc n)"
  proof (rule allI)+
    fix x m :: nat
    have "pot x (m + Suc n) = pot x (Suc (m + n))" by (simp only: add_Suc_right)
    also have "... = x * pot x (m + n)" by (simp only: poteq2)
    also have "... = x * (pot x m * pot x n)" by (simp only: hi)
    also have "... = pot x m * (x * pot x n)" by (simp add: ac_simps)
    also have "... = pot x m * pot x (Suc n)" by (simp only: poteq2)
    finally show "pot x (m + Suc n) = pot x m * pot x (Suc n)" .
  qed
qed

theorem t2: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
proof (induction n)
  (* Caso Base *)
  show "\<forall>x m::nat. pot x (m * 0) = pot (pot x m) 0"
  proof (rule allI)+
    fix x m :: nat
    have "pot x (m * 0) = pot x 0" by (simp only: mult_0_right)
    also have "... = 1" by (simp only: poteq1)
    also have "... = pot (pot x m) 0" by (simp only: poteq1)
    finally show "pot x (m * 0) = pot (pot x m) 0" .
  qed
next
  (* Passo Indutivo *)
  fix n :: nat
  assume hi: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
  
  show "\<forall>x m::nat. pot x (m * Suc n) = pot (pot x m) (Suc n)"
  proof (rule allI)+
    fix x m :: nat
    have "pot x (m * Suc n) = pot x (m + m * n)" by (simp only: mult_Suc_right)
    also have "... = pot x m * pot x (m * n)" by (simp only: t1)
    also have "... = pot x m * pot (pot x m) n" by (simp only: hi)
    also have "... = pot (pot x m) (Suc n)" by (simp only: poteq2)
    finally show "pot x (m * Suc n) = pot (pot x m) (Suc n)" .
  qed
qed

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

primrec somatorio :: "nat list \<Rightarrow> nat" where
somaeq1: "somatorio [] = 0" |
somaeq2: "somatorio (x#xs) = x + somatorio xs"

lemma t3: "\<forall>ys::nat list. somatorio (cat xs ys) = somatorio xs + somatorio ys"
proof (induction xs)
  (* Caso Base *)
  show "\<forall>ys::nat list. somatorio (cat [] ys) = somatorio [] + somatorio ys"
  proof (rule allI)
    fix ys :: "nat list"
    have "somatorio (cat [] ys) = somatorio ys" by (simp only: cateq1)
    also have "... = 0 + somatorio ys" by (simp only: add_0_left)
    also have "... = somatorio [] + somatorio ys" by (simp only: somaeq1)
    finally show "somatorio (cat [] ys) = somatorio [] + somatorio ys" .
  qed
next
  (* Passo Indutivo *)
  fix a :: nat
  fix xs :: "nat list"
  assume hi: "\<forall>ys::nat list. somatorio (cat xs ys) = somatorio xs + somatorio ys"
  
  show "\<forall>ys::nat list. somatorio (cat (a#xs) ys) = somatorio (a#xs) + somatorio ys"
  proof (rule allI)
    fix ys :: "nat list"
    have "somatorio (cat (a#xs) ys) = somatorio (a # cat xs ys)" by (simp only: cateq2)
    also have "... = a + somatorio (cat xs ys)" by (simp only: somaeq2)
    also have "... = a + (somatorio xs + somatorio ys)" by (simp only: hi)
    also have "... = (a + somatorio xs) + somatorio ys" by (simp only: add.assoc)
    also have "... = somatorio (a#xs) + somatorio ys" by (simp only: somaeq2)
    finally show "somatorio (cat (a#xs) ys) = somatorio (a#xs) + somatorio ys" .
  qed
qed

theorem t4: "somatorio (reverso xs) = somatorio xs"
proof (induction xs)
  (* Caso Base *)
  have "somatorio (reverso []) = somatorio []" by (simp only: reveq1)
  then show "somatorio (reverso []) = somatorio []" .
next
  (* Passo Indutivo *)
  fix a :: nat
  fix xs :: "nat list"
  assume hi: "somatorio (reverso xs) = somatorio xs"
  
  have "somatorio (reverso (a#xs)) = somatorio (cat (reverso xs) [a])" by (simp only: reveq2)
  also have "... = somatorio (reverso xs) + somatorio [a]" by (simp only: t3)
  also have "... = somatorio xs + somatorio [a]" by (simp only: hi)
  also have "... = somatorio xs + (a + somatorio [])" by (simp only: somaeq2)
  also have "... = somatorio xs + (a + 0)" by (simp only: somaeq1)
  also have "... = somatorio xs + a" by (simp only: add_0_right)
  also have "... = a + somatorio xs" by (simp only: add.commute)
  also have "... = somatorio (a#xs)" by (simp only: somaeq2)
  finally show "somatorio (reverso (a#xs)) = somatorio (a#xs)" .
qed

end