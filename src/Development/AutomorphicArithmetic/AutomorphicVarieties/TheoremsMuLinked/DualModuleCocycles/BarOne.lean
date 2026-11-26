module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DualMFst
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.FlagAEntry
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem UpperTheory.V.Th.Coc.flagA_full {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) {n : ℕ} (p : Fin n → P) :
    (List.ofFn fun j => φ (p j)).prod = φ (∏ j, p j) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

private theorem UpperTheory.V.Th.Coc.flagA_split {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) :
    ∀ {n : ℕ} (p : Fin n → P) (F : Fin n → M) (i : Fin n), (∀ j, j ≠ i → F j = φ (p j)) →
      (List.ofFn F).prod = φ (∏ j, if j < i then p j else 1) * F i * φ (∏ j, if i < j then p j else 1) := by
  intro n
  induction n with
  | zero => intro p F i; exact i.elim0
  | succ n ih =>
    intro p F i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro h
      have h1 : (fun j : Fin n => F j.succ) = fun j => φ (p j.succ) := funext fun j => h _ (Fin.succ_ne_zero j)
      rw [List.ofFn_succ, List.prod_cons, h1, flagA_full φ fun j : Fin n => p j.succ]
      simp [Fin.prod_univ_succ]
    · intro h
      rw [List.ofFn_succ, List.prod_cons,
        ih (fun j => p j.succ) (fun j => F j.succ) k (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e))),
        h 0 (Fin.succ_ne_zero k).symm]
      simp [Fin.prod_univ_succ, mul_assoc]

private theorem UpperTheory.V.Th.Coc.flagA_entry {A : Type} [CommRing A] {n : ℕ} (u Z : Matrix (Fin n) (Fin n) A) (α : Fin n → A)
    (a b : Fin n) : (kS u α * Z * kT u α) a b = (kEl u α a * Z * kEl u α b) a b := by
  simp [kS, kT, Matrix.mul_apply]

theorem UpperTheory.V.Th.Coc.flagA :
    ∀ {A H : Type} [CommRing A] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) A) (ψ : Fin n → H → A) (s : H), (∀ g : Fin n → H, (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) A)).prod = 0) → (∀ a b, a ≠ b → (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ g, (∀ a b, b < a → (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ i, (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) i i = ψ i g * (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) i i := by
  intro A H _ n r ψ s hrel
  let φ : Polynomial A →* Matrix (Fin n) (Fin n) A := (Polynomial.aeval (r s)).toRingHom.toMonoidHom
  let p : Fin n → Polynomial A := fun j => Polynomial.X - Polynomial.C (ψ j s)
  have hp : ∀ j, φ (p j) = r s - ψ j s • (1 : Matrix (Fin n) (Fin n) A) := by
    intro j
    simp [φ, p, Algebra.algebraMap_eq_smul_one]
  have hk : ∀ a, kEl (r s) (fun i => ψ i s) a = φ (∏ j ∈ Finset.univ.erase a, p j) := fun a => rfl
  have hfull : φ (∏ j, p j) = 0 := by
    rw [← flagA_full φ p]
    simp only [hp]
    exact hrel fun _ => s
  have h0 : ∀ a b, a ≠ b → kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b = 0 := by
    intro a b hab
    obtain ⟨q, hq⟩ : p a ∣ ∏ j ∈ Finset.univ.erase b, p j := Finset.dvd_prod_of_mem _ (by simp [hab])
    rw [hk, hk, ← map_mul, hq, ← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ a), map_mul, hfull, zero_mul]
  have h1 : ∀ g a b, b ≤ a → kEl (r s) (fun i => ψ i s) a * r g * kEl (r s) (fun i => ψ i s) b =
      ψ a g • (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) := by
    intro g a b hab
    have h := hrel (Function.update (fun _ => s) a g)
    rw [flagA_split φ p _ a (fun j hj => by rw [Function.update_of_ne hj, hp])] at h
    rw [Function.update_self, ← Finset.prod_filter, ← Finset.prod_filter] at h
    obtain ⟨q, hq⟩ : ∏ j ∈ Finset.univ.filter (· < a), p j ∣ ∏ j ∈ Finset.univ.erase a, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hj.ne]
    obtain ⟨q', hq'⟩ : ∏ j ∈ Finset.univ.filter (a < ·), p j ∣ ∏ j ∈ Finset.univ.erase b, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [(lt_of_le_of_lt hab hj).ne']
    have h2 : kEl (r s) (fun i => ψ i s) a * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
        kEl (r s) (fun i => ψ i s) b = 0 := by
      rw [hk, hk, hq, hq', mul_comm _ q, map_mul, map_mul]
      calc _ = φ q * (φ (∏ j ∈ Finset.univ.filter (· < a), p j) * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
            φ (∏ j ∈ Finset.univ.filter (a < ·), p j)) * φ q' := by simp only [mul_assoc]
        _ = 0 := by rw [h, mul_zero, zero_mul]
    rw [mul_sub, sub_mul, sub_eq_zero, mul_smul_comm, mul_one, smul_mul_assoc] at h2
    exact h2
  have he : ∀ a b, (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b =
      (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) a b := by
    intro a b
    simpa using flagA_entry (r s) 1 (fun i => ψ i s) a b
  refine ⟨fun a b hab => ?_, fun g => ⟨fun a b hab => ?_, fun i => ?_⟩⟩
  · rw [he, h0 a b hab]; rfl
  · rw [flagA_entry, h1 g a b hab.le, h0 a b hab.ne', smul_zero]; rfl
  · rw [flagA_entry, h1 g i i le_rfl, he]; rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TriAeval
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_pow {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (k : ℕ) :
    (∀ a b, b < a → (u ^ k) a b = 0) ∧ ∀ i, (u ^ k) i i = α i ^ k := by
  induction k with
  | zero =>
    refine ⟨fun a b hab => ?_, fun i => by simp⟩
    simp [Matrix.one_apply_ne hab.ne']
  | succ k ih =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rcases lt_or_ge c a with hc | hc
      · rw [ih.1 a c hc, zero_mul]
      · rw [h c b (lt_of_lt_of_le hab hc), mul_zero]
    · rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [ih.2, hd, pow_succ]
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [ih.1 i c hc, zero_mul]
        · rw [h c i hc, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi

private theorem tri_aeval {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (p : Polynomial O) :
    (∀ a b, b < a → (Polynomial.aeval u p) a b = 0) ∧ ∀ i, (Polynomial.aeval u p) i i = p.eval (α i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [map_add (f := _), Matrix.add_apply, hp.1 a b hab, hq.1 a b hab, add_zero]
    · rw [map_add (f := _), Matrix.add_apply, hp.2, hq.2, Polynomial.eval_add]
  | monomial k c =>
    have hk := tri_pow u α h hd k
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [Matrix.smul_apply, hk.1 a b hab, smul_zero]
    · rw [Matrix.smul_apply, hk.2, Polynomial.eval_monomial, smul_eq_mul]

theorem UpperTheory.V.Th.Coc.flagB :
    ∀ {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O), (∀ a b, b < a → u a b = 0) → (∀ i, u i i = α i) → (∀ a b, b < a → kS u α a b = 0 ∧ kT u α a b = 0) ∧ ∀ i, kS u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) ∧ kT u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) := by
  intro O _ n u α h hd
  have hev : ∀ i k, (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))).eval (α k) =
      ∏ j ∈ Finset.univ.erase i, (α k - α j) := by
    intro i k
    simp [Polynomial.eval_prod]
  refine ⟨fun a b hab => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · exact (tri_aeval u α h hd _).1 a b hab
  · exact (tri_aeval u α h hd _).1 a b hab
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.FlagCUpMul
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem flagC_up_mul {X : Type} [CommRing X] {n : ℕ} {A B : Matrix (Fin n) (Fin n) X}
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) :
    (∀ i j, j < i → (A * B) i j = 0) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k j (lt_of_lt_of_le hij h), mul_zero]
  · intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k i h, mul_zero]

private theorem flagC_core {X : Type} [CommRing X] {n : ℕ} (A B S T S₁ T₁ r D : Matrix (Fin n) (Fin n) X) (d : X)
    (g a : Fin n → X) (hAS : A * S = d • (1 : Matrix (Fin n) (Fin n) X)) (hTB : T * B = d • (1 : Matrix (Fin n) (Fin n) X))
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (hg : ∀ i, A i i * B i i * g i = d * d)
    (hL : ∀ i j, j < i → (S₁ * T + S * T₁) i j = 0) (hr : ∀ i j, j < i → r i j = 0)
    (hM : ∀ i j, j < i → (S₁ * r * T + S * D * T + S * r * T₁) i j = 0)
    (hMd : ∀ i, (S₁ * r * T + S * D * T + S * r * T₁) i i = g i * a i + r i i * (S₁ * T + S * T₁) i i) :
    (∀ i j, j < i → ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i j = 0) ∧
      ∀ i, ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i i = (d * d) * a i := by
  have e1 : A * (S₁ * r * T + S * D * T + S * r * T₁) * B =
      A * S₁ * r * (T * B) + (A * S) * D * (T * B) + (A * S) * r * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : A * (S₁ * T + S * T₁) * B = A * S₁ * (T * B) + (A * S) * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have key : (d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r) =
      A * (S₁ * r * T + S * D * T + S * r * T₁) * B - A * (S₁ * T + S * T₁) * B * r := by
    rw [e1, e2, hAS, hTB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul]
    abel
  obtain ⟨m1, m2⟩ := flagC_up_mul hA hM
  obtain ⟨m3, m4⟩ := flagC_up_mul m1 hB
  obtain ⟨l1, l2⟩ := flagC_up_mul hA hL
  obtain ⟨l3, l4⟩ := flagC_up_mul l1 hB
  obtain ⟨l5, l6⟩ := flagC_up_mul l3 hr
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, m3 i j hij, l5 i j hij, sub_zero]
  · rw [Matrix.sub_apply, m4, m2, l6, l4, l2, hMd, ← hg i]
    ring

theorem UpperTheory.V.Th.Coc.flagC :
    ∀ {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (S T : Matrix (Fin n) (Fin n) O) (Δ : Fin n → O), (∀ i, Δ i ≠ 0) → (∀ a b, b < a → S a b = 0 ∧ T a b = 0) → (∀ i, S i i = Δ i ∧ T i i = Δ i) → (∀ a b, a ≠ b → (S * T) a b = 0) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (S₁ T₁ : Matrix (Fin n) (Fin n) X), (∀ a b, a ≠ b → (S₁ * bar X T + bar X S * T₁) a b = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ (r : Matrix (Fin n) (Fin n) O) (D : Matrix (Fin n) (Fin n) X) (a : Fin n → X), (∀ i j, j < i → r i j = 0) → (∀ i j, j < i → (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i j = 0) → (∀ i, (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i i = (Δ i * Δ i) • a i + r i i • (S₁ * bar X T + bar X S * T₁) i i) → (∀ i j, j < i → (c₁ • D - (bar X r * Y - Y * bar X r)) i j = 0) ∧ ∀ i, (c₁ • D - (bar X r * Y - Y * bar X r)) i i = c₁ • a i := by
  intro O _ _ n S T Δ hΔ hup hdg hST
  have hS : ∀ i j, j < i → S i j = 0 := fun i j h => (hup i j h).1
  have hT : ∀ i j, j < i → T i j = 0 := fun i j h => (hup i j h).2
  obtain ⟨d, e, hd, he⟩ : ∃ (d : O) (e : Fin n → O), d ≠ 0 ∧ ∀ i, Δ i * Δ i * e i = d :=
    ⟨∏ i, Δ i * Δ i, fun i => ∏ k ∈ Finset.univ.erase i, Δ k * Δ k,
      Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hΔ i) (hΔ i),
      fun i => Finset.mul_prod_erase Finset.univ (fun k => Δ k * Δ k) (Finset.mem_univ i)⟩
  have hG : S * T = Matrix.diagonal fun i => Δ i * Δ i := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [(flagC_up_mul hS hT).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2]
    · rw [hST i j h, Matrix.diagonal_apply_ne _ h]
  have hdet : S.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hS i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [(hdg i).1]; exact hΔ i
  have hE : ∀ i j, j < i → Matrix.diagonal e i j = 0 := fun i j h => Matrix.diagonal_apply_ne _ h.ne'
  have h1 : S * T * Matrix.diagonal e = d • (1 : Matrix (Fin n) (Fin n) O) := by
    rw [hG, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    simp only [he]
  have h2 : T * Matrix.diagonal e * S = d • (1 : Matrix (Fin n) (Fin n) O) := by
    have h3 : S.adjugate * (S * T * Matrix.diagonal e * S) = S.det • (T * Matrix.diagonal e * S) := by
      rw [Matrix.mul_assoc S, Matrix.mul_assoc S, ← Matrix.mul_assoc S.adjugate, Matrix.adjugate_mul,
        Matrix.smul_mul, Matrix.one_mul]
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul, smul_comm] at h3
    exact (smul_right_injective _ hdet h3).symm
  have hmul : ∀ (X : Type) [CommRing X] [Algebra O X] (P Q : Matrix (Fin n) (Fin n) O),
      bar X P * bar X Q = bar X (P * Q) := fun X _ _ P Q => (Matrix.map_mul).symm
  have hone : ∀ (X : Type) [CommRing X] [Algebra O X],
      bar X (d • (1 : Matrix (Fin n) (Fin n) O)) = algebraMap O X d • (1 : Matrix (Fin n) (Fin n) X) := by
    intro X _ _
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hbar : ∀ (X : Type) [CommRing X] [Algebra O X] (P : Matrix (Fin n) (Fin n) O), (∀ i j, j < i → P i j = 0) →
      ∀ i j, j < i → bar X P i j = 0 := fun X _ _ P hP i j h => by simp [hP i j h]
  refine ⟨d * d, mul_ne_zero hd hd, fun X _ _ S₁ T₁ hL =>
    ⟨-(algebraMap O X d • (T₁ * bar X (Matrix.diagonal e * S))), fun r D a hr hM hMd => ?_⟩⟩
  have := flagC_core (bar X (T * Matrix.diagonal e)) (bar X (Matrix.diagonal e * S)) (bar X S) (bar X T) S₁ T₁ (bar X r) D
    (algebraMap O X d) (fun i => algebraMap O X (Δ i * Δ i)) a (by rw [hmul, h2, hone])
    (by rw [hmul, ← Matrix.mul_assoc, h2, hone]) (hbar X _ (flagC_up_mul hT hE).1) (hbar X _ (flagC_up_mul hE hS).1)
    (fun i => by
      change algebraMap O X ((T * Matrix.diagonal e) i i) * algebraMap O X ((Matrix.diagonal e * S) i i) * _ = _
      rw [← map_mul, ← map_mul, ← map_mul, (flagC_up_mul hT hE).2,
        (flagC_up_mul hE hS).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2, ← he i]
      congr 1
      ring)
    (fun i j h => hL i j h.ne') (hbar X r hr) hM
    (fun i => by rw [hMd i, Algebra.smul_def, Algebra.smul_def]; rfl)
  rw [← map_mul, algebraMap_smul] at this
  refine ⟨this.1, fun i => ?_⟩
  rw [this.2 i, Algebra.smul_def]
end

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_prod {A : Type} [CommRing A] {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) A)
    (h1 : ∀ i a b, b < a → M i a b = 0) (h2 : ∀ i, M i i i = 0) : (List.ofFn M).prod = 0 := by
  have key : ∀ k, k ≤ n → ∀ a b : Fin n, b.val < k → ((List.ofFn M).take k).prod a b = 0 := by
    intro k
    induction k with
    | zero => intro _ a b hb; omega
    | succ k ih =>
      intro hk a b hb
      have hl : k < (List.ofFn M).length := by simp; omega
      rw [List.prod_take_succ _ _ hl, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c.val < k
      · rw [ih (by omega) a c hc, zero_mul]
      · have : (List.ofFn M)[k] c b = 0 := by
          rw [List.getElem_ofFn]
          by_cases hcb : b < c
          · exact h1 _ _ _ hcb
          · have hcb' : c.val ≤ b.val := not_lt.mp hcb
            have e1 : c = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            have e2 : b = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            rw [e1, e2]
            exact h2 _
        rw [this, mul_zero]
  ext a b
  have := key n le_rfl a b b.2
  rwa [List.take_of_length_le (by simp)] at this

private theorem kEl_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) (i : Fin n) :
    (kEl u α i).map f = kEl (u.map f) (fun j => f (α j)) i := by
  unfold kEl
  generalize Finset.univ.erase i = t
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, map_mul, map_mul, Matrix.map_mul, ih]
    congr 1
    ext a b
    simp [Matrix.algebraMap_matrix_apply, apply_ite f]

private theorem kS_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) :
    (kS u α).map f = kS (u.map f) (fun j => f (α j)) := by
  ext a b
  simp only [kS, Matrix.map_apply, Matrix.of_apply, ← kEl_map]

private theorem kT_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) :
    (kT u α).map f = kT (u.map f) (fun j => f (α j)) := by
  ext a b
  simp only [kT, Matrix.map_apply, Matrix.of_apply, ← kEl_map]

private theorem fst_mul' {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) (DualNumber X)) :
    (A * B).map TrivSqZeroExt.fst = A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem snd_mul' {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) (DualNumber X)) :
    (A * B).map TrivSqZeroExt.snd =
      A.map TrivSqZeroExt.snd * B.map TrivSqZeroExt.fst + A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, ← Finset.sum_add_distrib, add_comm, mul_comm]

private theorem dualM_fst {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) X) :
    (dualM A B).map TrivSqZeroExt.fst = A := by
  ext a b
  simp [dualM]

private theorem dualM_snd {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) X) :
    (dualM A B).map TrivSqZeroExt.snd = B := by
  ext a b
  simp [dualM]

theorem UpperTheory.V.Th.Coc.flag :
    ∀ {O H : Type} [CommRing O] [IsDomain O] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) O) (ψ : Fin n → H → O) (s : H), (∀ g a b, b < a → r g a b = 0) → (∀ g i, r g i i = ψ i g) → (Function.Injective fun i => ψ i s) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (D : H → Matrix (Fin n) (Fin n) X) (a : Fin n → H → X), (∀ g : Fin n → H, (List.ofFn fun i => dualM (bar X (r (g i))) (D (g i)) - (TrivSqZeroExt.inl (algebraMap O X (ψ i (g i))) + TrivSqZeroExt.inr (a i (g i)) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ g, (∀ i j, j < i → (c₁ • D g - (bar X (r g) * Y - Y * bar X (r g))) i j = 0) ∧ ∀ i, (c₁ • D g - (bar X (r g) * Y - Y * bar X (r g))) i i = c₁ • a i g := by
  intro O H _ _ n r ψ s htri hdiag hinj
  have hrel : ∀ g : Fin n → H,
      (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) O)).prod = 0 := by
    intro g
    apply tri_prod
    · intro i a b hab
      simp [htri _ a b hab, Matrix.one_apply_ne hab.ne']
    · intro i
      simp [hdiag]
  obtain ⟨hoff, -⟩ := flagA r ψ s hrel
  obtain ⟨hB1, hB2⟩ := flagB (r s) (fun i => ψ i s) (htri s) (hdiag s)
  set S := kS (r s) (fun i => ψ i s) with hS
  set T := kT (r s) (fun i => ψ i s) with hT
  set Δ : Fin n → O := fun i => ∏ j ∈ Finset.univ.erase i, (ψ i s - ψ j s) with hΔ
  have hΔ0 : ∀ i, Δ i ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr fun j hj h => ?_
    exact (Finset.ne_of_mem_erase hj) (hinj (sub_eq_zero.mp h)).symm
  have hST : ∀ i, (S * T) i i = Δ i * Δ i := by
    intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hB2 i).1, (hB2 i).2]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [(hB1 i b h).1, zero_mul]
      · rw [(hB1 b i h).2, mul_zero]
    · simp
  obtain ⟨c₁, hc₁, hC⟩ := flagC S T Δ hΔ0 hB1 hB2 hoff
  refine ⟨c₁, hc₁, fun X _ _ D a hD => ?_⟩
  obtain ⟨h1, h2⟩ := flagA (fun g => dualM (bar X (r g)) (D g))
    (fun i g => (TrivSqZeroExt.inl (algebraMap O X (ψ i g)) + TrivSqZeroExt.inr (a i g) : DualNumber X)) s hD
  have eS := kS_map (TrivSqZeroExt.fstHom X X X).toRingHom (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X))
  have eT := kT_map (TrivSqZeroExt.fstHom X X X).toRingHom (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X))
  set S' := kS (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X)) with hS'
  set T' := kT (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X)) with hT'
  have hf : ⇑(TrivSqZeroExt.fstHom X X X).toRingHom = TrivSqZeroExt.fst := rfl
  have fS : S'.map TrivSqZeroExt.fst = bar X S := by
    rw [hf] at eS
    rw [eS, dualM_fst, hS, bar, bar, kS_map]
    simp
  have fT : T'.map TrivSqZeroExt.fst = bar X T := by
    rw [hf] at eT
    rw [eT, dualM_fst, hT, bar, bar, kT_map]
    simp
  have e1 : (S' * T').map TrivSqZeroExt.snd =
      S'.map TrivSqZeroExt.snd * bar X T + bar X S * T'.map TrivSqZeroExt.snd := by
    rw [snd_mul', fS, fT]
  have e2 : ∀ g, (S' * dualM (bar X (r g)) (D g) * T').map TrivSqZeroExt.snd =
      S'.map TrivSqZeroExt.snd * bar X (r g) * bar X T + bar X S * D g * bar X T +
        bar X S * bar X (r g) * T'.map TrivSqZeroExt.snd := by
    intro g
    rw [snd_mul', snd_mul', fst_mul', fS, fT, dualM_fst, dualM_snd, add_mul]
  have e3 : ∀ i, ((S' * T') i i).fst = algebraMap O X (Δ i * Δ i) := by
    intro i
    have : (S' * T').map TrivSqZeroExt.fst = bar X (S * T) := by
      rw [fst_mul', fS, fT, bar, bar, bar, Matrix.map_mul]
    have h := congrFun (congrFun this i) i
    rw [← hST]
    exact h
  obtain ⟨Y, hY⟩ := hC X (S'.map TrivSqZeroExt.snd) (T'.map TrivSqZeroExt.snd) (by
    intro a b hab
    rw [← e1, Matrix.map_apply, h1 a b hab, TrivSqZeroExt.snd_zero])
  refine ⟨Y, fun g => hY (r g) (D g) (fun i => a i g) (htri g) ?_ ?_⟩
  · intro i j hij
    rw [← e2, Matrix.map_apply, (h2 g).1 i j hij, TrivSqZeroExt.snd_zero]
  · intro i
    rw [← e2, ← e1, Matrix.map_apply, Matrix.map_apply, (h2 g).2 i, TrivSqZeroExt.snd_mul, e3, hdiag]
    generalize ((S' * T') i i).snd = z
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DualMSmulOne
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {n : ℕ}

end SlopeTestRemainingChoices

private theorem dualM_mul_dualM {X : Type} [CommRing X] {n : ℕ} (A B A' B' : Matrix (Fin n) (Fin n) X) :
    dualM A B * dualM A' B' = dualM (A * A') (A * B' + B * A') := by
  ext i j
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

theorem UpperTheory.V.Th.Coc.rel :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G H : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X) (φ : H → G) (ψ : Fin n → H → R) (g : Fin n → H), IsLift x δ (repR x ρ) τ c d → repR x ρ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → d (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → (List.ofFn fun i => dualM (bar X (ρ (φ (g i)))) (d (MonoidAlgebra.single (φ (g i)) 1)) - (TrivSqZeroExt.inl (algebraMap O X (x (ψ i (g i)))) + TrivSqZeroExt.inr (c • δ (ψ i (g i))) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0 := by
  intro O R X _ _ _ _ _ n G H _ x δ ρ τ c d φ ψ g hL h1 h2
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hd1 : d 1 = 0 := by
    have := hL.mul 1 1
    simp only [mul_one, map_one, hbar1, one_mul] at this
    have h' : d 1 + d 1 = d 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h'
  have hrep : ∀ (k : G) (r : R), repR x ρ (MonoidAlgebra.single k r) = x r • ρ k := by
    intro k r
    simp [repR, GDet.repAlg]
  have hs : ∀ r : R, MonoidAlgebra.single (1 : G) r = r • (1 : MonoidAlgebra R G) := by
    intro r
    simp [MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  let Φ : MonoidAlgebra R G →* Matrix (Fin n) (Fin n) (DualNumber X) :=
    { toFun := fun a => dualM (bar X (repR x ρ a)) (d a)
      map_one' := by
        ext i j
        · by_cases hij : i = j <;> simp [dualM, hbar1, Matrix.one_apply, hij]
        · by_cases hij : i = j <;> simp [dualM, hd1, Matrix.one_apply, hij]
      map_mul' := by
        intro a b
        rw [dualM_mul_dualM, hL.mul, map_mul]
        simp [bar, Matrix.map_mul, add_comm] }
  have key := map_list_prod Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i)))
  have hz : Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 := by
    show dualM _ _ = 0
    rw [h1, h2]
    ext i j <;> simp [dualM, bar]
  rw [hz, List.map_ofFn] at key
  rw [key]
  congr 2
  funext i
  show _ = dualM (bar X (repR x ρ (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))) (d (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))
  rw [map_sub, map_sub, hrep, hrep, hs (ψ i (g i)), hL.smul, hd1, map_one, map_one, map_one, one_smul, hbar1]
  ext a b
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
end

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_mul {X : Type} [CommRing X] {n : ℕ} (M N : Matrix (Fin n) (Fin n) X)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    (∀ i j, j < i → (M * N) i j = 0) ∧ ∀ i, M i i = 0 → (M * N) i i = 0 := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hM i k hk, zero_mul]
    · rw [hN k j (lt_of_lt_of_le hij hk), mul_zero]
  · intro i hi
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_trichotomy k i with hk | rfl | hk
    · rw [hM i k hk, zero_mul]
    · rw [hi, zero_mul]
    · rw [hN k i hk, mul_zero]

private theorem conj_id {O A : Type} [CommRing O] [Ring A] [Algebra O A] (c : O) (W Wi P Pi d Y : A)
    (h1 : Wi * W = 1) (h2 : W * Wi = 1) (h3 : P * Pi = 1) :
    Wi * (c • (d * Pi) - (P * (W * Y * Wi) * Pi - W * Y * Wi)) * W =
      (c • (Wi * d * W) - ((Wi * P * W) * Y - Y * (Wi * P * W))) * (Wi * Pi * W) := by
  have e1 : ∀ Z : A, W * (Wi * Z) = Z := fun Z => by rw [← mul_assoc, h2, one_mul]
  have e2 : ∀ Z : A, Wi * (W * Z) = Z := fun Z => by rw [← mul_assoc, h1, one_mul]
  have e3 : ∀ Z : A, P * (Pi * Z) = Z := fun Z => by rw [← mul_assoc, h3, one_mul]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, e1, e2, e3, h1, h2, h3, mul_one]

theorem UpperTheory.V.Th.Coc.locAt :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n) (v : L.Vl), ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (G : Glob l L) (h : G.Hom G0) (R : Type) [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (m : ℕ) (δ : R →ₗ[O] Om O m) (τ : MonoidAlgebra R G.G₀ → R) (c : O) (d : MonoidAlgebra R G.G₀ →+ Matrix (Fin n) (Fin n) (Om O m)) (ψ : Fin n → L.Gv v →* Rˣ), IsLift x δ (repR x (mat (y.ρ.comp h.p₀))) τ c d → (∀ i g, x (ψ i g : Rˣ) = (y.ψ v i g : Oˣ)) → (∀ g, repR x (mat (y.ρ.comp h.p₀)) (G.frame.oEl v ψ g) = 0 ∧ d (G.frame.oEl v ψ g) = 0) → (∀ i, ∀ g ∈ G.frame.mu v, δ (ψ i g : Rˣ) = 0) → ∃ Y, LocAt G.frame (y.ρm h m) (fun v => red m (y.w v)) (fun v => red m ((y.w v)⁻¹ : GL (Fin n) O)) (fun g => c₁ • (d (MonoidAlgebra.single g 1) * y.ρm h m g⁻¹)) v Y := by
  intro l _ L G0 n O _ _ _ _ y v
  obtain ⟨s, hs⟩ := y.reg v
  let r : L.Gv v → Matrix (Fin n) (Fin n) O := fun g =>
    (((y.w v)⁻¹ * y.ρ (G0.frame.φ v g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
  obtain ⟨c₁, hc₁, hfl⟩ := flag r (fun i g => ((y.ψ v i g : Oˣ) : O)) s
    (fun g => (y.tri v g).1) (fun g => (y.tri v g).2) (fun i j hij => hs (Units.ext hij))
  refine ⟨c₁, hc₁, ?_⟩
  intro G h R _ _ x m δ τ c d ψ hlift hψ hker hmu
  let W : GL (Fin n) O := y.w v
  let ρg : G.G₀ →* Matrix (Fin n) (Fin n) O := mat (y.ρ.comp h.p₀)
  let ρg' : G.G₀ →* Matrix (Fin n) (Fin n) O := mat ((MulAut.conj W⁻¹).toMonoidHom.comp (y.ρ.comp h.p₀))
  have hconj : ∀ a, repR x ρg' a = ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * repR x ρg a * ((W⁻¹⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, mul_add, add_mul]
    | single g a =>
      rw [repR_single, repR_single, inv_inv, mul_smul_comm, smul_mul_assoc]
      rfl
  obtain ⟨d', hl', hd'⟩ := liftConj x δ (repR x ρg') (repR x ρg) τ c W⁻¹ d hconj hlift
  have hp : ∀ g : L.Gv v, h.p₀ (G.frame.φ v g) = G0.frame.φ v g := fun g => Subtype.ext (h.φ v g)
  have hr : ∀ g, ρg' (G.frame.φ v g) = r g := by
    intro g
    simp only [ρg', r, mat, MonoidHom.comp_apply, hp, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl
  have hD : ∀ gt : Fin n → L.Gv v, (List.ofFn fun i => dualM (bar (Om O m) (r (gt i))) (d' (MonoidAlgebra.single (G.frame.φ v (gt i)) 1)) - (TrivSqZeroExt.inl (algebraMap O (Om O m) ((y.ψ v i (gt i) : Oˣ) : O)) + TrivSqZeroExt.inr (c • δ ((ψ i (gt i) : Rˣ) : R))) • 1).prod = 0 := by
    intro gt
    have e := rel x δ ρg' τ c d' (fun g : L.Gv v => G.frame.φ v g) (fun i g => ((ψ i g : Rˣ) : R)) gt hl' ?_ ?_
    · simpa only [hr, hψ] using e
    · rw [hconj]
      show _ * repR x ρg (G.frame.oEl v ψ gt) * _ = 0
      rw [(hker gt).1, mul_zero, zero_mul]
    · rw [hd']
      show _ * d (G.frame.oEl v ψ gt) * _ = 0
      rw [(hker gt).2, mul_zero, zero_mul]
  obtain ⟨Y', hY'⟩ := hfl (Om O m) (fun g => d' (MonoidAlgebra.single (G.frame.φ v g) 1)) (fun i g => c • δ ((ψ i g : Rˣ) : R)) hD
  have hredm : ∀ A B : Matrix (Fin n) (Fin n) O, red m (A * B) = red m A * red m B := fun A B => Matrix.map_mul
  have hred1 : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hbar : ∀ Z : Matrix (Fin n) (Fin n) O, bar (Om O m) Z = red m Z := fun Z => rfl
  have h1 : red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (W : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hredm, ← Units.val_mul, inv_mul_cancel, Units.val_one, hred1]
  have h2 : red m (W : Matrix (Fin n) (Fin n) O) * red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hredm, ← Units.val_mul, mul_inv_cancel, Units.val_one, hred1]
  have hd'' : ∀ a, red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * d a * red m (W : Matrix (Fin n) (Fin n) O) = d' a := by
    intro a
    rw [hd', inv_inv]
    rfl
  have hPr : ∀ g : G.G₀, ∀ g0 : L.Gv v, h.p₀ g = G0.frame.φ v g0 →
      red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * y.ρm h m g * red m (W : Matrix (Fin n) (Fin n) O) = bar (Om O m) (r g0) := by
    intro g g0 hg
    rw [hbar]
    show red m _ * red m _ * red m _ = red m _
    rw [← hredm, ← hredm]
    congr 1
    show ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ((y.ρ (h.p₀ g) : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (W : Matrix (Fin n) (Fin n) O) = _
    rw [hg]
    simp only [r, W, Units.val_mul]
  refine ⟨red m (W : Matrix (Fin n) (Fin n) O) * Y' * red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), fun g => ?_⟩
  have h3 : y.ρm h m (G.frame.φ v g) * y.ρm h m (G.frame.φ v g)⁻¹ = 1 := by
    show red m _ * red m _ = 1
    rw [← hredm, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, hred1]
  simp only [UpperTheory.V.Pa.dY]
  rw [conj_id c₁ _ _ _ _ _ Y' h1 h2 h3, hd'', hPr _ g (hp g), hPr _ g⁻¹ (by rw [map_inv, hp, map_inv])]
  have hN : ∀ i j, j < i → bar (Om O m) (r g⁻¹) i j = 0 := by
    intro i j hij
    show algebraMap O (Om O m) (r g⁻¹ i j) = 0
    rw [show r g⁻¹ i j = 0 from (y.tri v g⁻¹).1 i j hij, map_zero]
  have T := tri_mul _ _ (hY' g).1 hN
  refine ⟨T.1, fun hg i => T.2 i ?_⟩
  rw [(hY' g).2 i, hmu i g hg, smul_zero, smul_zero]
