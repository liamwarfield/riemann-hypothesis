module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyFewColumnsLinear
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.TB (perpVec)

namespace GlobalTheory.Harm

open GlobalTheory.MvPoly GlobalTheory.GridSize

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {Λ : Submodule (𝓞 E) (Fin n → E)}

private theorem perpVec_apply_eq_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {m : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin m → V) (g : V) (c : Fin m) :
    h (perpVec h e e' g) (e c) = 0 := by
  set M := ReciprocityTheory.ChartRestriction.G.TB.hMat h e e' with hMdef
  have hM : ∀ a', M a' c = h (e' a') (e c) := fun _ => rfl
  have hadj : ∀ a, ∑ a', M.adjugate a a' * M a' c = if a = c then M.det else 0 := by
    intro a
    have := congrFun (congrFun (Matrix.adjugate_mul M) a) c
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hrow : ∀ a, ∑ a', M.adjugate a a' * h g (e a) * h (e' a') (e c) =
      h g (e a) * if a = c then M.det else 0 := by
    intro a
    rw [← hadj a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [hM]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [perpVec, ← hMdef, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, hrow, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

theorem exists_short_harmonic_family_few_columns (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    {p q : ℕ} (hn : p + q ≤ n) {T : Type*} [Fintype T] (c : T → Fin p → ℕ)
    (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c') :
    ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
      (∀ s ∈ S, (∀ a, s.1 a ∈ Λ) ∧ (∀ b, s.2 b ∈ Λ) ∧ ∀ a b, herm 1 (s.2 b) (s.1 a) = 0) ∧
      (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
        (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x)) →
        Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
          minorProd c c' (fun t a k => τ t (cc (s.1 a k))) fun t b k => τ t (s.2 b k)) '' S) =
          rowHighest K c c') ∧
      (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
        l1Norm (minorProd c c' (fun t a k => τ t (cc (s.1 a k))) fun t b k => τ t (s.2 b k)) ≤
          (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * fdeg E * n) *
            ((2 * (p + q : ℕ) + 1) * typeDegree c c') *
            (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E)) ^ (2 * (p + q) + 1))) ^
            typeDegree c c') ∧
      S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * fdeg E * n * (2 * p + q)) := by
  classical
  obtain ⟨v, hvΛ, -, hvspan, hvlen⟩ := GlobalTheory.exists_short_vectors Λ hfg hint hdual
  have hN1 : 1 ≤ p + q := one_le_add_of_one_le_typeDegree ha
  have hn1 : 1 ≤ n := hN1.trans hn
  have hf1 : 1 ≤ fdeg E := one_le_fdeg
  have hrd : 1 ≤ rdE E := one_le_rdE
  obtain ⟨dg, hdg⟩ : ∃ dg, dg = (2 * (p + q) + 1) * typeDegree c c' := ⟨_, rfl⟩
  have hdg1 : 1 ≤ dg := by rw [hdg]; exact Nat.mul_pos (Nat.succ_pos _) ha
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E := ⟨_, rfl⟩
  have hρ1 : 1 ≤ ρ := by
    have h1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast hf1) (by norm_num)
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn1)
    have h3 : (1 : ℝ) ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) := by linarith
    rw [hρ]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h2) hrd
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((2 * fdeg E * n : ℕ) : ℝ) * (dg : ℝ) * ρ := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    have h1 : (1 : ℝ) ≤ ((2 * fdeg E * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos two_pos hf1) hn1
    have h2 : (1 : ℝ) ≤ (dg : ℝ) := by exact_mod_cast hdg1
    rw [hR]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hρ1
  let h := hermPairing E n
  have hpair : ∀ x y, h x y = herm 1 x y := fun _ _ => rfl
  have hh : ∀ x y, h x y = ∑ k, x k * cc (y k) := fun x y => (hpair x y).trans (herm_one_eq_sum x y)
  have hcomb : ∀ A : Fin (2 * fdeg E * n) → ℕ, ∑ i, (A i : E) • v i ∈ Λ := fun A =>
    Λ.sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hvΛ i) _
  have hlen : ∀ (σ : E →+* ℂ) (A : Fin (2 * fdeg E * n) → ℕ), (∀ i, A i ≤ dg) →
      ∑ k, ‖σ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ R ^ 2 := by
    intro σ A hA
    have := sum_sq_combination_le σ v (ρ := ρ) (fun i => by rw [hρ]; exact hvlen i σ) A hA
    rw [Fintype.card_fin] at this
    rw [hR]
    exact this
  let comb : (Fin (2 * fdeg E * n) → ℕ) → Fin n → E := fun A => ∑ i, (A i : E) • v i
  let F : (Fin p → Fin (2 * fdeg E * n) → ℕ) × (Fin p → Fin (2 * fdeg E * n) → ℕ) ×
      (Fin q → Fin (2 * fdeg E * n) → ℕ) → (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
    fun x => (fun a => comb (x.1 a),
      fun b => perpVec h (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a)) (comb (x.2.2 b)))
  let G := (Fintype.piFinset fun _ : Fin p => Fintype.piFinset fun _ : Fin (2 * fdeg E * n) =>
      Finset.range (dg + 1)) ×ˢ (Fintype.piFinset fun _ : Fin p =>
      Fintype.piFinset fun _ : Fin (2 * fdeg E * n) => Finset.range (dg + 1)) ×ˢ
      (Fintype.piFinset fun _ : Fin q => Fintype.piFinset fun _ : Fin (2 * fdeg E * n) =>
      Finset.range (dg + 1))
  have hG : ∀ x ∈ G, (∀ a i, x.1 a i ≤ dg) ∧ (∀ a i, x.2.1 a i ≤ dg) ∧ (∀ b i, x.2.2 b i ≤ dg) := by
    intro x hx
    simp only [G, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hx
    exact ⟨fun a i => Nat.lt_succ_iff.mp (hx.1 a i), fun a i => Nat.lt_succ_iff.mp (hx.2.1 a i),
      fun b i => Nat.lt_succ_iff.mp (hx.2.2 b i)⟩
  refine ⟨G.image F, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨fun a => hcomb _, fun b => perpVec_hermPairing_mem hint (fun a => hcomb _)
      (fun a => hcomb _) (hcomb _), fun a b => ?_⟩
    rw [← hpair]
    exact perpVec_apply_eq_zero h _ _ _ a
  · intro K _ _ τ hτ
    rw [(rowHighest_orbitSpan_main hn c c' K).2.1,
      ← span_grid_perpVec_eq_orbitSpan τ hτ hn h hh v hvspan c c' (le_of_eq hdg.symm)]
    congr 1
    rw [Finset.coe_image, ← Set.image_comp]
    ext P
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hG x hx
      exact ⟨x.1, x.2.1, x.2.2, h1, h2, h3, rfl⟩
    · rintro ⟨A, A', B, h1, h2, h3, rfl⟩
      refine ⟨(A, A', B), ?_, rfl⟩
      simp only [G, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset,
        Finset.mem_range]
      exact ⟨fun a i => Nat.lt_succ_of_le (h1 a i), fun a i => Nat.lt_succ_of_le (h2 a i),
        fun b i => Nat.lt_succ_of_le (h3 b i)⟩
  · intro τ s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hA, hA', hB⟩ := hG x hx
    have hR0 : 0 ≤ R := by linarith
    have hRR : R ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1) := by
      have h1 : (1 : ℝ) ≤ ((p + q + 1).factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : R ≤ R ^ (2 * (p + q) + 1) := by
        simpa using pow_le_pow_right₀ hR1 (Nat.le_add_left 1 (2 * (p + q)))
      calc R ≤ R ^ (2 * (p + q) + 1) := h2
        _ = 1 * R ^ (2 * (p + q) + 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pow_nonneg hR0 _)
    have hR'0 : 0 ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1) := by linarith
    refine (l1Norm_rowBlockLeadingMinorProduct_le c c' _ _ hR'0 ?_ ?_ (Nat.le_add_right p q)
      (Nat.le_add_left q p)).trans (le_of_eq ?_)
    · intro t a
      have := hlen ((τ t).comp (IsCMField.complexConj E : E →+* E)) (x.1 a) (hA a)
      exact this.trans (pow_le_pow_left₀ hR0 hRR 2)
    · intro t b
      have := sum_sq_perpVec_le (τ t) h hh (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a))
        (comb (x.2.2 b)) (R := R) (fun a => hlen _ _ (hA a)) (fun a => hlen _ _ (hA' a))
        (hlen _ _ (hB b))
      refine this.trans (pow_le_pow_left₀ (mul_nonneg (by positivity) (pow_nonneg hR0 _)) ?_ 2)
      have h1 : ((p + 1).factorial : ℝ) ≤ ((p + q + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have h2 : R ^ (2 * p + 1) ≤ R ^ (2 * (p + q) + 1) := pow_le_pow_right₀ hR1 (by omega)
      exact mul_le_mul h1 h2 (pow_nonneg hR0 _) (by positivity)
    · subst hR hρ hdg
      push_cast
      ring
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    simp only [G, Finset.card_product, Fintype.card_piFinset, Finset.card_range,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdg]
    ring

private theorem det_mem_subalgebra_of_entries_mem' {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Subalgebra A B) {m : ℕ} (M : Matrix (Fin m) (Fin m) B) (hM : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => hM _ _) _

private theorem minorProd_mem_Ha_of_herm_orthogonal {K : Type} [Field K] {T : Type*} [Fintype T] {p q : ℕ}
    (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (e : Fin p → Fin n → E)
    (f : Fin q → Fin n → E) (he : ∀ a, e a ∈ Λ) (hf : ∀ b, f b ∈ Λ)
    (hef : ∀ a b, herm 1 (e a) (f b) = 0) :
    minorProd c c' (fun t a k => τ t (e a k)) (fun t b k => τ t (cc (f b k))) ∈ Ha τ c c' Λ := by
  unfold Ha
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    apply minorProd_mem_rowHighest
    intro t a b
    have := congrArg (τ t) (hef a b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [herm_one_eq_sum, map_sum, map_zero] at this
    simpa [dotProduct, map_mul] using this
  · change minorProd c c' _ _ ∈ symO p q τ Λ
    unfold symO minorProd
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · unfold xMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inl ⟨t, _, e _, he _, rfl⟩)
    · unfold yMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inr ⟨t, _, f _, hf _, rfl⟩)

theorem exists_short_harmonic_family_few_columns_linear (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    {p q : ℕ} (hn : p + q ≤ n) {T : Type*} [Fintype T] (c : T → Fin p → ℕ)
    (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c') :
    ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
      (∀ s ∈ S, (∀ a, s.1 a ∈ Λ) ∧ (∀ b, s.2 b ∈ Λ) ∧ ∀ a b, herm 1 (s.1 a) (s.2 b) = 0) ∧
      (∀ (K : Type) [Field K] (τ : T → E →+* K), ∀ s ∈ S,
        (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ∈
          Ha τ c c' Λ) ∧
      (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
        (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x)) →
        Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
          minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) '' S) =
          rowHighest K c c') ∧
      (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
        l1Norm (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ≤
          (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * fdeg E * n) *
            ((2 * (p + q : ℕ) + 1) * typeDegree c c') *
            (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E)) ^ (2 * (p + q) + 1))) ^
            typeDegree c c') ∧
      S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * fdeg E * n * (2 * p + q)) := by
  classical
  obtain ⟨hfg', hint', hdual'⟩ := conjLattice_selfDual hfg hint hdual
  obtain ⟨S', hS'1, hS'2, hS'3, hS'4⟩ :=
    exists_short_harmonic_family_few_columns (Λ := conjLattice Λ) hfg' hint' hdual' hn c c' ha
  let cj : (Fin p → Fin n → E) × (Fin q → Fin n → E) → (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
    fun s => (fun a => conjVec E n (s.1 a), fun b => conjVec E n (s.2 b))
  have hcc : ∀ x : E, cc (cc x) = x := fun x => by
    have := congrFun (conjVec_conjVec (E := E) (n := 1) (fun _ => x)) 0
    simpa only [conjVec_apply] using this
  have hpoly : ∀ (K : Type) [Field K] (τ : T → E →+* K) (s : (Fin p → Fin n → E) × (Fin q → Fin n → E)),
      minorProd c c' (fun t a k => τ t ((cj s).1 a k)) (fun t b k => τ t (cc ((cj s).2 b k))) =
        minorProd c c' (fun t a k => τ t (cc (s.1 a k))) (fun t b k => τ t (s.2 b k)) := by
    intro K _ τ s
    simp only [cj, conjVec_apply, hcc]
  have hmem : ∀ s ∈ S', (∀ a, (cj s).1 a ∈ Λ) ∧ (∀ b, (cj s).2 b ∈ Λ) ∧
      ∀ a b, herm 1 ((cj s).1 a) ((cj s).2 b) = 0 := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hS'1 s hs
    refine ⟨fun a => mem_conjLattice.mp (h1 a), fun b => mem_conjLattice.mp (h2 b), fun a b => ?_⟩
    simp only [cj]
    rw [herm_conjVec]
    exact h3 a b
  refine ⟨S'.image cj, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    exact hmem s' hs'
  · intro K _ τ s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨h1, h2, h3⟩ := hmem s' hs'
    exact minorProd_mem_Ha_of_herm_orthogonal τ c c' _ _ h1 h2 h3
  · intro K _ _ τ hτ
    rw [← hS'2 K τ hτ, Finset.coe_image, ← Set.image_comp]
    exact congrArg _ (Set.image_congr fun s _ => hpoly K τ s)
  · intro τ s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    rw [hpoly ℂ τ s']
    exact hS'3 τ s' hs'
  · exact Finset.card_image_le.trans hS'4

end

theorem short_harmonic_family_few_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) → ∀ (p q : ℕ), p + q ≤ n → ∀ (T : Type) [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ), 1 ≤ typeDegree c c' → ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)), (∀ (K : Type) [Field K] (τ : T → E →+* K), ∀ s ∈ S, (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ∈ Ha τ c c' Λ) ∧ (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K), (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x)) → Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) => minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) '' S) = rowHighest K c c') ∧ (∀ (τ : T → E →+* ℂ), ∀ s ∈ S, l1Norm (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ≤ (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * fdeg E * n) * ((2 * (p + q : ℕ) + 1) * typeDegree c c') * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E)) ^ (2 * (p + q) + 1))) ^ typeDegree c c') ∧ S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * fdeg E * n * (2 * p + q)) := by
  intro E _ _ _ n Λ hfg hint hdual p q hn T _ c c' ha
  obtain ⟨S, -, h2, h3, h4, h5⟩ := exists_short_harmonic_family_few_columns_linear hfg hint hdual hn c c' ha
  exact ⟨S, h2, h3, h4, h5⟩

end GlobalTheory.Harm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogShortFamilyNumbersLe
namespace GlobalTheory

theorem log_shortFamilyNumbers_le : ∀ (N n a f : ℕ) (rd L : ℝ), 1 ≤ N → N ≤ n → 1 ≤ a → 1 ≤ f → 1 ≤ rd → 2 ≤ L → Real.log rd ≤ 2 * L → Real.log f ≤ 2 * L → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log (((N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1))) ^ a) ≤ 140 * N * L * a := by
  intro N n a f rd L hN hNn ha hf hrd hL h1 h2 h3 h4
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := hN'.trans hNn'
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp L := ⟨_, rfl⟩
  have hE3 : 3 ≤ E := by have := Real.add_one_le_exp L; linarith
  have hE1 : 1 ≤ E := by linarith
  have hE2 : Real.exp (2 * L) = E ^ 2 := by rw [hE, ← Real.exp_nat_mul]; norm_num
  have bn : (n : ℝ) ≤ E := by rw [hE]; exact (Real.log_le_iff_le_exp (by linarith)).1 h4
  have bf : (f : ℝ) ≤ E ^ 2 := by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h2
  have brd : rd ≤ E ^ 2 := by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h1
  have ba : (a : ℝ) ≤ E ^ 2 := by
    have : (1 + a : ℝ) ≤ E ^ 2 := by
      rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h3
    linarith
  have bN : (N : ℝ) ≤ E := hNn'.trans bn
  have b2 : (2 : ℝ) ≤ E := by linarith
  have b2N : (2 * N + 1 : ℝ) ≤ E ^ 2 := by nlinarith
  have bN1 : (N + 1 : ℝ) ≤ E ^ 2 := by nlinarith
  have bsq : Real.sqrt n ≤ E := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have bf32 : (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (E ^ 2) ^ 2 := by
    calc (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (f : ℝ) ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hf' (by norm_num)
      _ = (f : ℝ) ^ 2 := Real.rpow_natCast _ _
      _ ≤ (E ^ 2) ^ 2 := by gcongr
  have bfact : ((N + 1).factorial : ℝ) ≤ E ^ (4 * N) := by
    calc ((N + 1).factorial : ℝ) ≤ (((N + 1) ^ (N + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.factorial_le_pow (N + 1)
      _ = (N + 1 : ℝ) ^ (N + 1) := by push_cast; rfl
      _ ≤ (E ^ 2) ^ (N + 1) := by gcongr
      _ = E ^ (2 * (N + 1)) := by rw [← pow_mul]
      _ ≤ E ^ (4 * N) := pow_le_pow_right₀ hE1 (by omega)
  have binner : ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ)
      ≤ E ^ 17 := by
    calc ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ)
        ≤ (E * E ^ 2 * E) * (E ^ 2 * E ^ 2) * (E * (E ^ 2) ^ 2 * E ^ 2 * E ^ 2) := by gcongr
      _ = E ^ 17 := by ring
  have hpos : (0 : ℝ) < (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) := by
    have : (0 : ℝ) < N := by linarith
    have : (0 : ℝ) < n := by linarith
    have : (0 : ℝ) < a := by linarith
    have : (0 : ℝ) < f := by linarith
    have : (0 : ℝ) < rd := by linarith
    positivity
  have hle : (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) ≤ E ^ (140 * N) := by
    calc _ ≤ E * E * (E ^ (4 * N) * (E ^ 17) ^ (2 * N + 1)) := by gcongr
      _ = E ^ (2 + 4 * N + 17 * (2 * N + 1)) := by ring
      _ ≤ E ^ (140 * N) := pow_le_pow_right₀ hE1 (by omega)
  rw [Real.log_pow]
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow, hE, Real.log_exp] at hlog
  push_cast at hlog
  calc _ ≤ (a : ℝ) * (140 * N * L) := by gcongr
    _ = _ := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Harm

open MvPolynomial

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_iff_herm_of_unimod {n : ℕ} {Λ : GenLat E n} (h : Λ.Unimod) (x : Fin n → E) :
    x ∈ Λ.La ↔ ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := by
  have hI : ∀ z : E, IsIntegral ℤ z ↔ z ∈ (algebraMap (𝓞 E) E).range := fun z =>
    ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, fun ⟨o, ho⟩ => ho ▸ o.isIntegral_coe⟩
  have hc : ∀ z : E, IsIntegral ℤ (IsCMField.complexConj E z) ↔ IsIntegral ℤ z := by
    intro z
    constructor
    · intro hz
      have := hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
      simpa [IsCMField.complexConj_apply_apply] using this
    · intro hz
      exact hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  have key : ∀ y : Fin n → E, FD.herm 1 x y =
      IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FD.herm, FD.cc, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      IsCMField.complexConj_apply_apply]
  rw [h x]
  refine forall₂_congr fun y _ => ?_
  rw [key y, hc, hI]

theorem not_inPsi_and_conjugate (H : Host E) (τ : E →+* ℂ) :
    ¬ (InPsi H τ ∧ InPsi H (ComplexEmbedding.conjugate τ)) := by
  rintro ⟨h1, h2⟩
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h2
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

private theorem coe_embF {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : E) :
    ((embF c τ x : c.F) : ℂ) = τ x := rfl

theorem injective_embF_inPsi {H : Host E} {l : Level H} (c : Coeff l) :
    Function.Injective fun s : {τ : E →+* ℂ // InPsi H τ} × Bool =>
      fun x : E => embF c s.1.1 (if s.2 then FD.cc x else x) := by
  rintro ⟨⟨τ, hτ⟩, b⟩ ⟨⟨τ', hτ'⟩, b'⟩ h
  have hx : ∀ x : E, (if b then ComplexEmbedding.conjugate τ else τ) x =
      (if b' then ComplexEmbedding.conjugate τ' else τ') x := by
    intro x
    have := congrArg (fun z : c.F => (z : ℂ)) (congrFun h x)
    simp only [coe_embF] at this
    cases b <;> cases b' <;>
      simpa [FD.cc, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
        using this
  have hf : (if b then ComplexEmbedding.conjugate τ else τ) =
      (if b' then ComplexEmbedding.conjugate τ' else τ') := RingHom.ext hx
  cases b <;> cases b'
  · simp only [Bool.false_eq_true, if_false] at hf
    subst hf
    rfl
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ', by rw [← hf]; exact hτ⟩ (not_inPsi_and_conjugate H τ')
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ, by rw [hf]; exact hτ'⟩ (not_inPsi_and_conjugate H τ)
  · simp only [if_true] at hf
    have h2 := (ComplexEmbedding.involutive_conjugate E).injective hf
    subst h2
    rfl

theorem sum_norm_coeff_eq_l1Norm {K σ σ' : Type} [Field K] (e : σ ≃ σ') (f : K →+* ℂ)
    (Q : MvPolynomial σ K) :
    ∑ m ∈ Q.support, ‖f (Q.coeff m)‖ = MvPoly.l1Norm (MvPolynomial.map f (rename e Q)) := by
  rw [MvPolynomial.map_rename, MvPoly.l1Norm_rename_of_injective e.injective, MvPoly.l1Norm_map]

theorem log_le_of_le_of_log_le {x y B : ℝ} (hx : 0 ≤ x) (h : x ≤ y) (hy : Real.log y ≤ B)
    (hB : 0 ≤ B) : Real.log x ≤ B := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact hB
  · exact (Real.log_le_log hpos h).trans hy

end SlopeTestRemainingChoices

theorem exists_short_harmL_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l c n Λ hU hfg hn a L hL hrd hf hDF hnL
  classical
  let _ : Fintype {τ : E →+* ℂ // InPsi H τ} := Fintype.ofFinite _
  obtain ⟨e, hsym, hHH⟩ := theta_letter_dictionary E H Dw l c n
  have hint : ∀ x ∈ Λ.La, ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := fun x hx =>
    (mem_iff_herm_of_unimod hU x).1 hx
  have hdual : ∀ x, (∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ.La := fun x hx =>
    (mem_iff_herm_of_unimod hU x).2 hx
  have hre : ∀ M : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F,
      rename e (rename e.symm M) = M := fun M => by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
  have hre' : ∀ P : MvPolynomial (LtN Dw n) c.F, rename e.symm (rename e P) = P := fun P => by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  rcases hHH a with hzero | ⟨k, k', hdeg, hiff⟩
  · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
    rw [hzero P hP]
    exact Submodule.zero_mem _
  rcases Nat.eq_zero_or_pos (DF Dw a) with h0 | hpos
  ·
    have hconst : ∀ P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
        (fun τ i => a (τ, i)) → P = C (P.coeff 0) := by
      intro P hP
      have h1 := isHomogeneous_of_mem_rowHighest ((hiff P).1 hP)
      rw [hdeg, h0] at h1
      have h2 : (rename e P).totalDegree = 0 := Nat.le_zero.1 h1.totalDegree_le
      have h3 : P.totalDegree = 0 := by
        have := totalDegree_rename_le e.symm (rename e P)
        rw [hre', h2] at this
        exact Nat.le_zero.1 this
      exact totalDegree_eq_zero_iff_eq_C.1 h3
    by_cases h1 : (1 : MvPolynomial (LtN Dw n) c.F) ∈
        HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    · refine ⟨{1}, fun Q hQ => ?_, fun P hP => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hQ
        subst hQ
        refine ⟨⟨h1, Subring.one_mem _⟩, fun σ' => ?_⟩
        simp [h0]
      · rw [hconst P hP, ← mul_one (C (P.coeff 0)), ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · simp [h0]
    · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
      by_cases hr : P.coeff 0 = 0
      · rw [hconst P hP, hr, C_0]
        exact Submodule.zero_mem _
      · exfalso
        apply h1
        have hmem := (hiff P).1 hP
        rw [hconst P hP, rename_C] at hmem
        have h1' : (1 : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F)
            = C ((P.coeff 0)⁻¹ * P.coeff 0) := by
          rw [inv_mul_cancel₀ hr, C_1]
        rw [hiff, map_one, h1', C_mul, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hmem

  have ha1 : 1 ≤ typeDegree k k' := by rw [hdeg]; exact hpos
  have det_mem_subalgebra_of_entries_mem' {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
      (S : Subalgebra A B) {m : ℕ} (M : Matrix (Fin m) (Fin m) B) (hM : ∀ i j, M i j ∈ S) :
      M.det ∈ S := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => hM _ _) _

  have minorProd_mem_Ha_of_herm_orthogonal {Λ₀ : Submodule (𝓞 E) (Fin n → E)} {K : Type} [Field K] {T : Type} [Fintype T] {p q : ℕ}
      (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (e : Fin p → Fin n → E)
      (f : Fin q → Fin n → E) (he : ∀ a, e a ∈ Λ₀) (hf : ∀ b, f b ∈ Λ₀)
      (hef : ∀ a b, FD.herm 1 (e a) (f b) = 0) :
      minorProd c c' (fun t a k => τ t (e a k)) (fun t b k => τ t (FD.cc (f b k))) ∈ GlobalTheory.Harm.symO p q τ Λ₀ := by
    unfold GlobalTheory.Harm.symO minorProd
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
        (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
        (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · unfold xMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inl ⟨t, _, e _, he _, rfl⟩)
    · unfold yMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inr ⟨t, _, f _, hf _, rfl⟩)

  have local_short_family {Λ₀ : Submodule (𝓞 E) (Fin n → E)} (hfg : Λ₀.FG)
      (hint : ∀ x ∈ Λ₀, ∀ y ∈ Λ₀, IsIntegral ℤ (FD.herm 1 x y))
      (hdual : ∀ x, (∀ y ∈ Λ₀, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ₀)
      {p q : ℕ} (hn : p + q ≤ n) {T : Type} [Fintype T] (c : T → Fin p → ℕ)
      (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c') :
      ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
        (∀ s ∈ S, (∀ a, s.1 a ∈ Λ₀) ∧ (∀ b, s.2 b ∈ Λ₀) ∧ ∀ a b, FD.herm 1 (s.1 a) (s.2 b) = 0) ∧
        (∀ (K : Type) [Field K] (τ : T → E →+* K), ∀ s ∈ S,
          (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (FD.cc (s.2 b k))) ∈
            GlobalTheory.Harm.symO p q τ Λ₀) ∧
        (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
          (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then FD.cc x else x)) →
          Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
            minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (FD.cc (s.2 b k))) '' S) =
            rowHighest K c c') ∧
        (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
          MvPoly.l1Norm (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (FD.cc (s.2 b k))) ≤
            (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * FD.fdeg E * n) *
              ((2 * (p + q : ℕ) + 1) * typeDegree c c') *
              (2 * (FD.fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * FD.rdE E)) ^ (2 * (p + q) + 1))) ^
              typeDegree c c') ∧
        S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * FD.fdeg E * n * (2 * p + q)) := by
    classical
    obtain ⟨hfg', hint', hdual'⟩ := conjLattice_selfDual hfg hint hdual
    obtain ⟨S', hS'1, hS'2, hS'3, hS'4⟩ :=
      exists_short_harmonic_family_few_columns (Λ := conjLattice Λ₀) hfg' hint' hdual' hn c c' ha
    let cj : (Fin p → Fin n → E) × (Fin q → Fin n → E) → (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
      fun s => (fun a => conjVec E n (s.1 a), fun b => conjVec E n (s.2 b))
    have hcc : ∀ x : E, FD.cc (FD.cc x) = x := fun x => by
      have := congrFun (conjVec_conjVec (E := E) (n := 1) (fun _ => x)) 0
      simpa only [conjVec_apply] using this
    have hpoly : ∀ (K : Type) [Field K] (τ : T → E →+* K) (s : (Fin p → Fin n → E) × (Fin q → Fin n → E)),
        minorProd c c' (fun t a k => τ t ((cj s).1 a k)) (fun t b k => τ t (FD.cc ((cj s).2 b k))) =
          minorProd c c' (fun t a k => τ t (FD.cc (s.1 a k))) (fun t b k => τ t (s.2 b k)) := by
      intro K _ τ s
      simp only [cj, conjVec_apply, hcc]
    have hmem : ∀ s ∈ S', (∀ a, (cj s).1 a ∈ Λ₀) ∧ (∀ b, (cj s).2 b ∈ Λ₀) ∧
        ∀ a b, FD.herm 1 ((cj s).1 a) ((cj s).2 b) = 0 := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hS'1 s hs
      refine ⟨fun a => mem_conjLattice.mp (h1 a), fun b => mem_conjLattice.mp (h2 b), fun a b => ?_⟩
      simp only [cj]
      rw [herm_conjVec]
      exact h3 a b
    refine ⟨S'.image cj, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      exact hmem s' hs'
    · intro K _ τ s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨h1, h2, h3⟩ := hmem s' hs'
      exact minorProd_mem_Ha_of_herm_orthogonal τ c c' _ _ h1 h2 h3
    · intro K _ _ τ hτ
      rw [← hS'2 K τ hτ, Finset.coe_image, ← Set.image_comp]
      exact congrArg _ (Set.image_congr fun s _ => hpoly K τ s)
    · intro τ s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      rw [hpoly ℂ τ s']
      exact hS'3 τ s' hs'
    · exact Finset.card_image_le.trans hS'4
  obtain ⟨S0, _, hHa, hspan, hnorm, hcard⟩ := local_short_family hfg hint hdual hn k k' ha1
  have hinj := injective_embF_inPsi (H := H) c
  have hsp := hspan c.F (fun t => embF c t.1) hinj
  refine ⟨S0.image fun s => rename e.symm (minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
    fun t b kk => embF c t.1 (FD.cc (s.2 b kk))), fun Q hQ => ?_, fun P hP => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hQ
    have hM : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈ rowHighest c.F k k' := by
      rw [← hsp]
      exact Submodule.subset_span ⟨s, Finset.mem_coe.2 hs, rfl⟩
    have hS : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈
        GlobalTheory.Harm.symO Dw.p Dw.q (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La := by
      have := hHa c.F (fun t => embF c t.1) s hs
      exact this
    refine ⟨⟨(hiff _).2 (by rw [hre]; exact hM), (hsym Λ _).2 (by rw [hre]; exact hS)⟩,
      fun σ' => ?_⟩
    rw [sum_norm_coeff_eq_l1Norm e σ', hre, map_minorProd]
    have hb := hnorm (fun t => σ'.comp (embF c t.1)) s hs
    refine log_le_of_le_of_log_le (MvPoly.l1Norm_nonneg _) hb ?_ ?_
    · rw [hdeg]
      exact log_shortFamilyNumbers_le (Dw.p + Dw.q) n (DF Dw a) (FD.fdeg E) (FD.rdE E) L
        (one_le_add_of_one_le_typeDegree ha1) hn hpos one_le_fdeg one_le_rdE hL hrd hf hDF hnL
    · have hL0 : (0 : ℝ) ≤ L := by linarith
      positivity
  · have h1 : rename e P ∈ Submodule.span c.F ((fun s : (Fin Dw.p → Fin n → E) ×
        (Fin Dw.q → Fin n → E) => minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
          fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) '' ↑S0) := by
      rw [hsp]
      exact (hiff P).1 hP
    have h2 := Submodule.mem_map_of_mem
      (f := (rename (R := c.F) (⇑e.symm)).toLinearMap) h1
    rw [Submodule.map_span, ← Set.image_comp] at h2
    rw [Finset.coe_image]
    convert h2 using 1
    all_goals first
      | exact (hre' P).symm
      | simp
  · calc _ ≤ S0.card := Finset.card_image_le
      _ ≤ _ := by rw [← hdeg]; exact hcard

end GlobalTheory.Harm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodularStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_harmonic_family_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.Harm.exists_short_harmL_family | exact GlobalTheory.Harm.exists_short_harmL_family | (intros; apply GlobalTheory.Harm.exists_short_harmL_family <;> assumption)
end
