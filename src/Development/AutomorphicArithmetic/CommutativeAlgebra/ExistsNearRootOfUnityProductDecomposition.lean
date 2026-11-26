module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFactorizationNearRootOfUnityHenselian

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityLiftModNilpotentUnique
noncomputable section
open IsLocalRing UpperTheory.Et

private theorem isUnit_aeval_derivative {S : Type} [CommRing S] {q : ℕ} (hq : IsUnit (q : S)) (hq0 : q ≠ 0)
    {x : S} (hx : IsNilpotent (x ^ q - 1)) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))) := by
  have hxq : IsUnit (x ^ q) := by
    have h := IsNilpotent.isUnit_add_one hx
    simpa using h
  have hxu : IsUnit x := (isUnit_pow_iff hq0).1 hxq
  have h2 : Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))
      = (q : S) * x ^ (q - 1) := by
    simp [Polynomial.derivative_X_pow]
  rw [h2]
  exact hq.mul (hxu.pow _)

theorem UpperTheory.roots_of_unity_lift_mod_nilpotent_unique :
    ∀ (S : Type) [CommRing S] (q : ℕ), IsUnit (q : S) → (∀ x : S, IsNilpotent (x ^ q - 1) → ∃ y : S, y ^ q = 1 ∧ IsNilpotent (x - y)) ∧
      ∀ x y : S, x ^ q = 1 → y ^ q = 1 → IsNilpotent (x - y) → x = y := by
  intro S _ q hq
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : S) = 1 := by simpa using hq
    have : Subsingleton S := subsingleton_of_zero_eq_one h01
    exact ⟨fun x _ => ⟨x, Subsingleton.elim _ _, by simp⟩, fun x y _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx)
      (isUnit_aeval_derivative hq hq0 hx)
    refine ⟨y, ?_, hy1⟩
    simpa [sub_eq_zero] using hy2
  · have hx' : IsNilpotent (x ^ q - 1) := by simp [hx]
    have h := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx')
      (isUnit_aeval_derivative hq hq0 hx')
    exact h.unique ⟨by simp, by simp [hx]⟩ ⟨hxy, by simp [hy]⟩

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicLaurentPolynomialNearRootOfUnity
noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity :
    ∀ (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Int → ∀ (q : ℕ), 0 < q → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ (φ : LaurentPolynomial A →ₐ[A] D) (P : Polynomial (LaurentPolynomial A)) (n : ℕ), φ (LaurentPolynomial.T 1) = T.t ∧ φ (LaurentPolynomial.T (-1)) = T.s ∧ P.Monic ∧ P.eval₂ φ.toRingHom w = 0 ∧
        ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) := by
  intro A D _ _ _ _ T hI q hq w hw
  classical
  let τ : Dˣ := ⟨T.t, T.s, T.ts, by rw [mul_comm]; exact T.ts⟩
  let φ0 : LaurentPolynomial A →+* D := LaurentPolynomial.eval₂ (algebraMap A D) τ
  have hcomm : ∀ a : A, φ0 (algebraMap A (LaurentPolynomial A) a) = algebraMap A D a := by
    intro a
    simp [φ0, LaurentPolynomial.algebraMap_apply]
  let φ : LaurentPolynomial A →ₐ[A] D := { φ0 with commutes' := hcomm }
  have ht : φ (LaurentPolynomial.T 1) = T.t := by
    change φ0 _ = _
    simp [φ0, τ]
  have hs : φ (LaurentPolynomial.T (-1)) = T.s := by
    change φ0 _ = _
    simp [φ0, τ, zpow_neg]
  letI : Algebra (LaurentPolynomial A) D := φ.toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (LaurentPolynomial A) D r = φ r := fun _ => rfl
  have hadj : Algebra.adjoin A {T.t} ≤ φ.range := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact ⟨_, ht⟩
  have hB : ∀ b ∈ T.B, IsIntegral (LaurentPolynomial A) b := by
    intro b hb
    obtain ⟨p, hpm, hp0⟩ := hI.1 b hb
    have hl : p.map (algebraMap (Algebra.adjoin A {T.t}) D) ∈
        Polynomial.lifts (algebraMap (LaurentPolynomial A) D) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨r, hr⟩ := hadj (p.coeff n).2
      exact ⟨r, hr⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map]
    exact hp0
  have hint : Algebra.IsIntegral (LaurentPolynomial A) D := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, hk⟩ := T.locB x
    have hsI : IsIntegral (LaurentPolynomial A) T.s := by
      rw [← hs]
      exact isIntegral_algebraMap
    have : x = T.s ^ k * (T.t ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]
    rw [this]
    exact (hsI.pow k).mul (hB _ hk)
  have hu : w ^ q - 1 ∈ Ideal.map (algebraMap (LaurentPolynomial A) D)
      ((maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) := by
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro a ha d _
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : algebraMap A D a = algebraMap (LaurentPolynomial A) D (algebraMap A (LaurentPolynomial A) a) := by
        rw [hmap]
        exact (hcomm a).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    · intro x y hx hy
      exact Ideal.add_mem _ hx hy
  obtain ⟨Q, hQm, hQ0, hQc⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hu
  set I := (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) with hIdef
  have hmon : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : LaurentPolynomial A) hq.ne'
  have hdeg : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).natDegree ≠ 0 := by
    have := Polynomial.natDegree_X_pow_sub_C (n := q) (1 : LaurentPolynomial A)
    rw [map_one] at this
    rw [this]
    exact hq.ne'
  refine ⟨φ, Q.comp (Polynomial.X ^ q - 1), Q.natDegree, ht, hs, hQm.comp hmon hdeg, ?_, ?_⟩
  · rw [Polynomial.eval₂_comp]
    have : Polynomial.eval₂ φ.toRingHom w (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)) = w ^ q - 1 := by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow]
    rw [this]
    exact hQ0
  · intro i
    have hcoef : ∀ j, (Q - Polynomial.X ^ Q.natDegree).coeff j ∈ I := by
      intro j
      by_cases hj : j = Q.natDegree
      · subst hj
        have : Q.coeff Q.natDegree = 1 := hQm
        simp [this]
      · simpa [Polynomial.coeff_X_pow, hj] using hQc j hj
    have heq : Q.comp (Polynomial.X ^ q - 1) - (Polynomial.X ^ q - 1) ^ Q.natDegree =
        (Q - Polynomial.X ^ Q.natDegree).comp (Polynomial.X ^ q - 1) := by
      simp [Polynomial.sub_comp]
    rw [heq, ← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_comp]
    have : (Q - Polynomial.X ^ Q.natDegree).map (Ideal.Quotient.mk I) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hcoef j
    rw [this]
    simp

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTwoChartAdjoinRootLaurent
noncomputable section
open IsLocalRing UpperTheory.Et

section SlopeTestRemainingChoices

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

private theorem e_pow {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) (n : ℕ) :
    e 1 ^ n = e n := by
  induction n with
  | zero => simp [e0]
  | succ n ih =>
    rw [pow_succ, ih, ← ea]
    push_cast
    rfl

private theorem gen_eq {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) (r : D)
    (k i : ℕ) (a : ℤ) (h : (k : ℤ) * i ≤ a) :
    e a * r ^ i = e 1 ^ (a - k * i).toNat * (e 1 ^ k * r) ^ i := by
  have h0 : ((a - k * i).toNat : ℤ) = a - k * i := Int.toNat_of_nonneg (sub_nonneg.2 h)
  rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, e_pow e0 ea]
  congr 2
  push_cast
  rw [h0]
  ring

private theorem span_mul_mem {S : Set D} {M : Submodule A D} {c : D}
    (h : ∀ x ∈ S, c * x ∈ M) : ∀ w ∈ Submodule.span A S, c * w ∈ M := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [mul_zero]; exact M.zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact M.add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact M.smul_mem a hx

private theorem chart_eq {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) {r : D}
    {k N : ℕ}
    (hrel : r ^ N ∈ Submodule.span A
      {x : D | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧ x = e b * r ^ i}) :
    Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r}) =
      Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧ x = e a * r ^ i} := by
  set M := Submodule.span A
    {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧ x = e a * r ^ i} with hM
  have h1 : (1 : D) ∈ M := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have h10 : (1 : D) = 0 := by simpa using hrel
      rw [h10]
      exact M.zero_mem
    · exact Submodule.subset_span ⟨0, 0, hN, by simp, by simp [e0]⟩
  have ht : ∀ m ∈ M, e 1 * m ∈ M := by
    refine span_mul_mem ?_
    rintro _ ⟨a, i, hi, ha, rfl⟩
    refine Submodule.subset_span ⟨a + 1, i, hi, by linarith, ?_⟩
    rw [ea]
    ring
  have hy : ∀ m ∈ M, (e 1 ^ k * r) * m ∈ M := by
    refine span_mul_mem ?_
    rintro _ ⟨a, i, hi, ha, rfl⟩
    have hk : e 1 ^ k * r * (e a * r ^ i) = e (a + k) * r ^ (i + 1) := by
      rw [e_pow e0 ea, ea]
      ring
    rw [hk]
    by_cases hiN : i + 1 < N
    · refine Submodule.subset_span ⟨a + k, i + 1, hiN, ?_, rfl⟩
      push_cast
      linarith
    · have hN : i + 1 = N := by omega
      rw [hN]
      refine span_mul_mem ?_ _ hrel
      rintro _ ⟨b, j, hj, hb, rfl⟩
      refine Submodule.subset_span ⟨a + k + b, j, hj, ?_, ?_⟩
      · have h2 : (k : ℤ) * j ≤ k * i :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : j ≤ i)) (by positivity)
        have h3 : -(k : ℤ) ≤ b := by omega
        linarith
      · rw [ea (a + k) b]
        ring
  apply le_antisymm
  · intro x hx
    have key : ∀ x ∈ Algebra.adjoin A {e 1, e 1 ^ k * r}, ∀ m ∈ M, x * m ∈ M := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact ht
        · rw [Set.mem_singleton_iff.1 hx]
          exact hy
      | algebraMap c =>
        intro m hm
        rw [← Algebra.smul_def]
        exact M.smul_mem c hm
      | add x y _ _ hx hy =>
        intro m hm
        rw [add_mul]
        exact M.add_mem (hx m hm) (hy m hm)
      | mul x y _ _ hx hy =>
        intro m hm
        rw [mul_assoc]
        exact hx _ (hy m hm)
    simpa using key x hx 1 h1
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, i, hi, ha, rfl⟩
    rw [gen_eq e0 ea r k i a ha]
    refine Subalgebra.mem_toSubmodule _ |>.2 ?_
    exact mul_mem (pow_mem (Algebra.subset_adjoin (by simp)) _)
      (pow_mem (Algebra.subset_adjoin (by simp)) _)

private theorem chart_loc {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) {r : D}
    {k N : ℕ}
    (hall : Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} = ⊤)
    (S : Subalgebra A D) (ht : e 1 ∈ S)
    (hg : ∀ (a : ℤ) (i : ℕ), i < N → (k : ℤ) * i ≤ a → e a * r ^ i ∈ S) (x : D) :
    ∃ n : ℕ, e 1 ^ n * x ∈ S := by
  have hx : x ∈ Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} := by
    rw [hall]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, i, hi, rfl⟩ := hx
    refine ⟨((k : ℤ) * i - a).toNat, ?_⟩
    rw [← mul_assoc, e_pow e0 ea, ← ea]
    exact hg _ _ hi (by have := Int.self_le_toNat ((k : ℤ) * i - a); linarith)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have h : e 1 ^ (n + m) * (x + y) = e 1 ^ m * (e 1 ^ n * x) + e 1 ^ n * (e 1 ^ m * y) := by
      rw [pow_add]
      ring
    rw [h]
    exact add_mem (mul_mem (pow_mem ht _) hn) (mul_mem (pow_mem ht _) hm)
  | smul c x _ hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rw [mul_smul_comm]; exact S.smul_mem hn c⟩

private theorem exp_bound {A : Type} [CommRing A] (p : LaurentPolynomial A) :
    ∃ n : ℕ, ∀ m ≥ n, p ∈ Submodule.span A
      {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ m ∧ x = LaurentPolynomial.T b} := by
  refine LaurentPolynomial.induction_on' p ?_ ?_
  · rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, fun m hm => add_mem (ha m (le_of_max_le_left hm)) (hb m (le_of_max_le_right hm))⟩
  · intro n a
    refine ⟨n.natAbs, fun m hm => ?_⟩
    have h : LaurentPolynomial.C a * LaurentPolynomial.T n = a • LaurentPolynomial.T n := by
      rw [Algebra.smul_def]
      rfl
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hm, rfl⟩)

private theorem assemble {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) {r : D}
    {k N : ℕ} (β : Module.Basis (ℤ × Fin N) A D) (hβ : ∀ p, β p = e p.1 * r ^ (p.2 : ℕ))
    (hrel : r ^ N ∈ Submodule.span A
      {x : D | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧ x = e b * r ^ i}) :
    ∃ T : TC A D, T.Fin ∧ T.Coord ∧ T.t = e 1 ∧ T.s = e (-1) ∧
      T.B = Algebra.adjoin A {T.t, T.t ^ k * r} ∧ T.C = Algebra.adjoin A {T.s, T.s ^ k * r} := by
  classical
  have e0' : (fun a => e (-a)) 0 = 1 := by simpa using e0
  have ea' : ∀ a b, (fun a => e (-a)) (a + b) = (fun a => e (-a)) a * (fun a => e (-a)) b :=
    fun a b => by simp only [neg_add, ea]
  have himg : ∀ Q : ℤ → ℕ → Prop, β '' {p | Q p.1 p.2} =
      {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ Q a i ∧ x = e a * r ^ i} := by
    intro Q
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, p.2, p.2.2, hp, hβ p⟩
    · rintro ⟨a, i, hi, hq, rfl⟩
      exact ⟨(a, ⟨i, hi⟩), hq, hβ _⟩
  have hall : Submodule.span A
      {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} = ⊤ := by
    rw [eq_top_iff, ← β.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨p, rfl⟩
    exact ⟨p.1, p.2, p.2.2, hβ p⟩
  have hall' : Submodule.span A
      {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = (fun a => e (-a)) a * r ^ i} = ⊤ := by
    rw [eq_top_iff, ← hall]
    apply Submodule.span_mono
    rintro _ ⟨a, i, hi, rfl⟩
    exact ⟨-a, i, hi, by simp⟩
  have hrel' : r ^ N ∈ Submodule.span A
      {x | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧
        x = (fun a => e (-a)) b * r ^ i} := by
    refine Submodule.span_mono ?_ hrel
    rintro _ ⟨b, i, hi, hb, rfl⟩
    exact ⟨-b, i, hi, by simpa using hb, by simp⟩
  have hB := chart_eq (A := A) e0 ea hrel
  have hC := chart_eq (A := A) (e := fun a => e (-a)) e0' ea' hrel'
  have hsum : e 1 * e (-1) = 1 := by rw [← ea]; simpa using e0
  let T : TC A (D) :=
    { B := Algebra.adjoin A {e 1, e 1 ^ k * r}
      C := Algebra.adjoin A {e (-1), e (-1) ^ k * r}
      t := e 1
      s := e (-1)
      ts := hsum
      tB := Algebra.subset_adjoin (by simp)
      sC := Algebra.subset_adjoin (by simp)
      locB := chart_loc (k := k) e0 ea hall _ (Algebra.subset_adjoin (by simp)) (fun a i hi ha => by
        have h : e a * r ^ i ∈ Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r}) := by
          rw [hB]
          exact Submodule.subset_span ⟨a, i, hi, ha, rfl⟩
        exact h)
      locC := chart_loc (k := k) (e := fun a => e (-a)) e0' ea' hall' _ (Algebra.subset_adjoin (by simp)) (fun a i hi ha => by
        have h : (fun a => e (-a)) a * r ^ i ∈ Subalgebra.toSubmodule
            (Algebra.adjoin A {(fun a => e (-a)) 1, (fun a => e (-a)) 1 ^ k * r}) := by
          rw [hC]
          exact Submodule.subset_span ⟨a, i, hi, ha, rfl⟩
        exact h) }
  refine ⟨T, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · refine ⟨(Finset.range N).image (fun i => (e 1 ^ k * r) ^ i), ?_, ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
      exact pow_mem (Algebra.subset_adjoin (by simp)) i
    · intro b hb
      have hb' : b ∈ Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r}) := hb
      rw [hB] at hb'
      refine Submodule.span_mono ?_ hb'
      rintro _ ⟨a, i, hi, ha, rfl⟩
      exact ⟨(e 1 ^ k * r) ^ i, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩,
        (a - k * i).toNat, gen_eq e0 ea r k i a ha⟩
  · refine ⟨ℤ × Fin N, β, {p | (k : ℤ) * ((p.2 : ℕ) : ℤ) ≤ p.1},
      fun j => {p | p.1 ≤ (j : ℤ) - k * ((p.2 : ℕ) : ℤ)}, ?_, fun j => ⟨?_, ?_⟩⟩
    · exact hB.trans (congrArg (Submodule.span A) (himg fun a i => (k : ℤ) * i ≤ a).symm)
    · have hsj : e (-1) ^ j = e (-(j : ℤ)) := e_pow (e := fun a => e (-a)) e0' ea' j
      have hjj : e (-(j : ℤ)) * e j = 1 := by rw [← ea]; simpa using e0
      have hmap : (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j)) =
          (Subalgebra.toSubmodule T.C).map (LinearMap.mulLeft A (e j)) := by
        ext x
        constructor
        · intro hx
          refine ⟨e (-(j : ℤ)) * x, ?_, ?_⟩
          · have h : T.s ^ j * x ∈ Subalgebra.toSubmodule T.C := hx
            rw [show T.s ^ j = e (-(j : ℤ)) from hsj] at h
            exact h
          · simp only [LinearMap.mulLeft_apply]
            rw [← mul_assoc, mul_comm (e j), hjj, one_mul]
        · rintro ⟨m, hm, rfl⟩
          have h : T.s ^ j * (e j * m) = m := by
            rw [show T.s ^ j = e (-(j : ℤ)) from hsj, ← mul_assoc, hjj, one_mul]
          show T.s ^ j * (e j * m) ∈ Subalgebra.toSubmodule T.C
          rw [h]
          exact hm
      have hC2 : Subalgebra.toSubmodule T.C = Submodule.span A
          {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧
            x = (fun a => e (-a)) a * r ^ i} := hC
      rw [hmap, hC2, Submodule.map_span]
      refine congrArg (Submodule.span A) ?_
      refine Eq.trans ?_ (himg fun a i => a ≤ (j : ℤ) - k * i).symm
      ext x
      constructor
      · rintro ⟨_, ⟨a, i, hi, ha, rfl⟩, rfl⟩
        refine ⟨j - a, i, hi, by linarith, ?_⟩
        simp only [LinearMap.mulLeft_apply]
        rw [← mul_assoc, ← ea, sub_eq_add_neg]
      · rintro ⟨a, i, hi, ha, rfl⟩
        refine ⟨_, ⟨j - a, i, hi, by linarith, rfl⟩, ?_⟩
        simp only [LinearMap.mulLeft_apply]
        rw [← mul_assoc, ← ea]
        congr 2
        ring
    · refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) j).prod Set.finite_univ) ?_
      rintro ⟨a, i⟩ ⟨h1, h2⟩
      have h1' : (k : ℤ) * ((i : ℕ) : ℤ) ≤ a := h1
      have h2' : a ≤ (j : ℤ) - k * ((i : ℕ) : ℤ) := h2
      have h0 : (0 : ℤ) ≤ k * ((i : ℕ) : ℤ) := by positivity
      exact ⟨⟨by linarith, by linarith⟩, trivial⟩

end SlopeTestRemainingChoices

private theorem basis_model {A : Type} [CommRing A] {P : Polynomial (LaurentPolynomial A)}
    (hP : P.Monic) : ∃ β : Module.Basis (ℤ × Fin P.natDegree) A (AdjoinRoot P),
      ∀ p, β p = AdjoinRoot.of P (LaurentPolynomial.T p.1) * AdjoinRoot.root P ^ (p.2 : ℕ) := by
  let pb := (AdjoinRoot.powerBasis' hP).basis.reindex (finCongr (AdjoinRoot.powerBasis'_dim hP))
  refine ⟨(AddMonoidAlgebra.basis ℤ A).smulTower pb, fun p => ?_⟩
  rw [Module.Basis.smulTower_apply, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen, Algebra.smul_def]
  simp only [AddMonoidAlgebra.basis_apply]
  rfl

private theorem rel_model {A : Type} [CommRing A] {P : Polynomial (LaurentPolynomial A)}
    (hP : P.Monic) {k : ℕ} (hk : ∀ i < P.natDegree, P.coeff i ∈ Submodule.span A
      {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ k ∧ x = LaurentPolynomial.T b}) :
    AdjoinRoot.root P ^ P.natDegree ∈ Submodule.span A
      {x : AdjoinRoot P | ∃ (b : ℤ) (i : ℕ), i < P.natDegree ∧ b.natAbs ≤ k ∧
        x = AdjoinRoot.of P (LaurentPolynomial.T b) * AdjoinRoot.root P ^ i} := by
  have hof : ∀ (c : A) (x : LaurentPolynomial A),
      AdjoinRoot.of P (c • x) = c • AdjoinRoot.of P x := by
    intro c x
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]
  have hev := congrArg (Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)) hP.as_sum
  rw [AdjoinRoot.eval₂_root] at hev
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hev
  have hr : AdjoinRoot.root P ^ P.natDegree =
      -∑ i ∈ Finset.range P.natDegree, AdjoinRoot.of P (P.coeff i) * AdjoinRoot.root P ^ i :=
    eq_neg_of_add_eq_zero_left hev.symm
  rw [hr]
  refine neg_mem (sum_mem fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  have hc := hk i hi'
  generalize P.coeff i = c at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨b, i, hi', hb, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), add_mul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [hof, smul_mul_assoc]
    exact Submodule.smul_mem _ _ hx

theorem UpperTheory.exists_twoChart_adjoinRoot_laurent :
    ∀ (A : Type) [CommRing A] (P : Polynomial (LaurentPolynomial A)), P.Monic → ∀ k₀ : ℕ, ∃ k ≥ k₀, ∃ T : TC A (AdjoinRoot P), T.Fin ∧ T.Coord ∧
      T.t = AdjoinRoot.of P (LaurentPolynomial.T 1) ∧ T.s = AdjoinRoot.of P (LaurentPolynomial.T (-1)) ∧
      T.B = Algebra.adjoin A {T.t, T.t ^ k * AdjoinRoot.root P} ∧ T.C = Algebra.adjoin A {T.s, T.s ^ k * AdjoinRoot.root P} := by
  intro A _ P hP k₀
  obtain ⟨k, hk0, hk⟩ : ∃ k ≥ k₀, ∀ i < P.natDegree, P.coeff i ∈ Submodule.span A
      {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ k ∧ x = LaurentPolynomial.T b} := by
    choose f hf using fun i => exp_bound (P.coeff i)
    refine ⟨k₀ + ∑ i ∈ Finset.range P.natDegree, f i, Nat.le_add_right _ _, fun i hi => hf i _ ?_⟩
    exact (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)).trans
      (Nat.le_add_left _ _)
  have e0 : (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) 0 = 1 := by
    show AdjoinRoot.of P (LaurentPolynomial.T 0) = 1
    rw [LaurentPolynomial.T_zero, map_one]
  have ea : ∀ a b : ℤ, (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) (a + b) =
      (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) a *
        (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) b := fun a b => by
    show AdjoinRoot.of P (LaurentPolynomial.T (a + b)) = _
    rw [LaurentPolynomial.T_add, map_mul]
  obtain ⟨β, hβ⟩ := basis_model hP
  obtain ⟨T, h1, h2, h3, h4, h5, h6⟩ := assemble (k := k) e0 ea β hβ (rel_model hP hk)
  exact ⟨k, hk0, T, h1, h2, h3, h4, h5, h6⟩

end
end

noncomputable section
open IsLocalRing UpperTheory.Et

private lemma mem_mm_top_iff {A D : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (x : D) :
    x ∈ mm (⊤ : Subalgebra A D) ↔ x ∈ (maximalIdeal A).map (algebraMap A D) := by
  simp [mm, Algebra.top_toSubmodule, Ideal.smul_top_eq_map]

private lemma mm_map {A E D : Type} [CommRing A] [IsLocalRing A] [CommRing E] [Algebra A E] [CommRing D] [Algebra A D]
    (ψ : E →ₐ[A] D) (B₀ : Subalgebra A E) (B : Subalgebra A D) (h : ∀ x ∈ B₀, ψ x ∈ B) {x : E}
    (hx : x ∈ mm B₀) : ψ x ∈ mm B := by
  unfold mm at hx ⊢
  exact Submodule.smul_induction_on (p := fun z => ψ z ∈ maximalIdeal A • Subalgebra.toSubmodule B) hx
    (fun r hr y hy => by
      rw [AlgHom.map_smul_of_tower]
      exact Submodule.smul_mem_smul hr (h y hy))
    (fun a b ha hb => by
      rw [map_add (f := _)]
      exact add_mem ha hb)

private lemma adjoin_map {A E D : Type} [CommRing A] [CommRing E] [Algebra A E] [CommRing D] [Algebra A D]
    (ψ : E →ₐ[A] D) (S : Set E) (B : Subalgebra A D) (h : ∀ x ∈ S, ψ x ∈ B) :
    ∀ x ∈ Algebra.adjoin A S, ψ x ∈ B := by
  intro x hx
  exact (Algebra.adjoin_le (S := B.comap ψ) h) hx

private lemma root_mem {S K : Type} [CommRing S] [Nontrivial S] [CommRing K] [IsDomain K] (f : S →+* K)
    (h : ∀ p : Polynomial S, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) (x : K) :
    ∀ (n : ℕ) (p : Polynomial S), p.Monic → p.natDegree = n → p.eval₂ f x = 0 → ∃ a : S, f a = x := by
  intro n
  induction n with
  | zero =>
    intro p hp hdeg hx
    rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg] at hx
    simp at hx
  | succ n ih =>
    intro p hp hdeg hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr ha
    have hmX : (Polynomial.X - Polynomial.C a).Monic := Polynomial.monic_X_sub_C a
    have hp' : ((Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a))).Monic := by
      rw [hfac]
      exact hp
    have hmq : (p /ₘ (Polynomial.X - Polynomial.C a)).Monic := hmX.of_mul_monic_left hp'
    have hdq : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree = n := by
      have := hmX.natDegree_mul hmq
      rw [hfac, hdeg, Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp [sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hmq hdq h1

private lemma unity_ratio {A D : Type} [CommRing A] [CommRing D] [IsDomain D] [Algebra A D]
    (C : Subalgebra A D) (hC : Roots C) (q : ℕ) (hq : 0 < q) (a b : D) (h : a ^ q = b ^ q) :
    ∃ η ∈ C, η ^ q = 1 ∧ a = η * b := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨1, one_mem _, one_pow _, ?_⟩
    simp [zero_pow hq.ne', pow_eq_zero_iff hq.ne'] at h
    simp [h]
  · have hinj := IsFractionRing.injective D (FractionRing D)
    have hbK : algebraMap D (FractionRing D) b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    have hbq : algebraMap D (FractionRing D) (b ^ q) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero q hb)
    obtain ⟨η, hη⟩ := root_mem ((algebraMap D (FractionRing D)).comp C.val.toRingHom) hC
      (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b) q
      (Polynomial.X ^ q - Polynomial.C 1) (Polynomial.monic_X_pow_sub_C 1 hq.ne')
      (Polynomial.natDegree_X_pow_sub_C 1)
      (by simp [div_pow, ← map_pow, h, div_self hbq])
    have hη' : algebraMap D (FractionRing D) (η : D) = algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b := hη
    refine ⟨η, η.2, ?_, ?_⟩
    · apply hinj
      rw [map_pow, map_one, hη', div_pow, ← map_pow, ← map_pow, h, div_self hbq]
    · apply hinj
      rw [map_mul, hη', div_mul_cancel₀ _ hbK]

private lemma qth_root {A D : Type} [CommRing A] [CommRing D] [IsDomain D] [Algebra A D]
    (S : Subalgebra A D) (hS : Roots S) (q : ℕ) (hq : 0 < q) (c : D) (hc : c ∈ S) :
    ∃ u ∈ S, u ^ q = c := by
  obtain ⟨a, ha⟩ := hS (Polynomial.X ^ q - Polynomial.C ⟨c, hc⟩) (Polynomial.monic_X_pow_sub_C _ hq.ne')
    (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hq)
  refine ⟨a, a.2, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at ha
  have := congrArg Subtype.val (sub_eq_zero.mp ha)
  simpa using this

private lemma pow_root_mem {A : Type} [CommRing A] [IsLocalRing A] (P : Polynomial (LaurentPolynomial A))
    (q n : ℕ)
    (hP : ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) :
    (AdjoinRoot.root P ^ q - 1) ^ n ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)) := by
  have key : (AdjoinRoot.root P ^ q - 1) ^ n =
      -((P - (Polynomial.X ^ q - 1) ^ n).eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)) := by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, AdjoinRoot.eval₂_root]
  rw [key, Polynomial.eval₂_eq_sum_range]
  refine neg_mem (sum_mem fun i _ => ?_)
  apply Ideal.mul_mem_right
  have hm := Ideal.mem_map_of_mem (AdjoinRoot.of P) (hP i)
  rwa [Ideal.map_map, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_eq] at hm

private theorem adjoinRoot_liftAlgHom_of_laurent {A D : Type} [CommRing A] [CommRing D] [Algebra A D]
    {P : Polynomial (LaurentPolynomial A)} (φ : LaurentPolynomial A →ₐ[A] D) (w : D)
    (h : Polynomial.eval₂ φ.toRingHom w P = 0) (z : LaurentPolynomial A) :
    AdjoinRoot.liftAlgHom P φ w h (AdjoinRoot.of P z) = φ z :=
  AdjoinRoot.liftAlgHom_of P φ w h z

theorem UpperTheory.exists_near_root_of_unity_product_decomposition :
    ∀ (A D : Type) [CommRing A] [HenselianLocalRing A] [CommRing D] [Algebra A D] [IsDomain D] (T : TC A D), T.Int → Roots T.B → Roots T.C → ∀ (q : ℕ), IsUnit (q : A) → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ u ∈ T.B, ∃ v ∈ T.C, u ^ q - 1 ∈ mm T.B ∧ v ^ q - 1 ∈ mm T.C ∧ w - u * v ∈ mm (⊤ : Subalgebra A D) := by
  intro A D _ _ _ _ _ T hInt hB hC q hq w hw
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      simp at hq
    · exact h0
  have hmono : ∀ (S : Subalgebra A D) (x : D), x ∈ mm S → x ∈ mm (⊤ : Subalgebra A D) :=
    fun S x hx => mm_map (AlgHom.id A D) S ⊤ (fun _ _ => Algebra.mem_top) hx
  obtain ⟨φ, P, n, hφt, hφs, hPm, hPw, hPc⟩ := UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity A D T hInt q hq0 w hw
  obtain ⟨kB, hkB⟩ := T.locB w
  obtain ⟨kC, hkC⟩ := T.locC w
  obtain ⟨k, hk, T', hFin, hCoord, ht', hs', hB', hC'⟩ := UpperTheory.exists_twoChart_adjoinRoot_laurent A P hPm (max kB kC)
  let ψ : AdjoinRoot P →ₐ[A] D := AdjoinRoot.liftAlgHom P φ w hPw
  have hψr : ψ (AdjoinRoot.root P) = w := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψt : ψ T'.t = T.t := by
    rw [ht']
    exact (adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφt
  have hψs : ψ T'.s = T.s := by
    rw [hs']
    exact (adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφs
  have hψB : ∀ x ∈ T'.B, ψ x ∈ T.B := by
    rw [hB']
    apply adjoin_map
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hψt]
      exact T.tB
    · rw [map_mul, map_pow, hψt, hψr]
      have e : T.t ^ k * w = T.t ^ (k - kB) * (T.t ^ kB * w) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_left _ _) hk)]
      rw [e]
      exact mul_mem (pow_mem T.tB _) hkB
  have hψC : ∀ x ∈ T'.C, ψ x ∈ T.C := by
    rw [hC']
    apply adjoin_map
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hψs]
      exact T.sC
    · rw [map_mul, map_pow, hψs, hψr]
      have e : T.s ^ k * w = T.s ^ (k - kC) * (T.s ^ kC * w) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_right _ _) hk)]
      rw [e]
      exact mul_mem (pow_mem T.sC _) hkC
  have hqS : IsUnit ((q : AdjoinRoot P ⧸ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)))) := by
    have := hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))).comp
      (algebraMap A (AdjoinRoot P)))
    rwa [map_natCast] at this
  have hnil : IsNilpotent ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))
      (AdjoinRoot.root P)) ^ q - 1) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact pow_root_mem P q n hPc
  obtain ⟨y, hyq, hynil⟩ := (UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqS).1 _ hnil
  obtain ⟨ω, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hω : ω ^ q - 1 ∈ mm (⊤ : Subalgebra A (AdjoinRoot P)) := by
    rw [mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hyq, sub_self]
  obtain ⟨g', hg'B, g, hgC, μ, hg'1, hg1, hμ, hgg⟩ := UpperTheory.exists_factorization_near_root_of_unity_henselian A (AdjoinRoot P) T' hFin hCoord q hq ω hω
  have hG' : ψ g' ∈ T.B := hψB g' hg'B
  have hG : ψ g ∈ T.C := hψC g hgC
  have hG'1 : ψ g' - 1 ∈ mm T.B := by
    have := mm_map ψ T'.B T.B hψB hg'1
    rwa [map_sub, map_one] at this
  have hG1 : ψ g - 1 ∈ mm T.C := by
    have := mm_map ψ T'.C T.C hψC hg1
    rwa [map_sub, map_one] at this
  have hM : ψ μ - ψ ω ∈ mm (⊤ : Subalgebra A D) := by
    have := mm_map ψ ⊤ ⊤ (fun _ _ => Algebra.mem_top) hμ
    rwa [map_sub] at this
  have hGG : ψ g * ψ g' = (ψ μ) ^ q := by
    rw [← map_mul, hgg, map_pow]
  obtain ⟨u, hu, huq⟩ := qth_root T.B hB q hq0 (ψ g') hG'
  obtain ⟨v, hv, hvq⟩ := qth_root T.C hC q hq0 (ψ g) hG
  obtain ⟨η, hη, hηq, hηe⟩ := unity_ratio T.C hC q hq0 (ψ μ) (u * v)
    (by rw [mul_pow, huq, hvq, ← hGG, mul_comm])
  refine ⟨u, hu, η * v, mul_mem hη hv, ?_, ?_, ?_⟩
  · rw [huq]
    exact hG'1
  · rw [mul_pow, hηq, one_mul, hvq]
    exact hG1
  have hμe : u * (η * v) = ψ μ := by
    rw [hηe]
    ring
  rw [hμe]
  have hqD : IsUnit ((q : D ⧸ (maximalIdeal A).map (algebraMap A D))) := by
    have := hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D))).comp (algebraMap A D))
    rwa [map_natCast] at this
  have toQ : ∀ x : D, x ∈ mm (⊤ : Subalgebra A D) →
      Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) x = 0 := by
    intro x hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← mem_mm_top_iff]
    exact hx
  rw [mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply (UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqD).2
  · have := toQ _ hw
    rwa [map_sub, map_pow, map_one, sub_eq_zero] at this
  · have e1 := toQ _ (hmono _ _ hG1)
    have e2 := toQ _ (hmono _ _ hG'1)
    rw [map_sub, map_one, sub_eq_zero] at e1 e2
    rw [← map_pow, ← hGG, map_mul, e1, e2, one_mul]
  · obtain ⟨N, hN⟩ := hynil
    refine ⟨N, ?_⟩
    have h1 : (AdjoinRoot.root P - ω) ^ N ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub]
      exact hN
    have h2 : ψ ((AdjoinRoot.root P - ω) ^ N) ∈ (maximalIdeal A).map (algebraMap A D) := by
      have := Ideal.mem_map_of_mem (ψ : AdjoinRoot P →+* D) h1
      rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
    have h3 : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ μ) =
        Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ ω) := by
      rw [← sub_eq_zero, ← map_sub]
      exact toQ _ hM
    rw [h3, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← hψr, ← map_sub, ← map_pow]
    exact h2

end
