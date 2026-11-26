module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.PrimeMaximalOrKernel
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem prime_maximal_or_kernel (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (P : Ideal B) [hP : P.IsPrime]
    [Module.Finite O (B ⧸ P)] :
    P = maximalIdeal B ∨ ((∀ c : O, c ≠ 0 → algebraMap O B c ∉ P) ∧ ∃ σ : B →ₐ[O] K, RingHom.ker σ = P) := by
  classical
  haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  have hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P := by
    intro a
    rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  by_cases hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P
  · obtain ⟨c, hc0, hcP⟩ := hc
    left
    apply IsLocalRing.eq_maximalIdeal
    have hQ : (P.comap (algebraMap O B)).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)
      intro h
      have hmem : c ∈ P.comap (algebraMap O B) := hcP
      rw [h] at hmem
      exact hc0 ((Submodule.mem_bot O).1 hmem)
    have hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B) := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]
    haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.isPrime_bot
    have hmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) (⊥ : Ideal (B ⧸ P)) (by
      change ((⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P))).IsMaximal
      rw [hbot]
      exact hQ)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact Ring.isField_iff_maximal_bot.2 hmax
  · push_neg at hc
    right
    refine ⟨hc, ?_⟩
    have hinj : Function.Injective (algebraMap O (B ⧸ P)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact hc a h0 ((hcomap a).1 ha)
    haveI : Module.IsTorsionFree O (B ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
    haveI : Module.IsTorsionFree O K :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)
    haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let τ : (B ⧸ P) →ₐ[O] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩
    have hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O)
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0
      rw [AlgHom.commutes]
      constructor
      · intro h
        exact FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hτi : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ
    ext b
    rw [RingHom.mem_ker]
    change τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P
    rw [map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]

theorem UpperTheory.V.Alg.M.emb_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I →
    ∀ P : Ideal (𝒜 0), P.IsPrime → (∀ b : 𝒜 0, (b : A) ∈ I → b ∈ P) →
      (P = maximalIdeal (𝒜 0) ∨ ((∀ c : O, c ≠ 0 → algebraMap O (𝒜 0) c ∉ P) ∧ ∃ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = P)) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP
  let φ : 𝒜 0 →ₗ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype
  have hr : (LinearMap.range φ).FG := by
    have : LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [this]; exact hM
  haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr
  haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm
  let ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P) := (Ideal.Quotient.mkₐ O P).toLinearMap
  have hk : LinearMap.ker φ ≤ LinearMap.ker ψ := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))
  haveI : Module.Finite O (𝒜 0 ⧸ P) := by
    refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  exact prime_maximal_or_kernel O K (𝒜 0) P
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NsPoint
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped TensorProduct

private theorem ns_point (K R : Type) [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (Q : Ideal R) (hQ : Q.IsPrime) (x : R) (hx : x ∉ Q) :
    ∃ ψ : R →ₐ[K] K, (∀ y ∈ Q, ψ y = 0) ∧ ψ x ≠ 0 := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hj : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hx
  push Not at hx
  obtain ⟨M, ⟨hQM, hM⟩, hxM⟩ := hx
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  haveI : Algebra.IsAlgebraic K (R ⧸ M) := Algebra.IsAlgebraic.of_finite K _
  let e : (R ⧸ M) →ₐ[K] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨e.comp (Ideal.Quotient.mkₐ K M), fun y hy => ?_, ?_⟩
  · have : Ideal.Quotient.mk M y = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hQM hy)
    simp [this]
  · have : Ideal.Quotient.mk M x ≠ 0 := fun h => hxM (Ideal.Quotient.eq_zero_iff_mem.1 h)
    simpa using this

private theorem ns_prime (B A K : Type) [CommRing B] [CommRing A] [Field K] [Algebra B A] [Algebra B K]
    (P : Ideal A) [P.IsPrime] (hP : ∀ b, algebraMap B A b ∈ P ↔ algebraMap B K b = 0) :
    ∃ Q : Ideal (K ⊗[B] A), Q.IsPrime ∧ ∀ a : A, (1 : K) ⊗ₜ[B] a ∈ Q ↔ a ∈ P := by
  let p : Ideal B := P.under B
  haveI : p.IsPrime := inferInstance
  have h1 : p ≤ RingHom.ker (algebraMap B K) := fun b hb => (hP b).1 hb
  have h2 : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap B K) := fun b hb =>
    (isUnit_iff_ne_zero.2 (fun h => hb ((hP b).2 h)) : IsUnit (algebraMap B K b))
  have h1' : p ≤ RingHom.ker (algebraMap B P.ResidueField) := fun b hb => by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero]
    exact hb
  have h2' : p.primeCompl ≤ (IsUnit.submonoid P.ResidueField).comap (algebraMap B P.ResidueField) :=
    fun b hb => (isUnit_iff_ne_zero.2 (fun h => hb (by
      rw [IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero] at h
      exact h)) : IsUnit (algebraMap B P.ResidueField b))
  letI aK : Algebra p.ResidueField K := (Ideal.ResidueField.lift p _ h1 h2).toAlgebra
  letI aL : Algebra p.ResidueField P.ResidueField := (Ideal.ResidueField.lift p _ h1' h2').toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1 h2 b).symm
  haveI : IsScalarTower B p.ResidueField P.ResidueField := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1' h2' b).symm
  let T := K ⊗[p.ResidueField] P.ResidueField
  haveI : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    p.ResidueField K P.ResidueField (RingHom.injective _) (RingHom.injective _)
  obtain ⟨N, hN⟩ := Ideal.exists_maximal T
  let i1 : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft (S := B))
  let j : P.ResidueField →ₐ[p.ResidueField] T := Algebra.TensorProduct.includeRight
  let i2 : A →ₐ[B] T := (j.restrictScalars B).comp (IsScalarTower.toAlgHom B A P.ResidueField)
  let φ : K ⊗[B] A →ₐ[B] T := Algebra.TensorProduct.lift i1 i2 (fun _ _ => Commute.all _ _)
  refine ⟨N.comap φ, Ideal.comap_isPrime _ _, fun a => ?_⟩
  have hφ : φ ((1 : K) ⊗ₜ[B] a) = j (algebraMap A P.ResidueField a) := by
    simp [φ, i2]
  rw [Ideal.mem_comap, hφ]
  constructor
  · intro h
    by_contra ha
    have hu : IsUnit (algebraMap A P.ResidueField a) :=
      isUnit_iff_ne_zero.2 (fun h => ha (Ideal.algebraMap_residueField_eq_zero.1 h))
    exact hN.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.map j))
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
    exact N.zero_mem

theorem UpperTheory.V.Alg.M.ns_holds :
    ∀ (O B A K : Type) [CommRing O] [CommRing B] [CommRing A] [Field K] [IsAlgClosed K] [Algebra O B] [Algebra B A]
      [Algebra O A] [IsScalarTower O B A] [Algebra O K] [Algebra.FiniteType B A] (σ : B →ₐ[O] K) (J : Ideal A) (f : A),
      (∀ b, σ b = 0 → algebraMap B A b ∈ J) → (∀ (b : B) (n : ℕ), σ b ≠ 0 → algebraMap B A b * f ^ n ∉ J) →
      ∃ ξ : A →ₐ[O] K, (∀ b, ξ (algebraMap B A b) = σ b) ∧ (∀ g ∈ J, ξ g = 0) ∧ ξ f ≠ 0 := by
  intro O B A K _ _ _ _ _ _ _ _ _ _ _ σ J f h0 h1
  let S : Submonoid A :=
    { carrier := {a | ∃ (b : B) (n : ℕ), σ b ≠ 0 ∧ a = algebraMap B A b * f ^ n}
      one_mem' := ⟨1, 0, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, n, hb, rfl⟩ ⟨c, m, hc, rfl⟩
        exact ⟨b * c, n + m, by simp [hb, hc], by rw [map_mul]; ring⟩ }
  have hd : Disjoint (J : Set A) (S : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ha ⟨b, n, hb, rfl⟩
    exact h1 b n hb ha
  obtain ⟨P, hP, hJP, hPS⟩ := Ideal.exists_le_prime_disjoint J S hd
  rw [Set.disjoint_left] at hPS
  letI : Algebra B K := σ.toRingHom.toAlgebra
  have hσ : ∀ b, algebraMap B K b = σ b := fun _ => rfl
  haveI : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun o => by
    rw [hσ, AlgHom.commutes]
  obtain ⟨Q, hQ, hQP⟩ := ns_prime B A K P (fun b => by
    rw [hσ]
    constructor
    · intro hb
      by_contra hne
      exact hPS hb ⟨b, 0, hne, by simp⟩
    · intro hb
      exact hJP (h0 b hb))
  have hf : f ∉ P := fun h => hPS h ⟨1, 1, by simp, by simp⟩
  obtain ⟨ψ, hψ0, hψ1⟩ := ns_point K (K ⊗[B] A) Q hQ ((1 : K) ⊗ₜ[B] f) (fun h => hf ((hQP f).1 h))
  let ξ : A →ₐ[B] K := (ψ.restrictScalars B).comp Algebra.TensorProduct.includeRight
  refine ⟨ξ.restrictScalars O, fun b => ?_, fun g hg => ?_, hψ1⟩
  · exact (ξ.commutes b).trans (hσ b)
  · exact hψ0 _ ((hQP g).2 (hJP hg))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ValuationNonnegApplyDegreeZeroOfOnS
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IntHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.int_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v → ∀ y : K, IsIntegral O y → y ≠ 0 → 0 ≤ v y := by
  intro O _ _ _ _ _ K _ _ _ _ v hv y hy hy0
  have v1 : v 1 = 0 := by
    have h := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    linarith
  have vneg : ∀ z : K, z ≠ 0 → v (-z) = v z := by
    intro z hz
    have h1 := hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, v1] at h1
    have h2 := hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz
    rw [neg_one_mul] at h2
    linarith
  have vpow : ∀ k : ℕ, v (y ^ k) = k * v y := by
    intro k
    induction k with
    | zero => simp [v1]
    | succ k ih =>
      rw [pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]
      push_cast
      ring
  have vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => intro _ h; simp at h
    | insert a s ha ih =>
      intro hf hs
      rw [Finset.sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hs ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs
      by_cases hS : (∑ i ∈ s, f i) = 0
      · rw [hS, add_zero]
        exact hf a (Finset.mem_insert_self a s) hfa
      have h1 := hv.add _ _ hfa hS hs
      have h2 := hf a (Finset.mem_insert_self a s) hfa
      have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS
      exact le_trans (le_min h2 h3) h1
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hpm, hp⟩ := hy
  have hsum := hp
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hsum
  have hyn : y ^ p.natDegree ≠ 0 := pow_ne_zero _ hy0
  have hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.mpr hyn
  have hnpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [h, Finset.sum_range_zero, pow_zero] at hS
      exact one_ne_zero (neg_eq_zero.mp hS.symm)
    · exact h
  have hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 →
      ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i) := by
    intro i hi hne
    have hc : p.coeff i ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hmc : algebraMap O K (p.coeff i) ≠ 0 := by
      intro h
      apply hc
      exact (FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])
    rw [hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y := by
      apply mul_le_mul_of_nonpos_right _ hneg.le
      exact_mod_cast hi'
    have h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤
      v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) :=
    vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0
  rw [hS, vneg _ hyn, vpow, Nat.cast_pred hnpos] at hbound
  linarith
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.valuation_nonneg_apply_degreeZero_of_onS :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I → ∀ ξ : A →ₐ[O] K, OnS I ξ → ∀ b ∈ 𝒜 0, ξ b ≠ 0 → 0 ≤ v (ξ b) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x I hI ξ hξ b hb hne
  classical
  set M : Submodule O K := Submodule.map ξ.toLinearMap (𝒜 0) with hMdef
  have hker : ∀ f ∈ I, ξ f = 0 := hξ
  let ξ' : (A ⧸ I) →ₐ[O] K := Ideal.Quotient.liftₐ I ξ hker
  have hcomp : ξ.toLinearMap = ξ'.toLinearMap.comp (Ideal.Quotient.mkₐ O I).toLinearMap := by
    apply LinearMap.ext
    intro a
    rfl
  have hMfg : M.FG := by
    rw [hMdef, hcomp, Submodule.map_comp]
    exact Submodule.FG.map _ hI
  haveI : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hMfg
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {ξ b}) ≤ M := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin O {ξ b} := hz
    clear hz
    rw [hMdef, Submodule.mem_map]
    induction hz' using Algebra.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      exact ⟨b, hb, hw.symm⟩
    | algebraMap r =>
      exact ⟨algebraMap O A r, SetLike.algebraMap_mem_graded 𝒜 r, by simp⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      exact ⟨c₁ + c₂, add_mem hc₁ hc₂, by simp [← e₁, ← e₂]⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      have hm : c₁ * c₂ ∈ 𝒜 (0 + 0) := SetLike.mul_mem_graded hc₁ hc₂
      rw [add_zero] at hm
      exact ⟨c₁ * c₂, hm, by simp [← e₁, ← e₂]⟩
  haveI : IsNoetherian O (Subalgebra.toSubmodule (Algebra.adjoin O {ξ b})) := isNoetherian_of_le hle
  have hint : IsIntegral O (ξ b) :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin O {ξ b}) inferInstance (ξ b)
      (Algebra.subset_adjoin (Set.mem_singleton _))
  exact int_holds O K v hv (ξ b) hint hne
end
