module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.UnitAdj

theorem isIntegral_or_isIntegral_inv {O K L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] [FiniteDimensional K L] (y : L) :
    IsIntegral O y ∨ IsIntegral O y⁻¹ := by
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O K L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := O) K L
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left; rw [← hz]; exact z.2
  · right; rw [← hz]; exact z.2

theorem isIntegral_of_mul_self_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {e : A}
    (he : e * e = e) : IsIntegral O e := by
  refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [eval₂_sub, pow_two, he]

section Residues

variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem eq_zero_of_forall_mem {y : A} (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  rw [map_zero]
  funext I
  rw [IsArtinianRing.equivPi_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

theorem isIntegral_of_residues {O : Type} [CommRing O] [Algebra O A] {y : A}
    (h : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal y)) :
    IsIntegral O y := by
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  refine (isIntegral_algHom_iff ψ.toAlgHom ψ.injective).1 ?_
  refine GlobalTheory.UnitLemma.PrincipalLat.isIntegral_pi' _ fun I => ?_
  have : ψ.toAlgHom y I = Ideal.Quotient.mk I.asIdeal y := IsArtinianRing.equivPi_apply A y I
  rw [this]
  exact h I

theorem exists_residues_indicator (P : MaximalSpectrum A → Prop) :
    ∃ e : A, ∀ I : MaximalSpectrum A, (P I → e - 1 ∈ I.asIdeal) ∧ (¬ P I → e ∈ I.asIdeal) := by
  classical
  let v : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal := fun I => if P I then 1 else 0
  refine ⟨(IsArtinianRing.equivPi A).symm v, fun I => ⟨fun hP => ?_, fun hP => ?_⟩⟩
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq, h1, map_one]
    simp [v, hP]
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, h1]
    simp [v, hP]

end Residues

theorem exists_unitary_mul_integral : ∀ {O K A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ hτσ x hc hci
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A

  have hinj := IsFractionRing.injective O K
  choose s hs using hσ
  let σO : O →+* O :=
    { toFun := s
      map_one' := hinj (by simp [← hs])
      map_mul' := fun a b => hinj (by simp [← hs])
      map_zero' := hinj (by simp [← hs])
      map_add' := fun a b => hinj (by simp [← hs]) }
  have hτO : ∀ a : O, τ (algebraMap O A a) = algebraMap O A (σO a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O K A, hτσ]
    change _ = algebraMap O A (s a)
    rw [hs, ← IsScalarTower.algebraMap_apply]

  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum A → MaximalSpectrum A,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum A, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]

  obtain ⟨e, he⟩ := exists_residues_indicator (fun I : MaximalSpectrum A => WellOrderingRel I (tI I))
  have he1 : ∀ I, WellOrderingRel I (tI I) → e - 1 ∈ I.asIdeal := fun I => (he I).1
  have he0 : ∀ I, ¬ WellOrderingRel I (tI I) → e ∈ I.asIdeal := fun I => (he I).2
  have hτe1 : ∀ I, WellOrderingRel (tI I) I → τ e - 1 ∈ I.asIdeal := by
    intro I h
    have := he1 (tI I) (by rw [htt]; exact h)
    rw [hmem, map_sub, map_one] at this
    exact this
  have hτe0 : ∀ I, ¬ WellOrderingRel (tI I) I → τ e ∈ I.asIdeal := by
    intro I h
    exact (hmem I e).1 (he0 (tI I) (by rw [htt]; exact h))
  have hee : e * e = e := by
    refine sub_eq_zero.1 (eq_zero_of_forall_mem fun I => ?_)
    by_cases hP : WellOrderingRel I (tI I)
    · have := I.asIdeal.mul_mem_left e (he1 I hP)
      rwa [mul_sub, mul_one] at this
    · exact I.asIdeal.sub_mem (I.asIdeal.mul_mem_left e (he0 I hP)) (he0 I hP)
  have hgg : τ e * τ e = τ e := by rw [← map_mul, hee]
  have heg : e * τ e = 0 := by
    refine eq_zero_of_forall_mem fun I => ?_
    by_cases hP : WellOrderingRel I (tI I)
    · exact I.asIdeal.mul_mem_left _ (hτe0 I (asymm_of WellOrderingRel hP))
    · exact I.asIdeal.mul_mem_right _ (he0 I hP)

  set f : A := 1 - e - τ e with hf
  have hfix : ∀ I, tI I = I → f - 1 ∈ I.asIdeal := by
    intro I hI
    have h0 : ¬ WellOrderingRel I (tI I) := by rw [hI]; exact irrefl_of WellOrderingRel I
    have h0' : ¬ WellOrderingRel (tI I) I := by rw [hI]; exact irrefl_of WellOrderingRel I
    have : f - 1 = -(e + τ e) := by rw [hf]; ring
    rw [this]
    exact I.asIdeal.neg_mem (I.asIdeal.add_mem (he0 I h0) (hτe0 I h0'))
  have hmov : ∀ I, tI I ≠ I → f ∈ I.asIdeal := by
    intro I hI
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · have : f = -(e - 1) - τ e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (he1 I h)) (hτe0 I (asymm_of WellOrderingRel h))
    · exact absurd h.symm hI
    · have : f = -(τ e - 1) - e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (hτe1 I h)) (he0 I (asymm_of WellOrderingRel h))

  set a : A := (x : A) with ha
  set b : A := ((x⁻¹ : Aˣ) : A) with hb
  have hab : a * b = 1 := x.mul_inv
  have hpq : τ a * τ b = 1 := by rw [← map_mul, hab, map_one]

  have hstable : ∀ I : MaximalSpectrum A, tI I = I →
      IsIntegral O (Ideal.Quotient.mk I.asIdeal a) ∧ IsIntegral O (Ideal.Quotient.mk I.asIdeal b) := by
    intro I hI
    have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
      rw [Ideal.mem_comap, ← hmem, hI]; exact hy
    let ρ := Ideal.quotientMap I.asIdeal τ hle
    have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
      fun y => Ideal.quotientMap_mk
    have hcomp : (algebraMap O (A ⧸ I.asIdeal)).comp σO = ρ.comp (algebraMap O (A ⧸ I.asIdeal)) := by
      ext r
      change Ideal.Quotient.mk _ (algebraMap O A (σO r)) = ρ (Ideal.Quotient.mk _ (algebraMap O A r))
      rw [hρ, hτO]
    have hρi : ∀ z, IsIntegral O z → IsIntegral O (ρ z) := fun z hz =>
      IsIntegral.map_of_comp_eq σO ρ hcomp hz
    have hmk : ∀ y : A, IsIntegral O y → IsIntegral O (Ideal.Quotient.mk I.asIdeal y) :=
      fun y hy => hy.map (Ideal.Quotient.mkₐ O I.asIdeal)
    have hxa : a = (τ a * a) * τ b := by linear_combination -a * hpq
    have hxb : b = (τ b * b) * τ a := by linear_combination -b * hpq
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hX : Ideal.Quotient.mk I.asIdeal a * Ideal.Quotient.mk I.asIdeal b = 1 := by
      rw [← map_mul, hab, map_one]
    have hinv : (Ideal.Quotient.mk I.asIdeal a)⁻¹ = Ideal.Quotient.mk I.asIdeal b :=
      inv_eq_of_mul_eq_one_right hX
    rcases isIntegral_or_isIntegral_inv (O := O) (K := K) (Ideal.Quotient.mk I.asIdeal a) with h | h
    · refine ⟨h, ?_⟩
      rw [hxb, map_mul, ← hρ]
      exact (hmk _ hci).mul (hρi _ h)
    · rw [hinv] at h
      refine ⟨?_, h⟩
      rw [hxa, map_mul, ← hρ]
      exact (hmk _ hc).mul (hρi _ h)
  have haf : IsIntegral O (a * f) ∧ IsIntegral O (b * f) := by
    constructor <;>
    · refine isIntegral_of_residues fun I => ?_
      by_cases hI : tI I = I
      · have h1 : Ideal.Quotient.mk I.asIdeal f = 1 := by
          rw [← map_one (Ideal.Quotient.mk I.asIdeal)]
          exact Ideal.Quotient.eq.2 (hfix I hI)
        rw [map_mul, h1, mul_one]
        first | exact (hstable I hI).1 | exact (hstable I hI).2
      · rw [Ideal.Quotient.eq_zero_iff_mem.2 (I.asIdeal.mul_mem_left _ (hmov I hI))]
        exact isIntegral_zero

  set T : A := a * e + τ b * τ e + f with hT
  set S : A := b * e + τ a * τ e + f with hS
  have hTS : T * S = 1 := by
    rw [hT, hS, hf]
    linear_combination e ^ 2 * hab + τ e ^ 2 * hpq + (2 - a - b) * hee + (2 - τ a - τ b) * hgg +
      (a * τ a + b * τ b - a - b - τ a - τ b + 2) * heg
  have hτT : τ T = S := by
    rw [hT, hS, hf]
    simp only [map_add (f := _), map_sub, map_mul, map_one, hτ]
    ring
  have ie : IsIntegral O e := isIntegral_of_mul_self_eq hee
  have ig : IsIntegral O (τ e) := isIntegral_of_mul_self_eq hgg
  refine ⟨Units.mkOfMulEqOne T S hTS, ?_, ?_, ?_⟩
  · change τ T * T = 1
    rw [hτT, mul_comm, hTS]
  · change IsIntegral O (T * b)
    have : T * b = e + (τ b * b) * τ e + b * f := by
      rw [hT]; linear_combination e * hab
    rw [this]
    exact (ie.add (hci.mul ig)).add haf.2
  · change IsIntegral O (S * a)
    have : S * a = e + (τ a * a) * τ e + a * f := by
      rw [hS]; linear_combination e * hab
    rw [this]
    exact (ie.add (hc.mul ig)).add haf.1

end GlobalTheory.UnitAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit : ∀ {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  first | exact @GlobalTheory.UnitAdj.exists_unitary_mul_integral | exact GlobalTheory.UnitAdj.exists_unitary_mul_integral | (intros; apply GlobalTheory.UnitAdj.exists_unitary_mul_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixOfMapsToFullRankLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixOfMapsToFullRankLattice
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem isIntegral_of_mapsTo_lattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  intro O K _ _ _ n M hM c hc
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1
  let f : Module.End O M :=
    { toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩
      map_add' := fun x y => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun a x => by
        ext1
        simp only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]
        rw [Matrix.mulVec_smul] }
  have hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]
      have h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K) := rfl
      rw [← h1, ih]
  have key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp [Matrix.add_mulVec, hp, hq]
    | monomial k a =>
      intro v
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.aeval_def]
  set A := aeval c p
  have hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    intro v hv
    have := key p ⟨v, hv⟩
    rw [hpf] at this
    simpa using this
  rw [hM.2, top_le_iff, LinearMap.ker_eq_top] at hker
  have : Matrix.toLin' A = 0 := by rw [Matrix.toLin'_apply']; exact hker
  simpa using this

end GlobalTheory.LatOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixOfMapsToFullRankLatticeStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  first | exact @GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | exact GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | (intros; apply GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEq
open Polynomial Matrix GlobalTheory.LatOrb

noncomputable section

namespace GlobalTheory.LatOrb

variable {K : Type} [Field K] {n : ℕ}

theorem exists_mul_eq_one_mem {B : Type} [Ring B] [Algebra K B] (S : Subalgebra K B)
    [FiniteDimensional K S] {a : B} (ha : a ∈ S) (hc : ∀ b : B, a * b = 0 → b = 0) :
    ∃ b ∈ S, a * b = 1 := by
  let f : S →ₗ[K] S := LinearMap.mulLeft K (⟨a, ha⟩ : S)
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    exact hc x.1 (by simpa [f] using congrArg Subtype.val hx)
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact ⟨b.1, b.2, by simpa [f] using congrArg Subtype.val hb⟩

theorem conjTranspose_mem_adjoin (σ : K →+* K) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : (γ.map σ)ᵀ * γ = 1) {a : Matrix (Fin n) (Fin n) K} (ha : a ∈ Algebra.adjoin K {γ}) :
    (a.map σ)ᵀ ∈ Algebra.adjoin K {γ} := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨b, hbm, hb⟩ := exists_mul_eq_one_mem (Algebra.adjoin K {x}) (Algebra.subset_adjoin rfl)
      (fun b hb => by rw [← Matrix.one_mul b, ← hγ, Matrix.mul_assoc, hb, Matrix.mul_zero])
    have : (x.map σ)ᵀ = b := by
      calc (x.map σ)ᵀ = (x.map σ)ᵀ * (x * b) := by rw [hb, Matrix.mul_one]
        _ = b := by rw [← Matrix.mul_assoc, hγ, Matrix.one_mul]
    rw [this]; exact hbm
  | algebraMap r =>
    have : ((algebraMap K (Matrix (Fin n) (Fin n) K) r).map σ)ᵀ =
        algebraMap K (Matrix (Fin n) (Fin n) K) (σ r) := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, Matrix.transpose_mul]; exact mul_mem hy hx

theorem aeval_map_mulVec_mem {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (γ : Matrix (Fin n) (Fin n) K) (hM : ∀ v ∈ M, γ *ᵥ v ∈ M) (r : O[X]) :
    ∀ v ∈ M, aeval γ (r.map (algebraMap O K)) *ᵥ v ∈ M := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [Polynomial.map_add (f := _), map_add (f := _), Matrix.add_mulVec]
    exact add_mem (hp v hv) (hq v hv)
  | monomial k a =>
    intro v hv
    have hk : ∀ k : ℕ, γ ^ k *ᵥ v ∈ M := by
      intro k
      induction k with
      | zero => simpa using hv
      | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hM _ ih
    rw [Polynomial.map_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, algebraMap_smul]
    exact M.smul_mem a (hk k)

theorem matLat_le {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (u : Matrix (Fin n) (Fin n) K) (hu : ∀ v ∈ M, u *ᵥ v ∈ M) : matLat O u M ≤ M := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (mem_matLat u M v).mp hv
  exact hu w hw

theorem matLat_mono {O : Type} [CommRing O] [Algebra O K] {M N : Submodule O (Fin n → K)}
    (u : Matrix (Fin n) (Fin n) K) (h : M ≤ N) : matLat O u M ≤ matLat O u N :=
  Submodule.map_mono h

end GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem exists_unitary_matLat_eq : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧
      matLat O t M = matLat O (aeval γ p) M := by
  intro O K _ _ _ _ _ _ _ n P₀ hcop γ hchar σ hσ hσO hγ M hML hMγ p hpu hpM
  set A := Algebra.adjoin K {γ} with hAdef
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin_singleton K γ
  open scoped IsMulCommutative in
  letI : CommRing A := inferInstance
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    intro u hu v hv
    exact congrArg (fun z : A => z.1) (mul_comm (⟨u, hu⟩ : A) ⟨v, hv⟩)
  have hstar : ∀ a ∈ A, (a.map σ)ᵀ ∈ A := fun a ha => conjTranspose_mem_adjoin σ γ hγ ha
  let τ : A →+* A :=
    { toFun := fun a => ⟨(a.1.map σ)ᵀ, hstar a.1 a.2⟩
      map_one' := by
        apply Subtype.ext
        show (((1 : Matrix (Fin n) (Fin n) K)).map σ)ᵀ = 1
        rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a.1 * b.1).map σ)ᵀ = (a.1.map σ)ᵀ * (b.1.map σ)ᵀ
        rw [Matrix.map_mul, Matrix.transpose_mul]
        exact hcomm _ (hstar b.1 b.2) _ (hstar a.1 a.2)
      map_zero' := by
        apply Subtype.ext
        show (((0 : Matrix (Fin n) (Fin n) K)).map σ)ᵀ = 0
        rw [Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero]
      map_add' := fun a b => by
        apply Subtype.ext
        show ((a.1 + b.1).map σ)ᵀ = (a.1.map σ)ᵀ + (b.1.map σ)ᵀ
        rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add] }
  have hτv : ∀ a : A, (τ a).1 = (a.1.map σ)ᵀ := fun a => rfl
  have hττ : ∀ a, τ (τ a) = a := by
    intro a; apply Subtype.ext
    rw [hτv, hτv, Matrix.transpose_map, Matrix.map_map, Matrix.transpose_transpose]
    ext i j; simp [hσ]
  have hτk : ∀ k, τ (algebraMap K A k) = algebraMap K A (σ k) := by
    intro k; apply Subtype.ext
    rw [hτv]
    show ((algebraMap K (Matrix (Fin n) (Fin n) K) k).map σ)ᵀ = algebraMap K (Matrix (Fin n) (Fin n) K) (σ k)
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

  have hred : IsReduced A := by
    constructor
    rintro a ⟨k, hk⟩
    obtain ⟨q, hq⟩ : ∃ q, aeval γ q = a.1 := by
      exact (Algebra.adjoin_singleton_eq_range_aeval K γ).le a.2
    have h1 : aeval γ (q ^ k) = 0 := by
      rw [map_pow, hq]; exact congrArg Subtype.val hk
    have hsep : (minpoly K γ).Separable :=
      ((show P₀.Separable from hcop).map (f := algebraMap O K)).of_dvd
        (hchar ▸ Matrix.minpoly_dvd_charpoly γ)
    have h2 : minpoly K γ ∣ q := hsep.squarefree.isRadical k q (minpoly.dvd K γ h1)
    apply Subtype.ext
    rw [← hq]
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K γ)

  have hxA : aeval γ p ∈ A := Polynomial.aeval_mem_adjoin_singleton K γ
  obtain ⟨b, hbA, hb⟩ := exists_mul_eq_one_mem A hxA (fun b hb => by
    obtain ⟨u, hu⟩ := hpu
    rw [← hu] at hb
    rw [← Matrix.one_mul b, ← u.inv_mul, Matrix.mul_assoc, hb, Matrix.mul_zero])
  let x : Aˣ := Units.mkOfMulEqOne (⟨aeval γ p, hxA⟩ : A) ⟨b, hbA⟩ (Subtype.ext hb)
  have hxv : ((x : A) : Matrix (Fin n) (Fin n) K) = aeval γ p := rfl
  let ι : A →ₐ[O] Matrix (Fin n) (Fin n) K := (A.val).restrictScalars O
  have hι : ∀ a : A, IsIntegral O a ↔ IsIntegral O a.1 := fun a =>
    (isIntegral_algHom_iff ι Subtype.val_injective).symm

  have hcM : ∀ v ∈ M, (τ x * x : A).1 *ᵥ v ∈ M := by
    intro v hv
    have : (τ x * x : A).1 *ᵥ v ∈ matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M :=
      (mem_matLat _ _ _).mpr ⟨v, hv, rfl⟩
    rwa [hpM] at this
  have hcinv : (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) * (τ x * x) = 1 := by
    calc
      _ = (τ ((x⁻¹ : Aˣ) : A) * τ (x : A)) * (((x⁻¹ : Aˣ) : A) * (x : A)) := by ac_rfl
      _ = 1 := by rw [← map_mul]; simp
  have hc'M : ∀ v ∈ M, (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A) : A).1 *ᵥ v ∈ M := by
    intro v hv
    rw [← hpM] at hv
    obtain ⟨u, hu, rfl⟩ := (mem_matLat _ _ _).mp hv
    have e : ((τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A) : A).1 *ᵥ ((((aeval γ p).map σ)ᵀ * aeval γ p) *ᵥ u)) = u := by
      rw [Matrix.mulVec_mulVec]
      have := congrArg Subtype.val hcinv
      exact (congrArg (· *ᵥ u) this).trans (Matrix.one_mulVec u)
    rw [e]; exact hu
  have hi1 : IsIntegral O (τ (x : A) * x) := (hι _).mpr (GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice n M hML _ hcM)
  have hi2 : IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) :=
    (hι _).mpr (GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice n M hML _ hc'M)
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit σ hσO τ hττ hτk x hi1 hi2

  have hkeep : ∀ a : A, IsIntegral O a → ∀ v ∈ M, a.1 *ᵥ v ∈ M := by
    intro a ha
    obtain ⟨q, hq⟩ : ∃ q, aeval γ q = a.1 := by
      exact (Algebra.adjoin_singleton_eq_range_aeval K γ).le a.2
    have ha' : IsIntegral O (aeval γ q) := hq ▸ (hι a).mp ha
    obtain ⟨r, hr⟩ := GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly n P₀ hcop γ hchar q ha'
    rw [← hq, hr]
    exact aeval_map_mulVec_mem M γ hMγ r
  have hk1 := hkeep _ ht2
  have hk2 := hkeep _ ht3
  refine ⟨(t : A).1, congrArg Subtype.val ht1, hcomm _ (t : A).2 _ (Algebra.subset_adjoin rfl), ?_⟩
  apply le_antisymm
  · have e : (t : A).1 = (aeval γ p) * ((t : A) * ((x⁻¹ : Aˣ) : A)).1 := by
      rw [← hxv]
      show (t : A).1 = ((x : A) * ((t : A) * ((x⁻¹ : Aˣ) : A))).1
      rw [mul_comm (t : A), ← mul_assoc, Units.mul_inv, one_mul]
    rw [e, matLat_mul]
    exact matLat_mono _ (matLat_le M _ hk1)
  · have e : aeval γ p = (t : A).1 * (((t⁻¹ : Aˣ) : A) * (x : A)).1 := by
      rw [← hxv]
      show ((x : A)).1 = ((t : A) * (((t⁻¹ : Aˣ) : A) * (x : A))).1
      rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [e, matLat_mul]
    exact matLat_mono _ (matLat_le M _ hk2)

end GlobalTheory.LatOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEqStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧ matLat O t M = matLat O (aeval γ p) M := by
  first | exact @GlobalTheory.LatOrb.exists_unitary_matLat_eq | exact GlobalTheory.LatOrb.exists_unitary_matLat_eq | (intros; apply GlobalTheory.LatOrb.exists_unitary_matLat_eq <;> assumption)
end
