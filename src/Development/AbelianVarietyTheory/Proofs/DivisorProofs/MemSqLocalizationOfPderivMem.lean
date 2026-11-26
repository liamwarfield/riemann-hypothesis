module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem kerCotangentToTensor_injective_of_formallySmooth (k R F : Type*) [CommRing k] [CommRing R]
    [CommRing F] [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F]
    [Algebra.FormallySmooth k F] (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm
    ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) _ hsurj ⟨2, hnil⟩⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

theorem mem_sq_localization_of_pderiv_mem :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  intro Λ _ _ _ σ _ Q _ hQ x hx hd
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  let R := Localization.AtPrime Q
  let F := ResidueField R
  let k := FractionRing Λ
  have hunit : ∀ a : nonZeroDivisors Λ, IsUnit (algebraMap Λ R a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply Λ (MvPolynomial σ Λ) R]
    exact IsLocalization.map_units R (M := Q.primeCompl)
      ⟨MvPolynomial.C a.1, fun h => nonZeroDivisors.coe_ne_zero a (hQ _ h)⟩
  letI : Algebra k R := (IsLocalization.lift (M := nonZeroDivisors Λ) (S := k) hunit).toAlgebra
  haveI : IsScalarTower Λ k R := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq (M := nonZeroDivisors Λ) (S := k) hunit a).symm)
  letI : Algebra k F := ((algebraMap R F).comp (algebraMap k R)).toAlgebra
  haveI : IsScalarTower k R F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ k F := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply Λ R F, IsScalarTower.algebraMap_apply Λ k R]; rfl)
  haveI : Algebra.EssFiniteType (MvPolynomial σ Λ) R := .of_isLocalization R Q.primeCompl
  haveI : Algebra.EssFiniteType Λ R := .comp Λ (MvPolynomial σ Λ) R
  haveI : Algebra.EssFiniteType R F := .of_surjective (Algebra.ofId R F) residue_surjective
  haveI : Algebra.EssFiniteType Λ F := .comp Λ R F
  haveI : Algebra.EssFiniteType k F := Algebra.EssFiniteType.of_comp Λ k F
  haveI : Algebra.FormallySmooth k F := Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.FormallySmooth Λ k := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors Λ)
  haveI : Algebra.FormallySmooth Λ F := Algebra.FormallySmooth.comp Λ k F
  have hinj := kerCotangentToTensor_injective_of_formallySmooth Λ R F (residue_surjective)
  have hker : RingHom.ker (algebraMap R F) = maximalIdeal R := ker_residue
  have hmem : ∀ p ∈ Q, algebraMap (MvPolynomial σ Λ) R p ∈ RingHom.ker (algebraMap R F) := by
    intro p hp
    rw [hker]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q p).mpr hp
  have hym := hmem x hx
  have hD : KaehlerDifferential.D Λ (MvPolynomial σ Λ) x =
      ∑ s, MvPolynomial.pderiv s x • KaehlerDifferential.D Λ (MvPolynomial σ Λ) (MvPolynomial.X s) := by
    conv_lhs => rw [← (KaehlerDifferential.mvPolynomialBasis Λ σ).sum_repr (KaehlerDifferential.D Λ _ x)]
    simp [KaehlerDifferential.mvPolynomialBasis_repr_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  have h0 : KaehlerDifferential.kerCotangentToTensor Λ R F
      ((RingHom.ker (algebraMap R F)).toCotangent ⟨_, hym⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← KaehlerDifferential.map_D Λ Λ (MvPolynomial σ Λ) R, hD, map_sum, tmul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [LinearMap.map_smul_of_tower, ← algebraMap_smul R, ← smul_tmul, Algebra.smul_def, mul_one,
      RingHom.mem_ker.mp (hmem _ (hd s)), zero_tmul]
  have h2 : algebraMap (MvPolynomial σ Λ) R x ∈ RingHom.ker (algebraMap R F) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h2
  obtain ⟨m, hm, hmx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := R) _ _).mp h2
  exact ⟨m, hm, hmx⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMemStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  first | exact @GlobalTheory.mem_sq_localization_of_pderiv_mem | exact GlobalTheory.mem_sq_localization_of_pderiv_mem | (intros; apply GlobalTheory.mem_sq_localization_of_pderiv_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCornerUnitOfRightInverse
open scoped Matrix

namespace GlobalTheory


open Polynomial in
theorem exists_corner_unit_of_right_inverse :
    ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e →
      (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
        ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
      ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 →
        ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) := by
  intro F R _ _ _ e he hψ n D C P Q hDPCQ

  have hev : ∀ (s : R) (M : Matrix (Fin n) (Fin n) R[X]),
      M.det.eval s = (M.map (Polynomial.eval s)).det := by
    intro s M
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    rfl
  have hcoeff : ((1 + (X : R[X]) • D.map Polynomial.C).det).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, hev]
    have : (1 + (X : R[X]) • D.map Polynomial.C).map (Polynomial.eval 0) = 1 := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [this, Matrix.det_one]
  set ψ : R[X] := (-P).charpoly * (1 + (X : R[X]) • D.map Polynomial.C).det with hψdef
  have hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0 := by
    intro Ω _ φ _
    rw [hψdef, Polynomial.map_mul]
    refine mul_ne_zero ?_ ?_
    · rw [← Matrix.charpoly_map]
      exact (Matrix.charpoly_monic _).ne_zero
    · intro h
      have h0 := congrArg (fun f : Polynomial Ω => f.coeff 0) h
      simp only [Polynomial.coeff_map, hcoeff, map_one, Polynomial.coeff_zero] at h0
      exact one_ne_zero h0
  obtain ⟨t, ht⟩ := hψ ψ hne
  obtain ⟨s, hs⟩ : ∃ s : R, s = algebraMap F R t := ⟨_, rfl⟩
  rw [← hs] at ht
  obtain ⟨P', hP2⟩ : ∃ P' : Matrix (Fin n) (Fin n) R, P' = s • (1 : Matrix (Fin n) (Fin n) R) + P :=
    ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : R, p = P'.det := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : R, q = (1 + s • D).det := ⟨_, rfl⟩
  have hψs : ψ.eval s = p * q := by
    rw [hψdef, Polynomial.eval_mul, Matrix.eval_charpoly, hev, hpdef, hqdef, hP2]
    congr 2
    · ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring
  rw [hψs] at ht
  obtain ⟨w, hw⟩ := ht.exists_right_inv

  have hp : p * (e * q * w) = e := by
    linear_combination (w - p * q * w) * he + e * hw
  have hq : q * (e * p * w) = e := by
    linear_combination (w - p * q * w) * he + e * hw
  have hpow : ∀ k : ℕ, e ^ k * e = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, he, ih]
  refine ⟨(e * q * w) • (Q * P'.adjugate), ?_⟩
  set M : Matrix (Fin n) (Fin n) R := D + C * ((e * q * w) • (Q * P'.adjugate)) with hM
  have hxP : ((e * q * w) • (Q * P'.adjugate)) * P' = e • Q := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, ← hpdef, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, mul_comm (e * q * w) p, hp]
  have hMP : e • (M * P') = e • (1 + s • D) := by
    rw [hM, Matrix.add_mul, Matrix.mul_assoc, hxP, Matrix.mul_smul, smul_add, smul_smul, he, hP2,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_add, add_assoc, hDPCQ, add_comm]
  have hdet := congrArg Matrix.det hMP
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, ← hpdef, ← hqdef] at hdet
  have hab : M.det * (e ^ n * p * (e * p * w)) = e := by
    calc M.det * (e ^ n * p * (e * p * w)) = (e ^ n * (M.det * p)) * (e * p * w) := by ring
      _ = (e ^ n * q) * (e * p * w) := by rw [hdet]
      _ = e ^ n * e := by rw [mul_assoc, hq]
      _ = e := hpow n
  refine isUnit_iff_exists_inv.mpr ⟨e * (e ^ n * p * (e * p * w)) + (1 - e), ?_⟩
  linear_combination (M.det * (e ^ n * p * (e * p * w)) - M.det - (e ^ n * p * (e * p * w)) + 2) * he + e * hab

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
open NumberField

namespace GlobalTheory

theorem units_ringOfIntegers_mod_sq (L : Type) [Field L] [NumberField L] :
    ∃ R : Finset (𝓞 L)ˣ, ∀ x : (𝓞 L)ˣ, ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, x = ρ * w ^ 2 := by
  classical
  let N : Submodule ℤ (Additive (𝓞 L)ˣ) := LinearMap.range ((2 : ℤ) • LinearMap.id)
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := inferInstance
  haveI : Finite (Additive (𝓞 L)ˣ ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun q => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      show (2 : ℤ) • (Submodule.Quotient.mk (p := N) x) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
  haveI : Fintype (Additive (𝓞 L)ˣ ⧸ N) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective N)
  refine ⟨Finset.univ.image (fun q => Additive.toMul (rep q)), fun x => ?_⟩
  let q : Additive (𝓞 L)ˣ ⧸ N := Submodule.Quotient.mk (Additive.ofMul x)
  refine ⟨Additive.toMul (rep q), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hq : Submodule.Quotient.mk (p := N) (rep q) = q := Function.surjInv_eq _ q
  have hmem : Additive.ofMul x - rep q ∈ N := by
    rw [← Submodule.Quotient.eq]; exact hq.symm
  obtain ⟨y, hy⟩ := hmem
  refine ⟨Additive.toMul y, ?_⟩
  have h2 : Additive.toMul ((2 : ℤ) • y) = Additive.toMul (Additive.ofMul x - rep q) := by
    simpa using congrArg Additive.toMul hy
  rw [toMul_zsmul, toMul_sub, toMul_ofMul] at h2
  rw [eq_div_iff_mul_eq'] at h2
  rw [← h2]; exact mul_comm _ _

theorem units_fixed_eq_mul_mul_conj : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  intro L _ _ c _hc
  classical
  obtain ⟨R, hR⟩ := units_ringOfIntegers_mod_sq L
  let φ : 𝓞 L →* L := (algebraMap (𝓞 L) L : 𝓞 L →* L)
  have hA : ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) →
      ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, (ε : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by
    intro ε h1 h2
    let u : (𝓞 L)ˣ := ⟨⟨ε, h1⟩, ⟨((ε⁻¹ : Lˣ) : L), h2⟩,
      by apply RingOfIntegers.ext; exact ε.mul_inv, by apply RingOfIntegers.ext; exact ε.inv_mul⟩
    obtain ⟨ρ, hρ, w, hw⟩ := hR u
    refine ⟨ρ, hρ, w, ?_⟩
    calc (ε : L) = φ (u : 𝓞 L) := rfl
      _ = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by rw [hw, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  let P : (𝓞 L)ˣ → Prop := fun ρ => ∃ e : Lˣ, IsIntegral ℤ (e : L) ∧ IsIntegral ℤ ((e⁻¹ : Lˣ) : L) ∧
    c e = e ∧ ∃ w : (𝓞 L)ˣ, (e : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2
  let pick : (𝓞 L)ˣ → Finset L := fun ρ =>
    if h : P ρ then {((Classical.choose h : Lˣ) : L), -((Classical.choose h : Lˣ) : L)} else ∅
  refine ⟨R.biUnion pick, ?_⟩
  intro ε h1 h2 hfix
  obtain ⟨ρ, hρ, w, hw⟩ := hA ε h1 h2
  have hP : P ρ := ⟨ε, h1, h2, hfix, w, hw⟩
  obtain ⟨_g1, _g2, gfix, w', hw'⟩ := Classical.choose_spec hP
  have hpick : pick ρ = {((Classical.choose hP : Lˣ) : L), -((Classical.choose hP : Lˣ) : L)} := by
    simp only [pick, dif_pos hP]
  set e : Lˣ := Classical.choose hP with he
  let W : Lˣ := Units.map φ (w * w'⁻¹)
  have hint : ∀ v : (𝓞 L)ˣ, IsIntegral ℤ (φ (v : 𝓞 L)) := fun v => RingOfIntegers.isIntegral_coe _
  have hWint : IsIntegral ℤ (W : L) := hint _
  have hWint' : IsIntegral ℤ ((W⁻¹ : Lˣ) : L) := by
    have : W⁻¹ = Units.map φ (w * w'⁻¹)⁻¹ := (map_inv _ _).symm
    rw [this]; exact hint _
  have hw'0 : φ (w' : 𝓞 L) ≠ 0 := (Units.map φ w').ne_zero
  have hWval : (W : L) = φ (w : 𝓞 L) * (φ (w' : 𝓞 L))⁻¹ := by
    have : W = Units.map φ w * (Units.map φ w')⁻¹ := by simp only [W, map_mul, map_inv]
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have key : (ε : L) = (e : L) * (W : L) ^ 2 := by
    rw [hWval, hw', hw]; field_simp
  have he0 : (e : L) ≠ 0 := e.ne_zero
  have hsq : (c (W : L)) ^ 2 = (W : L) ^ 2 := by
    have h3 : c (ε : L) = c (e : L) * (c (W : L)) ^ 2 := by rw [key, map_mul, map_pow]
    rw [hfix, gfix, key] at h3
    exact (mul_left_cancel₀ he0 h3).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · refine ⟨(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring
  · refine ⟨-(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChart
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.ResidueDegreeChart

theorem inertiaDeg_eq_finrank_of_ker {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra K L] (φ : R →+* K) (ψ : S →+* L) (q : Ideal S)
    (hq : ∀ s, s ∈ q ↔ ψ s = 0)
    (hφ : ∀ z : K, ∃ a b, z = φ a / φ b) (hψ : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hc : ∀ r, algebraMap K L (φ r) = ψ (algebraMap R S r)) :
    q.inertiaDeg R = Module.finrank K L := by
  have hq' : q = RingHom.ker ψ := by ext s; simp [hq, RingHom.mem_ker]
  subst hq'
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
    ext r
    simp only [RingHom.mem_ker, Ideal.under, Ideal.mem_comap, ← hc]
    simp⟩
  let _ : Algebra R K := φ.toAlgebra
  let _ : Algebra S L := ψ.toAlgebra
  let _ : Algebra R L := (ψ.comp (algebraMap R S)).toAlgebra
  let _ : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  let _ : Algebra (S ⧸ RingHom.ker ψ) L := (RingHom.kerLift ψ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  have : FaithfulSMul (S ⧸ RingHom.ker ψ) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  have : IsFractionRing (R ⧸ RingHom.ker φ) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsFractionRing (S ⧸ RingHom.ker ψ) L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hψ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsScalarTower R (R ⧸ RingHom.ker φ) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⧸ RingHom.ker ψ) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Ideal.inertiaDeg_eq_of_isFractionRing (RingHom.ker φ) (RingHom.ker ψ) K L

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s, ← IsLocalRing.residue_eq_zero_iff]
  rfl

theorem exists_eq_div_evaluation {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (z : X.residueField x) :
    ∃ a b, z = (X.evaluation U x hx).hom a / (X.evaluation U x hx).hom b := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk x) t
  refine ⟨a, b, ?_⟩
  have hb : (X.evaluation U x hx).hom b ≠ 0 := fun h0 =>
    b.2 ((mem_primeIdealOf_iff hU x hx b).2 h0)
  rw [eq_div_iff hb]
  have := congrArg (X.residue x).hom h
  rw [map_mul] at this
  exact this

theorem residueDegree_eq_inertiaDeg : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  intro X Y g V hV hU w hw
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra (X.residueField (g w)) (Y.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  symm
  exact inertiaDeg_eq_finrank_of_ker (X.evaluation V (g w) hw).hom
    (Y.evaluation (g ⁻¹ᵁ V) w hw).hom _ (mem_primeIdealOf_iff hU w hw)
    (exists_eq_div_evaluation hV (g w) hw) (exists_eq_div_evaluation hU w hw)
    (fun r => Scheme.evaluation_naturality_apply g w hw r)

end GlobalTheory.ResidueDegreeChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  first | exact @GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | exact GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | (intros; apply GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowNumericalEnd
namespace GlobalTheory

theorem lamLow_numerical_end : ∀ (f n r : ℕ) (L' dmax mass Lq lam : ℝ) (H dt dk dD : Fin f → ℝ), 8 ≤ n → 2 * r ≤ n → 1 ≤ r → 1 ≤ f → (5.5 : ℝ) ≤ L' → Real.log n ≤ L' → 0 ≤ dmax → Real.log (dmax + 2) ≤ 2 * L' → 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass → 0 < Lq → |Real.log Lq| ≤ f * r / 4 → (∀ ρ, 0 < H ρ ∧ 1 ≤ dt ρ ∧ 1 ≤ dk ρ ∧ 0 < dD ρ ∧ Real.log (dD ρ) ≤ 2 + (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2))) → lam = mass * Lq * ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) → ∑ ρ, Real.log (H ρ) - 2 * f * (n : ℝ) ^ 2 * L' ≤ Real.log lam := by
  intro f n r L' dmax mass Lq lam H dt dk dD hn hr hr1 hf hL' hlogn hdmax hlogd hmass hLq hlogLq hρ hlam
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2 : 2 * (r : ℝ) ≤ n := by exact_mod_cast hr
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hmpos : 0 < mass := lt_of_lt_of_le (by positivity) hmass
  have hlogmass : -((n : ℝ) * Real.log 2 + (n : ℝ) * Real.log n) ≤ Real.log mass := by
    have h1 := Real.log_le_log (by positivity) hmass
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have hfac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.factorial_le_pow n
    linarith
  have hX : Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 * L' := by
    have hd : (0 : ℝ) < dmax + 2 := by linarith
    have h3 : 3 * (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hle : 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 3 * (dmax + 2) := by
      calc 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 2 * n * (dmax + 2) := by gcongr
        _ = (n : ℝ) ^ 3 * (dmax + 2) := by ring
    have hpos : 0 < 3 * (r : ℝ) ^ 2 * n * (dmax + 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hrpos 2)) hnpos) hd
    have h4 := Real.log_le_log hpos hle
    rw [Real.log_mul (pow_pos hnpos 3).ne' hd.ne', Real.log_pow] at h4
    push_cast at h4
    linarith
  have hsq : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by nlinarith
  have hdD : (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 / 4 * (n : ℝ) ^ 2 * L' := by
    calc (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ (r : ℝ) ^ 2 * (5 * L') :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 4 * (5 * L') := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = 5 / 4 * (n : ℝ) ^ 2 * L' := by ring
  have hfac_pos : ∀ ρ, 0 < H ρ * dt ρ * dk ρ / dD ρ := fun ρ => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    exact div_pos (mul_pos (mul_pos h1 ht) hk) h4
  have hprodpos : 0 < ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) := Finset.prod_pos (fun ρ _ => hfac_pos ρ)
  have e1 : Real.log lam = Real.log mass + Real.log Lq + ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    rw [hlam, Real.log_mul (mul_pos hmpos hLq).ne' hprodpos.ne', Real.log_mul hmpos.ne' hLq.ne',
      Real.log_prod (fun ρ _ => (hfac_pos ρ).ne')]
  have e2 : ∀ ρ, Real.log (H ρ) - (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤ Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    rw [Real.log_div (mul_pos (mul_pos h1 ht) hk).ne' h4.ne', Real.log_mul (mul_pos h1 ht).ne' hk.ne',
      Real.log_mul h1.ne' ht.ne']
    have := Real.log_nonneg h2
    have := Real.log_nonneg h3
    linarith
  have hsum : ∑ ρ, Real.log (H ρ) - (f : ℝ) * (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤
      ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    have := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => e2 ρ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hLqlow : -((f : ℝ) * r / 4) ≤ Real.log Lq := by
    have := neg_abs_le (Real.log Lq)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfL : 1 ≤ (f : ℝ) * L' := by nlinarith
  have hP1 : (n : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hfL hnpos.le]
  have hnL : 0 ≤ (n : ℝ) * L' := by positivity
  have hP2 : (n : ℝ) * L' ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_right hf1 hnL]
  have hP3 : (f : ℝ) * r / 4 ≤ f * n * L' := by
    have hrn : (r : ℝ) / 4 ≤ n * L' := by nlinarith
    linarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0 : ℝ) ≤ f)]
  have hnL2 : (2 : ℝ) ≤ n * L' := by nlinarith [mul_le_mul hn8 hL' (by norm_num) hnpos.le]
  have hP4 : 2 * (f : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hnL2 (by linarith : (0 : ℝ) ≤ f)]
  have hbig : 8 * ((f : ℝ) * n * L') ≤ f * (n : ℝ) ^ 2 * L' := by
    have h0 : 0 ≤ (f : ℝ) * n * L' := by positivity
    linarith [mul_le_mul_of_nonneg_right hn8 h0]
  have hm1 := mul_le_mul_of_nonneg_left hlog2 hnpos.le
  have hm2 := mul_le_mul_of_nonneg_left hlogn hnpos.le
  rw [e1]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplit
open Matrix Polynomial

namespace GlobalTheory

theorem reducedArtinian_exists_idem {R : Type} [CommRing R] [IsReduced R] [IsArtinianRing R]
    (a : R) : ∃ e b : R, e * e = e ∧ e = a * b ∧ a * e = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : R)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination ih + (-(a ^ k * y ^ k)) * hy
  have hm : a ^ (n + 1) = a ^ (n + 1 + (n + 1)) * y ^ (n + 1) := by
    linear_combination a * key (n + 1)
  refine ⟨a ^ (n + 1) * y ^ (n + 1), a ^ n * y ^ (n + 1), ?_, by ring, ?_⟩
  · linear_combination (-(y ^ (n + 1))) * hm
  · have h0 : (1 - a ^ (n + 1) * y ^ (n + 1)) * a ^ (n + 1) = 0 := by linear_combination hm
    have hnil : IsNilpotent ((1 - a ^ (n + 1) * y ^ (n + 1)) * a) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow, pow_succ (1 - a ^ (n + 1) * y ^ (n + 1)) n, mul_assoc, h0, mul_zero]
    have := hnil.eq_zero
    linear_combination -this

theorem reducedArtinian_involution_split :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by
  intro R _ _ _ σ hσ
  let S : Set (Ideal R) := {I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}
  have hS : S.Nonempty := ⟨_, 0, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  have hσe : σ e * σ e = σ e := by rw [← map_mul, he]
  set f := 1 - e - σ e with hfdef
  have hf : f * f = f := by linear_combination he + hσe + 2 * heσ
  have hσf : σ f = f := by simp only [hfdef, map_sub, map_one, hσ]; ring
  have hef : e * f = 0 := by linear_combination -he - heσ
  have hσef : σ e * f = 0 := by linear_combination -hσe - heσ
  refine ⟨e, f, he, hf, heσ, by ring, ?_⟩
  intro w hw
  by_contra hwf
  set w' := w * f with hw'def
  have hw'σ : w' * σ w' = 0 := by
    rw [hw'def, map_mul, hσf]; linear_combination (f * f) * hw
  obtain ⟨ε, a, hε, hεa, hw'ε⟩ := reducedArtinian_exists_idem w'
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hw'ε; exact hwf hw'ε.symm
  have hεσ : ε * σ ε = 0 := by
    rw [hεa, map_mul]; linear_combination (a * σ a) * hw'σ
  have hw'f : w' * f = w' := by rw [hw'def, mul_assoc, hf]
  have hεf : ε * f = ε := by rw [hεa]; linear_combination a * hw'f
  have hσεf : σ ε * f = σ ε := by
    have := congrArg σ hεf; rw [map_mul, hσf] at this; exact this
  have hσε : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have heε : e * ε = 0 := by linear_combination (-e) * hεf + ε * hef
  have heσε : e * σ ε = 0 := by linear_combination (-e) * hσεf + σ ε * hef
  have hσeε : σ e * ε = 0 := by linear_combination (-σ e) * hεf + ε * hσef
  have hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S :=
    ⟨e + ε, by linear_combination he + hε + 2 * heε,
      by rw [map_add (f := _)]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩
  apply hmin _ hmem
  have hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε) := by
    rw [map_add (f := _)]; linear_combination hf - hεf - hσεf
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨_, hff.symm⟩
  · intro hEq
    have : f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)} := by
      rw [hEq]; exact Ideal.mem_span_singleton_self f
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    apply hεne
    have hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0 := by
      rw [map_add (f := _)]; linear_combination -heε - hσeε - hε - hεσ
    linear_combination -hεf - ε * hc + c * hεg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplitStatement
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_artinian_involution_idempotent_split : ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧ ∀ w, w * σ w = 0 → w * f = 0 := by
  first | exact @GlobalTheory.reducedArtinian_involution_split | exact GlobalTheory.reducedArtinian_involution_split | (intros; apply GlobalTheory.reducedArtinian_involution_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumConjClassesRegroupWithInvariantSelection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumConjClassesRegroupWithInvariantSelection
namespace GlobalTheory

theorem hasSum_conjClasses_tsum_of_finite_support {G : Type} [Group G] (g : G → ℂ) (hg : (Function.support g).Finite)
    (R : G → Prop) (hR : ∀ δ, g δ ≠ 0 → R δ) :
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      (∑' δ, g δ) := by
  classical
  let c : G → Set G := fun δ => {δ' | IsConj δ δ'}
  have hsum : HasSum g (∑' δ, g δ) := (summable_of_hasFiniteSupport hg).hasSum
  have h1 := hsum.tsum_fiberwise c
  have hfib : ∀ γ : G, c ⁻¹' {c γ} = c γ := by
    intro γ; ext b
    simp only [c, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have : b ∈ {δ' | IsConj b δ'} := IsConj.refl b
      rw [h] at this; exact this
    · intro h; ext x; simp only [Set.mem_setOf_eq]
      exact ⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩
  have hsupp : Function.support (fun s : Set G => ∑' b : c ⁻¹' {s}, g b)
      ⊆ {s | ∃ γ, R γ ∧ s = {δ | IsConj γ δ}} := by
    intro s hs
    by_contra hns
    apply hs
    have : ∀ b : c ⁻¹' {s}, g b = 0 := by
      intro ⟨b, hb⟩
      by_contra hgb
      exact hns ⟨b, hR b hgb, (hb : c b = s).symm⟩
    simp [this]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at h1
  have key : (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      = fun i => (fun s : Set G => ∑' b : c ⁻¹' {s}, g b) i.1 := by
    funext i
    obtain ⟨s, γ, _, hs⟩ := i
    subst hs
    dsimp only
    rw [show c ⁻¹' {{δ | IsConj γ δ}} = {δ | IsConj γ δ} from hfib γ]
  rw [key]; exact h1

theorem classSum_regroup : ∀ {G : Type} [Group G] (g : G → ℂ), (Function.support g).Finite →
    ∀ (R P : G → Prop), (∀ δ, g δ ≠ 0 → R δ) → (∀ a b, IsConj a b → P a → P b) →
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) (∑' δ, g δ) ∧
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} =>
      {i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} | ∀ δ ∈ i.1, P δ}.indicator
        (fun i => ∑' δ : i.1, g δ) i) (∑' δ : {δ // P δ}, g δ) := by
  classical
  intro G _ g hg R P hR hP
  refine ⟨hasSum_conjClasses_tsum_of_finite_support g hg R hR, ?_⟩
  let g' : G → ℂ := fun δ => if P δ then g δ else 0
  have hg' : (Function.support g').Finite := by
    refine hg.subset ?_
    intro δ h
    by_cases hp : P δ <;> simp_all [g']
  have hR' : ∀ δ, g' δ ≠ 0 → R δ := by
    intro δ h; apply hR; by_cases hp : P δ <;> simp_all [g']
  have H := hasSum_conjClasses_tsum_of_finite_support g' hg' R hR'
  have htot : ∑' δ, g' δ = ∑' δ : {δ // P δ}, g δ := by
    rw [show (∑' δ : {δ // P δ}, g δ) = ∑' δ : ({δ | P δ} : Set G), g δ from rfl, tsum_subtype]
    congr 1
  rw [htot] at H
  convert H using 1
  funext i
  obtain ⟨s, γ, hγ, rfl⟩ := i
  rw [Set.indicator_apply]
  split_ifs with hall
  · congr 1; funext δ
    obtain ⟨δ, hδ⟩ := δ
    simp [g', hall δ hδ]
  · have hall' : ¬ ∀ δ ∈ ({δ | IsConj γ δ} : Set G), P δ := hall
    push_neg at hall'
    obtain ⟨δ0, hδ0, hnP⟩ := hall'
    symm
    have : ∀ δ : ({δ | IsConj γ δ} : Set G), g' δ = 0 := by
      intro ⟨δ, hδ⟩
      have hnδ : ¬ P δ := fun h => hnP (hP δ δ0 ((hδ : IsConj γ δ).symm.trans hδ0) h)
      simp [g', hnδ]
    simp [this]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumConjClassesRegroupWithInvariantSelectionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection : ∀ {G : Type} [Group G] (g : G → ℂ), (Function.support g).Finite → ∀ (R P : G → Prop), (∀ δ, g δ ≠ 0 → R δ) → (∀ a b, IsConj a b → P a → P b) → HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) (∑' δ, g δ) ∧ HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => {i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} | ∀ δ ∈ i.1, P δ}.indicator (fun i => ∑' δ : i.1, g δ) i) (∑' δ : {δ // P δ}, g δ) := by
  first | exact @GlobalTheory.classSum_regroup | exact GlobalTheory.classSum_regroup | (intros; apply GlobalTheory.classSum_regroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormSqLeNormProjApplySqOfSpanningParts
open scoped InnerProductSpace

namespace GlobalTheory

theorem mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
    {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (T : X →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ) (hP : (⨆ k, P k) = ⊤)
    (hl : ∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) (u : Y) :
    m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  haveI : Nontrivial Y := ⟨⟨u, 0, hu⟩⟩
  set S : Y →ₗ[ℂ] Y := T ∘ₗ LinearMap.adjoint T with hS
  have hsym : S.IsSymmetric := by
    intro a b
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, LinearMap.adjoint_inner_left]
  have hq : ∀ y : Y, RCLike.re ⟪S y, y⟫_ℂ = ‖LinearMap.adjoint T y‖ ^ 2 := by
    intro y
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, inner_self_eq_norm_sq]
  have hev : ∀ μ : ℝ, Module.End.HasEigenvalue S (μ : ℂ) → m ≤ μ := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    by_contra hlt
    have hlt : μ < m := not_le.mp hlt
    have hSv : S v = (μ : ℂ) • v := hv.apply_eq_smul
    have hle : ∀ k, P k ≤ (ℂ ∙ v)ᗮ := by
      intro k y hy
      obtain ⟨l, hml, hly⟩ := hl k
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 := hsym v y
      have h2 : S y = (l : ℂ) • y := hly y hy
      rw [hSv, h2, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h3 : ((μ : ℂ) - (l : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        have : μ = l := by exact_mod_cast h
        linarith
      have h4 : ((μ : ℂ) - (l : ℂ)) * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left h3
    have hv' : v ∈ (ℂ ∙ v)ᗮ := by
      have : (⊤ : Submodule ℂ Y) ≤ (ℂ ∙ v)ᗮ := hP ▸ iSup_le hle
      exact this Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hv'
    exact hv.2 hv'
  have h1 := hev _ hsym.hasEigenvalue_iInf_of_finiteDimensional
  have hb : BddBelow (Set.range fun x : { x : Y // x ≠ 0 } =>
      RCLike.re ⟪S x, x⟫_ℂ / ‖(x : Y)‖ ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [hq]
    positivity
  have h2 := h1.trans (ciInf_le hb ⟨u, hu⟩)
  simp only [hq] at h2
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  rwa [le_div_iff₀ hpos] at h2

theorem mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by
  intro X Y ι _ _ _ _ _ _ T e P m hm he hee hP hl x hx
  rw [LinearMap.orthogonal_ker] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply] at hw
  set u := e w with hu
  have h1 := mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts T P m hP hl u
  rw [hw] at h1
  have h2 : ⟪x, x⟫_ℂ = ⟪u, e (T x)⟫_ℂ := by
    have : ⟪u, e (T x)⟫_ℂ = ⟪e u, T x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left e, he]
    rw [this, hu, hee, ← hu, ← LinearMap.adjoint_inner_left T, hw]
  have h3 : ‖x‖ ^ 2 ≤ ‖u‖ * ‖e (T x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u (e (T x))
    rw [← h2, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  by_cases hx0 : x = 0
  · simp [hx0]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have h4 : (‖x‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
  have h5 : (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by
    calc (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ m * (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
      _ = ‖e (T x)‖ ^ 2 * (m * ‖u‖ ^ 2) := by ring
      _ ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact le_of_mul_le_mul_right h5 hpos

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectors
open Matrix Polynomial

namespace GlobalTheory


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem quadratic_preimage_compact_on_subspace
    (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K]
    (hstar : ∀ x : K, ‖star x‖ = ‖x‖) (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K))
    (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K) (hq : Continuous q)
    (hhom : ∀ (c : K) w, q (c • w) = (c * star c) • q w) (hnull : ∀ w ∈ S, q w = 0 → w = 0)
    (Q : Set (Matrix (Fin m) (Fin m) K)) (hQ : IsCompact Q) :
    ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by
  haveI : ProperSpace (Matrix (Fin m) (Fin m) K) := FiniteDimensional.proper K _
  obtain ⟨c₀, hc₀⟩ := NormedField.exists_one_lt_norm K
  have hc₀pos : 0 < ‖c₀‖ := lt_trans one_pos hc₀
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall 0
  set Sh : Set (Matrix (Fin m) (Fin m) K) :=
    (S : Set _) ∩ {w | 1 / ‖c₀‖ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hShdef
  have hSclosed : IsClosed (S : Set (Matrix (Fin m) (Fin m) K)) :=
    Submodule.closed_of_finiteDimensional S
  have hShc : IsCompact Sh := by
    refine (isCompact_closedBall (0 : Matrix (Fin m) (Fin m) K) 1).of_isClosed_subset ?_ ?_
    · refine hSclosed.inter ?_
      exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw
      simpa [Metric.mem_closedBall, dist_zero_right] using hw.2.2

  have hresc : ∀ w ∈ S, w ≠ 0 → ∃ d : K, d ≠ 0 ∧ d • w ∈ Sh ∧ ‖d • w‖ < 1 := by
    intro w hwS hw0
    obtain ⟨d, hd0, hlt, hge, -⟩ := rescale_to_shell hc₀ one_pos hw0
    exact ⟨d, hd0, ⟨S.smul_mem d hwS, hge, hlt.le⟩, hlt⟩
  by_cases hne : Sh.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hShc.exists_isMinOn hne
      (f := fun w => ‖q w‖) (continuous_norm.comp hq).continuousOn
    set μ := ‖q w₀‖ with hμ
    have hμpos : 0 < μ := by
      rw [hμ, norm_pos_iff]
      intro h0
      have := hnull w₀ hw₀.1 h0
      have h1 := hw₀.2.1
      rw [this, norm_zero] at h1
      exact absurd h1 (not_le.mpr (by positivity))
    refine ⟨Metric.closedBall 0 (max 1 (R / μ)), isCompact_closedBall _ _, ?_⟩
    intro w hwS hwQ
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hw0 : w = 0
    · rw [hw0, norm_zero]; exact le_trans zero_le_one (le_max_left _ _)
    obtain ⟨d, hd0, hdSh, hdlt⟩ := hresc w hwS hw0
    have hqw : ‖q w‖ ≤ R := by
      have := hR hwQ
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hmu_le : μ ≤ ‖d‖ ^ 2 * ‖q w‖ := by
      have h := isMinOn_iff.mp hmin _ hdSh
      rw [hhom, norm_smul, norm_mul, hstar] at h
      nlinarith [h]
    have hdw : ‖d‖ * ‖w‖ < 1 := by rwa [norm_smul] at hdlt
    have hd2 : ‖d‖ ^ 2 * ‖w‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖d‖ * ‖w‖ := by positivity
      nlinarith
    have key : μ * ‖w‖ ^ 2 ≤ R := by
      have hq0 : 0 ≤ ‖q w‖ := norm_nonneg _
      calc μ * ‖w‖ ^ 2 ≤ ‖d‖ ^ 2 * ‖q w‖ * ‖w‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hmu_le (by positivity)
        _ = (‖d‖ ^ 2 * ‖w‖ ^ 2) * ‖q w‖ := by ring
        _ ≤ 1 * ‖q w‖ := mul_le_mul_of_nonneg_right hd2 hq0
        _ ≤ R := by linarith
    by_cases h1 : ‖w‖ ≤ 1
    · exact le_trans h1 (le_max_left _ _)
    · push_neg at h1
      refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hμpos]
      have h2 : ‖w‖ * μ ≤ ‖w‖ ^ 2 * μ := by
        apply mul_le_mul_of_nonneg_right _ hμpos.le
        nlinarith
      linarith
  · refine ⟨{0}, isCompact_singleton, ?_⟩
    intro w hwS _
    by_contra hw0
    obtain ⟨d, -, hdSh, -⟩ := hresc w hwS hw0
    exact hne ⟨_, hdSh⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectorsStatement
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K)) (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K), Continuous q → (∀ (c : K) w, q (c • w) = (c * star c) • q w) → (∀ w ∈ S, q w = 0 → w = 0) → ∀ Q : Set (Matrix (Fin m) (Fin m) K), IsCompact Q → ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by
  first | exact @GlobalTheory.quadratic_preimage_compact_on_subspace | exact GlobalTheory.quadratic_preimage_compact_on_subspace | (intros; apply GlobalTheory.quadratic_preimage_compact_on_subspace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMemOfMemSpan
namespace GlobalTheory.NonzeroScalarInSpan

theorem exists_ne_zero_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (N : Submodule R V) {x : V}
    (hx : x ∈ Submodule.span K (↑N : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hq : (q : R) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨a * q, mul_ne_zero ha hq, ?_⟩
    have h1 : (q : R) • c • y = p • y := by
      rw [← algebraMap_smul K (q : R), smul_smul, mul_comm]
      simp only at hpq
      rw [hpq, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact N.smul_mem p hay

end GlobalTheory.NonzeroScalarInSpan
end
