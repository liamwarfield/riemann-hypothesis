module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Field

variable {K : Type} [Field K]

def Dm (Δ : K) : Subring (Matrix (Fin 2) (Fin 2) (Lsq K Δ)) where
  carrier := {m | m 1 1 = star (m 0 0) ∧ m 1 0 = - star (m 0 1)}
  mul_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4] <;> ring
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    constructor <;> simp [h1, h2, h3, h4, add_comm]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    obtain ⟨h1, h2⟩ := ha
    constructor <;> simp [h1, h2]

variable {Δ : K}

theorem mem_Dm {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} : m ∈ Dm Δ ↔ m 1 1 = star (m 0 0) ∧ m 1 0 = - star (m 0 1) := Iff.rfl

theorem mem_DX {g : GL (Fin 2) (Lsq K Δ)} : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) ∈ Dm Δ := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹ ↔ _
    rw [inv_inv, Units.ext_iff]
    rfl
  rw [e, mem_Dm, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  simp
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1.symm, by rw [h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem mt_mem (g : DX Δ) : mt g ∈ Dm Δ := mem_DX.1 g.2

theorem det_Dm {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : m ∈ Dm Δ) :
    m.det = algebraMap K _ ((m 0 0).re ^ 2 - Δ * (m 0 0).im ^ 2 + (m 0 1).re ^ 2 - Δ * (m 0 1).im ^ 2) := by
  rw [Matrix.det_fin_two, h.1, h.2]
  ext <;> simp [sq] <;> ring

variable {O : Type} [CommRing O] [Algebra O K]

theorem mem_KD {g : DX Δ} : g ∈ KD Δ O ↔ (∀ i j, IsIntegral O (mt g i j)) ∧ ∀ i j, IsIntegral O (mt g⁻¹ i j) := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : GeneralLinearGroup.map ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) u⁻¹ = (g⁻¹ : DX Δ) := by
      rw [map_inv, hu]; rfl
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have : mt g i j = (u i j : Lsq K Δ) := by
        change (g : GL (Fin 2) (Lsq K Δ)) i j = _
        have hu2 : (g : GL (Fin 2) (Lsq K Δ)) = _ := hu.symm
        rw [hu2]; rfl
      rw [this]; exact (u i j).2
    · have : mt g⁻¹ i j = ((u⁻¹ : GL (Fin 2) _) i j : Lsq K Δ) := by
        change ((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq K Δ)) i j = _
        rw [← hu']; rfl
      rw [this]; exact ((u⁻¹ : GL (Fin 2) _) i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (fun m : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) =>
        ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix m) :=
      Matrix.map_injective Subtype.val_injective
    let a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨_, h2 i j⟩
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · simp only [map_mul, map_one]
      exact (g : GL (Fin 2) (Lsq K Δ)).mul_inv
    · simp only [map_mul, map_one]
      exact (g : GL (Fin 2) (Lsq K Δ)).inv_mul

theorem isIntegral_star {a : Lsq K Δ} (h : IsIntegral O a) : IsIntegral O (star a) := by
  let f : Lsq K Δ →ₐ[O] Lsq K Δ := { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      change star (algebraMap O (Lsq K Δ) r) = _
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
      ext <;> simp }
  exact h.map f

theorem isIntegral_coords {a : Lsq K Δ} (h : IsIntegral O a) {m : K} (hm : IsIntegral O m) (hmΔ : IsIntegral O (m * Δ)) :
    IsIntegral O (2 * m * Δ * a.re) ∧ IsIntegral O (2 * m * Δ * a.im) := by
  have inj : Function.Injective (algebraMap K (Lsq K Δ)) := fun x y h => by simpa using congrArg QuadraticAlgebra.re h
  have h1 : IsIntegral O (2 * a.re) := by
    rw [← isIntegral_algebraMap_iff (B := Lsq K Δ)]
    convert h.add (isIntegral_star h) using 1
    ext <;> simp; ring
  have h2 : IsIntegral O (Δ * (2 * a.im) ^ 2) := by
    rw [← isIntegral_algebraMap_iff (B := Lsq K Δ)]
    convert (h.sub (isIntegral_star h)).pow 2 using 1
    ext <;> simp [sq] <;> ring
  refine ⟨by rw [show 2 * m * Δ * a.re = m * Δ * (2 * a.re) by ring]; exact hmΔ.mul h1, ?_⟩
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [show (2 * m * Δ * a.im) ^ 2 = m * (m * Δ) * (Δ * (2 * a.im) ^ 2) by ring]
  exact (hm.mul hmΔ).mul h2

theorem isIntegral_of_coords {a : Lsq K Δ} {m : K} (hm : IsIntegral O m) (hmΔ : IsIntegral O (m * Δ))
    (h1 : IsIntegral O a.re) (h2 : IsIntegral O a.im) : IsIntegral O (algebraMap K (Lsq K Δ) m * a) := by
  have h3 : IsIntegral O (⟨0, m⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    convert (hm.mul hmΔ).algebraMap (B := Lsq K Δ) using 1
    ext <;> simp [sq]; ring
  convert ((hm.mul h1).algebraMap (B := Lsq K Δ)).add (h3.mul (h2.algebraMap (B := Lsq K Δ))) using 1
  ext <;> simp

end Field

section Global

variable {F : Type} [Field F] [NumberField F]

theorem isIntegral_Ov {v : Pl F} {t : Kv v} : IsIntegral (Ov v) t ↔ t ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨t, h⟩, rfl⟩

theorem isIntegral_glob {t : F} : IsIntegral ℤ t ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v t) := by
  simp only [isIntegral_Ov]
  constructor
  · intro h v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t fun v => by
      have := h v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t]
      exact this
    exact y.2

theorem exists_nat_mul (t : F) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : F) * t) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) t)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

theorem exists_nat_mul_loc (v : Pl F) (t : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * t) := by
  obtain ⟨b, hb, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v t
  have hb0 : (b : F) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  obtain ⟨n, hn, h2⟩ := exists_nat_mul (b : F)⁻¹
  refine ⟨n, hn, ?_⟩
  have h' : IsIntegral (Ov v) (t * cv v (b : F)) := isIntegral_Ov.2 h
  have := (isIntegral_glob.1 h2 v).mul h'
  rwa [map_mul, map_natCast, mul_assoc, mul_left_comm _ t, ← map_mul, inv_mul_cancel₀ hb0, map_one, mul_one] at this

theorem exists_nat_mul_L {Δ : F} (v : Pl F) (a : Lsq (Kv v) (cv v Δ)) :
    ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * a) := by
  obtain ⟨m, hm, h⟩ := exists_nat_mul Δ
  obtain ⟨n1, hn1, h1⟩ := exists_nat_mul_loc v a.re
  obtain ⟨n2, hn2, h2⟩ := exists_nat_mul_loc v a.im
  refine ⟨m * (n1 * n2), by positivity, ?_⟩
  have := isIntegral_of_coords (O := Ov v) (a := ((n1 * n2 : ℕ) : Lsq (Kv v) (cv v Δ)) * a) (m := (m : Kv v))
    (isIntegral_natCast _) (by simpa using isIntegral_glob.1 h v)
    (by simpa [mul_assoc, mul_left_comm] using (isIntegral_natCast n2).mul h1)
    (by simpa [mul_assoc] using (isIntegral_natCast n1).mul h2)
  convert this using 1
  simp [mul_assoc]

theorem den_DA {Δ : F} (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ ∀ v i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * mt (g.1 v) i j) := by
  classical
  have hf : {v : Pl F | ¬ g.1 v ∈ KD (cv v Δ) (Ov v)}.Finite := g.2
  choose n hn h using fun (v : Pl F) (p : Fin 2 × Fin 2) => exists_nat_mul_L v (mt (g.1 v) p.1 p.2)
  refine ⟨∏ v ∈ hf.toFinset, ∏ p, n v p, Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun p _ => hn v p,
    fun v i j => ?_⟩
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact (isIntegral_natCast _).mul ((mem_KD.1 hv).1 i j)
  · obtain ⟨k, hk⟩ := (Finset.dvd_prod_of_mem (n v) (Finset.mem_univ (i, j))).trans
      (Finset.dvd_prod_of_mem (fun v => ∏ p, n v p) (hf.mem_toFinset.2 hv))
    rw [hk, Nat.cast_mul, mul_comm (n v (i, j) : Lsq (Kv v) (cv v Δ)), mul_assoc]
    exact (isIntegral_natCast _).mul (h v (i, j))

end Global

end UpperTheory.V.Z.Sym.Glob
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGTau
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem theta_theta {K : Type} [Field K] (Δ : K) (x : U3 Δ) : theta Δ (theta Δ x) = x := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  exact star_star ((x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)

private theorem mul_theta_conj {K : Type} [Field K] (Δ : K) (δ x : U3 Δ) :
    (x⁻¹ * δ * theta Δ x) * theta Δ (x⁻¹ * δ * theta Δ x) = x⁻¹ * (δ * theta Δ δ) * x := by
  simp only [map_mul, map_inv, theta_theta, mul_assoc, mul_inv_cancel_left]

private theorem charpoly_conj {K : Type} [Field K] (Δ : K) (n x : U3 Δ) :
    ((x⁻¹ * n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).charpoly =
      (n : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).charpoly := by
  have e : ((x⁻¹ * n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
      ((x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) := by
    rw [mul_assoc]; rfl
  rw [e, Matrix.charpoly_mul_comm]
  have e2 : ((n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
      ((n * x * x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) := rfl
  rw [e2, mul_inv_cancel_right]

private theorem lmap_star {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K) (x : Lsq K Δ) :
    lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

open Polynomial in
private theorem poly_expand {R : Type} [CommRing R] (t : R) :
    ((X - 1) * (X ^ 2 - C t * X + 1) : R[X]) = X ^ 3 - C (1 + t) * X ^ 2 + C (1 + t) * X - 1 := by
  simp only [C_add, C_1]; ring

open Polynomial in
theorem UpperTheory.V.Z.Sym.Glob.sideGTau :
    (∀ (K : Type) [Field K] (Δ : K) (δ x : U3 Δ) (τ : K), HasTau δ τ → HasTau (x⁻¹ * δ * theta Δ x) τ) ∧
    (∀ (K : Type) [Field K] (Δ : K) (δ : U3 Δ) (τ τ' : K), HasTau δ τ → HasTau δ τ' → τ = τ') ∧
    (∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (Δ : K) (δ : U3 Δ) (δ' : U3 (f Δ)) (τ : K),
      (δ' : Matrix (Fin 3) (Fin 3) _) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) → HasTau δ τ → HasTau δ' (f τ)) ∧
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (Δ : K) (δ : U3 Δ) (τ : K), δ ∈ KU O Δ → HasTau δ τ → IsIntegral O τ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K _ Δ δ x τ h
    unfold HasTau at h ⊢
    rw [mul_theta_conj, charpoly_conj, h]
  · intro K _ Δ δ τ τ' h h'
    unfold HasTau at h h'
    have e := h.symm.trans h'
    have m : (X - 1 : (Lsq K Δ)[X]).Monic := by
      simpa using Polynomial.monic_X_sub_C (1 : Lsq K Δ)
    have e1 := m.isRegular.left e
    have e2 := congrArg (fun p => p.coeff 1) e1
    simp [coeff_X, coeff_one, coeff_X_pow] at e2
    exact e2
  · intro K K' _ _ f Δ δ δ' τ hd h
    unfold HasTau at h ⊢
    have e : ((δ' * theta (f Δ) δ' : U3 (f Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) =
        ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) := by
      have a : ((theta (f Δ) δ' : U3 (f Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) =
          ((theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) := by
        refine Matrix.ext fun i j => ?_
        change star ((δ' : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) i j) = lmap f Δ (star ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
        rw [hd, lmap_star]; rfl
      change (δ' : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) * ((theta (f Δ) δ' : U3 (f Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) = _
      rw [a, hd]
      exact (Matrix.map_mul (f := lmap f Δ)).symm
    have hl : lmap f Δ (algebraMap K (Lsq K Δ) τ) = algebraMap K' (Lsq K' (f Δ)) (f τ) := by
      ext <;> simp [lmap]
    rw [e, Matrix.charpoly_map, h]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, hl]
  · intro O K _ _ _ Δ δ τ hK h
    unfold HasTau at h
    have hθ : theta Δ δ ∈ KU O Δ := fun i j => by
      refine ⟨(hK i j).2, ?_⟩
      change IsIntegral O (star (star ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)))
      rw [star_star]; exact (hK i j).1
    have hN := (KU O Δ).mul_mem hK hθ
    have ht : IsIntegral O (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))).trace :=
      IsIntegral.sum _ fun i _ => (hN i i).1
    have hc := Matrix.trace_eq_neg_charpoly_coeff ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
    have c2 : ∀ s : Lsq K Δ, (X ^ 3 - C s * X ^ 2 + C s * X - 1 : (Lsq K Δ)[X]).coeff (Fintype.card (Fin 3) - 1) = -s := by
      intro s
      simp [coeff_X, coeff_one, coeff_X_pow, coeff_C_mul]
    rw [h, poly_expand, c2, neg_neg] at hc
    rw [hc] at ht
    have h2 : IsIntegral O (algebraMap K (Lsq K Δ) τ) := by
      simpa using ht.sub isIntegral_one
    exact isIntegral_algebraMap_iff.1 h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.ExGModel
open Matrix QuadraticAlgebra

namespace UpperTheory.V.Z.Sym.Glob

open Loc

variable {K : Type} [Field K] {Δ τ : K}

private theorem sg_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sg_add (x y : EL Δ τ) : sigL (x + y) = sigL x + sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sg_sg (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sg_star (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

private theorem sg_smul (a : Lsq K Δ) (x : EL Δ τ) : sigL (a • x) = star a • sigL x := by
  ext <;> simp [sigL] <;> ring

private theorem sg_tr (x : EL Δ τ) : QuadraticAlgebra.trace (sigL x) = star (QuadraticAlgebra.trace x) := by
  ext <;> simp [sigL, QuadraticAlgebra.trace_def, two_mul] <;> ring

private theorem sg_ofE (z : Etau K τ) : sigL (ofE Δ z) = ofE Δ z := by
  ext <;> simp [sigL, ofE]

private theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private theorem ofE_star (x : Etau K τ) : ofE Δ (star x) = star (ofE Δ x) := by
  ext <;> simp [ofE]

private theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem st_alg (c : K) : star (algebraMap K (Lsq K Δ) c) = algebraMap K _ c := by
  ext <;> simp

private theorem herm_semi {c : K} {d m : EL Δ τ} (h : IsDat c d m) (x y : Sp Δ τ) :
    herm c m (semi d x) (semi d y) = star (herm c m x y) := by
  simp only [herm, semi, star_add, star_mul', star_star, st_alg, ← sg_tr, sg_mul, sg_sg, sg_star, h.m_sig]
  congr 2
  ring

private theorem herm_tor (c : K) (m : EL Δ τ) (z : (Etau K τ)ˣ) (x y : Sp Δ τ) :
    herm c m (tor Δ z x) (tor Δ z y) = herm c m x y := by
  have h1 : quo z * star (quo z) = 1 := by
    have e := z.mul_inv
    have e' := congrArg star e
    rw [star_mul', star_one] at e'
    simp only [quo, star_mul', star_star]
    linear_combination (star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * e + e'
  have h2 : ofE Δ (quo z) * star (ofE Δ (quo z)) = 1 := by rw [← ofE_star, ← ofE_mul, h1, ofE_one]
  simp only [herm, tor, sg_mul, sg_ofE, star_mul']
  congr 2
  linear_combination (m * x.2 * star (sigL y.2)) * h2

private theorem mem_unit (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
    (h : ∀ u v, ∑ i, (M *ᵥ u) i * star ((M *ᵥ v) i) = ∑ i, u i * star (v i)) : M ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) := by
  rw [Matrix.mem_unitaryGroup_iff']
  refine Matrix.ext fun a b => ?_
  have := h (Pi.single b 1) (Pi.single a 1)
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, mul_comm (star _)]
  rw [this, Matrix.one_apply, Finset.sum_eq_single a]
  · by_cases hab : a = b <;> simp [hab]
  · intro i _ hi
    simp [hi]
  · simp

theorem exG_models {c : K} {d m : EL Δ τ} (h : IsDat c d m) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    (hP : ∀ x y, herm c m x y = ∑ i, P x i * star (P y i)) : ∃ δ ι, Models c d m δ ι P := by
  let f : (Fin 3 → Lsq K Δ) →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ) :=
    { toFun := fun w => P (semi d (P.symm (star w)))
      map_add' := fun u v => by
        rw [← map_add (f := _), star_add, map_add (f := _)]
        congr 1
        simp [semi, sg_add, mul_add]
      map_smul' := fun a u => by
        rw [RingHom.id_apply, ← map_smul, star_smul, map_smul]
        congr 1
        simp [semi, sg_smul] }
  let T : (Etau K τ)ˣ → Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ := fun z =>
    { toFun := tor Δ z
      map_add' := fun u v => by simp [tor, mul_add]
      map_smul' := fun a u => by simp [tor] }
  let g : (Etau K τ)ˣ → Matrix (Fin 3) (Fin 3) (Lsq K Δ) := fun z =>
    LinearMap.toMatrix' (P.toLinearMap ∘ₗ T z ∘ₗ P.symm.toLinearMap)
  have hg : ∀ z w, g z *ᵥ w = P (tor Δ z (P.symm w)) := fun z w => LinearMap.toMatrix'_mulVec _ _
  have hf : ∀ w, LinearMap.toMatrix' f *ᵥ w = P (semi d (P.symm (star w))) := fun w => LinearMap.toMatrix'_mulVec _ _
  have hgu : ∀ z, g z ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) := fun z => mem_unit _ fun u v => by
    simp only [hg]
    rw [← hP, herm_tor, hP]
    simp
  have hfu : LinearMap.toMatrix' f ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) := mem_unit _ fun u v => by
    simp only [hf]
    rw [← hP, herm_semi h, hP]
    simp [star_mul']
  refine ⟨⟨_, hfu⟩, MonoidHom.mk' (fun z => ⟨g z, hgu z⟩) fun a b => Subtype.ext ?_, hP, fun x => ?_, fun z x => ?_⟩
  · change g (a * b) = g a * g b
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, hg, hg, hg, P.symm_apply_apply]
    congr 1
    have e : quo (a * b) = quo a * quo b := by
      simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring
    simp [tor, e, ofE_mul, mul_assoc]
  · change _ = LinearMap.toMatrix' f *ᵥ _
    rw [hf, star_star, P.symm_apply_apply]
  · change _ = g z *ᵥ _
    rw [hg, P.symm_apply_apply]

theorem exG_norm [CharZero K] {c : K} {d m : EL Δ τ} (h : IsDat c d m) :
    ∃ y : Lsq K Δ, algebraMap K (Lsq K Δ) (2 + τ) * QuadraticAlgebra.norm m = y * star y := by
  have h1 : star m = sigL m := by
    conv_lhs => rw [← h.m_star, star_star]
  have ho : ofE Δ (ω : Etau K τ) = ω := by ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hd : d * sigL d = ω := h.d_norm.trans ho
  have hd' : star d * star (sigL d) = star ω := by rw [← star_mul', hd]
  have hn : (ω : EL Δ τ) * star ω = 1 := by rw [← algebraMap_norm_eq_mul_star]; simp [QuadraticAlgebra.norm_def]
  have ht : (ω : EL Δ τ) + star ω = algebraMap _ _ (algebraMap K (Lsq K Δ) τ) := by
    rw [← algebraMap_trace_eq_add_star, trace_omega]
  have hs : sigL (1 + star ω : EL Δ τ) = 1 + star ω := by
    ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  set y : EL Δ τ := m * d * (1 + star ω) with hy
  have hys : star y = y := by
    rw [hy, star_mul', star_mul', h1, h.m_sig, star_add, star_one, star_star]
    linear_combination (m * d * (1 + ω)) * hd' + m * d * hn
  have him : y.im = 0 := by
    have e := congrArg QuadraticAlgebra.im hys
    rw [im_star] at e
    have e1 := congrArg QuadraticAlgebra.re e
    have e2 := congrArg QuadraticAlgebra.im e
    simp only [re_neg, im_neg] at e1 e2
    ext
    · exact self_eq_neg.1 e1.symm
    · exact self_eq_neg.1 e2.symm
  have hy1 : y = algebraMap _ _ y.re := by ext1 <;> simp [him]
  have hy2 : sigL y = algebraMap _ _ (star y.re) := by ext1 <;> simp [him, sigL]
  refine ⟨y.re, QuadraticAlgebra.algebraMap_injective (a := -1) (b := algebraMap K (Lsq K Δ) τ) ?_⟩
  rw [map_mul, map_mul, ← hy1, ← hy2, algebraMap_norm_eq_mul_star, hy, sg_mul, sg_mul, hs, ← h1, map_add (f := _), map_add (f := _), ← ht,
    map_ofNat, map_ofNat]
  linear_combination (-(m * star m * (1 + star ω) ^ 2)) * hd - (m * star m * (2 + star ω)) * hn

end UpperTheory.V.Z.Sym.Glob
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGTerm
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Glob.sideGTerm :
    ∀ (Γ G V H : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [Group H] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → B.ω = 1 → B.Γ₀ = ⊥ → ∀ (δ n : Γ) (i : H →* Γ), n ∉ i.range →
    (∀ x, x⁻¹ * δ * s.θΓ x = δ ↔ x ∈ i.range ∨ n * x ∈ i.range) → ∀ (U : Subgroup G) (H₀ : Subgroup H), B.U = U → i.ker = H₀ →
    2 * s.term f δ = LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) * gqOn (B.ι.comp i) H₀ U (fun y => f (y.out⁻¹ * B.ι δ * s.θ y.out)) := by
  classical
  intro Γ G V H _ _ _ _ _ B hB s f hf hω hΓ δ n i hn hc U H₀ hU hH
  subst hU hH
  set C := s.Cent δ with hC
  have memC : ∀ x, x ∈ C ↔ x⁻¹ * δ * s.θΓ x = δ := by
    intro x
    constructor
    · rintro ⟨z, hz, h⟩
      rw [hΓ, Subgroup.mem_bot] at hz
      simpa [hz] using h
    · intro h
      exact ⟨1, one_mem _, by simpa using h⟩
  have hRC : ∀ x, x ∈ C ↔ x ∈ i.range ∨ n * x ∈ i.range := fun x => (memC x).trans (hc x)
  have hiC : ∀ h, i h ∈ C := fun h => (hRC _).2 (Or.inl ⟨h, rfl⟩)
  let φ : H →* C := i.codRestrict C hiC
  have hnC : n ∈ C := by
    have : n⁻¹ ∈ C := (hRC _).2 (Or.inr (by simp [one_mem]))
    simpa using C.inv_mem this
  have hφ : ∀ c : C, c ∈ φ.range ↔ (c : Γ) ∈ i.range := by
    intro c
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, e⟩
      exact ⟨h, Subtype.ext e⟩
  have hidx : (φ.range ⊔ (⊥ : Subgroup C)).index = 2 := by
    rw [sup_bot_eq, Subgroup.index_eq_two_iff']
    refine ⟨⟨n, hnC⟩, fun b => ?_⟩
    rw [hφ, hφ]
    by_cases hb : (b : Γ) ∈ i.range
    · refine Or.inr ⟨hb, fun h => hn ?_⟩
      have := i.range.mul_mem h (i.range.inv_mem hb)
      simpa using this
    · refine Or.inl ⟨?_, hb⟩
      exact ((hRC _).1 b.2).resolve_left hb
  have hfl : ∀ (u : B.U) y, f (u * y) = f y := by
    intro u y
    rw [hf.left, hω]
    simp
  have hfr : ∀ (u : B.U) y, f (y * s.θ u) = f y := by
    intro u y
    rw [hf.right, hω]
    simp
  have kmk : ∀ g : G, s.ker f δ (g : G ⧸ B.U) = f (g⁻¹ * B.ι δ * s.θ g) := by
    intro g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U g
    have e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * (u : G)) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u) := by
      simp [mul_assoc]
    show f (_) = _
    rw [hu, e, hfl, hfr]
  have hk : ∀ (h : C) (y : G ⧸ B.U), s.ker f δ ((B.ι.comp C.subtype) h • y) = s.ker f δ y := by
    intro h y
    induction y using QuotientGroup.induction_on with
    | H g =>
      have e : (B.ι (h : Γ) * g)⁻¹ * B.ι δ * s.θ (B.ι (h : Γ) * g) =
          g⁻¹ * B.ι ((h : Γ)⁻¹ * δ * s.θΓ (h : Γ)) * s.θ g := by
        simp [s.comm, mul_assoc]
      show s.ker f δ ((B.ι (h : Γ) * g : G) : G ⧸ B.U) = _
      rw [kmk, kmk, e, (memC _).1 h.2]
  have hS : ∃ S : Finset (G ⧸ B.U), ∀ y, s.ker f δ y ≠ 0 → ∃ h, ∃ x ∈ S, y = (B.ι.comp C.subtype) h • x := by
    obtain ⟨S, hS⟩ := Tf.centFin Γ G V B hB s f hf δ
    refine ⟨Finset.image (QuotientGroup.mk : G → G ⧸ B.U) S, fun y hy => ?_⟩
    obtain ⟨t, x, hx, u, hu, e⟩ := hS y.out hy
    refine ⟨t, (x : G ⧸ B.U), Finset.mem_image_of_mem _ hx, ?_⟩
    calc y = ((y.out : G) : G ⧸ B.U) := (QuotientGroup.out_eq' y).symm
      _ = (((B.ι.comp C.subtype) t * x : G) : G ⧸ B.U) := by
        rw [e]
        exact QuotientGroup.mk_mul_of_mem _ hu
      _ = _ := rfl
  have hw : ∀ y : G ⧸ B.U, s.ker f δ y ≠ 0 →
      (⊥ : Subgroup C).relIndex ((MulAction.stabilizer G y).comap (B.ι.comp C.subtype)) ≠ 0 := by
    intro y _
    induction y using QuotientGroup.induction_on with
    | H g =>
      have h1 := hB.stab g
      rw [hΓ, Subgroup.relIndex_bot_left] at h1
      haveI := (Nat.card_ne_zero.1 h1).2
      rw [Subgroup.relIndex_bot_left, Nat.card_ne_zero]
      refine ⟨⟨1, one_mem _⟩, ?_⟩
      let m : ((MulAction.stabilizer G (g : G ⧸ B.U)).comap (B.ι.comp C.subtype)) →
          ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := fun c => ⟨(c.1 : Γ), by
        have h2 : (((B.ι (c.1 : Γ) * g : G)) : G ⧸ B.U) = (g : G ⧸ B.U) := c.2
        have h3 := QuotientGroup.eq.1 h2.symm
        exact ⟨_, h3, by simp [mul_assoc]⟩⟩
      refine Finite.of_injective m fun a b e => ?_
      exact Subtype.ext (Subtype.ext (congrArg (fun c => (c.1 : Γ)) e))
  have hz : ∀ z ∈ (⊥ : Subgroup C), ∀ y : G ⧸ B.U, (B.ι.comp C.subtype) z • y = y := by
    intro z hz y
    rw [Subgroup.mem_bot.1 hz]
    simp
  have key := Tf.gqIndex H C G φ (B.ι.comp C.subtype) ⊥ B.U (s.ker f δ) inferInstance hz
    (by rw [hidx]; norm_num) hk hS hw
  have e1 : (B.ι.comp C.subtype).comp φ = B.ι.comp i := by
    ext h
    rfl
  have e2 : (⊥ : Subgroup C).comap φ = i.ker := by
    ext h
    simp [φ, MonoidHom.mem_ker, Subtype.ext_iff]
  rw [e1, e2, hidx] at key
  have e3 : gqOn (B.ι.comp i) i.ker B.U (fun y => f (y.out⁻¹ * B.ι δ * s.θ y.out)) =
      gqOn (B.ι.comp i) i.ker B.U (s.ker f δ) := rfl
  rw [e3, key, Base.Tw.term, hΓ, Subgroup.bot_subgroupOf]
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSUnit
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix

private theorem fin_reps {A X : Type} [Finite X] (φ : A → X) (r : A → A → Prop) (h : ∀ a b, φ a = φ b → r a b) :
    ∃ S : Finset A, ∀ a, ∃ s ∈ S, r s a := by
  classical
  have hf : (Set.range fun x : Set.range φ => x.2.choose).Finite := Set.finite_range _
  refine ⟨hf.toFinset, fun a => ⟨(⟨φ a, a, rfl⟩ : Set.range φ).2.choose, hf.mem_toFinset.2 ⟨_, rfl⟩, h _ _ ?_⟩⟩
  exact (⟨φ a, a, rfl⟩ : Set.range φ).2.choose_spec

theorem su_abs {Γ G X : Type} [Group Γ] [Group G] [Finite X] (ι : Γ →* G) (Γ₁ : Subgroup Γ) (N K U : Subgroup G) [hN : N.Normal]
    (h₁ : ∀ γ ∈ Γ₁, ι γ ∈ N) (hU : U.relIndex K ≠ 0)
    (hcls : ∃ Y : Finset G, ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ K, g = ι γ * y * k) (x : G) (P : Γ → Prop) (c : Γ → X)
    (hP : ∀ γ, ∀ k ∈ K, ∀ y, ι γ * (y * k * y⁻¹) ∈ N → P γ)
    (hc : ∀ γ γ', P γ → P γ' → c γ = c γ' → ∃ z, ι z ∈ K ∧ ι z ∈ Subgroup.center G ∧ γ' * γ⁻¹ * z⁻¹ ∈ Γ₁) :
    ∃ S : Finset N, ∀ g : N, ∃ γ ∈ Γ₁, ∃ s ∈ S, ∃ u : N, x⁻¹ * u * x ∈ U ∧ (g : G) = ι γ * s * u := by
  classical
  obtain ⟨Y, hY⟩ := hcls
  choose γ y hy k hk e using fun g : N => hY (g * x)
  let yy : N → Y := fun g => ⟨y g, hy g⟩
  let b : N → N := fun g => Function.invFun yy (yy g)
  have hb : ∀ g, y (b g) = y g := fun g => congrArg Subtype.val (Function.invFun_eq (f := yy) ⟨g, rfl⟩)
  have rel : ∀ g g' : N, y g = y g' → (g' : G) = ι (γ g' * (γ g)⁻¹) * g * (x * ((k g)⁻¹ * k g') * x⁻¹) := by
    intro g g' h
    have e1 : (g : G) = ι (γ g) * y g * k g * x⁻¹ := by rw [← e g]; group
    have e2 : (g' : G) = ι (γ g') * y g * k g' * x⁻¹ := by rw [h, ← e g']; group
    rw [map_mul, map_inv, e1, e2]; group
  have hPg : ∀ g, P (γ g * (γ (b g))⁻¹) := by
    intro g
    refine hP _ _ (mul_mem (inv_mem (hk (b g))) (hk g)) x ?_
    have h := rel (b g) g (hb g)
    have h2 := mul_mem (inv_mem (hN.conj_mem _ (b g).2 (ι (γ g * (γ (b g))⁻¹)))) g.2
    convert h2 using 1
    conv_rhs => rw [h]
    group
  obtain ⟨S₁, hS₁⟩ := fin_reps (fun g : N => (yy g, c (γ g * (γ (b g))⁻¹)))
    (fun g g' => ∃ δ ∈ Γ₁, ∃ w ∈ K, (g' : G) = ι δ * g * (x * w * x⁻¹)) (by
      intro g g' h
      have h1 : yy g = yy g' := congrArg Prod.fst h
      have hbb : b g = b g' := by simp only [b, h1]
      obtain ⟨z, hz, hzc, hz1⟩ := hc _ _ (hPg g) (hPg g') (congrArg Prod.snd h)
      refine ⟨_, hz1, ι z * ((k g)⁻¹ * k g'), mul_mem hz (mul_mem (inv_mem (hk g)) (hk g')), ?_⟩
      have hcm := Subgroup.mem_center_iff.1 hzc ((g : G) * x)
      have := rel g g' (congrArg Subtype.val h1)
      rw [hbb]
      calc (g' : G) = ι (γ g' * (γ g)⁻¹) * (ι z)⁻¹ * (ι z * (g * x)) * ((k g)⁻¹ * k g') * x⁻¹ := by
            conv_lhs => rw [this]
            group
        _ = _ := by
            rw [← hcm]
            simp only [map_mul, map_inv]
            group)
  choose s hs δ hδ w hw e' using hS₁
  have : Finite (K ⧸ U.subgroupOf K) := by
    have : (U.subgroupOf K).FiniteIndex := ⟨hU⟩
    infer_instance
  obtain ⟨S, hS⟩ := fin_reps (fun g : N => ((⟨s g, hs g⟩ : S₁), ((⟨w g, hw g⟩ : K) : K ⧸ U.subgroupOf K)))
    (fun g g' => ∃ δ ∈ Γ₁, ∃ u : N, x⁻¹ * u * x ∈ U ∧ (g' : G) = ι δ * g * u) (by
      intro g g' h
      have h1 : s g = s g' := congrArg Subtype.val (congrArg Prod.fst h)
      have h2 : (w g)⁻¹ * w g' ∈ U := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (congrArg Prod.snd h :
        ((⟨w g, hw g⟩ : K) : K ⧸ U.subgroupOf K) = (⟨w g', hw g'⟩ : K)))
      have h3 : (g' : G) = ι (δ g' * (δ g)⁻¹) * g * (x * ((w g)⁻¹ * w g') * x⁻¹) := by
        conv_lhs => rw [e' g', ← h1]
        conv_rhs => rw [e' g]
        simp only [map_mul, map_inv]
        group
      have h4 := mul_mem (hδ g') (inv_mem (hδ g))
      refine ⟨_, h4, ⟨x * ((w g)⁻¹ * w g') * x⁻¹, ?_⟩, ?_, h3⟩
      · have h5 := mul_mem (inv_mem (mul_mem (h₁ _ h4) g.2)) g'.2
        convert h5 using 1
        conv_rhs => rw [h3]
        group
      · convert h2 using 1
        group)
  refine ⟨S, fun g => ?_⟩
  obtain ⟨s, hs, δ, hδ, u, hu, e⟩ := hS g
  exact ⟨δ, hδ, s, hs, u, hu, e⟩

section Local

variable {K : Type} [Field K] {Δ : K}

private theorem det_im [CharZero K] (g : DX Δ) : (mt g).det = algebraMap K (Lsq K Δ) (mt g).det.re := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (wJ Δ)⁻¹ * g.1 * (wJ Δ)⁻¹⁻¹ := g.2
  have h2 := congrArg (fun a : GL (Fin 2) (Lsq K Δ) => ((GeneralLinearGroup.det a : (Lsq K Δ)ˣ) : Lsq K Δ)) h
  simp only [map_mul, map_inv, mul_right_comm _ (GeneralLinearGroup.det g.1), mul_inv_cancel, one_mul] at h2
  have h3 : star (mt g).det = (mt g).det := ((starRingEnd (Lsq K Δ)).map_det (mt g)).trans h2
  have h4 := congrArg QuadraticAlgebra.im h3
  simp only [QuadraticAlgebra.im_star] at h4
  ext
  · simp
  · simp only [QuadraticAlgebra.algebraMap_im]
    linear_combination (-1 / 2 : K) * h4

private theorem det_int {O : Type} [CommRing O] [Algebra O K] {g : DX Δ} (h : g ∈ KD Δ O) : IsIntegral O (mt g).det := by
  obtain ⟨a, ha⟩ := h
  have : mt g = (a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).map (integralClosure O (Lsq K Δ)).val := by
    rw [mt, ← show _ = g.1 from ha]; rfl
  rw [this]
  have h2 := ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).map_det
    (a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)))
  exact h2 ▸ (a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).det.2

private theorem mem_SU {g : DX Δ} : g ∈ SU Δ ↔ (mt g).det = 1 := by
  rw [SU, MonoidHom.mem_ker, ← Units.val_inj]; rfl

variable (Δ) in
private def scal (z : Kˣ) : DX Δ :=
  ⟨GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z), by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) _ = (wJ Δ)⁻¹ * _ * (wJ Δ)⁻¹⁻¹
    rw [inv_inv, mul_assoc, eq_inv_mul_iff_mul_eq]
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [wJ, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals (ext <;> simp [starRingEnd_apply])⟩

private theorem mt_scal (z : Kˣ) : mt (scal Δ z) = scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := rfl

private theorem scal_KD {O : Type} [CommRing O] [Algebra O K] (u : Oˣ) (g : DX Δ)
    (hg : mt g = scalar (Fin 2) (algebraMap O (Lsq K Δ) u)) : g ∈ KD Δ O := by
  refine ⟨GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap O (integralClosure O (Lsq K Δ)) : O →* _) u), ?_⟩
  refine Units.ext ?_
  change _ = mt g
  rw [hg]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp

end Local

private theorem loc_glob {F : Type} [Field F] [NumberField F] (t : F) (h : ∀ v : Pl F, IsIntegral (Ov v) (cv v t)) :
    t ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F t fun v => ?_
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h v)
  have := a.2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, show (a : Kv v) = cv v t from ha] at this
  rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t]

section Global

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem lmap_alg (v : Pl F) (t : F) : lmap (cv v) Δ (algebraMap F (Lsq F Δ) t) = algebraMap (Kv v) _ (cv v t) := by
  ext <;> simp [lmap]

private theorem mem_SA {g : DA Δ} : g ∈ SA Δ ↔ ∀ v, (mt (g.1 v)).det = 1 := by
  rw [SA, Subgroup.mem_iInf]
  exact forall_congr' fun v => mem_SU

private theorem mem_box {g : DA Δ} : g ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v)) ↔ ∀ v, g.1 v ∈ KD (cv v Δ) (Ov v) := by
  rw [RPG.box, Subgroup.mem_iInf]; rfl

private theorem det_mul' {K : Type} [Field K] {Δ : K} (a b : DX Δ) : (mt (a * b)).det = (mt a).det * (mt b).det :=
  Matrix.det_mul _ _

private theorem det_inv' {K : Type} [Field K] {Δ : K} (a : DX Δ) : (mt a).det * (mt a⁻¹).det = 1 := by
  rw [← det_mul', mul_inv_cancel]; exact Matrix.det_one

private theorem det_iota {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) (γ : DX Δ) (v : Pl F) :
    (mt ((ι γ).1 v)).det = lmap (cv v) Δ (mt γ).det := by
  rw [hι]; exact ((lmap (cv v) Δ).map_det _).symm

private theorem SA_normal : (SA Δ).Normal := ⟨fun g hg y => mem_SA.2 fun v => by
  change (mt (y.1 v * g.1 v * (y.1 v)⁻¹)).det = 1
  rw [det_mul', det_mul', mem_SA.1 hg v, mul_one, det_inv']⟩

private theorem re_int {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) (γ : DX Δ)
    (h : ∀ v, IsIntegral (Ov v) (mt ((ι γ).1 v)).det) : (mt γ).det.re ∈ (algebraMap (𝓞 F) F).range := by
  refine loc_glob _ fun v => ?_
  have h1 := h v
  rw [det_iota hι, det_im, lmap_alg] at h1
  exact (isIntegral_algebraMap_iff ).1 h1

private theorem unit_det {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) (γ : DX Δ) (k : DA Δ)
    (hk : k ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v))) (y : DA Δ) (h : ι γ * (y * k * y⁻¹) ∈ SA Δ) :
    ∃ ε : (𝓞 F)ˣ, (mt γ).det = algebraMap F (Lsq F Δ) (algebraMap (𝓞 F) F ε) := by
  have h1 : ∀ v, (mt ((ι γ).1 v)).det * (mt (k.1 v)).det = 1 := fun v => by
    have h2 : (mt ((ι γ).1 v * (y.1 v * k.1 v * (y.1 v)⁻¹))).det = 1 := mem_SA.1 h v
    rwa [det_mul', det_mul', det_mul', mul_right_comm, det_inv', one_mul] at h2
  obtain ⟨a, ha⟩ := re_int hι γ fun v => by
    have h2 := det_int (inv_mem (mem_box.1 hk v))
    have h3 := det_inv' (k.1 v)
    have : (mt ((ι γ).1 v)).det = (mt (k.1 v)⁻¹).det := by
      rw [← mul_one (mt ((ι γ).1 v)).det, ← h3, ← mul_assoc, h1, one_mul]
    rwa [this]
  obtain ⟨b, hb⟩ := re_int hι γ⁻¹ fun v => by
    have h2 := det_int (mem_box.1 hk v)
    have h3 := det_inv' ((ι γ).1 v)
    have : (mt ((ι γ⁻¹).1 v)).det = (mt (k.1 v)).det := by
      rw [map_inv]
      change (mt ((ι γ).1 v)⁻¹).det = _
      rw [← one_mul (mt ((ι γ).1 v)⁻¹).det, ← h1, mul_right_comm, h3, one_mul]
    rwa [this]
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 F) F
    apply (algebraMap F (Lsq F Δ)).injective
    rw [map_mul, map_mul, ha, hb, ← det_im, ← det_im, det_inv', map_one, map_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, by rw [det_im, ← ha]⟩

theorem finS_cls_of (D : Dat Δ) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι)
    (hcls : ∃ Y : Finset (DA Δ), ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v)), g = ι γ * y * k)
    (hU : D.U2.relIndex ((rpg _ _).box fun v : Pl F => KD (cv v Δ) (Ov v)) ≠ 0)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {x : DA Δ} {B : Base (SU Δ) (SA Δ) V} (hB : D.IsBS ch x B) :
    ∃ S : Finset (SA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ B.U, g = B.ι γ * s * u := by
  classical
  have : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 F)ˣ (n := 2) two_ne_zero
  have := SA_normal (Δ := Δ)
  let P : DX Δ → Prop := fun γ => ∃ ε : (𝓞 F)ˣ, (mt γ).det = algebraMap F (Lsq F Δ) (algebraMap (𝓞 F) F ε)
  let c : DX Δ → (𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range := fun γ => if h : P γ then (h.choose : (𝓞 F)ˣ) else 1
  obtain ⟨S, hS⟩ := su_abs ι (SU Δ) (SA Δ) _ D.U2 (fun γ hγ => mem_SA.2 fun v => by rw [det_iota hι, mem_SU.1 hγ, map_one]) hU hcls x P c
    (unit_det hι) (by
      intro γ γ' h h' e
      simp only [c, dif_pos h, dif_pos h'] at e
      obtain ⟨η, hη⟩ := QuotientGroup.eq.1 e
      have hη' : h'.choose = h.choose * η ^ 2 := by rw [show η ^ 2 = _ from hη]; group
      let z := scal Δ (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) η)
      have hz : ∀ v, mt ((ι z).1 v) = scalar (Fin 2) (algebraMap (Kv v) (Lsq (Kv v) (cv v Δ)) (cv v (algebraMap (𝓞 F) F η))) := by
        intro v
        rw [hι, mt_scal, ← lmap_alg]
        ext i j : 1
        fin_cases i <;> fin_cases j <;> simp
      refine ⟨z, mem_box.2 fun v => scal_KD (Units.map (algebraMap (𝓞 F) (Ov v) : 𝓞 F →* Ov v) η) _ ?_, ?_, ?_⟩
      · rw [hz]; rfl
      · refine Subgroup.mem_center_iff.2 fun g => Subtype.ext (funext fun v => Subtype.ext (Units.ext ?_))
        change mt (g.1 v) * mt ((ι z).1 v) = mt ((ι z).1 v) * mt (g.1 v)
        rw [hz]
        exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq
      · have hd : (mt z).det = algebraMap F (Lsq F Δ) (algebraMap (𝓞 F) F η) ^ 2 := by
          rw [mt_scal, Matrix.scalar_apply, Matrix.det_diagonal]; simp
        have h3 : (mt γ').det = (mt γ).det * (mt z).det := by
          rw [h'.choose_spec, hη', hd]
          conv_rhs => rw [h.choose_spec]
          simp
        rw [mem_SU, det_mul', det_mul', h3]
        linear_combination ((mt z).det * (mt z⁻¹).det) * det_inv' γ + det_inv' z)
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, u, hu, e⟩ := hS g
  refine ⟨⟨γ, hγ⟩, s, hs, u, (hB.U u).2 hu, Subtype.ext ?_⟩
  have : (B.ι ⟨γ, hγ⟩ : DA Δ) = ι γ :=
    Subtype.ext (funext fun v => Subtype.ext (Units.ext ((hB.ι ⟨γ, hγ⟩ v).trans (hι γ v).symm)))
  rw [e, ← this]; rfl

end Global

end UpperTheory.V.Z.Sym.Glob
end
end
