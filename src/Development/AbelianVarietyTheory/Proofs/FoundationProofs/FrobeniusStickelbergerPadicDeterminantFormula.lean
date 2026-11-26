module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionSetSubgroup
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaZeroPeriodLatticeEq
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.JetsGenusOne

theorem sgStar_eq (L : PeriodPair) : TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L _ (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

end GlobalTheory.JetsGenusOne

namespace GlobalTheory.JetsGenusOne

end GlobalTheory.JetsGenusOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLinesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_fin_three_eq_zero_of_subst_lines : ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines | exact GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines | (intros; apply GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameter
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
namespace GlobalTheory.FrobStick

theorem det_column_alg {R : Type*} [CommRing R] (x e w q : Fin 3 → R) (ε r a₁ a₃ S D1 D2 D3 : R)
    (hq : ∀ i, q i * w i = 1) (hu : IsUnit (2 * ε ^ 4))
    (h : Matrix.det (Matrix.of fun i j => (![ε ^ 3 * x i ^ 3 * e i ^ 3,
      ε * e i ^ 3 * (x i * q i + ε ^ 2 * r * x i ^ 3),
      e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)] : Fin 3 → R) j) =
      2 * (ε * S) * (ε * D1) * (ε * D2) * (ε * D3)) :
    (x 0 ^ 3 * w 0 * (x 2 - x 1) + x 1 ^ 3 * w 1 * (x 0 - x 2) + x 2 ^ 3 * w 2 * (x 1 - x 0))
      * e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 = w 0 * w 1 * w 2 * S * D1 * D2 * D3 := by
  have hrow : ∀ i, e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)
      = e i ^ 3 * (a₁ * x i * q i + a₃ * x i ^ 3 - 2 * q i) := fun i => by
    linear_combination e i ^ 3 * a₃ * x i ^ 3 * hq i
  simp only [hrow] at h
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  have h2 : 2 * ε ^ 4 * (e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 *
      (x 0 ^ 3 * (q 1 * q 2) * (x 2 - x 1) + x 1 ^ 3 * (q 0 * q 2) * (x 0 - x 2)
        + x 2 ^ 3 * (q 0 * q 1) * (x 1 - x 0))) = 2 * ε ^ 4 * (S * D1 * D2 * D3) := by
    linear_combination h
  have h3 := hu.mul_left_cancel h2
  have h12 : q 1 * q 2 * (w 1 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h02 : q 0 * q 2 * (w 0 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h01 : q 0 * q 1 * (w 0 * w 1) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  linear_combination w 0 * w 1 * w 2 * h3
    - e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 * (x 0 ^ 3 * w 0 * (x 2 - x 1) * h12
      + x 1 ^ 3 * w 1 * (x 0 - x 2) * h02 + x 2 ^ 3 * w 2 * (x 1 - x 0) * h01)

theorem det_column_ops : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  intro p _ E wq ε r a₁ a₃ s d₁ d₂ d₃ hε hw hs h1 h2 h3 h
  have hC : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), HasSubst a → ∀ c : ℂ_[p],
      PowerSeries.subst a (PowerSeries.C c : PowerSeries ℂ_[p]) = MvPowerSeries.C c := by
    intro a ha c
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes c
  have hlin : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (PowerSeries.C ε * PowerSeries.X * E) =
        MvPowerSeries.C ε * (a * PowerSeries.subst a E) := by
    intro a ha
    have ha' : HasSubst a := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul ha', subst_mul ha', hC a ha', subst_X ha', mul_assoc]
  have hX : ∀ i : Fin 3, HasSubst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) := fun i =>
    HasSubst.of_constantCoeff_zero (by simp [GL3Theta.Xv])
  rw [hlin s hs, hlin d₁ h1, hlin d₂ h2, hlin d₃ h3] at h
  refine det_column_alg (fun i => (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]))
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) E)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq⁻¹)
    (MvPowerSeries.C ε) (MvPowerSeries.C r) (MvPowerSeries.C a₁) (MvPowerSeries.C a₃) _ _ _ _
    ?_ ?_ ?_
  · intro i
    rw [← subst_mul (hX i), PowerSeries.inv_mul_cancel _ (by rw [hw]; exact one_ne_zero),
      ← coe_substAlgHom (hX i), map_one]
  · have : (2 * MvPowerSeries.C ε ^ 4 : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.C (2 * ε ^ 4) := by
      rw [map_mul, map_pow, map_ofNat]
    rw [this]
    exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (pow_ne_zero _ hε))).map _
  · rw [← h]
    congr 1
    ext1 i j
    have hCi := hC _ (hX i)
    have hXi := subst_X (R := ℂ_[p]) (hX i)
    rw [← coe_substAlgHom (hX i)] at hCi hXi
    simp only [Matrix.of_apply]
    rw [← coe_substAlgHom (hX i)]
    fin_cases j
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, map_mul, map_pow, map_add, map_sub, map_ofNat, hCi, hXi]

end GlobalTheory.FrobStick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameterStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_column_operations_model_parameter : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  first | exact @GlobalTheory.FrobStick.det_column_ops | exact GlobalTheory.FrobStick.det_column_ops | (intros; apply GlobalTheory.FrobStick.det_column_ops <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.FrobStick

open PowerSeries

theorem omegaW_mul_inv {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (hwq : IsWq W wq) :
    omegaW W wq * (wq⁻¹ * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) =
      X * derivative (R := ℂ_[p]) wq⁻¹ - 2 * wq⁻¹ ∧ omegaW W wq ≠ 0 := by
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative (R := ℂ_[p]) wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative (R := ℂ_[p]) wq) * (wq * N)⁻¹ := by
      have hd : dX wq = derivative (R := ℂ_[p]) wq := by
        ext n
        simp [dX, coeff_derivative, mul_comm]
      unfold omegaW
      rw [hd]
      rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative (R := ℂ_[p]) e + e * derivative (R := ℂ_[p]) wq = 0 := by
    have := congrArg (derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  have key : omegaW W wq * (e * N) = X * derivative (R := ℂ_[p]) e - 2 * e := by
    linear_combination e ^ 2 * hω - X * e * hde -
      (omegaW W wq * N * e + 2 * e - X * derivative (R := ℂ_[p]) e) * he
  refine ⟨key, fun h => ?_⟩
  rw [h, zero_mul] at key
  have := congrArg constantCoeff key
  simp [he1, h2] at this

theorem atU_sgStar_eq {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (X * ePhi1 g.lam g.abelian₂ g.C g.wq) := by
  have h0 : constantCoeff (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.taylorCoeff_zero_eq_value,
      (hL.sg_eq_zero 0).2 (zero_mem _)]
    exact (GlobalTheory.SerTransport.lamC_coe g.lam 0).trans (map_zero g.lam)
  obtain ⟨S, hS⟩ := X_dvd_iff.2 h0
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g S hS, GlobalTheory.SerTransport.atU_eq, hS, subst_mul hs, subst_X hs,
    mul_assoc]

theorem colC_atU : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  intro hD p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hQ, eQ⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hσ', dσ⟩ := hD p g _ hσ
  obtain ⟨hQ', dQ⟩ := hD p g _ hQ
  obtain ⟨hT, hc, -⟩ := GlobalTheory.SerTransport.transport p g
  have hm : (-2 : ℂ) ∈ Qbar := neg_mem (ofNat_mem _ 2)
  obtain ⟨c1, c2⟩ := hc _ hm
  have c3 : lamC g.lam (-2) = -2 := by
    have : (-2 : ℂ) = ((-2 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  obtain ⟨a1, a2⟩ := (hT _ _ hσ hQ').1
  obtain ⟨b1, b2⟩ := (hT _ _ c1 hσ').1
  obtain ⟨d1, d2⟩ := (hT _ _ b1 hQ).1
  obtain ⟨f1, f2⟩ := (hT _ _ a1 d1).2
  have e : colC g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (-2 * deriv (sgStar g.abelian₂) z) * sqTh g.abelian₂ v z := by
    funext z
    rw [colC]; ring
  rw [e]
  refine ⟨f1, ?_⟩
  rw [f2, a2, d2, b2, c2, c3, map_neg, map_ofNat]
  obtain ⟨hω, hω0⟩ := omegaW_mul_inv g.W g.wq hq
  have eS := atU_sgStar_eq g hL
  have hε : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [constantCoeff_C, map_zero] at this
    exact Units.ne_zero _ this
  apply mul_left_cancel₀ (mul_ne_zero hε hω0)
  rw [eQ, lineSer] at dQ
  rw [eS] at dσ
  rw [eQ, eS, lineSer]
  generalize ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε at *
  generalize ePhi1 g.lam g.abelian₂ g.C g.wq = E at *
  generalize g.wq⁻¹ = q at *
  generalize xAt g v = x at *
  have k1 : derivative (R := ℂ_[p]) (C ε * (X * E)) = C ε * (E + X * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, Derivation.leibniz]; simp [add_comm]
  have k2 : derivative (R := ℂ_[p]) (E ^ 2 * (q - C x * X ^ 2)) =
      E ^ 2 * (derivative (R := ℂ_[p]) q - C x * (2 * X)) + (q - C x * X ^ 2) * (2 * E * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, map_sub, Derivation.leibniz (a := C x), Derivation.leibniz_pow, Derivation.leibniz_pow]
    simp only [derivative_C, derivative_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [k1] at dσ
  rw [k2] at dQ
  linear_combination -(C ε * (X * E)) * dQ + 2 * (E ^ 2 * (q - C x * X ^ 2)) * dσ - C ε * E ^ 3 * hω

end GlobalTheory.FrobStick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  first | exact @GlobalTheory.FrobStick.colC_atU | exact GlobalTheory.FrobStick.colC_atU | (intros; apply GlobalTheory.FrobStick.colC_atU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransport
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.DerivTransport

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) :
    coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · exact (contDiff_infty_iff_deriv.1 (hF.1.contDiff)).2.differentiable (by simp)
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = PowerSeries.derivative (R := ℂ_[p]) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  ext n
  have e : coef1 (deriv F) n = (((n + 1 : Qbar) * a (n + 1) : Qbar) : ℂ) := by
    rw [taylorCoeffAtZero_deriv, ha]; push_cast; rfl
  rw [PowerSeries.coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, e, ha,
    GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul]
  simp [mul_comm]

theorem atU_deriv : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  intro p _ g F hF
  refine ⟨algEnt_deriv hF, ?_⟩
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    PowerSeries.derivative_subst hs]
  have hd : PowerSeries.derivative (R := ℂ_[p]) (PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) =
      PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, GL3Theta.G1.l,
      GlobalTheory.WpForm.derivative_flog]
  rw [hd]
  ring

end GlobalTheory.DerivTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransportStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_parameter_series_deriv_transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  first | exact @GlobalTheory.DerivTransport.atU_deriv | exact GlobalTheory.DerivTransport.atU_deriv | (intros; apply GlobalTheory.DerivTransport.atU_deriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLog
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLog
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick.SubstLog

variable {p : ℕ} [Fact p.Prime]

theorem cc_lg (g : GL3Theta.G1 p) {x : MvPowerSeries (Fin 3) ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (g.lg x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ (GlobalTheory.SerTransport.const_l g)

theorem cc_pt {g : GL3Theta.G1 p} (hg : g.Ok) {x : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : MvPowerSeries.constantCoeff (g.pt x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ hg.2.2.1

theorem lg_pt {g : GL3Theta.G1 p} (hg : g.Ok) {x : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hx' : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have he : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hg.2.2.1
  unfold GL3Theta.G1.lg GL3Theta.G1.pt
  rw [← PowerSeries.subst_comp_subst_apply he hx', hg.2.2.2, PowerSeries.subst_X hx']

theorem cc_sum (g : GL3Theta.G1 p) {x y : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg x + g.lg y) = 0 := by
  rw [map_add (f := _), cc_lg g hx, cc_lg g hy, add_zero]

theorem cc_diff (g : GL3Theta.G1 p) {x y : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg x - g.lg y) = 0 := by
  rw [map_sub, cc_lg g hx, cc_lg g hy, sub_zero]

theorem cc_Cl (g : GL3Theta.G1 p) (c : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C c * g.l) = 0 := by
  rw [map_mul, GlobalTheory.SerTransport.const_l, mul_zero]

theorem subst_Cl (g : GL3Theta.G1 p) (c : ℂ_[p]) {w : MvPowerSeries (Fin 3) ℂ_[p]}
    (hw : MvPowerSeries.constantCoeff w = 0) (h : PowerSeries ℂ_[p]) :
    (PowerSeries.subst w (PowerSeries.subst (PowerSeries.C c * g.l) h : PowerSeries ℂ_[p]) :
        MvPowerSeries (Fin 3) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C c * g.lg w) h := by
  have hw' : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero hw
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (cc_Cl g c)) hw',
    PowerSeries.subst_mul hw', PowerSeries.subst_C]
  rfl

theorem hom_subst {a : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p]} (ha : MvPowerSeries.HasSubst a)
    {y : MvPowerSeries (Fin 3) ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) (h : PowerSeries ℂ_[p]) :
    MvPowerSeries.substAlgHom (R := ℂ_[p]) ha (PowerSeries.subst y h) =
      PowerSeries.subst (MvPowerSeries.substAlgHom (R := ℂ_[p]) ha y) h := by
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hy).const ha h

theorem formula_at {a : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p]}
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p])
    (h : GlobalTheory.FrobStick.defect f s = 0) :
    Matrix.det (Matrix.of fun i j => (PowerSeries.subst (a i) (f j) : MvPowerSeries (Fin 3) ℂ_[p])) =
      2 * PowerSeries.subst (a 0 + a 1 + a 2) s * PowerSeries.subst (a 0 - a 1) s *
        PowerSeries.subst (a 1 - a 2) s * PowerSeries.subst (a 2 - a 0) s := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hX : ∀ i, MvPowerSeries.substAlgHom (R := ℂ_[p]) ha (MvPowerSeries.X i) = a i := fun i => by
    rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  have h1 := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) ha) (sub_eq_zero.mp h)
  rw [AlgHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat, hom_subst ha (by simp),
    hom_subst ha (by simp), hom_subst ha (by simp), hom_subst ha (by simp)] at h1
  simp only [map_add (f := _), map_sub, hX] at h1
  rw [← h1]
  congr 1
  ext1 i j
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
  rw [hom_subst ha (by simp), hX]

theorem subst_log_formula : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  intro p _ g hg
  have hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have h01 : MvPowerSeries.constantCoeff
      (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := cc_pt hg (cc_sum g (hX 0) (hX 1))
  have hs : MvPowerSeries.constantCoeff
      (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    cc_pt hg (cc_sum g h01 (hX 2))
  have hd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (g.sub (GL3Theta.Xv i) (GL3Theta.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i j => cc_pt hg (cc_diff g (hX i) (hX j))
  refine ⟨hs, hd 0 1, hd 1 2, hd 2 0, fun c f s h => ?_⟩
  have ld : ∀ i j : Fin 3, g.lg (g.sub (GL3Theta.Xv i) (GL3Theta.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv i) - g.lg (GL3Theta.Xv j) := fun i j => lg_pt hg (cc_diff g (hX i) (hX j))
  have l01 : g.lg (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) := lg_pt hg (cc_sum g (hX 0) (hX 1))
  have ls : g.lg (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) + g.lg (GL3Theta.Xv 2) := by
    rw [← l01]; exact lg_pt hg (cc_sum g h01 (hX 2))
  have key := formula_at (a := fun i => MvPowerSeries.C c * g.lg (GL3Theta.Xv i))
    (fun i => by rw [map_mul, cc_lg g (hX i), mul_zero]) f s h
  simp only [subst_Cl g c (hX _), subst_Cl g c hs, subst_Cl g c (hd _ _), ld, ls, mul_add, mul_sub]
  exact key

end GlobalTheory.FrobStick.SubstLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLogStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.FrobStick.SubstLog.subst_log_formula | exact GlobalTheory.FrobStick.SubstLog.subst_log_formula | (intros; apply GlobalTheory.FrobStick.SubstLog.subst_log_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

def entireRing : Subring (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F}
  mul_mem' := fun {F G} hF hG => by
    exact (hF.mul hG : Differentiable ℂ (fun z => F z * G z))
  one_mem' := by simpa using (differentiable_const (1 : ℂ) : Differentiable ℂ fun _ : ℂ => (1 : ℂ))
  add_mem' := fun {F G} hF hG => by
    exact (hF.add hG : Differentiable ℂ (fun z => F z + G z))
  zero_mem' := by simpa using (differentiable_const (0 : ℂ) : Differentiable ℂ fun _ : ℂ => (0 : ℂ))
  neg_mem' := fun {F} hF => by
    exact (hF.neg : Differentiable ℂ (fun z => -F z))

theorem tay_coeff (F : ℂ → ℂ) (n : ℕ) : PowerSeries.coeff n (tay F) = coef1 F n := by
  simp [tay, PowerSeries.coeff_mk]

def tayHom : entireRing →+* PowerSeries ℂ where
  toFun F := tay F
  map_one' := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_one]
    exact GlobalTheory.SerTransport.taylorCoeff_const_function 1 n
  map_mul' F G := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_mul]
    have := GlobalTheory.SerTransport.taylorCoeff_mul_entire F.2 G.2 n
    simp only [tay_coeff]
    exact this
  map_zero' := by
    ext n
    rw [tay_coeff, map_zero]
    have := GlobalTheory.SerTransport.taylorCoeff_const_function 0 n
    simp only [ite_self] at this
    exact this
  map_add' F G := by
    ext n
    rw [map_add (f := _), tay_coeff, tay_coeff, tay_coeff]
    exact GlobalTheory.SerTransport.taylorCoeff_add_entire F.2 G.2 n

def scaleE (β : ℂ) (F : entireRing) : entireRing :=
  ⟨fun z => F.1 (β * z), F.2.comp (differentiable_id.const_mul β)⟩

theorem rescale_tayHom (β : ℂ) (F : entireRing) :
    PowerSeries.rescale β (tayHom F) = tayHom (scaleE β F) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  show β ^ n * PowerSeries.coeff n (tay F.1) = PowerSeries.coeff n (tay (fun z => F.1 (β * z)))
  rw [tay_coeff, tay_coeff, GlobalTheory.SerTransport.taylorCoeff_scale_entire F.2]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem tay_defect_eq_zero : (∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0) → (∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s) → (∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0)) → ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j)) (GlobalTheory.FrobStick.tay (sgStar Λ)) = 0 := by
  intro hLine hRestr hId Λ hL v hv
  have hS : Differentiable ℂ (sgStar Λ) := hL.differentiable
  have hQ : Differentiable ℂ (sqTh Λ v) := hL.differentiable_sqTh v
  have hdS : Differentiable ℂ (deriv (sgStar Λ)) := fun z => ((hS.analyticAt z).deriv).differentiableAt
  have hdQ : Differentiable ℂ (deriv (sqTh Λ v)) := fun z => ((hQ.analyticAt z).deriv).differentiableAt
  have hA : Differentiable ℂ (colA Λ) :=
    (hS.pow 3 : Differentiable ℂ (fun z => sgStar Λ z ^ 3))
  have hB : Differentiable ℂ (colB Λ v) :=
    (hS.mul (hQ.add ((hS.pow 2).const_mul (wpF Λ v))) :
      Differentiable ℂ (fun z => sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)))
  have hC : Differentiable ℂ (colC Λ v) :=
    ((hS.mul hdQ).sub ((hdS.const_mul 2).mul hQ) :
      Differentiable ℂ (fun z => sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z))
  let a : Fin 3 → entireRing := ![⟨colA Λ, hA⟩, ⟨colB Λ v, hB⟩, ⟨colC Λ v, hC⟩]
  let s : entireRing := ⟨sgStar Λ, hS⟩
  have ha : ∀ j, tay (![colA Λ, colB Λ v, colC Λ v] j) = tayHom (a j) := by
    intro j; fin_cases j <;> rfl
  apply hLine ℂ
  intro t
  rw [hRestr]
  have e1 : (Matrix.of fun i j => PowerSeries.rescale (t i) (tay (![colA Λ, colB Λ v, colC Λ v] j))) =
      tayHom.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ha, rescale_tayHom]
  have es : tay (sgStar Λ) = tayHom s := rfl
  rw [e1, ← RingHom.map_det, es, rescale_tayHom, rescale_tayHom, rescale_tayHom, rescale_tayHom,
    show (2 : PowerSeries ℂ) = tayHom 2 from (map_ofNat tayHom 2).symm,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub]
  convert map_zero tayHom
  refine Subtype.ext (funext fun z => ?_)
  let φ : entireRing →+* ℂ := (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp entireRing.subtype
  rw [ZeroMemClass.coe_zero, Pi.zero_apply]
  have hφ : ∀ x : entireRing, (x : ℂ → ℂ) z = φ x := fun x => rfl
  rw [hφ]
  rw [map_sub, RingHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  have hm : φ.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) =
      Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j ((fun i => t i * z) i) := by
    ext i j; fin_cases j <;> rfl
  rw [hm, hId Λ hL v hv (fun i => t i * z)]
  change _ - 2 * sgStar Λ ((t 0 + t 1 + t 2) * z) * sgStar Λ ((t 0 - t 1) * z) * sgStar Λ ((t 1 - t 2) * z) *
    sgStar Λ ((t 2 - t 0) * z) = 0
  simp only [add_mul, sub_mul, sub_self]

end GlobalTheory.FrobStick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZeroStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_taylor_defect_eq_zero : (∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0) → (∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s) → (∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0)) → ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j)) (GlobalTheory.FrobStick.tay (sgStar Λ)) = 0 := by
  first | exact @GlobalTheory.FrobStick.tay_defect_eq_zero | exact GlobalTheory.FrobStick.tay_defect_eq_zero | (intros; apply GlobalTheory.FrobStick.tay_defect_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLine
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick

theorem hasSubst_line {R : Type} [CommRing R] (t : Fin 3 → R) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := R))

theorem subst_line_subst {R : Type} [CommRing R] (t : Fin 3 → R) (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (PowerSeries.subst a f : MvPowerSeries (Fin 3) R) : PowerSeries R) =
      PowerSeries.subst (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a : PowerSeries R) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has (hasSubst_line t)]
  rfl

theorem subst_C_mul_X {R : Type} [CommRing R] (c : R) (f : PowerSeries R) :
    PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries R) f = PowerSeries.rescale c f := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem defect_line (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R)
    (t : Fin 3 → R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (GlobalTheory.FrobStick.defect f s) : PowerSeries R) =
      Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) -
        2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s *
          PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s := by
  have hb := hasSubst_line t
  have hlin : ∀ (a : MvPowerSeries (Fin 3) R) (c : R), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a =
        (PowerSeries.C c * PowerSeries.X : PowerSeries R) → ∀ g : PowerSeries R,
      (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
        (PowerSeries.subst a g : MvPowerSeries (Fin 3) R) : PowerSeries R) = PowerSeries.rescale c g := by
    intro a c ha h g
    rw [subst_line_subst t a ha, h, subst_C_mul_X]
  have hX : ∀ i, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R) :=
    fun i => MvPowerSeries.subst_X hb i
  unfold defect
  rw [← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_sub, map_mul, AlgHom.map_det]

  have hmat : (MvPowerSeries.substAlgHom hb).mapMatrix
      (Matrix.of fun i j => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) :
        MvPowerSeries (Fin 3) R)) = Matrix.of fun i j => PowerSeries.rescale (t i) (f j) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPowerSeries.coe_substAlgHom]
    exact hlin _ _ (MvPowerSeries.constantCoeff_X i) (hX i) _
  rw [hmat, map_ofNat]
  simp only [MvPowerSeries.coe_substAlgHom]
  have h3 : MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t 0 + t 1 + t 2) * PowerSeries.X : PowerSeries R) := by
    rw [MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, hX, hX, hX, map_add (f := _), map_add (f := _), add_mul, add_mul]
  have hd : ∀ i j : Fin 3, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t i - t j) * PowerSeries.X : PowerSeries R) := by
    intro i j
    rw [MvPowerSeries.subst_sub hb, hX, hX, map_sub, sub_mul]
  have c3 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = 0 := by
    simp
  have cd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) = 0 := by
    intro i j; simp
  rw [hlin _ _ c3 h3, hlin _ _ (cd 0 1) (hd 0 1), hlin _ _ (cd 1 2) (hd 1 2), hlin _ _ (cd 2 0) (hd 2 0)]

end GlobalTheory.FrobStick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLineStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelbergerDeterminantDefect_on_line : ∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s := by
  first | exact @GlobalTheory.FrobStick.defect_line | exact GlobalTheory.FrobStick.defect_line | (intros; apply GlobalTheory.FrobStick.defect_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_cube_det_cplx : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  intro Λ hΛ v hv z
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hΛL : Λ = L.lattice.toAddSubgroup := AddSubgroup.ext hL
  have hσ : sgStar Λ = Formalism.L2.Th1.F.sgStar L := by rw [hΛL]; exact GlobalTheory.JetsGenusOne.sgStar_eq L
  have hwp : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hsd : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hopen : IsOpen ((Λ : Set ℂ)ᶜ) := by
    have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun w => hL w
    rw [this]; exact L.isClosed_lattice.isOpen_compl
  have hB : ∀ w, w ∉ Λ → colB Λ v w = sgStar Λ w ^ 3 * L.weierstrassP w := by
    intro w hw
    rw [colB, hΛ.sqTh_eq hv hw, ← hwp]
    ring
  have hC : ∀ w, w ∉ Λ → colC Λ v w = sgStar Λ w ^ 3 * L.derivWeierstrassP w := by
    intro w hw
    have hwL : w ∉ L.lattice := fun h => hw ((hL w).2 h)
    have hpd : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      have h1 : DifferentiableAt ℂ L.weierstrassP w :=
        L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
      have h2 := h1.hasDerivAt
      rwa [L.deriv_weierstrassP] at h2
    have hev : sqTh Λ v =ᶠ[nhds w] fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v) := by
      filter_upwards [hopen.mem_nhds hw] with u hu
      rw [hΛ.sqTh_eq hv hu, hwp]
    have hd : HasDerivAt (fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v))
        ((2 : ℕ) * sgStar Λ w ^ (2 - 1) * deriv (sgStar Λ) w * (L.weierstrassP w - wpF Λ v) +
          sgStar Λ w ^ 2 * L.derivWeierstrassP w) w :=
      ((hsd w).hasDerivAt.pow 2).mul (hpd.sub_const _)
    rw [colC, hev.deriv_eq, hd.deriv, hΛ.sqTh_eq hv hw, hwp]
    push_cast
    ring
  have hoff : ∀ y : Fin 3 → ℂ, (∀ i, y i ∉ Λ) →
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) =
        2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    intro y hy
    have h := Formalism.L2.Th1.F.sgStarThree L (y 0) (y 1) (y 2)
      (fun h => hy 0 ((hL _).2 h)) (fun h => hy 1 ((hL _).2 h)) (fun h => hy 2 ((hL _).2 h))
    rw [← hσ] at h
    rw [Matrix.det_fin_three] at h ⊢
    simp [Matrix.vecHead, Matrix.vecTail] at h ⊢
    rw [hB _ (hy 0), hB _ (hy 1), hB _ (hy 2), hC _ (hy 0), hC _ (hy 1), hC _ (hy 2)]
    simp only [colA]
    linear_combination h
  have hcA : Continuous (colA Λ) := by
    have := hsd.continuous
    unfold colA; fun_prop
  have hcB : Continuous (colB Λ v) := by
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colB; fun_prop
  have hcC : Continuous (colC Λ v) := by
    have h1 : Continuous (deriv (sqTh Λ v)) :=
      ((hΛ.differentiable_sqTh v).contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv (sgStar Λ)) := (hsd.contDiff (n := 1)).continuous_deriv le_rfl
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colC; fun_prop
  have hcL : Continuous fun y : Fin 3 → ℂ =>
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    fin_cases j
    · exact hcA.comp (continuous_apply i)
    · exact hcB.comp (continuous_apply i)
    · exact hcC.comp (continuous_apply i)
  have hcR : Continuous fun y : Fin 3 → ℂ =>
      2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    have := hsd.continuous
    fun_prop
  have hdense : Dense {y : Fin 3 → ℂ | ∀ i, y i ∉ Λ} := by
    have := dense_pi (Set.univ : Set (Fin 3)) (s := fun _ => ((Λ : Set ℂ)ᶜ)) fun _ _ => hΛ.dense_compl
    convert this using 1
    ext y; simp
  exact congrFun (Continuous.ext_on hdense hcL hcR fun y hy => hoff y hy) z

end GlobalTheory.FrobStick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplexStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_stickelberger_sigmaStar_det_complex : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  first | exact @GlobalTheory.FrobStick.sgStar_cube_det_cplx | exact GlobalTheory.FrobStick.sgStar_cube_det_cplx | (intros; apply GlobalTheory.FrobStick.sgStar_cube_det_cplx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplex
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStickMap

theorem hasSubst_of_cc {R : Type*} [CommRing R] (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero ha

theorem map_defect {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (f : Fin 3 → R⟦X⟧) (s : R⟦X⟧) :
    MvPowerSeries.map h (GlobalTheory.FrobStick.defect f s)
      = GlobalTheory.FrobStick.defect (fun j => PowerSeries.map h (f j)) (PowerSeries.map h s) := by
  have hs : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ g : R⟦X⟧,
      MvPowerSeries.map h (subst a g) = subst (MvPowerSeries.map h a) (PowerSeries.map h g) :=
    fun a ha g => PowerSeries.map_subst (hasSubst_of_cc a ha) g
  unfold GlobalTheory.FrobStick.defect
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  rw [RingHom.map_det]
  congr 1
  · congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hs _ (by simp) _]
    simp
  · rw [hs _ (by simp), hs _ (by simp), hs _ (by simp), hs _ (by simp)]
    simp [map_add (f := _), map_sub]

end GlobalTheory.FrobStickMap

namespace GlobalTheory.FrobStickMap

noncomputable def tq (F : ℂ → ℂ) : (↥Qbar)⟦X⟧ :=
  PowerSeries.mk (fun n => if h : coef1 F n ∈ Qbar then ⟨_, h⟩ else 0)

theorem map_tq_of_algEnt (F : ℂ → ℂ) (hF : AlgEnt F) :
    PowerSeries.map (algebraMap (↥Qbar) ℂ) (tq F) = GlobalTheory.FrobStick.tay F := by
  ext n
  simp only [tq, GlobalTheory.FrobStick.tay, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [dite_eq_left (hF.2 n)]
  rfl

theorem mvmap_injective {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (hi : Function.Injective h) :
    Function.Injective (MvPowerSeries.map (σ := Fin 3) h) := by
  intro a b hab
  ext n
  apply hi
  have := congrArg (MvPowerSeries.coeff n) hab
  simpa [MvPowerSeries.coeff_map] using this

theorem defect_ser1_eq_zero_of_defect_tay_eq_zero (p : ℕ) [Fact p.Prime] (lam : (↥Qbar) →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ)
    (s : ℂ → ℂ) (hf : ∀ j, AlgEnt (f j)) (hs : AlgEnt s)
    (h0 : GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0) :
    GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  have hq : GlobalTheory.FrobStick.defect (fun j => tq (f j)) (tq s) = 0 := by
    apply mvmap_injective (algebraMap (↥Qbar) ℂ) (FaithfulSMul.algebraMap_injective _ _)
    rw [map_defect, map_zero]
    simp only [map_tq_of_algEnt _ (hf _), map_tq_of_algEnt _ hs]
    exact h0
  have hser : ∀ F : ℂ → ℂ, AlgEnt F → GL3Theta.ser1 lam F = PowerSeries.map lam (tq F) := fun F hF =>
    GlobalTheory.EvenTheta.Param.theta_series_map_coefficients lam F (tq F) (map_tq_of_algEnt F hF).symm
  simp only [hser _ (hf _), hser _ hs]
  rw [← map_defect, hq, map_zero]

end GlobalTheory.FrobStickMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplexStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ) (s : ℂ → ℂ), (∀ j, AlgEnt (f j)) → AlgEnt s → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0 → GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  first | exact @GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | exact GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | (intros; apply GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormula
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

theorem frobenius_stickelberger_padic_determinant_formula : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := GlobalTheory.T.genus_one_datum_model_lattice_algebraic_data D p cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  obtain ⟨hAa, hBa, hS, hAv, hBv⟩ := GlobalTheory.T.sigmaStar_cube_columns_model_parameter_series p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hCa, hCv⟩ := GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series GlobalTheory.T.model_parameter_series_deriv_transport p g hq hL h2 h3 hσ v hv hw
  have hF : ∀ j, AlgEnt (![colA g.abelian₂, colB g.abelian₂ v, colC g.abelian₂ v] j) := by
    intro j; fin_cases j
    exacts [hAa, hBa, hCa]
  have h6 := GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex p g.lam _ (sgStar g.abelian₂) hF hσ (GlobalTheory.T.frobeniusStickelberger_taylor_defect_eq_zero GlobalTheory.T.mvPowerSeries_fin_three_eq_zero_of_subst_lines GlobalTheory.T.frobeniusStickelbergerDeterminantDefect_on_line GlobalTheory.T.frobenius_stickelberger_sigmaStar_det_complex g.abelian₂ hL v hv)
  obtain ⟨c0, c1, c2, c3, h7⟩ := GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log p g ok
  have h8 := h7 ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) _ _ h6
  have e : ∀ F : ℂ → ℂ, (PowerSeries.subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) (GL3Theta.ser1 g.lam F) : PowerSeries ℂ_[p]) = g.atU F :=
    fun F => (GlobalTheory.SerTransport.atU_eq g F).symm
  simp only [e, hS] at h8
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  refine GlobalTheory.T.det_column_operations_model_parameter p (ePhi1 g.lam g.abelian₂ g.C g.wq) g.wq ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) g.C.r g.W.a₁ g.W.a₃ _ _ _ _ (Units.ne_zero _) hw0 c0 c1 c2 c3 ?_
  rw [← h8]
  congr 1
  ext i j
  fin_cases j <;> simp [hAv, hBv, hCv]

end GlobalTheory.FrobStick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormulaStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  first | exact @GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | exact GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | (intros; apply GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula <;> assumption)
end
