module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaCombinationsAwayD
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodModelTwoScaleOne
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc

theorem goodModelTwo_scaleOne : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[2], ∃ W : WeierstrassCurve ℂ_[2], Unif 2 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W ∧
      ‖W.a₁‖ = 1 := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  obtain ⟨hsq, -, hcm⟩ := LocJets.data ha hd lam hlam hok
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨c, hc, W', ⟨e2, e3⟩, ⟨h1, h2, h3, h4, h6, hΔ⟩, ha1⟩ := hIn.modelTwo D.host.d L hsq h8 hcm ι
  have hL1 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hlat]; rfl
    obtain ⟨f2, f3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
    rw [← f2, ← f3]
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have hh := Formalism.L2.Th1.F.homogeneity L c hc
  have s2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hh.2.2.2.2.2.2.2.2.2.1
  have s3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hh.2.2.2.2.2.2.2.2.2.2
  have g2W : W'.c₄ / 12 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := e2
  have g3W : W'.c₆ / 216 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := e3
  set u : ℂ_[2] := ι c with hu
  have hu0 : u ≠ 0 := by simpa [hu] using hc

  have hW'Δ : W'.Δ = (u ^ 12)⁻¹ := by
    have hrel := W'.c_relation
    have hc4 : W'.c₄ = 12 * ((u ^ 4)⁻¹ * ι L.g₂) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s2, ← g2W]; ring
    have hc6 : W'.c₆ = 216 * ((u ^ 6)⁻¹ * ι L.g₃) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s3, ← g3W]; ring
    have hι1 : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hL1, map_one]
    rw [hc4, hc6] at hrel
    have h1728 : (1728 : ℂ_[2]) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h1728
    rw [hrel]
    field_simp
    linear_combination (1728 : ℂ_[2]) * hι1
  have hun : ‖u‖ = 1 := by
    rw [hW'Δ, norm_inv, norm_pow] at hΔ
    have h12 : ‖u‖ ^ 12 = 1 := by
      have hpos : 0 < ‖u‖ ^ 12 := pow_pos (norm_pos_iff.2 hu0) _
      field_simp at hΔ; linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  let C : WeierstrassCurve.VariableChange ℂ_[2] := ⟨(Units.mk0 u hu0)⁻¹, 0, 0, 0⟩
  have hCu : ((C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) = u := by simp [C]
  refine ⟨C • W', ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (C • W').c₄ / 12 = ι L.g₂
    rw [WeierstrassCurve.variableChange_c₄, hCu, mul_div_assoc, g2W, s2, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · show (C • W').c₆ / 216 = ι L.g₃
    rw [WeierstrassCurve.variableChange_c₆, hCu, mul_div_assoc, g3W, s3, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact h1
  · rw [WeierstrassCurve.variableChange_a₂, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, norm_mul, norm_pow, hun, one_pow,
      one_mul]; exact h2
  · rw [WeierstrassCurve.variableChange_a₃, hCu]
    simp only [C, zero_mul, mul_zero, add_zero, norm_mul, norm_pow, hun, one_pow, one_mul]; exact h3
  · rw [WeierstrassCurve.variableChange_a₄, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, norm_mul, norm_pow, hun,
      one_pow, one_mul]; exact h4
  · rw [WeierstrassCurve.variableChange_a₆, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, zero_pow three_ne_zero,
      norm_mul, norm_pow, hun, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, hCu, norm_mul, norm_pow, hun, one_pow, one_mul]; exact hΔ
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact ha1

end GlobalTheory.ThLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfDisc
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.ModelThree

theorem norm_add_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_sub_le_max' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K} (hlt : ‖α‖ < ‖β‖)
    (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  have hb : 0 < ‖β‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : ‖α ^ 2 - α * β‖ < ‖β ^ 2‖ := by
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
    · rw [norm_pow, norm_pow]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    · rw [norm_mul, norm_pow, sq]; exact mul_lt_mul_of_pos_right hlt hb
  have h2 : ‖β ^ 2 + (α ^ 2 - α * β)‖ = ‖β ^ 2‖ := norm_add_of_lt h1
  have h3 : α ^ 2 - α * β + β ^ 2 = β ^ 2 + (α ^ 2 - α * β) := by ring
  rw [h3, h2, norm_pow] at hN
  have h4 : ‖β‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact ⟨(hlt.trans_le h4).le, h4⟩

theorem norm_le_one_of_disc {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K}
    (h : ‖α * β * (α - β)‖ = 1) (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  rcases lt_trichotomy ‖α‖ ‖β‖ with hlt | heq | hgt
  · exact norm_le_one_of_lt hlt hN
  · have hc : ‖α - β‖ ≤ ‖α‖ := by
      refine (norm_sub_le_max' _ _).trans ?_
      rw [heq, max_self]
    rcases hc.lt_or_eq with hc | hc
    · have h1 : ‖(α - β) ^ 2‖ < ‖α * β‖ := by
        rw [norm_pow, norm_mul, ← heq, ← sq]
        exact pow_lt_pow_left₀ hc (norm_nonneg _) (by norm_num)
      have h2 : ‖α * β + (α - β) ^ 2‖ = ‖α * β‖ := norm_add_of_lt h1
      have h3 : α ^ 2 - α * β + β ^ 2 = α * β + (α - β) ^ 2 := by ring
      rw [h3, h2, norm_mul, ← heq] at hN
      have h4 : ‖α‖ ≤ 1 := by
        by_contra hc'
        push Not at hc'
        nlinarith
      exact ⟨h4, heq ▸ h4⟩
    · rw [norm_mul, norm_mul, hc, ← heq] at h
      have h4 : ‖α‖ ^ 3 = 1 := by rw [← h]; ring
      have h5 : ‖α‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4
      exact ⟨h5.le, (heq ▸ h5).le⟩
  · have hN' : ‖β ^ 2 - β * α + α ^ 2‖ ≤ 1 := by
      have : β ^ 2 - β * α + α ^ 2 = α ^ 2 - α * β + β ^ 2 := by ring
      rw [this]; exact hN
    exact (norm_le_one_of_lt hgt hN').symm

theorem exists_roots {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (g2 g3 : K) :
    ∃ α β : K, 16 * (α ^ 2 - α * β + β ^ 2) = 12 * g2 ∧
      64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) = 216 * g3 := by
  let f : Polynomial K := Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C g2 * Polynomial.X - Polynomial.C g3
  have hdeg : f.degree ≠ 0 := by
    have h3 : f.natDegree = 3 := by
      simp only [f]
      compute_degree!
    intro h
    have h0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h.le
    omega
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root f hdeg
  have he' : 4 * e ^ 3 - g2 * e - g3 = 0 := by simpa [f, Polynomial.IsRoot] using he
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (g2 - 3 * e ^ 2) (n := 2) (by norm_num)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨(-3 * e + s) / 2, (-3 * e - s) / 2, ?_, ?_⟩
  · field_simp
    linear_combination (48 : K) * hs
  · have e1 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he'
    rw [e1]
    field_simp
    linear_combination (-1728 * e : K) * hs

def twoTorsionModel {K : Type} [Field K] (α β : K) : WeierstrassCurve K := ⟨0, -(α + β), 0, α * β, 0⟩

theorem c₄_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₄ = 16 * (α ^ 2 - α * β + β ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, twoTorsionModel]
  ring

theorem c₆_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₆ = 64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, twoTorsionModel]
  ring

theorem Δ_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).Δ = 16 * (α * β * (α - β)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, twoTorsionModel]
  ring

theorem norm_two : ‖(2 : ℂ_[3])‖ = 1 := by
  have e : (2 : ℂ_[3]) = algebraMap ℚ_[3] ℂ_[3] ((2 : ℕ) : ℚ_[3]) := by rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  norm_num

theorem exists_model (g2 g3 : ℂ_[3]) (hΔ : g2 ^ 3 - 27 * g3 ^ 2 = 1) (hj : ‖1728 * g2 ^ 3‖ ≤ 1) :
    ∃ W : WeierstrassCurve ℂ_[3], Formalism.L2.Th1.A.g₂ W = g2 ∧ Formalism.L2.Th1.A.g₃ W = g3 ∧ IntCurve W := by
  obtain ⟨α, β, h4, h6⟩ := exists_roots g2 g3
  have c4 : (twoTorsionModel α β).c₄ = 12 * g2 := by rw [c₄_model, h4]
  have c6 : (twoTorsionModel α β).c₆ = 216 * g3 := by rw [c₆_model, h6]
  have hD : (twoTorsionModel α β).Δ = 1 := by
    have hc := (twoTorsionModel α β).c_relation
    rw [c4, c6] at hc
    have : (1728 : ℂ_[3]) * (twoTorsionModel α β).Δ = 1728 * (g2 ^ 3 - 27 * g3 ^ 2) := by
      linear_combination hc
    exact (mul_left_cancel₀ (by norm_num) this).trans hΔ
  have n16 : ‖(16 : ℂ_[3])‖ = 1 := by
    have : (16 : ℂ_[3]) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, norm_two, one_pow]
  have hprod : ‖α * β * (α - β)‖ = 1 := by
    have h1 := congrArg norm hD
    rw [Δ_model, norm_mul, n16, one_mul, norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1 := by
    have e : (16 * (α ^ 2 - α * β + β ^ 2)) ^ 3 = 1728 * g2 ^ 3 := by rw [h4]; ring
    have h1 : ‖(16 * (α ^ 2 - α * β + β ^ 2)) ^ 3‖ ≤ 1 := by rw [e]; exact hj
    rw [norm_pow, norm_mul, n16, one_mul] at h1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨ha, hb⟩ := norm_le_one_of_disc hprod hN
  refine ⟨twoTorsionModel α β, ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂
    rw [c4]; field_simp
  · unfold Formalism.L2.Th1.A.g₃
    rw [c6]; field_simp
  · refine ⟨by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_⟩
    · simp only [twoTorsionModel, norm_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · simp only [twoTorsionModel, norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) hb
    · rw [hD, norm_one]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_iota_le_one (ι : ℂ ≃+* ℂ_[3]) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨f, hf, hr⟩ := hx
  refine norm_le_one_of_isIntegral ⟨f, hf, ?_⟩
  have h := congrArg (ι : ℂ →+* ℂ_[3]) hr
  rw [map_zero, Polynomial.hom_eval₂] at h
  have e : (@algebraMap ℤ ℂ_[3] _ _ (Ring.toIntAlgebra ℂ_[3])) = (ι : ℂ →+* ℂ_[3]).comp (algebraMap ℤ ℂ) :=
    Subsingleton.elim _ _
  rw [e]
  exact h

theorem goodModelThree : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[3], ∃ W : WeierstrassCurve ℂ_[3], Unif 3 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hL ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) L hL'
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd hok.1
      (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ D.host.d hok.1 hok.2.2.1))
  have hd8 := hok.2.2.1
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) :=
    hIn.jInt D.host.d L hok.2.2.2.prime.squarefree (by omega) hcm
  have hj' : Formalism.L2.Th1.CM.jInv L = 1728 * L.g₂ ^ 3 := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [hdisc, div_one]
  rw [hj'] at hj
  have hn := norm_iota_le_one ι hj
  have hΔ : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
    have := congrArg ι hdisc
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one] using this
  have hn' : ‖1728 * ι L.g₂ ^ 3‖ ≤ 1 := by
    simpa only [map_mul, map_pow, map_ofNat] using hn
  obtain ⟨W, h2, h3, hW⟩ := exists_model _ _ hΔ hn'
  exact ⟨W, ⟨h2, h3⟩, hW⟩

end GlobalTheory.ThLoc.ModelThree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDisc
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

open scoped ComplexConjugate

theorem GlobalTheory.ThLoc.jetsIntegral_three (hIn : GlobalTheory.ThLoc.Inputs) {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hd : 0 < dK)
    (lam : ℂ) (hlam : lam ≠ 0) (hd3 : dK % 3 = 2) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (ι : ℂ ≃+* ℂ_[3])
    (hL : GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ dK ha hd lam hlam h Λ θ 3 ι) (W : WeierstrassCurve ℂ_[3])
    (hU : Unif 3 (cmL a₀ b₀ dK ha hd lam hlam) ι W) (hW : IntCurve W)
    {κx : Type} [Fintype κx] (r : κx → ℂ_[3]) (t : κx → n → ℂ) (M : ℕ) (hr : ∀ k, ‖r k‖ ≤ 1) (hM : 0 < M)
    (hpM : ¬ 3 ∣ M) (ht : ∀ k, (M : ℂ) • t k ∈ Λ) {J : Type} [Fintype J] (v : J → n → ℂ)
    (hv : ∀ j, InMul (cmL a₀ b₀ dK ha hd lam hlam) Λ (v j)) {ν : Type} [Fintype ν] (A : J → ν → ℂ_[3])
    (hA : ∀ j x, ‖A j x‖ ≤ 1) :
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[3]) h θ r t (frameM (ι : ℂ →+* ℂ_[3]) v A)) := by
  obtain ⟨hcmok, l2, l3, l4, l5⟩ := hL
  obtain ⟨-, -, hcm⟩ := GlobalTheory.ThLoc.LocJets.data ha hd lam hlam hcmok
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hd lam hlam).lattice :=
    (cmL a₀ b₀ dK ha hd lam hlam).ω₁_mem_lattice
  have hω1 : Formalism.L2.Th1.CM.omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok 1 (Or.inl rfl)
    simpa [Formalism.L2.Th1.CM.omegaK] using this
  have hω2 : conj (Formalism.L2.Th1.CM.omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok (-1) (Or.inr rfl)
    rw [GlobalTheory.ThLoc.LocJets.conj_omegaK]
    simpa [sub_eq_add_neg] using this
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := l5
  obtain ⟨Dm, q0, hD, hq0, hfac, hgram⟩ :=
    GlobalTheory.ThLoc.LocJets.gram_transfer a₀ b₀ c₀ dK ha hd lam hlam hcmok n h Λ g₁ hiso 3 ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    Formalism.L2.Th1.GD.FrameCompose_proof ℂ_[3] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) Dm (fun i j => ι (v j i))
      (fun j k => ι (Formalism.L2.Th1.GD.hOK (cmL a₀ b₀ dK ha hd lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (Formalism.L2.Th1.G.linSub (frameM (ι : ℂ →+* ℂ_[3]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[3]) (taylorMv (Formalism.L2.Th1.H.opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩ := GlobalTheory.ThLoc.LocJets.fourth_power_theta a₀ b₀ c₀ dK ha hd
      lam hlam hcmok n h Λ l2 l3 θ l4 3 ι g₁ ε hiso hidx hidx' hε hten (t k) M hM hpM (ht k)
    have hj := hIn.jetsThree dK _ hcmok.2.2.1 hd3 hcm ι W hU hW (lam * a₀) hω hω1 hω2
      (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs'
    rw [← he] at hj
    exact GlobalTheory.ThLoc.LocJets.jets_linear ℂ_[3] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[3]) v A) Cm hCm hfacC
  exact GlobalTheory.ThLoc.LocJets.jets_comb r _ hr key

theorem GlobalTheory.ThLoc.jetsIntegral_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat n _ _ h Λ θ p _ ι hL hpd h3 κx _ r t M hr hM hpM ht
    J _ v hv ν _ A hA
  have hpr : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    obtain ⟨W, hU, hW, ha1⟩ := GlobalTheory.ThLoc.goodModelTwo_scaleOne hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact (hIn.jetsTwo a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 ι W hU hW ha1 l5 κx r t M hr hM hpM ht
      J v hv ν A hA).1
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨W, hU, hW⟩ := GlobalTheory.ThLoc.ModelThree.goodModelThree hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact GlobalTheory.ThLoc.jetsIntegral_three hIn ha hd lam hlam (h3 rfl) h Λ θ ι hL W hU hW r t M hr hM hpM ht v hv A hA
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by decide)
  have h5 : 5 ≤ p := by have := hpr.two_le; omega
  have hW := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat p h5 ι
  have hnd : ¬ p ∣ D.host.d := fun hdv => hpd ((Nat.prime_dvd_prime_iff_eq hpr l1.2.2.2).1 hdv)
  exact (hIn.jetsOdd a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 p hp2 hnd ι hW l5 κx r t M hr hM hpM ht
    J v hv ν A hA).1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDiscStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  first | exact @GlobalTheory.ThLoc.jetsIntegral_away_disc | exact GlobalTheory.ThLoc.jetsIntegral_away_disc | (intros; apply GlobalTheory.ThLoc.jetsIntegral_away_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaCombinationsAwayD
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

theorem jets_comb {K : Type} [NormedField K] [IsUltrametricDist K] {X κ : Type} [Fintype κ] (r : κ → K)
    (sg : κ → MvPowerSeries X K) (hr : ∀ k, ‖r k‖ ≤ 1) (hsg : ∀ k, JetsIntegral (sg k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * sg k) := by
  refine (Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_
  refine Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_
  exact Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k))
    ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((TaylorLogMetric.embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem norm_natCast_coprime {p : ℕ} [Fact p.Prime] {n : ℕ} (h : Nat.Coprime n p) : ‖(n : ℂ_[p])‖ = 1 := by
  have e : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p]) := (map_natCast _ n).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem atLin_X {σ κ : Type} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) F = Formalism.L2.Th1.G.linSub c F := rfl

theorem tauEmb_eq {D : D7} {p : ℕ} [Fact p.Prime] {lm : TaylorLogMetric.Qbar →+* ℂ_[p]} {ι : ℂ ≃+* ℂ_[p]}
    (hι : Formalism.L2.KerInert.IotaExt lm ι) (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.tauEmb D lm τ x = ι (TaylorLogMetric.embT D τ x) := by
  have h := embT_mem D τ x
  show TaylorLogMetric.lamC lm (TaylorLogMetric.embT D τ x) = _
  rw [TaylorLogMetric.lamC, dite_eq_left h]
  exact (hι ⟨_, h⟩).symm

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem analytic_U (B : Base D cc δ) (t : TaylorLogMetric.VC D N N') {G : TaylorLogMetric.VC D N N' → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (TaylorLogMetric.U D B.tor t G) Set.univ := by
  have hadd : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => z + t) Set.univ := fun z _ => by fun_prop
  have h1 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => G (z + t)) Set.univ :=
    hG.comp hadd (fun _ _ => Set.mem_univ _)
  let ℓ : TaylorLogMetric.VC D N N' →ₗ[ℂ] ℂ := (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N').flip t
  have h2 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => ℓ z) Set.univ :=
    (LinearMap.toContinuousLinearMap ℓ).analyticOnNhd _
  have h3 : ∀ z : TaylorLogMetric.VC D N N', TaylorLogMetric.Hf D B.tor z t = ℓ z := fun z => by
    show _ = formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' z t
    rw [formV_apply]; rfl
  intro z hz
  have h4 : AnalyticAt ℂ (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) z := by
    have := h2 z hz
    fun_prop
  have h5 := (h1 z hz).mul h4
  have e : TaylorLogMetric.U D B.tor t G = (fun z => G (z + t)) * (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) := by
    funext z
    simp only [TaylorLogMetric.U, h3, Pi.mul_apply]
  rw [e]
  exact h5

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem term_jets (hIn : GlobalTheory.ThLoc.Inputs) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {X : Fields} (s : Seam D X) (hs : s.Ok)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁') {p : ℕ} [Fact p.Prime] (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁')
    (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) (hι : Formalism.L2.KerInert.IotaExt lm ι)
    (hpd : p ≠ D.host.d) (h3 : p = 3 → D.host.d % 3 = 2)
    (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t)
    {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (hy : ∀ j, y j ∈ TaylorLogMetric.YYl D L L') :
    JetsIntegral (TaylorLogMetric.atLin (fun k j => TaylorLogMetric.tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j)
      (TaylorLogMetric.pSer D lm (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')))) := by
  obtain ⟨s₁, hs₁, e1, e2⟩ := id hE
  obtain ⟨s₂, hs₂, e3, e4⟩ := id hE'
  have hS : Nat.Coprime (s₁ * s₂) p := Nat.Coprime.mul_left hs₁ hs₂
  obtain ⟨M, hM0, hMc, hMm⟩ := (Formalism.L2.KerInert.pairing_fact D cc δ p N N' L L₁ L' L₁' hE hE').2 t ht
  have hLat := GlobalTheory.T.normalisedThetaFamily_normalised_all_places D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L₁ L₁' hA₁ p ι

  have hθ := hLat.mem_th.1
  have hEan : AnalyticOnNhd ℂ (B.eNat χ N N' L₁ L₁') Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) Set.univ :=
      (LinearMap.toContinuousLinearMap (s.flatV N N').symm.toLinearMap).analyticOnNhd _
    have h2 := hθ.comp h1 (fun _ _ => Set.mem_univ _)
    have e : (B.eNat χ N N' L₁ L₁') = (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) ∘ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) := by
      funext w
      simp
    rw [e]
    exact h2
  have hGan := analytic_U B t hEan
  have hCo : TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')) TaylorLogMetric.Qbar :=
    hIn.algT D cc δ B χ hcc hδ hχ N N' L₁ L₁' hA₁ t ⟨M, hM0, hMm⟩

  have hU : (fun z => TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁') (s.flatV N N' z)) =
      Formalism.L2.Th1.H.opU (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) ((s.flatV N N').symm t)
        (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) := by
    funext z
    rw [KS.opU_pb (s.flatV N N') _ _ (KS.form_flat s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))), LinearEquiv.apply_symm_apply]
    simp only [Formalism.L2.Th1.H.opU, formV_apply]
    rfl

  let v : Fin n → DVar X.Tau N N' → ℂ := fun j =>
    (s.flatV N N').symm (TaylorLogMetric.embV D B.tor (((s₁ * s₂ : ℕ) : D.host.E) • y j))
  let A : Fin n → Fin n → ℂ_[p] := fun j x => if j = x then (((s₁ * s₂ : ℕ) : ℂ_[p]))⁻¹ else 0
  have hn1 : ‖(((s₁ * s₂ : ℕ) : ℂ_[p]))‖ = 1 := norm_natCast_coprime hS
  have hn0 : (((s₁ * s₂ : ℕ) : ℂ_[p])) ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  have hv : ∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) (s.laF B.tor L₁ L₁') (v j) := by
    intro j ω hω
    show s.flatV N N' (ω • v j) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
    rw [map_smul, LinearEquiv.apply_symm_apply]
    refine AddSubgroup.subset_closure ⟨ω, ?_, _, Formalism.L2.KerInert.ie_yy_scale s₁ s₂ e2 e3 (hy j), rfl⟩
    show ω ∈ TaylorLogMetric.lamOf D cc δ
    rw [← hlat]
    exact hω
  have hA : ∀ j x, ‖A j x‖ ≤ 1 := by
    intro j x
    by_cases h : j = x
    · simp only [A, if_pos h, norm_inv, hn1, inv_one, le_refl]
    · simp only [A, if_neg h, norm_zero, zero_le_one]
  have hfr : (fun (i : DVar X.Tau N N') x => (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : Fin n) =>
      TaylorLogMetric.tauEmb D lm k.1 (y j k.2.1 k.2.2)) (s.iT i.1, i.2) x) = frameM (ι : ℂ →+* ℂ_[p]) v A := by
    funext i x
    have e : v x i = ((s₁ * s₂ : ℕ) : ℂ) * TaylorLogMetric.embT D (s.iT i.1) (y x i.2.1 i.2.2) := by
      show TaylorLogMetric.embT D (s.iT i.1) ((((s₁ * s₂ : ℕ) : D.host.E) • y x) i.2.1 i.2.2) = _
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast]
    simp only [frameM, A, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [tauEmb_eq hι, e]
    simp only [RingHom.coe_coe, map_mul, map_natCast]
    field_simp
  have key := GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hlat (DVar X.Tau N N')
    (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L₁ L₁')
    (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) p ι hLat hpd h3 Unit (fun _ => 1)
    (fun _ => (s.flatV N N').symm t) M (fun _ => by simp) hM0
    (fun h => by
      have := Nat.Coprime.eq_one_of_dvd hMc.symm h
      exact (Fact.out : p.Prime).one_lt.ne' this)
    (fun _ => by
      show s.flatV N N' ((M : ℂ) • (s.flatV N N').symm t) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
      rw [map_smul, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
      exact hMm)
    (Fin n) v hv (Fin n) A hA
  rw [GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor D X s N N' p lm ι hι _ hGan hCo (Fin n), hfr, hU]
  simpa [thetaLin] using key

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

theorem GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → TaylorLogMetric.JetsInt D lm (TaylorLogMetric.YYl D L L') F := by
  intro hIn D cc δ hcc hδ B χ hχ X s hs N N' L L' hA p _ lm hpd h3 F hF
  obtain ⟨ι, hι⟩ := hIn.lamExt p lm
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd : 0 < D.host.d := hdp.pos
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd hd8 hdp B.L (GlobalTheory.FourthRootStd.hst B)
  have hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by
    rw [hL]
    exact B.lat
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL1, rfl⟩ := hF
  refine (GlobalTheory.T.latticeJetsIntegral_iff_integralFrames D N N' p lm _ _).1.2 fun n y hy => ?_
  have e : ∀ (c : D.what₂.Tau × Fin N' × Fin N → Fin n → ℂ_[p]) (G : Fin m → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j)
        (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) * G k) =
      ∑ k, MvPowerSeries.C (r k) * TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) (G k) := by
    intro c G
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.atLin_X, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, Formalism.L2.Th1.G.linSubHom_apply]
    rfl
  rw [e]
  exact GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jets_comb r _ hr fun k =>
    GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.term_jets hIn hcc hδ B χ hχ s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat (hL1 k).1 (hL1 k).2.1 (hL1 k).2.2 lm ι hι hpd h3
      (t k) (ht k) y hy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaCombinationsAwayDStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralJets_normalisedThetaCombinations_away_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → TaylorLogMetric.JetsInt D lm (TaylorLogMetric.YYl D L L') F := by
  first | exact @GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll | exact GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll | (intros; apply GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBases
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHoms
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHoms
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.EntryHomComb

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem det_map_isUnit (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {P : Matrix (Fin N) (Fin N) D.host.E}
    (h : P.det ≠ 0) : IsUnit (P.map ρ).det := by
  have := ρ.map_det P
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact Ne.isUnit ((map_ne_zero ρ).2 h)

theorem coord_le_one (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (hP : LocBasisW D ρ L P) {x : Fin N → D.host.E} (hx : x ∈ L) (m : Fin N) :
    ‖((P.map ρ)⁻¹ *ᵥ fun i => ρ (x i)) m‖ ≤ 1 := by
  obtain ⟨s, hs, c, hc⟩ := hP.2.2 x hx
  have hs0 : ρ (s : D.host.E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hs; exact zero_ne_one hs
  have e : ∀ i, (s : D.host.E) * x i = ∑ a, (c a : D.host.E) * P i a := fun i => by
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply] at this
    exact this
  have h1 : (fun i => ρ (x i)) = (P.map ρ) *ᵥ fun a => (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have h2 := congrArg ρ (e i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum] at h2
    simp only [map_mul] at h2
    calc ρ (x i) = (ρ (s : D.host.E))⁻¹ * (ρ (s : D.host.E) * ρ (x i)) := by field_simp
      _ = _ := by
        rw [h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (det_map_isUnit D ρ hP.1), Matrix.one_mulVec, norm_mul,
    norm_inv, hs, inv_one, one_mul]
  exact GlobalTheory.JetTieCompare.norm_int_le ρ (c m)

theorem inv_mul_le_one (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B P : Matrix (Fin N) (Fin N) _}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (m b : Fin N) : ‖((P.map ρ)⁻¹ * B) m b‖ ≤ 1 := by
  obtain ⟨n, r, x, hr, hx, hcol⟩ := hB.2.2 b
  have : ((P.map ρ)⁻¹ * B) m b = ∑ k, r k * ((P.map ρ)⁻¹ *ᵥ fun i => ρ (x k i)) m := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hr k) (norm_nonneg _) (coord_le_one D ρ hP (hx k) m)

theorem inv_mul_le_one' (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B : Matrix (Fin N) (Fin N) ℂ_[p]}
    {P : Matrix (Fin N) (Fin N) D.host.E}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (a i : Fin N) : ‖(B⁻¹ * P.map ρ) a i‖ ≤ 1 := by
  obtain ⟨s, hs, hmem⟩ := hP.2.1 i
  have h := hB.2.1 _ hmem a
  rw [hρ] at h
  have e : (fun j => ρ ((s • P.transpose i) j)) = ρ (s : D.host.E) • fun j => ρ (P j i) := by
    funext j
    change ρ ((s : D.host.E) * P j i) = ρ (s : D.host.E) * ρ (P j i)
    rw [map_mul]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hs, one_mul] at h
  convert h using 2
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem entry_comb : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  intro D N N' L L' hA p _ lm τ B B' hB hB' a b
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lm τ
  obtain ⟨P, hP⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L hA.2.2.1.1 hA.2.2.1.2.1
  obtain ⟨P', hP'⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L' hA.2.2.2.1 hA.2.2.2.2.1
  have hex : ∀ q : Fin N' × Fin N, ∃ s : D.host.E, ‖ρ s‖ = 1 ∧
      (Matrix.of fun i j => s * (P' i q.1 * P⁻¹ q.2 j)) ∈ homL D L L' := fun q =>
    GlobalTheory.Proof.DirectionalDerivative.exists_smul_mem_homL D ρ hA.2.2.1.1 hP hP' q.2 q.1
  choose s hs hsA using hex
  have hs0 : ∀ q, ρ (s q) ≠ 0 := fun q h => by rw [← norm_eq_zero, hs q] at h; exact one_ne_zero h
  let e := Fintype.equivFin (Fin N' × Fin N)
  have hdet := det_map_isUnit D ρ hP.1
  have hdet' := det_map_isUnit D ρ hP'.1
  have hinv : (P.map ρ)⁻¹ = (P⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hP.1), Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  refine ⟨Fintype.card (Fin N' × Fin N),
    fun j => ((P'.map ρ)⁻¹ * B') (e.symm j).1 b * (B⁻¹ * P.map ρ) a (e.symm j).2 * (ρ (s (e.symm j)))⁻¹,
    fun j => Matrix.of fun k l => s (e.symm j) * (P' k (e.symm j).1 * P⁻¹ (e.symm j).2 l), fun j => ?_,
    fun j => hsA _, fun k l => ?_⟩
  · rw [norm_mul, norm_mul, norm_inv, hs, inv_one, mul_one]
    exact mul_le_one₀ (inv_mul_le_one D ρ hρ hB' hP' _ b) (norm_nonneg _) (inv_mul_le_one' D ρ hρ hB hP a _)
  · have e1 : B' k b = ∑ m, ρ (P' k m) * ((P'.map ρ)⁻¹ * B') m b := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_left (P'.map ρ) B' hdet']
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    have e2 : B⁻¹ a l = ∑ i, (B⁻¹ * P.map ρ) a i * ρ (P⁻¹ i l) := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_right (P.map ρ) B⁻¹ hdet, hinv]
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    rw [e1, e2, Finset.sum_mul_sum, ← Fintype.sum_prod_type', hρ, ← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, map_mul]
    field_simp [hs0 (e.symm j)]

end GlobalTheory.EntryHomComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHomsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixUnit_integral_comb_embedded_homs : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  first | exact @GlobalTheory.EntryHomComb.entry_comb | exact GlobalTheory.EntryHomComb.entry_comb | (intros; apply GlobalTheory.EntryHomComb.entry_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBases
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.integral_jets_realPlace_local_bases

theorem tauEmb_ringHom (D : D7) {p : ℕ} [Fact p.Prime] (lm : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ g : D.host.E →+* ℂ_[p], ∀ x, tauEmb D lm τ x = g x := by
  have hm : ∀ x, embT D τ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  exact ⟨lm.comp ((embT D τ).codRestrict Qbar hm), fun x => dif_pos (hm x)⟩

theorem jetsIntegral_basR : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  intro D cD hD N N' L L' hA p _ lm B B' κ hB hB' hκ F hF
  refine (GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames D N N' p lm (YYl D L L') F).2 hF _ _ ?_
  rintro ⟨j1, a, b⟩
  by_cases h0 : lamC lm (cD (tauPl D j1)) = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun ⟨τ, k1, k2⟩ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs with h
    · subst h
      have : κ (tauPl D j1) = 0 := by
        have := hκ (tauPl D j1); rw [h0, norm_zero] at this; exact norm_le_zero_iff.1 this
      simp [this]
    · rfl
  · set τ0 := tauPl D j1 with hτ0
    set c := κ τ0 / lamC lm (cD τ0) with hc
    have hcn : ‖c‖ ≤ 1 := by
      rw [hc, norm_div]; exact div_le_one_of_le₀ (hκ τ0) (norm_nonneg _)
    obtain ⟨n, r, aa, hr, haa, hsum⟩ := GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hD p lm τ0
    obtain ⟨m, r', A, hr', hA', hAsum⟩ :=
      GlobalTheory.T.matrixUnit_integral_comb_embedded_homs D N N' L L' hA p lm τ0 (B τ0) (B' τ0) (hB τ0) (hB' τ0) a b
    refine ⟨n * m, fun t => c * r (finProdFinEquiv.symm t).1 * r' (finProdFinEquiv.symm t).2,
      fun t => aa (finProdFinEquiv.symm t).1 • A (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
    · intro t
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖r _‖ * ‖r' _‖ ≤ 1 * 1 * 1 := by
            gcongr
            · exact hr _
            · exact hr' _
        _ = 1 := by norm_num
    · intro t
      exact Submodule.subset_span ⟨aa _, haa _, A _, hA' _, rfl⟩
    · rintro ⟨τ, k1, k2⟩
      obtain ⟨g, hg⟩ := tauEmb_ringHom D lm τ
      rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      have key : ∑ i : Fin n, ∑ j : Fin m, c * r i * r' j * tauEmb D lm τ ((aa i • A j) k1 k2)
          = c * ((∑ i, r i * tauEmb D lm τ (aa i)) * (∑ j, r' j * tauEmb D lm τ (A j k1 k2))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg, Matrix.smul_apply, smul_eq_mul, map_mul]
        ring
      rw [key, hsum τ]
      split_ifs with h1 h2 h2
      · subst h2
        rw [← hAsum k1 k2, hc, ← mul_assoc, div_mul_cancel₀ _ h0, mul_assoc]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
end GlobalTheory.Proof.integral_jets_realPlace_local_bases
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBasesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_jets_realPlace_local_bases : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  first | exact @GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | exact GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | (intros; apply GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJets
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJets
open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJetsStatement
open Formalism.MainNotions Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kvalGe_zero_of_integral_jets : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]), Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  first | exact @GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | exact GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | (intros; apply GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.AdmEntInt

theorem mod_three_eq_two_of_jacobiSym_neg_eq_one (d : ℕ) (h : jacobiSym (-(d : ℤ)) 3 = 1) : d % 3 = 2 := by
  rw [jacobiSym.mod_left] at h
  simp only [Nat.cast_ofNat] at h
  have : (-(d : ℤ)) % 3 = 0 ∨ (-(d : ℤ)) % 3 = 1 ∨ (-(d : ℤ)) % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at h
  · norm_num at h
  · omega
  · norm_num at h

end GlobalTheory.Ggeo.AdmEntInt

theorem GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hHyp h3 ep be sg
  intro u μ w hlf hd i hi _heven c c'
  have hlf' : LevFree Y u μ w := hlf
  obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hHyp u μ w hlf' i hi c c'
  have hd3 : D.what₂.places.resChar w = 3 → D.host.d % 3 = 2 := fun _ =>
    GlobalTheory.Ggeo.AdmEntInt.mod_three_eq_two_of_jacobiSym_neg_eq_one _ (D.host.split_small 3 Nat.prime_three (by norm_num) h3)
  have hJ := GlobalTheory.T.integralJets_normalisedThetaCombinations_away_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hAdm
    (D.what₂.places.resChar w) (t.ent.lam w) hd hd3 _ hComb
  let T := t.kf u μ w hlf'
  have hB := T.B_bas i hi.le c
  have hB' := T.B_bas (i + 1) hi c'
  have hK := GlobalTheory.T.integral_jets_realPlace_local_bases D (t.O u μ).dgen (t.O u μ).dgen_gen _ _ _ _ hAdm (D.what₂.places.resChar w) (t.ent.lam w)
    (T.B i c) (T.B (i + 1) c') (fun τ => T.c0 i c c' τ * TaylorLogMetric.lamC (t.ent.lam w) ((t.O u μ).dgen τ)) hB hB'
    (fun τ => by rw [norm_mul, T.unitAbs_eq_one, one_mul]) _ hJ
  rw [← T.th i hi c c'] at hK
  exact GlobalTheory.T.kvalGe_zero_of_integral_jets _ _ _ _ _ _ hK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromDStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | exact GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | (intros; apply GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d <;> assumption)
end
