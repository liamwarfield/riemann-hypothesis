module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GramXDiag

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_realPar_ne (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l ∧ ∀ τ, l τ ≠ 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  have hy0 : y ≠ 0 := by
    rw [hy_def]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 ha0
  refine ⟨fun τ => -(tauE D τ y).re, ?_, fun τ => ?_⟩
  · intro x
    have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
      simp only [psiInf]
      rw [ha]
      congr 1
      show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
      rw [mul_zero]; rfl
    rw [e1, h₀.2.2 θ hθ]
    congr 1
    have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
      intro ρ
      have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
          ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
      rw [e3, map_mul, (hθ ρ).1]
    simp only [e2]
    have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
      intro ρ
      apply Complex.ext <;> simp [hreal ρ]
    simp only [e4, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  · intro h
    have h1 : tauE D τ y ≠ 0 := (map_ne_zero_iff _ (tauE D τ).injective).2 hy0
    apply h1
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith
    · simp [hreal τ]

theorem cx_lne {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → NNReal}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)} {τ : D.what₂.Tau}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : PositivityTheory.Rg.Sw.GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) : ∀ τ', l τ' ≠ 0 := by
  obtain ⟨l', hl', hne⟩ := exists_realPar_ne D ψ hC.hψ θ hC.hθ
  rw [GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hC.hθ l l' hC.hl hl']
  exact hne

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

open LocLawH in
theorem lIl : LIl := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨l', hl', hne⟩ := exists_realPar_ne D ψ hC.hψ θ hC.hθ
  rw [GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hC.hθ l l' hC.hl hl']
  exact hne τ

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob


set_option synthInstance.maxHeartbeats 400000 in
theorem realPar_explicit (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ a : D.host.F, a ≠ 0 ∧
      HasRealPar ψ θ (fun τ => -(tauE D τ (algebraMap D.host.F D.host.E a)).re) ∧
      ∀ τ, (tauE D τ (algebraMap D.host.F D.host.E a)).im = 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨a, ha0, ?_, hreal⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e5 : ∀ ρ, (((tauE D ρ (algebraMap D.host.F D.host.E a)).re : ℝ) : ℂ) = tauE D ρ y := by
    intro ρ
    have h := hreal ρ
    rw [hy_def] at h ⊢
    apply Complex.ext
    · simp
    · simp [h]
  simp only [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [e5 ρ]
  ring

theorem lNZ : LNZ := by
  intro D ψ θ l hψ hθ hl τ
  obtain ⟨a, ha0, hl0, hre⟩ := realPar_explicit D ψ hψ θ hθ
  have e : l = _ := GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl0
  rw [e]
  intro h0
  apply ha0
  have h1 : tauE D τ (algebraMap D.host.F D.host.E a) = 0 := by
    apply Complex.ext
    · simpa using h0
    · simpa using hre τ
  have h2 : algebraMap D.host.F D.host.E a = 0 := (map_eq_zero _).1 h1
  exact (map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h2

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DSiegH

variable {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem cross_form_linear_fractional_eq_conjTranspose_sub (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) = Wᴴ - W := by
  have e : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) =
      Wᴴ * (Aᴴ * C - Cᴴ * A) * W + Wᴴ * (Aᴴ * D - Cᴴ * B) + (Bᴴ * C - Dᴴ * A) * W + (Bᴴ * D - Dᴴ * B) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [e, sub_eq_zero.2 h1, h3, h4, sub_eq_zero.2 h2]
  noncomm_ring

theorem det_ne (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : ∀ v : Fin n → ℂ, v ≠ 0 → star v ⬝ᵥ ((Wᴴ - W) *ᵥ v) ≠ 0) :
    (C * W + D).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have key := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => star v ⬝ᵥ (M *ᵥ v)) (cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_zero, zero_sub, dotProduct_neg] at key
  have e : star v ⬝ᵥ ((C * W + D)ᴴ *ᵥ ((A * W + B) *ᵥ v)) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hQv, star_zero, zero_dotProduct]
  rw [e, neg_zero] at key
  exact hW v hv (by rw [Matrix.sub_mulVec] at *; simpa [dotProduct_sub] using key.symm)

theorem im_formula (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) :
    (A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ =
      ((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹ := by
  set P := A * W + B
  set Q := C * W + D
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQh : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQQ, conjTranspose_one]
  have hc : Pᴴ * Q - Qᴴ * P = Wᴴ - W := cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W
  have e1 : P * Q⁻¹ = (Q⁻¹)ᴴ * (Qᴴ * P) * Q⁻¹ := by rw [← Matrix.mul_assoc, hQh, Matrix.one_mul]
  have e2 : (P * Q⁻¹)ᴴ = (Q⁻¹)ᴴ * (Pᴴ * Q) * Q⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [e2, e1, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  have : Qᴴ * P - Pᴴ * Q = -(Pᴴ * Q - Qᴴ * P) := by abel
  rw [this, hc]
  abel

theorem siegel_of (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) (a : ℂ)
    (hW : (a • (W - Wᴴ)).PosDef) :
    (a • ((A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ)).PosDef := by
  rw [im_formula h1 h2 h3 h4 W hQ]
  have e : a • (((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹) =
      ((C * W + D)⁻¹)ᴴ * (a • (W - Wᴴ)) * (C * W + D)⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact hW.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hQ)))

theorem posDef_diag_re (w : Fin n → ℂ) (hw : ∀ j, 0 < (w j).re) (a : ℂ)
    (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) (hsa : a * s * 2 = 1) :
    (a • (s • diagonal w - (s • diagonal w)ᴴ)).PosDef := by
  have e : a • (s • diagonal w - (s • diagonal w)ᴴ) = diagonal fun j => ((w j).re : ℂ) := by
    rw [conjTranspose_smul, diagonal_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hst : star s = -s := by
        rcases hs with rfl | rfl <;> simp [Complex.conj_I]
      simp only [Matrix.smul_apply, Matrix.sub_apply, diagonal_apply_eq, smul_eq_mul, hst, Pi.star_apply]
      have hw' : (w i : ℂ) + star (w i) = 2 * ((w i).re : ℂ) := by
        rw [Complex.star_def, Complex.add_conj]; push_cast; ring
      calc a * (s * w i - -s * star (w i)) = a * s * ((w i : ℂ) + star (w i)) := by ring
        _ = a * s * (2 * ((w i).re : ℂ)) := by rw [hw']
        _ = ((w i).re : ℂ) := by linear_combination ((w i).re : ℂ) * hsa
    · simp [hij]
  rw [e, Matrix.posDef_diagonal_iff]
  intro j
  exact_mod_cast hw j

theorem det_ne_of_posDef (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1)
    (h4 : Bᴴ * C - Dᴴ * A = -1) (W : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (ha : a ≠ 0) (hX : (a • (W - Wᴴ)).PosDef) :
    (C * W + D).det ≠ 0 := by
  refine det_ne h1 h2 h3 h4 W fun v hv => ?_
  have e : Wᴴ - W = (-a⁻¹) • (a • (W - Wᴴ)) := by
    rw [smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_one_smul, neg_sub]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero ha)) (hX.dotProduct_mulVec_pos hv).ne'

end DSiegH

open DRealH DSiegH in
theorem dSieg : DSieg := by
  intro n y X z hz
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG (g := mR y) y.2
  set A := (mR y).toBlocks₁₁ with hA
  set B := (mR y).toBlocks₁₂ with hB
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  set w : Fin n → ℂ := fun j => Complex.exp (2 * z * X j) with hwdef
  set E : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (z * X j) with hE
  set F : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (-(z * X j)) with hF
  have hwre : ∀ j, 0 < (w j).re := by
    intro j
    simp only [hwdef, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    all_goals
      have hj := hz j
      have him : (2 * z * (X j : ℂ)).im = 2 * (z.im * X j) := by simp [Complex.mul_im]; ring
      rw [him]
      rw [abs_lt] at hj
      linarith [hj.1, hj.2]
  have hM : mR y * aC X z = fromBlocks (A * E) (B * F) (C * E) (D * F) := by
    have e : mR y = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    rw [e]
    unfold aC
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, hE, hF]
  have hFu : IsUnit F.det := by
    rw [hF, det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => Complex.exp_ne_zero _)
  have hFF : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hFu
  have hWF : ∀ s : ℂ, E * (s • 1) = (s • diagonal w) * F := by
    intro s
    rw [hE, hF, Matrix.smul_mul, diagonal_mul_diagonal, Matrix.mul_smul, Matrix.mul_one]
    congr 1
    congr 1
    funext j
    rw [hwdef, ← Complex.exp_add]
    congr 1; ring
  have hblk : ∀ s : ℂ, ((mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) = (C * (s • diagonal w) + D) * F ∧
      ((mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) = (A * (s • diagonal w) + B) * F := by
    intro s
    rw [hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    constructor
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
  have hpt : ∀ s : ℂ, ptZ y X z s = (A * (s • diagonal w) + B) * (C * (s • diagonal w) + D)⁻¹ := by
    intro s
    simp only [ptZ]
    rw [(hblk s).1, (hblk s).2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFF, Matrix.mul_one]
  have hI2 : -(Complex.I / 2) ≠ 0 := by simp [Complex.I_ne_zero]
  have hI2' : Complex.I / 2 ≠ 0 := by simp [Complex.I_ne_zero]
  have hX1 : ((-(Complex.I / 2)) • ((Complex.I • diagonal w) - (Complex.I • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ Complex.I (Or.inl rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hX2 : ((Complex.I / 2) • (((-Complex.I) • diagonal w) - ((-Complex.I) • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ (-Complex.I) (Or.inr rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hQ1 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2 hX1
  have hQ2 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2' hX2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold IsSiegel
    rw [hpt]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ1) _ hX1
  · unfold IsSiegel
    rw [hpt, conjTranspose_conjTranspose]
    have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, (-(Complex.I / 2)) • (Zᴴ - Z) = (Complex.I / 2) • (Z - Zᴴ) := by
      intro Z; rw [← neg_sub, smul_neg, neg_smul, neg_neg]
    rw [e]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ2) _ hX2
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ1 (isUnit_iff_ne_zero.1 hFu)
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ2 (isUnit_iff_ne_zero.1 hFu)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere
namespace UpperTheory.Reformulated.B.P6.r24a

theorem quadratic_form_smul_re {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
  ring

theorem inv_norm_smul_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

theorem PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos :
    ∀ {V : Type} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ), (∀ (x : V), x ≠ OfNat.ofNat (nat_lit 0) → OfNat.ofNat (nat_lit 0) < (DFunLike.coe (DFunLike.coe Q x) x).re) → ∃ (κ : ℝ), OfNat.ofNat (nat_lit 0) < κ ∧ ∀ (x : V), κ * ‖x‖ ^ OfNat.ofNat (nat_lit 2) ≤ (DFunLike.coe (DFunLike.coe Q x) x).re := by
  intro V _ _ _ Q hQ
  have hcont : Continuous fun x : V => (Q x x).re :=
    Complex.continuous_re.comp (Q.continuous.clm_apply continuous_id)
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(Q x0 x0).re, hQ x0 hx0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨y, hyd⟩ : ∃ y : V, y = ‖x‖⁻¹ • x := ⟨_, rfl⟩
      have hy : y ∈ Metric.sphere (0 : V) 1 := hyd ▸ inv_norm_smul_mem_sphere x hx
      have h1 : (Q x0 x0).re ≤ (Q y y).re := hmin hy
      have h2 : ‖x‖ • y = x := by
        rw [hyd, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h3 : (Q x x).re = ‖x‖ ^ 2 * (Q y y).re := by
        have := quadratic_form_smul_re Q ‖x‖ y
        rw [h2] at this
        exact this
      rw [h3, mul_comm (‖x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨_, inv_norm_smul_mem_sphere x hx⟩
    subst hx
    simp

end UpperTheory.Reformulated.B.P6.r24a
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

theorem trace_gramB (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a) ⬝ᵥ (Zᵀ *ᵥ u a) := by
  set S := Finset.univ.filter (fun a => ε a = b)
  have hG : ∀ i j, gramB ε b u j i = ∑ a ∈ S, star (u a j) * u a i := fun i j => GaussH.gramB_apply ε b u j i
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.mul_sum, dotProduct, mulVec,
    Matrix.transpose_apply, Pi.star_apply]
  calc _ = ∑ i, ∑ a ∈ S, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ i, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ j, ∑ i, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem im_quad (W : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (W *ᵥ y)).im = (star y ⬝ᵥ (((-(Complex.I / 2)) • (W - Wᴴ)) *ᵥ y)).re := by
  have hs : star (star y ⬝ᵥ (W *ᵥ y)) = star y ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, ← hs]
  set s := star y ⬝ᵥ (W *ᵥ y)
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

theorem coercive_of_pos {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (h : ∀ x, x ≠ 0 → 0 < (Q x x).re) : ∃ κ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ (Q x x).re :=
  _root_.UpperTheory.Reformulated.B.P6.r24a.PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos Q h

end PositivityTheory.Rg.Sw.Glob.GCSchH
end
end

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

def qF (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  -(Complex.I * c * ∑ a ∈ S, star (u a) ⬝ᵥ (Zᵀ *ᵥ v a) - Complex.I * c * ∑ a ∈ S', star (u a) ⬝ᵥ (Z'ᵀ *ᵥ v a))

def qL (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (qF S S' c Z Z')
    (fun u₁ u₂ v => by
      simp only [qF, Pi.add_apply, star_add, add_dotProduct, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, Complex.real_smul, ← Finset.mul_sum]
      ring)
    (fun u v₁ v₂ => by
      simp only [qF, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, ← Finset.mul_sum]
      ring)

def qB (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ qL S S' c Z Z')

theorem qB_apply (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) :
    qB S S' c Z Z' u v = qF S S' c Z Z' u v := rfl

theorem re_I_mul (c : ℝ) (z : ℂ) : (Complex.I * c * z).re = -(c * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem quad_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) (y : Fin n → ℂ) : 0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

theorem quad_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) {y : Fin n → ℂ} (hy : y ≠ 0) :
    0 < (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.pos_iff.mp (hP.dotProduct_mulVec_pos hy)).1

end PositivityTheory.Rg.Sw.Glob.GCSchH
end
end

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GCSchH

theorem gCSch : GCSch := by
  intro m n ε t c hc htc Z Z' hZ hZ'
  set S := Finset.univ.filter (fun a => epsT t ε a = true) with hS
  set S' := Finset.univ.filter (fun a => epsT t ε a = false) with hS'
  set B := qB S S' c Z Z' with hB
  have hgC : gC ε t c Z Z' = fun u => Complex.exp (-(B u u)) := by
    funext u
    simp only [gC, hB, qB_apply, qF, neg_neg, trace_gramB]
    rfl
  have hP1 : ((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)).PosDef := by
    have h := hZ.transpose
    rwa [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose] at h
  have hP2 : ((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)).PosDef := by
    have h := hZ'.transpose
    unfold IsSiegel at h
    rw [Matrix.conjTranspose_conjTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.conjTranspose_transpose] at h
    rwa [Matrix.conjTranspose_neg, sub_neg_eq_add, neg_add_eq_sub]
  have hre : ∀ u : Fin m → Fin n → ℂ, (B u u).re = c * (∑ a ∈ S, (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re + ∑ a ∈ S', (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re) := by
    intro u
    rw [hB, qB_apply, qF, Complex.neg_re, Complex.sub_re, re_I_mul, re_I_mul, Complex.im_sum, Complex.im_sum]
    have e2 : ∀ a, (star (u a) ⬝ᵥ (Z'ᵀ *ᵥ u a)).im = -(star (u a) ⬝ᵥ ((-Z'ᵀ) *ᵥ u a)).im := by
      intro a; rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im, neg_neg]
    simp only [e2, Finset.sum_neg_distrib, im_quad]
    ring
  have hpos : ∀ u : Fin m → Fin n → ℂ, u ≠ 0 → 0 < (B u u).re := by
    intro u hu
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
    rw [hre]
    apply mul_pos hc
    have n1 : 0 ≤ ∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP1 _
    have n2 : 0 ≤ ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP2 _
    cases hb : epsT t ε a
    · have haS : a ∈ S' := by simp [hS', hb]
      have p2 := Finset.sum_pos' (fun a _ => quad_nonneg hP2 (u a)) ⟨a, haS, quad_pos hP2 ha⟩
      linarith
    · have haS : a ∈ S := by simp [hS, hb]
      have p1 := Finset.sum_pos' (fun a _ => quad_nonneg hP1 (u a)) ⟨a, haS, quad_pos hP1 ha⟩
      linarith
  obtain ⟨κ, hκ, hco⟩ := coercive_of_pos B hpos
  obtain ⟨g, hg, -⟩ := GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form _ B κ hκ hco
  refine ⟨g, ?_⟩
  rw [hgC]
  funext u
  exact hg u

theorem gZSch : GZSch := by
  intro m n ε t c hc htc Z hZ
  show IsSch (gC ε t c Z Zᴴ)
  exact gCSch m n ε t c hc htc Z Zᴴ hZ (by rw [Matrix.conjTranspose_conjTranspose]; exact hZ)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRConjTranspose
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB

variable {n : ℕ}

def dR (β : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (β j : ℂ)

theorem dR_conjTranspose (β : Fin n → ℝ) : (dR β)ᴴ = dR β := by
  simp [dR, Matrix.diagonal_conjTranspose]

theorem dR_mul (β β' : Fin n → ℝ) : dR β * dR β' = dR (fun j => β j * β' j) := by
  simp [dR, Matrix.diagonal_mul_diagonal]

theorem dR_add (β β' : Fin n → ℝ) : dR β + dR β' = dR (fun j => β j + β' j) := by
  simp [dR, Matrix.diagonal_add]

theorem dR_neg (β : Fin n → ℝ) : -dR β = dR (fun j => -β j) := by
  simp [dR, Matrix.diagonal_neg]

theorem dR_one : dR (fun _ : Fin n => (1 : ℝ)) = 1 := by
  simp [dR]

theorem dR_inv (β : Fin n → ℝ) (hβ : ∀ j, β j ≠ 0) : (dR β)⁻¹ = dR (fun j => (β j)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [dR_mul]
  rw [← dR_one]
  congr 1
  funext j
  exact inv_mul_cancel₀ (hβ j)

theorem kth_eq (θ : Fin n → ℝ) : kth θ = fromBlocks (dR fun j => Real.cos (θ j)) (dR fun j => Real.sin (θ j))
    (-dR fun j => Real.sin (θ j)) (dR fun j => Real.cos (θ j)) := rfl

theorem kth_decomp (θ : Fin n → ℝ) (hc : ∀ j, Real.cos (θ j) ≠ 0) :
    kth θ = nU (dR fun j => Real.tan (θ j)) * nbar (dR fun j => -(Real.sin (θ j) * Real.cos (θ j))) *
      mM (dR fun j => (Real.cos (θ j))⁻¹) := by
  have hinv : ((dR fun j => (Real.cos (θ j))⁻¹)ᴴ)⁻¹ = dR fun j => Real.cos (θ j) := by
    rw [dR_conjTranspose, dR_inv _ (fun j => inv_ne_zero (hc j))]
    simp only [inv_inv]
  rw [kth_eq]
  simp only [nU, nbar, mM, hinv, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.add_mul, dR_mul]
  rw [dR_add, dR_neg]
  congr 1
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq (θ j))
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  · congr 1
    funext j
    have h1 := hc j
    field_simp

theorem kth_half (θ : Fin n → ℝ) : kth θ = kth (fun j => θ j / 2) * kth (fun j => θ j / 2) := by
  have hc : ∀ j, Real.cos (θ j) = Real.cos (θ j / 2) * Real.cos (θ j / 2) -
      Real.sin (θ j / 2) * Real.sin (θ j / 2) := by
    intro j
    have := Real.cos_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    linear_combination Real.sin_sq_add_cos_sq (θ j / 2)
  have hs : ∀ j, Real.sin (θ j) = Real.cos (θ j / 2) * Real.sin (θ j / 2) +
      Real.sin (θ j / 2) * Real.cos (θ j / 2) := by
    intro j
    have := Real.sin_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    ring
  rw [kth_eq, kth_eq, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_neg, Matrix.neg_mul, dR_mul, dR_neg, dR_add]
  congr 1
  · congr 1
    funext j
    rw [hc j]
    ring
  · congr 1
    funext j
    rw [hs j]
  · congr 1
    funext j
    rw [hs j]
    ring
  · congr 1
    funext j
    rw [hc j]
    ring

end PositivityTheory.Rg.Sw.Glob.VacD
end
end
