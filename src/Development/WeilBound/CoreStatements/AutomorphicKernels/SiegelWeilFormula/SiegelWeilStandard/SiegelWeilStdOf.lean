module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.SiegelWeilStdLeaves
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.TThetaSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.TthetaComm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaAutoAt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.UnfoldOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SubMulRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaLine
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwayActOfTAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpExOfTAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.UnrWhitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaInvPoOfOneLt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.CpowProdOfReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.FactorCore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerLowRank.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GenDictXOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ProjectedBlockUpperSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.CongUnip
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.NdZero
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Imports
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrime
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ZOfSurjBdd
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.BaseOneOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.ChapterTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaTop

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousQuad
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def imM (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Z - Zᴴ)

theorem star_c : star (-(Complex.I / 2)) = -(-(Complex.I / 2)) := by
  apply Complex.ext <;> simp <;> norm_num

theorem imM_herm (Z : Matrix (Fin n) (Fin n) ℂ) : (imM Z).IsHermitian := by
  unfold imM
  rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, star_c, neg_smul,
    ← smul_neg, neg_sub]

theorem mem_dom_iff (Z : Fin n → Fin n → ℂ) : Z ∈ Dom n ↔ (imM (Matrix.of Z)).PosDef := Iff.rfl

theorem posdef_iff_re {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M.PosDef ↔ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x hx
    exact (Complex.lt_def.1 (h hx)).1
  · intro h
    refine ⟨hM, fun x hx => ?_⟩
    have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := hM.im_star_dotProduct_mulVec_self x
    exact Complex.lt_def.2 ⟨h x hx, by simpa using him.symm⟩

theorem re_smul_quad (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (c : ℝ) :
    (star ((c : ℂ) • x) ⬝ᵥ (M *ᵥ ((c : ℂ) • x))).re = c ^ 2 * (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem continuous_quad : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) =>
    (star p.2 ⬝ᵥ (imM (Matrix.of p.1) *ᵥ p.2)).re := by
  have h1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_fst
  have h2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => imM (Matrix.of p.1) := by
    unfold imM
    exact (h1.sub h1.matrix_conjTranspose).const_smul (-(Complex.I / 2) : ℂ)
  exact Complex.continuous_re.comp (continuous_snd.star.dotProduct (h2.matrix_mulVec continuous_snd))

theorem isOpen_dom' : IsOpen (Dom n) := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  have hsph : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have key : ∀ᶠ W in 𝓝 Z, ∀ y ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star y ⬝ᵥ (imM (Matrix.of W) *ᵥ y)).re := by
    apply hsph.eventually_forall_of_forall_eventually
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hpos : 0 < (star y ⬝ᵥ (imM (Matrix.of Z) *ᵥ y)).re :=
      (posdef_iff_re (imM_herm _)).1 ((mem_dom_iff Z).1 hZ) y hy0
    exact (continuous_quad.tendsto (Z, y)).eventually (lt_mem_nhds hpos)
  filter_upwards [key] with W hW
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)]
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy : (((‖x‖⁻¹ : ℝ) : ℂ) • x) ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn.ne']
  have hxe : x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  rw [hxe, re_smul_quad]
  exact mul_pos (pow_pos hn 2) (hW _ hy)

theorem convex_dom' : Convex ℝ (Dom n) := by
  intro Z hZ W hW a b ha hb hab
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)] at hZ hW ⊢
  intro x hx
  have hm : imM (Matrix.of (a • Z + b • W)) = (a : ℂ) • imM (Matrix.of Z) + (b : ℂ) • imM (Matrix.of W) := by
    ext i j
    simp [imM, Complex.real_smul]
    ring
  have hq : (star x ⬝ᵥ (imM (Matrix.of (a • Z + b • W)) *ᵥ x)).re
      = a * (star x ⬝ᵥ (imM (Matrix.of Z) *ᵥ x)).re + b * (star x ⬝ᵥ (imM (Matrix.of W) *ᵥ x)).re := by
    rw [hm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  rw [hq]
  have hp := hZ x hx
  have hq' := hW x hx
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hq'
  · linarith [mul_pos ha' hp, mul_nonneg hb hq'.le]

private theorem conjTranspose_I_smul_add_sub_eq_neg_two_I (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (h1 : -(Cᴴ * A) + Aᴴ * C = 0) (h2 : -(Cᴴ * B) + Aᴴ * D = 1)
    (h3 : -(Dᴴ * A) + Bᴴ * C = -1) (h4 : -(Dᴴ * B) + Bᴴ * D = 0) :
    (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  linear_combination (norm := skip) h1 + h4 + (-Complex.I) • h2 + Complex.I • h3
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem posDef_imM_mul_inv_of_skew_relation (X U : Matrix (Fin n) (Fin n) ℂ)
    (hk : Xᴴ * U - Uᴴ * X = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (imM (X * U⁻¹)).PosDef := by
  have hker : ∀ v, U *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e : star v ⬝ᵥ ((Xᴴ * U - Uᴴ * X) *ᵥ v)
        = star v ⬝ᵥ (((-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) := by
      rw [hk]
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec, hv, star_zero, zero_dotProduct,
      neg_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at e
    have h2I : -(2 * Complex.I) ≠ 0 := by simp
    have hvv : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 e.symm).resolve_left h2I
    exact dotProduct_star_self_eq_zero.1 hvv
  have hinj : Function.Injective U.mulVec := by
    intro v w hvw
    have h0 : U *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact hvw
    exact sub_eq_zero.1 (hker _ h0)
  have hU : IsUnit U := mulVec_injective_iff_isUnit.1 hinj
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  have hc : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← conjTranspose_mul, hUU, conjTranspose_one]
  have e1 : X * U⁻¹ - (X * U⁻¹)ᴴ = (U⁻¹)ᴴ * (Uᴴ * X - Xᴴ * U) * U⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Uᴴ X, hc,
      Matrix.one_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Xᴴ U, Matrix.mul_assoc _ U U⁻¹, hUU, Matrix.mul_one]
  have e2 : Uᴴ * X - Xᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← neg_sub, hk, neg_smul, neg_neg]
  have e3 : imM (X * U⁻¹) = (U⁻¹)ᴴ * 1 * U⁻¹ := by
    unfold imM
    rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hs : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
      ring_nf
      simp [Complex.I_sq]
    rw [hs, one_smul]
  have hinv : Function.Injective (U⁻¹).mulVec := by
    intro v w hvw
    have := congrArg (fun z => U *ᵥ z) hvw
    simpa [Matrix.mulVec_mulVec, hUU] using this
  rw [e3]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinv

theorem zOf_mem' (y : GR n) : zOf y ∈ Dom n := by
  have hM : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hblk : mR y = fromBlocks (toBlocks₁₁ (mR y)) (toBlocks₁₂ (mR y)) (toBlocks₂₁ (mR y))
      (toBlocks₂₂ (mR y)) :=
    (fromBlocks_toBlocks _).symm
  rw [hblk, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at hM
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hM
  have hk := conjTranspose_I_smul_add_sub_eq_neg_two_I _ _ _ _ h1 h2 h3 h4
  refine (mem_dom_iff (n := n) (zOf y)).2 ?_
  exact posDef_imM_mul_inv_of_skew_relation _ _ hk

theorem neg_conj_mem' {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) :
    (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) ∈ Dom n := by
  have h : imM (Matrix.of (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)) = imM (Matrix.of W) := by
    change imM (-(Matrix.of W)ᴴ) = imM (Matrix.of W)
    ext i j
    simp [imM]
    ring
  refine (mem_dom_iff (n := n) (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)).2 ?_
  rw [h]
  exact (mem_dom_iff W).1 hW

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.RealLowOf
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem card_places (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) :
    Fintype.card ι = Module.finrank ℚ F := by
  classical
  haveI : IsTotallyReal F := hCM.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let eT := GlobalTheory.SiegelWeilConvCompare.tensHomeo (F := F) (E := E) (Ainf F) b
  let eR : Ainf F ≃ₜ (InfinitePlace F → ℝ) := Homeomorph.piCongrRight fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have hRadd : ∀ x y : InfinitePlace F → ℝ, eR.symm (x + y) = eR.symm x + eR.symm y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.map_add (x v) (y v)
  have hTadd : ∀ x y : Fin 2 → Ainf F, eT.symm (x + y) = eT.symm x + eT.symm y := by
    intro x y
    exact (Algebra.TensorProduct.basis (Ainf F) b).equivFun.symm.map_add x y
  let f : (Fin 2 → InfinitePlace F → ℝ) → (ι → ℂ) := fun x i => θ i (eT.symm (fun k => eR.symm (x k)))
  have hfadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y; funext i
    simp only [f, Pi.add_apply]
    rw [show (fun k => eR.symm (x k + y k)) = (fun k => eR.symm (x k)) + (fun k => eR.symm (y k)) from
      funext fun k => hRadd (x k) (y k), hTadd, map_add]
  let fA : (Fin 2 → InfinitePlace F → ℝ) →+ (ι → ℂ) :=
    { toFun := f
      map_zero' := by
        have h0 := hfadd 0 0
        rw [add_zero] at h0
        exact (add_eq_left.1 h0.symm)
      map_add' := hfadd }
  have hfc : Continuous fA := continuous_pi fun i => (hP.cont i).comp
    (eT.symm.continuous.comp (continuous_pi fun k => eR.symm.continuous.comp (continuous_apply k)))
  let L := fA.toRealLinearMap hfc
  have hbij : Function.Bijective L := by
    have h1 : Function.Bijective (fun x : Fin 2 → InfinitePlace F → ℝ => fun k => eR.symm (x k)) :=
      (Equiv.piCongrRight fun _ => eR.symm.toEquiv).bijective
    exact hP.bij.comp (eT.symm.bijective.comp h1)
  have hr := (LinearEquiv.ofBijective (L : (Fin 2 → InfinitePlace F → ℝ) →ₗ[ℝ] (ι → ℂ)) hbij).finrank_eq
  simp only [Module.finrank_pi, Module.finrank_fin_fun, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self] at hr
  have hc : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      add_zero, IsTotallyReal.finrank]
  omega

theorem realLow_of (h : WROrd) : RealLow := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hMn ψ hψ ι _ θ l hP e fr hfr g μ ν hμ hν T hT
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  obtain ⟨eC, heC⟩ := exists_crdHomeo σ hCM ψ θ l hP fr g
  obtain ⟨eb, heb⟩ := exists_ybHomeo σ hCM ψ θ l hP g
  haveI := haar_volE ι n
  haveI := haar_volW ι M n
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨cμ, -, hcμ⟩ := exists_map_eq_smul (volume : Measure (ι → Fin M → Fin n → ℂ)) μ eC
  obtain ⟨cb, -, hcb⟩ := exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eb
  have hl : ∀ i, l i ≠ 0 := hP.ne
  have hβ : ∀ i, (herm (ygAll σ θ g T i)).det ≠ 0 := det_herm_ygAll σ hCM ψ θ l hP g T hT
  have hw : ∀ i, ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
      Integrable (fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z) ∧
      z ^ (n - M) * W z = ∫ y, fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z y := by
    intro i
    have hc : 0 < 2 * Real.pi * |l i| := by have := abs_pos.2 (hl i); positivity
    have ht : 2 * Real.pi * l i = 2 * Real.pi * |l i| ∨ 2 * Real.pi * l i = -(2 * Real.pi * |l i|) := by
      rcases le_or_gt 0 (l i) with h | h
      · left; rw [abs_of_nonneg h]
      · right; rw [abs_of_neg h]; ring
    exact h M n hMn (e i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) hc ht (ygAll σ θ g T i) (hβ i)
  choose Wi hWid hrest using hw
  choose σ₀ hσ₀ using hrest
  set s0 : ℂ := ((M : ℂ) - n) / 2 with hs0
  refine ⟨fun z => (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0), ?_, ((M : ℝ) - n) / 2 + ∑ i, |σ₀ i|,
    fun z hz => ?_⟩
  · refine (differentiable_const _).mul ?_
    have := Differentiable.finsetProd (u := Finset.univ) (f := fun i z => Wi i (z - s0))
      (fun i _ => (hWid i).comp (differentiable_id.sub_const s0))
    rw [Finset.prod_fn] at this
    exact this
  · have hzi : ∀ i, σ₀ i < (z - s0).re := by
      intro i
      have h1 : (z - s0).re = z.re - ((M : ℝ) - n) / 2 := by
        rw [hs0]; simp
      have h2 : σ₀ i ≤ ∑ j, |σ₀ j| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₀ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i))
      rw [h1]; linarith
    have hint : ∀ i, Integrable (fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i)
        (ygAll σ θ g T i) (z - s0)) := fun i => (hσ₀ i _ (hzi i)).1
    obtain ⟨h1, h2⟩ := integral_whI σ hCM ψ θ l hP J (fun i _ => e i) fr hfr g (fun _ => 1) μ eC heC cμ hcμ ν eb heb
      cb hcb T z hint
    refine ⟨h1, ?_⟩
    rw [← hs0] at h2
    rw [h2]
    have h3 : ∀ i, ∫ y, fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i)
        (ygAll σ θ g T i) (z - s0) y = (z - s0) ^ (n - M) * Wi i (z - s0) := fun i => ((hσ₀ i _ (hzi i)).2).symm
    simp only [h3]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places σ hCM ψ θ l hP, ← pow_mul,
      mul_comm (n - M)]
    ring

end PositivityTheory.SiegelWeilFormula.GReal
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.HolomorphicAverageUniform
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicTranslationLevi
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

abbrev EE (n : ℕ) := Fin n → Fin n → ℂ

theorem herm_re (v : EE n) : (Matrix.of ((1 / 2 : ℂ) • (v + fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  ring

theorem herm_im (v : EE n) :
    (Matrix.of ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  field_simp
  ring

theorem split_re_im (v : EE n) :
    v = (1 / 2 : ℂ) • (v + fun i j => star (v j i)) + Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i))) := by
  funext i j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

private theorem herm_Hpk_smul_left (k : EE n) (hk : (Matrix.of k).IsHermitian) (t : ℝ) :
    (Matrix.of ((t : ℂ) • k)).IsHermitian := by
  ext i j
  have h2 := congrFun (congrFun hk i) j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply] at h2 ⊢
  simp [h2]

theorem const_of_transl (G : EE n → ℂ) (hG : DifferentiableOn ℂ G (Dom n))
    (hT : ∀ W ∈ Dom n, ∀ k : EE n, (Matrix.of k).IsHermitian → G (W + k) = G W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n, G W = G W' := by
  have key : ∀ W ∈ Dom n, fderiv ℂ G W = 0 := by
    intro W hW
    have hGd : HasFDerivAt G (fderiv ℂ G W) W :=
      ((hG W hW).differentiableAt (isOpen_dom'.mem_nhds hW)).hasFDerivAt
    have hk0 : ∀ k : EE n, (Matrix.of k).IsHermitian → fderiv ℂ G W k = 0 := by
      intro k hk
      have hc : HasDerivAt (fun t : ℝ => W + (t : ℂ) • k) k 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const k).const_add W
        simpa using h1
      have hcomp := (hGd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
      have hfun : (G ∘ fun t : ℝ => W + (t : ℂ) • k) = fun _ => G W := by
        funext t
        exact hT W hW _ (herm_Hpk_smul_left k hk t)
      rw [hfun] at hcomp
      simpa using hcomp.unique (hasDerivAt_const _ _)
    refine ContinuousLinearMap.ext fun v => ?_
    calc fderiv ℂ G W v = fderiv ℂ G W ((1 / 2 : ℂ) • (v + fun i j => star (v j i)) +
          Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))) := by
          rw [← split_re_im v]
      _ = 0 := by
          rw [map_add (f := _), hk0 _ (herm_re v), map_smul, hk0 _ (herm_im v)]
          simp
  intro W hW W' hW'
  exact convex_dom'.is_const_of_fderivWithin_eq_zero hG
    (fun x hx => by rw [fderivWithin_of_isOpen isOpen_dom' hx]; exact key x hx) hW hW'

private theorem exp_trace_mul_H_const_on_dom (H : EE n → ℂ) (hH : DifferentiableOn ℂ H (Dom n))
    (β : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c * c = 1) (hcs : star c = c)
    (hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n,
      Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W =
        Complex.exp (-(c * Complex.I * (β * Matrix.of W').trace)) * H W' := by
  apply const_of_transl (fun W => Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W)
  · refine DifferentiableOn.mul ?_ hH
    apply Differentiable.differentiableOn
    have hl : Differentiable ℂ (fun W : EE n => (β * Matrix.of W).trace) := by
      simp only [Matrix.trace, Matrix.mul_apply, Matrix.of_apply, Matrix.diag]
      fun_prop
    fun_prop
  · intro W hW k hk
    have hof : Matrix.of (c • k) = c • Matrix.of k := rfl
    have hh : (Matrix.of (c • k)).IsHermitian := by
      rw [hof, Matrix.IsHermitian, Matrix.conjTranspose_smul, hcs, hk.eq]
    have hWk : W + k = W + c • (c • k) := by
      ext i j
      simp [smul_smul, hc]
    have htr : (β * Matrix.of (W + k)).trace = (β * Matrix.of W).trace + (β * Matrix.of k).trace := by
      rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.trace_add]
    have htr2 : (β * Matrix.of (c • k)).trace = c * (β * Matrix.of k).trace := by
      rw [hof, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hHk : H (W + k) = Complex.exp (Complex.I * (c * (β * Matrix.of k).trace)) * H W := by
      rw [hWk, hT W hW _ hh, htr2]
    try dsimp only
    rw [hHk, htr, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring

theorem holomorphic_translation_levi : ∀ (n p q : ℕ) (e : ℤ) (φ : GR n → ℂ), IsHolW p q e φ → ∀ β : Matrix (Fin n) (Fin n) ℂ,
    (∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      φ (x * y) = Complex.exp (Complex.I * (β * h).trace) * φ y) →
    ∀ (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), mR x = Matrix.fromBlocks a 0 0 a' → aᴴ * β * a = β →
      φ (x * y) = F0 p q e x * φ y := by
  intro n p q e φ hφ β hβ a a' x y hx ha
  obtain ⟨H, hH, hφH⟩ := hφ
  obtain ⟨Z, hZ⟩ : ∃ Z : GR n → Matrix (Fin n) (Fin n) ℂ,
      ∀ y, Z y = if q = 0 then zOf y else -(zOf y)ᴴ := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = if q = 0 then 1 else -1 := ⟨_, rfl⟩
  have hφ' : ∀ y, φ y = F0 p q e y * H (Z y) := fun y => by rw [hZ]; exact hφH y
  have hdom : ∀ y : GR n, Z y ∈ Dom n := by
    intro y
    rw [hZ]
    split_ifs
    · exact zOf_mem' y
    · exact neg_conj_mem' (zOf_mem' y)
  have hsurj : ∀ W ∈ Dom n, ∃ y : GR n, Z y = W := by
    intro W hW
    simp only [hZ]
    split_ifs
    · exact zOf_surj' hW
    · obtain ⟨y, hy⟩ := zOf_surj' (neg_conj_mem' hW)
      refine ⟨y, ?_⟩
      rw [hy]
      simp only [Matrix.conjTranspose_neg, neg_neg, Matrix.conjTranspose_conjTranspose]
      rfl
  have hnU : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      Z (x * y) = Z y + c • h := by
    intro h x y hh hx
    rw [hZ, hZ, hc, zOf_nU' h x y hx]
    split_ifs
    · simp
    · rw [Matrix.conjTranspose_add, hh.eq]
      simp
      abel
  have hlevi : ∀ y : GR n, Z (x * y) = a * Z y * aᴴ := by
    intro y
    rw [hZ, hZ, zOf_levi' a a' x y hx]
    split_ifs
    · rfl
    · simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W := by
    intro W hW h hh
    obtain ⟨y0, hy0⟩ := hsurj W hW
    obtain ⟨x0, hx0⟩ := nU_mem' hh
    have h1 := hβ _ x0 y0 hh hx0
    rw [hφ', hφ', spherical_section_unipotent_invariant p q e _ x0 y0 hx0, hnU _ x0 y0 hh hx0] at h1
    have e0 : (W + c • h : EE n) = Z y0 + c • Matrix.of h := by
      rw [hy0]
      rfl
    rw [e0]
    apply mul_left_cancel₀ (spherical_section_ne_zero_group p q e y0)
    rw [h1, hy0]
    ring
  have hc2 : c * c = 1 := by
    rw [hc]
    split_ifs <;> norm_num
  have hcs : star c = c := by
    rw [hc]
    split_ifs <;> simp
  have hconst := exp_trace_mul_H_const_on_dom H hH β c hc2 hcs hT
  have htr : (β * (a * Z y * aᴴ)).trace = (β * Z y).trace := by
    rw [show β * (a * Z y * aᴴ) = (β * a * Z y) * aᴴ by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show aᴴ * (β * a * Z y) = (aᴴ * β * a) * Z y by simp [Matrix.mul_assoc], ha]
  have hHeq : H (a * Z y * aᴴ) = H (Z y) := by
    have h1 := hconst _ (hlevi y ▸ hdom (x * y)) _ (hdom y)
    have htr' : (β * Matrix.of (a * Z y * aᴴ)).trace = (β * Matrix.of (Z y)).trace := htr
    rw [htr'] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  rw [hφ' (x * y), hφ' y, spherical_section_levi_mul p q e a a' x y hx, hlevi y, hHeq]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.ContinuousWeightFactor
noncomputable section

open Matrix Metric Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.SiegelWeilFormula.Holtb

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.HSt.HolTPf

variable {n : ℕ}

def bmap (q : ℕ) (y : GR n) : Matrix (Fin n) (Fin n) ℂ := if q = 0 then zOf y else -(zOf y)ᴴ

def negConj (W : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := fun i j => -star (W j i)

theorem negConj_eq (W : Fin n → Fin n → ℂ) : negConj W = (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j; simp [negConj]

theorem negConj_negConj (W : Fin n → Fin n → ℂ) : negConj (negConj W) = W := by
  ext i j; simp [negConj]

theorem negConj_mem {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : negConj W ∈ Dom n := by
  rw [negConj_eq]; exact neg_conj_mem' hW

theorem norm_negConj_sub (W W' : Fin n → Fin n → ℂ) : ‖negConj W - negConj W'‖ ≤ ‖W - W'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h : (negConj W - negConj W') i j = -star ((W - W') j i) := by
    show -star (W j i) - -star (W' j i) = -star (W j i - W' j i)
    rw [star_sub]; ring
  rw [h, norm_neg, norm_star]
  exact (norm_le_pi_norm ((W - W') j) i).trans (norm_le_pi_norm (W - W') j)

theorem bmap_local (q : ℕ) (W₀ : Fin n → Fin n → ℂ) (hW₀ : W₀ ∈ Dom n) : ∃ r > 0, closedBall W₀ r ⊆ Dom n ∧
    ∃ S : Set (GR n), IsCompact S ∧ ∀ W ∈ closedBall W₀ r, ∃ y ∈ S, (bmap q y : Fin n → Fin n → ℂ) = W := by
  by_cases hq : q = 0
  · obtain ⟨r, hr, hsub, S, hS, hcov⟩ := zOf_surj_bdd' W₀ hW₀
    refine ⟨r, hr, hsub, S, hS, fun W hW => ?_⟩
    obtain ⟨y, hy, hyW⟩ := hcov W hW
    refine ⟨y, hy, ?_⟩
    unfold bmap
    rw [if_pos hq]
    exact hyW
  · obtain ⟨r, hr, hsub, S, hS, hcov⟩ := zOf_surj_bdd' (negConj W₀) (negConj_mem hW₀)
    have key : ∀ W ∈ closedBall W₀ r, negConj W ∈ closedBall (negConj W₀) r := by
      intro W hW
      rw [mem_closedBall, dist_eq_norm] at hW ⊢
      exact (norm_negConj_sub W W₀).trans hW
    refine ⟨r, hr, fun W hW => ?_, S, hS, fun W hW => ?_⟩
    · have h := negConj_mem (hsub (key W hW))
      rwa [negConj_negConj] at h
    · obtain ⟨y, hy, hyW⟩ := hcov (negConj W) (key W hW)
      refine ⟨y, hy, ?_⟩
      unfold bmap
      rw [if_neg hq, hyW]
      funext i j
      show -star (negConj W j i) = W i j
      simp [negConj]

theorem bmap_surj (q : ℕ) {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : ∃ y : GR n, (bmap q y : Fin n → Fin n → ℂ) = W := by
  by_cases hq : q = 0
  · obtain ⟨y, hy⟩ := zOf_surj' hW
    refine ⟨y, ?_⟩
    unfold bmap
    rw [if_pos hq]
    exact hy
  · obtain ⟨y, hy⟩ := zOf_surj' (negConj_mem hW)
    refine ⟨y, ?_⟩
    unfold bmap
    rw [if_neg hq, hy]
    funext i j
    show -star (negConj W j i) = W i j
    simp [negConj]

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_toBlocks₂₁ : Continuous fun M : M2 n => M.toBlocks₂₁ :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))

theorem continuous_toBlocks₂₂ : Continuous fun M : M2 n => M.toBlocks₂₂ :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))

theorem zpow_cond {a : ℂ} {k : ℤ} (h : a ^ k ≠ 0) : a ≠ 0 ∨ 0 ≤ k := by
  by_contra hc
  push_neg at hc
  obtain ⟨rfl, hk⟩ := hc
  exact h (zero_zpow k (ne_of_lt hk))

theorem continuous_weight_factor (p q : ℕ) (e : ℤ) : Continuous (F0 p q e : GR n → ℂ) := by
  have hd : Continuous fun y : GR n => (mR y).det := continuous_mR.matrix_det
  have hb1 : Continuous fun y : GR n => toBlocks₂₁ (mR y) := continuous_toBlocks₂₁.comp continuous_mR
  have hb2 : Continuous fun y : GR n => toBlocks₂₂ (mR y) := continuous_toBlocks₂₂.comp continuous_mR
  have h1 : Continuous fun y : GR n => (u1 (mR y)).det := by
    unfold u1
    exact (((continuous_const (y := Complex.I)).smul hb1).add hb2).matrix_det
  have h2 : Continuous fun y : GR n => (u2 (mR y)).det := by
    unfold u2
    exact ((((continuous_const (y := Complex.I)).smul hb1).neg).add hb2).matrix_det
  have hne := spherical_section_ne_zero_group (n := n) p q e
  simp only [F0, f0] at hne ⊢
  exact (hd.zpow₀ e fun y => zpow_cond (left_ne_zero_of_mul (hne y))).mul
    ((h1.zpow₀ _ fun y => zpow_cond (left_ne_zero_of_mul (right_ne_zero_of_mul (hne y)))).mul
      (h2.zpow₀ _ fun y => zpow_cond (right_ne_zero_of_mul (right_ne_zero_of_mul (hne y)))))

end PositivityTheory.SiegelWeilFormula.Holtb
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.IntHol
noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace PositivityTheory.SiegelWeilFormula.Holtb

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem aesm_fderiv (f : X → E → ℂ) (W₀ : E) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x, DifferentiableAt ℂ (f x) W₀)
    (hm : ∀ W ∈ ball W₀ r, AEStronglyMeasurable (f · W) ν) :
    AEStronglyMeasurable (fun x => fderiv ℂ (f x) W₀) ν := by
  classical
  let b := Module.finBasis ℂ E
  let L : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hrep : ∀ x, fderiv ℂ (f x) W₀ = ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := by
    intro x
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, L, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hfun : (fun x => fderiv ℂ (f x) W₀) = fun x => ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := funext hrep
  rw [hfun]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  refine AEStronglyMeasurable.smul_const ?_ (L i)
  set v := b i
  set ε : ℝ := r / (2 * (‖v‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  set t : ℕ → ℂ := fun k => ((ε * (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) with ht_def
  have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε)
      rw [mul_zero] at h
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa [ht_def, Function.comp_def] using h2
    · simp only [ht_def, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have htn : ∀ k, ‖t k‖ ≤ ε := by
    intro k
    simp only [ht_def, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have htmem : ∀ k, W₀ + t k • v ∈ ball W₀ r := by
    intro k
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ε * (‖v‖ + 1) = r / 2 := by rw [hε_def]; field_simp
    have h2 : ‖t k‖ * ‖v‖ ≤ ε * (‖v‖ + 1) := by
      calc ‖t k‖ * ‖v‖ ≤ ε * ‖v‖ := by gcongr; exact htn k
        _ ≤ ε * (‖v‖ + 1) := by nlinarith
    linarith
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun k x => (t k)⁻¹ • (f x (W₀ + t k • v) - f x W₀)) (fun k => ?_) (ae_of_all _ fun x => ?_)
  · exact (((hm _ (htmem k)).sub (hm _ (mem_ball_self hr))).const_smul ((t k)⁻¹)).congr (ae_of_all _ fun x => rfl)
  · have hl : HasDerivAt (fun s : ℂ => W₀ + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add W₀
    have h1 : HasDerivAt (fun s : ℂ => f x (W₀ + s • v)) (fderiv ℂ (f x) W₀ v) 0 :=
      (hd x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
    have h2 := h1.tendsto_slope_zero.comp ht0
    simpa [Function.comp_def] using h2

theorem differentiableOn_integral_of_bdd [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (f : X → E → ℂ)
    (hd : ∀ x, DifferentiableOn ℂ (f x) U) (hm : ∀ W ∈ U, AEStronglyMeasurable (f · W) ν)
    (hb : ∀ W₀ ∈ U, ∃ r > 0, ∃ M, ball W₀ r ⊆ U ∧ ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M) :
    DifferentiableOn ℂ (fun W => ∫ x, f x W ∂ν) U := by
  intro W₀ hW₀
  obtain ⟨r, hr, M, hsub, hM⟩ := hb W₀ hW₀
  set M' := max M 0
  have hM' : ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M' := fun x W hW => (hM x W hW).trans (le_max_left _ _)
  have hdiffAt : ∀ x, ∀ W ∈ ball W₀ r, DifferentiableAt ℂ (f x) W := fun x W hW =>
    (hd x).differentiableAt (hU.mem_nhds (hsub hW))
  have hball : ∀ W ∈ ball W₀ (r / 2), ball W (r / 2) ⊆ ball W₀ r := by
    intro W hW
    apply ball_subset_ball'
    rw [mem_ball] at hW
    linarith
  have hbnd : ∀ x, ∀ W ∈ ball W₀ (r / 2), ‖fderiv ℂ (f x) W‖ ≤ (2 * M') / (r / 2) := by
    intro x W hW
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
    · exact (hd x).mono ((hball W hW).trans hsub)
    · intro Z hZ
      rw [mem_closedBall, dist_eq_norm]
      have hZ' : Z ∈ ball W₀ r := hball W hW hZ
      have hW' : W ∈ ball W₀ r := ball_subset_ball (by linarith) hW
      calc ‖f x Z - f x W‖ ≤ ‖f x Z‖ + ‖f x W‖ := norm_sub_le _ _
        _ ≤ M' + M' := add_le_add (hM' x Z hZ') (hM' x W hW')
        _ = 2 * M' := by ring
    · positivity
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun W x => f x W)
    (F' := fun W x => fderiv ℂ (f x) W) (bound := fun _ => (2 * M') / (r / 2)) (s := ball W₀ (r / 2)) (x₀ := W₀)
    (ball_mem_nhds W₀ (by positivity))
    (eventually_of_mem (hU.mem_nhds hW₀) fun W hW => hm W hW)
    ((integrable_const M').mono' (hm W₀ hW₀) (ae_of_all _ fun x => hM' x W₀ (mem_ball_self hr)))
    (aesm_fderiv f W₀ r hr (fun x => hdiffAt x W₀ (mem_ball_self hr)) (fun W hW => hm W (hsub hW)))
    (ae_of_all _ fun x W hW => hbnd x W hW)
    (integrable_const _)
    (ae_of_all _ fun x W hW => (hdiffAt x W (ball_subset_ball (by linarith) hW)).hasFDerivAt)
  exact key.differentiableAt.differentiableWithinAt

end PositivityTheory.SiegelWeilFormula.Holtb
end
end

noncomputable section

open Matrix Metric Set Filter Topology MeasureTheory
open scoped ComplexOrder

namespace PositivityTheory.SiegelWeilFormula.Holtb

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.HSt.HolTPf

theorem holomorphic_average_uniform : ∀ (n p q : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ι : GR n →* G),
    Continuous ι →
    ∀ A : G → ℂ, Continuous A → (∀ g, IsHolW p q e fun y => A (g * ι y)) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (c : X → G) (u : X → ℂ) (C : Set G), IsCompact C →
      (∀ x, c x ∈ C) → (∀ x, ‖u x‖ ≤ 1) → (∀ y, AEStronglyMeasurable (fun x => A (c x * ι y) * u x) ν) →
      IsHolW p q e fun y => ∫ x, A (c x * ι y) * u x ∂ν := by
  intro n p q e G _ _ _ ι hι A hA hhol X _ ν _ c u C hC hcC hu hmeas
  choose H hHd hHe using hhol
  have hHe' : ∀ g y, A (g * ι y) = F0 p q e y * H g (bmap q y) := hHe
  have hval : ∀ g y, H g (bmap q y) = A (g * ι y) / F0 p q e y := by
    intro g y
    rw [hHe' g y]
    exact (mul_div_cancel_left₀ _ (spherical_section_ne_zero_group p q e y)).symm
  set f : X → (Fin n → Fin n → ℂ) → ℂ := fun x W => H (c x) W * u x with hf
  refine ⟨fun W => ∫ x, f x W ∂ν, ?_, ?_⟩
  · refine differentiableOn_integral_of_bdd (U := Dom n) isOpen_dom' f (fun x => (hHd (c x)).mul_const _) ?_ ?_
    · intro W hW
      obtain ⟨y, hy⟩ := bmap_surj q hW
      have h : (fun x => f x W) = fun x => (A (c x * ι y) * u x) * (F0 p q e y)⁻¹ := by
        funext x
        simp only [hf]
        rw [← hy, hval, div_eq_mul_inv]
        ring
      rw [h]
      exact (hmeas y).mul_const _
    · intro W₀ hW₀
      obtain ⟨r, hr, hsub, S, hS, hSW⟩ := bmap_local q W₀ hW₀
      obtain ⟨K, hK⟩ := (hC.prod hS).exists_bound_of_continuousOn
        ((hA.comp (continuous_fst.mul (hι.comp continuous_snd))).continuousOn)
      obtain ⟨y₀, hy₀S, -⟩ := hSW W₀ (mem_closedBall_self hr.le)
      obtain ⟨ym, hymS, hymin⟩ := hS.exists_isMinOn ⟨y₀, hy₀S⟩ (continuous_weight_factor p q e).norm.continuousOn
      have hm : 0 < ‖F0 p q e ym‖ := norm_pos_iff.2 (spherical_section_ne_zero_group p q e ym)
      refine ⟨r, hr, K / ‖F0 p q e ym‖, ball_subset_closedBall.trans hsub, fun x W hW => ?_⟩
      obtain ⟨y, hyS, hy⟩ := hSW W (ball_subset_closedBall hW)
      have hAy : ‖A (c x * ι y)‖ ≤ K := hK (c x, y) ⟨hcC x, hyS⟩
      have hmy : ‖F0 p q e ym‖ ≤ ‖F0 p q e y‖ := hymin hyS
      have hK0 : 0 ≤ K := (norm_nonneg _).trans hAy
      have hfx : ‖f x W‖ = ‖A (c x * ι y)‖ / ‖F0 p q e y‖ * ‖u x‖ := by
        simp only [hf]
        rw [← hy, hval, norm_mul, norm_div]
      rw [hfx]
      calc ‖A (c x * ι y)‖ / ‖F0 p q e y‖ * ‖u x‖ ≤ K / ‖F0 p q e ym‖ * 1 := by
            apply mul_le_mul _ (hu x) (norm_nonneg _) (by positivity)
            exact div_le_div₀ hK0 hAy hm hmy
        _ = K / ‖F0 p q e ym‖ := mul_one _
  · intro y
    show _ = F0 p q e y * ∫ x, f x (bmap q y) ∂ν
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hf]
    rw [hHe' (c x) y]
    ring

theorem holT : HolT := ⟨holomorphic_translation_levi, holomorphic_average_uniform⟩

end PositivityTheory.SiegelWeilFormula.Holtb
end
end

noncomputable section

open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem tTheta : TTheta := Tpar.tTheta_of (tweyl.tthetaComm TBij.tBij)

theorem tAll_of (hW : TWeyl) : TAll := ⟨TBij.tBij, Tpar.tPar, hW, tTheta, Tauto.thetaAuto GlobalTheory.T.siegel_set_unitary Tpar.tPar tTheta⟩

theorem thetaCoef : ThetaCoef := Tauto.thetaCoef GlobalTheory.T.siegel_set_unitary TBij.tBij Tpar.tPar tTheta

theorem whitGenLt : Gen.WhitGenLt :=
  Gen.whitGenLtOf SwLocFin.locFin2 Gunr.unrWhit (GReal.realWhit_of WR.wr) GFac.factorX PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA

theorem whitGenEq : Gen.WhitGenEq :=
  Gen.whitGenEqOf SwLocFin.locFinX Gunr.unrWhitX (GReal.realWhitEq_of WR.wr) GFac.factorX Gen.lOrd PositivityTheory.Rg.Base1.densEq

theorem whitGenLow : Gen.WhitGenLow :=
  Gen.whitGenLowOf SwLocFin.locFinX Gunr.unrWhitX (GReal.realLow_of SP.wrOrd) GFac.factorX Gen.lOrd

theorem siegelWeilStd_of (hT : TAll) (hLI : LocInst) (hGD : GIdil) (hKP : KFinPoly) (hPK : PolyKFin) (hLD : LDEx)
    (hCT : CTSplit) (hH : HolLead) : SiegelWeilStd := by
  have hA : AuxiliaryPrimeFunction := kfour.auxEx
  have hF : FockMem := KFock.fockMem
  have hLo : LocOpEx := locOpEx_of_tAll hT
  have hGS : GSplit := KSplit.gSplit_of hF (KAway.awayAct_of_tAll hT)
  have hVK : VacK := Avac.vacK_of hT hF hLo hLI (KAway.finAct_of_tAll hT)
  have hW : WhitK := KWhit.whitK_of hT hA Krd.rdEx hF hKP Khead.secK kunf.unfold whitGenLt thetaCoef kfour.lamBd hPK
  have hWE : WhitEq :=
    KWhit.whitEq_of hT hA Krd.rdEx hF hKP Khead.secK kunf.unfold Aeis.eisWk whitGenEq thetaCoef kfour.lamBd hPK
  have hWL : WhitLow := KWhit.whitLow_of hVK hT hA hF Khead.secK kunf.unfold Aeis.eisWk whitGenLow thetaCoef kfour.lamBd hPK
  have hSt : Step := AStep.stepOf hH Holtb.holT hT thetaCoef hA kfour.coefEx hF (KFock.liftEx hT.1) hLo hLI hGS hPK Khead.secK
    Aeis.eisWk kfour.lamBd (KSing.lamSing_of kfour.coefEx kfour.fourierZero Krd.denseW hA) kfour.fourierZero kunf.unfold hWL hVK
    (Avac.iwaQ_of' hT) hCT Afc.uEx (Afc.fcConj_of hA) Afc.orbRes
  exact Atop.siegelWeilStd_of AbsSt.absThm hT thetaCoef hLo hLI hGS (KSplit.gIinv_of hT hF) hGD hKP hPK kunf.unfold hW hWE
    AbsSt.vacuum_generates_polynomials hLD hVK hSt

end PositivityTheory.SiegelWeilFormula.Fin

end
