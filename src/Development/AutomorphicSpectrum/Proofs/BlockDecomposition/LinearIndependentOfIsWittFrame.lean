module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.UnipCocompact

open GlobalTheory.UnipFlagCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem unipMin_eq_radSet (X : Matrix (Fin n) (Fin r) E) :
    unipMin σ J X = radSet σ J X Fin.val := by
  ext u
  constructor
  · rintro ⟨B, hB, hd, hX, hz⟩
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * (B - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      exact congrArg (· - adMat F X) hX
    refine ⟨fun i => ⟨fun j => (B - 1) j i, fun j hij => ?_, ?_⟩, hz⟩
    · rcases (Fin.le_def.2 hij).eq_or_lt with e | e
      · subst e; simp [hd]
      · simp [hB e, e.ne']
    · funext k
      exact congrFun (congrFun e k) i
  · rintro ⟨h1, h2⟩
    choose a ha ha' using h1
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * Matrix.of (fun j i => a i j) := by
      ext k i
      exact congrFun (ha' i) k
    refine ⟨1 + Matrix.of (fun j i => a i j), fun i j hij => ?_, fun i => ?_, ?_, h2⟩
    · have hij' : j < i := hij
      simp [ha j i hij'.le, hij'.ne']
    · simp [ha i i le_rfl]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul]
      exact (add_sub_cancel _ _).symm

theorem closure_radSet_subset (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {X : Matrix (Fin n) (Fin r) E}
    (hC : LinearIndependent E Xᵀ) (h0 : cT (σ : E →+* E) X * J * X = 0) {g : HA (AF F) σ J}
    (hg : g ∈ Subgroup.closure (radSet σ J X Fin.val)) : g ∈ radSet σ J X Fin.val := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hσ hJ X hC h0
  have hd : ∀ j : Fin r, (j : ℕ) < r := fun j => j.2
  have he := idem_complete hσ hJ X L hL h0 hLL
  have hs := fam_st (adj_mul hσ hJ) (adj_adj hσ hJ) (idem (F := F) X L) (Fin.val : Fin r → ℕ) r
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hσ hJ) (adj_adj hσ hJ)
  rw [mem_radSet_iff hσ hJ X L hL h0 hLL hd]
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_radSet_iff hσ hJ X L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    have e : (HA.mat _ σ J (x * y)).1 = (HA.mat _ σ J x).1 * (HA.mat _ σ J y).1 := rfl
    rw [e]
    generalize (HA.mat _ σ J x).1 = a at hx ⊢
    generalize (HA.mat _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adj_mul hσ hJ) (adj_adj hσ hJ) hs 0 hx
    rwa [map_sub, adj_mat hσ hJ, h1] at this

theorem linearIndependent_of_isWittFrame (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) : LinearIndependent E Xᵀ := by
  have e : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' hσ hJ, cT_gram hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  refine Matrix.mulVec_injective_iff.1 fun v w h => ?_
  have := congrArg ((cT (σ : E →+* E) Y * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] using this

theorem unipMin_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ u ∈ unipMin σ J X, ∃ δ ∈ ratPts σ J, δ ∈ unipMin σ J X ∧ ∃ c ∈ C, c ∈ unipMin σ J X ∧ u = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  have hσ := sigma_sigma h
  have hC := linearIndependent_of_isWittFrame hσ hJ hW
  obtain ⟨K, hK, hcov⟩ := closure_radSet_cocompact hσ hJ X hC hW.xx Fin.val
  have hsub : ∀ g : Subgroup.closure (radSet σ J X Fin.val), g.1 ∈ unipMin σ J X := fun g => by
    rw [unipMin_eq_radSet]
    exact closure_radSet_subset hσ hJ hC hW.xx g.2
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun u hu => ?_⟩
  rw [unipMin_eq_radSet] at hu
  obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨u, Subgroup.subset_closure hu⟩
  exact ⟨γ.1, hγ, hsub γ, k.1, ⟨k, hk, rfl⟩, hsub k, congrArg Subtype.val e⟩

end GlobalTheory.CompanionTheory.UnipCocompact
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqIntAt
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  simpa using lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
    two_ne_zero ENNReal.ofNat_ne_top hc.eLpNorm_lt_top

end GlobalTheory.CompanionTheory.SqIntFD
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PosNorm
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.PosNormFD

theorem posNorm : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.PosNorm := by
  intro E _ _ _ N _ _ μ _ 𝓕 h𝓕 φ hA hS hne
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  have hc : Continuous φ.1 := GlobalTheory.CuspRep.IsAutForm.continuous hA
  have hl := GlobalTheory.DiscreteUnit.left_latticeGL hA hS
  by_contra h0
  have h0' : ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ = 0 := by simpa using h0
  have hm : Measurable fun g => ‖φ.1 g‖ₑ ^ 2 := hc.enorm.measurable.pow_const 2
  have hz := (lintegral_eq_zero_iff hm).1 h0'
  have hSo : IsOpen {g | φ.1 g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hSF : μ ({g | φ.1 g ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hSo.measurableSet]
    refine measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)
    have hg' : φ.1 g ≠ 0 := hg
    simpa [hg'] using hg'
  have hinv : ∀ γ : latticeGL E N, γ • {g | φ.1 g ≠ 0} = {g | φ.1 g ≠ 0} := fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e : φ.1 (γ⁻¹ • x) = φ.1 x := hl _ (γ⁻¹).2 x
    simp only [Set.mem_setOf_eq, e]
  set_option synthInstance.maxHeartbeats 200000 in
    have hS0 := h𝓕.measure_zero_of_invariant _ hinv hSF
  have hemp := (hSo.measure_eq_zero_iff μ).1 hS0
  refine hne (Subtype.ext (funext fun g => ?_))
  by_contra hg
  exact (Set.eq_empty_iff_forall_notMem.1 hemp g) hg

end GlobalTheory.CompanionTheory.PosNormFD
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzero
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem sqMass_ne_top_and_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
      ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
        (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  intro E _ _ _ N _ _ μ _ F hF φ hA hS hne
  exact ⟨(GlobalTheory.CompanionTheory.SqIntFD.sqIntAt E N μ F hF φ hA hS).ne,
    (GlobalTheory.CompanionTheory.PosNormFD.posNorm E N μ F hF φ hA hS hne).ne'⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzeroStatement
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_norm_finite_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
    (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero | exact GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero | (intros; apply GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLinearChangeModulus
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLinearChangeModulus
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BZPhiPG.Scale

theorem sr1_field (k : Type) [Field k] : GlobalTheory.HaarLin.HasStableRangeOne k := by
  intro a b h
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      exact not_isCoprime_zero_zero h
    exact ⟨b⁻¹, by simp [hb]⟩
  · exact ⟨0, by simp [ha]⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAddHaar_muD (t : ℕ) : @Measure.IsAddHaarMeasure _ _ _ (_root_.borel _) (muD k t) := by
  letI : MeasurableSpace (Fin t → k) := _root_.borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem map_muD (t : ℕ) (A : GL (Fin t) k) :
    @Measure.map _ _ (_root_.borel _) (_root_.borel _) (fun d : Fin t → k => (A⁻¹ : GL (Fin t) k).val *ᵥ d) (muD k t) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det A)) • muD k t := by
  haveI : SecondCountableTopology k := GlobalTheory.HaarScaleMatrix.secondCountable_of_localField k
  have h := GlobalTheory.HaarLin.map_mulVec_of_mem_TD k (Fin t) (A⁻¹ : GL (Fin t) k).val
    (GlobalTheory.HaarLin.Gauss.mem_TD_of_isUnit_det k (sr1_field k) (Fin t) _
      (Matrix.GeneralLinearGroup.det (A⁻¹ : GL (Fin t) k)).isUnit)
    (Matrix.GeneralLinearGroup.det (A⁻¹ : GL (Fin t) k)) rfl (muD k t) (isAddHaar_muD t)
  rw [h, map_inv, map_inv, inv_inv]

theorem val_dpow_one (t : ℕ) (A : GL (Fin t) k) :
    ((dpow t 1 A : ℂˣ) : ℂ) = ((distribHaarChar k (Matrix.GeneralLinearGroup.det A) : ℝ) : ℂ) := by
  show ((absPow k (((1 : ℝ)) : ℂ) (Matrix.GeneralLinearGroup.det A) : ℂˣ) : ℂ) = _
  rw [val_absPow, Complex.ofReal_one, Complex.cpow_one]
  rfl

theorem smInt_mulVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W)
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) =
      ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) φ := by
  classical
  letI : MeasurableSpace (Fin t → k) := _root_.borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  haveI : (muD k t).IsAddHaarMeasure := isAddHaar_muD t
  set f : (Fin t → k) → (Fin t → k) := fun d => (A⁻¹ : GL (Fin t) k).val *ᵥ d with hf
  have fc : Continuous f := Continuous.matrix_mulVec continuous_const continuous_id
  have fm : Measurable f := fc.measurable
  set a : NNReal := distribHaarChar k (Matrix.GeneralLinearGroup.det A) with ha
  have hmeas : ∀ y : W, muD k t ((φ ∘ f) ⁻¹' {y}) = a • muD k t (φ ⁻¹' {y}) := by
    intro y
    have hS : MeasurableSet (φ ⁻¹' {y}) := (l.isOpen_fiber y).measurableSet
    rw [Set.preimage_comp, ← Measure.map_apply fm hS, map_muD t A]
    rfl
  let S : Finset W := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have e₀ : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (id ∘ (φ ∘ f)) =
      ∑ y ∈ S, ((((muD k t) ((φ ∘ f) ⁻¹' {y})).toReal : ℝ) : ℂ) • id y :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp (muD k t) (φ ∘ f) id S (fun x => hS _)
      (fun y _ => ((l.comp_continuous fc).isOpen_fiber y).measurableSet)
      (fun y _ hy => by
        rw [hmeas y]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (GlobalTheory.CompanionTheory.Rodier.SmIntEl.measure_level_ne_top _ c hy))
  have e₁ : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (id ∘ φ) =
      ∑ y ∈ S, ((((muD k t) (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • id y :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp (muD k t) φ id S hS
      (fun y _ => (l.isOpen_fiber y).measurableSet)
      (fun y _ hy => GlobalTheory.CompanionTheory.Rodier.SmIntEl.measure_level_ne_top _ c hy)
  have e₀' : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (fun d => φ (f d)) = _ := e₀
  have e₁' : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) φ = _ := e₁
  rw [val_dpow_one]
  refine e₀'.trans ?_
  rw [e₁', Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hmeas y, ENNReal.toReal_smul, smul_smul]
  congr 1
  simp [NNReal.smul_def, ← ha]

end GlobalTheory.CompanionTheory.BZPhiPG.Scale

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLinearChangeModulusStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_linear_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W) (l : IsLocallyConstant φ) (c : HasCompactSupport φ), @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) = ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) φ := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def XA (lam : Fin n → ℤ) (B : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => fderiv ℂ (fun x : Mat n => Rm lam x i j) 1 B

def Xu (lam : Fin n → ℤ) (a b : Fin n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  XA lam (Matrix.single a b 1)

def HolRm (lam : Fin n → ℤ) : Prop :=
  ∀ (i j : Jd n lam), ∀ g ∈ GLs n, DifferentiableAt ℂ (fun x : Mat n => Rm lam x i j) g

theorem XA_add (lam : Fin n → ℤ) (B B' : Mat n) : XA lam (B + B') = XA lam B + XA lam B' := by
  ext i j; simp [XA]

theorem XA_smul (lam : Fin n → ℤ) (c : ℂ) (B : Mat n) : XA lam (c • B) = c • XA lam B := by
  ext i j; simp [XA]

theorem XA_sum (lam : Fin n → ℤ) {ι : Type} (s : Finset ι) (B : ι → Mat n) :
    XA lam (∑ r ∈ s, B r) = ∑ r ∈ s, XA lam (B r) := by
  ext i j; simp [XA, Matrix.sum_apply]

theorem Rm_of_unit (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) :
    Rm lam x = LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h)) := by
  rw [Rm, dite_eq_left h]

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Mat n) = 1 := by
  have h : IsUnit (1 : Mat n).det := by simp
  rw [Rm_of_unit lam h]
  have e : Matrix.nonsingInvUnit (1 : Mat n) h = 1 := Units.ext rfl
  rw [e, map_one]
  exact LinearMap.toMatrix_one _

theorem Rm_mul (lam : Fin n → ℤ) {x y : Mat n} (hx : IsUnit x.det) (hy : IsUnit y.det) :
    Rm lam (x * y) = Rm lam x * Rm lam y := by
  have h : IsUnit (x * y).det := by rw [Matrix.det_mul]; exact hx.mul hy
  rw [Rm_of_unit lam h, Rm_of_unit lam hx, Rm_of_unit lam hy]
  have e : Matrix.nonsingInvUnit (x * y) h = Matrix.nonsingInvUnit x hx * Matrix.nonsingInvUnit y hy := Units.ext rfl
  rw [e, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem isUnit_det_of_mem {g : Mat n} (hg : g ∈ GLs n) : IsUnit g.det := isUnit_iff_ne_zero.2 hg

theorem mem_GLs_of_isUnit {g : Mat n} (hg : IsUnit g.det) : g ∈ GLs n := hg.ne_zero

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne_fun this continuous_const

theorem hasDerivAt_line {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (i j : Jd n lam) :
    HasDerivAt (fun t : ℂ => Rm lam (1 + t • B) i j) (XA lam B i j) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => (1 : Mat n) + t • B) B 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const B).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h2 := (hD i j 1 one_mem_GLs).hasFDerivAt
  exact h2.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by simp)

theorem eventually_line_unit (B : Mat n) : ∀ᶠ t : ℂ in 𝓝 0, IsUnit ((1 : Mat n) + t • B).det := by
  have hc : Continuous fun t : ℂ => (1 : Mat n) + t • B := continuous_const.add (continuous_id.smul continuous_const)
  have : ∀ᶠ t : ℂ in 𝓝 0, (1 : Mat n) + t • B ∈ GLs n :=
    hc.continuousAt.eventually_mem (isOpen_GLs.mem_nhds (by simpa using one_mem_GLs))
  exact this.mono fun t ht => isUnit_det_of_mem ht

theorem conj_XA {lam : Fin n → ℤ} (hD : HolRm lam) {x B B' : Mat n} (hx : IsUnit x.det) (h : x * B = B' * x) :
    Rm lam x * XA lam B = XA lam B' * Rm lam x := by
  ext i j
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j = ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j := by
    filter_upwards [eventually_line_unit B, eventually_line_unit B'] with t h1 h2
    have e : x * (1 + t • B) = (1 + t • B') * x := by
      simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, h]
    have := Rm_mul lam hx h1
    rw [e, Rm_mul lam h2 hx] at this
    have := congrFun (congrFun this i) j
    simpa [Matrix.mul_apply] using this.symm
  have hL : HasDerivAt (fun t : ℂ => ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam x i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hR : HasDerivAt (fun t : ℂ => ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j)
      (∑ k, XA lam B' i k * Rm lam x k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B' i k).mul_const _
  simpa [Matrix.mul_apply] using (hL.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)).unique hR |>.symm ▸ rfl

theorem fderiv_Rm {lam : Fin n → ℤ} (hD : HolRm lam) {g : Mat n} (hg : g ∈ GLs n) (B : Mat n) (i j : Jd n lam) :
    fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B) = (Rm lam g * XA lam B) i j := by
  have hu := isUnit_det_of_mem hg
  have hline : HasDerivAt (fun t : ℂ => g + t • (g * B)) (g * B) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const (g * B)).const_add g
    rw [one_smul] at h
    exact h
  have h1 : HasDerivAt (fun t : ℂ => Rm lam (g + t • (g * B)) i j)
      (fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B)) 0 :=
    (hD i j g hg).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have h2 : HasDerivAt (fun t : ℂ => ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam g i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hev : ∀ᶠ t : ℂ in 𝓝 0, Rm lam (g + t • (g * B)) i j = ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j := by
    filter_upwards [eventually_line_unit B] with t ht
    have e : g + t • (g * B) = g * (1 + t • B) := by
      simp only [mul_add, mul_one, Matrix.mul_smul]
    rw [e, Rm_mul lam hu ht, Matrix.mul_apply]
  simpa [Matrix.mul_apply] using h1.unique (h2.congr_of_eventuallyEq hev)

end GlobalTheory.CompanionTheory.RmHol
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjoint
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjoint
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.SpinRel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def quadM (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b

theorem term_comm {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g e : Fin n) :
    c a e * c e b * c d g - c d g * (c a e * c e b) =
      (if b = d then (if e = g then (2 : ℂ) • c a g else 0) else 0) -
        (if a = g then (if e = d then (2 : ℂ) • c d b else 0) else 0) := by
  have h1 := hc.1 e b d g
  have h2 := hc.1 a e d g
  have h : c a e * c e b * c d g - c d g * (c a e * c e b) =
      c a e * (c e b * c d g + c d g * c e b) - (c a e * c d g + c d g * c a e) * c e b := by
    noncomm_ring
  rw [h, h1, h2]
  by_cases hbd : b = d <;> by_cases heg : e = g <;> by_cases hag : a = g <;> by_cases hed : e = d <;>
    simp only [hbd, heg, hag, hed, and_self, and_true, and_false, true_and, false_and, if_true, if_false,
      mul_zero, zero_mul, sub_zero, two_smul, mul_two, two_mul] <;> simp_all [two_smul, mul_two, two_mul]

theorem quad_c {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g : Fin n) :
    quadM c a b * c d g - c d g * quadM c a b =
      (if b = d then c a g else 0) - (if a = g then c d b else 0) := by
  have h : quadM c a b * c d g - c d g * quadM c a b =
      (1 / 2 : ℂ) • ∑ e, (c a e * c e b * c d g - c d g * (c a e * c e b)) := by
    simp only [quadM, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm hc, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hag : a = g <;>
    simp [hbd, hag, smul_sub, smul_smul]

theorem quad_quad {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d e : Fin n) :
    quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (if b = d then quadM c a e else 0) - (if e = a then quadM c d b else 0) := by
  have h : ∀ f, quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b =
      ((if b = d then c a f else 0) - (if a = f then c d b else 0)) * c f e +
        c d f * ((if b = f then c a e else 0) - (if a = e then c f b else 0)) := by
    intro f
    rw [← quad_c hc a b d f, ← quad_c hc a b f e]
    noncomm_ring
  have h2 : quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (1 / 2 : ℂ) • ∑ f, (quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b) := by
    conv_lhs => rw [show quadM c d e = (1 / 2 : ℂ) • ∑ f, c d f * c f e from rfl]
    simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h2]
  simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hae : a = e
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel

theorem spinM_eq (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    spinM c a b = quadM c a b - (if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0) := rfl

theorem spin_glRel {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) : Formalism.REAL.GlRel (spinM c) := by
  intro a b d e
  have h := quad_quad hc a b d e
  have hcomm : spinM c a b * spinM c d e - spinM c d e * spinM c a b =
      quadM c a b * quadM c d e - quadM c d e * quadM c a b := by
    simp only [spinM_eq]
    by_cases hab : a = b <;> by_cases hde : d = e <;>
      simp only [hab, hde, if_true, if_false, sub_zero, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one] <;> module
  rw [hcomm, h]
  by_cases hbd : b = d
  · by_cases hea : e = a
    · subst hbd
      subst hea
      simp [spinM_eq]
    · have hae : ¬ a = e := fun h => hea h.symm
      subst hbd
      simp [spinM_eq, hea, hae]
  · by_cases hea : e = a
    · have hdb : ¬ d = b := fun h => hbd h.symm
      simp [spinM_eq, hbd, hea, hdb]
    · simp [hbd, hea]

theorem spin_conjTranspose {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b : Fin n) :
    (spinM c a b)ᴴ = spinM c b a := by
  simp only [spinM_eq, quadM]
  by_cases hab : a = b
  · subst hab
    simp [conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul, Complex.conj_ofNat]
  · simp [hab, Ne.symm hab, conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul]

theorem spinRel : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a :=
  fun _ hc => ⟨spin_glRel hc, spin_conjTranspose hc⟩

end GlobalTheory.CompanionTheory.RealCount.SpinRel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjointStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spin_gl_relations_adjoint : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | exact GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateField
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateField
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem eq_one_of_pow_eq_one_of_valuation_sub_lt {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ} {ξ : K}
    (hm : v (m : K) = 1) (hξ : ξ ^ m = 1) (h : v (ξ - 1) < 1) : ξ = 1 := by
  have hv : v ξ ≤ 1 := by
    have e : ξ = (ξ - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le h.le (by simp))
  have hp : ∀ i : ℕ, v (ξ ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : ξ ^ (i + 1) - 1 = ξ * (ξ ^ i - 1) + (ξ - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt v ?_ h
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) ih
  have hs : v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : K)) < 1 := by
    have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : K) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    exact Valuation.map_sum_lt v one_ne_zero fun i _ => hp i
  have hsum : (∑ i ∈ Finset.range m, ξ ^ i) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hm] at hs
    exact lt_irrefl _ hs
  have := mul_geom_sum ξ m
  rw [hξ, sub_self] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)

theorem natCast_residue_eq_zero {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F (Om l)]
    [ValuativeExtension F (Om l)] : (l : 𝓀[F]) = 0 := by
  have hnl : ¬ ((1 : F) ≤ᵥ (l : F)) := by
    intro h
    have h2 := (ValuativeExtension.vle_iff_vle (A := F) (B := Om l)).2 h
    rw [map_one, map_natCast, GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, norm_one,
      ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends] at h2
    exact absurd (Padic.norm_natCast_lt_one_iff.mpr (dvd_refl l)) (not_lt.mpr h2)
  have hlt : valuation F (((l : 𝒪[F]) : 𝒪[F]) : F) < 1 := by
    refine not_le.mp fun h => hnl ?_
    rw [Valuation.Compatible.vle_iff_le (v := valuation F), map_one]
    simpa using h
  have hmem : (l : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
    exact ne_of_lt hlt
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
  exact hmem

theorem unramifiedDegree_eq_one_of_mem_inertia : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  intro l _ E Ω _ _ _ _ _ A O _ _ _ Bw hj F _ _ _ _ _ _ _ σ hσ g hg
  rw [GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, natCast_residue_eq_zero (l := l) (F := F), zero_mul]
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero m := ⟨hm0⟩
  have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ₀, h₀⟩ : ∃ z : Ω, IsPrimitiveRoot z m := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hj0 := h₀.map_of_injective Bw.j.injective
  obtain ⟨i, -, hi⟩ := hj0.eq_pow_of_pow_eq_one hζm

  obtain ⟨z, hz, hzm⟩ : ∃ z : Ω, Bw.j z = ζ ∧ z ^ m = 1 :=
    ⟨ζ₀ ^ i, by rw [map_pow, hi], by rw [← pow_mul, mul_comm, pow_mul, h₀.pow_eq_one, one_pow]⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hm0] at hzm
  let s : G E Ω := (σ : G E Ω)
  have hgz : g ζ = Bw.j (s z) := by
    rw [hg, ← hz]
    exact Bw.e_comm σ z
  have hnorm : ‖Bw.j z‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp ?_
    rw [← norm_pow, ← map_pow, hzm, map_one, norm_one]
  have hzA : A.valuation z ≤ 1 := by
    rw [A.valuation_le_one_iff]
    exact (hj z).mpr hnorm.le
  have hzunit : A.valuation z = 1 :=
    le_antisymm hzA (not_lt.mp fun h => ((hj.valuation_lt_one_iff z).mp h).ne hnorm)
  have hlt : A.valuation (s z - z) < 1 := hσ.2 z hzA
  have hmn : ‖Bw.j (m : Ω)‖ = 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop
  have hmv : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ?_ (not_lt.mp fun h => ((hj.valuation_lt_one_iff _).mp h).ne hmn)
    rw [A.valuation_le_one_iff]
    exact (hj _).mpr hmn.le
  have hsz : (s z / z) ^ m = 1 := by
    rw [div_pow, ← map_pow, hzm, map_one, div_one]
  have hone : s z / z = 1 := by
    refine eq_one_of_pow_eq_one_of_valuation_sub_lt A.valuation hmv hsz ?_
    have e : s z / z - 1 = (s z - z) / z := by field_simp
    rw [e, map_div₀, hzunit, div_one]
    exact hlt
  rw [hgz, (div_eq_one_iff_eq hz0).mp hone, hz]

end GlobalTheory.CompanionTheory.LTLink
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateFieldStatement
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bridge_lubin_tate_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | exact GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbedding
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open GlobalTheory.CompanionTheory.FineProd (dropHom)

namespace GlobalTheory.CompanionTheory.WordProd.RowCell

section Blocks

variable {r r' N : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
  (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o)

def dropSigma : (Σ a, Fin (d (o a))) ≃ (Σ j, Fin (d j)) :=
  Equiv.ofBijective (fun p => ⟨o p.1, p.2⟩) (by
    constructor
    · rintro ⟨a, t⟩ ⟨b, s⟩ h
      obtain rfl : a = b := ho.injective (congrArg Sigma.fst h)
      simpa using h
    · rintro ⟨j, t⟩
      obtain ⟨a, rfl⟩ := hz j (Nat.pos_iff_ne_zero.1 (Fin.pos t))
      exact ⟨⟨a, t⟩, rfl⟩)

def dropPlacing (f : (Σ j, Fin (d j)) ≃ Fin N) : (Σ a, Fin (d (o a))) ≃ Fin N :=
  (dropSigma d o ho hz).trans f

@[simp] theorem dropPlacing_apply (f : (Σ j, Fin (d j)) ≃ Fin N) (a : Fin r') (t : Fin (d (o a))) :
    dropPlacing d o ho hz f ⟨a, t⟩ = f ⟨o a, t⟩ := rfl

variable (k : Type) [Field k] (f : (Σ j, Fin (d j)) ≃ Fin N)

theorem mem_parab_dropPlacing (g : GL (Fin N) k) :
    g ∈ parab k f ↔ g ∈ parab k (dropPlacing d o ho hz f) := by
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    exact h a b i j (ho.lt_iff_lt.1 hab)

theorem mem_unipRad_dropPlacing (g : GL (Fin N) k) :
    g ∈ unipRad k f ↔ g ∈ unipRad k (dropPlacing d o ho hz f) := by
  rw [mem_unipRad, mem_unipRad, ← mem_parab_dropPlacing d o ho hz k f g]
  refine and_congr_right fun _ => ⟨fun h a i j => h (o a) i j, fun h a i j => ?_⟩
  obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
  exact h a i j

theorem leviEmb_dropPlacing (g : Levi k fun j => Fin (d j)) :
    leviEmb k f g = leviEmb k (dropPlacing d o ho hz f) (dropHom d o g) := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, dropPlacing_apply, dropPlacing_apply, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne k _ _ hab, dropPlacing_apply, dropPlacing_apply,
      leviEmb_apply_ne k _ _ (ho.injective.ne hab)]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSubquotient_pullback {G L W : Type} [Group G] [Group L] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (s : L →* G) (h : IsSubquotient σ ρ) :
    IsSubquotient (σ.comp s) (ρ.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩, hf⟩

theorem jac_dropPlacing_equiv (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (f : (Σ j, Fin (d j)) ≃ Fin N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((GlobalTheory.SmGL.jac f π).Equiv
      ((GlobalTheory.SmGL.jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _)) := by
  have hs' : ∀ g, ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) g ∈
      Subgroup.normalizer (unipRad k (dropPlacing d o ho hz f) : Set (GL (Fin N) k)) :=
    fun g => leviEmb_mem_normalizer k _ _
  obtain ⟨φ⟩ := Placing.jacquet_equiv π (N := unipRad k f) (N' := unipRad k (dropPlacing d o ho hz f))
    (s := leviEmb k f) (s' := (leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o))
    (leviEmb_mem_normalizer k f) hs' (deltaHalf k fun j => Fin (d j))⁻¹ 1
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).1 hu)
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).2 hu)
    (fun g => by simpa using leviEmb_dropPlacing d o ho hz k f g)
  have e : GlobalTheory.SmGL.twist (jacquet π (unipRad k (dropPlacing d o ho hz f))
      ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) hs')
        (deltaHalf k fun j => Fin (d j))⁻¹ =
      ((GlobalTheory.SmGL.jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, MonoidHom.comp_apply]
    show _ = GlobalTheory.SmGL.twist _ _ _ v
    rw [twist_apply, MonoidHom.inv_apply, MonoidHom.inv_apply,
      GlobalTheory.CompanionTheory.FineProd.ProdDrop.deltaHalf_drop d o ho hz g]
    rfl
  rw [← e]
  exact ⟨φ⟩

theorem jhMult_jac_ne_zero_of_jm (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) (hd : ∑ a, (y (o a)).1 = N)
    (f : (Σ j, Fin (y j).1) ≃ Fin N) (π : Representation ℂ (GL (Fin N) k) V)
    (h : jm (fun a => y (o a)) hd π ≠ 0) :
    jhMult (piTensor fun j => (y j).rep) (GlobalTheory.SmGL.jac f π) ≠ 0 := by
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨ψ⟩ := jac_dropPlacing_equiv (fun j => (y j).1) o ho hz f π
  obtain ⟨χ⟩ := (Placing.parInd_jac_placing k _ _ _
    (stdBlocks (fun a => (y (o a)).1) hd) (dropPlacing (fun j => (y j).1) o ho hz f) V).2 π
  have h1 : IsSubquotient (piTensor fun a => (y (o a)).rep)
      (GlobalTheory.SmGL.jac (dropPlacing (fun j => (y j).1) o ho hz f) π) :=
    (jhMult_ne_zero_iff.1 h).trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)
  have h2 := isSubquotient_pullback (dropHom (k := k) (fun j => (y j).1) o) h1
  exact jhMult_ne_zero_iff.2
    ((IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
      (h2.trans (.of_injective ψ.symm.toIntertwiningMap ψ.symm.toLinearEquiv.injective)))

end Local

theorem sigma_clOf {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (d : ℕ) (h : d = x.1) : (⟨d, clOf x d⟩ : IrrGL (k := k)) = x := by
  subst h
  exact Sigma.ext rfl (heq_of_eq (clOf_self x))

theorem jhMult_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (GlobalTheory.SmGL.jac f π) ≠ 0 := by
  intro k _ _ _ _ n p N V _ _ π _ zz σ c hc h0 hz f h
  let y : Fin n → IrrGL (k := k) := fun j => ⟨c j, clOf (zz j) (c j)⟩
  have hy : (fun a => y (σ a)) = fun a => zz (σ a) := funext fun a => sigma_clOf _ _ (hc a)
  have key : ∀ (x x' : Fin p → IrrGL (k := k)) (_ : x = x') (hx : ∑ a, (x a).1 = N) (hx' : ∑ a, (x' a).1 = N),
      jm x hx π = jm x' hx' π := by
    rintro x _ rfl _ _
    rfl
  have hd : ∑ a, (y (σ a)).1 = N := by
    rw [← hz]
    exact Finset.sum_congr rfl fun a _ => hc a
  exact jhMult_jac_ne_zero_of_jm y σ σ.strictMono
    (fun j hj => by_contra fun hn => hj (h0 j hn)) hd f π (by rwa [key _ _ hy hd hz])

end GlobalTheory.CompanionTheory.WordProd.RowCell

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbeddingStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_order_embedding : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  exact @GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row
end
end
