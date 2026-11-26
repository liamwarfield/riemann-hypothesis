module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.WeilM
open Filter Topology

theorem isLocallyConstant_finprod_evalV {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hy : ∀ᶠ v in Filter.cofinite, ∀ i,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.mono fun v hv => hv
  set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F)} with hT
  have hTfin : T.Finite := hcof.and hy
  have hO : IsOpen {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hU : ∀ᶠ y' in 𝓝 y, ∀ i, ∀ v, (y' i - y i) v ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i :=
      (continuous_apply i).sub continuous_const
    have hmem : (fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i) y ∈
        {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} := by
      intro v
      simp only [sub_self]
      exact zero_mem _
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)
  have hS : ∀ᶠ y' in 𝓝 y, ∀ v ∈ T, (φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) =
      φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
    refine (Filter.eventually_all_finite hTfin).2 fun v _ => ?_
    have hg : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F =>
        fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    exact ((IsLocallyConstant.iff_eventually_eq _).1 ((hφ v).1.comp_continuous hg)) y
  filter_upwards [hU, hS] with y' hU' hS'
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ T
  · exact hS' v hv
  · have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
        ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      simpa [hT] using hv
    obtain ⟨h1, h2⟩ := hv'
    have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) ∈ v.adicCompletionIntegers F := by
      intro i
      have h4 := add_mem (hU' i v) (h2 i)
      have h5 : (y' i - y i) v + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) := by
        show (y' i) v - (y i) v + (y i) v = (y' i) v
        exact sub_add_cancel _ _
      rwa [h5] at h4
    rw [h1, Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3),
      Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
    rfl

end GlobalTheory.WeilM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_finprod_schwartzBruhat_finiteAdeles : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.WeilM.isLocallyConstant_finprod_evalV | exact GlobalTheory.WeilM.isLocallyConstant_finprod_evalV | (intros; apply GlobalTheory.WeilM.isLocallyConstant_finprod_evalV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses

def gramOn {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K)) :
    Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
  Matrix.of fun i j => hform σ H (Module.finBasis K V i).1 (Module.finBasis K V j).1

def sgnOn {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (Q : K[X]) (A : Matrix (Fin n) (Fin n) K) : ℂ :=
  (-1) ^ ordL (gramOn σ H (LinearMap.ker (Matrix.toLin' (aeval A Q)))).det

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Gen
variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ}

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) K) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cT_units (k : GL (Fin n) K) : cT σ (k⁻¹).val * cT σ k.val = 1 := by
  rw [← cT_mul, Units.mul_inv, cT_one]

theorem cT_units' (k : GL (Fin n) K) : cT σ k.val * cT σ (k⁻¹).val = 1 := by
  rw [← cT_mul, Units.inv_mul, cT_one]

theorem cT_units_left (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ (k⁻¹).val * (cT σ k.val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units, Matrix.one_mul]

theorem cT_units_left' (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units', Matrix.one_mul]

theorem herm_of (hσ : ∀ x, σ (σ x) = x) (k : GL (Fin n) K) : IsHerm σ (cT σ (k⁻¹).val * (k⁻¹).val) := by
  unfold IsHerm; rw [cT_mul, cT_cT σ hσ]

theorem det_ne (k : GL (Fin n) K) : (cT σ (k⁻¹).val * (k⁻¹).val).det ≠ 0 := by
  have h1 : ((k⁻¹).val).det ≠ 0 := ((k⁻¹).isUnit.map Matrix.detMonoidHom).ne_zero
  have h2 : (cT σ (k⁻¹).val).det = σ ((k⁻¹).val).det := by
    unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [Matrix.det_mul, h2]
  exact mul_ne_zero ((map_ne_zero σ).2 h1) h1

theorem one_of (k : GL (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * (k⁻¹).val) * k.val = 1 := by
  simp only [Matrix.mul_assoc, cT_units_left', Units.inv_mul]

theorem inv_of_unit (k a : GL (Fin n) K) (hy : cT σ (k⁻¹ * a * k).val * 1 * (k⁻¹ * a * k).val = 1) :
    cT σ a.val * (cT σ (k⁻¹).val * (k⁻¹).val) * a.val = cT σ (k⁻¹).val * (k⁻¹).val := by
  have ha : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
  rw [ha]
  generalize k⁻¹ * a * k = y at hy ⊢
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one] at hy ⊢
  simp only [cT_units_left', Units.inv_mul_cancel_left]
  rw [← Matrix.mul_assoc (cT σ y.val), hy, Matrix.one_mul]

theorem unit_of_form (γ₀ h : GL (Fin n) K) (hinv : cT σ γ₀.val * (cT σ h.val * h.val) * γ₀.val = cT σ h.val * h.val) :
    cT σ (h * γ₀ * h⁻¹).val * 1 * (h * γ₀ * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) hinv
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

theorem unit_of_two (k c h : GL (Fin n) K) (H' : Matrix (Fin n) (Fin n) K)
    (h1 : H' = cT σ c.val * (cT σ (k⁻¹).val * (k⁻¹).val) * c.val) (h2 : H' = cT σ h.val * h.val) :
    cT σ (k⁻¹ * c * h⁻¹).val * 1 * (k⁻¹ * c * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) (h1.symm.trans h2)
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

end Gen

theorem cT_map (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (w.adicCompletion E)) =
      cT (cj w) (M.map (algebraMap E (w.adicCompletion E))) := by
  have h := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hw).1
  ext i j; simp [cT, h]

theorem locPt_val (hU : Unr E) {n : ℕ} (w : Pl E) (γ : UE E n) :
    ((locPt w γ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  have hm : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
    unfold UL
    split_ifs with hs
    · trivial
    · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 * γ.1 = 1 := γ.2
      show cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val *
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = 1
      have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hγ
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hs] at this
      simpa using this
  unfold locPt toSub
  rw [dite_eq_left hm]

theorem aeval_map_mat {n : ℕ} (w : Pl E) (M : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    aeval (M.map (algebraMap E (w.adicCompletion E))) (atPl w p) = (aeval M p).map (algebraMap E (w.adicCompletion E)) := by
  rw [atPl, aeval_map_algebraMap]
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E (w.adicCompletion E))) M p
  have e : (⇑(Algebra.ofId E (w.adicCompletion E)) : E → _) = algebraMap E _ := rfl
  simpa [AlgHom.mapMatrix_apply, e] using this

theorem kapSign_eq {n : ℕ} (w : Pl E) (hw : ¬ IsSplitAt w) (Q : (w.adicCompletion E)[X]) (γ : GLw n w) :
    kapSign n w Q γ = sgnOn (cj w) 1 Q γ.val := by
  unfold kapSign sgnOn gramOn hform
  rw [if_neg hw]
  simp [Matrix.one_apply]

theorem mem_S {S : Set (Pl E)} (hS : IsSection S) {w : Pl E} (hw : ¬ IsSplitAt w) : w ∈ S := by
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
  by_contra h
  exact hw ⟨u, fun e => h (e ▸ hu), hu'⟩

end GlobalTheory.UnitaryClasses
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
noncomputable section
namespace GlobalTheory.StabHaar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem isClosed_stabK (B : Base F E) {n : ℕ} (X : Spc F E n)
    (hL : IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E))) :
    IsClosed ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have h1 : IsClosed {g : UA σ X.J | ∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))
  have h2 : IsClosed {g : UA σ X.J | ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  exact h1.inter h2

end GlobalTheory.StabHaar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUTransport

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (UB incM incM_smul mt_gram continuous_conj continuous_conjU)

variable {D : D7}

theorem mem_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) :
    (GeneralLinearGroup.map (cA D) (show GL (Fin V.rank) (AE D) from x.1) : GL (Fin V.rank) (AE D)) ∈
      HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have e : ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D) =
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hx : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))ᵀ * incM J *
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM J := x.2
  show (((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D))ᵀ * incM V.gram *
    (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM V.gram
  rw [e]
  generalize (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = X at hx ⊢
  rw [h, incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D c⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul] at hx'
  exact hx'

def conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) : GA D V :=
  show HR (AF D.host.F) D.sp.cm.sig V.gram from ⟨_, mem_inv V c hc h x⟩

def conjEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* UB J where
  toFun := conjU V c h
  invFun := conjUInv V c hc h
  left_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  right_inv x := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show (mt V (a * b)).map (cA D) = (mt V a).map (cA D) * (mt V b).map (cA D)
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt, map_mul]

theorem continuous_conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjUInv V c hc h) := by
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_conj D)
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (continuous_conj D)

theorem cA_inclR (a : D.host.E) :
    cA D (inclR (F := D.host.F) (AF D.host.F) a) = inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig a) := rfl

theorem rat_fwd (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram)
    (γ : GA D V) (hγ : γ ∈ GQ V) : conjU V c h γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  obtain ⟨y, -, e⟩ := hγ
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) y, Units.ext ?_⟩
  have e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val e).symm
  show _ = (mt V γ).map (cA D)
  rw [e']
  ext i j
  exact (cA_inclR _).symm

theorem inclR_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem rat_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) : conjUInv V c hc h x ∈ GQ V := by
  obtain ⟨z, hz⟩ := hx
  have hz' : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val hz).symm
  set Z := (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E) with hZ
  have hY : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) =
      Z.map (inclR (F := D.host.F) (AF D.host.F)) := by
    rw [hz']; ext i j; exact cA_inclR _
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) z, ?_, Units.ext ?_⟩
  · have hm := mem_inv V c hc h x
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)) *
      JR (AF D.host.F) V.gram * (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = JR (AF D.host.F) V.gram at hm
    rw [hY] at hm
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact cA_inclR _
    rw [hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z = V.gram
    apply Matrix.map_injective inclR_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · show Z.map (inclR (F := D.host.F) (AF D.host.F)) = (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)
    exact hY.symm

def ratEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J ≃ GQ V where
  toFun γ := ⟨conjUInv V c hc h γ.1, rat_inv V c hc h γ.1 γ.2⟩
  invFun γ := ⟨conjU V c h γ.1, rat_fwd V c h γ.1 γ.2⟩
  left_inv γ := Subtype.ext ((conjEquiv V c hc h).right_inv γ.1)
  right_inv γ := Subtype.ext ((conjEquiv V c hc h).left_inv γ.1)

theorem map_isHaar_isFundamentalDomain : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure →
    IsFundamentalDomain (GQ V) fd ν →
    (ν.map (conjU V c h)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (conjU V c h '' fd) (ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := conjEquiv V c hc h
  have c1 : Continuous φ := continuous_conjU V c h
  have c2 : Continuous φ.symm := continuous_conjUInv V c hc h
  have hH : (ν.map φ).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ c1 c2
  refine ⟨hH, ?_⟩
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  let M := H.toMeasurableEquiv
  have hq : Measure.QuasiMeasurePreserving M.symm (ν.map M) ν :=
    (M.measurePreserving_symm ν).quasiMeasurePreserving
  refine hfd.image_of_equiv M.toEquiv hq (ratEquiv V c hc h) fun γ x => ?_
  show φ (φ.symm γ.1 * x) = γ.1 * φ x
  rw [map_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.ConjUTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_and_fundamentalDomain : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure →
    IsFundamentalDomain (GQ V) fd ν →
    (ν.map (conjU V c h)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (conjU V c h '' fd) (ν.map (conjU V c h)) := by
  first | exact @GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain | exact GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain | (intros; apply GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandra
noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecFinite

open GlobalTheory.CuspMult GlobalTheory.PRep

section Abstract

variable {H X : Type} [Group H] [TopologicalSpace H] [AddCommGroup X] [Module ℂ X]

theorem simple_asSubmodule {ρ : Representation ℂ H X} (U : Subrepresentation ρ) (hU : U.toRepresentation.IsIrreducible) :
    IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).1 hU
  exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U).symm

theorem exists_sub_equiv {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (h1 : σ.IsIrreducible) {f : W →ₗ[ℂ] X} (hf : ∀ g s, f (σ g s) = ρ g (f s)) (h0 : f ≠ 0) :
    ∃ U : Subrepresentation ρ, U.toSubmodule = LinearMap.range f ∧ Function.Injective f ∧
      ∃ e : W ≃ₗ[ℂ] U.toSubmodule, (∀ s, (e s : X) = f s) ∧ ∀ g s, e (σ g s) = U.toRepresentation g (e s) := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨F.range, rfl, hi, LinearEquiv.ofInjective f hi, fun s => rfl, fun g s => Subtype.ext (hf g s)⟩

theorem rank_homInto_lt {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X) (K : Subgroup H) (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) (h1 : σ.IsIrreducible)
    {x : W} (hx0 : x ≠ 0) (hx : ∀ k ∈ K, σ k x = x) : Module.rank ℂ (homInto σ ρ C) < Cardinal.aleph0 := by
  let ev : homInto σ ρ C →ₗ[ℂ] ↥(C ⊓ fixed ρ K) :=
    { toFun := fun f => ⟨(f : W →ₗ[ℂ] X) x, f.2.1 x, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← f.2.2, hx k hk]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    by_contra hne
    obtain ⟨U, -, hi, -⟩ := exists_sub_equiv h1 f.2.2 (fun h => hne (Subtype.ext h))
    have h0 : (f : W →ₗ[ℂ] X) x = (f : W →ₗ[ℂ] X) 0 := by
      rw [map_zero]
      exact congrArg Subtype.val hf
    exact hx0 (hi h0)
  haveI := FiniteDimensional.of_injective ev hinj
  exact Module.rank_lt_aleph0 ℂ _

theorem finite_classes (ρ : Representation ℂ H X) (C : Submodule ℂ X) (K : Subgroup H)
    (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) :
    ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (σs : ∀ i, Representation ℂ H (Ws i)),
      ((∀ i, (σs i).IsIrreducible) ∧ (∀ i, IsAdmissible (σs i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σs i).Equiv (σs j))) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → IsAdmissible σ →
        homInto σ ρ C ≠ ⊥ → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i)) := by
  classical
  let S : Set (Subrepresentation ρ) := {U | U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    IsAdmissible U.toRepresentation ∧ U.toSubmodule ⊓ fixed ρ K ≠ ⊥}
  let comp : Subrepresentation ρ → Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    fun U => isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule U.asSubmodule
  let T : Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) := comp '' S
  have hT : sSupIndep T := (sSupIndep_isotypicComponents (MonoidAlgebra ℂ H) ρ.asModule).mono (by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨U.asSubmodule, simple_asSubmodule U hU.2.1, rfl⟩)
  have hy : ∀ c : T, ∃ y : ↥(C ⊓ fixed ρ K), y ≠ 0 ∧
      ρ.asModuleEquiv.symm (y : X) ∈ (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := by
    rintro ⟨_, U, hU, rfl⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hU.2.2.2
    exact ⟨⟨y, hU.1 hy.1, hy.2⟩, fun h => hy0 (congrArg Subtype.val h), U.asSubmodule.le_isotypicComponent hy.1⟩
  choose y hy0 hyc using hy
  have hsm : ∀ (c : T) (a : ℂ), ρ.asModuleEquiv.symm ((a • y c : ↥(C ⊓ fixed ρ K)) : X) ∈
      (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := fun c a => by
    rw [Submodule.coe_smul, map_smul]
    exact Submodule.smul_of_tower_mem _ a (hyc c)
  have hli : LinearIndependent ℂ y := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have hx : ρ.asModuleEquiv.symm ((g i • y i : ↥(C ⊓ fixed ρ K)) : X) ∈
        (i : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ⊓ sSup (T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)}) := by
      refine ⟨hsm i (g i), ?_⟩
      have he : (g i • y i : ↥(C ⊓ fixed ρ K)) = - ∑ j ∈ s.erase i, g j • y j := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase s (fun j => g j • y j) hi, hs]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [he, Submodule.coe_neg, Submodule.coe_sum, map_neg, map_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      refine (le_sSup (show (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ∈ T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)} from
          ⟨j.2, fun h => Finset.ne_of_mem_erase hj (Subtype.ext h)⟩) :
        (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ≤ _) (hsm j (g j))
    rw [(hT i.2).eq_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff, Submodule.coe_eq_zero, smul_eq_zero] at hx
    exact hx.resolve_right (hy0 i)
  haveI : Finite T := hli.finite
  haveI := Fintype.ofFinite T
  let e := Fintype.equivFin T
  have hrep : ∀ c : T, ∃ U ∈ S, comp U = c := fun c => c.2
  choose U hUS hUc using hrep
  refine ⟨Fintype.card T, fun i => ↥(U (e.symm i)).toSubmodule, fun i => inferInstance, fun i => inferInstance,
    fun i => (U (e.symm i)).toRepresentation, ⟨fun i => (hUS _).2.1, fun i => (hUS _).2.2.1, fun i j hij => ⟨fun φ => hij ?_⟩⟩, ?_⟩
  · obtain ⟨ψ⟩ := (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).1 ⟨φ⟩
    have h3 := ((GlobalTheory.RepCount.subEquiv _).symm.trans (ψ.trans (GlobalTheory.RepCount.subEquiv _))).isotypicComponent_eq
      (M := ρ.asModule)
    exact e.symm.injective (Subtype.ext ((hUc _).symm.trans (h3.trans (hUc _))))
  · rintro W _ _ σ h1 h2 hne ⟨x, hx0, hx⟩
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨V, hV, hi, ev, hev, heq⟩ := exists_sub_equiv h1 hf.2 hf0
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).1 h1
    let ψ : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule :=
      LinearEquiv.ofBijective (GlobalTheory.RepCount.modMap ev.toLinearMap heq) ev.bijective
    have hVirr : V.toRepresentation.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).2 (IsSimpleModule.congr ψ.symm)
    have hVS : V ∈ S := by
      refine ⟨?_, hVirr, GlobalTheory.RepCount.isAdmissible_of_injective ev.symm.toLinearMap (fun g s => ?_) ev.symm.injective h2, ?_⟩
      · rw [hV]
        rintro _ ⟨s, rfl⟩
        exact hf.1 s
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, heq, LinearEquiv.apply_symm_apply]
      · rw [Submodule.ne_bot_iff]
        refine ⟨f x, ⟨hV ▸ ⟨x, rfl⟩, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← hf.2, hx k hk]⟩, fun h => hx0 (hi ?_)⟩
        rw [h, map_zero]
    refine ⟨e ⟨comp V, V, hVS, rfl⟩, ?_⟩
    show Nonempty (σ.Equiv (U (e.symm (e ⟨comp V, V, hVS, rfl⟩))).toRepresentation)
    generalize hc : e.symm (e ⟨comp V, V, hVS, rfl⟩) = c
    rw [Equiv.symm_apply_apply] at hc
    haveI := simple_asSubmodule V hVirr
    haveI := simple_asSubmodule (U c) (hUS c).2.1
    have hle : (U c).asSubmodule ≤ comp V :=
      ((U c).asSubmodule.le_isotypicComponent).trans_eq ((hUc c).trans (congrArg Subtype.val hc).symm)
    obtain ⟨χ⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule V.asSubmodule) _ hle
    exact (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).2
      ⟨(ψ.trans (GlobalTheory.RepCount.subEquiv V)).trans (χ.symm.trans (GlobalTheory.RepCount.subEquiv _).symm)⟩

end Abstract

theorem specFin : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation →
    SpecFin := by
  intro hQ hP hDM D V S M μ _ _
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hm : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ →
      mCuspDS μ σ M = Module.rank ℂ (homInto σ (finRep M) (allMaps θ M)) := fun W _ _ σ h =>
    (GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hQ hP hDM D θ hθ V S M μ W σ h.1).symm
  refine ⟨fun W _ _ σ h1 h2 => ?_, fun K hK => ?_⟩
  · haveI := GlobalTheory.CuspFactor.nontrivial_of_irr σ h1
    obtain ⟨x, hx0⟩ := exists_ne (0 : W)
    let St : Subgroup (GfC V) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          show σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          show σ a⁻¹ x = x
          conv_lhs => rw [← ha]
          simp }
    rw [hm W σ h2]
    exact rank_homInto_lt σ (finRep M) (allMaps θ M) St (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ St (h2.1 x)) h1 hx0
      (fun k hk => hk)
  · obtain ⟨n, Ws, i1, i2, σs, hs, hcov⟩ :=
      finite_classes (finRep M) (allMaps θ M) K (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
    refine ⟨n, Ws, i1, i2, σs, hs, fun W _ _ σ h1 h2 hm0 hx => hcov W σ h1 h2 (fun h => hm0 ?_) hx⟩
    rw [hm W σ h2, h, rank_bot]

end GlobalTheory.SpecFinite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandraStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_spectrum_finiteness_of_decay_harishChandra : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → SpecFin := by
  first | exact @GlobalTheory.SpecFinite.specFin | exact GlobalTheory.SpecFinite.specFin | (intros; apply GlobalTheory.SpecFinite.specFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU

theorem conj_div_norm_zpow (u : ℂ) (hu : u ≠ 0) (k : ℤ) :
    (starRingEnd ℂ u / ((‖starRingEnd ℂ u‖ : ℝ) : ℂ)) ^ (-k) = (u / ((‖u‖ : ℝ) : ℂ)) ^ k := by
  have h0 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hu)
  rw [Complex.norm_conj, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  rw [inv_div, div_eq_div_iff ((map_ne_zero _).2 hu) h0, Complex.mul_conj', sq]

theorem piInf_eq {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (w : InfinitePlace D.host.F)
    (h : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) y = starRingEnd ℂ (θ τ (infPart D y)) := by
  have hr : ∀ a : Ainf D.host.F, InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.AutFunCompare.evW w a) =
      starRingEnd ℂ (θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    intro a
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap D.host.F) a (isClosed_eq ?_ ?_) fun f => ?_
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
    · exact Complex.continuous_conj.comp (hθ τ).2
    · rw [(GlobalTheory.AutFunCompare.evW w).commutes]
      have e1 := InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm f)
      have e2 : θ τ (algebraMap D.host.F (Ainf D.host.F) f ⊗ₜ[D.host.F] (1 : D.host.E)) = tauE D τ (algebraMap D.host.F D.host.E f) := by
        rw [← (hθ τ).1, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
      rw [e2]
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]
      refine e1.trans ?_
      exact (RingHom.congr_fun h f).symm
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, map_add (starRingEnd ℂ)]
  | tmul a x =>
    have e : θ τ (fstA D.host.F a ⊗ₜ[D.host.F] x) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
      rw [← (hθ τ).1 x, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (a ⊗ₜ[D.host.F] x) =
        infEmb (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (evInf D.host.F w a ⊗ₜ[D.host.F] x) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, compInf, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    have l2 : infPart D (a ⊗ₜ[D.host.F] x) = fstA D.host.F a ⊗ₜ[D.host.F] x := by
      simp only [infPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rw [l1, l2, infEmb_tmul, e, map_mul, ← hr]
    rfl

end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

theorem finPart_eq_one {D : D7} (z : AE D) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (z - 1)) : finPart D z = 1 := by
  let u : AF D.host.F := ⟨0, 1⟩
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
    exact map_zero _
  have h1 := hz u hu0
  have key : ∀ y : AE D, finPart D (u • y) = finPart D y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | add a b ha hb => rw [smul_add, RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      simp only [finPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, smul_eq_mul, map_mul]
      congr 1
      show (1 : Af D.host.F) * sndA D.host.F a = sndA D.host.F a
      exact one_mul _
  rw [← sub_eq_zero, ← RingHom.map_one (finPart D), ← RingHom.map_sub, ← key, h1, RingHom.map_zero]
end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU


set_option maxHeartbeats 1000000 in
theorem hasExp_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  intro D c a ha τf hτf
  choose n hn hθ using ha
  refine ⟨fun w => -n (τf w), ?_, fun w => by push_cast; rw [hn]; ring⟩
  intro z hz
  have hf : finPart D (z : AE D) = 1 := finPart_eq_one _ hz
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ0 : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ0 (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ0 ρ hρ r1 r0
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  let zx : D.what₂.Tau → ℂˣ := fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom z
  have hzx : ∀ τ, ((zx τ : ℂˣ) : ℂ) = θ τ (infPart D (z : AE D)) := fun τ => rfl
  have hT : z = T.toHomUnits zx :=
    Units.ext (ext _ _ (hf.trans (tf _).symm) fun τ => (ti zx τ).symm)
  have single : ∀ τ (v : ℂˣ), ((c (T.toHomUnits (Pi.mulSingle τ v)) : Circle) : ℂ) =
      ((v : ℂ) / ((‖(v : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro τ v
    have h := (hθ τ).2 θ hθ0 (T.toHomUnits (Pi.mulSingle τ v)) (tf _) fun τ' hτ' => by
      show θ τ' (infPart D (t _)) = 1
      rw [ti, Pi.mulSingle_eq_of_ne hτ', Units.val_one]
    rw [h]
    show ((θ τ (infPart D (t _))) / ((‖θ τ (infPart D (t _))‖ : ℝ) : ℂ)) ^ n τ = _
    rw [ti, Pi.mulSingle_eq_same]
  have hprod : ((c z : Circle) : ℂ) = ∏ τ, ((zx τ : ℂ) / ((‖(zx τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    have e1 : T.toHomUnits zx = ∏ τ, T.toHomUnits (Pi.mulSingle τ (zx τ)) := by
      rw [← map_prod]; congr 1; exact (Finset.univ_prod_mulSingle zx).symm
    have e2 : ((c z : Circle) : ℂ) = Circle.coeHom (∏ τ, c (T.toHomUnits (Pi.mulSingle τ (zx τ)))) := by
      rw [← map_prod, ← e1, ← hT]; rfl
    rw [e2, map_prod]
    exact Finset.prod_congr rfl fun τ _ => single τ (zx τ)
  have hinj : Function.Injective τf := fun w1 w2 h => by
    have e : w1.embedding = w2.embedding := by rw [← hτf w1, ← hτf w2, h]
    rw [← InfinitePlace.mk_embedding w1, ← InfinitePlace.mk_embedding w2, e]
  have hbij : Function.Bijective τf := (Fintype.bijective_iff_injective_and_card τf).2
    ⟨hinj, (Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D)).symm⟩
  rw [hprod]
  symm
  refine Fintype.prod_bijective τf hbij _ _ fun w => ?_
  beta_reduce
  rw [piInf_eq θ hθ0 (τf w) w (hτf w), ← hzx]
  exact conj_div_norm_zpow _ (zx (τf w)).ne_zero _

end GlobalTheory.ConjInfExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExpStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  first | exact @GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp | exact GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp | (intros; apply GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp <;> assumption)
end
end
end
