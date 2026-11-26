module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LanglandsMultisegmentsOfSeg
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

noncomputable section
namespace GlobalTheory.RSPole

def schurDir (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' l : {l : Fin n → ℕ // Antitone l},
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)))

def eulD {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∏' w, schurDir (q w) (α w) x

def thetaZ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a)) (𝓕 : Set (GA E a))
    (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (x : ℝ) : ℂ :=
  ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ φ' Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
    ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ

end GlobalTheory.RSPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreRationalFormsSubsetCoverForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlaces
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUpInt

theorem valuation_lt_one_iff {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    la.valuation K x < 1 ↔ 0 < vLa la x := by
  have h0 : la.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [vLa]
  omega

theorem overLa_comp {K K₂ : Type} [Field K] [NumberField K] [Field K₂] [NumberField K₂] (i : K →+* K₂)
    {la : HeightOneSpectrum (𝓞 K)} {la₂ : HeightOneSpectrum (𝓞 K₂)}
    (h : ∀ x : 𝓞 K, x ∈ la.asIdeal ↔ la₂.valuation K₂ (i x) < 1) {T : CDVR} {io₂ : K₂ →+* T.Fr} {e₂ : ℕ}
    (ho : OverLa la₂ T.V io₂ e₂) : ∃ e, OverLa la T.V (io₂.comp i) e := by
  obtain ⟨N, hN, hp⟩ := GlobalTheory.IntCoefExt.exists_nat_pos ho
  obtain ⟨la', e, ho'⟩ := GlobalTheory.IntCoefExt.exists_overLa (io₂.comp i) hN hp
  obtain rfl : la' = la := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp
    have hx' : (x : K) ≠ 0 := by simpa using hx
    have e1 := ho'.2 (x : K)
    rw [RingHom.comp_apply, ho.2] at e1
    rw [h, valuation_lt_one_iff la₂ ((map_ne_zero i).2 hx'), ← la'.valuation_lt_one_iff_mem (K := K)]
    refine (valuation_lt_one_iff la' hx').trans ?_
    have p1 : (0 : ℤ) < e := by exact_mod_cast ho'.1
    have p2 : (0 : ℤ) < e₂ := by exact_mod_cast ho.1
    rw [← mul_pos_iff_of_pos_left p1, ← e1, mul_pos_iff_of_pos_left p2]
  exact ⟨e, ho'⟩

theorem pull_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, (∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ la₂ ∈ S₂, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la₂, 0 ≤ v f₂ := by
  intro D T hT j hj σ _ C _ a n _ S S₂ hS f _ hint f₂ _ hP la₂ hla₂ v hv
  obtain ⟨⟨q, T', io₂, e₂, ho, y₂, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨la, hla, hl⟩ := hS la₂ hla₂
  obtain ⟨e, ho'⟩ := overLa_comp C.inc hl ho
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    intro e
    have h1 := GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj
    obtain ⟨k, hk⟩ := r_odd D
    omega
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have hO := GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d
  have hK : KA T.Q.l ≤ KA C.d.l₂ := GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _
  let io' : C.c'.F →+* T'.Fr := io₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  let io : T.Q.c.F →+* T'.Fr := io₂.comp C.inc
  have hio : ∀ x, io' (incF T.Q.c C.c' C.hle x) = io x := fun _ => rfl
  letI := io₂.toAlgebra
  letI := io'.toAlgebra
  letI := io.toAlgebra
  obtain ⟨y', hy'⟩ := GlobalTheory.CovPull.below_exists C.d hO hK (S := T'.Fr) (fun _ => rfl) y₂.1
  let y : IntFr (T.Q.Xo j) T.Q.c T' io := ⟨y'.res C.hle hio, GlobalTheory.TransferCompare.allTest_framed _ _ _ _,
    (GlobalTheory.IntCoefExt.integral_res_iff C.hle T' io' io hio _).1
      (GlobalTheory.CoverDown.integral_below C.d T' io' io₂ (fun _ => rfl) y' y₂.1 hy' y₂.2.2)⟩
  have e1 : evI y₂ f₂ = evI y f := hP T'.Fr hio (fun _ => rfl) y₂.1 y' hy'
  have key := hint la hla _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho' y hy () trivial, rfl⟩
  refine (GlobalTheory.IntCoefExt.nval_nonneg_iff ho.1 _).2 ?_
  rw [e1]
  exact (GlobalTheory.IntCoefExt.nval_nonneg_iff ho'.1 _).1 key

end GlobalTheory.CoverUpInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlacesStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_pullback_uniformisedLevelCover_places : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, (∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ la₂ ∈ S₂, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la₂, 0 ≤ v f₂ := by
  first | exact @GlobalTheory.CoverUpInt.pull_integral | exact GlobalTheory.CoverUpInt.pull_integral | (intros; apply GlobalTheory.CoverUpInt.pull_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreRationalFormsSubsetCoverForms
set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUp

theorem baseForms_sub_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → baseForms T j σ a n ⊆ C.ratForms a n ∧ ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → baseInt T j σ a n S ⊆ C.intForms a n S₂ := by
  intro D T hL j hj σ hσ C hU a n hD hP
  constructor
  · intro x hx
    obtain ⟨f, ⟨hf, hh⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨hf₂, GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩
  · intro S S₂ hS
    intro x hx
    obtain ⟨f, ⟨hf, hh, hi⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨⟨hf₂, GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩,
      GlobalTheory.T.integral_pullback_uniformisedLevelCover_places D T hL j hj σ hσ C hU a n hD S S₂ hS f hf hi f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩

end GlobalTheory.CoverUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreRationalFormsSubsetCoverFormsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreRationalForms_subset_coverForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → baseForms T j σ a n ⊆ C.ratForms a n ∧ ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → baseInt T j σ a n S ⊆ C.intForms a n S₂ := by
  first | exact @GlobalTheory.CoverUp.baseForms_sub_cover | exact GlobalTheory.CoverUp.baseForms_sub_cover | (intros; apply GlobalTheory.CoverUp.baseForms_sub_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestriction
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFormDesc

theorem mem_span_of_image_mem_span {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M] {W : Type}
    [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (R : M →ₛₗ[σ] W) (S : Submodule K M)
    (hinj : ∀ (m : ℕ) (f : Fin m → M), (∀ i, f i ∈ S) → LinearIndependent K f → LinearIndependent ℂ (fun i => R (f i)))
    {k : ℕ} (g : Fin k → M) (hg : ∀ i, g i ∈ S) (f₂ : M) (hf : f₂ ∈ S)
    (hφ : R f₂ ∈ Submodule.span ℂ (Set.range fun i => R (g i))) : ∃ c : Fin k → K, ∑ i, c i • g i = f₂ := by
  refine (Submodule.mem_span_range_iff_exists_fun K).mp ?_
  by_contra hno
  set G := Submodule.span K (Set.range g) with hG
  haveI : FiniteDimensional K G := FiniteDimensional.span_of_finite _ (Set.finite_range g)
  let b := Module.finBasis K G
  let v : Fin (Module.finrank K G) → M := fun i => (b i : M)
  have hvsp : Submodule.span K (Set.range v) = G := by
    have : Set.range v = G.subtype '' Set.range b := by
      ext x; simp [v]
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent K (Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) := by
    rw [linearIndependent_finCons]
    exact ⟨b.linearIndependent.map' G.subtype (Submodule.ker_subtype G), by rwa [hvsp]⟩
  have hsecG : G ≤ S := by
    rw [hG, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hg i
  have hin : ∀ i, (Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) i ∈ S := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hsecG (b i).2
  have hC := hinj _ _ hin hli
  have hfun : (fun i => R ((Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) i)) =
      Fin.cons (R f₂) (fun i => R (v i)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hfun, linearIndependent_finCons] at hC
  apply hC.2
  have hG' : ∀ x ∈ G, R x ∈ Submodule.span ℂ (Set.range fun i => R (v i)) := by
    intro x hx
    rw [← hvsp] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.mpr ?_ hφ
  rintro _ ⟨i, rfl⟩
  exact hG' _ (Submodule.subset_span ⟨i, rfl⟩)

def rdL {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))

theorem rd_eq {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : Rul C.d.Xo₂ C.d.c₂) : C.rd a f = rdL C a f := rfl

theorem cover_form_desc : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j σ) → ℂ)), (∀ i, ψ i ∈ baseForms T j σ a n) ∧ φ = ∑ i, C.σ₂ (x i) • ψ i := by
  intro D T hL j hj σ hσ C hU a n hD hP hspan hmu φ hφ hφK
  have hsp : φ ∈ Submodule.span ℂ (baseForms T j σ a n) := GlobalTheory.T.coverForm_levelInvariant_mem_span_baseForms D T hL j hj σ hσ C hU a n hD hP hspan hmu φ hφ hφK
  obtain ⟨f₂, ⟨hf₂s, -⟩, rfl⟩ := hφ
  obtain ⟨m, z, ψ, hψ⟩ := Submodule.mem_span_set'.mp hsp
  have hup := (GlobalTheory.T.coreRationalForms_subset_coverForms D T hL j hj σ hσ C hU a n hD hP).1
  choose g hg hgψ using fun i => hup (ψ i).2
  have hinj : ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) →
      LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => rdL C a (f i)) :=
    fun m f hf hli => GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hP.1 a n hD m f hf hli
  have hmem : rdL C a f₂ ∈ Submodule.span ℂ (Set.range fun i => rdL C a (g i)) := by
    rw [← rd_eq, ← hψ]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [← hgψ i, rd_eq]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := mem_span_of_image_mem_span C.σ₂ (rdL C a) (sec C.d.Xo₂ C.d.c₂ a n) hinj g (fun i => (hg i).1) f₂ hf₂s hmem
  refine ⟨m, c, fun i => (ψ i : GA D (T.V j σ) → ℂ), fun i => (ψ i).2, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc, rd_eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, ← rd_eq, hgψ i]

end GlobalTheory.CoverFormDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_sections_span_restriction : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j σ) → ℂ)), (∀ i, ψ i ∈ baseForms T j σ a n) ∧ φ = ∑ i, C.σ₂ (x i) • ψ i := by
  first | exact @GlobalTheory.CoverFormDesc.cover_form_desc | exact GlobalTheory.CoverFormDesc.cover_form_desc | (intros; apply GlobalTheory.CoverFormDesc.cover_form_desc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

open scoped ComplexOrder Topology
noncomputable section
namespace GlobalTheory.SmoothVac
variable {D : D7}

theorem comm_compAt_one (W : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    s * compAt θ τ (Formalism.L2.Theta.mt W 1) = compAt θ τ (Formalism.L2.Theta.mt W 1) * s := by
  have h1 : Formalism.L2.Theta.mt W 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, compAt, Matrix.map_one _ (by simp) (by simp), Matrix.one_mul, Matrix.mul_one]

theorem isCartanInv_one (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem exists_ne_zero_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT LS LT f) : ∃ w, f w ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have := hn p hp
  have h0 : f = 0 := funext h
  rw [h0] at this
  simp [nrm2] at this

theorem finCong_of_mul_left {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V a k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨b • y, nsmul_mem hy b, by rw [e, mul_smul]⟩

theorem finCong_of_mul_right {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V b k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨a • y, nsmul_mem hy a, by rw [e, mul_comm, mul_smul]⟩

theorem isOpen_comap_St (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    IsOpen (((Formalism.L2.DIV.St β).comap ((Formalism.UG.bc (Lev.swapAE D)).comp (Bridge.Gf V).subtype) :
      Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β ∅ (continuous_subtype_val (p := fun x => x ∈ Bridge.Gf V)) rfl]
    with x hh
  exact hh.1


set_option maxHeartbeats 1000000 in
theorem isOpen_map_levelGroup (V : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup V N).map (finHom V).rangeRestrict : Subgroup (Bridge.Gf V)) :
      Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, -, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have hc : Continuous fun x : Bridge.Gf V => ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : Bridge.Gf V | ∃ y ∈ latHat V,
      ((k : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
        Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ GlobalTheory.AdLat.fv D.host.F x -
        GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : Bridge.Gf V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx := GlobalTheory.Member.PrincLevel.continuous_mulVec_sub hc (GlobalTheory.AdLat.fv D.host.F x)
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨g, hg⟩ := x.2
  refine ⟨GlobalTheory.LevelNbhd.finPartG V g, ⟨GlobalTheory.LevelNbhd.finPartG_mem_GfC V g, ?_⟩, ?_⟩
  · unfold GlobalTheory.Member.FinCong
    rw [GlobalTheory.LevelNbhd.finHom_finPartG, hg]
    rw [h1] at hx ⊢
    exact GlobalTheory.Member.PrincLevel.cong_of_gen _ _ hLS _ N fun s hs => hx s hs
  · exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, GlobalTheory.LevelNbhd.finHom_finPartG, hg])

theorem om_pow_eq {V W : HSp D} (ω : PairRep V W) (k : GA D V) (f : WO V W → ℂ) (c : ℂ) (hc : ω (k, 1) f = c • f) :
    ∀ m : ℕ, ω (k ^ m, 1) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : ((k ^ (m + 1), (1 : GA D W)) : GA D V × GA D W) = (k ^ m, 1) * (k, 1) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

end GlobalTheory.SmoothVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExhaustionGLHolds
theorem GlobalTheory.langlandsExhaustionGL_holds : GlobalTheory.Published.LanglandsExhaustionGL :=
  CompanionTheory.Exh.langlandsExhaustionGL_of_seg CompanionTheory.RgGu.segmentRepresentation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramified
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut

namespace GlobalTheory.UnrNoChi

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem chi_one_eq_one (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ)
    {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨-, e, he⟩ := hρ
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  simp only [hγ, Units.val_one, Matrix.map_one (toK D.nd i) (map_zero _) (map_one _), Matrix.one_mulVec, hu,
    LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

end GlobalTheory.UnrNoChi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
namespace GlobalTheory

theorem genericUnlinkedGL_outright : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem gl_lc_sc (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ SecondCountableTopology (GL (Fin r) F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem gl_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  intro F E _ _ _ _ hU r M
  haveI : LocallyCompactSpace F := hU.lcF
  obtain ⟨h1, h2⟩ := gl_lc_sc F r
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  have hmod : ∀ a : GL (Fin r) F, Measure.modularCharacterFun a = 1 := by
    intro a
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center
      (Measure.modularCharacter : GL (Fin r) F →* NNReal) (fun z hz => ?_) a
    change Measure.modularCharacterFun z = 1
    have e : Measure.map (fun x : GL (Fin r) F => x * z)
        (Measure.haar : Measure (GL (Fin r) F)) = Measure.haar := by
      rw [show (fun x : GL (Fin r) F => x * z) = fun x => z * x from
        funext fun x => (hz x).symm, map_mul_left_eq_self]
    rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (GL (Fin r) F)) z]
    simp only [e, Measure.haarScalarFactor_self]
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, hmod, one_smul]

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramifiedStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.gl_unimodular | exact GlobalTheory.JR.gl_unimodular | (intros; apply GlobalTheory.JR.gl_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

section H

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secRow_eq_rowMat {R : Type} [CommRing R] (y : Fin (m + 1) → R) :
    secRow y = GlobalTheory.RSTheta.rowMat (Fin.last m) y := by
  ext i j
  simp only [secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by simpa using e)))]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secInv_eq_inv_rowGL {y : Fin (m + 1) → Cinf E} (hy : y ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m)) :
    secInv y = (GlobalTheory.RSTheta.rowGL (Fin.last m) y)⁻¹ := by
  have hu := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hy
  have hd : IsUnit (secRow y).det := by rw [secRow_eq_rowMat, GlobalTheory.RSTheta.det_rowMat]; exact hu
  rw [secInv, dite_eq_left hd]
  congr 1
  apply Units.ext
  rw [GlobalTheory.RSTheta.val_rowGL hu, ← secRow_eq_rowMat]
  rfl

theorem continuous_yInf : Continuous (yInf : GA E (m + 1) → Fin (m + 1) → Cinf E) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp
    (Units.continuous_val.matrix_elem (Fin.last m) i)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_sqrtC {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) : Continuous (sqrtC Φ) :=
  Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (Complex.continuous_re.comp hΦ))

theorem lastRow_mul_of_row {h g : GA E (m + 1)}
    (hr : ∀ l, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply, hr]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem blkU_lastRow {r : ℕ} (hr : r ≤ m) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) (l : Fin (m + 1)) :
    ((blkU x : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change (1 + posM Subtype.val x : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, -⟩
  have h1 : (t.1.1 : ℕ) = m := by rw [e1]; simp
  have h2 := t.2.1
  omega

omit [_root_.NumberField.IsTotallyComplex E] in
theorem ratGL_lastRow {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) (l : Fin (m + 1)) :
    ((ratGL E (m + 1) γ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change algebraMap E (Ad E) (γ.val (Fin.last m) l) = _
  rw [hγ (Fin.last m) l (Or.inl (by simp))]
  by_cases h : Fin.last m = l
  · simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h]

theorem continuous_fT {φ : GA E (m + 1) → ℂ} (hφ : Continuous φ) {Φ : (Fin (m + 1) → Cinf E) → ℂ}
    (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m)) : Continuous (fT φ Φ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hp : yInf g ∈ tsupport Φ
  · have hU : GlobalTheory.RSTheta.rowSet E (Fin.last m) ∈ nhds (yInf g) :=
      (GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds (hs hp)
    have hc : ContinuousOn (fun u => infGL E (m + 1) (secInv u)) (GlobalTheory.RSTheta.rowSet E (Fin.last m)) := by
      refine (GlobalTheory.RSTheta.continuousOn_inv_rowGL (E := E) (Fin.last m)).congr fun u hu => ?_
      simp only [secInv_eq_inv_rowGL hu, map_inv]
    have h1 : ContinuousAt (fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv (yInf g))) g :=
      continuousAt_id.mul ((hc.continuousAt hU).comp continuous_yInf.continuousAt)
    exact (hφ.continuousAt.comp h1).mul ((continuous_sqrtC hΦ).comp continuous_yInf).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuous_yInf.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [fT, sqrtC, hq]

end H

theorem good_fT : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  intro E _ _ _ m φ hφ hl hv Φ hΦ hs ψ
  refine ⟨continuous_fT hφ hΦ hs, ?_, ?_, ?_⟩
  · intro γ hγ g
    rw [fT_of_lastRow (lastRow_mul_of_row (ratGL_lastRow hγ)), mul_assoc, hl, fT]
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have e : (fun x : UnipotentBlockColumnIndex (m + 1) r m → Ad E => fT φ Φ (blkU x * g)) = fun x =>
        sqrtC Φ (yInf g) * φ (blkU x * (g * infGL E (m + 1) (secInv (yInf g)))) := by
      funext x
      rw [fT_of_lastRow (lastRow_mul_of_row (blkU_lastRow hrm x)), mul_comm, mul_assoc]
    rw [e, avg_const_mul, hv r hr hrm, mul_zero]

end GlobalTheory.ZUnf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTopStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  first | exact @GlobalTheory.ZUnf.good_fT | exact GlobalTheory.ZUnf.good_fT | (intros; apply GlobalTheory.ZUnf.good_fT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate Matrix

namespace GlobalTheory.ZUnfTheta

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem continuous_secRow {n : ℕ} :
    Continuous (fun y : Fin n → Cinf E => secRow y) := by
  refine continuous_matrix fun i j => ?_
  simp only [secRow, Matrix.of_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

theorem continuousOn_secInv {n : ℕ} :
    ContinuousOn (fun y : Fin n → Cinf E => secInv y) {y | IsUnit (secRow y).det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        ((secInv y.1 : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = (secRow y.1)⁻¹ := fun y => by
      rw [secInv, dite_eq_left (show IsUnit (secRow y.1).det from y.2), Matrix.coe_units_inv]
      rfl
    have hc : Continuous fun y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow y.1 :=
      continuous_secRow.comp continuous_subtype_val
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hinv : ContinuousAt Ring.inverse (secRow y.1).det := by
      have := NormedRing.inverse_continuousAt y.2.unit
      simpa using this
    have h2 : ContinuousAt (fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => (secRow z.1)⁻¹) y :=
      (continuousAt_matrix_inv _ hinv).comp (f := fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1)
        hc.continuousAt
    convert h2 using 1
    funext z
    exact h1 z
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        (((secInv y.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = secRow y.1 := fun y => by
      rw [secInv, dite_eq_left (show IsUnit (secRow y.1).det from y.2), inv_inv]
      rfl
    convert (continuous_secRow.comp continuous_subtype_val :
      Continuous fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1) using 1
    funext z
    exact h1 z

variable {m : ℕ}

theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  have h : natLat E N =
      (fun u : Af E => (N : Af E) * u) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [h]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

theorem continuous_lastRow : Continuous fun g : GA E (m + 1) => GlobalTheory.ZEul.lastRow g :=
  continuous_pi fun j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem (Fin.last m) j

theorem continuous_yInfRow : Continuous fun g : GA E (m + 1) => fun i => pInf E (GlobalTheory.ZEul.lastRow g i) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_lastRow)

theorem measurable_mulSec :
    Measurable fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
  have hy := continuous_yInfRow (E := E) (m := m)
  set s := {g : GA E (m + 1) | IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g i)).det} with hsdef
  have hs : IsOpen s := Units.isOpen.preimage ((continuous_secRow.comp hy).matrix_det)
  refine measurable_of_restrict_of_restrict_compl hs.measurableSet ?_ ?_
  · have hc : ContinuousOn (fun g : GA E (m + 1) =>
        g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) s :=
      continuousOn_id.mul (GlobalTheory.ConstTermSmooth.continuous_infGL.comp_continuousOn
        (continuousOn_secInv.comp hy.continuousOn fun g hg => hg))
    exact hc.restrict.measurable
  · convert (measurable_subtype_coe : Measurable (Subtype.val : (sᶜ : Set (GA E (m + 1))) → GA E (m + 1))) using 1
    funext g
    have hg : ¬ IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)).det := g.2
    show g.1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)) = g.1
    rw [secInv, dite_eq_right hg, map_one, mul_one]

theorem measurable_integrand {φ φ' : GA E (m + 1) → ℂ} (hφ : Measurable φ) (hφ' : Measurable φ')
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) (N : ℕ) (x : ℝ) :
    Measurable fun g : GA E (m + 1) => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) := by
  have hh := measurable_mulSec (E := E) (m := m)
  have hy := continuous_yInfRow (E := E) (m := m)
  have hI : Measurable fun g : GA E (m + 1) => indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    have hS : IsClosed {g : GA E (m + 1) | ∀ i : Fin (m + 1),
        GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => (isClosed_natLat N).preimage
        (((continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp ((continuous_apply i).comp continuous_lastRow)).sub
          continuous_const)
    unfold indN
    exact Measurable.ite hS.measurableSet measurable_const measurable_const
  have hD : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ) := by
    unfold detPow chiDet
    exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.comp
      ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det)))
  unfold Psi
  exact ((((hφ.comp hh).mul (Complex.continuous_conj.measurable.comp (hφ'.comp hh))).mul
    (hΦ.measurable.comp hy.measurable)).mul hI).mul hD.measurable

end GlobalTheory.ZUnfTheta

set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.ZUnfTheta.zint_eq_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  intro E _ _ _ m μ _ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hφm hφ'm hφ hφ' N Φ hΦ x hfin
  set l : Fin (m + 1) := Fin.last m with hl
  let F : GA E (m + 1) → (Fin (m + 1) → Ad E) → ℂ := fun g y => Psi φ φ' Φ N g y * (detPow E (m + 1) x g : ℂ)
  have hv : (Pi.single l 1 : Fin (m + 1) → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin (m + 1)) E,
      γ ∈ mirU E (m + 1) m ↔ (Pi.single l 1 : Fin (m + 1) → E) ᵥ* γ.val = Pi.single l 1 := fun γ => by
    rw [mem_mirU_last, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
    exact Iff.rfl
  have he : ∀ g : GA E (m + 1),
      (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E)) ᵥ* g.val = GlobalTheory.ZEul.lastRow g := fun g => by
    have h1 : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E) = Pi.single l 1 := by
      funext j
      simp only [Function.comp_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [h1, Matrix.single_one_vecMul]
    rfl
  have hF : ∀ γ g y, F (ratGL E (m + 1) γ * g) y = F g y := fun γ g y => by
    simp only [F, Psi, mul_assoc (ratGL E (m + 1) γ) g, hφ, hφ', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  have hm : Measurable fun g => F g (GlobalTheory.ZEul.lastRow g) := GlobalTheory.ZUnfTheta.measurable_integrand hφm hφ'm hΦ N x
  have h𝓕P' : IsFundamentalDomain ((mirU E (m + 1) m).map (ratGL E (m + 1))) 𝓕P μ := h𝓕P
  have hlin := GlobalTheory.ThetaUnfold.lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' (fun g y => ‖F g y‖ₑ)
    (fun γ g y => by simp only [hF]) (by simp only [he]; exact hm.enorm.aemeasurable)
  have hfin' : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0},
      ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤ := by
    rw [hlin]
    simpa only [he] using hfin
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.ThetaUnfold.integral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' F hF
    (by simp only [he]; exact hm.aestronglyMeasurable) hfin'
  simp only [he] at hint
  unfold Zint thetaSum
  rw [← hint]
  congr 1
  funext g
  rw [← tsum_mul_right]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrothendieckRingPolynomialOutright
namespace GlobalTheory

theorem grothendieckRingPolynomial_outright : GlobalTheory.Published.GrothendieckRingPolynomial :=
  CompanionTheory.Groth.grothendieckRingPolynomial_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletion
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem GlobalTheory.WeilDeligne.WDRep.rho_apply_of_mk_eq_lpOfChar {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {n : ℕ} (b : WDRep h (Fin n → ℂ)) (χ : Weil h →* ℂˣ) (hχ : WeilDeligne.IsSmooth χ)
    (hb : WD.mk b = WD.lpOfChar h χ hχ) (σ : Weil h) (v : Fin n → ℂ) : b.ρ σ v = (χ σ : ℂ) • v := by
  obtain ⟨e, h1, -⟩ := WD.mk_eq_mk.1 hb
  apply e.injective
  rw [h1, map_smul]
  ext k
  simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def kSpan : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (G : GA E a → ℂ), GlobalTheory.JSW.IsRapidInf ν k γ ∧ Good G ∧
      F = fun g => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν}

end GlobalTheory.MSpanDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSegmentPolynomialOfHasSupport
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open Classical

noncomputable section

namespace GlobalTheory.LocGL.ZelevinskyExpansion

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem msupp_eq_of_isL {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    (hπ : π.IsIrreducible) {𝔫 : Multiset (Segment k)} (h𝔫 : IsL 𝔫 π) {s : Multiset (IrrGL (k := k))}
    (hs : HasSupport π s) : msupp 𝔫 = s := by
  obtain ⟨h, y, hd, ⟨D, ⟨hD, -⟩, hz⟩, hcos⟩ := h𝔫
  have hsy : HasSupport π (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hz i).hasSupport) hπ hcos.isSubquotient
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique CompanionTheory.Exh.geometricLemmaGL
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hsy hs
  rw [← heq, msupp, ← hD, Multiset.bind_map]
  rfl

end GlobalTheory.LocGL.ZelevinskyExpansion
end
end
