module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGenEqOneOfFrOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorSixth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolCompact

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf' {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_second (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

end GlobalTheory.PolCompact

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedExponent
noncomputable section

namespace GlobalTheory.BotLValue

section General

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

end General

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.L2.Host (aboveF)

open NumberField IsDedekindDomain in
private theorem eq_or_eq_of_comp_eq_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (ψ : F →+* ℂ)
    (ρ α β : E →+* ℂ) (hρ : ρ.comp (algebraMap F E) = ψ) (hα : α.comp (algebraMap F E) = ψ)
    (hβ : β.comp (algebraMap F E) = ψ) (hαβ : α ≠ β) : ρ = α ∨ ρ = β := by
  classical
  letI : Algebra F ℂ := ψ.toAlgebra
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let mk : ∀ γ : E →+* ℂ, γ.comp (algebraMap F E) = ψ → E →ₐ[F] ℂ := fun γ hγ =>
    { toRingHom := γ
      commutes' := fun a => (congrArg (fun f : F →+* ℂ => f a) hγ : _) }
  have hcoe : ∀ (γ : E →+* ℂ) (hγ : γ.comp (algebraMap F E) = ψ), ((mk γ hγ : E →ₐ[F] ℂ) : E →+* ℂ) = γ :=
    fun γ hγ => rfl
  by_contra hne
  push_neg at hne
  have hcard := AlgHom.card F E ℂ
  rw [h2] at hcard
  have hfa : mk ρ hρ ≠ mk α hα := fun e => hne.1 (by rw [← hcoe ρ hρ, ← hcoe α hα, e])
  have hfb : mk ρ hρ ≠ mk β hβ := fun e => hne.2 (by rw [← hcoe ρ hρ, ← hcoe β hβ, e])
  have hab : mk α hα ≠ mk β hβ := fun e => hαβ (by rw [← hcoe α hα, ← hcoe β hβ, e])
  have h3 : ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfa, hfb]), Finset.card_pair hab]
  have := Finset.card_le_univ ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ))
  omega


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.BotLValue.isCMType_embOver {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, _root_.GlobalTheory.AdelicU.EmbOver E w) :
    _root_.GlobalTheory.CMVal.IsCMType fun w => (τ w).1 := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at h
  obtain ⟨hF, hE, h2, hσ⟩ := h
  unfold _root_.GlobalTheory.CMVal.IsCMType
  have hreal : ∀ v : InfinitePlace F, ComplexEmbedding.conjugate v.embedding = v.embedding :=
    fun v => ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hF.isReal v))
  have hconj : ∀ (v : InfinitePlace F) (γ : E →+* ℂ), γ.comp (algebraMap F E) = v.embedding →
      (ComplexEmbedding.conjugate γ).comp (algebraMap F E) = v.embedding := by
    intro v γ hγ
    rw [← hreal v, ← hγ]
    rfl
  have hτ : ∀ v : InfinitePlace F, ((τ v).1).comp (algebraMap F E) = v.embedding := fun v => (τ v).2
  have hne : ∀ v : InfinitePlace F, (τ v).1 ≠ ComplexEmbedding.conjugate (τ v).1 := by
    intro v e
    have hc := hE.isComplex (InfinitePlace.mk (τ v).1)
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff] at hc
    exact hc e.symm
  intro ρ
  set v := InfinitePlace.mk (ρ.comp (algebraMap F E)) with hvdef
  have hv : ρ.comp (algebraMap F E) = v.embedding := by
    rcases InfinitePlace.embedding_mk_eq (ρ.comp (algebraMap F E)) with e | e
    · exact e.symm
    · rw [← hreal v, e]
      exact (star_star _).symm
  refine ⟨v, eq_or_eq_of_comp_eq_of_finrank_two h2 v.embedding ρ _ _ hv (hτ v) (hconj v _ (hτ v)) (hne v), ?_⟩
  intro w hw
  have hw' : ρ.comp (algebraMap F E) = w.embedding := by
    rcases hw with e | e
    · rw [e]; exact hτ w
    · rw [e]; exact hconj w _ (hτ w)
  rw [hvdef, hw', InfinitePlace.mk_embedding]

end GlobalTheory.BotLValue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option synthInstance.maxHeartbeats 100000 in
theorem cuspOn_fd_and_span_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x h Z σ hσ a n hD hpos hn
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · haveI := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]; exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z
    have e : goodOf c σ = σ := if_pos hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_pos]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact AllWt.rdU_mul (U σ) _ _

end GlobalTheory.FlatCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpannedStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x h Z σ hσ a n hD hpos hn
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · have := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]
      exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z
    have e : goodOf c σ = σ := ite_eq_left hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dite_eq_left]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]
      exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact GlobalTheory.AllWt.rdU_mul (U σ) _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.ConjNorm

open GlobalTheory.ConjInner

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)


set_option maxHeartbeats 1000000 in
theorem inner_reading_conj_at (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i)
    (hB : JEvBarAt T R κ i σ hV) :
    ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
      starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have h1 := (hT i σ hσ hV).1 hB
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R he i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

theorem norm_eq_of_inner_conj {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {x : H} {y : H'} (h : ⟪x, x⟫_ℂ = starRingEnd ℂ ⟪y, y⟫_ℂ) : ‖y‖ = ‖x‖ := by
  rw [inner_conj_symm] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h]


set_option maxHeartbeats 1000000 in
theorem norm_conj_of_not_good (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (hu : R.LUnif)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (x : Fin (R.nW i) → D.what₂.LL) :
    ‖(R.FW i).j ((starRingEnd ℂ).comp σ) x‖ = ‖(R.FW i).j σ x‖ := by
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hB : JEvBarAt T R κ i σ hV
  · exact norm_eq_of_inner_conj (inner_reading_conj_at T R κ v₀ he fw hE hT i σ hσ hV hB x x)
  · have h0 := (hT i σ hσ hV).2 hB
    have hx : x = 0 := by
      by_contra hx
      have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
      have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
      rw [h0] at h2
      exact h2 rfl
    subst hx
    rw [map_zero, map_zero, norm_zero, norm_zero]


omit R in
theorem not_good_conj {σ : D.what₂.LL →+* ℂ} (h : GoodEmb T.Q.c (res T σ)) :
    ¬ GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := by
  have key : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
      {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {s : c.F →+* ℂ}, GoodEmb c s →
      ¬ GoodEmb c ((starRingEnd ℂ).comp s) := by
    intro E _ _ _ H l c s h h'
    have h2 : starRingEnd ℂ H.rt0 = H.rt0 := by
      conv_lhs => rw [← h]
      exact h'
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
    have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h3
    nlinarith [mul_self_nonneg H.rt0.re]
  exact key T.Q.c h

end GlobalTheory.ConjNorm


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ConjNorm.pConj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ fw : FWTie T R κ v₀, BarTie fw → R.LUnif → R.PConj := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ fw hT hu i σ x
  have hE := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hu
  have key : ∀ σ, ¬ GoodEmb T.Q.c (res T σ) → (R.FW i).nrmAt ((starRingEnd ℂ).comp σ) x = (R.FW i).nrmAt σ x :=
    fun σ hσ => GlobalTheory.ConjNorm.norm_conj_of_not_good T R κ v₀ hC.models.HW fw hE hT hu i σ hσ x
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · have h1 := key _ (GlobalTheory.ConjNorm.not_good_conj T hσ)
    have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
    exact h1.symm.trans (congrArg (fun s => (R.FW i).nrmAt s x) e)
  · exact key σ hσ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicForm_norm_eq_at_conjugateEmbedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ fw : FWTie T R κ v₀, BarTie fw → R.LUnif → R.PConj := by
  first | exact @GlobalTheory.ConjNorm.pConj | exact GlobalTheory.ConjNorm.pConj | (intros; apply GlobalTheory.ConjNorm.pConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LocalWeilHom

theorem tens_cancel {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    {R : (κ → AF F) → ℂ} (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x) (hR0 : R 0 ≠ 0)
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrx : R (0 + z) = R 0 := hR 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₂ : ∀ Φ ∈ schA F κ, T₂ Φ ∈ schA F κ)
    {φ φ' φ'' : (κ → Fv F v) → ℂ} (h₂ : Acts (evFin F v) T₂ φ φ') (h₁ : Acts (evFin F v) T₁ φ' φ'') :
    Acts (evFin F v) (T₁ * T₂) φ φ'' := by
  intro r hr
  have e₂ := h₂ r hr
  have hr' : Rest (evFin F v) φ' r := ⟨hr.1, by rw [← e₂]; exact hT₂ _ hr.2⟩
  show T₁ (T₂ (tens (evFin F v) φ r)) = _
  rw [e₂]
  exact h₁ r hr'

theorem exists_hom {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {Γ : Type} [Monoid Γ]
    (ρ : Γ →* Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ γ, ∀ Φ ∈ schA F κ, ρ γ Φ ∈ schA F κ)
    (hex : ∀ γ, ∀ m ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (ρ γ) m φ₁) :
    ∃ ω : Γ →* Module.End ℂ (SB (κ → Fv F v)), ∀ γ (m : SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      φ₁ ∈ SB (κ → Fv F v) → (Acts (evFin F v) (ρ γ) (m : (κ → Fv F v) → ℂ) φ₁ ↔ ((ω γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = φ₁) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (SB _).zero_mem).1
  choose f hfSB hfA using hex

  have hread : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (ρ γ) m φ₁ → ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R :=
    fun γ m hm φ₁ h => h R (hR m hm)
  have huniq : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R → f γ m hm = φ₁ := by
    intro γ m hm φ₁ h
    exact tens_cancel v hRi hR0 ((hread γ m hm _ (hfA γ m hm)).symm.trans h)
  have htadd : ∀ φ φ' : (κ → Fv F v) → ℂ, tens (evFin F v) (φ + φ') R =
      tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro φ φ'; funext x; simp only [tens, Pi.add_apply, add_mul]
  have htsmul : ∀ (c : ℂ) (φ : (κ → Fv F v) → ℂ), tens (evFin F v) (c • φ) R = c • tens (evFin F v) φ R := by
    intro c φ; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let L : Γ → Module.End ℂ (SB (κ → Fv F v)) := fun γ =>
    { toFun := fun m => ⟨f γ m m.2, hfSB γ m m.2⟩
      map_add' := fun m m' => by
        apply Subtype.ext
        show f γ _ _ = f γ m m.2 + f γ m' m'.2
        apply huniq
        rw [Submodule.coe_add, htadd, map_add (f := _), hread γ m m.2 _ (hfA γ m m.2),
          hread γ m' m'.2 _ (hfA γ m' m'.2), htadd]
      map_smul' := fun c m => by
        apply Subtype.ext
        show f γ _ _ = c • f γ m m.2
        apply huniq
        rw [Submodule.coe_smul, htsmul, map_smul, hread γ m m.2 _ (hfA γ m m.2), htsmul] }
  have hL : ∀ γ (m : SB (κ → Fv F v)), ((L γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = f γ m m.2 := fun _ _ => rfl
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    apply huniq
    rw [map_one]; rfl
  · intro γ γ'
    apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    show f (γ * γ') m m.2 = f γ (f γ' m m.2) (hfSB γ' m m.2)
    apply huniq
    rw [map_mul]
    exact acts_mul v (ρ γ) (ρ γ') (hpres γ') (hfA γ' m m.2) (hfA γ _ (hfSB γ' m m.2)) R (hR m m.2)
  · intro γ m φ₁ _
    show _ ↔ f γ m m.2 = φ₁
    constructor
    · intro h; exact huniq γ m m.2 φ₁ (hread γ m m.2 φ₁ h)
    · intro h; rw [← h]; exact hfA γ m m.2

end GlobalTheory.LocalWeilHom

namespace GlobalTheory.LocalWeilHom

theorem local_weil_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ σL JS JT ιS ιT hιS hιT
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  let ρ := om'.comp (MonoidHom.prodMap ιS ιT)
  have hρ : ∀ g h, ρ (g, h) = om' (ιS g, ιT h) := fun _ _ => rfl
  have hpres : ∀ γ, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ρ γ Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun γ Φ hΦ => hW.pres _ Φ hΦ
  have hex : ∀ γ, ∀ m ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (ρ γ) m φ₁ := by
    rintro ⟨g, h⟩ m hm
    obtain ⟨φ₁, hφ₁, hA₁⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v (ιT h) (hιT h) m hm
    obtain ⟨S, hS⟩ := GlobalTheory.WeilLocality.locality B G X om om' hTr v (ιS g) (hιS g)
    refine ⟨S φ₁, (hS φ₁ hφ₁).1, ?_⟩
    have hsplit : ρ (g, h) = om' (ιS g, 1) * om' (1, ιT h) := by
      rw [hρ, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hsplit]
    exact acts_mul v _ _ (fun Φ hΦ => hW.pres _ Φ hΦ) hA₁ (hS φ₁ hφ₁).2
  obtain ⟨ω, hω⟩ := exists_hom v ρ hpres hex
  exact ⟨ω, fun g h m φ₁ hφ₁ => hω (g, h) m φ₁ hφ₁⟩

end GlobalTheory.LocalWeilHom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

section Mark

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {g : ℕ}

theorem mark_of_exp {D : Datum H} {l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}
    {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hu : F₂.u k₂ P₂ ≫ r = F.u k P)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ a, P (gam a) = h (P₂ a))
    (hx : ∀ z, (F.ex k P (h z)).left = (F₂.ex k₂ P₂ z).left ≫ m.φ) :
    ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  intro a ha
  have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
  have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
    rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← GlobalTheory.CoverExp.pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
  have e : F.ex k P ((l.M : ℂ)⁻¹ • P (gam (F₂.t k₂ a))) = F.ex k P ((l.M : ℂ)⁻¹ • P (F.t k a)) := by
    apply Over.OverMorphism.ext
    rw [hh, ← map_smul h, hx, ← j₁, ← j₂, Over.comp_left, Over.comp_left, Category.assoc, heta]
    have w₂ : (toUnit (Over.mk (F₂.u k₂ P₂))).left = F₂.u k₂ P₂ := by
      simpa using Over.w (toUnit (Over.mk (F₂.u k₂ P₂)))
    have w₁ : (toUnit (Over.mk (F.u k P))).left = F.u k P := by
      simpa using Over.w (toUnit (Over.mk (F.u k P)))
    rw [w₂, w₁, ← Category.assoc, hu]
  exact (GlobalTheory.UnifPoint.div_eq_iff hP.2.1 (F.ex_add k P hP) (F.ex_ker k P hP) hM0 _ _).1 e

end Mark

section Down

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem exists_frOver_down (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (y₂ : FrPt d.Xo₂ d.c₂ S) (y₀ : FrPt Xo c S) (e : y₂.x ≫ d.r = y₀.x) (hu : ∀ τ i, y₂.u τ i ≫ d.m.φ = y₀.u τ i) :
    ∃ y : FrPt Xo c S, y.x = y₀.x ∧ y.u = y₀.u ∧ FrOver d y₂ y := by
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₀.x, y₀.x_over, y₀.u, y₀.tan, y₀.eig, y₀.basis, s, fun s' => ?_⟩, rfl, rfl,
    (frOver_iff d _ _).2 ⟨e, hu, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
  refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
  exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
    ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
      (scal_iff (fst (Over.mk y₀.x) Xo.univ.t.G).left (toΓ S a) s s').symm)

end Down

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem good_comp (d : DeltaDat Xo c n) (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) :=
  (congrArg σ₂ (Subtype.ext rfl)).trans h

theorem genScal_eq {S : Type} [CommRing S] (t : Sˣ) :
    genScal (Dw := Dw) t = fun i => Option.elim i t (fun _ => 1) := by
  funext i
  cases i <;> simp [genScal]

end Emb


open AlgebraicGeometry CategoryTheory in
set_option maxHeartbeats 1600000 in
theorem over_comp : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ k₂
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := good_comp d σ₂ hσ₂
  set σ := σ₂.comp (d.eF : c.F →+* d.c₂.F) with hσe
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hU := hL.unf σ hσ
  have hU₂ := hL₂.unf σ₂ hσ₂
  obtain ⟨hr₀, hW⟩ := hL.modelW σ hσ
  obtain ⟨hr₂, hW₂⟩ := hL₂.modelW σ₂ hσ₂
  have hpq : Dw.p ≠ Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, hA, hA₂]
  have hinc : (σ₂.comp (IntermediateField.inclusion d.c₂.le).toRingHom).comp
      (IntermediateField.inclusion hle).toRingHom = σ.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun a => congrArg σ₂ (Subtype.ext rfl)
  have hrel : ∀ τ : D.host.E →+* ℂ, relab c σ τ = relab d.c₂ σ₂ τ := fun τ => by
    ext a
    exact congrArg σ₂ (Subtype.ext rfl)
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hper⟩ := id hU
  obtain ⟨-, -, -, -, -, g₂, e₂, F₂, ik₂, φ₂, hEF₂, hper₂⟩ := id hU₂
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U₂ σ₂).X k₂)
  obtain ⟨P₀, hP₀, hp₀, hu₀, -⟩ := hper₂ k₂ ⟨x₀, hx₀⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hy : (F₂.u (ik₂ k₂) P₀ ≫ d.r) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [CategoryTheory.Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle,
      ← CategoryTheory.Category.assoc, F₂.over_σ _ P₀ hp₀, GlobalTheory.ClsVal.Cmp.spMap_comp', hinc]
  have hframe {S : Type} [Field S] [Algebra c.F S] (x : Sp S ⟶ Xo.X)
      (hx : x ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, y.x = x := by
    choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
    obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
    exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
  obtain ⟨y, hyx⟩ := @hframe (CAt σ) (inferInstanceAs (Field ℂ)) (instAlgebraCAt σ) (F₂.u (ik₂ k₂) P₀ ≫ d.r) (by
    exact hy)
  obtain ⟨k, x₁, t₁, hb⟩ := hU.2.2.1 y
  obtain ⟨P₁, hP₁, hp₁, hu₁, -⟩ := hper k x₁
  have hu : F₂.u (ik₂ k₂) P₀ ≫ d.r = F.u (ik k) P₁ := by
    rw [← hu₁, ← hb.1]
    exact hyx.symm
  obtain ⟨gam, hl, hg, hh, hx⟩ := GlobalTheory.CoverFrameMod.exists_isometry_of_cover F₂ F d.m hp₀ hp₁ hu
  have gM := mark_of_exp d.m d.pd hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ (ik k) (ik₂ k₂) hp₁ hp₀ hu gam hl hh hx
  obtain ⟨a, ε, hε, hξ, hmul, -, hiso⟩ := GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry D.host.E D.R.r
    ((U₂ σ₂).X k₂) ((U σ).X k) (fun τ => (hL₂.xiAbs σ₂ hσ₂ k₂ τ).trans (hL.xiAbs σ hσ k τ).symm)
    ((φ₂ k₂).symm.trans (gam.trans (φ k))) (fun u v => by
      have e₁ := hEF k (gam ((φ₂ k₂).symm u)) (gam ((φ₂ k₂).symm v))
      have e₂ := hEF₂ k₂ ((φ₂ k₂).symm u) ((φ₂ k₂).symm v)
      rw [hg] at e₁
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e₂
      exact e₁.symm.trans e₂)
  have hξ₀ : ((U σ).X k).ξ0 = ((U₂ σ₂).X k₂).ξ0 := (hW k).2.trans (hW₂ k₂).2.symm
  obtain rfl : ε = 1 := mul_right_cancel₀ ((U₂ σ₂).X k₂).ξ0_ne (by rw [← hξ, one_mul, hξ₀])
  have hG : ((U σ).X k).Gm = ((U₂ σ₂).X k₂).Gm := (hW k).1.trans (hW₂ k₂).1.symm
  have hΨ : ∀ τ, τ ∈ ((U σ).X k).Ψ ↔ τ ∈ ((U₂ σ₂).X k₂).Ψ := fun τ =>
    ((hU.2.1 k).2 τ).trans ((hU₂.2.1 k₂).2 τ).symm
  have hp0 : ((U σ).X k).p0 = ((U₂ σ₂).X k₂).p0 := (hU.2.1 k).1.trans (hU₂.2.1 k₂).1.symm
  have hiso' : ∀ v w, herm ((U σ).X k).Gm ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
      ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w := fun v w => by
    rw [hiso, one_mul]
  have hgam : ∀ b, (φ k (gam b) : Fin D.R.r → D.host.E) =
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (φ₂ k₂ b : Fin D.R.r → D.host.E) := fun b => by
    rw [hmul (φ₂ k₂ b)]
    simp
  refine ⟨k, a, hG.symm, fun v w => ?_, ?_⟩
  · have h' := hiso' v w
    rwa [hG] at h'
  intro x hx x' hmv
  have hx' : x' ∈ ((U σ).X k).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ a hp0 hΨ hiso' x x' hx hmv
  refine ⟨hx', ?_⟩
  obtain ⟨Q₁, hQ₁, hq₁, hqu₁, hqv₁, hqn₁⟩ := hper k ⟨x', hx'⟩
  obtain ⟨Q₂, hQ₂, hq₂, hqu₂, hqv₂, hqn₂⟩ := hper₂ k₂ ⟨x, hx⟩
  obtain ⟨c₁, c₂⟩ := GlobalTheory.CoverFrameRead.point_over d hd hpq hA hle hinc e e₂ F F₂ (ik k) (ik₂ k₂) hq₁ hq₂ gam hg gM
    (fun b i => by
      rw [hQ₁, hQ₂, hgam, Equiv.apply_symm_apply, hrel]
      exact GlobalTheory.CoverFrameRead.perFr_move _ _ hΨ hp0 hG a hiso' x x' hmv _ _ _)
  have hx₂ : ((U₂ σ₂).un k₂ ⟨x, hx⟩).x ≫ d.r = ((U σ).un k ⟨x', hx'⟩).x := by
    rw [hqu₁, hqu₂]
    exact c₁
  have hu₂ : ∀ τ i, ((U₂ σ₂).un k₂ ⟨x, hx⟩).u τ i ≫ d.m.φ = ((U σ).un k ⟨x', hx'⟩).u τ i :=
    fun τ i => c₂ ⟨τ, i⟩ _ _ (hqv₁ τ i) (hqv₂ τ i)
  letI : Algebra c.F (CAt σ₂) := σ.toAlgebra
  obtain ⟨z, hzx, hzu, ho⟩ := exists_frOver_down (S := CAt σ₂) d ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) hx₂ hu₂
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen (σ := σ) ((U σ).un k ⟨x', hx'⟩) z hzx hzu
  have hn' : (∀ τ i, ‖dmin ((U₂ σ₂).X k₂).Gm x τ i‖ = 1) → ∀ τ i, ‖dmin ((U σ).X k).Gm x' τ i‖ = 1 := by
    intro hn τ i
    obtain ⟨τ, h₁⟩ := τ
    have h₂ := (hΨ τ).1 h₁
    have e' : dmin ((U σ).X k).Gm x' ⟨τ, h₁⟩ i = dmin ((U₂ σ₂).X k₂).Gm x ⟨τ, h₂⟩ i := by
      unfold dmin
      rw [hmv τ h₂ h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso' τ]
    rw [e']
    exact hn _ _
  refine ⟨t, fun hn => ?_, z, ?_, ho⟩
  · exact GlobalTheory.CoverFrameMod.norm_gen_eq_one_of_frOver d F₂ F (ik₂ k₂) (ik k) Q₂ Q₁ ((U₂ σ₂).un k₂ ⟨x, hx⟩)
      ((U σ).un k ⟨x', hx'⟩) z (fun i => Option.elim i t (fun _ => 1)) hq₂ hq₁ hqu₂ hqu₁ (hqn₂ hn) (hqn₁ (hn' hn)) ho ht
  · have e' : genScal (Dw := Dw) (S := CAt σ₂) t = fun i => Option.elim i t (fun _ => 1) := genScal_eq _
    exact e'.symm ▸ ht

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometryStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_component_over_base_rational_isometry : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  first | exact @GlobalTheory.LevModel.over_comp | exact GlobalTheory.LevModel.over_comp | (intros; apply GlobalTheory.LevModel.over_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilModelLineActionExists
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealLift.FirstLine

open scoped Matrix Classical
open Formalism.BasicNotions.TH

open GlobalTheory.RealLift GlobalTheory.RealLift.LieFirstPf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf' {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem fockMap_swap {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    {JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix β (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} (hΦ : IsFockMap ψ τ d A C Φ)
    (hdd : ∀ x : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = d.e x) :
    IsFockMap ψ τ d' C A (Φ ∘ₗ (swapT (InfinitePlace F) P Q R S).toLinearMap) := by
  refine ⟨hΦ.1.comp (swapT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
  have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
  have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
    rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapT (InfinitePlace F) P Q R S T)
  have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
    show schr ψ (d'.e _) = schr ψ (d.e _)
    rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
  set_option backward.isDefEq.respectTransparency false in
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => swapE_heisOp (c w) f)]

end GlobalTheory.RealLift.FirstLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsWeightCompat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem markOver_zsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l l₂ : Level H} {r : ℕ} {L : Lt E r} {mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : MarkOver l l₂ L mk mk₂) (m : ℤ) :
    MarkOver l l₂ L (m • mk) (m • mk₂) := fun a ha => by
  obtain ⟨u, hu, e⟩ := h a ha
  refine ⟨m • u, zsmul_mem hu _, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e, smul_add, smul_comm m l.M]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem div_mul_phiC {s : T.Q.c.F →+* ℂ} {W : HSp D} {j : ℕ} (hV : T.V j s = W) (hc : CUnit (T.cE j s))
    (cst : (T.U j s).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (h : GA D W) :
    cst (castDict hV (T.dict j s) h).1 / T.cE j s (castDict hV (T.dict j s) h).1 * phiC T hV a f h =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (castDict hV (T.dict j s) h).1 * castDict hV (T.mu j s) h *
        rdU (T.U j s) f (castDict hV (T.dict j s) h).1 (castDict hV (T.dict j s) h).2) := by
  subst hV
  have h0 : T.cE j s (T.dict j s h).1 ≠ 0 := norm_ne_zero_iff.1 ((hc _).trans_ne one_ne_zero)
  change cst (T.dict j s h).1 / T.cE j s (T.dict j s h).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
    (T.cE j s (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)) =
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)
  field_simp

theorem inj_of_indep {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module ℂ M] {s : K →+* ℂ}
    (c : X →ₛₗ[s] M) (h : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ fun j => c (b j)) :
    Function.Injective c := (injective_iff_map_eq_zero c).2 fun x hx => by
  by_contra h0
  exact (h 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem exists_ext (O : OM T R i) (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hP : Pinned κ v₀ O)
    (σ : D.what₂.LL →+* ℂ) : ∃ σ' : O.c'.F →+* ℂ, σ'.comp O.jL = σ := by
  have hs : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ : (y : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hF ▸ y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hP.lift.field x).trans hx)⟩
  let e := RingEquiv.ofBijective O.jL ⟨O.jL.injective, hs⟩
  exact ⟨σ.comp e.symm.toRingHom, RingHom.ext fun x => congrArg σ (e.symm_apply_apply x)⟩

end GlobalTheory.GalOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeOfIsIdemAt
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum

theorem conj_smul_ne_of_isIdemAt {D : D7} {e : Formalism.L2.Theta.AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : D.host.conj • P.asIdeal ≠ P.asIdeal := by
  intro h
  have hc := GlobalTheory.EtaProduct.cA_of_fixed (GlobalTheory.HeckeDetChar.isPlIdem he) h
  have h0 : e = 0 := by
    have := he.1.2.1
    rw [hc, he.1.1] at this
    exact this
  apply P.ne_bot
  refine eq_bot_iff.2 fun x hx => ?_
  by_contra hx0
  have := (he.2 x hx0).1 hx
  rw [h0, zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem condE_isCoprime_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L),
    IsCoprime (condE P) (D.host.conj • condE P) := by
  intro D T L P
  have hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F) :=
    GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj
      (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)
  unfold GlobalTheory.FunObj.SqNum.condE
  rw [Finset.smul_prod']
  refine IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_
  rw [smul_pow']
  refine IsCoprime.pow ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  have hm : (D.host.conj • (P.w v').asIdeal).IsMaximal := by
    have := (P.w v').isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  refine Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_
  have hvv : v = v' := by
    have a := congrArg HeightOneSpectrum.asIdeal (P.under_w hv)
    have b := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    refine HeightOneSpectrum.ext ?_
    rw [← a, ← b]
    show Ideal.under _ _ = Ideal.under _ _
    rw [heq, hF]
  subst hvv
  obtain ⟨e, he⟩ := P.w_split v hv
  exact conj_smul_ne_of_isIdemAt he heq.symm

end GlobalTheory.FunObj.StdDatum

end
end
