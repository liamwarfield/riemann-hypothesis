module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvOfNear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensor
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn.HalfOff

variable {D : D7} {S T : HSp D}

theorem smul_apply' (b : AE D) (t : WO S T) (i j) : (b • t) i j = b * t i j := by
  rw [Matrix.smul_apply, smul_eq_mul]

theorem smul_half_zero {a b : AE D} (hab : a * b = 0) {x : WO S T} (hx : IsHalf a x) : b • x = 0 := by
  ext i j
  rw [smul_apply', Matrix.zero_apply, ← hx i j, ← mul_assoc, mul_comm b a, hab, zero_mul]

theorem half_smul {b : AE D} (hb : b * b = b) (t : WO S T) : IsHalf b (b • t) := fun i j => by
  rw [smul_apply', ← mul_assoc, hb]

theorem tens_trans {a b : AE D} (hab : a * b = 0) (Φ Ψ : WO S T → ℂ) {x : WO S T} (hx : IsHalf a x) :
    tens b (fun t => Φ (t + x)) Ψ = fun t => tens b Φ Ψ (t + x) := by
  funext t
  simp only [tens_apply, smul_add, smul_half_zero hab hx, add_zero]
  congr 2
  abel

theorem tens_modul (ψ : AddChar (AF D.host.F) ℂ) {a b : AE D} (hab : a * b = 0) (hb : b * b = b)
    (Φ Ψ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D a) y) :
    tens b (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
  funext t
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
    rw [← GlobalTheory.LocMod.TensorModel.symplO_add_left', sub_add_cancel]
  rw [tens_apply, tens_apply, e1, GlobalTheory.LocMod.TensorModel.symplO_half_zero hba (half_smul hb t) hy, add_zero, mul_assoc]

theorem tens_vac {a b : AE D} (hab : a * b = 0) (hb : b * b = b) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens b ((1 : ℂ) • halfInd a Λ) (halfInd b Λ) = (1 : ℂ) • halfInd (a + b) Λ := by
  classical
  funext t
  simp only [one_smul, tens_apply]
  set M : WO S T := b • t with hMdef
  have hM : IsHalf b M := half_smul hb t
  have key : ((t - M ∈ Λ ∧ IsHalf a (t - M)) ∧ M ∈ Λ) ↔ (t ∈ Λ ∧ IsHalf (a + b) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, smul_apply'] at h
      linear_combination h + t i j * hab
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λ := hΛ t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, smul_apply']
      linear_combination h2 i j - t i j * hab
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (a + b) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos ⟨h3, hM⟩, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λ
    · rw [if_pos (show M ∈ Λ ∧ IsHalf b M from ⟨h3, hM⟩), mul_one,
        if_neg (show ¬(t - M ∈ Λ ∧ IsHalf a (t - M)) from fun h => hR (key.1 ⟨h, h3⟩))]
    · rw [if_neg (show ¬(M ∈ Λ ∧ IsHalf b M) from fun h => h3 h.1), mul_zero]

end GlobalTheory.FinPl.PutIn.HalfOff


open GlobalTheory.FinPl.PutIn.HalfOff in
theorem GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensL b (halfInd b Λ)) := by
  intro D ψ S T a b Λ f₀ Tm hab hb hΛ hT
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have hsb : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf (a + b) Λ (tens b Φ (halfInd b Λ)) := fun Φ hΦ =>
    GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents D S T a b Λ Φ (halfInd b Λ) hab hb hΛ hΦ (GlobalTheory.isSBHalf_halfInd b Λ)
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.comp_apply, tensL_apply, tens_trans hab Φ _ hx]
    have hx' : IsHalf (a + b) x := by
      rw [add_comm]; exact GlobalTheory.LocMod.TensorModel.half_sum hba hx
    exact hT.trans _ (hsb Φ hΦ) x hx'
  · rw [LinearMap.comp_apply, tensL_apply, tens_modul ψ hab hb Φ _ hy]
    have hy' : IsHalf (cA D (a + b)) y := by
      rw [add_comm]; exact GlobalTheory.LocMod.TensorModel.half_sum_cA hba hy
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensL_apply, tens_vac hab hb Λ hΛ]
    exact hT.vac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_comp_idempotentSplitTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensL b (halfInd b Λ)) := by
  first | exact @GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf | exact GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf | (intros; apply GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBadPrimeOverChartBadPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBadPrimeOverChartBadPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over_sub : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) := by
  intro B X I hOk _ l Z a v hv
  obtain ⟨P, hP, hPv⟩ := exists_SBof_over I hOk l Z a v hv
  exact ⟨⟨P, hP⟩, hPv⟩

end GlobalTheory.Mem.Col2.AdT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBadPrimeOverChartBadPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_badPrime_over_chart_bad_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) := by
  exact @GlobalTheory.Mem.Col2.AdT.exists_SBof_over_sub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

namespace GlobalTheory.AdForm.ChiCont


set_option maxHeartbeats 2000000 in
theorem chi_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ) := by
  intro B X I hI hP l Z u a Ch A hA i hi β
  obtain ⟨n, hn, hfin⟩ := hA.fin i hi β
  let Vs : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) :=
    {v | ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)}
  have hVs : Vs.Finite := by
    have e : Vs = ⋃ P : SBof I a, {v | Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)} := by
      ext v; simp [Vs]
    rw [e]
    refine Set.finite_iUnion fun P => Set.Subsingleton.finite ?_
    intro v hv w hw
    exact HeightOneSpectrum.ext (hv.trans hw.symm)
  have hbad : ∀ v ∈ A.bad i, v ∈ Vs := fun v hv => GlobalTheory.T.exists_badPrime_over_chart_bad_place I hI hP l Z a v (hA.bad_le i hi v hv)
  have hker := GlobalTheory.T.levelCharacter_trivial_near_one_of_local_bad_places (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi)
    (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev Vs hVs hbad (by
    rintro v ⟨P, hv⟩
    obtain ⟨N, hN⟩ := GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace I hI hP l Z a (B.T u) i hi (A.bad i) (A.K i hi β).lev n hn hfin P v hv
    have h2 := GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) ((I.rec7 l Z).R.N i) N
      (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    exact h2.mono fun w hw x hx hxw => hN x hx w hw hxw)

  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  haveI : IsTopologicalGroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let Φ : A.U i β →* GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    (GlobalTheory.ClassSumLevel.finGLHom ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi)).comp (A.U i β).subtype
  have hΦc : Continuous Φ := (GlobalTheory.ClassSumLevel.continuous_finGLHom _ _).comp continuous_subtype_val
  have ht : Tendsto Φ (nhds 1) (nhds 1) := by
    have := hΦc.tendsto 1
    rwa [map_one] at this
  have hev : ∀ᶠ g in nhds (1 : A.U i β), (1 : ℂˣ) = A.chi i β g := by
    filter_upwards [ht.eventually hker] with g hg
    obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
    rw [hA.chi i hi β g κ hκ]
    exact (hg κ (Units.ext (hκ.trans rfl))).symm
  have hχ : Continuous (A.chi i β) := by
    refine continuous_of_continuousAt_one (A.chi i β) ?_
    exact continuousAt_const.congr hev
  exact Units.continuous_val.comp hχ

end GlobalTheory.AdForm.ChiCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.AdForm.ChiCont.chi_continuous | exact GlobalTheory.AdForm.ChiCont.chi_continuous | (intros; apply GlobalTheory.AdForm.ChiCont.chi_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMemLatVIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_ofSplit (q : SplitPt D k) (x : D.host.E) : (ofSplit q).pr x = q.pr (incA D x) := rfl

theorem eq_sec_add_cA (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  rw [q.sec_pr, q.sec_pr, RingHom.map_mul, Formalism.L2.Theta.cA_cA, ← add_mul, (idem_iff q a).1 ha]

theorem pr_mem_of_int (q : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : q.pr a ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt q).2 ha

theorem mem_intAt_iff_pr (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_int q h.2, pr_mem_of_int q ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add_cA q ha, RingHom.map_add (f := _)]
  exact add_mem ((q.int_iff _).1 h.1) ((cA_int_iff _).2 ((q.int_iff _).1 h.2))

theorem single_int {Y' : Type} [DecidableEq Y'] (m₁ : Y') (i : Y') : (Pi.single m₁ (1 : k) : Y' → k) i ∈ 𝒪[k] := by
  by_cases hi : i = m₁
  · subst hi; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem wpart {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E} {c : k} {m₀ : Y}
    (hI : IntIn q S F L) (hc : valuation k c = 1) (hu : ∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) (x : k) :
    (fun r => q.sec (x * (ofSplit q).pr (u r))) ∈ latV S L (· = q.v) ↔ x ∈ 𝒪[k] := by
  have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact zero_ne_one hc
  have e : (fun r => q.sec (x * (ofSplit q).pr (u r))) =
      fun r => q.sec ((F.β *ᵥ Pi.single m₀ (x / c)) r) := by
    funext r
    congr 1
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single m₀ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, ← hu r]
    field_simp
  rw [e, ← hI (Pi.single m₀ (x / c))]
  constructor
  · intro h
    have h1 := h m₀
    rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one] at h1
    exact (Valuation.mem_integer_iff _ _).2 h1
  · intro h i
    by_cases hi : i = m₀
    · subst hi
      rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one]
      exact (Valuation.mem_integer_iff _ _).1 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

theorem wbar {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E}
    (hL : IsSelfDualC S L) (hI : IntIn q S F L)
    (hb : ∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k])
    (hb1 : ∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) (A : k) :
    (fun r => cA D (q.sec (A * (ofSplit q).pr (star (u r))))) ∈ latV S L (· = q.v) ↔ A ∈ 𝒪[k] := by
  have ht : ∀ i, (ofSplit q).pr (star ((S.gram *ᵥ u) i)) =
      ∑ j, q.pr (cA D (incA D (S.gram i j))) * (ofSplit q).pr (star (u j)) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pr_ofSplit, Matrix.mulVec, dotProduct, star_sum, star_mul', map_sum, map_mul, cA_incA]
  have hsum : ∀ x : Fin S.rank → k,
      ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
      A * ∑ m, (F.γ *ᵥ x) m * ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) := by
    intro x
    have h1 : ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
        A * ∑ i, x i * (ofSplit q).pr (star ((S.gram *ᵥ u) i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ht i, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    congr 1
    have hx : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    generalize F.γ *ᵥ x = y at hx ⊢
    subst hx
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_)
    ring
  rw [csec_mem_iff hL]
  simp only [hsum]
  obtain ⟨m₁, hm₁⟩ := hb1
  constructor
  · intro h
    have hx : (fun i => q.sec ((F.β *ᵥ Pi.single m₁ (1 : k)) i)) ∈ latV S L (· = q.v) :=
      (hI _).1 (single_int (k := k) m₁)
    have h2 := h _ hx
    rw [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec,
      Finset.sum_eq_single m₁ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
      Valuation.mem_integer_iff, map_mul, hm₁, mul_one] at h2
    exact (Valuation.mem_integer_iff _ _).2 h2
  · intro hA x hx
    have hy := (hI (F.γ *ᵥ x)).2 (by rwa [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec])
    exact mul_mem hA (sum_mem fun m _ => mul_mem (hy m) (hb m))

theorem line_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (c : k) (m₀ : Y),
    IsSelfDualC S L → IntIn q S F L → valuation k c = 1 → (∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) →
    (∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k]) →
    (∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) →
    ∀ a ∈ GlobalTheory.FinPl.idAt D (· = q.v),
      ((fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S L Y _ _ F u c m₀ hL hI hc hu hb hb1 a ha
  have hy : (fun r => a * incA D (u r)) = (fun r => q.sec (q.pr a * (ofSplit q).pr (u r))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * (ofSplit q).pr (star (u r))))) := by
    funext r
    rw [Pi.add_apply]
    conv_lhs => rw [eq_sec_add_cA q ha]
    rw [add_mul, sec_mul_right]
    congr 1
    have e : incA D (u r) = cA D (incA D (star (u r))) := by rw [cA_incA, star_star]
    rw [e, ← RingHom.map_mul, sec_mul_right]
    rfl
  rw [hy]
  refine (decomp hL (fun r => q.pr a * (ofSplit q).pr (u r))
    (fun r => q.pr (cA D a) * (ofSplit q).pr (star (u r)))).trans ?_
  rw [mem_intAt_iff_pr q ha]
  exact and_congr (wpart hI hc hu _) (wbar hL hI hb hb1 _)

end GlobalTheory.SplitLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyVacuumData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mem_latV_iff (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) (w : Fin S.rank → k) :
    (fun i => q.sec (w i)) ∈ latV S L (· = q.v) ↔ ∀ i, w i ∈ 𝒪[k] := by
  classical
  have hmem : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hsingle : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ L := fun i =>
    (hmem _).2 fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
  let G : Finset (Fin S.rank → D.host.E) := Finset.univ.image fun i => Pi.single i 1
  have hGL : ∀ x ∈ (G : Set (Fin S.rank → D.host.E)), x ∈ L := by
    intro x hx
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hsingle i
  have hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L := by
    apply le_antisymm
    · rw [Submodule.span_le]; exact hGL
    · intro x hx
      have hi := (hmem x).1 hx
      have e : x = ∑ i, (⟨x i, hi i⟩ : 𝓞 D.host.E) • (Pi.single i 1 : Fin S.rank → D.host.E) := by
        funext j
        rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
        simp [Algebra.smul_def]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G]))
  constructor
  · intro h
    have h1 := FullLatFrame.pr_mem_span q G hG h
    simp only [q.pr_sec] at h1
    have h2 : ∀ z ∈ Submodule.span 𝒪[k] (FullLatFrame.aux₃ q '' (G : Set (Fin S.rank → D.host.E))), ∀ i, z i ∈ 𝒪[k] := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        intro i
        exact FullLatFrame.pr_int_mem q ⟨x i, (hmem x).1 (hGL x hx) i⟩
      | zero => intro i; exact zero_mem _
      | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
      | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
    exact h2 _ h1
  · intro h
    have e : w = ∑ i, (⟨w i, h i⟩ : 𝒪[k]) • FullLatFrame.aux₃ q (S := S) (Pi.single i 1) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [FullLatFrame.aux₃, Pi.single_apply, Ne.symm hb]) (by simp)]
      simp [FullLatFrame.aux₃]
      change _ = w j * 1
      rw [mul_one]
    rw [← FullLatFrame.mem_latW, e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [FullLatFrame.mem_latW]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (hsingle i)

theorem intIn_stdFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) : IntIn q S (stdFr k e) L := by
  intro y
  rw [sec_mem_latV_iff q S L hL]
  have h : (stdFr k e).β *ᵥ y = y ∘ e.symm := by
    change (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e *ᵥ y = _
    have := Matrix.submatrix_mulVec_equiv (1 : Matrix (Fin S.rank) (Fin S.rank) k) y id e
    simpa [Function.comp_def] using this
  rw [h]
  exact ⟨fun h i => h _, fun h a => by simpa using h (e a)⟩

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFr {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (e : Y ≃ Fin N) (d : Y → k) (hd : ∀ y, d y ≠ 0) :
    GlobalTheory.LocMod.Frame k N Y where
  β := (stdFr k e).β * Matrix.diagonal d
  γ := Matrix.diagonal (fun y => (d y)⁻¹) * (stdFr k e).γ
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      show (fun y => d y * (d y)⁻¹) = fun _ => (1 : k) from funext fun y => mul_inv_cancel₀ (hd y),
      Matrix.diagonal_one, Matrix.one_mul, (stdFr k e).βγ]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (stdFr k e).γ, (stdFr k e).γβ, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      show (fun y => (d y)⁻¹ * d y) = fun _ => (1 : k) from funext fun y => inv_mul_cancel₀ (hd y), Matrix.diagonal_one]

theorem intIn_diagFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) (d : Y → k) (hd : ∀ y, d y ≠ 0) (hv : ∀ y, valuation k (d y) = 1) :
    IntIn q S (diagFr e d hd) L := by
  intro y
  have h1 := intIn_stdFr q S L hL e (fun a => d a * y a)
  have h2 : (diagFr e d hd).β *ᵥ y = (stdFr k e).β *ᵥ fun a => d a * y a := by
    change ((stdFr k e).β * Matrix.diagonal d) *ᵥ y = _
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext a
    exact Matrix.mulVec_diagonal _ _ _
  rw [h2, ← h1]
  refine forall_congr' fun a => ?_
  change valuation k (y a) ≤ 1 ↔ valuation k (d a * y a) ≤ 1
  rw [map_mul, hv, one_mul]

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

theorem oTop_iA {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

theorem oTop_iB {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iB b a = if (I.rec7 l Z).sp.X'.rank = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

theorem entry_inl {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ} {Y : Type} [Fintype Y]
    [DecidableEq Y] (eT : Y ≃ Fin n) (iA : Matrix (Fin N) (Fin n) E) (hA : ∀ b a, iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0)
    (r : Fin N) (c : Y) (m : Fin N) (hm : (m : ℕ) = eT c) :
    (1 : Matrix (Fin N) (Fin N) k) r m = (iA.map f * (1 : Matrix (Fin n) (Fin n) k).submatrix id eT) r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (eT c)
    (fun b _ hb => by rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]) (by simp)]
  rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, hA, Matrix.one_apply]
  by_cases h : (eT c : ℕ) = r
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

theorem entry_inr {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ}
    (iB : Matrix (Fin N) (Fin 1) E) (hB : ∀ b a, iB b a = if n = (b : ℕ) then 1 else 0) (z : Fin 1 → E) (x : E)
    (hz : ∀ i, z i = x) (r : Fin N) (m : Fin N) (hm : (m : ℕ) = n) :
    (1 : Matrix (Fin N) (Fin N) k) r m * f x = (iB.map f *ᵥ fun i => f (z i)) r := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, hB, hz, Matrix.one_apply]
  by_cases h : n = (r : ℕ)
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames


end GlobalTheory.XGeoStd.Frames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfJacFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV MonoAt idAt intAt colMul Lat SplitPt Pl)
open GlobalTheory.IwaPlace GlobalTheory.IwaDecomp GlobalTheory.FinPl.FrameLat

noncomputable section
namespace GlobalTheory.JacMono

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_herm (S : HSp D) (x y : Fin S.rank → AE D) : cA D (hermAt S x y) = hermAt S y x := by
  have hg : ∀ i j, cA D (gA S i j) = gA S j i := fun i j => congrFun (congrFun (adj_gA S) j) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermAt, map_sum, RingHom.map_mul, Formalism.L2.Theta.cA_cA, hg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem herm_smul_right (S : HSp D) (t : AE D) (x y : Fin S.rank → AE D) :
    hermAt S x (t • y) = cA D t * hermAt S x y := by
  rw [← conj_herm, hermAt_smul_left, RingHom.map_mul, conj_herm]

variable (q : SplitPt D k)

theorem conj_eps : cA D (q.e + cA D q.e) = q.e + cA D q.e := by rw [RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]

theorem conj_idAt {a : AE D} (ha : a ∈ idAt D (· = q.v)) : cA D a ∈ idAt D (· = q.v) := by
  rw [idem_iff, ← conj_eps, ← RingHom.map_mul, (idem_iff q a).1 ha]

theorem conj_intAt {a : AE D} (ha : a ∈ intAt D (· = q.v)) : cA D a ∈ intAt D (· = q.v) :=
  ⟨conj_idAt q ha.1, (cA_int_iff a).2 ha.2⟩

theorem colMul_smul {m n : ℕ} (M : Mx D m n) (i : Fin n) (a b : AE D) : a • colMul M i b = colMul M i (a * b) := by
  funext r; simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem colMul_add {m n : ℕ} (M : Mx D m n) (i : Fin n) (a b : AE D) :
    colMul M i (a + b) = colMul M i a + colMul M i b := by
  funext r; simp only [colMul, Pi.add_apply, add_mul]

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}

theorem line_eps (hL : IsSelfDualC S L) (M : Mx D S.rank ρ) (i : Fin ρ) (h1 : colMul M i q.e ∈ latV S L (· = q.v))
    (h2 : ∀ x ∈ latV S L (· = q.v), q.e * ((adj M * gA S) *ᵥ x) i ∈ intAt D (· = q.v)) :
    colMul M i (q.e + cA D q.e) ∈ latV S L (· = q.v) := by
  rw [colMul_add]
  refine add_mem h1 ?_
  refine ((LocSD.isSDAt_latV D S L q.v hL).2.2 (colMul M i (cA D q.e)) fun r => Ideal.mul_mem_right _ _ (conj_idAt q (e_mem_idAt q))).2 fun x hx => ?_
  rw [← conj_herm, hermAt_colMul, Formalism.L2.Theta.cA_cA]
  exact conj_intAt q (h2 x hx)

theorem line_mem (hL : IsSelfDualC S L) (M M' : Mx D S.rank ρ) (i : Fin ρ)
    (h1 : colMul M i (q.e + cA D q.e) ∈ latV S L (· = q.v)) (h2 : colMul M' i (q.e + cA D q.e) ∈ latV S L (· = q.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = q.v)) :
    colMul M i (((adj M' * gA S) *ᵥ y) i) ∈ latV S L (· = q.v) := by
  have hs : ((adj M' * gA S) *ᵥ y) i ∈ idAt D (· = q.v) := mulVec_mem_idAt _ (latV_supp hy) i
  have h3 := ((LocSD.isSDAt_latV D S L q.v hL).2.2 y (latV_supp hy)).1 hy _ h2
  rw [hermAt_colMul, conj_eps, (idem_iff q _).1 hs] at h3
  have h4 := smul_mem hL h1 h3
  rwa [colMul_smul, mul_comm, (idem_iff q _).1 hs] at h4

theorem monoAt_of_half (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hp : ∀ x ∈ latV S L (· = q.v), (∀ i, q.e * (d.pX *ᵥ x) i ∈ intAt D (· = q.v)) ∧
      (∀ i, q.e * (d.pY *ᵥ x) i ∈ intAt D (· = q.v)) ∧ q.e • (d.p0 *ᵥ x) ∈ latV S₀ L₀ (· = q.v))
    (hX : ∀ i, colMul d.jX i q.e ∈ latV S L (· = q.v)) (hY : ∀ i, colMul d.jY i q.e ∈ latV S L (· = q.v))
    (h0 : ∀ w ∈ latV S₀ L₀ (· = q.v), q.e • (d.j0 *ᵥ w) ∈ latV S L (· = q.v)) : MonoAt d L L₀ q.v := by
  have sd := (LocSD.isSDAt_latV D S L q.v hL).2.2
  have sd₀ := (LocSD.isSDAt_latV D S₀ L₀ q.v hL₀).2.2
  have hX' : ∀ i, colMul d.jX i (q.e + cA D q.e) ∈ latV S L (· = q.v) := fun i =>
    line_eps q hL d.jX i (hX i) fun x hx => by rw [← d.pY_eq]; exact (hp x hx).2.1 i
  have hY' : ∀ i, colMul d.jY i (q.e + cA D q.e) ∈ latV S L (· = q.v) := fun i =>
    line_eps q hL d.jY i (hY i) fun x hx => by rw [← d.pX_eq]; exact (hp x hx).1 i
  have h0' : ∀ w ∈ latV S₀ L₀ (· = q.v), d.j0 *ᵥ w ∈ latV S L (· = q.v) := by
    intro w hw
    have hs : ∀ r, (d.j0 *ᵥ w) r ∈ idAt D (· = q.v) := mulVec_mem_idAt _ (latV_supp hw)
    have e1 : d.j0 *ᵥ w = q.e • (d.j0 *ᵥ w) + cA D q.e • (d.j0 *ᵥ w) := by
      funext r
      rw [← add_smul, Pi.smul_apply, smul_eq_mul, (idem_iff q _).1 (hs r)]
    rw [e1]
    refine add_mem (h0 w hw) ((sd (cA D q.e • (d.j0 *ᵥ w)) fun r => Ideal.mul_mem_left _ _ (hs r)).2 fun x hx => ?_)
    rw [hermAt_smul_left, adelicHermitianForm_wittCoreInclusion_left, ← herm_smul_right]
    exact (sd₀ w (latV_supp hw)).1 hw _ (hp x hx).2.2
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [d.pX_eq]; exact line_mem q hL _ _ i (hX' i) (hY' i) hy
    · rw [d.pY_eq]; exact line_mem q hL _ _ i (hY' i) (hX' i) hy
    · refine (sd₀ _ (mulVec_mem_idAt _ (latV_supp hy))).2 fun w hw => ?_
      rw [← conj_herm, ← adelicHermitianForm_wittCoreInclusion_left, conj_herm]
      exact (sd y (latV_supp hy)).1 hy _ (h0' w hw)
  · rintro ⟨h1, h2, h3⟩
    rw [decomp_vec d y, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    exact add_mem (add_mem (sum_mem fun i _ => h1 i) (h0' _ h3)) (sum_mem fun i _ => h2 i)

section Frames

variable {Y Y₀ : Type} [Fintype Y] [DecidableEq Y] [Fintype Y₀] [DecidableEq Y₀]

def colAt {N : ℕ} (F : Frame k N Y) (c : Y) : Fin N → AE D := fun r => q.sec (F.β r c)

theorem colAt_mem {F : Frame k S.rank Y} (h : IntIn q S F L) (c : Y) : colAt q F c ∈ latV S L (· = q.v) := by
  have h1 := (h (Pi.single c 1)).1 fun i => by
    by_cases hi : i = c
    · subst hi; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _
  rw [Matrix.mulVec_single_one] at h1
  exact h1

theorem expand (hL : IsSelfDualC S L) {F : Frame k S.rank Y} (h : IntIn q S F L) {x : Fin S.rank → AE D}
    (hx : x ∈ latV S L (· = q.v)) {m : ℕ} (M : Mx D m S.rank) :
    ∃ a : Y → AE D, (∀ c, a c ∈ intAt D (· = q.v)) ∧ q.e • (M *ᵥ x) = ∑ c, a c • (M *ᵥ colAt q F c) := by
  have h1 : F.β *ᵥ (F.γ *ᵥ fun r => q.pr (x r)) = fun r => q.pr (x r) := by
    rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  have h2 : (fun r => q.sec ((F.β *ᵥ (F.γ *ᵥ fun r => q.pr (x r))) r)) = q.e • x := by
    rw [h1]; funext r; exact q.sec_pr _
  have h3 := (h (F.γ *ᵥ fun r => q.pr (x r))).2 (by rw [h2]; exact smul_mem hL hx (e_mem_intAt q))
  refine ⟨fun c => q.sec ((F.γ *ᵥ fun r => q.pr (x r)) c), fun c => sec_mem_intAt q _ (h3 c), ?_⟩
  simp only [← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum, ← h2]
  congr 1
  generalize (F.γ *ᵥ fun r => q.pr (x r)) = y
  funext r
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colAt, sec_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem mulVec_colMul {l m n : ℕ} (M : Mx D l m) (N : Mx D m n) (i : Fin n) (a : AE D) :
    M *ᵥ colMul N i a = colMul (M * N) i a := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem colMul_zero {m n : ℕ} (i : Fin n) (a : AE D) : colMul (0 : Mx D m n) i a = 0 := by
  funext r; simp only [colMul, Matrix.zero_apply, mul_zero, Pi.zero_apply]

theorem colMul_one {n : ℕ} {v : Pl D} (i j : Fin n) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    colMul (1 : Mx D n n) i a j ∈ intAt D (· = v) := by
  simp only [colMul, Matrix.one_apply]
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]; exact intAt_zero'

theorem unit_line (hL : IsSelfDualC S L) (M : Mx D S.rank ρ) (i : Fin ρ) {t : k} (ht : valuation k t = 1)
    (h : colMul M i (q.sec t) ∈ latV S L (· = q.v)) : colMul M i q.e ∈ latV S L (· = q.v) := by
  have h0 : t ≠ 0 := fun h => by rw [h, map_zero] at ht; exact zero_ne_one ht
  have h1 : t⁻¹ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, ht, inv_one])
  have h2 := smul_mem hL h (sec_mem_intAt q _ h1)
  rwa [colMul_smul, ← sec_mul, inv_mul_cancel₀ h0, sec_one] at h2

theorem monoAt_of_cols (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀) {F : Frame k S.rank Y} {F₀ : Frame k S₀.rank Y₀}
    (h : IntIn q S F L) (h₀ : IntIn q S₀ F₀ L₀)
    (cover : ∀ c, (∃ a, colAt q F c = d.j0 *ᵥ colAt q F₀ a) ∨
      (∃ i t, valuation k t = 1 ∧ colAt q F c = colMul d.jX i (q.sec t)) ∨
      ∃ i t, valuation k t = 1 ∧ colAt q F c = colMul d.jY i (q.sec t))
    (c0 : ∀ a, ∃ c, colAt q F c = d.j0 *ᵥ colAt q F₀ a)
    (cX : ∀ i, ∃ c t, valuation k t = 1 ∧ colAt q F c = colMul d.jX i (q.sec t))
    (cY : ∀ i, ∃ c t, valuation k t = 1 ∧ colAt q F c = colMul d.jY i (q.sec t)) : MonoAt d L L₀ q.v := by
  have hu : ∀ t : k, valuation k t = 1 → q.sec t ∈ intAt D (· = q.v) := fun t ht =>
    sec_mem_intAt q t ((Valuation.mem_integer_iff _ _).2 ht.le)
  have hc : ∀ c, (∀ i, (d.pX *ᵥ colAt q F c) i ∈ intAt D (· = q.v)) ∧ (∀ i, (d.pY *ᵥ colAt q F c) i ∈ intAt D (· = q.v)) ∧
      d.p0 *ᵥ colAt q F c ∈ latV S₀ L₀ (· = q.v) := by
    intro c
    rcases cover c with ⟨a, e⟩ | ⟨i, t, ht, e⟩ | ⟨i, t, ht, e⟩ <;> rw [e]
    · simp only [Matrix.mulVec_mulVec]
      rw [d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec]
      exact ⟨fun _ => intAt_zero', fun _ => intAt_zero', colAt_mem q h₀ a⟩
    · simp only [mulVec_colMul]
      rw [d.pX_jX, d.pY_jX, d.p0_jX, colMul_zero, colMul_zero]
      exact ⟨fun _ => colMul_one _ _ (hu t ht), fun _ => intAt_zero', zero_mem _⟩
    · simp only [mulVec_colMul]
      rw [d.pX_jY, d.pY_jY, d.p0_jY, colMul_zero, colMul_zero]
      exact ⟨fun _ => intAt_zero', fun _ => colMul_one _ _ (hu t ht), zero_mem _⟩
  refine monoAt_of_half q d hL hL₀ (fun x hx => ⟨fun i => ?_, fun i => ?_, ?_⟩) (fun i => ?_) (fun i => ?_) fun w hw => ?_
  · obtain ⟨a, ha, e⟩ := expand q hL h hx d.pX
    have e' := congrFun e i
    rw [Finset.sum_apply] at e'
    change q.e * _ = _ at e'
    rw [e']
    exact intAt_sum' _ _ fun c _ => intAt_mul' (ha c) ((hc c).1 i)
  · obtain ⟨a, ha, e⟩ := expand q hL h hx d.pY
    have e' := congrFun e i
    rw [Finset.sum_apply] at e'
    change q.e * _ = _ at e'
    rw [e']
    exact intAt_sum' _ _ fun c _ => intAt_mul' (ha c) ((hc c).2.1 i)
  · obtain ⟨a, ha, e⟩ := expand q hL h hx d.p0
    rw [e]
    exact sum_mem fun c _ => smul_mem hL₀ (hc c).2.2 (ha c)
  · obtain ⟨c, t, ht, e⟩ := cX i
    exact unit_line q hL _ i ht (e ▸ colAt_mem q h c)
  · obtain ⟨c, t, ht, e⟩ := cY i
    exact unit_line q hL _ i ht (e ▸ colAt_mem q h c)
  · obtain ⟨a, ha, e⟩ := expand q hL₀ h₀ hw d.j0
    rw [e]
    refine sum_mem fun c _ => smul_mem hL ?_ (ha c)
    obtain ⟨c', e'⟩ := c0 c
    exact e' ▸ colAt_mem q h c'

theorem colAt_line {N n : ℕ} {F : Frame k N Y} {c : Y} (M : Matrix (Fin N) (Fin n) D.host.E) (i : Fin n) {t : k}
    (h : ∀ r, F.β r c = t * (ofSplit q).pr (M r i)) : colAt q F c = colMul (rat M) i (q.sec t) := by
  funext r
  change q.sec (F.β r c) = q.sec t * incA D (M r i)
  rw [h, sec_mul_right]; rfl

theorem colAt_core {N n : ℕ} {F : Frame k N Y} {F₀ : Frame k n Y₀} {c : Y} (M : Matrix (Fin N) (Fin n) D.host.E) (a : Y₀)
    (h : ∀ r, F.β r c = (M.map (ofSplit q).pr * F₀.β) r a) : colAt q F c = (rat M : Mx D N n) *ᵥ colAt q F₀ a := by
  funext r
  change q.sec (F.β r c) = ∑ l, incA D (M r l) * q.sec (F₀.β l a)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (incA D _), sec_mul_right, mul_comm]; rfl

theorem monoAt_of_jacFrame (hU : q.UnitAA) (J : JacLev D ρ) {L : Lat J.W} {L₀ : Lat J.W₀} (hL : IsSelfDualC J.W L)
    (hL₀ : IsSelfDualC J.W₀ L₀) {c : ℕ} {F : Frame k J.W.rank (Y₀ ⊕ Fin c)} {F₀ : Frame k J.W₀.rank Y₀} {s hh : k}
    (hs : valuation k s = 1) (hz : valuation k hh = 1) (hF : (ofSplit q).IsJacFrame J s hh F₀ F)
    (h : IntIn q J.W F L) (h₀ : IntIn q J.W₀ F₀ L₀) : MonoAt J.d L L₀ q.v := by
  have hξ : valuation k (ofSplit q).xi = 1 := GlobalTheory.SplitWeilChar.valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  obtain ⟨rfl, h1, h2, h3⟩ := hF
  have hX : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val = i.val →
      ∃ t, valuation k t = 1 ∧ colAt q F (Sum.inr j) = colMul J.d.jX i (q.sec t) := fun i j hj =>
    ⟨_, by rw [map_mul, map_pow, hs, hξ, one_pow, one_mul], colAt_line q J.d.e i (h2 i j hj)⟩
  have hY : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val + i.val + 1 = 2 * ρ →
      ∃ t, valuation k t = 1 ∧ colAt q F (Sum.inr j) = colMul J.d.jY i (q.sec t) := fun i j hj =>
    ⟨_, by rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, map_one, hs, hz, hξ]; simp,
      colAt_line q J.d.e' i (h3 i j hj)⟩
  refine monoAt_of_cols q J.d hL hL₀ h h₀ ?_ (fun a => ⟨Sum.inl a, colAt_core q J.d.i₀ a fun r => h1 r a⟩)
    (fun i => ⟨Sum.inr ⟨i.val, by omega⟩, hX i _ rfl⟩)
    (fun i => ⟨Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, hY i _ (by change 2 * ρ - 1 - i.val + i.val + 1 = _; omega)⟩)
  rintro (a | j)
  · exact Or.inl ⟨a, colAt_core q J.d.i₀ a fun r => h1 r a⟩
  · by_cases hj : j.val < ρ
    · exact Or.inr (Or.inl ⟨⟨j.val, hj⟩, hX _ j rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨2 * ρ - 1 - j.val, by omega⟩, hY _ j (by change j.val + (2 * ρ - 1 - j.val) + 1 = _; omega)⟩)

end Frames

end GlobalTheory.JacMono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EntryDatumTransportBadPrimeAnyTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EntryDatumTransportBadPrimeAnyTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.EntryAny

open GlobalTheory.Transport.Entry

theorem entry_transport_any : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 < B.R.m) (al : (I.idx a).β i) (be : (I.idx a).β (i + 1)) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀) =
        Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) := by
  intro B X I hI l u a i hm al be P p q p' q' k y k' y' hp hpN hp' hpN' hq hq'
  have hX := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hL := hI.idx_ok a
  have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.Transport.Entry.qOf_pos P.1).ne'
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · obtain ⟨M, hM, H⟩ := exists_modulus hp hp' hq hq' ⟨P.1, hP⟩ (pow_ne_zero (I.cst a).B hq0)
    refine ⟨M, hM, fun M₀ hM₀ x x₀ hx => ?_⟩
    obtain ⟨U, U', hU, hU', h⟩ := H M₀ hM₀ x x₀ hx
    have hu := exp_le_val_qOf (GlobalTheory.UnfoldTwoSided.degOne_bad hX.ok l.pr hI.sel_ok P)
    unfold Formalism.L2.Col.frsF
    simp only [dif_pos hP]
    refine (eq_of_near (P := P.1) _ hq0 (val_qOf_lt_one P.1) (pow_ne_zero (I.cst a).B hq0) (fun κ κ' hκ hκ' z => ?_)
      (hL.xiInv i (by omega) al be P) _ _ U U' (hU.mono hu) (hU'.mono hu) h).symm
    refine xiAt_inFr hX l.pr hI.ch_ok hI.sel_ok hL (by omega) al be P κ κ' ?_ ?_ z
    · rw [hL.depthG P hP, pow_one]
      exact hκ
    · rw [hL.depthG P hP, pow_one]
      exact hκ'
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (GlobalTheory.Transport.Entry.qOf_pos P.1) _, fun M₀ hM₀ x x₀ hx => ?_⟩
    have hd := GlobalTheory.Transport.TwistRead.qread I u a i P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hx
    set z₀ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hz₀
    set z₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hz₁
    have hMv : P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) ≤
        P.1.valuation B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).B) := by
      obtain ⟨c, rfl⟩ := hM₀
      rw [Nat.cast_mul, map_mul, Nat.cast_pow]
      refine mul_le_of_le_one_right' ?_
      simpa using P.1.valuation_le_one (K := B.fields.E) (c : 𝓞 B.fields.E)
    have e : z₁ = z₀ + (z₁ - z₀) := by abel
    rw [e]
    refine (hL.xiInv i (by omega) al be P z₀ (z₁ - z₀) fun s l => ?_).symm
    refine intAt_inv_mul (pow_ne_zero _ hq0) ?_
    have e2 : (z₁ - z₀) (Pi.single s 1) l = (LinearMap.toMatrix' z₁ - LinearMap.toMatrix' z₀) l s := by
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.sub_apply, Pi.sub_apply]
    rw [e2]
    exact (hd l s).trans hMv

end GlobalTheory.Transport.EntryAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EntryDatumTransportBadPrimeAnyTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entryDatum_transport_badPrime_anyTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 < B.R.m) (al : (I.idx a).β i) (be : (I.idx a).β (i + 1)) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀) =
        Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) := by
  exact @GlobalTheory.Transport.EntryAny.entry_transport_any
end
end
