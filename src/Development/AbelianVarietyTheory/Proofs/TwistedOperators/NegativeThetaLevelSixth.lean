module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactAction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxX

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := _root_.GlobalTheory.CuspTypeApproxUp.norm_sub_sum_sigma_lt (E := E) (m := m) (δ := δ) I L n J hδ h1 h2

end GlobalTheory.CuspTypeApproxX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingConstant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerPCpt

theorem pure_add' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.add_apply, Pi.add_apply, add_mul]

theorem pure_smul' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem pure_zero' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) φ = 0 := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.zero_apply, Pi.zero_apply, zero_mul]

theorem pure_sub' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.sub_apply, Pi.sub_apply, sub_mul]

theorem isHecke_quot {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  unfold GlobalTheory.LFun.IsHecke at h h' ⊢
  obtain ⟨hc, hx⟩ := h
  obtain ⟨hc', hx'⟩ := h'
  refine ⟨?_, fun x => ?_⟩
  · have hfun : (⇑(χ / χ')) = fun z => χ z / χ' z := funext (MonoidHom.div_apply χ χ')
    rw [hfun]
    exact hc.div' hc'
  · rw [MonoidHom.div_apply, hx x, hx' x, div_one]

theorem resEtaPow_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) (hk : k = n + m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') k := by
  unfold GlobalTheory.WeilM.ResEtaPow at h h' ⊢
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u, hk]
  split_ifs
  · norm_num
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

theorem isPair_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_quot h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_quot h.chars.resα h.chars.resβ (by omega)
    weil := h.weil' }

end GlobalTheory.SquareAgree.KerPCpt

namespace GlobalTheory.SquareAgree.KerPCpt

end GlobalTheory.SquareAgree.KerPCpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LiftTypeDn

theorem hasTypeAt_of_approx {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (ψ : GA D V → ℂ)
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ χ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S χ ∧ ∀ x ∈ C, ‖ψ x - χ x‖ < δ) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S ψ := by
  intro C hC δ hδ
  obtain ⟨χ, hχ, h1⟩ := h C hC (δ / 2) (by linarith)
  obtain ⟨ψ', hψ', h2⟩ := hχ C hC (δ / 2) (by linarith)
  refine ⟨ψ', hψ', fun x hx => ?_⟩
  have e : ψ x - ψ' x = (ψ x - χ x) + (χ x - ψ' x) := by ring
  rw [e]
  have := norm_add_le (ψ x - χ x) (χ x - ψ' x)
  linarith [h1 x hx, h2 x hx]

end GlobalTheory.LiftTypeDn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open scoped ContDiff ComplexOrder

namespace GlobalTheory.ColLiftAut

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}

theorem isThetaFunO_smul (hΦ : IsThetaFunO ψ S T Φ) (c : ℂ) : IsThetaFunO ψ S T (c • Φ) := by
  refine ⟨fun γ w => ?_, ?_, continuous_const.mul hΦ.cont, fun k L hL hf w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hΦ.quasi γ w]; ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu' => ?_⟩
    funext w
    have := congrFun (h u hu hu') w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]; ring
  · exact contDiff_const.mul (hΦ.smooth k L hL hf w)

theorem kernel_left (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ) (g : GA D S) {γ : GA D T}
    (hγ : γ ∈ GQ T) (h : GA D T) : thetaKO om g (γ * h) Φ = thetaKO om g h Φ := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hΦ)

theorem kernel_right (g : GA D S) (h k : GA D T) : thetaKO om g (h * k) Φ = thetaKO om g h (om (1, k) Φ) := by
  have e : ((g, h * k) : GA D S × GA D T) = (g, h) * (1, k) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]

theorem lift_continuous (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    Continuous fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  have := GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector ψ S T χS χT om hW hS ν 𝓕 hν h𝓕 ℂ
    (LinearMap.toSpanSingleton ℂ _ Φ) (fun x => isThetaFunO_smul hΦ x) φ hφ.cont hφ.left
  refine this.congr fun h => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [LinearMap.toSpanSingleton_apply, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end GlobalTheory.ColLiftAut

namespace GlobalTheory.ColLiftAut

theorem posDef_of_nodeIs {D : D7} {N : GlobalTheory.Grid.Node D} {ν q : ℕ} {Sp : D.what₂.Tau → SPar} (h : N.Is ν q Sp) (hq : q = 0) :
    ∀ τ, (gramAt D N.V τ).PosDef := fun τ =>
  GlobalTheory.RepsObj.gramAt_posDef (fun σ => by rw [h.sig σ, h.rank, hq]; simp) h.sigOK τ

end GlobalTheory.ColLiftAut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FinPl.LocGlob

variable {D : D7}

theorem swap_finPart_pure (α : Af D.host.F) (e : D.host.E) :
    Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e)) = e ⊗ₜ[D.host.F] α := by
  have h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  rw [h1]
  rfl

theorem mem_of_local {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (z : Fin S.rank → D.host.E)
    (hz : ∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈
      GlobalTheory.FinPl.latV S L (· = v)) : z ∈ L := by
  classical
  have hlat := hL.1
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have hspan := Submodule.IsFullLattice.span_eq_top (self := hfull S L hL)
  obtain ⟨d, hd, hdz⟩ := GlobalTheory.FinPl.exists_int_smul_le (Submodule.span (𝓞 D.host.E) {z}) L
    (Submodule.fg_span_singleton z) hspan
  set T := (GlobalTheory.FinPl.finite_places_int (D := D) d hd).toFinset with hT
  set β : Af D.host.F := 1 - ∑ v ∈ T, GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) with hβ
  have hβv : ∀ w, evalV D.host.F w β = if w ∈ T then 0 else 1 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hβ, map_sub, map_one, map_sum]
    simp only [GlobalTheory.FinPl.LatMem.evalV_indP]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  have hoff : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) ∈
      GlobalTheory.FinPl.latV S L (fun w => w ∉ T) := by
    apply GlobalTheory.FinPl.LocAgree.latV_le_of_int_smul_on S (Submodule.span (𝓞 D.host.E) {z}) L d hd hdz
    · intro v hv hmem
      exact hv ((Set.Finite.mem_toFinset _).2 hmem)
    · apply AddSubgroup.subset_closure
      refine ⟨β, fun w => ?_, fun w hw => ?_, 1, rfl, z, Submodule.mem_span_singleton_self z, rfl⟩
      · rw [hβv]
        split_ifs
        · exact zero_mem _
        · exact one_mem _
      · rw [hβv, if_pos (not_not.1 hw)]
  have hall : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    have e : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) =
        ∑ v ∈ T, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) +
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) := by
      funext i
      rw [Pi.add_apply, Finset.sum_apply, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]
      congr 1
      have hpa : ∀ a b : Af D.host.F, pairA D.host.F 0 a + pairA D.host.F 0 b = pairA D.host.F 0 (a + b) :=
        fun a b => Prod.ext (add_zero 0) rfl
      have hsum : ∀ (s : Finset (Pl D)) (f : Pl D → Af D.host.F),
          ∑ v ∈ s, pairA D.host.F 0 (f v) = pairA D.host.F 0 (∑ v ∈ s, f v) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => exact Prod.ext rfl rfl
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hpa]
      rw [hsum, hpa, hβ, add_sub_cancel]
    rw [e]
    exact add_mem (sum_mem fun v _ => GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) (hz v))
      (GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) hoff)
  have hhat := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ hall
  have e2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (z i) := by
    funext i
    rw [swap_finPart_pure]
    rfl
  rw [e2] at hhat
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff hlat.fg hspan z).1 hhat

theorem mem_of_mem_latV_all : ∀ {D : D7} {S : HSp D} {L : Lat S}, IsSelfDualC S L → (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) :=
  fun hL z hz => mem_of_local hL z hz

end GlobalTheory.FinPl.LocGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletionsStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions : ∀ {D : D7} {S : HSp D} {L : Lat S}, IsSelfDualC S L → (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) := by
  first | exact @GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all | exact GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all | (intros; apply GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.LatStdStab
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem latAt_mul_inv_eq_stdL : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ k : FinPt G X,
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X)) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V X) k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X))) →
    GlobalTheory.SumSize.latAt S X (k * (S.N.u X)⁻¹) = stdL D _ := by
  intro D T L sc G W S X hX k hk
  have hC := GlobalTheory.MovedHomLat.colLat_fin (S.N.fr X)
  have hsp := GlobalTheory.MovedHomLat.colLat_span (S.N.fr X)

  have key : ∀ y, y ∈ Formalism.UG.CS.globLat (finG (G.V X) (k * (S.N.u X)⁻¹)) (G.Λ X) ↔ y ∈ colLat (S.N.fr X) := by
    intro y
    have e : finG (G.V X) (k * (S.N.u X)⁻¹) * Formalism.IndefR.Lev.finE (G.V X) (S.N.u X).1 =
        Formalism.IndefR.Lev.finE (G.V X) k.1 := by
      show Formalism.IndefR.Lev.finE (G.V X) ((k * (S.N.u X)⁻¹ : FinPt G X) : GA D (G.V X)) * _ = _
      rw [← map_mul]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [GlobalTheory.MovedHomLat.globLat_mul_iff _ _ _ _ (S.N.u_lat X hX), e, GlobalTheory.MovedHomLat.mem_globLat_iff]
    rw [hk, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact GlobalTheory.CongStdLoc.incl_mem_hatL_iff (F := D.host.F) (Module.Finite.iff_fg.1 hC) hsp y
  ext z
  simp only [GlobalTheory.SumSize.latAt, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [key]
  have := congrArg (z ∈ ·) (GlobalTheory.ColStd.colLat_comap_eq_stdLat (S.N.fr X))
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at this
  exact Iff.of_eq this

end GlobalTheory.LatStdStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeOf_stabiliser_mul_inv_eq_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ k : FinPt G X,
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X)) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V X) k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X))) →
    GlobalTheory.SumSize.latAt S X (k * (S.N.u X)⁻¹) = stdL D _ := by
  first | exact @GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL | exact GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL | (intros; apply GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptiona
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptiona
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.ModulUnit

variable {D : D7}

theorem exists_sep {v v' : GlobalTheory.FinPl.Pl D} (h : v' ≠ v) :
    ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hc))

theorem idV_eq_one_of_mem {v : GlobalTheory.FinPl.Pl D} {I : Ideal (𝓞 D.host.E)} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (hI : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ I) :
    GlobalTheory.SeeSaw.idV ((I : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 1 v := by
  refine le_antisymm (GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v) ?_
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, ha, rfl⟩
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα h0
  rw [GlobalTheory.IdVGen.tmul_eq ht α]
  refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, I.mul_mem_right o hI, ?_⟩
  rw [map_mul]
  rfl

theorem idV_mul_of_eq_one {𝔞 I : GlobalTheory.SeeSaw.FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : GlobalTheory.SeeSaw.idV I v = GlobalTheory.SeeSaw.idV 1 v) : GlobalTheory.SeeSaw.idV (𝔞 * I) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  rcases eq_or_ne 𝔞 0 with rfl | h0
  · rw [zero_mul]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h0
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 I x 1 hx0 one_ne_zero hx
    (GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 h)
  rw [mul_one] at this
  ext s
  rw [this, hx]

variable {T : Type} {L : LevCh D T}

theorem exists_mem_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modul sc := by
  classical
  have hsep : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal :=
    fun v' hv' => exists_sep fun e => hv (e ▸ hv')
  choose! t ht using hsep
  refine ⟨∏ v' ∈ P.S0, t v' ^ P.depth sc v', fun hm => ?_, ?_⟩
  · obtain ⟨v', hv', hm'⟩ := (haveI := v.isPrime; Ideal.IsPrime.prod_mem_iff.1 hm)
    exact (ht v' hv').2 (v.isPrime.mem_of_pow_mem _ hm')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h : t v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hv']; exact (ht v' hv').1
    exact h
end GlobalTheory.ModulUnit

namespace GlobalTheory.ModulUnit

variable {D : D7} {T : Type} {L : LevCh D T}

theorem conj_smul_algebraMap (s : 𝓞 D.host.F) :
    D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
  apply RingOfIntegers.ext
  show D.host.conj ((s : D.host.F) : D.host.E) = ((s : D.host.F) : D.host.E)
  exact (D.host.conjE_mem_hostF_iff _).1 (s : D.host.F).2

theorem exists_mem_modulBar (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modulBar sc := by
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  refine ⟨s, hs, ?_⟩
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  rwa [conj_smul_algebraMap] at this

end GlobalTheory.ModulUnit


open GlobalTheory.ModulUnit in
theorem GlobalTheory.ChiGrid.Places.idV_mul_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  obtain ⟨s', hs', hm'⟩ := exists_mem_modulBar P sc hv
  exact ⟨idV_mul_of_eq_one (idV_eq_one_of_mem hs hm), idV_mul_of_eq_one (idV_eq_one_of_mem hs' hm')⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptionaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_mul_modulus_offExceptional : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ChiGrid.Places.idV_mul_modul | exact GlobalTheory.ChiGrid.Places.idV_mul_modul | (intros; apply GlobalTheory.ChiGrid.Places.idV_mul_modul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFlatLaws

theorem flatS_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y _ f hf
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  refine ⟨fun N hN => ?_, fun ξ => ?_⟩
  · exact GlobalTheory.FlatShiftPf.flatAt_shift hψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν s.vU.unit.1 _ _ f N hN
  · exact GlobalTheory.FlatLawsDuality.flatAt_iso dV dW s.vS s.vT s.vU.ν _ _ hψ f hf ξ

end GlobalTheory.AscFlatLaws

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_heisenberg_and_hom_transformation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  first | exact @GlobalTheory.AscFlatLaws.flatS_laws | exact GlobalTheory.AscFlatLaws.flatS_laws | (intros; apply GlobalTheory.AscFlatLaws.flatS_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthCongruenceSubgroupCompactOpenPlacesToAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthCongruenceSubgroupCompactOpenPlacesToAdeles
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PlaceLevelCosets

variable {D : D7}

theorem mem_GinfC_of_off (V : HSp D) (S : GlobalTheory.FinPl.Pl D → Prop) {g : GA D V} (h1 : g ∈ grpOff V S)
    (h2 : g ∈ grpOff V (fun v => ¬ S v)) : g ∈ GinfC V := by
  have h3 : g ∈ grpOff V (fun _ => True) := by
    refine GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.2 fun i j => ?_
    have a := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h1 i j
    have b := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h2 i j
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf] at a b ⊢
    intro w
    by_cases hw : S w.1
    · exact a ⟨w.1, hw⟩
    · exact b ⟨w.1, hw⟩
  exact GlobalTheory.FinPl.OffInh.mem_GinfC_of_all (fun _ => trivial) h3


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem mem_lev_of_inK {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node)
    (hΛ : Submodule.IsFullLattice D.host.E (G.Λ X)) {κ : GA D (G.V X)}
    (hκ : InK (G.V X) (G.Λ X) (fun v => v ∉ G.pl.S0) κ) : κ ∈ lev G X := by
  classical
  have hfg : (G.Λ X).FG := Submodule.IsLattice.fg D.host.E (G.Λ X)
  obtain ⟨hGf, hpr⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff (G.V X) _ κ).1 hκ.1
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E (G.V X).rank (G.Λ X) hΛ
  have hS : Lev.finE (G.V X) κ ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (G.V X) β (G.Λ X) hβ κ).2
      (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK (G.V X) (G.Λ X) hfg _ hκ))
  refine ⟨hGf, ?_⟩
  show Lev.finE (G.V X) κ ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  rw [← GlobalTheory.ColMeas.princ_eq_congLev D.sp.cm (G.V X).gram hβ G.modul]
  refine ⟨GlobalTheory.LevSplit.finE_mem_UA (G.V X) κ, ?_⟩
  obtain ⟨y, hy⟩ := hS
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, hy, fun a b => ?_⟩

  have hE : ∀ c d, ((Lev.finE (G.V X) κ).1 - 1) c d = toEAf D ((Formalism.L2.Theta.mt (G.V X) κ - 1) c d) := by
    intro c d
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
    congr 1
    by_cases h : c = d
    · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero]
  have hW : ∀ w ∈ G.pl.W0, ((Lev.finE (G.V X) κ).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    have h1 := (GlobalTheory.FinPl.KOpen.proj_eq_one_iff (G.V X) v κ).1 (hpr v (not_not.2 hv))
    refine Matrix.ext fun c d => ?_
    rw [Matrix.map_apply, hE, Matrix.zero_apply]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt v _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero v _ (h1 c d)) _ (G.pl.under_w hv)
  have hconj : (Lev.finE (G.V X) κ).1 = β.1 * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 * (β⁻¹).1 := by
    rw [← hy]; rfl
  have hY := GlobalTheory.LevRedTriv.conj_sub_one β _ _ hconj
  refine (GlobalTheory.FunObj.Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
  have hM : ((Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    rw [hY, Matrix.map_mul, Matrix.map_mul, hW w hw, Matrix.mul_zero, Matrix.zero_mul]
  have e0 : GlobalTheory.StdFrames.cpt w (((y.1 - 1) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 0 := by
    rw [GlobalTheory.LevRedTriv.coe_sub_one_apply]
    exact congrFun (congrFun hM a) b
  rw [e0, map_zero]
  exact zero_le'

theorem idAt_le_idOff_compl (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D (fun v => ¬ P v) ≤ idOff D P := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, not_not.2 w.2⟩

theorem idAt_le_idOff_compl' (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D P ≤ idOff D (fun v => ¬ P v) := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, w.2⟩

end GlobalTheory.PlaceLevelCosets


open GlobalTheory.PlaceLevelCosets GlobalTheory.FinPl.PlacesAdeles in
theorem GlobalTheory.PlaceLevelCosets.levCoset_of_places : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → (lev G (.grid i 0) ≤ GfC _ ∧ IsCompact (lev G (.grid i 0) : Set (GA D (G.V (.grid i 0)))) ∧ IsOpen (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0))))) ∧ ∀ (R : Subgroup (GA D (G.V (.grid i 0)))) h, (∀ v ∉ G.pl.S0, ∀ h₁ ∈ grpAt _ (· = v), ∀ h₂ ∈ grpOff _ (· = v), h = h₁ * h₂ → CosetAt _ R (G.Λ (.grid i 0)) v h₁) → (∀ h₁ ∈ grpAt _ (fun v => v ∈ G.pl.S0), ∀ h₂ ∈ grpOff _ (fun v => v ∈ G.pl.S0), h = h₁ * h₂ → ∃ r ∈ R, r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid i 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ h₁ = r * k) → ∃ r ∈ R, ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid i 0), h = r * a * k := by
  intro D _ T L μ0 hL sc G W M _ i hi
  have hV := node_isV G hL (X := .grid i 0) ⟨hi, Nat.zero_le _⟩
  have hlat : Submodule.IsFullLattice D.host.E (G.Λ (.grid i 0)) :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd
  have hoc := congLev_open_compact (G.V (.grid i 0)) hlat (G.pl.modul_ne_bot sc)
  refine ⟨⟨inf_le_left, hoc.2, ?_⟩, ?_⟩
  · have e : (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0)))) =
        Subtype.val ⁻¹' ((((congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul).comap
          (Lev.finE (G.V (.grid i 0))) : Subgroup (GA D (G.V (.grid i 0)))) : Set (GA D (G.V (.grid i 0))))) := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hoc.1.preimage continuous_subtype_val
  · intro R h hA hB
    have hsd : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := hV.sd
    have hoff : ∀ v, (fun v => v ∉ G.pl.S0) v → ∃ hv ∈ grpAt (G.V (.grid i 0)) (· = v), ∃ h' ∈ grpOff (G.V (.grid i 0)) (· = v),
        h = hv * h' ∧ ∃ r ∈ R, r ∈ grpAt (G.V (.grid i 0)) (· = v) ∧ ∃ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ ∧
          hv = r * κ := by
      intro v hv
      obtain ⟨x, hx, y, hy, e⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 (G.V (.grid i 0))).1 h
      exact ⟨x, hx, y, hy, e, hA v hv x hx y hy e⟩
    obtain ⟨r₁, hr₁, hr₁P, g, hg, κ₁, hκ₁, e₁⟩ :=
      GlobalTheory.FinPl.placesToAdeles_all D (G.V (.grid i 0)) (G.Λ (.grid i 0)) (fun v => v ∉ G.pl.S0) hsd R h hoff
    obtain ⟨hdec, hcomm, -, -⟩ := (GlobalTheory.FinPl.localComponents D (fun v => v ∈ G.pl.S0)).2 (G.V (.grid i 0))
    obtain ⟨g₁, hg₁, g₂, hg₂, eg⟩ := hdec g
    have hin : ∀ x ∈ grpAt (G.V (.grid i 0)) (fun v => v ∉ G.pl.S0), x ∈ grpOff (G.V (.grid i 0)) (fun v => v ∈ G.pl.S0) :=
      fun x hx => congGrp_mono (idAt_le_idOff_compl (fun v => v ∈ G.pl.S0)) hx
    have hr₁off := hin r₁ hr₁P
    have hκ₁off := hin κ₁ hκ₁.1
    have hg₁off : g₁ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) :=
      congGrp_mono (idAt_le_idOff_compl' (fun v => v ∈ G.pl.S0)) hg₁
    have hg₂off : g₂ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) := by
      have : g₂ = g₁⁻¹ * g := by rw [eg]; group
      rw [this]
      exact mul_mem (inv_mem hg₁off) hg
    have c1 : r₁ * g₁ = g₁ * r₁ := (hcomm g₁ hg₁ r₁ hr₁off).symm
    have eh : h = g₁ * (r₁ * g₂ * κ₁) := by
      rw [e₁, eg, ← mul_assoc, ← mul_assoc, ← mul_assoc, c1]
    obtain ⟨r₀, hr₀, -, k₀, hk₀, hk₀S, ek⟩ := hB g₁ hg₁ _ (mul_mem (mul_mem hr₁off hg₂) hκ₁off) eh
    have c2 : k₀ * r₁ = r₁ * k₀ := hcomm k₀ hk₀S r₁ hr₁off
    have c3 : k₀ * g₂ = g₂ * k₀ := hcomm k₀ hk₀S g₂ hg₂
    refine ⟨r₀ * r₁, R.mul_mem hr₀ hr₁, g₂, mem_GinfC_of_off _ _ hg₂ hg₂off, k₀ * κ₁,
      mul_mem hk₀ (mem_lev_of_inK G _ hlat hκ₁), ?_⟩
    calc h = g₁ * (r₁ * g₂ * κ₁) := eh
      _ = r₀ * (k₀ * r₁) * g₂ * κ₁ := by rw [ek]; simp only [mul_assoc]
      _ = r₀ * r₁ * (k₀ * g₂) * κ₁ := by rw [c2]; simp only [mul_assoc]
      _ = r₀ * r₁ * g₂ * (k₀ * κ₁) := by rw [c3]; simp only [mul_assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthCongruenceSubgroupCompactOpenPlacesToAdelesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthCongruenceSubgroup_compactOpen_places_to_adeles : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → (lev G (.grid i 0) ≤ GfC _ ∧ IsCompact (lev G (.grid i 0) : Set (GA D (G.V (.grid i 0)))) ∧ IsOpen (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0))))) ∧ ∀ (R : Subgroup (GA D (G.V (.grid i 0)))) h, (∀ v ∉ G.pl.S0, ∀ h₁ ∈ grpAt _ (· = v), ∀ h₂ ∈ grpOff _ (· = v), h = h₁ * h₂ → CosetAt _ R (G.Λ (.grid i 0)) v h₁) → (∀ h₁ ∈ grpAt _ (fun v => v ∈ G.pl.S0), ∀ h₂ ∈ grpOff _ (fun v => v ∈ G.pl.S0), h = h₁ * h₂ → ∃ r ∈ R, r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid i 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ h₁ = r * k) → ∃ r ∈ R, ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid i 0), h = r * a * k := by
  first | exact @GlobalTheory.PlaceLevelCosets.levCoset_of_places | exact GlobalTheory.PlaceLevelCosets.levCoset_of_places | (intros; apply GlobalTheory.PlaceLevelCosets.levCoset_of_places <;> assumption)
end
end
