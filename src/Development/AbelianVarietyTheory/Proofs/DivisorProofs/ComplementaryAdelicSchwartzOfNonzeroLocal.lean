module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.RestCofactor

variable {F : Type} [Field F] [NumberField F]

def shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) : κ → Af F :=
  fun i => y i + (singleFin v (x₀ i) - singleFin v (evalV F v (y i)))

theorem evalV_shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) (i : κ) :
    evalV F v (shiftFin v x₀ y i) = x₀ i := by
  simp only [shiftFin, map_add (f := _), map_sub, evalV_singleFin_self]
  abel

theorem shiftFin_back (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) :
    shiftFin v (fun i => evalV F v (y i)) (shiftFin v x₀ y) = y := by
  funext i
  rw [shiftFin, evalV_shiftFin]
  simp only [shiftFin]
  abel

theorem continuous_shiftFin (v : Pl (F := F)) {κ : Type} :
    Continuous fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2 := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  refine continuous_pi fun i => ?_
  have h2 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.2 i := (continuous_apply i).comp continuous_snd
  have h1 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.1 i := (continuous_apply i).comp continuous_fst
  exact h2.add (((continuous_singleFin v).comp h1).sub ((continuous_singleFin v).comp (hev.comp h2)))

theorem mem_SB_shift (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) {φ' : (κ → Fv F v) → ℂ}
    (hφ' : φ' ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    (fun y : κ → Af F => φ' (fun i => evalV F v (y i)) * g (shiftFin v x₀ y)) ∈ SB (κ → Af F) := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have hE : Continuous fun y : κ → Af F => fun i => evalV F v (y i) :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have hS : Continuous (shiftFin v x₀) :=
    (continuous_shiftFin v).comp (continuous_const.prodMk continuous_id)
  refine ⟨(hφ'.1.comp_continuous hE).mul (hg.1.comp_continuous hS), ?_⟩
  have hK : IsCompact ((fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2) ''
      (tsupport φ' ×ˢ tsupport g)) := (IsCompact.prod hφ'.2 hg.2).image (continuous_shiftFin v)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  have ha : φ' (fun i => evalV F v (y i)) ≠ 0 := left_ne_zero_of_mul hne
  have hb : g (shiftFin v x₀ y) ≠ 0 := right_ne_zero_of_mul hne
  exact hy ⟨(fun i => evalV F v (y i), shiftFin v x₀ y),
    ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, shiftFin_back v x₀ y⟩

theorem rest_of_rest : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  intro F _ _ κ _ v φ φ' r hφ hφ' hr
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  refine ⟨hr.1, ?_⟩
  let z : (κ → AF F) → κ → AF F := fun x i =>
    pairA F 0 (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2))
  have hz : ∀ x, At (evFin F v) (z x) := by
    intro x u hu
    funext i
    refine Prod.ext ?_ ?_
    · change u.1 * 0 = 0
      exact mul_zero _
    · change u.2 * (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2)) = 0
      refine af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw
        have : evalV F w u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [map_sub, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_zero, mul_zero]
  have h1 : ∀ x i, ((x + z x) i).1 = (x i).1 := fun x i => by
    change (x i).1 + 0 = (x i).1
    exact add_zero _
  have h2 : ∀ x i, ((x + z x) i).2 = shiftFin v x₀ (fun i => (x i).2) i := fun x i => rfl
  have hev : ∀ x i, evFin F v ((x + z x) i) = x₀ i := fun x i => by
    change evalV F v ((x + z x) i).2 = x₀ i
    rw [h2, evalV_shiftFin]
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => φ' (fun i => evFin F v (x i)) * Φ (x + z x)
      map_add' := fun Φ Ψ => funext fun x => by simp only [Pi.add_apply]; ring
      map_smul' := fun c Φ => funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hL : schA F κ ≤ (schA F κ).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨f, _, mem_SB_shift v x₀ hφ' hg, funext fun x => ?_⟩
    change φ' (fun i => evFin F v (x i)) * pureA F f g (x + z x) = _
    simp only [pureA, h1, h2]
    change _ = _ * (φ' (fun i => evFin F v (x i)) * _)
    ring
  have key : tens (evFin F v) φ' r = (φ x₀)⁻¹ • L (tens (evFin F v) φ r) := by
    funext x
    change φ' (fun i => evFin F v (x i)) * r x =
      (φ x₀)⁻¹ * (φ' (fun i => evFin F v (x i)) * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x)))
    have hx : φ x₀ ≠ 0 := hx₀
    simp only [hev, hr.1 x (z x) (hz x)]
    rw [mul_left_comm (φ x₀)⁻¹, ← mul_assoc (φ x₀)⁻¹, inv_mul_cancel₀ hx, one_mul]
  rw [key]
  exact Submodule.smul_mem _ _ (hL hr.2)

end GlobalTheory.RestCofactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  first | exact @GlobalTheory.RestCofactor.rest_of_rest | exact GlobalTheory.RestCofactor.rest_of_rest | (intros; apply GlobalTheory.RestCofactor.rest_of_rest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory.BigTop

theorem famHyp_of_working_duty : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps),
    GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  intro 𝒜 eps Fm hW hD
  obtain ⟨⟨⟨⟨_, hDvd, _, hBox, hQD, hCYL⟩, hSm⟩, hTw⟩, hCE, hTu, hDG⟩ := hW
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm hD
  exact ⟨h1, h2, h3, h4, h5, hDvd, hBox, hQD, hCYL, hSm, hTw, hCE, hTu, hDG⟩

end GlobalTheory.BigTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDutiesStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyHypotheses_of_workingClass_sevenDuties : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  first | exact @GlobalTheory.BigTop.famHyp_of_working_duty | exact GlobalTheory.BigTop.famHyp_of_working_duty | (intros; apply GlobalTheory.BigTop.famHyp_of_working_duty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)]

theorem fg_htLat (P : Point p v O (𝓞 E)) (τ : E →+* ℂ) : (htLat c P τ).FG := by
  classical
  unfold htLat
  split_ifs
  · exact P.fg_latTQuot _ _
  · exact fg_inf P.integers P.fg_latT _

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_isHTFrame (hs : ∀ a : 𝓞 E, star a = H.bar a) (hv : v.Integers O) {T : CDVR} {io : c.F →+* T.Fr}
    (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O)
    (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) :
    ∃ y : FrPt Xo c C, IsHTFrame p v O y₀ k y := by
  classical
  letI := io.toAlgebra
  obtain ⟨P, ψ, hP⟩ := GlobalTheory.CompHt.exists_pointOver E H Dw l Xo c p C v O hs hv T io y₀ hy k.toRingHom kO hk
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c _ C k y₀.1
  obtain ⟨x, hx⟩ := GlobalTheory.CompHt.TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz
  have hli : ∀ τ, LinearIndependent C fun j => P.bLie (x τ j) := fun τ =>
    (GlobalTheory.CompHt.alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P (GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hP)).2 _ (x τ)
      (GlobalTheory.CompHt.linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ (x τ) (hx τ))
  have hmem : ∀ τ j, P.bLie (x τ j) ∈ htLat c P τ := fun τ j =>
    wRec_le_htLat P τ ⟨⟨x τ j, (hx τ j).isEig hP (z.eig τ j)⟩, rfl⟩
  choose g hg0 hg1 hg2 using fun τ => GlobalTheory.CompHt.FlagBasis.exists_adapted_basis O C P.V v hv (Dw.mult τ) (htLat c P τ) (fg_htLat P τ)
    (fun j => P.bLie (x τ j)) (hli τ) fun j => ⟨1, one_ne_zero, by rw [one_smul]; exact hmem τ j⟩
  obtain ⟨y, hy', -⟩ := existsUnique_frChg E H Dw l Xo c C z g 1 fun τ => by
    rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg0 τ i j hij]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hg1 τ i).isUnit
  exact ⟨y, (GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c).1.2.2.2.2.1 C y, kO, P, ψ, z, hP, hz, g, _, x, hy', hg0,
    by simp, hx, hg2⟩

end General

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

theorem exists_isHTFrameCp {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p])
      (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hy
  letI := io.toAlgebra
  letI : Algebra c.F ℂ_[p] := (k.comp io).toAlgebra
  letI := H.starRing
  obtain ⟨y, h⟩ := exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p]) (fun _ => rfl)
    (PadicComplexInt.integers p) y₀ hy { k with commutes' := fun _ => rfl } kO hk
  exact ⟨p, hp, _, _, y, h⟩

end GlobalTheory.CompHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecond
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerAll


open NumberField Matrix Complex MeasureTheory IsDedekindDomain in
open scoped TensorProduct Classical ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.AdTh.SerAll.lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) :
    _root_.Formalism.L2.Pj.lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ _root_.GlobalTheory.PtId.degW Dw a := by
  have hy : 0 < 2 * Real.pi * x := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    Real.rpow_def_of_pos hy]
  unfold _root_.Formalism.L2.Pj.lieFac _root_.GlobalTheory.PtId.degW
  congr 1
  push_cast
  ring


end GlobalTheory.AdTh.SerAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj.LocTensor

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem condLE_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {e e' : ℕ} (he : e ≤ e') {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : CondLE ϖ e' χ :=
  fun x hx => h x ⟨hx.1, hx.2.trans (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_right_of_le_one' hϖ.mem he)⟩

theorem isNatDatum_squareFlip [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ C)
    {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {ϖ : kˣ} {e e' : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) (he : e ≤ e') (P : Finset C)
    {Φ : Matrix A' C k → ℂ} (hΦ : IsNatDatum ϖ e' Φ) : IsNatDatum ϖ e' (squareFlip μ σ ψ (α / β) ϖ e' P Φ) := by
  refine (GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A C ψ⁻¹ ϖ e' Pᶜ h.unif h.inv.cond).2 _ ?_
  rw [← latA_blockLat]
  exact GlobalTheory.FrameDepth.hasDepth_phiA k A A' C μ (hμ := hμ) σ _ ϖ e' _ _ h.unif (h.one_le.trans he) (condLE_mono h.unif he h.condν)
    ((GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A' C ψ ϖ e' P h.unif h.cond).1 _ hΦ)

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem isNatDatum_flipAt (hL : L.Is μ₀) (W : G.Weil) {t : T} (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {n : ℕ} (hn : depthAt G w ≤ n)
    {Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ} (hΦ : IsNatDatum (unifAt w) n Φ) :
    IsNatDatum (unifAt w) n (flipAt W t i j w n Φ) := by
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  have := isHaarMeasure_haarVol h2.1 h2.2
  rw [flipAt, ← Grid.alpha_div_beta]
  exact isNatDatum_squareFlip _ _ ((Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2) hn _ hΦ

theorem local_tensors (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) :
    (∃ e, IsIdemSum e (locPl G t)) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeSmall t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ Φ) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeBig t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ Φ) ∧
    ((∀ w ∈ locPl G t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ n Φ, (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' ∧ ∀ b, ∃ a, ρ.Matched a b ∧ IsMatched B t ρ i j (tensT W a τ) (tensT W b τ')) := by
  refine ⟨exists_idemSum_locPl hL G t, fun e he n Φ h => exists_hasLocal_small B ρ t i j hL he h,
    fun e he n Φ h => exists_hasLocal_big B ρ t i j hL he h, fun hb n Φ h => ?_⟩
  obtain ⟨τ, τ', H⟩ := exists_hasFlip_of_nat B ρ t i j hL (fun w hw => (h w hw).2)
    fun w hw => isNatDatum_flipAt hL W i j hw (hb w hw) (h w hw).1 (h w hw).2
  refine ⟨τ, τ', H, fun b => ?_⟩
  obtain ⟨a, ha⟩ := ρ.exists_matched i j b
  exact ⟨a, ha t, a, b, τ, τ', n, Φ, ha t, h, H, rfl, rfl⟩

end GlobalTheory.FunObj.LocTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChain
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnAtPlacesBase

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

theorem on_of_has_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : HasIndexBound O) (hD : LeafData O) (hJ : GlobalTheory.TraceClassRank.RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : HasTwistBound O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hE : HasExpBound N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ∃ err, ONwith S N err := by
  obtain ⟨Th1, a, r1, r2, de2, hT0⟩ := hT0
  obtain ⟨ε, h1⟩ := h1
  obtain ⟨-, Jp, hJS, hJE⟩ := hE
  exact ⟨_, GlobalTheory.TraceClassRank.on_core_atPlaces N
    ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2, ε0 := ε, Jp := Jp } : OnObj S P c) CE hRk
    hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1⟩

end Free

theorem on_base_atPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hO s N C hOk h1 h2 hM hμ hth hU hB hrat hRk hSq hY hSup hSp hS hT0
    hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1
  classical
  obtain ⟨hc, hinj, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  have hN : TieLevelNum O (rankPred D.R) D.R.f := by
    letI := st
    letI := hostAlg D
    refine ⟨hd.f_eq, ?_⟩
    rw [hO.rr_eq, OntoChain.rank_eq]
    push_cast
    rfl
  obtain ⟨w, hw⟩ := GlobalTheory.BigOnBase.exists_tieCoord_base ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hM.HV hM.jV hM.HW hμ (phasedLift_one hth) hU hB hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact on_of_has_atPlaces N (withCoord O w) C hRk hMk hSup hP hw hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1

end GlobalTheory.OnAtPlacesBase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChainStatement
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlacesBoundChain_twoRunChain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  first | exact @GlobalTheory.OnAtPlacesBase.on_base_atPlaces | exact GlobalTheory.OnAtPlacesBase.on_base_atPlaces | (intros; apply GlobalTheory.OnAtPlacesBase.on_base_atPlaces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.AnnCompactStd

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b := by
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) = 0 + 0
  exact (add_zero 0).symm

theorem exists_psi_fin_trivial {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
      ψ (pairA F 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) * y)) = 1 := by
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨ψ (pairA F 0 y), mem_sphere_zero_iff_norm.2 (GlobalTheory.StdCharFromIsStd.norm_psi_fin hψ y)⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        show ψ (pairA F 0 0) = 1
        exact AddChar.map_zero_eq_one ψ
      map_add_eq_mul' := fun a b => by
        apply Subtype.ext
        show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
        rw [pairA_zero_add, AddChar.map_add_eq_mul] }
  have hχ : Continuous χ :=
    Continuous.subtype_mk (hψ.1.comp (continuous_const.prodMk continuous_id)) _
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_finiteChar_mul_eq_one χ hχ
  refine ⟨d, hd0, fun y hy => ?_⟩
  have h := congrArg (fun z : Circle => (z : ℂ)) (hd y hy)
  exact h

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_mul_mem_of_forall {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (pairA F 0 (z * t)) = 1) →
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) * z ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  obtain ⟨d, hd0, hd⟩ := exists_psi_fin_trivial hψ
  obtain ⟨m, hm0, hm⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  refine ⟨m * d, mul_ne_zero (nonZeroDivisors.ne_zero hm0) hd0, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) z
  set δ : F := algebraMap (𝓞 F) F d with hδ
  have hint : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := fun a =>
    GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a
  have htr : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) = n := by
    intro a
    have h1 := hz (algebraMap F _ δ * algebraMap F _ (algebraMap (𝓞 F) F a))
      (Subring.mul_mem _ (hint d) (hint a))
    have hsplit : z * (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * δ * algebraMap (𝓞 F) F a) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * ((z - algebraMap F _ k) *
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) := by
      rw [map_mul, map_mul]; ring
    rw [hsplit, pairA_zero_add, AddChar.map_add_eq_mul, hd _ (Subring.mul_mem _ hk (hint a)), mul_one,
      GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
      push_cast
      exact mul_right_cancel₀ hne hn
    exact_mod_cast h2
  have hdual : k * δ ∈ ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rw [FractionalIdeal.coeToSubmodule_dual_one, Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨n, hn⟩ := htr b
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩
  obtain ⟨b, hb⟩ := hm _ hdual
  have hsum : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (m * d)) * z =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F b) +
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F m) *
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (z - algebraMap F _ k)) := by
    rw [hb, Algebra.smul_def, map_mul, map_mul, map_mul, map_mul]; ring
  rw [hsum]
  exact Subring.add_mem _ (hint b) (Subring.mul_mem _ (hint m) (Subring.mul_mem _ (hint d) hk))

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open Topology

theorem isCompact_annihilator : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
  intro F _ _ ψ hψ κ _ L hL
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_of_forall hψ
  have hW : ∀ i, (fun y : FiniteAdeleRing (𝓞 F) F => (Pi.single i y : κ → FiniteAdeleRing (𝓞 F) F)) ⁻¹' L ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i =>
    (hL.preimage (continuous_single i)).mem_nhds (by
      show Pi.single i (0 : FiniteAdeleRing (𝓞 F) F) ∈ L
      rw [Pi.single_zero]; exact L.zero_mem)
  choose d hd0 hd using fun i => GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds (hW i)
  set e : κ → F := fun i => algebraMap (𝓞 F) F (c * d i) with he_def
  have he : ∀ i, e i ≠ 0 := fun i => by
    simp only [he_def]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mul_ne_zero hc0 (hd0 i))
  let K : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun i =>
    (fun y => algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hK : IsCompact K := isCompact_univ_pi fun i =>
    (GroundTheory.Global.isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)
  refine hK.of_isClosed_subset ?_ ?_
  · have hset : {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} =
        ⋂ y ∈ L, {x | ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
      ext x; simp
    rw [hset]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    exact hψ.1.comp (continuous_const.prodMk
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const))
  · intro x hx i _
    have hz : ∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
        ψ (pairA F 0 ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i)) * x i) * t)) = 1 := by
      intro t ht
      have h1 := hx _ (hd i t ht)
      rw [dotProduct_single] at h1
      rwa [mul_comm (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i))) (x i), mul_assoc]
    have h2 := hc _ hz
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i, ?_, ?_⟩
    · simp only [he_def, map_mul]
      rw [mul_assoc]
      exact SetLike.mem_coe.mpr h2
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i) = x i
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (he i), map_one, one_mul]

end GlobalTheory.AnnCompactStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdelesStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_annihilator_openSubgroup_finiteAdeles : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
  first | exact @GlobalTheory.AnnCompactStd.isCompact_annihilator | exact GlobalTheory.AnnCompactStd.isCompact_annihilator | (intros; apply GlobalTheory.AnnCompactStd.isCompact_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tens_inj (v : Pl (F := F)) {κ : Type} (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRt : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (e : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hRt 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

section Grp
variable {n : ℕ} {W : Spc F E n}

end Grp

section Loc
variable {a a' : ℕ} {B : Base F E} (G : Geo σ a a') {X : Chars F E}


variable {G} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

end Loc

end GlobalTheory.InertAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt
open scoped ENNReal Classical

theorem eLpNorm_sq_le_add {α : Type} [MeasurableSpace α] {μ : Measure α} (hμ : μ Set.univ ≤ 1) {f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ a, f a ^ 2 ≤ g a ^ 2 + C) : eLpNorm' f 2 μ ^ 2 ≤ eLpNorm' g 2 μ ^ 2 + ENNReal.ofReal C := by
  have key : ∀ u : α → ℝ, eLpNorm' u 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (u a ^ 2) ∂μ := fun u => by
    have e := (lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := u) (μ := μ) (q := 2) (by norm_num)).symm
    simp only [ENNReal.rpow_ofNat] at e
    rw [e]
    refine lintegral_congr fun a => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [key, key]
  calc ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (g a ^ 2) + ENNReal.ofReal C ∂μ :=
        lintegral_mono fun a => by
          rw [← ENNReal.ofReal_add (sq_nonneg _) hC]
          exact ENNReal.ofReal_le_ofReal (h a)
    _ = ∫⁻ a, ENNReal.ofReal (g a ^ 2) ∂μ + ENNReal.ofReal C * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hμ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem denseRange_of_goodEmb {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) : DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · exfalso
    have h1 : H.rt0 ∈ σ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨_, hσ⟩
    rw [h] at h1
    obtain ⟨t, ht⟩ := h1
    have h2 := H.sqrt_neg_disc_sq
    rw [← ht] at h2
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h3 : t ^ 2 = -(H.d : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact h2
    nlinarith [sq_nonneg t]
  · rw [denseRange_iff_closure_range]
    exact congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h

section Model

variable {r : ℕ} {Cp : Type} [Fintype Cp] {X : Cp → FD.Data E r} {la : ∀ k, FD.Wt (X k).Ψ r}

theorem exists_ptN_le {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : FPt X, ptN la P ⟨p.1, p.2.1⟩ ≤ M :=
  ⟨(supE X la P).toReal, ENNReal.toReal_nonneg, fun p => (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top X la hP)).1
    (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)⟩


omit [Fintype Cp] in
theorem ptN_add_le (P Q : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (P + Q) z ≤ ptN la P z + ptN la Q z :=
  pnorm_add_le _ _ _ _ _


omit [Fintype Cp] in
theorem ptN_smul (a : ℂ) (P : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (a • P) z = ‖a‖ * ptN la P z :=
  pnorm_smul _ _ _ _ _

theorem exists_ptN_sub_le {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ∀ ε : ℝ, 0 < ε → ∃ f ∈ C, ∀ p : FPt X, ptN la (Q - rd f) ⟨p.1, p.2.1⟩ ≤ ε := by
  have h0 : ∀ z, ptN la (0 : FDSec X) z = 0 := fun z => pnorm_zero _ _ _
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact fun ε hε => ⟨f, hf, fun p => by rw [sub_self, h0]; exact hε.le⟩
  | zero => exact fun ε hε => ⟨0, zero_mem _, fun p => by rw [map_zero, sub_self, h0]; exact hε.le⟩
  | add P Q _ _ hP hQ =>
    intro ε hε
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2) (half_pos hε)
    obtain ⟨g, hg, h₂⟩ := hQ (ε / 2) (half_pos hε)
    refine ⟨f + g, add_mem hf hg, fun p => ?_⟩
    rw [map_add (f := _), show P + Q - (rd f + rd g) = (P - rd f) + (Q - rd g) by abel]
    exact (ptN_add_le _ _ _).trans (by linarith [h₁ p, h₂ p])
  | smul a P _ hP =>
    intro ε hε
    have ha : 0 < ‖a‖ + 1 := by positivity
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2 / (‖a‖ + 1)) (by positivity)
    obtain ⟨M, hM, h₂⟩ := exists_ptN_le (hC f hf)
    obtain ⟨b, hb⟩ := hσ.exists_dist_lt a (show 0 < ε / 2 / (M + 1) by positivity)
    rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hb
    refine ⟨b • f, C.smul_mem b hf, fun p => ?_⟩
    rw [map_smulₛₗ, show a • P - σ b • rd f = a • (P - rd f) + (a - σ b) • rd f by
      rw [smul_sub, sub_smul]; abel]
    refine (ptN_add_le _ _ _).trans ?_
    rw [ptN_smul, ptN_smul]
    have e₁ := (le_div_iff₀ ha).1 (h₁ p)
    have e₂ := mul_le_mul_of_nonneg_left (h₂ p) (norm_nonneg (a - σ b))
    nlinarith [ptN_nonneg la (P - rd f) ⟨p.1, p.2.1⟩, norm_nonneg (a - σ b)]

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (dict : Formalism.L2.Theta.GA D V → Σ k, FD.Frame (X k).Ψ r)
  (μ : Measure (AutQ V))

theorem ptN_sq_le_of_mem_span (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom)
    {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) (z : FPt X) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ f ∈ C, ptN la (rd f) ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la (rd f)).toReal ^ 2) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la Q).toReal ^ 2 := by
  have hQ' : Q ∈ holSub X la := (Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact hC f hf)) hQ
  obtain ⟨M, hM, h₂⟩ := exists_ptN_le hQ'
  have hfin := petE_ne_top V dict μ hμ hd hQ'
  set A := (petE V dict μ la Q).toReal with hA
  have step : ∀ ε : ℝ, 0 < ε →
      ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2) := fun ε hε => by
    obtain ⟨f, hf, h₁⟩ := exists_ptN_sub_le hσ rd C hC hQ ε hε
    have up : ∀ p : FPt X, ptN la (rd f) ⟨p.1, p.2.1⟩ ≤ ptN la Q ⟨p.1, p.2.1⟩ + ε := fun p => by
      have e := ptN_add_le (la := la) Q ((-1 : ℂ) • (Q - rd f)) ⟨p.1, p.2.1⟩
      rw [ptN_smul, show Q + (-1 : ℂ) • (Q - rd f) = rd f by rw [neg_one_smul]; abel, norm_neg, norm_one,
        one_mul] at e
      linarith [h₁ p]
    have dn : ptN la Q ⟨z.1, z.2.1⟩ ≤ ptN la (rd f) ⟨z.1, z.2.1⟩ + ε := by
      have e := ptN_add_le (la := la) (rd f) (Q - rd f) ⟨z.1, z.2.1⟩
      rw [add_sub_cancel] at e
      linarith [h₁ z]
    have hC0 : 0 ≤ 2 * M * ε + ε ^ 2 := by positivity
    have e₁ : petE V dict μ la (rd f) ^ 2 ≤ petE V dict μ la Q ^ 2 + ENNReal.ofReal (2 * M * ε + ε ^ 2) :=
      eLpNorm_sq_le_add hμ hC0 fun q => by
        have a₁ : ptN la (rd f) (dict q.out) ≤ ptN la Q (dict q.out) + ε := up ⟨_, _, hd q.out⟩
        have a₂ : ptN la Q (dict q.out) ≤ M := h₂ ⟨_, _, hd q.out⟩
        have a₃ := pow_le_pow_left₀ (ptN_nonneg _ _ _) a₁ 2
        nlinarith
    have e₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hfin, ENNReal.ofReal_ne_top⟩) e₁
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top hfin) ENNReal.ofReal_ne_top, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hC0] at e₂
    have e₃ := (h f hf).trans (mul_le_mul_of_nonneg_left e₂ hB)
    have e₄ := pow_le_pow_left₀ (ptN_nonneg _ _ _) dn 2
    have e₅ : ptN la (rd f) ⟨z.1, z.2.1⟩ ≤ M + ε := by linarith [up z, h₂ z]
    nlinarith
  have lim : Filter.Tendsto (fun ε : ℝ => B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (B * A ^ 2)) := by
    refine Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (by simp)) nhdsWithin_le_nhds
  exact ge_of_tendsto lim (eventually_nhdsWithin_of_forall step)

end Model

section Berg

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : Formalism.BasicNotions.D7}
  {V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D}
  {dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r} {Z : Comp Xo c}

theorem eq_zero_of_mem_span_cuspOn {G : WTZ E} {σ : c.F →+* ℂ} {Q : FDSec (U σ).X}
    (hQ : Q ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))))
    {z : Σ k, FD.Frame ((U σ).X k).Ψ r} (hz : z ∉ framesOn (U σ) Z) : Q z.1 z.2 = 0 := by
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact rdU_eq_zero _ hf.2 hz
  | zero => rfl
  | add P Q _ _ hP hQ => rw [Pi.add_apply, Pi.add_apply, hP, hQ, add_zero]
  | smul a P _ hP => rw [Pi.smul_apply, Pi.smul_apply, hP, smul_zero]

theorem bergOn_le_bergCusp {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z ≤ bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ := by
  by_cases h : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = ⊤
  · exact h ▸ le_top
  have hB := (bergCusp_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge
  rw [← ENNReal.ofReal_toReal h]
  set B := (bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩).toReal
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  set μ := muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z
  have hμ : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin := fun P (hP : P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G)) =>
    petE_ne_top (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd hP
  refine (bergE_le_iff _ _ μ hfin z ENNReal.ofReal_ne_top).2 fun P hP => ?_
  obtain ⟨Q, hQ, hPQ⟩ := hspan P hP
  have key := ptN_sq_le_of_mem_span (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd
    (denseRange_of_goodEmb (goodEmb_goodOf c σ)) (rdU (U (goodOf c σ))) (cuspOn U Z G)
    (fun f hf => (mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ)) z hB0 (fun f hf => by
      have e := hB f hf
      have hl := lieFacZ_pos (Dw := Dw) x G
      simp only [homN, petOn, petAt, mul_pow] at e
      exact le_of_mul_le_mul_left (e.trans_eq (by ring)) (pow_pos hl 2)) hQ
  have hle : ∀ w, ptN (modelWt (U (goodOf c σ)) G) Q w ≤ ptN (modelWt (U (goodOf c σ)) G) P w := fun w => by
    by_cases hw : w ∈ framesOn (U (goodOf c σ)) Z
    · simp only [ptN, FD.Data.pnorm, hPQ w hw, le_refl]
    · refine le_trans (le_of_eq ?_) (ptN_nonneg _ P w)
      simp only [ptN, FD.Data.pnorm, eq_zero_of_mem_span_cuspOn hQ hw, norm_zero, zero_mul]
  have hpet : petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) Q ≤
      petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) P :=
    eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
      exact hle _)
  have hz' : ptN (modelWt (U (goodOf c σ)) G) P ⟨z.1, z.2.1⟩ = ptN (modelWt (U (goodOf c σ)) G) Q ⟨z.1, z.2.1⟩ := by
    have := hPQ _ hz
    simp only [ptN, FD.Data.pnorm] at this ⊢
    rw [this]
  have e := key.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (hfin P hP) hpet) 2) hB0)
  rw [hz', ← ENNReal.ofReal_toReal (hfin P hP), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _),
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hB0]
  exact ENNReal.ofReal_le_ofReal e

theorem bergCusp_eq_bergOn {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z :=
  le_antisymm (bergCusp_le_bergOn hd z) (bergOn_le_bergCusp hd hspan z hz)

end Berg

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  first | exact @GlobalTheory.InertLagUniq.exists_test | exact GlobalTheory.InertLagUniq.exists_test | (intros; apply GlobalTheory.InertLagUniq.exists_test <;> assumption)
end
