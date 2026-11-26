module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FinrankOfExpBij
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsMore
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PelUnifPowerDvr

theorem main : Laws → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (j : ℕ), ∃ (t' : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P' : Geo.Tor.PELUnif (maximalIdeal V) t') (pG : IsPowGrp t'.G t.G j) (pD : IsPowDeg P'.D.toPre P.D.toPre j) (pA : IsPowPolAV P'.A P.A j), Nonempty (UnifPowOf3 pD pA pG P'.U P.U) ∧ (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧ ∀ (a : NumberField.RingOfIntegers E) (x : P'.D.toPre.X), pD.xe (a • x) = a • pD.xe x := by
  intro hL hT V _ _ _ E _ _ _ H t P j
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ P.A j
  exact GlobalTheory.exists_pelUnif_pow hL.globalFns V _ E H t P j
    (GlobalTheory.UnifPower.main hL (GlobalTheory.UnitBallFree.main hL.globalFns hT) V)
    (GlobalTheory.PowDegData.main hL.globalFns V _ P.D j) ⟨A', ⟨pA⟩⟩

end GlobalTheory.PelUnifPowerDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowData


set_option maxHeartbeats 1000000 in
theorem exists_powData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ
  obtain ⟨hL, hL2, -, hL4, -⟩ := firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  refine ⟨?_, fun n => ?_⟩
  · choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨t', P', pG, pD, pA, ⟨PU⟩, -⟩ := PelUnifPowerDvr.main hL hT T.V E H C.I.G P n
  obtain ⟨M, oD, hx, hact⟩ := powOAct_of_globalFns hL.globalFns E H T.V C.I.G P n P'.D pD
  refine ⟨P'.D, P'.A, t'.G, inferInstance, inferInstance, pD, pA, pG, P'.U, PU, M, oD, hx, hact, ?_⟩
  intro F _ _ _ _ _ _ v hv Q hQ α N hN hα
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ P'.D (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D P'.D pD Q hQ) F v hv
  letI := M
  have hw : TraceFormTwistIso P'.D.toPre oD H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre P'.D.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V P'.D F (𝓞 E) oD H.w0 hw α N 1 hN le_rfl hα
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_productData_copies_trivialisation_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  first | exact @GlobalTheory.PowData.exists_powData | exact GlobalTheory.PowData.exists_powData | (intros; apply GlobalTheory.PowData.exists_powData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
noncomputable section

namespace GlobalTheory.LevelCusp.Transport

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open GlobalTheory.Dict (castFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem integral_eq_zero_cast {α : Type} {Ψ Ψ' : Finset α} (h : Ψ = Ψ') {L : AddSubgroup (Ψ → ℝ)}
    {L' : AddSubgroup (Ψ' → ℝ)} [Countable L] [Countable L'] {D : Set (Ψ → ℝ)} {D' : Set (Ψ' → ℝ)}
    {g : (Ψ → ℝ) → ℂ} {g' : (Ψ' → ℝ) → ℂ} {c : ℂ}
    (hg : ∀ s, g s = c * g' (fun τ => s ⟨τ.1, h ▸ τ.2⟩))
    (hD : IsAddFundamentalDomain L D volume) (hD' : IsAddFundamentalDomain L' D' volume)
    (hf : volume D < ⊤) (hf' : volume D' < ⊤) (hp' : 0 < volume D') (hc : Continuous g)
    (hb : ∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) (hL : ∀ p ∈ L, ∀ s, g (p + s) = g s)
    (hL' : ∀ p ∈ L', ∀ s, g' (p + s) = g' s) (h0 : ∫ s in D', g' s = 0) : ∫ s in D, g s = 0 := by
  subst h
  have hg' : ∀ s, g s = c * g' s := hg
  have key := GlobalTheory.mean_fundamentalDomain_eq_of_periodic Ψ L L' D D' g hD hD' hf hf' hc hb (fun p hp s => by rw [add_comm, hL p hp])
    (fun p hp s => by rw [hg', hg', add_comm, hL' p hp])
  have e : ∫ s in D', g s = 0 := by
    simp only [hg']
    rw [integral_const_mul, h0, mul_zero]
  rw [e, mul_zero] at key
  refine (mul_eq_zero.1 key.symm).resolve_left ?_
  exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne'

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem nfac_eq (h : IsMatch X X' a) {la : Wt X.Ψ r} {la' : Wt X'.Ψ r}
    (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

theorem isIso_map (h : IsMatch X X' a) {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X'.IsIso ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
  refine ⟨(h.lat ξ).1 hξ.1, by rw [h.iso, hξ.2.1], fun e => hξ.2.2 ?_⟩
  rw [← GlobalTheory.Dict.Pull.inv_mulVec a ξ, e, Matrix.mulVec_zero]

theorem map_mul_flowMat (h : IsMatch X X' a) (ξ : Fin r → E) (τ : X'.Ψ) (s : ℂ) :
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ s =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ s * (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
  have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
    Matrix.mulVec_add, Matrix.mulVec_smul]

theorem lact_flow (h : IsMatch X X' a) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_mul_flowMat h]

theorem freq_zero (X : Data E r) (la : Wt X.Ψ r) :
    ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (0 : X.Ψ → ℝ) τ * p τ = k := fun p _ => ⟨0, by simp⟩

theorem fjI_zero (X : Data E r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (s : X.Ψ → ℝ) :
    fjI X ξ 0 P x s = P (X.flow ξ (cR X s) x) := by
  simp [fjI]
  rfl

theorem fj_zero_eq (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.fj la ξ 0 P x = ((volume (ExponentialGrowthExclusion.exists_fd X la).choose).toReal : ℂ)⁻¹ *
      ∫ s in (ExponentialGrowthExclusion.exists_fd X la).choose, fjI X ξ 0 P x s := by
  rw [Data.fj, if_pos (freq_zero X la), dite_eq_left (ExponentialGrowthExclusion.exists_fd X la)]
  rfl

end GlobalTheory.LevelCusp.Transport

end

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix


open GlobalTheory.LevelCusp.Transport ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity in
theorem GlobalTheory.LevelCusp.mem_SS_of_isMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  intro E _ _ _ r X X' a h la la' hl P Q c hP hQ hPQ
  obtain ⟨⟨hQs, C, hC⟩, hQ0⟩ := hQ
  have hb : ∀ x ∈ X.dom, X.pnorm la P x ≤ ‖c‖ * C := fun x hx => by
    have := hC _ (h.mem_dom hx)
    rw [BoundedSectionAlgebra.pnorm_eq, nfac_eq h hl] at this
    rw [BoundedSectionAlgebra.pnorm_eq, hPQ x hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  refine ⟨⟨hP, _, hb⟩, fun ξ hξ x hx => ?_⟩
  have hξ' := isIso_map h hξ
  have hx' := h.mem_dom hx
  have h0 := hQ0 _ hξ' _ hx'
  obtain ⟨-, hD, -, hf⟩ := (ExponentialGrowthExclusion.exists_fd X la).choose_spec
  obtain ⟨-, hD', hp', hf'⟩ := (ExponentialGrowthExclusion.exists_fd X' la').choose_spec
  rw [fj_zero_eq] at h0 ⊢
  have hne : ((MeasureTheory.volume (ExponentialGrowthExclusion.exists_fd X' la').choose).toReal : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne')
  have : Countable (X.periods la) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : Countable (X'.periods la') := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  rw [integral_eq_zero_cast h.psi (c := c) (fun s => ?_) hD hD' hf hf' hp'
    (fjI_continuous X la P hP hξ.2.1 0 hx) ⟨‖c‖ * C / X.nfac la x, fun s => ?_⟩
    (fjI_periodic X la P hP hξ.1 hξ.2.1 0 (freq_zero X la) hx)
    (fjI_periodic X' la' Q hQs hξ'.1 hξ'.2.1 0 (freq_zero X' la') hx')
    ((mul_eq_zero.1 h0).resolve_left hne), mul_zero]
  · rw [fjI_zero, fjI_zero, hPQ _ (flow_real_mem_dom X hξ.2.1 s x hx), lact_flow h]
    rfl
  · have hT := hb _ (flow_real_mem_dom X hξ.2.1 s x hx)
    rw [BoundedSectionAlgebra.pnorm_eq, BoundedSectionAlgebra.nfac_flow_real X hξ.2.1] at hT
    rw [fjI_zero, le_div_iff₀ (BoundedSectionAlgebra.nfac_pos X hx la)]
    exact hT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMoveStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cuspForms_of_multiple_rational_isometry_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  first | exact @GlobalTheory.LevelCusp.mem_SS_of_isMatch | exact GlobalTheory.LevelCusp.mem_SS_of_isMatch | (intros; apply GlobalTheory.LevelCusp.mem_SS_of_isMatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.LevelCusp

theorem apply_of_cols {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ))
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (cf : ∀ τ, Fin (m τ) → Fin (m τ) → ℂ)
    (hcol : ∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ j, cf τ i j • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) (z : Fin g → ℂ) (τ : α) (i : Fin (m τ)) :
    h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩) := by
  classical
  refine Pi.single_induction (p := fun z => h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩)) z (by simp)
    (fun z w hz hw => by simp only [map_add (f := _), Pi.add_apply, hz, hw, mul_add, Finset.sum_add_distrib]) fun n a => ?_
  · beta_reduce
    obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective n
    have h1 : (Pi.single (e.symm ⟨τ', i'⟩) a : Fin g → ℂ) = a • (Pi.single (e.symm ⟨τ', i'⟩) 1 : Fin g → ℂ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, hcol]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hτ : τ = τ'
    · subst hτ
      simp [mul_comm]
    · simp [hτ]


set_option maxHeartbeats 1000000 in
theorem exists_isometry_tri_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (i : Fin (Dw.mult τ)), A τ i i = Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hM hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p'
    (by rw [← hPx, ← hPx', ← hB.1]; exact hM.1.symm)
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P' p' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ i)
      (y'.u τ i)).1 (hPx' ▸ hcf3 τ i)
    have d0 := FibreDeriv.isDerivAt0_comp (hv τ i) ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    rw [hM.2.1] at d1
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  refine ⟨(φ k).symm ≪≫ₗ gam ≪≫ₗ φ k',
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun τ i j hji => ?_,
    fun τ i hi v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dite_eq_left ⟨hi, j.2⟩]
    rfl
  · beta_reduce
    rw [dite_eq_left ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.LevelCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMoveStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_triangular_periods_of_framePointMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (i : Fin (Dw.mult τ)), A τ i i = Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
  first | exact @GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove | exact GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove | (intros; apply GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.MoveValues

open GlobalTheory.MoveCalc

noncomputable abbrev cpt : Sp ℂ := IsLocalRing.closedPoint ℂ

noncomputable def ev : (Sp ℂ).presheaf.stalk cpt →+* ℂ := (stalkClosedPointIso (CommRingCat.of ℂ)).hom.hom

theorem mem_iff {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) : f cpt ∈ U ↔ ⊤ ≤ f ⁻¹ᵁ U :=
  ⟨fun h p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p cpt]
    exact h, fun h => h trivial⟩

theorem ev_gs {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)) :
    ev (gs f cpt U a) = valAt' f U a := by
  have h' := (mem_iff f U).1 h
  rw [gs_eq f cpt U h, valAt', dite_eq_left h', valAt, ← germ_stalkClosedPointIso_hom (CommRingCat.of ℂ)]
  exact congrArg ev (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') cpt trivial _).symm

theorem ev_gm {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)ˣ) :
    ev (gm f cpt U a).val = valAt' f U a.val :=
  (congrArg ev (gs_unit f cpt U h a).symm).trans (ev_gs f U h _)

section General

variable {X Y Y' : Scheme.{0}} {L : LB X} {F : X ⟶ X}

theorem mem_div {p : Sp ℂ ⟶ X} {i j : L.ι} :
    ⊤ ≤ p ⁻¹ᵁ (LB.div (L.pull F) L).U ((fun _ => i), j) ↔ F (p cpt) ∈ L.U i ∧ p cpt ∈ L.U j :=
  (mem_iff p _).symm.trans (and_congr_left' (mem_pull (F := F) (J := fun _ => i)))

theorem ev_gw (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    ev (gw w p cpt i j).val =
      valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val :=
  ev_gm p _ (show p cpt ∈ (L.pull F).U (fun _ => i) ⊓ L.U j from ⟨mem_pull.2 hi, hj⟩) _

theorem val_ne (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val ≠ 0 := by
  rw [← ev_gw w p hi hj]
  exact ((gw w p cpt i j).isUnit.map ev).ne_zero

theorem val_pgen {w : LB.Iso L (L.pull F)} (h : PGen w) (p : Sp ℂ ⟶ X) {i j i' j' : L.ι}
    (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) (hi' : F (p cpt) ∈ L.U i') (hj' : p cpt ∈ L.U j') :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
      valAt' (p ≫ F) (L.U i ⊓ L.U i') (L.g i i').val *
        valAt' p ((LB.div (L.pull F) L).U ((fun _ => i'), j')) (w.s ((fun _ => i'), j')).val := by
  have e : gw w p cpt i j * gm p cpt _ (L.g j j') = gm (p ≫ F) cpt _ (L.g i i') * gw w p cpt i' j' := by
    rw [h _ p cpt i i' j j' hi hi' hj hj', mul_right_comm, inv_mul_cancel_right]
  rw [← ev_gw w p hi hj, ← ev_gw w p hi' hj', ← ev_gm p (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    ← ev_gm (p ≫ F) (L.U i ⊓ L.U i') ⟨hi, hi'⟩, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, e]

theorem val_pmaps {w : LB.Iso L (L.pull F)} {e : Y ⟶ X} {t : LB.Gen (L.pull e)} {ρ : Y ⟶ Y} (he : e ≫ F = ρ ≫ e)
    (h : PMaps w (K := PUnit) (fun _ => e) (fun _ => e) (fun _ => 1) t t ρ) (x : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((x ≫ e) cpt) ∈ L.U i) (hj : (x ≫ e) cpt ∈ L.U j) :
    valAt' (x ≫ ρ) ((L.pull e).U (fun _ => i)) (t.s (fun _ => i)).val =
      valAt' (x ≫ e) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' x ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val := by
  have A := h _ x cpt (fun _ => i) (fun _ => j) (fun _ => hi) (fun _ => hj)
  rw [Fintype.prod_unique, zpow_one] at A
  have m : (x ≫ ρ) cpt ∈ (L.pull e).U (fun _ => i) := mem_pull.2 (by
    have h' : (e ≫ F) (x cpt) ∈ L.U i := hi
    rw [he] at h'
    exact h')
  rw [← ev_gw w (x ≫ e) hi hj, ← ev_gm (x ≫ ρ) _ m, ← ev_gm x ((L.pull e).U (fun _ => j)) (mem_pull.2 hj),
    ← map_mul, ← Units.val_mul]
  exact congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) A

theorem val_carry {w : LB.Iso L (L.pull F)} {q : Y ⟶ X} {q' : Y' ⟶ X} {pm : Y ⟶ Y'} (hpm : pm ≫ q' = q ≫ F)
    {a : Fam L q} {a' : Fam L q'} (h : Carry w pm a a') (pt : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((pt ≫ q) cpt) ∈ L.U i) (hj : (pt ≫ q) cpt ∈ L.U j) :
    valAt' (pt ≫ pm) _ (a' fun _ => i) =
      valAt' (pt ≫ q) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' pt _ (a fun _ => j) := by
  have m : (pt ≫ pm) cpt ∈ LB.wchart L (fun _ : Fin 1 => q') (fun _ => i) := mem_chart.2 (by
    have h' : (q ≫ F) (pt cpt) ∈ L.U i := hi
    rw [← hpm] at h'
    exact h')
  rw [← ev_gw w (pt ≫ q) hi hj, ← ev_gs (pt ≫ pm) _ m,
    ← ev_gs pt (LB.wchart L (fun _ : Fin 1 => q) (fun _ => j)) (mem_chart.2 hj), ← map_mul]
  exact congrArg ev (h _ pt cpt i j hi hj)

end General

theorem frMove_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c (CAt σ)), FrMove ρ ν y y' → ∃ (O : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → Xo.univ.t.G.left.Opens) (ω : ∀ i j, Γ(Xo.univ.t.G.left, O i j)), (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ p ⁻¹ᵁ Xo.univ.t.PP.L.U j)) ∧ (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0) ∧ (∀ i j i' j' (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' → valAt' p (O i j) (ω i j) * valAt' p (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val = valAt' (p ≫ ν.φ) (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * valAt' p (O i' j') (ω i' j')) ∧ (∀ i j (x : Sp ℂ ⟶ Xo.X) (p : Sp ℂ ⟶ Xo.univ.t.G.left), p = x ≫ eSec Xo.univ.t.G → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' (x ≫ ρ) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val = valAt' p (O i j) (ω i j) * valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧ ∀ i j (pt : Sp ℂ ⟶ Gx y.x) (pt' : Sp ℂ ⟶ Gx y'.x) (p : Sp ℂ ⟶ Xo.univ.t.G.left), pt ≫ Formalism.L2.PjFree.gxFst y.x = p → pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) → pt' ≫ Formalism.L2.PjFree.gxFst y'.x = p ≫ ν.φ → pt' ≫ Formalism.L2.PjFree.gxSnd y'.x = 𝟙 (Sp ℂ) → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' pt' ((PPx y'.x).U (fun _ => i)) (y'.s.f (fun _ => i)) = valAt' p (O i j) (ω i j) * valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo c σ ρ ν y y' h
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 h
  obtain ⟨g, r, -⟩ := (cubIso_iff ν w).1 hw
  refine ⟨fun i j => (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j),
    fun i j => (w.s ((fun _ => i), j)).val, fun i j p => ?_, fun i j p hp => ?_, fun i j i' j' p hp hp' => ?_,
    fun i j x p e hp => ?_, fun i j pt pt' p e₁ e₂ e₃ e₄ hp => ?_⟩
  · exact mem_div.trans (and_congr (mem_iff (p ≫ ν.cm.F) _) (mem_iff p _))
  · exact val_ne w p (mem_div.1 hp).1 (mem_div.1 hp).2
  · exact val_pgen g p (mem_div.1 hp).1 (mem_div.1 hp).2 (mem_div.1 hp').1 (mem_div.1 hp').2
  · subst e
    have A := val_pmaps ν.cm.e_comm r x (mem_div.1 hp).1 (mem_div.1 hp).2
    rw [ν.base] at A
    exact A
  · subst e₁
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact e₄.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · exact e₃.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm)
    exact val_carry hs hc pt (mem_div.1 hp).1 (mem_div.1 hp).2

end GlobalTheory.MoveValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSection
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSection
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

namespace TransPullEx

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem exists_isNormPull (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen)
    {T : Over S} (s : LB.Sec (LPow A L.L b T)) : ∃ s', IsNormPull A L φ a b s s' := by
  have hL := L.isLB
  have ha : eSec A ≫ φ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ha, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + - -b + (a + -b) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ β (LB.pullGen L.L _ _ (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (eSec A)))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (NormMulUniv.rigPow_isGen L.rigGen _)
        (NormMulUniv.rigPow_isGen L.rigGen _))) _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ φ).left]) (ε' := ![a, -b])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨s', hs', -⟩ := existsUnique_isTwistPull S A L.L hL T (endOver A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α hα s
  refine ⟨s', α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ, hs'⟩
  rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormMulUniv.eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end TransPullEx

theorem exists_isTransPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G), b ^ N = 1 → ∃ hh, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  intro E _ _ _ H Dw l Xo c F _ _ xF α N hN hα s b hb
  letI := H.starRing
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have := Xo.univ.t.act.hom α
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 α N hα (Xo.univ.t.adj α)
    Xo.univ.t.prim 1
  rw [Nat.one_mul] at h
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act α).left] ![(N : ℤ), -1] rfl
  obtain ⟨h₁, hh₁⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act α) (N : ℤ) 1 β hβ s
  obtain ⟨⟨U, hU⟩, -⟩ := symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) N hN
    (UnivPol.isUnit_natCast Xo _ hN.pos) (N : ℤ) rfl (ptO Xo xF) b hb
  obtain ⟨hh, hhh, -⟩ := existsUnique_isTwistPull Xo.X Xo.univ.t.G Xo.univ.t.PP.L hL (ptO Xo xF)
    (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _) (N : ℤ) (N : ℤ) U.φ U.isGen h₁
  exact ⟨hh, h₁, hh₁, hb, U, hU, hhh⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translated_normalisedPullback_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G), b ^ N = 1 → ∃ hh, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  first | exact @GlobalTheory.exists_isTransPull | exact GlobalTheory.exists_isTransPull | (intros; apply GlobalTheory.exists_isTransPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundAndFarBoundAndDecGap
namespace GlobalTheory.Deep

theorem ptBound_and_farBound_and_decGap :
    GlobalTheory.Deep.PtBound ∧ GlobalTheory.Deep.FarBound ∧ GlobalTheory.DSId.DecGap :=
  have hd : GlobalTheory.DSId.DecGap :=
    GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hp : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hd
  ⟨hp, GlobalTheory.FarTerms.farBound_of_ptBound hp, hd⟩

end GlobalTheory.Deep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayInputsOfDecAll
noncomputable section

namespace GlobalTheory.DecTransport

open Matrix Finset
open scoped InnerProductSpace
open Formalism.QuantumDeterminants (UH Hpk IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open GlobalTheory.Count (dOp rkR)
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp dimV DecGap DecKFin DecSmooth)

lemma hs_le_op {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (x i j) ≤ n * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := by
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ i, Complex.normSq (x i j) ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := by
    intro j
    have h1 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x).le_opNorm (EuclideanSpace.single j (1 : ℂ))
    rw [PiLp.norm_single, norm_one, mul_one] at h1
    refine le_trans (le_of_eq ?_) (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]
    congr 2
    have := GlobalTheory.Dec.stdRep_apply x (EuclideanSpace.single j (1 : ℂ)) i
    simp only [GlobalTheory.Dec.stdRep] at this
    rw [this]
    simp
  calc _ ≤ ∑ _j : Fin n, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

lemma op_conj {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (P * x * star P)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ := by
  have hu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P ∈ unitary _ := by
    rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem hP,
      Unitary.mul_star_self_of_mem hP, map_one]
    exact ⟨rfl, rfl⟩
  rw [map_mul, map_mul, map_star, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
    CStarRing.norm_mem_unitary_mul _ hu]

lemma rkR_eq {k r : ℕ} (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) : rkR ε = r + 1 := by
  have h1 := (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff k r ε).1 ⟨P, hP⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r + k + 1))))
    (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h2
  unfold rkR
  omega

lemma exp_le_rpow {a b c N G : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c) (hN : 0 ≤ Real.log N) (hG : 0 < G)
    (hGN : G ≤ c * N) : Real.exp (-b * Real.log N) ≤ c ^ a * G ^ (-a) := by
  have hN0 : 0 < N := by
    by_contra h
    nlinarith [mul_nonneg hc.le (neg_nonneg.2 (not_lt.1 h))]
  have hl := Real.log_le_log hG hGN
  rw [Real.log_mul hc.ne' hN0.ne'] at hl
  rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left hl ha, mul_le_mul_of_nonneg_right hab hN]

lemma gN_pos {k r : ℕ} {x : Mat k r} (hx : x ∈ UH (Hpk k r)) : 0 < gN x := by
  refine lt_of_le_of_ne (Real.sqrt_nonneg _) fun h => ?_
  have h0 : ∑ i, ∑ j, Complex.normSq (x i j) = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 h.symm
  have hx0 : x = 0 := by
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (x i j)).1 h0 i (mem_univ _)
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (x i j)).1 h1 j (mem_univ _))
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 : xᴴ * Hpk k r * x = Hpk k r := hx
  rw [hx0, Matrix.mul_zero] at h3
  rw [← h3, Matrix.mul_zero] at h2
  exact zero_ne_one h2

end GlobalTheory.DecTransport
end
end

namespace GlobalTheory.DecTransport


open Matrix Finset Formalism.FourierDecayAlt.ThreeDimData in
open scoped InnerProductSpace in
lemma decE_le {q : ℕ} (hq : 1 ≤ q) {h d : ℝ} (hh : 0 ≤ h) (hd : 0 ≤ d) :
    GlobalTheory.Count.decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q)) * d) := by
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hq)

  have key : d / Real.sqrt q - min (2 * d ^ 2) (d / Real.sqrt q) ≤ 1 := by
    rcases le_total (2 * d ^ 2) (d / Real.sqrt q) with hm | hm
    · rw [min_eq_left hm]
      have : d / Real.sqrt q ≤ d := div_le_self hd hs
      nlinarith [sq_nonneg (d - 1 / 4)]
    · rw [min_eq_right hm]; linarith
  have e : -(h / (8 * Real.sqrt q)) * d = -(h / 8) * (d / Real.sqrt q) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ h / 8)]

private lemma inv_mul_and_mul_inv_of_isCayleyU {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : PI.UpqRep.IsCayleyU k r ε P) :
    P⁻¹ * P = 1 ∧ P * P⁻¹ = 1 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  exact ⟨Matrix.nonsing_inv_mul P hd, Matrix.mul_nonsing_inv P hd⟩

private lemma conjTranspose_mem_Kset' {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : PI.UpqRep.IsCayleyU k r ε P) (hQ : PI.UpqRep.IsCayleyU k r ε Q) :
    P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  obtain ⟨⟨-, hPJ⟩, -⟩ := hP
  obtain ⟨⟨-, hQJ⟩, hQu⟩ := hQ
  have hQi : Q⁻¹ = Q.conjTranspose := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hQu)
  have hQQ : Q * Q.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hQu
  show (P * Q⁻¹).conjTranspose * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  rw [hQi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Q * P.conjTranspose * PI.UpqRep.Jm ε * (P * Q.conjTranspose)
        = Q * (P.conjTranspose * PI.UpqRep.Jm ε * P) * Q.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = Q * (Q.conjTranspose * PI.UpqRep.Jm ε * Q) * Q.conjTranspose := by rw [hPJ, hQJ]
    _ = (Q * Q.conjTranspose) * PI.UpqRep.Jm ε * (Q * Q.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = PI.UpqRep.Jm ε := by rw [hQQ, Matrix.one_mul, Matrix.mul_one]

private lemma rpow_three_div_two_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_one_add' hx (by norm_num), Real.sqrt_eq_rpow]


open Matrix Finset GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap Formalism.FourierDecayAlt.B in
open scoped InnerProductSpace in
theorem decLow_of_decGap (hA : GlobalTheory.DSId.DecGap) : Formalism.FourierDecayAlt.ThreeDimData.DecLow := by
  intro k r hk ε lam h H _ _ _ σ hl hσ hg h120 P hP w₁ w₂ h₁ h₂
  have hh : 0 ≤ h := by
    have : (0 : ℝ) ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    linarith
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hPi : P⁻¹ = star P := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hPu)
  have hPP := inv_mul_and_mul_inv_of_isCayleyU hP

  obtain ⟨P0, hP0, hDS0⟩ := hσ
  have hP0P := inv_mul_and_mul_inv_of_isCayleyU hP0
  have hDS : PI.UpqRep.IsDS ε lam (fun g => σ (P⁻¹ * g * P)) := by
    have h0 := GlobalTheory.CayleyChoice.isDS_conj hDS0 (conjTranspose_mem_Kset' hP hP0) (conjTranspose_mem_Kset' hP0 hP)
      (by
        calc P * P0⁻¹ * (P0 * P⁻¹) = P * (P0⁻¹ * P0) * P⁻¹ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hP0P.1, Matrix.mul_one, hPP.2])
    have hfun : (fun g => σ (P⁻¹ * g * P)) =
        (fun g => σ (P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0)) := by
      funext g
      congr 1
      calc P⁻¹ * g * P = (P0⁻¹ * P0) * (P⁻¹ * g * P) * (P0⁻¹ * P0) := by
            rw [hP0P.1, Matrix.one_mul, Matrix.mul_one]
        _ = P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0 := by simp only [Matrix.mul_assoc]
    rw [hfun]
    exact h0

  have hq : rkR ε = r + 1 := rkR_eq hk hP
  have hgap : 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hq]
    have h1 := GlobalTheory.GapSizeCheck.decay_range k r h h120
    have e : (((r + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) = ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) := by
      push_cast
      exact rpow_three_div_two_eq_mul_sqrt (by positivity)
    rw [e]
    exact h1

  have ha : 0 ≤ h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by positivity
  have hab : h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ h / (8 * Real.sqrt ((r : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left hh (by positivity)
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    gcongr
    linarith
  refine ⟨Real.exp (h / 8) * Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
    ‖w₁‖ * ‖w₂‖, fun x hx => ?_⟩

  have ex : P⁻¹ * (P * x * P⁻¹) * P = x := by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPP.1, Matrix.one_mul, Matrix.mul_one]
  have hgU : P * x * P⁻¹ ∈ PI.UpqRep.UJset ε :=
    (GlobalTheory.UnitaryCayley.transport hP (P * x * P⁻¹)).1.mp (by rw [ex]; exact hx)
  have hb : ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := by
    have h0 := (hA _ ε lam H (fun g => σ (P⁻¹ * g * P)) hl hDS h hg hgap (P * x * P⁻¹) hgU w₁ h₁ w₂ h₂).2
    rw [hq] at h0
    simpa only [ex] using h0
  have hd : 0 ≤ dOp (P * x * P⁻¹) := ((GlobalTheory.Dec.dFacts_holds _ ε).1 _ hgU).1
  have hdecE : decE (r + 1) h (dOp (P * x * P⁻¹)) ≤
      Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) := by
    have h0 := decE_le (q := r + 1) (by omega) hh hd
    push_cast at h0
    exact h0

  have hcl : Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) (P * x * P⁻¹) =
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹)) := by
    first
      | rfl
      | (apply ContinuousLinearMap.coe_injective; simp [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin])
  have hGN : gN x ≤ Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) *
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
    have h1 := hs_le_op x
    have h2 : ‖Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) x‖ =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
      rw [← hcl, ← op_conj hPu x, hPi]
    rw [h2] at h1
    show Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j)) ≤ _
    calc Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j))
        ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hE : Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) ≤
      Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
        gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
    exp_le_rpow ha hab (by positivity) hd (gN_pos hx) hGN
  calc ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := hb
    _ ≤ (Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹))) *
          ‖w₁‖ * ‖w₂‖ := by gcongr
    _ ≤ (Real.exp (h / 8) * (Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
          gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))))) * ‖w₁‖ * ‖w₂‖ := by gcongr
    _ = _ := by ring

theorem decLow_holds : Formalism.FourierDecayAlt.ThreeDimData.DecLow :=
  decLow_of_decGap GlobalTheory.Deep.ptBound_and_farBound_and_decGap.2.2

end GlobalTheory.DecTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaLift

theorem exists_theta_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L ((0 : ℕ) : ℤ) T, θ.pt = x := by
  refine ⟨⟨x, ⟨fun _ => 1⟩, ?_⟩, rfl⟩
  refine isGen_of_gm (M := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A x).left])
    (ε := ![((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ)]) _ fun w j j' h h' => ?_
  refine (map_one _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_one _)).symm)
  simp [trF, Fin.prod_univ_two]

theorem exists_theta_of_field : ∀ (K : Type) [Field K] (A : PolAV (Sp K)) (Y : Over (Sp K)) (F : Type) [Field F] (e : Y.left ≅ Sp F) (k : ℕ) (x : Y ⟶ A.A), x ^ k = 1 → ∃ θ : ThetaGrp A.A A.L (k : ℤ) Y, θ.pt = x := by
  intro K _ A Y F _ e k x hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact exists_theta_zero A.L x
  · have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    have : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
    have : Subsingleton Y.left := e.hom.homeomorph.toEquiv.subsingleton
    have : Nonempty Y.left := e.hom.homeomorph.toEquiv.nonempty
    exact GlobalTheory.BoxTheta.exists_theta GlobalTheory.firstFiveLaws.1.kerPow A hk x hx

end GlobalTheory.ThetaLift
end
