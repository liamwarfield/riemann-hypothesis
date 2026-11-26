module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MoyalOrthogonalityHeisenbergThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColPtInvMemStdLatIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertDbl.inlD_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  intro F E _ _ _ _ _ σ d W v k hk
  refine ⟨?_, fun z hz => ?_⟩
  · intro u hu
    rw [GlobalTheory.InertDbl.matD_inlD]
    have h1 := hk.1 u hu
    have h1' : u • (mat k - 1) = 0 := h1
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have := congrFun (congrFun h1' i) j
      simpa [Matrix.fromBlocks, Matrix.one_apply] using this
    all_goals simp [Matrix.fromBlocks, Matrix.one_apply]
  · have hinv : GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ W k)⁻¹ = Matrix.fromBlocks (mat k⁻¹) 0 0 1 := by
      rw [← map_inv]; rfl
    rw [hinv, GlobalTheory.InertDbl.matD_inlD]
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨a1, a2⟩ := hk.2 _ hz1
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [Matrix.fromBlocks_mulVec]; convert a1 using 1; funext i; simp [Function.comp_def]
    · simpa [Matrix.fromBlocks_mulVec] using hz2
    · simp only [Matrix.fromBlocks_mulVec]; convert a2 using 1; funext i; simp [Function.comp_def]
    · simpa [Matrix.fromBlocks_mulVec] using hz2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  first | exact @GlobalTheory.InertDbl.inlD_mem_KAtD | exact GlobalTheory.InertDbl.inlD_mem_KAtD | (intros; apply GlobalTheory.InertDbl.inlD_mem_KAtD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonneg
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.TowVal

theorem bddAll_one_iff_valSet_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (f : Rul Xo c), GlobalTheory.GoodPts.BddAll Xo c la 1 f ↔ ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c la f
  constructor
  · rintro h _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    have h1 := h T io e ho y hy
    rw [map_one, one_mul] at h1
    exact (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 _).1 h1
  · intro h T io e ho y hy
    rw [map_one, one_mul, GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1]
    exact h _ ⟨PtV.mk la ho y hy () trivial, rfl⟩

end GlobalTheory.TowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonnegStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (f : Rul Xo c), GlobalTheory.GoodPts.BddAll Xo c la 1 f ↔ ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f := by
  first | exact @GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg | exact GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg | (intros; apply GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

def conjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp ω

theorem conjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    conjRep ω p F = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (ω p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F)) := rfl

def adjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep T S :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint (conjRep ω)

theorem adjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (h : GA D T) (g : GA D S) (F : WO T S → ℂ) :
    adjRep ω (h, g) F = fun y => ω (g, h) (fun x => F (adjO T S x)) (adjO S T y) := by
  funext y
  show starRingEnd ℂ (starRingEnd ℂ (ω (g, h) (fun x => starRingEnd ℂ (starRingEnd ℂ (F (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x))))
    (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S y))) = _
  simp only [Complex.conj_conj, GlobalTheory.ConjAdjWeil.dagger_eq]


open GlobalTheory.FockAdjoint in
def swapHom {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank →ₐ[ℂ] PolF D S.rank T.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)


open GlobalTheory.FockAdjoint in
def swapInv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D S.rank T.rank →ₐ[ℂ] PolF D T.rank S.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1)

open GlobalTheory.FockAdjoint in
theorem swapHom_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D T.rank S.rank) :
    swapHom A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapHom]

open GlobalTheory.FockAdjoint in
theorem swapInv_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D S.rank T.rank) :
    swapInv A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapInv]


open GlobalTheory.FockAdjoint in
def swapEquiv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank ≃ₐ[ℂ] PolF D S.rank T.rank :=
  AlgEquiv.ofAlgHom (swapHom A B) (swapInv A B)
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapInv_X, map_mul, swapHom_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapHom_X, map_mul, swapInv_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])

end GlobalTheory.AdjTr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_down {D : D7} {X : ProvA} (h : GlobalTheory.ArchRec.Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) (τ : D.what₂.Tau) (V W : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ForAllAt τ V W aS aT S S' fun MS MT A B pt =>
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.LiftLaw MT τ B pt MS A ∧ ∀ ip, GlobalTheory.ArchRec.IsIp V W ip → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaLaw MT τ B pt MS A ip := by
  obtain ⟨al, be, ga, de, hd, -, rfl, rfl⟩ := hp
  intro ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf
  obtain ⟨hm, e, u, hk⟩ := GlobalTheory.ArchRec.tie_small h hd.1 MS τ true false p1
  obtain ⟨e', u', hk'⟩ := GlobalTheory.ArchRec.tie_large h hd.1 MT τ false true p2
  obtain ⟨κ, hR⟩ := GlobalTheory.ArchRec.exists_real hω hS hT (GlobalTheory.ArchRec.isFrameOf_model MS τ) (GlobalTheory.ArchRec.isFrameOf_model MT τ) hf
    hk.ord.1 hk'.ord.1
  exact GlobalTheory.ArchRec.lift_down h h1 h3 hd hm hk hk' hR

theorem pairPar_of_upPair {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) :
    GlobalTheory.PairLift.PairPar S S' aS aT ∧ GlobalTheory.PairLift.PairPar S' S aT aS := by
  obtain ⟨al, be, ga, de, hd, hfar, rfl, rfl⟩ := hp
  have hT : GlobalTheory.PairLift.ThetaPar t (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) (GlobalTheory.Chain.signed (al ++ block t ++ de) (ga ++ be) aS) aT aS :=
    ⟨al, be, ga, de, rfl, Or.inl ⟨hd, rfl⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + aT := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨⟨t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩, ⟨t, _, _, rfl, rfl, Or.inr hT⟩⟩

theorem upPair_arch : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ),
    UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X →
      Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  intro hDS hHC D t S S' aS aT hp
  refine ⟨fun τ V W => ?_, fun X h3 h4 h5 => ?_⟩
  · obtain ⟨X, hX, h1, -, h3, -, -⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
    have h : GlobalTheory.ArchRec.Good D X :=
      ⟨hX, GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX, hHC.admQ5_of_harishChandraModules X, GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D⟩
    have down := upPair_down h h1 h3 hp τ V W
    exact ⟨fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).1,
      fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf μ 𝓕 m1 m2 =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).2 _ ⟨μ, 𝓕, m1, m2, rfl⟩⟩
  · obtain ⟨q1, q2⟩ := pairPar_of_upPair hp
    exact ⟨GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q1, GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q2⟩

end GlobalTheory.EvenOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirectionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ), UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  first | exact @GlobalTheory.EvenOnto.upPair_arch | exact GlobalTheory.EvenOnto.upPair_arch | (intros; apply GlobalTheory.EvenOnto.upPair_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibility
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibility
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Irr

variable {D : D7}

theorem thPair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem irr : ∀ D : D7, Irr D := by
  intro D ψ hψ S T Γ ℓ hℓ f₀ hf₀ hne hann f hf
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI := v.covol.1
  haveI : SFinite v.μ := inferInstance
  obtain ⟨hint, hmoy⟩ := GlobalTheory.T.moyal_orthogonality_heisenberg_thetaFunctions D ψ hψ S T v f f₀ hf.1 hf₀.1
  have heq : (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) =
      thPair v.μ v.𝓕 f₀ f₀ • f := funext fun x => by rw [hmoy x]; rfl
  have hth : IsThetaFunO ψ S T (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) := by
    rw [heq]; exact GlobalTheory.OrientedHeis.theta_smul _ hf.1
  have hsup := hℓ.sup f₀ hf₀.1 v.μ _ hint hth
  rw [heq, hℓ.smul _ _ hf.1] at hsup
  have hz : ∀ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * ℓ (heisO ψ S T w f₀) = 0 := fun w => by
    by_cases hw : w ∈ Ann ψ S T Γ
    · rw [hann w hw, mul_zero]
    · rw [(GlobalTheory.T.heisenbergVacuumCommutant_preserves_latticeVacua D ψ hψ S T Γ).2.2 v f f₀ hf hf₀ w hw, zero_mul]
  simp_rw [hz, integral_zero] at hsup
  exact (mul_eq_zero.1 hsup).resolve_left (thPair_self_ne_zero hψ v hf₀.1 hne)

end GlobalTheory.Irr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibilityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_functional_vacuum_irreducibility : ∀ D : D7, Irr D := by
  first | exact @GlobalTheory.Irr.irr | exact GlobalTheory.Irr.irr | (intros; apply GlobalTheory.Irr.irr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.FormTopAut

variable {D : D7}

theorem aut_cast {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : IsAutFun D.sp.X' φ) :
    IsAutFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact hφ

theorem formTop_cont_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t y, Continuous (formTop ch t y) ∧
    ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g := by
  refine ⟨0, ?_⟩
  intro ε CF _
  refine ⟨0, ?_⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ t y
  have hm := hS.core.models
  obtain ⟨h1, -, -⟩ := GlobalTheory.EndCusp.formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have k := aut_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (ch.cv.formX t y) h1.toIsAutFun
  exact ⟨k.cont, k.left⟩

end GlobalTheory.FormTopAut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTopVertexFormFunction_continuous_left_invariant : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t y, Continuous (formTop ch t y) ∧
    ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g := by
  first | exact @GlobalTheory.FormTopAut.formTop_cont_left | exact GlobalTheory.FormTopAut.formTop_cont_left | (intros; apply GlobalTheory.FormTopAut.formTop_cont_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirection
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree


open scoped Classical in
theorem GlobalTheory.HeisLineDeriv.exists_actsD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      ∃ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ :=
  fun M ψ hψ g u hu => by
    obtain ⟨D, hD⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
    exact ⟨D g, hD g⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      ∃ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ := by
  first | exact @GlobalTheory.HeisLineDeriv.exists_actsD | exact GlobalTheory.HeisLineDeriv.exists_actsD | (intros; apply GlobalTheory.HeisLineDeriv.exists_actsD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def formGen (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) : Fn ch.G (.grid 0 D.R.m) := fun g =>
  η (R.cX.ext ((R.HX t).e y) (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) g))

def genPer (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H) (Q : PolCol ch.G × PolRow ch.G)
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) : ℂ :=
  defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)

end Gen

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Gen2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def GenConv (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H) (Q : PolCol ch.G × PolRow ch.G)
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) : Prop :=
  PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) ∧
    PathConv ch.W M (rowPath _ D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) (formGen ch t y η) ∧
    IntegrableOn (fun h => liftP ch.W M (colPath t D.R.m)
        (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j))
          (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (stabilizerEmbedding ch.G.sp.topDec h) *
        liftP ch.W M (rowPath _ D.R.m D.R.m)
          (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) (formGen ch t y η) h)
      (M.fd (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m))

end Gen2

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPt0InvMemStdLatIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove GlobalTheory.FirstRowVertex
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstRowLat

variable {D : D7}

theorem givenLevel_zero_le_KO {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) (hg : g ∈ givenLevel G t w (0, k)) :
    g ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin ((locGrid G t w).rank (0, k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  change g ∈ (stepGroup L t w (j + 1)).map (GlobalTheory.StepData.reGL (ixFin G t w (j + 1))).toMonoidHom at hg
  by_cases hP : w ∈ L.Pg
  · exact ((GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description G t w hP (j + 1) g).1 hg).1
  · exact ((GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G t w hP (j + 1) g).1 hg).1

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem levRow_zero_stab (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    Lev.finE (G.V (.grid 0 D.R.m)) k.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid 0 D.R.m))) := by
  have hβ : IsFrame (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) := S.B.isFrame_β hL (Nat.zero_le _) le_rfl
  have hsd : IsSelfDualC (G.V (.grid 0 D.R.m)) (G.Λ (.grid 0 D.R.m)) := by
    have key : ∀ X : LSp D, X = ⟨D.sp.X', L.ΛX⟩ → IsSelfDualC X.sp X.lat := by
      rintro X rfl
      exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX
    exact key _ (colY_m L)
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA hβ hsd (locPl G t)
    (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) (fun _ => rfl)
  have hle : S.levRow t 0 (Nat.zero_le _) ≤ prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) := by
    refine inf_le_inf_right _ (iInf_mono fun w => Subgroup.comap_mono ?_)
    intro g hg
    exact givenLevel_zero_le_KO G t w.1 D.R.m hm g hg
  have hmem : finG (G.V (.grid 0 D.R.m)) k ∈ prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) ⊓
        UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    Subgroup.mem_inf.2 ⟨hle hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [e, congLev_top] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

end GlobalTheory.FirstRowLat

theorem GlobalTheory.FirstRowLat.rowPt0_inv_mem_stdLat_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ k : FinPt G (.grid 0 D.R.m), finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) →
    ∀ x : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)),
      actO _ _ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) ↔ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) := by
  intro D T L sc G W U S μ₀ hL t _ k hk x
  have h1 := GlobalTheory.FirstRowLat.levRow_zero_stab S hL t k hk
  have h2 := GlobalTheory.LastColLat.conj_stab S.N (X := .grid 0 D.R.m) (by simp [DefNode]) k h1
  have e : G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1 =
      (1, ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1) := by
    show (negGA _ 1, _) = _
    rw [map_one]
    rfl
  rw [e]
  exact GlobalTheory.LastColLat.actO_inv_mem_latO_iff _ _ _ _ _ h2 x

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelKFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KFinStruct

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.KFinVec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kFin_eq : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ = kFinSub ε σ :=
  le_antisymm (sSup_le fun W hW _ hw => ⟨W, hW.1, hw, hW.2⟩)
    fun _ ⟨W, h1, h2, h3⟩ => (le_sSup (a := W) ⟨h1, h3⟩ : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) h2

theorem conj_lie' {A B G G' Y : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (hG : Aᴴ * G * A = G')
    (hY : Yᴴ * G + G * Y = 0) : (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0 := by
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY]; simp

theorem exp_smul_conj' {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Q * NormedSpace.exp (t • X) * Q⁻¹ = NormedSpace.exp (t • (Q * X * Q⁻¹)) := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

theorem model (h : GlobalTheory.Published.KFiniteVectorsUnitary) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = G) :
    (∃ p : kFinSub ε σ, p ≠ 0) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ v : kFinSub ε σ, ∃ w : kFinSub ε σ,
      HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0) ∧
    ∀ B : Submodule ℂ (kFinSub ε σ), B ≠ ⊥ →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ v w : kFinSub ε σ, v ∈ B →
        HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0 → w ∈ B) → B = ⊤ := by
  haveI := hσ.1
  haveI := hσ.2.1
  obtain ⟨-, -, hd, hst, hirr⟩ := h.of_isDS hσ
  have hdet := (isUnit_iff_isUnit_det _).1 hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hG' : (P⁻¹)ᴴ * G * P⁻¹ = Jm ε := by
    rw [← hJ]
    calc _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp
  refine ⟨?_, fun X hX v => ?_, fun B hB hS => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    obtain ⟨y, hy, hy'⟩ := hd.exists_mem_open isOpen_compl_singleton ⟨x, hx⟩
    exact hy' (congrArg Subtype.val (hne ⟨y, hy⟩))
  · have hY : inG ε (P * X * P⁻¹) := conj_lie' h1 hG' hX
    refine ⟨⟨dRep σ (P * X * P⁻¹) v, hst _ hY _ v.2⟩, ?_⟩
    simp only [exp_smul_conj' hP]
    exact h.hasDerivAt hσ.2.2.1 hσ.2.2.2.1 v.2 hY
  · have hle : B.map (kFinSub ε σ).subtype ≤ kFinSub ε σ := Submodule.map_subtype_le _ _
    have hs : IsLieStable ε σ (B.map (kFinSub ε σ).subtype) := by
      rintro Y hY _ ⟨v, hv, rfl⟩
      refine ⟨⟨dRep σ Y v, hst _ hY _ v.2⟩, hS (P⁻¹ * Y * P) (conj_lie' h2 hJ hY) v _ hv ?_, rfl⟩
      have e : P * (P⁻¹ * Y * P) * P⁻¹ = Y := by
        calc _ = (P * P⁻¹) * Y * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [h2]; simp
      simp only [exp_smul_conj' hP, e]
      exact h.hasDerivAt hσ.2.2.1 hσ.2.2.2.1 v.2 hY
    rcases hirr _ hle hs with e | e
    · exact absurd ((Submodule.map_injective_of_injective (kFinSub ε σ).injective_subtype)
        (e.trans (Submodule.map_bot _).symm)) hB
    · exact (Submodule.map_injective_of_injective (kFinSub ε σ).injective_subtype)
        (e.trans (Submodule.map_subtype_top _).symm)

end Model

end GlobalTheory.KFinStruct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {D : D7}

theorem hasTypeAll_const_mul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {Lie Gs : Set (Mx n)} {f : Mx n → ℂ} (c : ℂ) (h : HasTypeAll Lie Gs σ f) :
    HasTypeAll Lie Gs σ fun g => c * f g := by
  obtain ⟨v, h1, ℓ, hℓ, ⟨S, C, hS, h2, h3, B, hB, hc⟩, h4⟩ := hasTypeAll_iff.1 h
  refine hasTypeAll_iff.2 ⟨v, h1, fun i => c • ℓ i, fun i => GlobalTheory.MultMem.sobCont_smul c (hℓ i),
    ⟨S, fun i => ‖c‖ * C i, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, hc⟩, fun g hg => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i w hw) (norm_nonneg c)
  · simpa only [mul_assoc] using (h3 S' hS').mul_left ‖c‖
  · simpa only [LinearMap.smul_apply, smul_eq_mul] using (h4 g hg).mul_left c

def TypedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹))
    fun g => φ (x * atTau θ V τ g)

theorem isTypeAt_of_typedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {φ : GA D V → ℂ} (h : TypedBy θ M τ φ) : IsTypeAt θ V τ (S τ) φ :=
  ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ, fun x => hasTypeAll_iff.1 (h x)⟩

theorem typedBy_value (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar}
    (M : DSModel V Sp) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (τ : D.what₂.Tau) : TypedBy θ M τ (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  intro x
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  refine GlobalTheory.CuspValueType.hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
  have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
  have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
  show ℓ (M.rep τ g (v τ)) = _
  rw [h2, h1]
  rfl

theorem star_lift_isTypeAt (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) (z : SmT M)
    (τ : D.what₂.Tau) : IsTypeAt θ V τ (dualPar (S τ)) fun g => star (PiTensorProduct.lift T z g) := by
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨hsm, hmult⟩ := GlobalTheory.ConjMult.conj_mult θ M M' c hc
  obtain ⟨T', hT'm, hT'⟩ := hmult J χ T hT
  have hT'' := (GlobalTheory.MultMem.mem_mult_iff D θ V _ M' J _ T').1 hT'm
  refine isTypeAt_of_typedBy θ M' τ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    let f' : M'.Vec := fun ρ => ⟨(c ρ).symm (f ρ), (hsm ρ _).2 (by simp)⟩
    have e : (fun g => star (PiTensorProduct.lift T (r • PiTensorProduct.tprod ℂ f) g)) = fun g => star r * T' f' g := by
      funext g
      rw [hT' f' f (fun ρ => by simp [f']) g, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, star_mul']
    rw [e]
    intro x
    exact hasTypeAll_const_mul (star r) (typedBy_value θ hHC M' hT'' f' τ x)
  | add a b ha hb =>
    intro x
    have e : (fun g => star (PiTensorProduct.lift T (a + b) (x * atTau θ V τ g))) =
        fun g => star (PiTensorProduct.lift T a (x * atTau θ V τ g)) + star (PiTensorProduct.lift T b (x * atTau θ V τ g)) := by
      funext g
      rw [map_add (f := _), Pi.add_apply, star_add]
    rw [e]
    exact (ha x).add (hb x)

end GlobalTheory.StartCusp

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult

variable {D : D7}

theorem isCuspFun_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) : IsCuspFun V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact GlobalTheory.MultMem.isCuspFun_add (GlobalTheory.EndCusp.isAutFunSm_lift hT a).toIsAutFun
      (GlobalTheory.EndCusp.isAutFunSm_lift hT b).toIsAutFun ha hb


end GlobalTheory.StartCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInterchange

open Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

def Good (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  Φ ∈ schA F (Fin n × Fin d) ∧ ∃ Φ' ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t => T t Φ x) (Φ' x) 0) ∧
    ∀ w, HasDerivAt (fun t => thetaSum F (M.co.rho ψ w (T t Φ))) (thetaSum F (M.co.rho ψ w Φ')) 0

theorem rho_add (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E))
    (a b : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (a + b) = M.co.rho ψ w a + M.co.rho ψ w b := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (c • a) = c • M.co.rho ψ w a := by
  funext x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.rho ψ w (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem theta_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : Matrix (Fin n) (Fin d) (AE F E))
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : a ∈ schA F (Fin n × Fin d)) (hb : b ∈ schA F (Fin n × Fin d)) :
    thetaSum F (M.co.rho ψ w (a + b)) = thetaSum F (M.co.rho ψ w a) + thetaSum F (M.co.rho ψ w b) := by
  rw [rho_add]
  unfold GlobalTheory.WeilM.thetaSum
  exact (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ ha)).tsum_add
    (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ hb))

theorem theta_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : thetaSum F (M.co.rho ψ w (c • a)) = c * thetaSum F (M.co.rho ψ w a) := by
  rw [rho_smul]
  unfold GlobalTheory.WeilM.thetaSum
  simp only [Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem good_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) :
    Good M ψ T 0 := by
  refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun x => ?_, fun w => ?_⟩
  · simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · simp only [map_zero, rho_zero, GlobalTheory.WeilM.thetaSum, Pi.zero_apply, tsum_zero]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem good_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)} (hT : ∀ t, ∀ Φ ∈ schA F (Fin n × Fin d), T t Φ ∈ schA F _)
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) (hb : Good M ψ T b) : Good M ψ T (a + b) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  obtain ⟨hb, b', hb', hpb, htb⟩ := hb
  refine ⟨Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', fun x => ?_, fun w => ?_⟩
  · simp only [map_add (f := _), Pi.add_apply]
    exact (hpa x).add (hpb x)
  · have e : (fun t => thetaSum F (M.co.rho ψ w (T t (a + b)))) =
        fun t => thetaSum F (M.co.rho ψ w (T t a)) + thetaSum F (M.co.rho ψ w (T t b)) := by
      funext t
      rw [map_add (f := _), theta_add M hψ w (hT t a ha) (hT t b hb)]
    rw [e, theta_add M hψ w ha' hb']
    exact (hta w).add (htb w)

theorem good_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (c : ℂ)
    {a : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) : Good M ψ T (c • a) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  refine ⟨Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', fun x => ?_, fun w => ?_⟩
  · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (hpa x).const_mul c
  · simp only [map_smul, theta_smul]
    exact (hta w).const_mul c

theorem schA_le_of_pure {κ : Type} [Fintype κ] {N : Submodule ℂ ((κ → AF F) → ℂ)}
    (h : ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → pure f φ ∈ N) :
    schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.SBSpan.mem_span_restrictedProd F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ hφ hs

end GlobalTheory.ThetaInterchange
end
end
