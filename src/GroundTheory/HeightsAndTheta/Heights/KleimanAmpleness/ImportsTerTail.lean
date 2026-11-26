module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSplit
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveNumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
        relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        NumbersDVR.intNum F W ![β] =
          Kleiman.interNum (W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k))) ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (L L' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β β' : K → ℤ),
      BundleRealises y k₀ L β → BundleRealises y k₀ L' β' → BundleRealises y k₀ (L.tensor L') (β + β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

theorem ModelGenerated.proof : ModelGenerated.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy β
  obtain ⟨i₀, -⟩ := hy.1 k₀
  have hcard : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hcard).symm⟩
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hy β
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full.{0, 0} F Ω N x Q
  refine ⟨c₀, fun c hc => ?_⟩
  set δ := β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  set L := Q.tensor (Kleiman.twistBundle F x c) with hL
  have hLsys : L.toSubSystem = Q.toSubSystem.twist (Kleiman.twistSys F x c) := rfl
  have hgen : L.toSubSystem.Generated := by rw [hLsys]; exact hc₀ c hc
  have hsecs : L.toSubSystem.secs = secOver F y δ := by rw [hLsys, hQ c]

  have hgam : ∀ m : ℤ, L.toSubSystem.gam m = secOver F y (δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro m
    rw [Kleiman.SubSystem.gam, hLsys, Kleiman.SubSystem.twist_assoc, Kleiman.twistSys_twist_twistSys, hQ (c + m),
      hδ, add_smul, add_assoc]

  have hsub : ∀ I : Kleiman.Chart x, (L.sub I : Set Ω) = chartSecOver F y k₀ e δ I := by
    intro I
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [hgam]

  have hfg : ∀ I : Kleiman.Chart x, ∃ G : Finset Ω, Submodule.span (Kleiman.chartRing F x I) (G : Set Ω) = L.sub I :=
    fun I => L.fg I
  choose G hG using hfg
  have hfin : ∀ (I : Kleiman.Chart x) (g : Ω), ∃ T : Finset Ω, (T : Set Ω) ⊆ L.toSubSystem.secs ∧
      (g ∈ L.sub I → g ∈ Submodule.span (Kleiman.chartRing F x I) (T : Set Ω)) := by
    intro I g
    by_cases hg : g ∈ L.sub I
    · rw [← hgen I] at hg
      obtain ⟨T, hT, hgT⟩ := Submodule.mem_span_finite_of_mem_span hg
      exact ⟨T, hT, fun _ => hgT⟩
    · exact ⟨∅, by simp, fun h => absurd h hg⟩
  choose T hTsec hTspan using hfin
  let U : Finset Ω := Finset.univ.biUnion fun I => (G I).biUnion fun g => T I g
  have hU : (U : Set Ω) ⊆ L.toSubSystem.secs := by
    intro s hs
    simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Finset.mem_coe] at hs
    obtain ⟨I, g, -, hs⟩ := hs
    exact hTsec I g hs
  have hspanU : ∀ I : Kleiman.Chart x, Submodule.span (Kleiman.chartRing F x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hU
    · rw [← hG I, Submodule.span_le]
      intro g hg
      have hgI : g ∈ L.sub I := by rw [← hG I]; exact Submodule.subset_span hg
      refine Submodule.span_mono ?_ (hTspan I g hgI)
      intro s hs
      simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
        Finset.mem_coe]
      exact ⟨I, g, hg, hs⟩
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext s
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hs
      exact ⟨U.equivFin ⟨s, hs⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver F y δ := fun j => hsecs ▸ hU (hrange ▸ Set.mem_range_self j)
  refine ⟨U.card, η, hη, ?_⟩
  refine (ChartSecGen.full F K ι Ω y k₀ N e hy δ U.card η hη).mpr fun I => ?_
  rw [hrange, hspanU I, hsub I]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleTwistVanish
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc quotPart)

def ModelCechTwist.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p b : ℕ) (m c : ℤ) (i : ℕ),
        Nonempty ((((Kleiman.twistMul Q.toSubSystem p m).pow b).twist
            (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).H i ≃ₗ[F]
          cechHc ι (quotPart F (mIdealOver F y)) (b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelCechTwist.proof (hMul : ChartSecMul.Statement) (hBase : BaseRealises.Statement)
    (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) : ModelCechTwist.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM β Q hQ p b m c i

  have hbun : ∀ (L : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : K → ℤ),
      BundleRealises y k₀ L δ → ∀ J, (L.sub J : Set Ω) = chartSecOver F y k₀ e δ J := by
    intro L δ hL J
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hL]
  have hO : ∀ (a : ℤ) J,
      ((Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) a).sub J : Set Ω) =
        chartSecOver F y k₀ e (a • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) J := fun a =>
    hbun (Kleiman.twistBundle F _ a) _ (hBase F K ι Ω y k₀ N e _ rfl hM a)

  have hmul : ∀ (R R' : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ δ' : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      (∀ J, (R'.sub J : Set Ω) = chartSecOver F y k₀ e δ' J) →
      ∀ J, ((R.twist R').sub J : Set Ω) = chartSecOver F y k₀ e (δ' + δ) J := by
    intro R R' δ δ' hR hR' J
    rw [twist_sub_eq_mul, Submodule.mul_eq_span_mul_set, hR' J, hR J]
    exact hMul F K ι Ω y k₀ N e hM δ' δ J
  have hpow : ∀ (R : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      ∀ (n : ℕ) J, ((R.pow n).sub J : Set Ω) = chartSecOver F y k₀ e (n • δ) J := by
    intro R δ hR n
    induction n with
    | zero =>
      intro J
      have h0 := hO 0 J
      rw [zero_smul] at h0
      rw [zero_smul]
      exact h0
    | succ n ih =>
      intro J
      rw [succ_nsmul']
      exact hmul _ _ _ _ ih hR J
  have hT := hmul _ _ _ _ (hpow _ _ (hmul _ _ _ _ (hpow _ _ (hbun Q β hQ) p) (hO m)) b) (hO c)
  have hγ : c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + b • (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + p • β) =
      b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp only [IndefiniteRowSideFullHecke.Kleiman2.stepL]
    module
  rw [hγ] at hT
  obtain ⟨e₁⟩ := hRef F K ι Ω y k₀ N e hM _ _ hT i
  obtain ⟨e₂⟩ := hLoc F K ι Ω y _ i
  exact ⟨e₁.trans e₂⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanishAll
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem TwistVanishAll.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanishAll.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun i b c hi hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c i
  have := hc₀ i hi c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

theorem twistVanishAll_closed : Kleiman.TwistVanishAll.Statement.{0, 0} :=
  Kleiman.TwistVanishAll.proof Kleiman.Extension.full Kleiman.SerreVanish.full Kleiman.TwistSplit.proof

theorem lineBundle_twist_vanish {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (Q : Kleiman.LineBundle F x) :
    ∃ c₀ : ℤ, ∀ (i : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton ((Q.twist (Kleiman.twistSys F x c)).H i) := by
  obtain ⟨c₀, hc₀⟩ := twistVanishAll_closed F Ω N x Q (Kleiman.twistBundle F x 1) N x
    Kleiman.mem_secs_twistBundle_one Kleiman.span_range_eq_twistMod_one
  refine ⟨c₀, fun i c hi hc => ?_⟩
  have h := hc₀ i 0 c hi hc
  have e : Q.twist ((Kleiman.twistBundle F x 1).pow 0) = Q.toSubSystem :=
    Kleiman.SubSystem.twist_twistSys_zero _
  rwa [e] at h

theorem RayVanish.proof (hMC : ModelCechTwist.Statement) : RayVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ hM β
  have : Nonempty (ι k₀) := let ⟨i, _⟩ := hM.1 k₀; ⟨i⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := lineBundle_twist_vanish Q
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun c hc i hi => ?_⟩
  obtain ⟨φ⟩ := hMC F K ι Ω y k₀ N e hM β Q hQ 1 1 0 c i
  have hdeg : (1 : ℕ) • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β 1 0 + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ =
      β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL]
  have hsys : (Kleiman.twistMul Q.toSubSystem 1 0).pow 1 = Q.toSubSystem := by
    change (Kleiman.twistSys _ _ 0).twist (Kleiman.twistMul Q.toSubSystem 1 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.twistMul]
    change ((Kleiman.twistSys _ _ 0).twist Q.toSubSystem).twist (Kleiman.twistSys _ _ 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.SubSystem.twist_twistSys_zero]
  rw [hdeg, hsys] at φ
  have := hc₀ i c hi (by omega)
  exact φ.symm.toEquiv.subsingleton

theorem RayVanish.proof_of_ties (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) :
    RayVanish.Statement :=
  RayVanish.proof (ModelCechTwist.proof (ChartSecMul.proof BundleOfDeg.full) BaseRealises.proof hLoc hRef)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def ModelMulSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p : ℕ) (j : ℤ), (Kleiman.twistMul Q.toSubSystem p j).secs =
        secOver F y (p • β + j • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelVeryAmpleEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (a : ℕ) (m : ℤ), 1 ≤ a →
        (Kleiman.IsVeryAmple (Kleiman.twistMul Q.toSubSystem a m) ↔
          IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowLocCover.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      ∃ (m : ℕ) (f u : Fin m → Ω),
        (∀ l, f l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        (∀ l, u l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        ∑ l, u l * f l = 1 ∧
        ∀ l, ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I = ⊥) ∧
          (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I ≤
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I') ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l)
                (Function.update I k (insert (c k) (I k))) =
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellDMulLeft
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem cellD_mul_left (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ) (r : Ω)
    (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :
    cellD S y n (fun I => r * t I) = fun J => r * cellD S y n t J := by
  classical
  funext J
  simp only [cellD, LinearMap.pi_apply]
  split_ifs with hJ
  · simp only [LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm]
      rfl
    · simp
  · simp

theorem CellLocGlue.proof : CellLocGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y G R m f u hf hu hsum hR hloc q s hs hds
  classical
  have memC : ∀ (H : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) (x : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω),
      x ∈ cellCOf S H n ↔ ∀ I, x I ∈ H I.1 := fun H n x => by
    simp [cellCOf, Submodule.mem_pi]

  let J : Ideal R :=
    { carrier := {r | ∃ t ∈ cellCOf S G q, cellD S y q t = fun I => (r : Ω) * s I}
      add_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb, Submodule.add_mem _ hta htb, ?_⟩
        rw [map_add (f := _), ha, hb]
        funext I
        simp [add_mul]
      zero_mem' := ⟨0, Submodule.zero_mem _, by funext I; simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht, hdt⟩
        refine ⟨fun I => (c : Ω) * t I, (memC _ _ _).2 fun I => hR _ _ c.2 _ ((memC _ _ _).1 ht I), ?_⟩
        rw [cellD_mul_left, hdt]
        funext I
        simp [mul_assoc] }

  have hmono : ∀ l (I : ∀ k, Finset (ι k)),
      Monotone fun n : ℕ => (G I).comap (LinearMap.mulLeft S (f l ^ n)) := by
    intro l I n n' hnn' a ha
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at ha ⊢
    have : f l ^ n' * a = f l ^ (n' - n) * (f l ^ n * a) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnn']
    rw [this]
    exact hR _ _ (pow_mem (hf l) _) _ ha
  have key : ∀ l, ∃ N : ℕ, (⟨f l, hf l⟩ : R) ^ N ∈ J := by
    intro l
    have hsl : s ∈ cellCOf S (cellLocSys G (f l)) (q + 1) := by
      rw [memC] at hs ⊢
      intro I
      exact (le_iSup (fun n : ℕ => (G I.1).comap (LinearMap.mulLeft S (f l ^ n))) 0)
        (by simpa [Submodule.mem_comap] using hs I)
    obtain ⟨t, ht, hdt⟩ := hloc l q s hsl hds
    have hn : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q, ∃ n : ℕ, f l ^ n * t I ∈ G I.1 := by
      intro I
      have h := (memC _ _ _).1 ht I
      rw [cellLocSys, Submodule.mem_iSup_of_directed _ (hmono l I.1).directed_le] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa [Submodule.mem_comap] using hn⟩
    choose n hn using hn
    have : Finite (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := by unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell; infer_instance
    have : Fintype (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := Fintype.ofFinite _
    refine ⟨Finset.univ.sup n, fun I => f l ^ Finset.univ.sup n * t I, (memC _ _ _).2 fun I => ?_, ?_⟩
    · have := hmono l I.1 (Finset.le_sup (Finset.mem_univ I) : n I ≤ Finset.univ.sup n)
      exact this (by simpa [Submodule.mem_comap] using hn I)
    · rw [cellD_mul_left, hdt]
      funext I
      simp
  have hone : (1 : R) ∈ J := by
    have hrad : J.radical = ⊤ := by
      rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
      have h1 : (1 : R) = ∑ l, (⟨u l, hu l⟩ : R) * ⟨f l, hf l⟩ :=
        Subtype.ext (by simpa using hsum.symm)
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (key l)
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]
    exact Submodule.mem_top
  obtain ⟨t, ht, hdt⟩ := hone
  exact ⟨t, ht, by rw [hdt]; funext I; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RatioMonHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

noncomputable section

section Ratio

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def ResidueGen.ratioMon (β : K → ℤ) (c d : ∀ k, ι k) : MRingOver F ι :=
  ∏ k, (X ⟨k, d k⟩ ^ (β k).toNat * X ⟨k, c k⟩ ^ (-β k).toNat)

theorem ResidueGen.ratioMon_homog (β : K → ℤ) :
    ∃ a : K → ℕ, ∀ c d : ∀ k, ι k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ResidueGen.ratioMon (F := F) β c d) a := by
  classical
  refine ⟨_, fun c d => ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_prod _ _ _ fun k _ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_mul
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (d k)) _)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (c k)) _)⟩

omit [∀ k, Fintype (ι k)] in
theorem ResidueGen.aeval_ratioMon {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) =
      ∏ k, (z ⟨k, d k⟩ ^ (β k).toNat * z ⟨k, c k⟩ ^ (-β k).toNat) := by
  simp [ResidueGen.ratioMon, map_prod]


omit [∀ k, Fintype (ι k)] in
theorem ResidueGen.ratio_eval {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) / aeval z (ResidueGen.ratioMon (F := F) β d c) =
      (∏ k, z ⟨k, c k⟩ ^ (-β k)) / ∏ k, z ⟨k, d k⟩ ^ (-β k) := by
  rw [ResidueGen.aeval_ratioMon, ResidueGen.aeval_ratioMon, ← Finset.prod_div_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hck := hc k
  have hdk := hd k
  conv_rhs => rw [← Int.toNat_sub_toNat_neg (β k)]
  rw [neg_sub, zpow_sub₀ hck, zpow_sub₀ hdk]
  simp only [zpow_natCast]
  field_simp

end Ratio

theorem ResidueGen.proof : ResidueGen.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' _ R σ hσ hchart β hgen d₀ hd₀
  classical

  have hne : ∀ p : Σ k, ι k, y' p ≠ 0 → y p ≠ 0 := by
    rintro ⟨k, a⟩ hp h0
    obtain ⟨hm, he⟩ := hσ (X ⟨k, a⟩) (X ⟨k, a⟩) _ (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a) (by simpa [aeval_X] using hp)
    have h0' : (⟨_, hm⟩ : R) = 0 := Subtype.ext (by simp [aeval_X, h0])
    rw [h0', map_zero, aeval_X, div_self hp] at he
    exact zero_ne_one he
  have hy0 : ∀ k, y ⟨k, d₀ k⟩ ≠ 0 := fun k => hne _ (hd₀ k)
  have hG0' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  have hG0 : (∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy0 k)
  obtain ⟨ext, ext_eq⟩ : ∃ e : Ω → K', ∀ z (hz : z ∈ R), e z = σ ⟨z, hz⟩ :=
    ⟨fun z => if hz : z ∈ R then σ ⟨z, hz⟩ else 0, fun z hz => dif_pos hz⟩
  obtain ⟨a, ha⟩ := ResidueGen.ratioMon_homog (F := F) (ι := ι) β

  have key : ∀ h ∈ secOver F y β, ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∃ hh : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R,
        σ ⟨_, hh⟩ = ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) *
          ∏ k, y' ⟨k, c k⟩ ^ (-β k) := by
    intro h hH c hc'
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
    obtain ⟨h0R, -⟩ := hchart d₀ hd₀ _ ((PowRealises.mem_secOver y β h).mp hH d₀ hy0)
    obtain ⟨hrR, hr⟩ := hσ (ResidueGen.ratioMon β c d₀) (ResidueGen.ratioMon β d₀ c) a (ha c d₀) (ha d₀ c)
      (by
        rw [ResidueGen.aeval_ratioMon]
        exact Finset.prod_ne_zero_iff.mpr fun k _ =>
          mul_ne_zero (pow_ne_zero _ (hc' k)) (pow_ne_zero _ (hd₀ k)))
    have eqΩ := ResidueGen.ratio_eval (F := F) y β c d₀ hc hy0
    have eqK := ResidueGen.ratio_eval (F := F) y' β c d₀ hc' hd₀
    have hprod : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) = (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) *
        (aeval y (ResidueGen.ratioMon (F := F) β c d₀) / aeval y (ResidueGen.ratioMon (F := F) β d₀ c)) := by
      rw [eqΩ]
      field_simp
    have hmem : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R := by
      rw [hprod]
      exact mul_mem h0R hrR
    refine ⟨hmem, ?_⟩
    have hsplit : (⟨_, hmem⟩ : R) = ⟨_, h0R⟩ * ⟨_, hrR⟩ := Subtype.ext hprod
    rw [hsplit, map_mul, hr, eqK, ext_eq _ h0R]
    ring
  refine ⟨fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)),
    fun h hH => key h hH d₀ hd₀, ?_⟩
  intro c hc'
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
  have hGc' : (∏ k, y' ⟨k, c k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc' k)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, hH, rfl⟩
    rw [SetLike.mem_coe, PowRealises.mem_span_inv_iff _ hGc']
    obtain ⟨hh, he⟩ := key h hH c hc'
    obtain ⟨_, hin⟩ := hchart c hc' _ ((PowRealises.mem_secOver y β h).mp hH c hc)
    beta_reduce
    rw [← he]
    exact hin
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hg⟩ := hgen
    obtain ⟨u, hu, hsum⟩ := hg c hc
    choose hUR hUc using fun j => hchart c hc' _ (hu j)
    choose hWR hW using fun j => key (s j) (hs j) c hc'
    have hsumR : (∑ j, (⟨u j, hUR j⟩ : R) * ⟨_, hWR j⟩) = 1 := by
      apply Subtype.ext
      push_cast
      exact hsum
    have hone := congrArg σ hsumR
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at hone
    have h2 : (∑ j, σ ⟨u j, hUR j⟩ *
        (ext (s j * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)))) *
          (∏ k, y' ⟨k, c k⟩ ^ (-β k)) = 1 := by
      rw [Finset.sum_mul, ← hone]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hW j]
      ring
    rw [← eq_inv_of_mul_eq_one_left h2]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hj := Submodule.smul_mem
      (Submodule.span (chartRingOver F y' c)
        ((fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k))) ''
          (secOver F y β : Set Ω)))
      (⟨_, hUc j⟩ : chartRingOver F y' c) (Submodule.subset_span (Set.mem_image_of_mem _ (hs j)))
    rwa [Subalgebra.smul_def, smul_eq_mul] at hj

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeEmbed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated (cellRes_mk cellMon_mono isMultiHomog_monomial)

noncomputable section

namespace KHFreeEmbed

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_monoFrac {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (a : (Σ k, ι k) → ℤ)
    (hJ : ∀ k, negSet a k ⊆ J k) :
    KH.cellRes S (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) J I (monoFrac S J a) = monoFrac S I a := by
  have hI : ∀ k, negSet a k ⊆ I k := fun k => (hJ k).trans (hJI k)
  unfold monoFrac
  rw [dite_eq_left hJ, dite_eq_left hI, cellRes_mk (cellMon_mono hJI)]

theorem blockSum_add_negExp (a : (Σ k, ι k) → ℤ) (k : K) :
    KHFree.blockSum a k + ((∑ i, negExp a ⟨k, i⟩ : ℕ) : ℤ) = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ) := by
  unfold KHFree.blockSum
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [negExp, posExp, Finsupp.coe_equivFunOnFinite_symm]
  omega

theorem isMultiHomog_posExp (a : (Σ k, ι k) → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial (posExp a) (1 : S) : MRingOver S ι) fun k => ∑ i, posExp a ⟨k, i⟩ :=
  isMultiHomog_monomial _ _ _ fun _ => rfl

theorem mk_posExp_mem (a : (Σ k, ι k) → ℤ) (e : K → ℤ) (he : ∀ k, e k = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ)) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (posExp a) 1) ∈
      KH.quotPart S (⊥ : Ideal (MRingOver S ι)) e := by
  unfold KH.quotPart
  refine Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩
  · rw [he k]; exact Int.natCast_nonneg _
  · have : (fun k => (e k).toNat) = fun k => ∑ i, posExp a ⟨k, i⟩ := funext fun k => by rw [he k]; rfl
    rw [this]
    exact isMultiHomog_posExp a

theorem update_erase_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl; rw [Function.update_self]; exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]


open Classical in
theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n) :
    embed S a n f I = if h : ∀ k, negSet a k ⊆ I.1 k then f ⟨I, h⟩ • monoFrac S I.1 a else 0 := by
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl


open Classical in
theorem cechD_apply (n : ℕ) (x : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n)
    (I : KH.Cell K ι (n + 1)) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n x I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        KH.faceSign I.1 k i • KH.cellRes S _ (Function.update I.1 k ((I.1 k).erase i)) I.1
          (x ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  unfold KH.cechD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl


open Classical in
theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
          ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
        KH.faceSign I.1.1 k i • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  unfold combD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem embed_comm (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
      embed S a (n + 1) (combD S (negSet a) n f) := by
  classical
  funext I
  rw [cechD_apply, embed_apply]
  by_cases hI : ∀ k, negSet a k ⊆ I.1 k
  · rw [dite_eq_left hI]
    erw [combD_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n
    · rw [dite_eq_left hc]
      erw [embed_apply]
      by_cases hJ : ∀ l, negSet a l ⊆ Function.update I.1 k ((I.1 k).erase i) l
      · rw [dite_eq_left hJ, dite_eq_left ⟨hc, hJ⟩, LinearMap.map_smul_of_tower,
          cellRes_monoFrac (update_erase_subset I.1 k i) a hJ, smul_assoc]
      · rw [dite_eq_right hJ, dite_eq_right (fun h => hJ h.2), map_zero]
        simp
    · rw [dite_eq_right hc, dite_eq_right (fun h => hc h.1), zero_smul]
  · rw [dite_eq_right hI]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hc
    · erw [embed_apply]
      rw [dite_eq_right (fun hJ => hI fun l => (hJ l).trans (update_erase_subset I.1 k i l)), map_zero]
      simp
    · rfl

theorem embed_mem (a : (Σ k, ι k) → ℤ) (c d : K → ℤ) (h : KHFree.blockSum a = c + d) (n : ℕ)
    (f : CombC S (negSet a) n) :
    embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  classical
  unfold KH.cechCc
  refine Submodule.mem_pi.mpr fun I _ => ?_
  erw [embed_apply]
  split_ifs with hI
  · refine Submodule.smul_mem _ _ ?_
    unfold monoFrac
    rw [dite_eq_left hI]
    refine Submodule.subset_span ⟨_, _, fun k => ∑ i, negExp a ⟨k, i⟩,
      isMultiHomog_monomial _ _ _ fun _ => rfl, ?_, rfl⟩
    refine mk_posExp_mem a _ fun k => ?_
    have hk := blockSum_add_negExp a k
    rw [h] at hk
    simp only [Pi.add_apply] at hk ⊢
    linarith
  · exact zero_mem _

theorem monoFrac_of_nonneg (a : (Σ k, ι k) → ℤ) (ha : ∀ p, 0 ≤ a p) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (KHFree.blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1 := by
  classical
  have hneg : ∀ k, negSet a k = ∅ := fun k =>
    Finset.filter_eq_empty_iff.mpr fun i _ => not_lt.mpr (ha _)
  have hnegExp : negExp a = 0 := by
    ext p
    simp only [negExp, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
    have := ha p
    omega
  refine ⟨_, mk_posExp_mem a _ fun k => ?_, fun I => ?_⟩
  · have hk := blockSum_add_negExp a k
    rw [hnegExp] at hk
    simpa using hk
  · have hI : ∀ k, negSet a k ⊆ I k := fun k => by rw [hneg k]; exact Finset.empty_subset _
    unfold monoFrac
    rw [dite_eq_left hI]
    congr 1
    exact Subtype.ext (by simp [hnegExp])

theorem full : KHFreeEmbed.Statement := by
  intro S _ K _ _ ι _ _ a
  exact ⟨fun n f => embed_comm a n f, fun c d h n f => embed_mem a c d h n f, monoFrac_of_nonneg a⟩

end KHFreeEmbed

end

end GroundTheory.Heights₂.Heights.Kleiman
end
