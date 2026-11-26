module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Assembly
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPtZeroNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def ModelNumEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (d : ℕ) (βs : Fin d → K → ℤ)
      (Qs : Fin d → Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ j (c : ℤ), ((Qs j).twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (βs j + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
          (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) d →
      Kleiman.interNum (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
          (fun j => (Qs j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) βs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfModelNumEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelNumEq.proof (hN : NumModel.Statement) : ModelNumEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d βs Qs hsecs hsub
  exact hN F K ι Ω y k₀ N e _ rfl hmod d Qs βs (fun j c => hsecs j c) hsub

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqSegreRealise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem SegreRealise.proof (hB : SegreBase.Statement) (hT : SegreTwist.Statement) (hD : SegreDim.Statement)
    (hNf : SegreNef.Statement) (hNm : SegreNum.Statement) (hBd : BundleOfDeg.Statement)
    (hMD : ModelDimEq.Statement) (hMN : ModelNefEq.Statement) (hMNum : ModelNumEq.Statement) :
    SegreRealise.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y d μs hy hd
  have : ∀ a, Nonempty (ι a) := fun a => ⟨(hy a).choose⟩
  have hcard : 0 < Fintype.card (∀ a, ι a) := Fintype.card_pos
  let N := Fintype.card (∀ a, ι a) - 1
  let eqv : (∀ a, ι a) ≃ Fin (N + 1) := Fintype.equivFinOfCardEq (by omega)
  have hbase : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (segreJoin y) (Sum.inl ()) := (hB F K ι Ω y hy).1
  choose Ms hMs using fun j =>
    hBd F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j))
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)) d :=
    (hMD F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d).2 (by rw [hD F K ι Ω y hy]; exact hd)
  refine ⟨N, eqv, IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm, Ms, fun i => ?_, hsub,
    fun j c => ?_, fun j => ?_, ?_⟩
  · show ∏ a, y ⟨a, eqv.symm (eqv i) a⟩ = ∏ a, y ⟨a, i a⟩
    rw [Equiv.symm_apply_apply]
  · exact (hMs j c).trans (hT F K ι Ω y hy (μs j) c)
  · exact (hMN F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase _ (Ms j) (hMs j)).trans (hNf F K ι Ω y hy (μs j))
  · exact (hMNum F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) Ms
      hMs hsub).trans (hNm F K ι Ω y hy d μs)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.Kleiman

theorem KleimanNefB.segreRealise (hNef : SectionsOverLocalization.NefEq.Statement) (hCh : SectionsOverLocalization.ModelChangeNef.Statement)
    (hNM : SectionsOverLocalization.NumModel.Statement) : SectionsOverLocalization.SegreRealise.Statement :=
  SectionsOverLocalization.SegreRealise.proof SectionsOverLocalization.SegreBase.proof SectionsOverLocalization.SegreTwist.proof SectionsOverLocalization.SegreDim.proof
    (SectionsOverLocalization.SegreNef.proof SectionsOverLocalization.SegreDim.proof SectionsOverLocalization.SegreNum.proof) SectionsOverLocalization.SegreNum.proof
    SectionsOverLocalization.BundleOfDeg.full SectionsOverLocalization.ModelDimEq.full (SectionsOverLocalization.ModelNefEq.proof hNef hCh)
    (SectionsOverLocalization.ModelNumEq.proof hNM)

end GroundTheory.Heights₂.Heights.ForSecondHalf
