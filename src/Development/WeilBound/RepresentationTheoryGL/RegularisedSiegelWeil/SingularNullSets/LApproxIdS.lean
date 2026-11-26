module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem haar_map_eq {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G']
    [SecondCountableTopology G'] [T2Space G'] [MeasurableSpace G'] [BorelSpace G'] (Θ : G ≃ₜ+ G')
    (μ : Measure G) [μ.IsAddHaarMeasure] (μ' : Measure G') [μ'.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map Θ = c • μ' := by
  haveI : (μ.map Θ).IsAddHaarMeasure := Θ.isAddHaarMeasure_map μ
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, Measure.isAddLeftInvariant_eq_smul _ _⟩

def fixS {X : Type} [AddCommGroup X] (p : X →+ X) : AddSubgroup X where
  carrier := {x | p x = x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add (f := _), ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_neg, ha]

theorem decomp {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (p : X →+ X) (hp : Continuous p)
    (hpp : ∀ x, p (p x) = p x) (μ : Measure X) [μ.IsAddHaarMeasure] (νH : Measure (fixS p)) [νH.IsAddHaarMeasure]
    (νY : Measure p.ker) [νY.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : X → ℂ,
      (Integrable f μ ↔ Integrable (fun z : fixS p × p.ker => f (z.1.1 + z.2.1)) (νH.prod νY)) ∧
      ∫ x, f x ∂μ = (c : ℂ) * ∫ z : fixS p × p.ker, f (z.1.1 + z.2.1) ∂(νH.prod νY) := by
  have hH : IsClosed (fixS p : Set X) := isClosed_eq hp continuous_id
  have hY : IsClosed (p.ker : Set X) := isClosed_singleton.preimage hp
  haveI : LocallyCompactSpace (fixS p) := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace p.ker := hY.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (fixS p) :=
    TopologicalSpace.Subtype.secondCountableTopology (fixS p : Set X)
  haveI : SecondCountableTopology p.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (p.ker : Set X)
  haveI : BorelSpace (fixS p) := inferInstance
  haveI : BorelSpace p.ker := inferInstance
  haveI : BorelSpace (fixS p × p.ker) := Prod.borelSpace
  let Θ : (fixS p × p.ker) ≃ₜ+ X :=
    { toFun := fun z => z.1.1 + z.2.1
      invFun := fun x => (⟨p x, hpp x⟩, ⟨x - p x, by rw [AddMonoidHom.mem_ker, map_sub, hpp, sub_self]⟩)
      left_inv := by
        rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        have ha' : p a = a := ha
        have hb' : p b = 0 := hb
        ext <;> simp [ha', hb']
      right_inv := fun x => by simp
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add]
        abel
      continuous_toFun := by fun_prop
      continuous_invFun := by
        refine Continuous.prodMk (hp.subtype_mk _) ((continuous_id.sub hp).subtype_mk _) }
  obtain ⟨c, hc, hmap⟩ := haar_map_eq Θ (νH.prod νY) μ
  have hemb : MeasurableEmbedding Θ := Θ.toHomeomorph.measurableEmbedding
  have hμ : μ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) • (νH.prod νY).map Θ := by
    rw [hmap, ← ENNReal.smul_def, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨c⁻¹, inv_pos.2 hc, fun f => ⟨?_, ?_⟩⟩
  · rw [hμ, integrable_smul_measure (by simpa using hc.ne') ENNReal.coe_ne_top, hemb.integrable_map_iff]
    rfl
  · rw [hμ, integral_smul_measure, hemb.integral_map]
    simp only [ENNReal.coe_toReal, Complex.real_smul, NNReal.coe_inv, Complex.ofReal_inv]
    push_cast
    rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

abbrev fixE {F : Type} [Field F] [NumberField F] (ε : AF F) : AddSubgroup (AF F) := fixS (AddMonoidHom.mulLeft ε)


open Classical in
def IsIdF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) : Prop :=
  fstA F ε = 1 ∧ ∀ v, (sndA F ε) v = if v ∈ S then 1 else 0

def OneD : Prop := ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsIdF S ε → ∀ ν : Measure (fixE ε), ν.IsAddHaarMeasure →
  ∃ (g : ℕ → fixE ε → ℂ) (G : ℕ → AF F → ℝ) (Sp : ℕ → Set (AF F)),
    (∀ k, Integrable (g k) ν ∧ (∀ h, ‖g k h‖ ≤ 1) ∧ ∀ s, 0 ≤ G k s ∧ ∫ h, g k h * ψ (h.1 * s) ∂ν = G k s) ∧
    (∀ h, Tendsto (fun k => g k h) atTop (𝓝 1)) ∧
    (∀ k s, G k s ≠ 0 → -(ε * s) ∈ Sp k) ∧ Tendsto Sp atTop (𝓝 (0 : AF F)).smallSets

end PositivityTheory.Rg.Rsw.L.LApproxId

end
