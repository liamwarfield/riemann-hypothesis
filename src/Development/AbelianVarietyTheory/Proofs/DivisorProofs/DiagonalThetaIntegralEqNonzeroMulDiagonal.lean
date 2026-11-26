module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DarbouxMeasure

theorem transport_covol_one : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  intro D S T κ _ e he ν 𝓕 hc
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F)
      (Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
  obtain ⟨hH, hF, h1⟩ := hc
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Formalism.IndefR.Datum.WO S T ≃ₜ ((κ → AF D.host.F) × (κ → AF D.host.F)) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  let m := h.toMeasurableEquiv
  refine ⟨Measure.map m ν, m '' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e.toAddEquiv hc1 hc2
  · let r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ ≃ ratL T S :=
      { toFun := fun p => ⟨e.symm p, (he (e.symm p)).2 (by simpa using p.2)⟩
        invFun := fun γ => ⟨e γ, (he γ).1 γ.2⟩
        left_inv := fun p => by ext1; simp
        right_inv := fun γ => by ext1; simp }
    refine hF.image_of_equiv m.toEquiv (m.measurePreserving_symm ν).quasiMeasurePreserving r ?_
    intro g x
    change e (e.symm (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + x) = (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + e x
    rw [map_add (f := _), LinearEquiv.apply_symm_apply]
  · rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ m.injective, h1]
  · intro g
    rw [m.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ m.injective]
    rfl

end GlobalTheory.DarbouxMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  first | exact @GlobalTheory.DarbouxMeasure.transport_covol_one | exact GlobalTheory.DarbouxMeasure.transport_covol_one | (intros; apply GlobalTheory.DarbouxMeasure.transport_covol_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaUnfoldInt

theorem integral_fundamentalDomain_tsum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ 𝓕₁ h𝓕 hfin h hc hB
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := hB
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (GlobalTheory.ThetaUnfold.ratEquiv F κ)
  have hcont : ∀ η : κ → F, Continuous fun x => h ((fun i => algebraMap F (AF F) (η i)) + x) :=
    fun η => hc.comp (continuous_const.add continuous_id)
  have hreidx : ∀ f : (κ → AF F) → ENNReal,
      ∫⁻ x, f x ∂μ = ∑' η : κ → F, ∫⁻ x in 𝓕₁, f ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ := by
    intro f
    rw [h𝓕.lintegral_eq_tsum' f, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
    refine tsum_congr fun ξ => ?_
    simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
    rfl
  have hpt : ∀ x, ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ≤ ENNReal.ofReal B := by
    intro x
    obtain ⟨hs, hle⟩ := hB x
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hle
  have hfinite : ∑' η : κ → F, ∫⁻ x in 𝓕₁, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum fun η => (hcont η).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hint : Integrable h μ := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖h a‖ₑ ∂μ < ⊤
    rw [hreidx fun a => ‖h a‖ₑ]
    exact hfinite.lt_top
  rw [integral_tsum (fun η => (hcont η).aestronglyMeasurable) hfinite,
    h𝓕.integral_eq_tsum' h hint, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl

end GlobalTheory.ThetaUnfoldInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  first | exact @GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum | exact GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum | (intros; apply GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.RatDarbouxPointsD


set_option maxHeartbeats 1000000 in
theorem ratL_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  intro D S T κ _ e hrat w
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  · intro hp

    let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
    haveI : Module.Free (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Finite.of_basis bA
    have hAE : Module.finrank (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) =
        Module.finrank D.host.F D.host.E := by
      rw [Module.finrank_eq_card_basis bA, Fintype.card_fin]
    have hκ : 2 * Fintype.card κ = T.rank * S.rank * Module.finrank D.host.F D.host.E := by
      have h := e.finrank_eq
      have ha : Module.finrank (AF D.host.F)
          (Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AF D.host.F ⊗[D.host.F] D.host.E) = _
        simp [Module.finrank_pi_fintype, hAE, mul_assoc]
      have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [← hb, ← h, ha]

    let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
      LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
    let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
      J1.prodMap J1
    let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F]
        Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
      (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
    let L := (e.toLinearMap.restrictScalars D.host.F).comp I
    have hJinj : Function.Injective J := by
      rintro ⟨y, z⟩ ⟨y', z'⟩ h
      have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
      simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
      refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
      · exact congrFun h.1 i
      · exact congrFun h.2 i
    have hLinj : Function.Injective L := by
      have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
      intro x x' h
      have := e.injective h
      exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
    have hle : LinearMap.range L ≤ LinearMap.range J := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, h⟩ := hrat x
      exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
    have heq : LinearMap.range L = LinearMap.range J := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
      have hm : Module.finrank D.host.F (Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank D.host.F (Fin T.rank → Fin S.rank → D.host.E) = _
        simp [Module.finrank_pi_fintype, mul_assoc]
      have hp2 : Module.finrank D.host.F ((κ → D.host.F) × (κ → D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [hm, hp2, hκ]
    obtain ⟨y, z, hw⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_⟩
    have hx' : e (incM D.host.F x) = e w := by rw [hw]; exact hx
    exact e.injective hx'

end GlobalTheory.RatDarbouxPointsD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  first | exact @GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair | exact GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair | (intros; apply GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNormAdelicSchwartzRationalTranslatesLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNormAdelicSchwartzRationalTranslatesLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.UniformTranslateBound

open Filter Topology
open scoped Classical

theorem schwartz_translate_decay {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) (k : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : E, ‖y‖ ≤ R → ‖f (x + y)‖ ≤ D * ((1 + ‖x‖) ^ k)⁻¹ := by
  set M := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hM
  have h0 : ∀ w : E, (1 + ‖w‖) ^ k * ‖f w‖ ≤ M := fun w => by
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f w
    rwa [norm_iteratedFDeriv_zero] at h1
  have hM0 : 0 ≤ M := le_trans (by positivity) (h0 0)
  refine ⟨(1 + R) ^ k * M, by positivity, fun x y hy => ?_⟩
  have hx : 0 < (1 + ‖x‖) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hx]
  have h2 : 1 + ‖x‖ ≤ (1 + R) * (1 + ‖x + y‖) := by
    have : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by simpa using norm_sub_le (x + y) y
    nlinarith [norm_nonneg (x + y), norm_nonneg y, mul_nonneg hR (norm_nonneg (x + y))]
  calc ‖f (x + y)‖ * (1 + ‖x‖) ^ k ≤ ‖f (x + y)‖ * ((1 + R) * (1 + ‖x + y‖)) ^ k := by gcongr
    _ = (1 + R) ^ k * ((1 + ‖x + y‖) ^ k * ‖f (x + y)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + R) ^ k * M := by gcongr; exact h0 _

theorem summable_one_add_norm_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), ← inv_pow]
  gcongr
  show ‖z‖ ≤ 1 + ‖z‖
  linarith

variable (F : Type) [Field F] [NumberField F]

theorem mixed_algebraMap_fst (x : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) x).1 = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem pureA_bound {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  let zi : (κ → AdeleRing (𝓞 F) F) → (κ → mixedEmbedding.mixedSpace F) :=
    fun z i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : (κ → AdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun z i => (z i).2
  have hzi : Continuous zi :=
    continuous_pi fun i => (GlobalTheory.ThetaTransformMeas.continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  have hzf : Continuous zf := continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  obtain ⟨R, hR⟩ := (hK.image hzi).isBounded.subset_closedBall 0
  obtain ⟨Bg, hBg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  let C : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - p.2) '' (tsupport g ×ˢ (zf '' K))
  have hC : IsCompact C := (hg.2.isCompact.prod (hK.image hzf)).image (continuous_fst.sub continuous_snd)
  obtain ⟨N, hN, hNC⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hC
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let e : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i)
  let S : Set (κ → F) := {ξ | e ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  obtain ⟨D, hD0, hD⟩ := schwartz_translate_decay f (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1)
    (max R 0) (le_max_right _ _)
  let h : (κ → F) → ℝ := S.indicator fun ξ =>
    D * ((1 + ‖e ξ‖) ^ (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1))⁻¹ * Bg
  have hh : ∀ ξ, 0 ≤ h ξ := fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
  have hsum : Summable h := by
    rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val hab) i))
    exact (((summable_one_add_norm_inv _).comp_injective hj).mul_left D).mul_right Bg
  refine ⟨∑' ξ, h ξ, fun z hz s => ?_⟩
  refine le_trans (Finset.sum_le_sum fun ξ _ => ?_) (hsum.sum_le_tsum s fun ξ _ => hh ξ)
  have hsplit : GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z) =
      f (e ξ + zi z) * g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) := by
    unfold GlobalTheory.WeilM.pureA
    congr 2
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).1 + (z i).1) = _
    rw [map_add (f := _), mixed_algebraMap_fst]
    rfl
  rw [hsplit, norm_mul]
  by_cases hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) = 0
  · rw [hg0, norm_zero, mul_zero]; exact hh ξ
  have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ C :=
    ⟨(_, zf z), ⟨subset_tsupport _ hg0, z, hz, rfl⟩, add_sub_cancel_right _ _⟩
  have hξS : ξ ∈ S := by
    show ∀ i, (N : ℝ) • e ξ i ∈ mixedEmbedding.integerLattice F
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hNC _ hmem i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  show _ ≤ S.indicator _ ξ
  rw [Set.indicator_of_mem hξS]
  have hzR : ‖zi z‖ ≤ max R 0 := le_max_of_le_left (mem_closedBall_zero_iff.1 (hR ⟨z, hz, rfl⟩))
  exact mul_le_mul (hD _ _ hzR) (hBg _) (norm_nonneg _) (by positivity)

theorem schA_bound_compact {κ : Type} [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pureA_bound F f hg hK
  | zero => exact ⟨0, fun z _ s => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨B1, hB1⟩ := h1
    obtain ⟨B2, hB2⟩ := h2
    refine ⟨B1 + B2, fun z hz s => ?_⟩
    refine le_trans (Finset.sum_le_sum fun ξ _ => norm_add_le (Φ _) (Ψ _)) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add (hB1 z hz s) (hB2 z hz s)
  | smul c Φ _ h =>
    obtain ⟨B, hB⟩ := h
    refine ⟨‖c‖ * B, fun z hz s => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB z hz s) (norm_nonneg c)

theorem tsum_norm_translate_le : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι],
    ∀ Φ ∈ GlobalTheory.WeilM.schA F ι,
    ∃ B : ℝ, ∀ z : ι → AF F, ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ ≤ B := by
  intro F _ _ ι _ Φ hΦ
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.RatVecDomain.exists_compact_cover_ratVec F ι
  obtain ⟨B, hB⟩ := schA_bound_compact F hΦ hK
  refine ⟨B, fun z => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hcov z
  obtain ⟨η, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff _).1 hγ
  let G : (ι → F) → ℝ := fun ξ =>
    ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i)) + z))‖
  have hG : ∀ ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = G (Equiv.subRight η ξ) := by
    intro ξ
    show _ = ‖Φ _‖
    congr 2
    ext i
    simp only [Pi.add_apply, Equiv.subRight_apply, Pi.sub_apply, map_sub]
    abel
  calc ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = ∑' ξ, G (Equiv.subRight η ξ) := tsum_congr hG
    _ = ∑' ξ, G ξ := (Equiv.subRight η).tsum_eq G
    _ ≤ B := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (hB _ hγK)

end GlobalTheory.UniformTranslateBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNormAdelicSchwartzRationalTranslatesLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_norm_adelicSchwartz_rationalTranslates_le : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι], ∀ Φ ∈ GlobalTheory.WeilM.schA F ι,
    ∃ B : ℝ, ∀ z : ι → AF F, ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ ≤ B := by
  first | exact @GlobalTheory.UniformTranslateBound.tsum_norm_translate_le | exact GlobalTheory.UniformTranslateBound.tsum_norm_translate_le | (intros; apply GlobalTheory.UniformTranslateBound.tsum_norm_translate_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIterated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIterated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.PeriodicIteratedIntegral

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem integral_fundamentalDomain_eq_iterated (Γ₁ : AddSubgroup V) [Countable Γ₁]
    (Γ : AddSubgroup (V × V)) (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (mW : MeasurableSpace (V × V)) (hmW : mW = Prod.instMeasurableSpace)
    (ν : @Measure (V × V) mW) (hν : @Measure.IsAddHaarMeasure _ _ _ mW ν)
    (𝓕 : Set (V × V)) (h𝓕 : @IsAddFundamentalDomain Γ _ _ _ mW 𝓕 ν)
    (𝓕₁ : Set V) (h𝓕₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) (hfin : μ 𝓕₁ ≠ ⊤) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : V × V → ℂ, @Measurable _ _ mW _ G →
      (∀ γ ∈ Γ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓕, G w ∂ν = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  subst hmW
  haveI := hν
  haveI : Countable Γ := by
    have hinj : Function.Injective (fun k : Γ =>
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁), (⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁))) := by
      intro k k' hk
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk
      exact Subtype.ext (Prod.ext hk.1 hk.2)
    exact hinj.countable
  have hmeq := Measure.isAddLeftInvariant_eq_smul ν (μ.prod μ)
  set c : NNReal := Measure.addHaarScalarFactor ν (μ.prod μ)
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (μ.prod μ)
  have hν' : ν = (c : ENNReal) • μ.prod μ := by
    rw [← ENNReal.smul_def]; exact hmeq
  refine ⟨(c : ℝ), by exact_mod_cast hcpos, fun G hG hper hB => ?_⟩
  obtain ⟨B, hB⟩ := hB
  open scoped Pointwise in
  have hprod : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) (μ.prod μ) := by
    refine ⟨h𝓕₁.nullMeasurableSet.prod h𝓕₁.nullMeasurableSet, ?_, ?_⟩
    · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h𝓕₁.ae_covers
      have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h𝓕₁.ae_covers
      filter_upwards [h1, h2] with p ha hb
      obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      exact ⟨⟨((a : V), (b : V)), (hΓ _).2 ⟨a.2, b.2⟩⟩, ha, hb⟩
    · intro g g' hne
      have hset : ∀ k : Γ, k +ᵥ (𝓕₁ ×ˢ 𝓕₁) =
          ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁) +ᵥ 𝓕₁) ×ˢ
            ((⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁) +ᵥ 𝓕₁) := by
        intro k
        ext ⟨x, y⟩
        simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod, AddSubgroup.vadd_def,
          AddSubgroup.coe_neg, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      show μ.prod μ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₁))) = 0
      rw [hset g, hset g', Set.prod_inter_prod, Measure.prod_prod]
      by_cases h1 : (g : V × V).1 = (g' : V × V).1
      · have h2 : (g : V × V).2 ≠ (g' : V × V).2 := by
          intro h2
          exact hne (Subtype.ext (Prod.ext h1 h2))
        have := h𝓕₁.aedisjoint (i := ⟨(g : V × V).2, ((hΓ _).1 g.2).2⟩)
          (j := ⟨(g' : V × V).2, ((hΓ _).1 g'.2).2⟩) (fun h' => h2 (congrArg Subtype.val h'))
        rw [show μ _ = 0 from this, mul_zero]
      · have := h𝓕₁.aedisjoint (i := ⟨(g : V × V).1, ((hΓ _).1 g.2).1⟩)
          (j := ⟨(g' : V × V).1, ((hΓ _).1 g'.2).1⟩) (fun h' => h1 (congrArg Subtype.val h'))
        rw [show μ _ = 0 from this, zero_mul]
  have hD : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) ν :=
    hprod.mono (by rw [hν']; exact Measure.smul_absolutelyContinuous)
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  have hint : Integrable G ((μ.restrict 𝓕₁).prod (μ.restrict 𝓕₁)) :=
    Integrable.of_bound hG.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  rw [h𝓕.setIntegral_eq hD (fun g x => hper g g.2 x), hν', Measure.restrict_smul,
    integral_smul_measure, ← Measure.prod_restrict, integral_prod _ hint, ENNReal.coe_toReal,
    Complex.real_smul]

end General

end GlobalTheory.PeriodicIteratedIntegral

namespace GlobalTheory.PeriodicIteratedIntegral

theorem integral_ratPair_fundamentalDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ (lam : MeasureTheory.Measure ((κ → AF F) × (κ → AF F))), lam.IsAddHaarMeasure →
    ∀ 𝓖 : Set ((κ → AF F) × (κ → AF F)),
      MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) 𝓖 lam →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ℂ, Measurable G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓖, G w ∂lam = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  intro F _ _ κ _ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ hfin
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.PeriodicIterated.countable_ratVec F κ
  haveI := hμ
  exact integral_fundamentalDomain_eq_iterated (GlobalTheory.ThetaParseval.ratVec F κ)
    (GlobalTheory.WeilUnitaryTransport.ratPair F κ) (GlobalTheory.PeriodicIterated.mem_ratPair_iff_ratVec F κ) μ (borel _)
    (Prod.borelSpace (α := κ → AF F) (β := κ → AF F)).measurable_eq.symm lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ hfin

end GlobalTheory.PeriodicIteratedIntegral

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIteratedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ (lam : MeasureTheory.Measure ((κ → AF F) × (κ → AF F))), lam.IsAddHaarMeasure →
    ∀ 𝓖 : Set ((κ → AF F) × (κ → AF F)),
      MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) 𝓖 lam →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ℂ, Measurable G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓖, G w ∂lam = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  first | exact @GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated | exact GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DiagThetaRatInv

theorem dot_elim {R : Type} [CommRing R] {κ : Type} [Fintype κ] (x : κ ⊕ κ → R) (v : κ → R) :
    x ⬝ᵥ Sum.elim v (-v) = ∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem schr_diag {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (u v : κ → R) (Φ : (κ ⊕ κ → R) → ℂ) (x : κ ⊕ κ → R) :
    GlobalTheory.WeilM.schr ψ (Sum.elim u u, Sum.elim v (-v)) Φ x =
      ψ (∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i) * Φ (x + Sum.elim u u) := by
  simp only [GlobalTheory.WeilM.schr]
  rw [dot_elim, dot_elim]
  simp

theorem diag_theta_rat_inv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).1 hγ
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← (Equiv.subRight (Sum.elim a a)).tsum_eq]
  congr 1
  funext η
  rw [schr_diag, schr_diag]
  simp only [Equiv.subRight_apply, Prod.fst_add, Prod.snd_add]
  have h1 : (∑ i, (algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inl i)) -
        algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inr i))) * ((fun i => algebraMap F (AF F) (b i)) + w.2) i) =
      algebraMap F (AF F) (∑ i, (η (Sum.inl i) - η (Sum.inr i)) * b i) +
        ∑ i, (algebraMap F (AF F) (η (Sum.inl i)) - algebraMap F (AF F) (η (Sum.inr i))) * w.2 i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, map_sub, map_mul]
    ring
  have h2 : (fun i => algebraMap F (AF F) ((η - Sum.elim a a) i)) +
        Sum.elim ((fun i => algebraMap F (AF F) (a i)) + w.1) ((fun i => algebraMap F (AF F) (a i)) + w.1) =
      (fun i => algebraMap F (AF F) (η i)) + Sum.elim w.1 w.1 := by
    funext j
    cases j <;> simp <;> abel
  rw [h1, h2, AddChar.map_add_eq_mul, hψ.2.2.1, one_mul]

end GlobalTheory.DiagThetaRatInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalThetaSum_rationalPair_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  first | exact @GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | exact GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | (intros; apply GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegelUnfold

open MeasureTheory


set_option maxHeartbeats 1000000 in
theorem diag_theta_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ S T JA JB ξ hJA hJB κ _ co hrat ν 𝓕 hν μ hμ
  letI mV : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  letI mVV : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  have hψc : IsCharAF D.host.F ψ := hψ.1
  obtain ⟨lam, 𝓖, hlam, h𝓖, -, htr⟩ := GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar D S T κ co.e (GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair D S T κ co.e hrat) ν 𝓕 hν
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain D.host.F κ μ hμ
  obtain ⟨c₁, hc₁, hiter⟩ := GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated D.host.F κ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ htop
  have hpos : 0 < μ.real 𝓕₁ := ENNReal.toReal_pos h0 htop
  refine ⟨((c₁ * μ.real 𝓕₁ : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr (mul_pos hc₁ hpos).ne', fun Φ hΦ => ?_⟩

  set G : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ := fun p =>
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) Φ) with hGdef
  have hdiag : ∀ w, GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ (GlobalTheory.DiagSiegel.diagMat w) =
      G (co.e w) := by
    intro w
    have h1 : (GlobalTheory.DblSchr.ddr co).e (GlobalTheory.DiagSiegel.diagMat w) =
        (Sum.elim (co.e w).1 (co.e w).1, Sum.elim (co.e w).2 (-(co.e w).2)) := by
      rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e]
      have h2 : (GlobalTheory.DiagSiegel.diagMat w).submatrix id finSumFinEquiv.symm.symm = Matrix.fromCols w w := by
        ext i j
        simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_apply_apply, id]
      rw [h2]
      rfl
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, h1, hGdef]

  obtain ⟨B, hB⟩ := GlobalTheory.T.tsum_norm_adelicSchwartz_rationalTranslates_le D.host.F (κ ⊕ κ) Φ hΦ
  have hsumΦ : ∀ z : κ ⊕ κ → AF D.host.F, Summable fun ξ : κ ⊕ κ → D.host.F =>
      ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + z)‖ := fun z => by
    have h1 := GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F z hΦ)
    exact h1
  have hGbd : ∃ B : ℝ, ∀ w, ‖G w‖ ≤ B := by
    refine ⟨B, fun w => ?_⟩
    have hn : ∀ ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ =
        ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ := by
      intro ξ
      simp only [GlobalTheory.WeilM.schr, norm_mul, hψc.2.1, one_mul]
    have hs : Summable fun ξ : κ ⊕ κ → D.host.F => ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := by
      simp_rw [hn]
      exact hsumΦ _
    calc ‖G w‖ ≤ ∑' ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
          (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' ξ : κ ⊕ κ → D.host.F, ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ :=
          tsum_congr hn
      _ ≤ B := hB _
  have hGm : Measurable G := by
    letI mW : MeasurableSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := borel _
    haveI : BorelSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := ⟨rfl⟩
    have hm := GlobalTheory.ThetaTransformMeas.main D.host.F ψ hψc (κ ⊕ κ) Φ hΦ
    have hc : Continuous fun p : (κ → AF D.host.F) × (κ → AF D.host.F) =>
        ((Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) : (κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := by
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_) <;> rcases i with i | i
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_snd
      · exact ((continuous_apply i).comp continuous_snd).neg
    exact hm.comp hc.measurable
  have hGper : ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, ∀ w, G (γ + w) = G w :=
    fun γ hγ w => GlobalTheory.T.diagonalThetaSum_rationalPair_invariant D.host.F ψ hψc κ Φ γ hγ w

  set h : (κ → AF D.host.F) → ℂ := fun u => Φ (Sum.elim u u) with hhdef
  have hcont : Continuous h :=
    (GlobalTheory.ThetaUnfold.schA_continuous D.host.F hΦ).comp
      (continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i)
  have hhbd : ∃ B : ℝ, ∀ x : κ → AF D.host.F, Summable (fun η : κ → D.host.F =>
      ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖) ∧
      ∑' η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ ≤ B := by
    refine ⟨B, fun x => ?_⟩
    have hj : Function.Injective fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F) := by
      intro η η' e
      funext i
      exact congrFun e (Sum.inl i)
    have key : ∀ η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ =
        ((fun ξ : κ ⊕ κ → D.host.F => ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim x x)‖) ∘
          fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F)) η := by
      intro η
      simp only [hhdef, Function.comp_apply]
      congr 2
      funext i
      rcases i with i | i <;> rfl
    simp_rw [key]
    exact ⟨(hsumΦ _).comp_injective hj,
      (tsum_comp_le_tsum_of_inj (hsumΦ _) (fun _ => norm_nonneg _) hj).trans (hB _)⟩
  have hinner : ∀ x, ∫ y in 𝓕₁, G (x, y) ∂μ = (μ.real 𝓕₁ : ℂ) *
      ∑' η : κ → D.host.F, h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x) := by
    intro x
    exact GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal D.host.F ψ hψc κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ x
  calc GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)
      = ∫ w in 𝓕, G (co.e w) ∂ν := by
        unfold GlobalTheory.DiagSiegel.thetaDiagInt
        simp_rw [hdiag]
    _ = ∫ p in 𝓖, G p ∂lam := htr G
    _ = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := hiter G hGm hGper hGbd
    _ = c₁ * ((μ.real 𝓕₁ : ℂ) * ∫ u, h u ∂μ) := by
        simp_rw [hinner]
        rw [integral_const_mul, GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates D.host.F κ μ hμ 𝓕₁ h𝓕₁ htop h hcont hhbd]
    _ = ((c₁ * μ.real 𝓕₁ : ℝ) : ℂ) * GlobalTheory.DiagSiegel.diagInt μ Φ := by
        push_cast
        rw [mul_assoc]
        rfl

end GlobalTheory.DiagSiegelUnfold

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalThetaIntegral_eq_nonzero_mul_diagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagSiegelUnfold.diag_theta_integral | exact GlobalTheory.DiagSiegelUnfold.diag_theta_integral | (intros; apply GlobalTheory.DiagSiegelUnfold.diag_theta_integral <;> assumption)
end
