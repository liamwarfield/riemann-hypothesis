module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceAdeleRingNumberField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceBis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalizedHaarPairAtFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalizedHaarPairAtFinitePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem normAt_exists : ∀ (D : D7) (V : HSp D) (R : Subgroup (GA D V)), IsClosed (R : Set (GA D V)) → ∀ (L : Lat V),
    IsSelfDualC V L → ∀ Q : Finset (Pl D), ∃ ρ μ, IsNormAt V R L (· ∈ Q) ρ μ := by
  intro D V R hR L hL Q
  obtain ⟨⟨K, hK, hKc, hKo⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q).2.2.2.2.2.2.2.2.1 L hL (· ∈ Q)
  have hKG : ∀ g : GA D V, g ∈ K → g ∈ grpAt V (· ∈ Q) := fun g hg => ((hK g).1 hg).1
  have h1 : InK V L (· ∈ Q) 1 := (hK 1).1 K.one_mem

  let S : Set (grpAt V (· ∈ Q)) := {g | InK V L (· ∈ Q) g.1}
  have hSe : S = ((K.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) := by
    ext g; simp [S, Subgroup.mem_subgroupOf, hK]
  have hSo : IsOpen S := hSe ▸ hKo
  have hSc : IsCompact S := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert hKc using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact (hK _).2 hg
    · intro hx; exact ⟨⟨x, hKG x hx⟩, (hK x).1 hx, rfl⟩

  let T := R.subgroupOf (grpAt V (· ∈ Q))
  let S' : Set T := {g | InK V L (· ∈ Q) g.1.1}
  have hS'o : IsOpen S' := hSo.preimage continuous_subtype_val
  have hS'c : IsCompact S' := by
    rw [(Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isCompact_iff]
    convert hKc.inter_right hR using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨(hK _).2 hg, Subgroup.mem_subgroupOf.1 g.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨⟨x, hKG x hx⟩, Subgroup.mem_subgroupOf.2 hxR⟩, (hK x).1 hx, rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts (grpAt V (· ∈ Q)) :=
    ⟨⟨S, hSc⟩, by rw [hSo.interior_eq]; exact ⟨1, h1⟩⟩
  let K₁ : TopologicalSpace.PositiveCompacts T :=
    ⟨⟨S', hS'c⟩, by rw [hS'o.interior_eq]; exact ⟨1, h1⟩⟩
  refine ⟨Measure.haarMeasure K₁, Measure.haarMeasure K₀, inferInstance, inferInstance, ?_, ?_⟩
  · exact Measure.haarMeasure_self (K₀ := K₀)
  · exact Measure.haarMeasure_self (K₀ := K₁)

end GlobalTheory.SeeSaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalizedHaarPairAtFinitePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalizedHaarPair_at_finitePlaces : ∀ (D : D7) (V : HSp D) (R : Subgroup (GA D V)), IsClosed (R : Set (GA D V)) → ∀ (L : Lat V), IsSelfDualC V L → ∀ Q : Finset (Pl D), ∃ ρ μ, IsNormAt V R L (· ∈ Q) ρ μ := by
  first | exact @GlobalTheory.SeeSaw.normAt_exists | exact GlobalTheory.SeeSaw.normAt_exists | (intros; apply GlobalTheory.SeeSaw.normAt_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFlatMapIndepUnfoldingStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_flatMap_indep_unfoldingStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s s' : StepBF ψ B J) f, IsThetaFunO ψ B.V J.W f → flatBF s f = flatBF s' f) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s s' : StepFB ψ J B) f, IsThetaFunO ψ J.W B.V f → flatFB s f = flatFB s' f := by
  first | exact @GlobalTheory.FlatIndep.flat_indep | exact GlobalTheory.FlatIndep.flat_indep | (intros; apply GlobalTheory.FlatIndep.flat_indep <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegrandVacuumFormBasePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegrandVacuumFormBasePoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.VMove


set_option maxHeartbeats 4000000 in
theorem seeSaw_iteratedIntegrand_vacuumForm_base_points_alt : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∀ (φ : t.Ch j → GA D (c.X j) → ℂ) (F : GA D (c.V (j + 1 + 1)) → ℂ) Ψ₁ Ψ₂ f z, Ψ₁ = v.Ψ j P₁ 1 a → Ψ₂ = v.Ψ (j + 1) P₂ a a' → f = rTrans (a' * v.b (j + 1 + 1)) F → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => t.integrand j σ h P₁ P₂ φ F (a * q₁.1) (a' * q₂.1)) (w.sc j * w.sc (j + 1) * z) := by
  intro D c v t w hc hv ht hw j σ h P₁ P₂ a ha a' ha' φ F Ψ₁ Ψ₂ f z hΨ₁ hΨ₂ hf hI
  classical
  obtain ⟨-, -, hcomm₁, -, hright₁, -⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨-, -, hcomm₂, -, hright₂, -⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  have hj₁ : j + 1 < D.R.m := by omega
  have hj₂ : j + 1 + 1 < D.R.m := by omega

  have key : ∀ p₁ ∈ GfC (c.V (j + 1)), ∀ p₂ ∈ GfC (c.V (j + 1 + 1)),
      t.integrand j σ h P₁ P₂ φ F (a * (p₁ * v.b (j + 1))) (a' * (p₂ * v.b (j + 1 + 1))) =
        w.sc j * w.sc (j + 1) * ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
            (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
            (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g p₁ p₂) (rTrans p₂ f) := by
    intro p₁ hp₁ p₂ hp₂
    have ec₁ : a * (p₁ * v.b (j + 1)) = p₁ * (a * v.b (j + 1)) := by
      rw [← mul_assoc, hcomm₁ a ha p₁ hp₁, mul_assoc]
    have ec₂ : a' * (p₂ * v.b (j + 1 + 1)) = p₂ * (a' * v.b (j + 1 + 1)) := by
      rw [← mul_assoc, hcomm₂ a' ha' p₂ hp₂, mul_assoc]
    have er : rTrans (a' * (p₂ * v.b (j + 1 + 1))) F = rTrans p₂ f := by
      rw [hf, ec₂]; funext x; simp only [rTrans, mul_assoc]
    unfold Tup.integrand
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [(hw.e j α).1, Finsupp.mapDomain_support_of_injective (mul_left_injective (v.b j)),
      Finset.sum_image (fun x _ y _ hxy => mul_right_cancel hxy), Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finsupp.mapDomain_apply_of_injective (mul_left_injective (v.b j))]
    have e₁ : (t.sBF j (σ + 1) h).om (g * v.b j, a * (p₁ * v.b (j + 1))) (t.pt j P₁) =
        w.sc j • (t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
      rw [(ht.sBF j (σ + 1) h).1, ec₁,
        show ((g * v.b j, p₁ * (a * v.b (j + 1))) : GA D (c.V j) × GA D (c.V (j + 1))) =
          (g, p₁) * (1 * v.b j, a * v.b (j + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf j hj₁ P₁ 1 (one_mem _) a ha, map_smul, hΨ₁]
    have e₂ : (t.sFB j σ h).om (a * (p₁ * v.b (j + 1)), a' * (p₂ * v.b (j + 1 + 1))) (t.pt (j + 1) P₂) =
        w.sc (j + 1) • (t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
      rw [(ht.sFB j σ h).1, ec₁, ec₂,
        show ((p₁ * (a * v.b (j + 1)), p₂ * (a' * v.b (j + 1 + 1))) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) =
          (p₁, p₂) * (a * v.b (j + 1), a' * v.b (j + 1 + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf (j + 1) hj₂ P₂ a ha a' ha', map_smul, hΨ₂]
    have hh := (GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)).1
    simp only [Chain.hand]
    rw [e₁, e₂, hh, er]
    have hp := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (w.sc j * w.sc (j + 1)) 1
      (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α)
        (flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)))))
        (flatFB (t.sFB j σ h) ((t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)))))
      (rTrans p₂ f)
    rw [one_smul] at hp
    rw [hp]
    ring
  obtain ⟨f₁, h1, h2⟩ := hI
  haveI := hright₁ _ (hc.μf (j + 1))
  haveI := hright₂ _ (hc.μf (j + 1 + 1))
  set B₁ : GfC (c.V (j + 1)) := ⟨v.b (j + 1), hv.b (j + 1)⟩ with hB₁
  set B₂ : GfC (c.V (j + 1 + 1)) := ⟨v.b (j + 1 + 1), hv.b (j + 1 + 1)⟩ with hB₂
  refine ⟨fun q => (w.sc j * w.sc (j + 1)) * f₁ (q * B₁⁻¹), ?_, fun q => ?_⟩
  · exact (h1.mul_right B₁⁻¹).smul (w.sc j * w.sc (j + 1))
  · have := ((h2 (q * B₁⁻¹)).mul_right B₂⁻¹).smul (w.sc j * w.sc (j + 1))
    convert this using 1
    funext q₂
    have eq₁ : (q : GA D (c.V (j + 1))) = ((q * B₁⁻¹ : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) * v.b (j + 1) := by
      simp [hB₁]
    have eq₂ : (q₂ : GA D (c.V (j + 1 + 1))) =
        ((q₂ * B₂⁻¹ : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) * v.b (j + 1 + 1) := by
      simp [hB₂]
    rw [Pi.smul_apply, smul_eq_mul]
    beta_reduce
    rw [eq₁, eq₂]
    exact key _ (q * B₁⁻¹).2 _ (q₂ * B₂⁻¹).2

end GlobalTheory.VMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegrandVacuumFormBasePointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_iteratedIntegrand_vacuumForm_base_points : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∀ (φ : t.Ch j → GA D (c.X j) → ℂ) (F : GA D (c.V (j + 1 + 1)) → ℂ) Ψ₁ Ψ₂ f z, Ψ₁ = v.Ψ j P₁ 1 a → Ψ₂ = v.Ψ (j + 1) P₂ a a' → f = rTrans (a' * v.b (j + 1 + 1)) F → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => t.integrand j σ h P₁ P₂ φ F (a * q₁.1) (a' * q₂.1)) (w.sc j * w.sc (j + 1) * z) := by
  first | exact @GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt | exact GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt | (intros; apply GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValFin

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun _ _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => by simp only [Pi.zero_apply]; exact contDiff_const⟩

theorem isLatVac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) :
    IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩

theorem isReal_zero (c : Comm D) (j : ℕ) : c.IsReal j 0 := by
  refine ⟨⟨continuous_const, fun v => ⟨isThetaFunO_zero _ _ _, isLatVac_zero _ _ _ _⟩,
    fun u => ⟨isThetaFunO_zero _ _ _, isLatVac_zero _ _ _ _⟩⟩, ?_⟩
  intro n L L' _ _ _ _ u v
  simp only [Pi.zero_apply]
  exact contDiff_const

theorem isAutFun_rTrans {V : HSp D} (x : GA D V) {φ : GA D V → ℂ} (h : IsAutFun V φ) :
    IsAutFun V (rTrans x φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  refine ⟨fun γ hγ g => ?_, ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩, ?_⟩
  · simp only [rTrans, mul_assoc]; exact h.left γ hγ (g * x)
  · have hc : Continuous fun k : GA D V => x⁻¹ * k * x := by fun_prop
    exact hU.preimage hc
  · have hk' : x⁻¹ * k * x ∈ U := by simpa [MulAut.conj_apply] using hk
    have hf : x⁻¹ * k * x ∈ GfC V := by
      unfold GfC at hkf ⊢
      rw [MonoidHom.mem_ker] at hkf ⊢
      simp [hkf]
    have e : g * k * x = g * x * (x⁻¹ * k * x) := by group
    simp only [rTrans]
    rw [e, hUφ _ hk' hf]
  · exact h.cont.comp (continuous_mul_const x)

theorem trc_mapDomain {V : HSp D} (ε : GA D V →₀ ℂ) (b : GA D V) (f : GA D V → ℂ) :
    trc (ε.mapDomain (· * b)) f = trc ε (rTrans b f) := by
  unfold trc
  change (ε.mapDomain (· * b)).sum (fun g c => c • rTrans g f) = ε.sum (fun g c => c • rTrans g (rTrans b f))
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  funext z
  simp [rTrans, mul_assoc]

end GlobalTheory.ValFin

namespace GlobalTheory.ValFin

variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (Q : Pl D → Prop) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT Q f := by
  have key := (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hstd S T Q (fun p => ¬ Q p) (fun p hp hn => hn hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => Q p ∨ ¬ Q p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  rw [e] at key
  exact (key.1 hf).1

theorem ctr_indep (c : Comm D) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (s₁ s₁' : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h))
    (s₂ s₂' : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ)
    (h₁ : IsThetaFunO c.ψ _ _ Ψ₁) (h₂ : IsThetaFunO c.ψ _ _ Ψ₂) :
    c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂ = c.ctr j σ h s₁' s₂' Ψ₁ Ψ₂ := by
  unfold Comm.ctr
  rw [(GlobalTheory.T.theta_flatMap_indep_unfoldingStep D c.ψ).1 _ _ _ s₁ s₁' Ψ₁ h₁, (GlobalTheory.T.theta_flatMap_indep_unfoldingStep D c.ψ).2 _ _ _ s₂ s₂' Ψ₂ h₂]

theorem valX : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → v.Is →
    (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → ContrLaw D → FlatLaw D → BiAct D → ValX t := by
  intro D c v 𝒯 t w hc hv ht hL hContr hFlat hBi
  intro j σ h P₁ P₂ a ha a' ha'
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  have hV₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (v.Ψ j P₁ 1 a) :=
    hv.Ψ j hj1 P₁ 1 (one_mem _) a ha
  have hV₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) (v.Ψ (j + 1) P₂ a a') :=
    hv.Ψ (j + 1) hj2 P₂ a ha a' ha'
  by_cases hT : Nonempty 𝒯
  swap
  · exact ⟨0, isReal_zero c j, fun s => (hT ⟨s⟩).elim⟩
  obtain ⟨s₀⟩ := hT
  refine ⟨(v.op j).app c.ψ (c.ctr j σ h ((t s₀).sBF j (σ + 1) h) ((t s₀).sFB j σ h) (v.Ψ j P₁ 1 a) (v.Ψ (j + 1) P₂ a a')),
    ((GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction D c v (t s₀) (w s₀) hc hv (ht s₀) (hL s₀).vac (hL s₀).tl hFlat).1 j σ h _ _ hV₁ hV₂).2, ?_⟩
  intro s ψ hψ y G x
  have hLs := hL s
  have hF := hLs.form
  have hj2m : j + 2 ≤ D.R.m := by omega
  have hφR : ∀ α, (t s).rd j α ψ y ∈ v.RamAd j := fun α => (hF.rd j hj2m ψ hψ α y).1
  have hφX : ∀ α, (t s).rd j α ψ y ∈ (w s).FX j α := fun α => (hF.rd j hj2m ψ hψ α y).2.1
  have hφS : ∀ α, (t s).rd j α ((t s).S j ψ) y = v.Sad j ((t s).rd j α ψ y) := fun α => (hF.rd j hj2m ψ hψ α y).2.2
  have hφA : ∀ α, IsContAut _ ((t s).rd j α ψ y) := fun α => (hv.ram j _ (hφR α)).1
  have hFaut : IsAutFun _ (G.1 x) := by
    obtain ⟨J, χ, hJ⟩ := (ht s).CC (j + 1 + 1) hj2
    exact (GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp c.θ (c.M (j + 1 + 1)) J χ G.1 (hJ G.2) x).1.toIsAutFun
  have hfaut : IsAutFun _ (rTrans (a' * v.b (j + 1 + 1)) (G.1 x)) := isAutFun_rTrans _ hFaut
  have hfY : rTrans (a' * v.b (j + 1 + 1)) (G.1 x) ∈ (w s).FY (j + 1 + 1) := (hF.row (j + 1 + 1) hj2 G x a' ha').1
  obtain ⟨ρ₁, μ₁, hn₁⟩ := GlobalTheory.T.exists_normalizedHaarPair_at_finitePlaces D (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (GlobalTheory.jacGrp_isClosed _ _ _ _ _)
    (v.N (j + 1)) (hv.sd (j + 1) hj1) (w s).Q
  obtain ⟨ρ₂, μ₂, hn₂⟩ := GlobalTheory.T.exists_normalizedHaarPair_at_finitePlaces D (c.V (j + 1 + 1))
    (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
    (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) (v.N (j + 1 + 1)) (hv.sd (j + 1 + 1) hj2) (w s).Q
  have hdisj : ∀ p, p ∈ v.gP → ¬ p ∈ (w s).Q := fun p hp hq => Finset.disjoint_left.mp hF.disjG hq hp
  have K₁ := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (· ∈ (w s).Q) hdisj
  have K₂ := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V (j + 1)) (c.V (j + 1 + 1)) (· ∈ v.gP) (· ∈ (w s).Q) hdisj
  have hVQ₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ (w s).Q) (comb c.ψ _ _ (v.eG j) (v.Ψ j P₁ 1 a)) :=
    (K₁.2.1 (v.eG j) (hv.atG j).1).2 _ _ _
      (vac_of_all hc.std (hv.sd j (by omega)) (hv.sd (j + 1) hj1) _ hV₁)
  have hVQ₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ (w s).Q) (comb c.ψ _ _ (v.eG (j + 1)) (v.Ψ (j + 1) P₂ a a')) :=
    (K₂.2.1 (v.eG (j + 1)) (hv.atG (j + 1)).1).2 _ _ _
      (vac_of_all hc.std (hv.sd (j + 1) hj1) (hv.sd (j + 1 + 1) hj2) _ hV₂)
  have hQ := hLs.ql j σ h ρ₁ μ₁ ρ₂ μ₂ hn₁ hn₂ _ _ hVQ₁ hVQ₂ (fun α => (t s).rd j α ψ y)
    (fun α => ⟨hφA α, hφX α⟩) _ hfaut hfY
  have hc₁ := K₁.1 (v.eG j) ((w s).eQ j) (hv.atG j).1 (hF.atQ j).1 (v.Ψ j P₁ 1 a)
  have hc₂ := K₂.1 (v.eG (j + 1)) ((w s).eQ (j + 1)) (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 (v.Ψ (j + 1) P₂ a a')
  rw [← hc₁, ← hc₂] at hQ
  have hcell := GlobalTheory.T.seeSawDoubleStep_finiteIntegral_collapse_twistPlaces D c v (t s) (w s) hc hv (ht s) hF hLs.weil hLs.off hLs.gs hLs.qfin hContr hFlat j σ h
    ρ₁ μ₁ ρ₂ μ₂ hn₁ hn₂ _ _ hV₁ hV₂ (fun α => (t s).rd j α ψ y) hφR G x a' ha' _ rfl _ hQ
  have hmove := GlobalTheory.T.seeSaw_iteratedIntegrand_vacuumForm_base_points D c v (t s) (w s) hc hv (ht s) hF j σ h P₁ P₂ a ha a' ha' (fun α => (t s).rd j α ψ y)
    (G.1 x) _ _ _ _ rfl rfl rfl hcell
  convert hmove using 1
  have hrhs := GlobalTheory.T.seeSaw_unfoldedData_eq_kernelData_at_level D c v (t s) (w s) hc hv (ht s) hF hLs.gv hLs.tl hFlat hBi j σ h _ _ hV₁ hV₂
    (fun α => (t s).rd j α ψ y) hφR
  have hct := ctr_indep c j σ h ((t s).sBF j (σ + 1) h) ((t s₀).sBF j (σ + 1) h) ((t s).sFB j σ h) ((t s₀).sFB j σ h)
    _ _ hV₁.1 hV₂.1
  rw [hct] at hrhs
  beta_reduce at hrhs
  have hper : ∀ (k : ℂ) φ' f', (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (k • φ') f' =
      k * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ φ' f' := by
    intro k φ' f'
    have := (GlobalTheory.HandHom.hand_hom D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      ((t s).sBF j (σ + 1) h) ((t s).sFB j σ h) (c.lnk j σ h) (c.vL j σ h) 0).2.2 k 1 φ' f'
    rwa [one_smul, mul_one] at this
  have htwo : (fun α => (t s).rd j α ((t s).S j ψ) y) = fun α => v.Sad j ((t s).rd j α ψ y) := funext hφS
  have hcomm : v.b (j + 1 + 1) * a' = a' * v.b (j + 1 + 1) :=
    GlobalTheory.FinTranslate.comm_fin_real _ (hv.b (j + 1 + 1)) ha'
  have htrc : ∀ β, trc ((t s).e (j + 1 + 1) β) (rTrans a' (G.1 x)) =
      trc ((w s).ε (j + 1 + 1) β) (rTrans (a' * v.b (j + 1 + 1)) (G.1 x)) := by
    intro β
    rw [(hF.e (j + 1 + 1) β).1, trc_mapDomain]
    congr 1
    funext g
    simp [rTrans, mul_assoc, hcomm]
  rw [hLs.cv.1 j σ h]
  unfold Tup.perF
  rw [htwo]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hrhs β, hper, htrc β]
  ring

end GlobalTheory.ValFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → ContrLaw D → FlatLaw D → BiAct D → ValX t := by
  first | exact @GlobalTheory.ValFin.valX | exact GlobalTheory.ValFin.valX | (intros; apply GlobalTheory.ValFin.valX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstCells

variable {D : D7}

theorem latO_mono' (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : latO S T LS LT Q ≤ latO S T LS LT P := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hvan, rest⟩
  exact ⟨α, hα, fun v hv => hvan v fun hq => hv (h v hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (h : ∀ v, Q v → P v) : Vac ψ S T LS LT Q f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono' S T _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono' S T _ _ h hu) hh⟩

theorem theta_smul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi γ w]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w)) }

theorem vac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    (c : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (c • f) := by
  have e : ∀ u, heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
    intro u; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  exact ⟨theta_smul' c hf.1, fun u hu => by rw [e, hf.2.1 u hu], fun e' he u hu hh => by rw [e, hf.2.2 e' he u hu hh]⟩

theorem comb_smul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem mem_cong {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem real_le_off (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, mem_cong]
  intro i j
  have h2 : finPart D (Formalism.L2.Theta.mt V a i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) ha
  rw [idOff, Ideal.mem_iInf]
  intro w
  rw [RingHom.mem_ker, GlobalTheory.FinPl.compAt, RingHom.comp_apply, RingHom.map_sub, h2]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self, RingHom.map_zero]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero, sub_self, RingHom.map_zero]

theorem grpOff_inf_le (V : HSp D) (P P' : Pl D → Prop) :
    grpOff V P ⊓ grpOff V P' ≤ grpOff V (fun p => P p ∨ P' p) := by
  intro g hg
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  rw [grpOff, mem_cong] at h1 h2 ⊢
  intro i j
  have a1 := h1 i j
  have a2 := h2 i j
  rw [idOff, Ideal.mem_iInf] at a1 a2 ⊢
  rintro ⟨w, hw | hw⟩
  · exact a1 ⟨w, hw⟩
  · exact a2 ⟨w, hw⟩

theorem exists_level (D : D7) (V : HSp D) (N : Lat V) (A B : Finset (Pl D)) (JA JB : Subgroup (GA D V)) (b : GA D V)
    (hAB : Disjoint B A) (hN : IsSelfDualC V N) (hb : b ∈ GfC V) (hA : JA ≤ grpAt V (· ∈ A)) (hAc : IsCompact (JA : Set (GA D V)))
    (hAo : IsOpen ((JA.subgroupOf (grpAt V (· ∈ A)) : Subgroup _) : Set (grpAt V (· ∈ A)))) (hB : JB ≤ grpAt V (· ∈ B))
    (hBc : IsCompact (JB : Set (GA D V)))
    (hBo : IsOpen ((JB.subgroupOf (grpAt V (· ∈ B)) : Subgroup _) : Set (grpAt V (· ∈ B)))) :
    ∃ K : Subgroup (GA D V), K ≤ GfC V ∧ IsCompact (K : Set (GA D V)) ∧
      IsOpen ((K.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) ∧
      ∀ k, k ∈ K ↔ ∃ κ x y, InK V N (fun p => p ∉ A ∧ p ∉ B) κ ∧ x ∈ JA ∧ y ∈ JB ∧ k = b⁻¹ * (κ * x * y) * b := by
  first
  | exact @_root_.GlobalTheory.CompactOpenIntegers.exists_level
  | exact _root_.GlobalTheory.CompactOpenIntegers.exists_level
  | (apply _root_.GlobalTheory.CompactOpenIntegers.exists_level <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompactOpenIntegers.exists_level <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompactOpenIntegers.exists_level <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompactOpenIntegers.exists_level ..)

theorem split_off (D : D7) (V : HSp D) (A B : Finset (Pl D)) (hAB : Disjoint B A) (z : GA D V)
    (hz : z ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B)) :
    ∃ a ∈ GinfC V, ∃ x ∈ grpAt V (· ∈ A), ∃ y ∈ grpAt V (· ∈ B), z = a * y * x := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨-, -, hf1, hf2, -, ⟨e', he'⟩, hO, hI, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V B
  have h1 := he (e.symm z)
  rw [e.apply_symm_apply] at h1
  have h2 := he' (e'.symm (e.symm z).2)
  rw [e'.apply_symm_apply] at h2
  generalize e'.symm (e.symm z).2 = p at h2
  generalize e.symm z = q at h1 h2
  obtain ⟨⟨y, hy⟩, ⟨x, hx⟩⟩ := p
  obtain ⟨⟨a, ha⟩, ⟨f, hf⟩⟩ := q
  dsimp only at h1 h2
  subst h2
  refine ⟨a, ha, x, ?_, y, hy, by rw [h1, mul_assoc]⟩
  have hxo : x ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B) := by
    have : x = y⁻¹ * (a⁻¹ * z) := by rw [h1]; group
    rw [this]
    exact mul_mem (inv_mem (hO _ _ (fun p hp h => h.2 hp) hy)) (mul_mem (inv_mem (real_le_off V _ ha)) hz)
  have hxB : x ∈ grpOff V (· ∈ B) := hO _ _ (fun p hp h => hp h) hx
  have hx' : x ∈ GfC V ⊓ grpOff V (fun p => (p ∉ A ∧ p ∉ B) ∨ p ∈ B) :=
    ⟨hf2 hx, grpOff_inf_le V _ _ ⟨hxo, hxB⟩⟩
  rw [hI] at hx'
  have hP : (fun p => ¬ ((p ∉ A ∧ p ∉ B) ∨ p ∈ B)) = (· ∈ A) := by
    funext p
    have := fun h : p ∈ B => Finset.disjoint_left.1 hAB h
    apply propext
    tauto
  rwa [hP] at hx'

theorem comm_at (D : D7) (V : HSp D) (A B : Finset (Pl D)) (hAB : Disjoint B A) {x y : GA D V} (hx : x ∈ grpAt V (· ∈ A))
    (hy : y ∈ grpAt V (· ∈ B)) : y * x = x * y := by
  obtain ⟨-, -, -, -, hcm, -, hO, hI, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V B
  refine hcm y hy x ?_
  have hx' : x ∈ GfC V ⊓ grpOff V (· ∈ B) :=
    ⟨(GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V A).2.2.1 hx, hO _ _ (fun p hp h => Finset.disjoint_left.1 hAB h hp) hx⟩
  rwa [hI] at hx'


set_option maxHeartbeats 800000 in
theorem locFin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → OffLaw v w → GSupp (t := t) v → QFin v w → t.LocFin := by
  classical
  intro D c v t w hc hv ht hF hO hG hQ j σ h P₁ P₂
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  obtain ⟨KQ, TQ, hKQ, hKQc, hKQo, hTQ, hKQlaw, hTQsupp⟩ := hQ j σ h
  obtain ⟨hJG, hJGc, hJGo⟩ := hv.JG (j + 1) hj1
  obtain ⟨K, hKf, hKc, hKo, hKmem⟩ := exists_level D (c.V (j + 1)) (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) KQ
    (v.b (j + 1)) hF.disjG (hv.sd (j + 1) hj1) (hv.b (j + 1)) hJG hJGc hJGo hKQ hKQc hKQo
  have hone : InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) 1 := ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩

  have VGQ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) w.Q
  have VGG := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) v.gP
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp hg => Finset.disjoint_left.1 hF.disjG hp hg
  have hGQ : ∀ p, p ∈ v.gP → ¬ p ∈ w.Q := fun p hg hp => hQG p hp hg
  have hQoff : ∀ p, p ∈ w.Q → ¬ offP v w p := fun p hp h' => h'.2 hp
  have hGoff : ∀ p, p ∈ v.gP → ¬ offP v w p := fun p hp h' => h'.1 hp
  have hoffQ : ∀ p, offP v w p → ¬ p ∈ w.Q := fun p h' => h'.2
  have hoffG : ∀ p, offP v w p → ¬ p ∈ v.gP := fun p h' => h'.1
  have hQf : grpAt (c.V (j + 1)) (· ∈ w.Q) ≤ GfC _ := VGQ.2.2.1
  have hGf : grpAt (c.V (j + 1)) (· ∈ v.gP) ≤ GfC _ := VGG.2.2.1
  have gO : ∀ (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → grpAt (c.V (j + 1)) P ≤ grpOff (c.V (j + 1)) P' :=
    VGQ.2.2.2.2.2.2.1

  have W1 := (t.sBF j (σ + 1) h).weil
  rw [(ht.sBF j (σ + 1) h).1] at W1
  have W2 := (t.sFB j σ h).weil
  rw [(ht.sFB j σ h).1] at W2

  have hΨ1 := hv.Ψ j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
  have hΨ2 := hv.Ψ (j + 1) hj2 P₂ 1 (one_mem _) 1 (one_mem _)
  have VC1 := fun P P' hPP' => GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) P P' hPP'
  have VC2 := fun P P' hPP' => GlobalTheory.DisjComb.main D c.ψ hc.std (c.V (j + 1)) (c.V (j + 1 + 1)) P P' hPP'
  obtain ⟨hG1, -, -⟩ := hv.atG j
  obtain ⟨hG2, -, -⟩ := hv.atG (j + 1)
  obtain ⟨hQ1, -, -⟩ := hF.atQ j
  obtain ⟨hQ2, -, -⟩ := hF.atQ (j + 1)
  refine ⟨K, TQ.image (· * v.b (j + 1)), hKf, hKc, hKo, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 hq
    exact mul_mem (hQf (hTQ q' hq')) (hv.b (j + 1))
  · intro k hk
    obtain ⟨κ, x, y, hκ, hx, hy, rfl⟩ := (hKmem k).1 hk
    obtain ⟨ax, hax, hx1, hx2, -⟩ := hF.lawG j hj1 x hx
    obtain ⟨ay, hay, hyl⟩ := hKQlaw y hy
    have hΨ1Q := vac_mono (Q := (· ∈ w.Q)) hΨ1 fun _ _ => trivial
    have hΨ2Q := vac_mono (Q := (· ∈ w.Q)) hΨ2 fun _ _ => trivial
    have hΨ1G := vac_mono (Q := (· ∈ v.gP)) hΨ1 fun _ _ => trivial
    have hΨ2G := vac_mono (Q := (· ∈ v.gP)) hΨ2 fun _ _ => trivial
    have hΨ1O := vac_mono (Q := offP v w) hΨ1 fun _ _ => trivial
    have hΨ2O := vac_mono (Q := offP v w) hΨ2 fun _ _ => trivial
    obtain ⟨hy1, hy2⟩ := hyl _ _ hΨ1Q hΨ2Q
    have hκG : κ ∈ grpOff _ (· ∈ v.gP) := gO _ _ hoffG hκ.1
    have hκQ : κ ∈ grpOff _ (· ∈ w.Q) := gO _ _ hoffQ hκ.1
    have hyG : y ∈ grpOff _ (· ∈ v.gP) := gO _ _ hQG (hKQ hy)
    have hθ1 : IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1)) :=
      (((VC1 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ1).2 _ _ _ hΨ1G).1
    have hθ2 : IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1)) :=
      (((VC2 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ2).2 _ _ _ hΨ2G).1
    have hV1 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1)) :=
      ((VC1 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ1).2 _ _ _ hΨ1G
    have hV2 : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1)) :=
      ((VC2 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ2).2 _ _ _ hΨ2G
    have hO1 := hO j σ h _ _ hΨ1O hΨ2O

    have L1 : t.om j (1, κ * x * y) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1))) =
        (ax * ay)⁻¹ • comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1)) := by
      have e : ((1 : GA D (c.V j)), κ * x * y) = (1, κ) * (1, x) * (1, y) := by simp
      rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      rw [(VC1 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hG1 1 (one_mem _) y hyG _ hθ1, hy1,
        comb_smul', map_smul, hx1 _ hV1, map_smul, map_smul, smul_smul,
        (VC1 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hG1 1 (one_mem _) κ hκG _ hθ1,
        (VC1 (· ∈ w.Q) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hQ1 1 (one_mem _) κ hκQ _ hΨ1.1,
        ((hO1.1 κ hκ).1), mul_inv, mul_comm]
    have L2 : t.om (j + 1) (κ * x * y, 1) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1))) =
        (ax * ay) • comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1)) := by
      have e : (κ * x * y, (1 : GA D (c.V (j + 1 + 1)))) = (κ, 1) * (x, 1) * (y, 1) := by simp
      rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      rw [(VC2 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W2 _ hG2 y hyG 1 (one_mem _) _ hθ2, hy2,
        comb_smul', map_smul, hx2 hj2 _ hV2, map_smul, map_smul, smul_smul,
        (VC2 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W2 _ hG2 κ hκG 1 (one_mem _) _ hθ2,
        (VC2 (· ∈ w.Q) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W2 _ hQ2 κ hκQ 1 (one_mem _) _ hΨ2.1,
        ((hO1.1 κ hκ).2), mul_comm]

    have vf1 := hF.vf j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
    have vf2 := hF.vf (j + 1) hj2 P₂ 1 (one_mem _) 1 (one_mem _)
    simp only [one_mul] at vf1 vf2
    have pt1 : t.pt j P₁ = t.om j ((v.b j)⁻¹, (v.b (j + 1))⁻¹) (w.sc j • comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1))) := by
      rw [← vf1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk,
        map_one, Module.End.one_apply]
    have pt2 : t.pt (j + 1) P₂ = t.om (j + 1) ((v.b (j + 1))⁻¹, (v.b (j + 1 + 1))⁻¹)
        (w.sc (j + 1) • comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1))) := by
      rw [← vf2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk,
        map_one, Module.End.one_apply]
    refine ⟨ax * ay, mul_ne_zero hax hay, ?_, ?_⟩
    · rw [pt1, ← Module.End.mul_apply, ← map_mul]
      have e : ((1 : GA D (c.V j)), (v.b (j + 1))⁻¹ * (κ * x * y) * v.b (j + 1)) * ((v.b j)⁻¹, (v.b (j + 1))⁻¹) =
          ((v.b j)⁻¹, (v.b (j + 1))⁻¹) * (1, κ * x * y) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_assoc, mul_inv_cancel]
      rw [e, map_mul, Module.End.mul_apply, map_smul, L1, smul_comm, map_smul]
    · rw [pt2, ← Module.End.mul_apply, ← map_mul]
      have e : ((v.b (j + 1))⁻¹ * (κ * x * y) * v.b (j + 1), (1 : GA D (c.V (j + 1 + 1)))) *
          ((v.b (j + 1))⁻¹, (v.b (j + 1 + 1))⁻¹) = ((v.b (j + 1))⁻¹, (v.b (j + 1 + 1))⁻¹) * (κ * x * y, 1) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_assoc, mul_inv_cancel]
      rw [e, map_mul, Module.End.mul_apply, map_smul, L2, smul_comm, map_smul]
  · intro α g hg h₁ hne
    obtain ⟨he, heQ⟩ := hF.e j α
    rw [he] at hg
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    obtain ⟨-, -, hrf, -⟩ := GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1))
    have gO0 : ∀ (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → grpAt (c.V j) P ≤ grpOff (c.V j) P' :=
      (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) w.Q).2.2.2.2.2.2.1
    have hεG : ε ∈ grpOff _ (· ∈ v.gP) := gO0 _ _ hQG (heQ ε hε)
    have hεO : ε ∈ grpOff _ (offP v w) := gO0 _ _ hQoff (heQ ε hε)
    have omm : ∀ (a a' : GA D (c.V j)) (b b' : GA D (c.V (j + 1))) f, t.om j (a, b) (t.om j (a', b') f) = t.om j (a * a', b * b') f :=
      fun a a' b b' f => by rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

    have vf1 := hF.vf j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
    rw [one_mul, one_mul, ← comb_smul', ← comb_smul'] at vf1
    have hΨ := vac_smul (w.sc j) hΨ1
    generalize w.sc j • v.Ψ j P₁ 1 1 = Ψ at vf1 hΨ
    obtain ⟨x, rfl⟩ : ∃ x, h₁ = x * v.b (j + 1) := ⟨h₁ * (v.b (j + 1))⁻¹, by group⟩
    rw [← omm, vf1] at hne
    have hΨQ := vac_mono (Q := (· ∈ w.Q)) hΨ fun _ _ => trivial
    have hΨG := vac_mono (Q := (· ∈ v.gP)) hΨ fun _ _ => trivial
    have hΨO := vac_mono (Q := offP v w) hΨ fun _ _ => trivial
    have hΨ2G := vac_mono (Q := (· ∈ v.gP)) hΨ2 fun _ _ => trivial
    have hΨ2O := vac_mono (Q := offP v w) hΨ2 fun _ _ => trivial
    have hVG : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb c.ψ _ _ (w.eQ j) Ψ) :=
      ((VC1 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ1).2 _ _ _ hΨG
    have hVQ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) (comb c.ψ _ _ (v.eG j) Ψ) :=
      ((VC1 (· ∈ v.gP) (· ∈ w.Q) hGQ).2.1 _ hG1).2 _ _ _ hΨQ
    have hVO : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) :=
      ((VC1 (· ∈ v.gP) (offP v w) hGoff).2.1 _ hG1).2 _ _ _ (((VC1 (· ∈ w.Q) (offP v w) hQoff).2.1 _ hQ1).2 _ _ _ hΨO)

    obtain ⟨r, hr, hrO, z, hz, κ, hκ, rfl⟩ := (hO j σ h _ _ (GlobalTheory.OffPlaceWeil.vac_off W1 hVO hεO (one_mem _)) hΨ2O).2.2.1 x
      (by rwa [omm, one_mul, mul_one])
    have hfix := ((hO j σ h _ _ hVO hΨ2O).1 κ hκ).1
    have hne2 : flatBF (t.sBF j (σ + 1) h) (t.om j (ε, z) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ))) ≠ 0 := by
      intro h0
      have hR := (GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant D c.ψ (offP v w)).1 (σ + 1) _ _ (t.sBF j (σ + 1) h) _ (W1.om_pres (ε, z) _ hVO.1) r hr hrO
      rw [(ht.sBF j (σ + 1) h).1] at hR
      apply hne
      have e := hR.2 h0
      have e' : t.om j (ε, r * z * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) =
          t.om j (1, r) (t.om j (ε, z) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ))) := by
        conv_rhs => rw [← hfix]
        rw [omm, omm, one_mul, mul_one]
      rw [e']
      exact e
    obtain ⟨a, ha, xG, hxG, xQ, hxQ, rfl⟩ := split_off D _ v.gP w.Q hF.disjG z hz
    have cQG : ∀ {x y}, x ∈ grpAt (c.V (j + 1)) (· ∈ v.gP) → y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q) → y * x = x * y :=
      fun hx hy => comm_at D _ v.gP w.Q hF.disjG hx hy

    have haQ : a * xQ ∈ grpOff _ (· ∈ v.gP) := mul_mem (real_le_off _ _ ha) (gO _ _ hQG hxQ)
    obtain ⟨rG, hrG, hrGa, kG, hkG, hxG'⟩ := (hG j σ h _ _ (GlobalTheory.OffPlaceWeil.vac_off W1 hVG hεG haQ) hΨ2G).1 xG hxG (by
      rw [← (VC1 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hG1 ε hεG _ haQ _ hVG.1, omm, one_mul,
        ← mul_assoc, ← hrf a ha xG (hGf hxG), mul_assoc, ← cQG hxG hxQ, ← mul_assoc]
      exact hne2)

    have haG : a * xG ∈ grpOff _ (· ∈ w.Q) := mul_mem (real_le_off _ _ ha) (gO _ _ hGQ hxG)
    obtain ⟨rQ, hrQ, hrQa, q, hq, kQ, hkQ, hxQ'⟩ := hTQsupp _ (GlobalTheory.OffPlaceWeil.vac_off W1 hVQ (one_mem _) haG) α ε hε xQ hxQ (by
      rw [← (VC1 (· ∈ w.Q) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hQ1 1 (one_mem _) _ haG _ hVQ.1, omm, mul_one,
        ← mul_assoc, ← hrf a ha xQ (hQf hxQ), ← (VC1 (· ∈ v.gP) (· ∈ w.Q) hGQ).1 _ _ hG1 hQ1]
      exact hne2)
    refine ⟨q * v.b (j + 1), Finset.mem_image_of_mem _ hq, r * rG * rQ, mul_mem (mul_mem hr hrG) hrQ, a, ha,
      (v.b (j + 1))⁻¹ * (kG * kQ * κ) * v.b (j + 1), ?_, ?_⟩
    · have m1 := (hKmem _).2 ⟨1, kG, kQ, hone, hkG, hkQ, rfl⟩
      have m2 := (hKmem _).2 ⟨κ, 1, 1, hκ, one_mem _, one_mem _, rfl⟩
      have m3 := mul_mem m1 m2
      have e : (v.b (j + 1))⁻¹ * (kG * kQ * κ) * v.b (j + 1) = (v.b (j + 1))⁻¹ * (1 * kG * kQ) * v.b (j + 1) *
          ((v.b (j + 1))⁻¹ * (κ * 1 * 1) * v.b (j + 1)) := by
        simp only [mul_assoc, mul_inv_cancel_left, one_mul, mul_one]
      rw [e]
      exact m3
    · have c1 : a * (rQ * q * kQ) * (rG * kG) = rG * rQ * a * q * (kG * kQ) := by
        rw [← hxQ', mul_assoc a xQ, ← mul_assoc xQ, cQG hrGa hxQ, ← mul_assoc a, ← mul_assoc a, hrf a ha rG (hGf hrGa), hxQ',
          ← cQG (hJG hkG) (hKQ hkQ), mul_assoc rG rQ a, ← hrf a ha rQ (hQf hrQa)]
        simp only [mul_assoc]
      rw [hxG', hxQ', c1]
      simp only [mul_assoc, mul_inv_cancel_left]

end GlobalTheory.FirstCells
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_finite_of_tuple_conditions : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → OffLaw v w → GSupp (t := t) v → QFin v w → t.LocFin := by
  first | exact @GlobalTheory.FirstCells.locFin | exact GlobalTheory.FirstCells.locFin | (intros; apply GlobalTheory.FirstCells.locFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawPlaceLawsGiveFiniteIntegralLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem placeLaws_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c)
    (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) →
    (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v 𝒯 t w hc hvl hv ht hp
  refine ⟨fun s => ?_, ?_, ?_⟩
  · exact GlobalTheory.T.locally_finite_of_tuple_conditions D c v (t s) (w s) hc hv (ht s) (hp s).form (hp s).off (hp s).gs (hp s).qfin
  · exact GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value D c v 𝒯 t w hc hv ht hp (GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)
  · exact GlobalTheory.T.seeSawLastTwoSteps_doubleLiftPeriod_value D c v 𝒯 t w hc hvl hv ht hp (GlobalTheory.Unf.LastSteps.lastLaw D) (GlobalTheory.T.lastSeeSaw_thetaIdentity D)
      (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)

end GlobalTheory.SeeSaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawPlaceLawsGiveFiniteIntegralLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_place_laws_give_finite_integral_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  first | exact @GlobalTheory.SeeSaw.placeLaws_finiteIntegrals | exact GlobalTheory.SeeSaw.placeLaws_finiteIntegrals | (intros; apply GlobalTheory.SeeSaw.placeLaws_finiteIntegrals <;> assumption)
end
