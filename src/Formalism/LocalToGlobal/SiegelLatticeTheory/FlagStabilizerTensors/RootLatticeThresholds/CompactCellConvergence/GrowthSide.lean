module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
public import Formalism.PeriodIntegrals.GoodTwo
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProper5OfSteps
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

def PolyProper5 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
      (∀ σ ∈ Sg k r z z' γ, ∀ s' ∈ Sset k r z',
        B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2)) ∧
      (∀ s ∈ Sset k r z, ∀ σ' ∈ Sg' k r z z' γ,
        B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (5 * (r + 1) ^ 2))

theorem polyProper5_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper5 := by
  intro k r z z' γ hstd hpos hmono
  obtain ⟨CA, hA1, hA2⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩
  · intro σ hσ s' hs'
    obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
    obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
    have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
    obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu
  · intro s hs σ' hσ'
    obtain ⟨hsG, u, hu, hsf⟩ := hS k r z hstd.2.1 s hs
    obtain ⟨hσG, v', hv', hPv, hσf⟩ := hSg' k r z z' γ hstd σ' hσ'
    have hg : s⁻¹ * γ * σ' ∈ B.GV k r := hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ s σ' u v' hsG hσG hsf hσf
    obtain ⟨hbu, hbv⟩ := hA2 u hu v' hv' hPv _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv

theorem polyProper5 : PolyProper5 :=
  polyProper5_of_steps gvGroup normInv gnFacts fmulBound zhatMove
    (frameS_of Formalism.FourierDecayAlt.P.unipotent_map_frame gvGroup)
    (frameSg_of Formalism.FourierDecayAlt.P.unipotent_map_frame (tauMem_of mxFacts TauN.neFacts) gvGroup)
    (frameSg'_of Formalism.FourierDecayAlt.P.unipotent_map_frame (tauMem_of mxFacts TauN.neFacts) gvGroup)
    (unitriangular_inverse_bound second_order_norm_bound)
    (coreInst_of isoCore hpkInvol gnFacts frameInd)

end PI.PolynomialProperness
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.PairMajInv
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.EtEquiv
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.ClosedExistsOfCompact
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.FlagStabClosed
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.OrbitIdentity
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.PairMeasBad
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.MsetOfClosed
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem uh_isUnit {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hdet k r
  have h := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h
  exact hH.ne_zero h.symm

theorem n_sub {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Nset k r) :
    g ∈ UH (Hpk k r) := hg.1

def Good (L : LocBessel k r) (x : PairSp k r) : Prop :=
  Matrix.of x.1.2 ∈ Nset k r ∧ Matrix.of x.2.2 ∈ Nset k r ∧ Matrix.of x.1.1 ∈ UWset k r L.z ∧
    Matrix.of x.2.1 ∈ UWset k r L.z'

theorem nset_closed : IsClosed (Nset k r) := by
  have hU : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        g i (eI k r a) = if i = eI k r a then 1 else 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have h3 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        g i j = if i = j then 1 else 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  exact hU.inter (h2.inter h3)

theorem uw_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have hU : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h3 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact hU.inter (h2.inter h3)

theorem mset_of_closed {s : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} (hs : IsClosed s) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ s} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  exact (hs.preimage hc).measurableSet

theorem good_mset (L : LocBessel k r) : MeasurableSet {x : PairSp k r | Good L x} := by
  have h1 := mset_of_closed (nset_closed (k := k) (r := r))
  have h2 := mset_of_closed (uw_closed (k := k) (r := r) L.z)
  have h3 := mset_of_closed (uw_closed (k := k) (r := r) L.z')
  exact (h1.preimage measurable_fst.snd).inter ((h1.preimage measurable_snd.snd).inter
    ((h2.preimage measurable_fst.fst).inter (h3.preimage measurable_snd.fst)))

theorem good_stabAct (L : LocBessel k r) {γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (x : PairSp k r) : Good L (stabAct γ a x) ↔ Good L x := by
  have hmul : ∀ b ∈ Nset k r, ∀ m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      b * m ∈ Nset k r ↔ m ∈ Nset k r := by
    intro b hb m
    refine ⟨fun h => ?_, fun h => Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hb h⟩
    have hu := uh_isUnit (n_sub hb)
    have := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hb) h
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
  show (a * Matrix.of x.1.2 ∈ Nset k r ∧ γ⁻¹ * a * γ * Matrix.of x.2.2 ∈ Nset k r ∧
      Matrix.of x.1.1 ∈ UWset k r L.z ∧ Matrix.of x.2.1 ∈ UWset k r L.z') ↔ Good L x
  rw [hmul a ha.1, hmul _ ha.2]
  rfl

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem sfin_muN (L : LocBessel k r) : SFinite L.μN := by
  exact Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _

theorem pairMeas_bad (L : LocBessel k r) : pairMeas L {x | ¬ Good L x} = 0 := by
  haveI : SFinite L.μN := sfin_muN L
  haveI : SigmaFinite L.μW := L.hμW.1.1
  haveI : SigmaFinite L.μW' := L.hμW'.1.1
  have hN : L.μN {x | Matrix.of x ∉ Nset k r} = 0 := by
    obtain ⟨c, -, hform⟩ := Formalism.MainNotions.BridgeCSB.haarLie_N_eq (k := k) (r := r)
    have h1 := (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top).2.2.1
    rw [hform, one_smul] at h1
    rw [LocBessel.μN, hform, Measure.smul_apply, h1, smul_zero]
  have hW : L.μW {x | Matrix.of x ∉ UWset k r L.z} = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' {x | Matrix.of x ∉ UWset k r L.z'} = 0 := L.hμW'.1.2.2.1
  have hsub : {x : PairSp k r | ¬ Good L x} ⊆
      ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r}) ×ˢ Set.univ ∪
        Set.univ ×ˢ (Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r})) ∪
      (({x | Matrix.of x ∉ UWset k r L.z} ×ˢ Set.univ) ×ˢ Set.univ ∪
        Set.univ ×ˢ ({x | Matrix.of x ∉ UWset k r L.z'} ×ˢ Set.univ)) := by
    intro x hx
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and, and_true]
    by_contra hc
    push_neg at hc
    exact hx (by unfold Good; exact ⟨hc.1.1, hc.1.2, hc.2.1, hc.2.2⟩)
  refine measure_mono_null hsub ?_
  unfold pairMeas
  refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>
    simp only [Measure.prod_prod, hN, hW, hW', mul_zero, zero_mul]

theorem nu_bad (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} (hR0 : μR ≠ 0) (hRc : μR {x | Matrix.of x ∉ RStab k r γ} = 0)
    {ν : Measure (PairSp k r)} (hQ : IsOrbQuot L γ μR ν) : ν {x | ¬ Good L x} = 0 := by
  have hm : MeasurableSet {x : PairSp k r | ¬ Good L x} := (good_mset L).compl
  have h := hQ ({x : PairSp k r | ¬ Good L x}.indicator 1) (measurable_one.indicator hm)
  rw [lintegral_indicator_one hm, pairMeas_bad] at h
  have hin : ∀ x, ∫⁻ a, {x : PairSp k r | ¬ Good L x}.indicator 1 (stabAct γ (Matrix.of a) x) ∂μR =
      μR Set.univ * {x : PairSp k r | ¬ Good L x}.indicator 1 x := by
    intro x
    have hst : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := by
      rw [ae_iff]
      exact hRc
    have hae : ∀ᵐ a ∂μR, {x : PairSp k r | ¬ Good L x}.indicator (1 : PairSp k r → ℝ≥0∞)
        (stabAct γ (Matrix.of a) x) = {x : PairSp k r | ¬ Good L x}.indicator 1 x := by
      filter_upwards [hst] with a ha
      classical
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, good_stabAct L ha x]
    rw [lintegral_congr_ae hae, lintegral_const, mul_comm]
  simp_rw [hin] at h
  rw [lintegral_const_mul _ (measurable_one.indicator hm), lintegral_indicator_one hm] at h
  have hR : μR Set.univ ≠ 0 := by rwa [Ne, Measure.measure_univ_eq_zero]
  exact (mul_eq_zero.1 h.symm).resolve_left hR

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem rmulF_meas (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) ρ) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Formalism.FourierDecayAlt.B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  first
  | exact (measurable_pi_iff.mp (measurable_pi_apply i) l).mul measurable_const
  | fun_prop

theorem orbit_identity (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} (hR : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μR)
    (hRc : μR {x | Matrix.of x ∉ RStab k r γ} = 0) (hR0 : μR ≠ 0)
    {ν : Measure (PairSp k r)} (hQ : IsOrbQuot L γ μR ν)
    (F : PairSp k r → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ x, Good L x → ∀ a ∈ RStab k r γ, F (stabAct γ a x) = F x)
    (E : Set (Mt k r)) (hE : MeasurableSet E) (A : Set (Mt k r)) (hA : MeasurableSet A)
    (ρh : Mt k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hρ : ∀ n : Mt k r, Matrix.of n ∈ Nset k r → ρh n ∈ RStab k r γ ∧
      ∀ a : Mt k r, Matrix.of a ∈ RStab k r γ →
        ((fun i j => (Matrix.of a * Matrix.of n) i j : Mt k r) ∈ E ↔ Formalism.FourierDecayAlt.B.rmulF (ρh n) a ∈ A)) :
    ∫⁻ x, F x * E.indicator (1 : Mt k r → ℝ≥0∞) x.1.2 ∂(pairMeas L) = μR A * ∫⁻ x, F x ∂ν := by
  have hfst : Measurable (fun x : PairSp k r => x.1.2) := measurable_snd.comp measurable_fst
  have hf : Measurable (fun x : PairSp k r => F x * E.indicator (1 : Mt k r → ℝ≥0∞) x.1.2) :=
    hF.mul ((measurable_one.indicator hE).comp hfst)
  rw [hQ _ hf, ← lintegral_const_mul _ hF]
  have hgood : ∀ᵐ x ∂ν, Good L x := by
    rw [ae_iff]
    exact nu_bad L hR0 hRc hQ
  have hstab : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := by
    rw [ae_iff]
    simpa using hRc
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with x hx
  obtain ⟨hρn, hiff⟩ := hρ x.1.2 hx.1
  have hmr : Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) (ρh x.1.2)) := rmulF_meas _
  have hin : ∀ᵐ a ∂μR, F (stabAct γ (Matrix.of a) x) *
      E.indicator (1 : Mt k r → ℝ≥0∞) (stabAct γ (Matrix.of a) x).1.2 =
      F x * ((Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) (ρh x.1.2)) ⁻¹' A).indicator 1 a := by
    filter_upwards [hstab] with a ha
    rw [hFinv x hx _ ha]
    congr 1
    have h1 := hiff a ha
    show E.indicator (1 : Mt k r → ℝ≥0∞) (fun i j => (Matrix.of a * Matrix.of x.1.2) i j) = _
    by_cases hA' : Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) (ρh x.1.2) a ∈ A
    · simp only [Set.indicator_of_mem (h1.mpr hA'), Set.indicator_of_mem (show a ∈ _ ⁻¹' A from hA'),
        Pi.one_apply]
    · simp only [Set.indicator_of_notMem (fun h => hA' (h1.mp h)),
        Set.indicator_of_notMem (show a ∉ _ ⁻¹' A from hA')]
  rw [lintegral_congr_ae hin, lintegral_const_mul _ ((measurable_one.indicator (hmr hA))),
    lintegral_indicator_one (hmr hA), ← Measure.map_apply hmr hA, hR.right _ hρn, mul_comm]

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem ltset_closed (m : ℕ) : IsClosed (LTset m) := by
  have h1 : IsClosed {l : Matrix (Fin m) (Fin m) ℂ | ∀ i j, i < j → l i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have h2 : IsClosed {l : Matrix (Fin m) (Fin m) ℂ | ∀ i, l i i = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
  exact h1.inter h2

theorem lpg_closed {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : IsClosed (LPg P) := by
  have hc : Continuous (fun l : Matrix (Fin m) (Fin m) ℂ => P⁻¹ * l * P) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (ltset_closed m).inter ((ltset_closed m).preimage hc)

theorem flagStab_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (FlagStab k r z) := by
  have hG : IsClosed (Formalism.FourierDecayAlt.B.GV k r) := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).closed
  have hF : IsClosed {s : Formalism.FourierDecayAlt.B.Mat k r |
      ∀ a, s *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional (flagSpan k r z a)).preimage
      ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  exact hG.inter hF

theorem sset_closed (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) : IsClosed (Sset k r z) := by
  rw [← Formalism.FourierDecayAlt.P.standard_flag_property k r z hz]
  exact flagStab_closed z

theorem uMap_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (uMap k r z) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold uMap herm
  split_ifs
  · exact continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))
  · exact (continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))).div_const _

def SgS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {s | s ∈ Sset k r z ∧ (uMap k r z s)ᴴ ∈ LPg (Formalism.QuantumDeterminants.Zhat k r z z' γ)}

theorem sgS_closed (z z' : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : IsClosed (SgS k r z z' γ) :=
  (sset_closed z hz).inter ((lpg_closed _).preimage ((uMap_cont z).matrix_conjTranspose))

theorem n_in_sset (z : Fin (2 * r + k + 1) → ℂ) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨WeylGroupFacts.uh_one, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem uw_in_sset (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩

theorem sg_eq (z z' : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Sg k r z z' γ = SgS k r z z' γ := by
  have hU := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hT := Formalism.FourierDecayAlt.P.c2_tau_mem k r z hz
  have hSG := Formalism.QuantumDeterminants.symmetric_group_holds k r z hz.1
  ext s
  constructor
  · rintro ⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩
    obtain ⟨hτN, -, hτu⟩ := hT v hv
    have h1 : n0 ∈ Sset k r z := n_in_sset z hn0.1
    have h2 : tauM k r z v ∈ Sset k r z := n_in_sset z hτN
    have h3 : h ∈ Sset k r z := uw_in_sset z hh
    refine ⟨hSG.2.1 _ (hSG.2.1 _ h1 _ h2) _ h3, ?_⟩
    rw [(hU.1 _ (hSG.2.1 _ h1 _ h2)).2.2 _ h3, (hU.1 _ h1).2.2 _ h2, hn0.2, hτu, hU.2 h hh]
    simpa using hvL
  · rintro ⟨hs, hsL⟩
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    have hhU : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
    have hn : h * m * h⁻¹ ∈ Nset k r := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz.1 h hh m hm).1
    set v := uMap k r z (h * m) with hvdef
    have hS : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
    have hv : v ∈ UTset (r + 1) := (hU.1 _ hS).2.1
    obtain ⟨hτN, -, hτu⟩ := hT v hv
    have hτU : IsUnit (tauM k r z v).det := WeylGroupFacts.isUnit_of_uh hτN.1
    have hτi : (tauM k r z v)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hτN
    have hn0 : h * m * h⁻¹ * (tauM k r z v)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_mul hn hτi
    have hmul : ∀ a ∈ Sset k r z, ∀ b ∈ Sset k r z, uMap k r z (a * b) = uMap k r z a * uMap k r z b :=
      fun a ha b hb => (hU.1 a ha).2.2 b hb
    have hsplit : h * m = h * m * h⁻¹ * h := by
      rw [Matrix.mul_assoc (h * m), Matrix.nonsing_inv_mul _ hhU, Matrix.mul_one]
    have hun : uMap k r z (h * m * h⁻¹) = v := by
      have := hmul _ (n_in_sset z hn) _ (uw_in_sset z hh)
      rw [← hsplit, hU.2 h hh, Matrix.mul_one] at this
      exact this.symm
    have hone : uMap k r z 1 = 1 := hU.2 1 ⟨WeylGroupFacts.uh_one, fun a => by simp, by simp⟩
    have huinv : uMap k r z (h * m * h⁻¹ * (tauM k r z v)⁻¹) = 1 := by
      have e1 := hmul _ (n_in_sset z hn) _ (n_in_sset z hτi)
      have e2 := hmul _ (n_in_sset z hτN) _ (n_in_sset z hτi)
      rw [Matrix.mul_nonsing_inv _ hτU, hone, hτu] at e2
      rw [e1, hun]; exact e2.symm
    refine ⟨_, ⟨hn0, huinv⟩, v, hv, by simpa using hsL, h, hh, ?_⟩
    rw [Matrix.mul_assoc (h * m * h⁻¹), Matrix.nonsing_inv_mul _ hτU, Matrix.mul_one, ← hsplit]

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem entry_le_gN (y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    ‖y i j‖ ≤ Formalism.FourierDecayAlt.B.gN y := by
  unfold Formalism.FourierDecayAlt.B.gN
  rw [← Real.sqrt_sq (norm_nonneg (y i j)), Complex.sq_norm]
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (y i j) ≤ ∑ j', Complex.normSq (y i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (y i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (y i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (y i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

def AT (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (T : ℝ) : Set (Mt k r) :=
  {y | Matrix.of y ∈ RStab k r γ ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of y) ≤ T}

theorem rstab_closed {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) :
    IsClosed {y : Mt k r | Matrix.of y ∈ RStab k r γ} :=
  (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) (uh_isUnit hγ)).closed

theorem at_compact {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (T : ℝ) :
    IsCompact (AT (k := k) (r := r) γ T) := by
  have hc : IsClosed (AT (k := k) (r := r) γ T) :=
    (rstab_closed hγ).inter (isClosed_le Formalism.FourierDecayAlt.P.s3dx1S_gNc continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hc ?_
  refine (Metric.isBounded_closedBall (x := (0 : Mt k r)) (r := max T 0)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2
    fun j => le_trans (entry_le_gN (Matrix.of y) i j) (le_trans hy.2 (le_max_left _ _))

theorem at_mset {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (T : ℝ) :
    MeasurableSet (AT (k := k) (r := r) γ T) := (at_compact hγ T).isClosed.measurableSet

def ET (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (T : ℝ) :
    Set (Mt k r) :=
  {m | ∃ y ∈ AT (k := k) (r := r) γ T, Hpk k r * (Matrix.of y)ᴴ * Hpk k r * Matrix.of m ∈ SgS k r z z' γ}

theorem closed_exists_of_compact {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {K : Set X} (hK : IsCompact K) (Φ : X × Y → Z) (hΦ : Continuous Φ) {S : Set Z}
    (hS : IsClosed S) : IsClosed {m : Y | ∃ y ∈ K, Φ (y, m) ∈ S} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × Y => Φ ((p.1 : X), p.2)) :=
    hΦ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hC : IsClosed {p : K × Y | Φ ((p.1 : X), p.2) ∈ S} := hS.preimage hc
  have himg : {m : Y | ∃ y ∈ K, Φ (y, m) ∈ S} = Prod.snd '' {p : K × Y | Φ ((p.1 : X), p.2) ∈ S} := by
    ext m; constructor
    · rintro ⟨y, hy, hm⟩; exact ⟨(⟨y, hy⟩, m), hm, rfl⟩
    · rintro ⟨⟨⟨y, hy⟩, m'⟩, hm, rfl⟩; exact ⟨y, hy, hm⟩
  rw [himg]
  exact isClosedMap_snd_of_compactSpace _ hC

theorem et_closed (z z' : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (T : ℝ) :
    IsClosed (ET (k := k) (r := r) z z' γ T) := by
  have hcont : Continuous (fun p : Mt k r × Mt k r =>
      Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r * Matrix.of p.2) :=
    ((continuous_const.matrix_mul (PI.WUN.continuous_of.comp continuous_fst).matrix_conjTranspose).matrix_mul
      continuous_const).matrix_mul (PI.WUN.continuous_of.comp continuous_snd)
  exact closed_exists_of_compact (at_compact hγ T) _ hcont (sgS_closed z z' hz γ)

theorem uh_inv_eq {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ UH (Hpk k r)) :
    Hpk k r * ρᴴ * Hpk k r = ρ⁻¹ := by
  have h1 : Hpk k r * ρᴴ * Hpk k r * ρ = 1 := by
    have : ρᴴ * Hpk k r * ρ = Hpk k r := hρ
    rw [Matrix.mul_assoc (Hpk k r * ρᴴ), Matrix.mul_assoc, ← Matrix.mul_assoc ρᴴ, this, WeylGroupFacts.hpk_sq]
  exact (Matrix.inv_eq_left_inv h1).symm

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem rst_iff {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hstd : Std k r z z') (hpos : PosPt k r z z' γ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : g ∈ Rst k r z z' γ ↔ g ∈ RStab k r γ := by
  have hγu : IsUnit γ.det := uh_isUnit hpos.1
  rw [(Formalism.FourierDecayAlt.P.stabilizer_split k r z z' γ hstd hpos).2.1]
  constructor
  · rintro ⟨hg, n, hn, rfl⟩
    refine ⟨hg, ?_⟩
    have : γ⁻¹ * (γ * n * γ⁻¹) * γ = n := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγu, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hγu, Matrix.one_mul]
    rw [this]; exact hn
  · rintro ⟨hg, hg'⟩
    refine ⟨hg, _, hg', ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul]

theorem et_equiv (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hstd : Std k r L.z L.z') (hpos : PosPt k r L.z L.z' γ) (hmono : IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ)) (T : ℝ) :
    ∃ ρh : Mt k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, ∀ n : Mt k r,
      Matrix.of n ∈ Nset k r → ρh n ∈ RStab k r γ ∧
      ∀ a : Mt k r, Matrix.of a ∈ RStab k r γ →
        ((fun i j => (Matrix.of a * Matrix.of n) i j : Mt k r) ∈ ET (k := k) (r := r) L.z L.z' γ T ↔
          Formalism.FourierDecayAlt.B.rmulF (ρh n) a ∈ AT (k := k) (r := r) γ T) := by
  classical
  have hSD := Formalism.FourierDecayAlt.P.c2_section_decomp k r L.z L.z' γ hstd hpos hmono
  have hRg := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) (uh_isUnit hpos.1)
  let ρh : Mt k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun n =>
    if h : Matrix.of n ∈ Sset k r L.z then (hSD (Matrix.of n) h).exists.choose.1 else 1
  refine ⟨ρh, fun n hn => ?_⟩
  have hnS : Matrix.of n ∈ Sset k r L.z := n_in_sset L.z hn
  have hspec := (hSD (Matrix.of n) hnS).exists.choose_spec
  have hρdef : ρh n = (hSD (Matrix.of n) hnS).exists.choose.1 := dif_pos hnS
  set ρ0 := (hSD (Matrix.of n) hnS).exists.choose.1 with hρ0
  set σ0 := (hSD (Matrix.of n) hnS).exists.choose.2 with hσ0
  have hρ0R : ρ0 ∈ RStab k r γ := (rst_iff hstd hpos ρ0).1 hspec.1
  have hσ0 : σ0 ∈ Sg k r L.z L.z' γ := hspec.2.1
  have hn0 : Matrix.of n = ρ0 * σ0 := hspec.2.2
  rw [hρdef]
  refine ⟨hρ0R, fun a ha => ?_⟩
  have haU : IsUnit (Matrix.of a).det := uh_isUnit ha.1.1
  have hρU : IsUnit ρ0.det := uh_isUnit hρ0R.1.1
  have haρ : Matrix.of a * ρ0 ∈ RStab k r γ := hRg.mul_mem _ ha _ hρ0R
  have hanS : Matrix.of a * Matrix.of n ∈ Sset k r L.z := n_in_sset L.z (WeylGroupFacts.mem_n_mul ha.1 hn)
  have hsg := sg_eq (k := k) (r := r) L.z L.z' hstd.2.1 γ
  constructor
  · rintro ⟨y, hy, hΦ⟩
    have hyU : Matrix.of y ∈ UH (Hpk k r) := hy.1.1.1
    rw [uh_inv_eq hyU] at hΦ
    have hΦ' : (Matrix.of y)⁻¹ * (Matrix.of a * Matrix.of n) ∈ Sg k r L.z L.z' γ := by rw [hsg]; exact hΦ
    have hyu : IsUnit (Matrix.of y).det := uh_isUnit hyU
    have e1 : Matrix.of a * Matrix.of n = Matrix.of y * ((Matrix.of y)⁻¹ * (Matrix.of a * Matrix.of n)) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mul]
    have e2 : Matrix.of a * Matrix.of n = (Matrix.of a * ρ0) * σ0 := by rw [hn0, Matrix.mul_assoc]
    have huniq := (hSD _ hanS).unique
      (y₁ := (Matrix.of y, (Matrix.of y)⁻¹ * (Matrix.of a * Matrix.of n)))
      (y₂ := (Matrix.of a * ρ0, σ0))
      ⟨(rst_iff hstd hpos _).2 hy.1, hΦ', e1⟩ ⟨(rst_iff hstd hpos _).2 haρ, hσ0, e2⟩
    have hyeq : Matrix.of y = Matrix.of a * ρ0 := congrArg Prod.fst huniq
    have : Formalism.FourierDecayAlt.B.rmulF ρ0 a = y := by
      show (Matrix.of a * ρ0 : Matrix _ _ ℂ) = Matrix.of y
      rw [hyeq]
    rw [this]; exact hy
  · intro hy
    refine ⟨_, hy, ?_⟩
    have hyM : Matrix.of (Formalism.FourierDecayAlt.B.rmulF ρ0 a) = Matrix.of a * ρ0 := rfl
    rw [hyM, uh_inv_eq haρ.1.1, ← hsg, Matrix.mul_inv_rev]
    show ρ0⁻¹ * (Matrix.of a)⁻¹ * (Matrix.of a * Matrix.of n) ∈ Sg k r L.z L.z' γ
    have : ρ0⁻¹ * (Matrix.of a)⁻¹ * (Matrix.of a * Matrix.of n) = σ0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of a)⁻¹, Matrix.nonsing_inv_mul _ haU, Matrix.one_mul,
        hn0, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρU, Matrix.one_mul]
    rw [this]; exact hσ0

theorem at_pos {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)}
    (hR0 : μR ≠ 0) (hRc : μR {x | Matrix.of x ∉ RStab k r γ} = 0) : ∃ T : ℕ, μR (AT (k := k) (r := r) γ T) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hU : μR {x : Mt k r | Matrix.of x ∈ RStab k r γ} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (measure_iUnion_null hcon)
    obtain ⟨T, hT⟩ := exists_nat_ge (Formalism.FourierDecayAlt.B.gN (Matrix.of y))
    exact Set.mem_iUnion.2 ⟨T, hy, hT⟩
  have : μR Set.univ = 0 := by
    refine measure_mono_null (fun y _ => ?_) (measure_union_null hU hRc)
    by_cases h : Matrix.of y ∈ RStab k r γ
    · exact Or.inl h
    · exact Or.inr h
  exact hR0 (Measure.measure_univ_eq_zero.mp this)

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.KeyBound
noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

theorem key_bound {X Y M K b : ℝ} {E : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hM : 1 ≤ M) (hK : 0 < K) (hE : 0 < E)
    (hb : 0 ≤ b) (h : X + Y ≤ K * M ^ E) :
    M ^ (-b) ≤ K ^ (b / E) * (X ^ (-(b / (2 * E))) * Y ^ (-(b / (2 * E)))) := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hs0 : 0 ≤ b / E := div_nonneg hb hE'.le
  have hc : b / (2 * E) = b / E / 2 := by ring
  rw [hc]
  have hXY0 : 0 < X * Y := by nlinarith
  have hsq : Real.sqrt (X * Y) ≤ K * M ^ E := by
    have h1 : Real.sqrt (X * Y) ≤ X + Y := by
      rw [show X + Y = Real.sqrt ((X + Y) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hpow : (X * Y) ^ (b / E / 2) ≤ K ^ (b / E) * M ^ b := by
    rw [show b / E / 2 = (1 / 2) * (b / E) by ring, Real.rpow_mul hXY0.le, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (X * Y) ^ (b / E) ≤ (K * M ^ E) ^ (b / E) :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) hsq hs0
      _ = K ^ (b / E) * M ^ b := by
        rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith)]
        congr 2
        field_simp
  have hA : 0 < (X * Y) ^ (b / E / 2) := Real.rpow_pos_of_pos hXY0 _
  have hM0 : 0 < M ^ b := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith), Real.rpow_neg (by linarith),
    ← mul_inv, ← Real.mul_rpow (by linarith) (by linarith), ← div_eq_mul_inv,
    le_div_iff₀ hA, inv_mul_le_iff₀ hM0]
  linarith

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem pairMaj_inv (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) (b : ℝ) {x : PairSp k r} (hx : Good L x)
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ RStab k r γ) :
    Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b (stabAct γ a x) = Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b x := by
  have hg : IsUnit γ.det := PIQnLT.isUnit_det_of_UH γ hγ
  have ha' : IsUnit a.det := PIQnLT.isUnit_det_of_UH a ha.1.1
  have key : (Matrix.of x.1.1)⁻¹ * (a * Matrix.of x.1.2)⁻¹ * γ * (γ⁻¹ * a * γ * Matrix.of x.2.2) * Matrix.of x.2.1
      = (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1 := by
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hg,
      Matrix.nonsing_inv_mul_cancel_left _ _ ha']
  unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj stabAct
  exact congrArg (fun M => Formalism.FourierDecayAlt.B.gN M ^ (-b)) key

theorem pair_bound (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hstd : Std k r L.z L.z') (hpos : PosPt k r L.z L.z' γ) (hmono : IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ))
    (T : ℝ) (hT : 1 ≤ T) (b : ℝ) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : PairSp k r, Good L x → x.1.2 ∈ ET (k := k) (r := r) L.z L.z' γ T →
      Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b x ≤
        K * (Formalism.FourierDecayAlt.B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ^ (-(b / (2 * (5 * (r + 1) ^ 2 : ℕ)))) *
          Formalism.FourierDecayAlt.B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-(b / (2 * (5 * (r + 1) ^ 2 : ℕ))))) := by
  classical
  have hγ : γ ∈ UH (Hpk k r) := hpos.1
  have hγu : IsUnit γ.det := PIQnLT.isUnit_det_of_UH γ hγ
  obtain ⟨C, hC1, -⟩ := PI.PolynomialProperness.polyProper5 k r L.z L.z' γ hstd hpos hmono
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have gnn : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, 0 ≤ Formalism.FourierDecayAlt.B.gN g :=
    fun g => (PI.PolynomialProperness.gnFacts k r).1 g
  have gmul : ∀ g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Formalism.FourierDecayAlt.B.gN (g * h) ≤ Formalism.FourierDecayAlt.B.gN g * Formalism.FourierDecayAlt.B.gN h :=
    fun g h => PI.PolynomialProperness.GN.gN_mul_le g h
  have c1nn : 0 ≤ Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ :=
    mul_nonneg (mul_nonneg (gnn _) hT0) (gnn _)
  have hKc : (0 : ℝ) < max ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) 1 :=
    lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) 1) ^
      (b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ)), Real.rpow_pos_of_pos hKc _, ?_⟩
  intro x hx hET
  obtain ⟨y, ⟨⟨hyN, hyN'⟩, hyT⟩, hyS⟩ := hET
  obtain ⟨hP12, hP22, hP11, hP21⟩ := hx
  have hyU : Matrix.of y ∈ UH (Hpk k r) := hyN.1
  have hyu : IsUnit (Matrix.of y).det := PIQnLT.isUnit_det_of_UH _ hyU
  rw [uh_inv_eq hyU, ← sg_eq L.z L.z' hstd.2.1 γ] at hyS
  have hσ : (Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1 ∈ Sg k r L.z L.z' γ := by
    obtain ⟨n0, hn0, v, hv, hv', h, hh, he⟩ := hyS
    exact ⟨n0, hn0, v, hv, hv', h * Matrix.of x.1.1, Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul hh hP11,
      by rw [he]; simp only [Matrix.mul_assoc]⟩
  have hmN : γ⁻¹ * Matrix.of y * γ ∈ Nset k r := hyN'
  have hP21u : IsUnit (Matrix.of x.2.1).det := PIQnLT.isUnit_det_of_UH _ hP21.1
  have hs : (γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1 ∈ Sset k r L.z' := by
    have hmn : (γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 ∈ Nset k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN) hP22
    have hw := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hP21
    refine ⟨Matrix.of x.2.1, hP21,
      (Matrix.of x.2.1)⁻¹ * ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2) * Matrix.of x.2.1, ?_, ?_⟩
    · rw [Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff]
      refine ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hw.1 hmn.1) hP21.1, ?_⟩
      exact Formalism.QuantumDeterminants.WeylGroupFacts.conj_col (Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hw) (Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hP21)
        (Matrix.nonsing_inv_mul _ hP21u) ((Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).1 hmn).2
    · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP21u]
  have hb1 := hC1 _ hσ _ hs
  have hmu : IsUnit (γ⁻¹ * Matrix.of y * γ).det := PIQnLT.isUnit_det_of_UH _ hmN.1
  have hMeq : (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1 =
      ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1)⁻¹ * γ *
        ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hγu,
      Matrix.nonsing_inv_nonsing_inv _ hyu, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hγu, Matrix.mul_nonsing_inv_cancel_left _ _ hyu]
  have hX : Formalism.FourierDecayAlt.B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ≤
      T * Formalism.FourierDecayAlt.B.gN ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) := by
    have e : Matrix.of x.1.2 * Matrix.of x.1.1 =
        Matrix.of y * ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hyu]
    rw [e]
    exact le_trans (gmul _ _) (mul_le_mul_of_nonneg_right hyT (gnn _))
  have hY : Formalism.FourierDecayAlt.B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ≤
      (Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ) *
        Formalism.FourierDecayAlt.B.gN ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := by
    have e : Matrix.of x.2.2 * Matrix.of x.2.1 =
        (γ⁻¹ * Matrix.of y * γ) * ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := by
      rw [Matrix.mul_assoc ((γ⁻¹ * Matrix.of y * γ)⁻¹), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hmu, Matrix.one_mul]
    have hm : Formalism.FourierDecayAlt.B.gN (γ⁻¹ * Matrix.of y * γ) ≤ Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ := by
      calc Formalism.FourierDecayAlt.B.gN (γ⁻¹ * Matrix.of y * γ)
          ≤ Formalism.FourierDecayAlt.B.gN (γ⁻¹ * Matrix.of y) * Formalism.FourierDecayAlt.B.gN γ := gmul _ _
        _ ≤ (Formalism.FourierDecayAlt.B.gN γ⁻¹ * Formalism.FourierDecayAlt.B.gN (Matrix.of y)) * Formalism.FourierDecayAlt.B.gN γ :=
          mul_le_mul_of_nonneg_right (gmul _ _) (gnn _)
        _ ≤ Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyT (gnn _)) (gnn _)
    rw [e]
    exact le_trans (gmul _ _) (mul_le_mul_of_nonneg_right hm (gnn _))
  have hUH12 : Matrix.of x.1.2 * Matrix.of x.1.1 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hP12.1 hP11.1
  have hUH22 : Matrix.of x.2.2 * Matrix.of x.2.1 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hP22.1 hP21.1
  have hUHM : (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hP11.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hP12.1)) hγ)
      hP22.1) hP21.1
  have hsum : Formalism.FourierDecayAlt.B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) + Formalism.FourierDecayAlt.B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ≤
      max ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) 1 *
        Formalism.FourierDecayAlt.B.gN ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * γ * Matrix.of x.2.2 * Matrix.of x.2.1) ^
          (5 * (r + 1) ^ 2) := by
    rw [hMeq]
    have hpow : 0 ≤ Formalism.FourierDecayAlt.B.gN (((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1)⁻¹ * γ *
        ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1)) ^ (5 * (r + 1) ^ 2) :=
      pow_nonneg (gnn _) _
    have hσn := gnn ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1)
    have hsn := gnn ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1)
    calc _ ≤ T * Formalism.FourierDecayAlt.B.gN ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) +
          (Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ) *
            Formalism.FourierDecayAlt.B.gN ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1) := add_le_add hX hY
      _ ≤ (T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) *
          (Formalism.FourierDecayAlt.B.gN ((Matrix.of y)⁻¹ * Matrix.of x.1.2 * Matrix.of x.1.1) +
            Formalism.FourierDecayAlt.B.gN ((γ⁻¹ * Matrix.of y * γ)⁻¹ * Matrix.of x.2.2 * Matrix.of x.2.1)) := by
          nlinarith [mul_nonneg c1nn hσn, mul_nonneg hT0 hsn]
      _ ≤ (T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * (C * _) :=
          mul_le_mul_of_nonneg_left hb1 (by linarith)
      _ = ((T + Formalism.FourierDecayAlt.B.gN γ⁻¹ * T * Formalism.FourierDecayAlt.B.gN γ + 1) * C) * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  have hE : 0 < 5 * (r + 1) ^ 2 := by positivity
  have key := key_bound (PI.PolynomialProperness.GN.gN_ge_one hUH12) (PI.PolynomialProperness.GN.gN_ge_one hUH22)
    (PI.PolynomialProperness.GN.gN_ge_one hUHM) hKc hE hb hsum
  unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
  exact key

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem growth_side {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ⊤) {β : ℝ} (hβ : Formalism.FourierDecayAlt.ThreeDimData.AG k r < β) :
    ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β))
      ∂(μW.prod (haarLie (Nset k r) κ)) < ⊤ := by
  set μN := haarLie (Nset k r) κ with hμN
  obtain ⟨μG, hμG⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  have hGsk : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG :=
    ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμG, hμG.ne_zero, hμG.conc, hμG.left⟩
  have hS := Formalism.L2.SG.Pf.Choice.isHaarOn_muS hz hT hW hW1 hκ0 hκt
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists k r z hz hT μG _ hGsk hS
  have hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN := Formalism.MainNotions.BridgeCSB.haarLieN k r κ hκ0 hκt
  have hgr := Formalism.FourierDecayAlt.P.growth_spherical_bound k r z μW μN μG νq β hz hT hW hN hGsk hq hβ
  have hβ0 : 0 < β := lt_of_le_of_lt (by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity) hβ
  have hI : ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) ∂(μW.prod μN) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p =>
      Real.rpow_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _) _)).1 hgr.2

  obtain ⟨CW0, hCW0⟩ := (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT).exists_bound_of_continuousOn
    (f := fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Formalism.FourierDecayAlt.B.gN x)
    Formalism.FourierDecayAlt.P.s3dx1S_gNc.continuousOn
  set CW := max CW0 1 with hCW
  have hCW1 : 1 ≤ CW := le_max_right _ _
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound k r
  have : SigmaFinite μW := hW.1
  have : SFinite μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have hpt : ∀ᵐ p ∂(μW.prod μN), ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β)) ≤
      ENNReal.ofReal ((CW * CW) ^ β) * ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) := by
    refine hae.mono fun p hp => ?_
    set h := Matrix.of p.1
    set n := Matrix.of p.2
    have hhU : h ∈ UH (Hpk k r) := hp.1.1
    have hhu : IsUnit h.det := uh_isUnit hhU
    have hnh : n * h ∈ UH (Hpk k r) := PI.WUN.UH_mul hp.2.1 hhU
    have hhn : h * n ∈ UH (Hpk k r) := PI.WUN.UH_mul hhU hp.2.1
    have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN (h * n) := (hNI.2 _ hhn).2
    have hgh : Formalism.FourierDecayAlt.B.gN h ≤ CW := by
      have := hCW0 h hp.1
      rw [Real.norm_of_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _)] at this
      exact this.trans (le_max_left _ _)
    have hghi : Formalism.FourierDecayAlt.B.gN h⁻¹ ≤ CW := by rw [(hNI.2 h hhU).1]; exact hgh
    have hle : Formalism.FourierDecayAlt.B.gN (h * n) ≤ CW * CW * Formalism.FourierDecayAlt.B.gN (n * h) := by
      have e : h * n = h * (n * h) * h⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.mul_one]
      rw [e]
      calc Formalism.FourierDecayAlt.B.gN (h * (n * h) * h⁻¹) ≤ Formalism.FourierDecayAlt.B.gN (h * (n * h)) * Formalism.FourierDecayAlt.B.gN h⁻¹ := hNI.1 _ _
        _ ≤ (Formalism.FourierDecayAlt.B.gN h * Formalism.FourierDecayAlt.B.gN (n * h)) * CW :=
            mul_le_mul (hNI.1 _ _) hghi (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _)
              (mul_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _) (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _))
        _ ≤ (CW * Formalism.FourierDecayAlt.B.gN (n * h)) * CW :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgh (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _))
              (by linarith)
        _ = CW * CW * Formalism.FourierDecayAlt.B.gN (n * h) := by ring
    have hpos : 0 < Formalism.FourierDecayAlt.B.gN (h * n) / (CW * CW) := div_pos (by linarith) (by positivity)
    have hle' : Formalism.FourierDecayAlt.B.gN (h * n) / (CW * CW) ≤ Formalism.FourierDecayAlt.B.gN (n * h) := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hm := Real.rpow_le_rpow_of_nonpos hpos hle' (by linarith : -β ≤ 0)
    rw [Real.div_rpow (by linarith) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ CW * CW),
      div_inv_eq_mul] at hm
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    exact ENNReal.ofReal_le_ofReal (hm.trans_eq (mul_comm _ _))
  calc ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β)) ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal ((CW * CW) ^ β) *
          ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) ∂(μW.prod μN) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((CW * CW) ^ β) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) ∂(μW.prod μN) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
