module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiQEqZeroOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

def suppQ {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) : Set (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
  {x | IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧ (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1}

theorem phiQ_eq_zero_of_not_mem {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (hx : x ∉ suppQ v r) : phiQ v r mu x = 0 := by
  unfold phiQ
  rw [dite_eq_right]
  exact hx

end GlobalTheory.NrmVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepTwistedNormSqEqUntwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSqThetaLocalDatumAtTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMulConjEqIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMulConjEqIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_mul_conj_eq_indicator : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v r mu x * (starRingEnd ℂ) (phiQ v r mu x) = (GlobalTheory.NrmVol.suppQ v r).indicator (fun _ => (1 : ℂ)) x := by
  intro D PP v φ hP a b r ξ mu hL x
  by_cases hx : x ∈ GlobalTheory.NrmVol.suppQ v r
  · rw [Set.indicator_of_mem hx]
    have h : IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧
        (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1 := hx
    unfold phiQ
    rw [dite_eq_left h]
    obtain ⟨⟨red, -, -, hrel, -⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
    set u := h.1.unit with hu
    have hv : Valued.v (u : Fv D.host.F v) = 1 := by rw [hu, IsUnit.unit_spec]; exact h.2.1
    have hvi : Valued.v ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have hint : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.le
    have hint' : ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hvi.le
    have hunit : IsUnit (⟨(u : Fv D.host.F v), hint⟩ : v.adicCompletionIntegers D.host.F) :=
      ⟨⟨⟨_, hint⟩, ⟨_, hint'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
    set k := (hunit.map red).unit with hk
    have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) :=
      (hrel _ _).2 ⟨hint, (IsUnit.unit_spec (hunit.map red)).symm⟩
    have hmu : mu u = ξ k := hL u k hR
    haveI : Finite (kP PP)ˣ := Finite.of_injective _ Units.val_injective
    obtain ⟨n, hn0, hn⟩ := (ξ.isOfFinOrder (isOfFinOrder_of_finite k)).exists_pow_eq_one
    have hpow : ((mu u : ℂˣ) : ℂ) ^ n = 1 := by
      rw [hmu, ← Units.val_pow_eq_pow_val, hn, Units.val_one]
    have hnorm : ‖((mu u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hn0.ne'
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inv, hnorm]
    norm_num
  · rw [Set.indicator_of_notMem hx, phiQ_eq_zero_of_not_mem v r mu x hx, zero_mul]

end GlobalTheory.NrmVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMulConjEqIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceChainStepDatum_mul_conj_eq_indicator : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v r mu x * (starRingEnd ℂ) (phiQ v r mu x) = (GlobalTheory.NrmVol.suppQ v r).indicator (fun _ => (1 : ℂ)) x := by
  first | exact @GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator | exact GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator | (intros; apply GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMemSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMemSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.SBTwist

theorem viaRed_mem_SB {D : D7} {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ}
    (r : v.adicCompletionIntegers D.host.F →+* k)
    (hr : ∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) :
    GlobalTheory.StepVec.viaRed r ω ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  classical
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : ∀ᶠ y in nhds x, ∀ i j, Valued.v (y i j - x i j) < 1 := by
      rw [Filter.eventually_all]; intro i
      rw [Filter.eventually_all]; intro j
      have hc : Continuous fun y : Matrix (Fin b) (Fin a) (Fv D.host.F v) => y i j :=
        continuous_id.matrix_elem i j
      have hn : {z : Fv D.host.F v | Valued.v (z - x i j) < 1} ∈ nhds (x i j) :=
        Valued.mem_nhds.2 ⟨1, fun z hz => by simpa using hz⟩
      exact hc.continuousAt.preimage_mem_nhds hn
    filter_upwards [hU] with y hy
    have hint : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F ↔ x i j ∈ v.adicCompletionIntegers D.host.F := by
      intro i j
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 := hy i j
      constructor
      · intro h
        have : x i j = y i j - (y i j - x i j) := by ring
        rw [this]
        refine le_trans (Valuation.map_sub _ _ _) (max_le h (le_of_lt h1))
      · intro h
        have : y i j = (y i j - x i j) + x i j := by ring
        rw [this]
        exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt h1) h)
    unfold GlobalTheory.StepVec.viaRed
    by_cases hx : ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F
    · have hy' : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun i j => (hint i j).2 (hx i j)
      rw [dite_eq_left hy', dite_eq_left hx]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      have hs : (⟨y i j, hy' i j⟩ : v.adicCompletionIntegers D.host.F) - ⟨x i j, hx i j⟩ =
          ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩ := rfl
      have h0 := (hr ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩).2 (hy i j)
      rw [← hs, map_sub, sub_eq_zero] at h0
      exact h0
    · have hy' : ¬ ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun h => hx fun i j => (hint i j).1 (h i j)
      rw [dif_neg hy', dif_neg hx]
  · haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers D.host.F v
    have hK : IsCompact {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} := by
      have he : {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} =
          Set.pi Set.univ (fun _ : Fin b => Set.pi Set.univ (fun _ : Fin a => (v.adicCompletionIntegers D.host.F : Set (Fv D.host.F v)))) := by
        ext Y
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [he]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 ‹_›
    refine HasCompactSupport.intro hK ?_
    intro Y hY
    have hY' : ¬ ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F := hY
    unfold GlobalTheory.StepVec.viaRed
    exact dif_neg hY'

theorem phiQ_mem_SB : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hφ a b r ξ mu hmu
  obtain ⟨⟨rr, hrr⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hred : GlobalTheory.StepVec.IsRedMap φ PP rr := hrr
  have hmu' : LiftsChar φ PP mu ξ⁻¹⁻¹ := by rwa [inv_inv]
  have heq : phiQ (a := a) (b := b) v r mu = GlobalTheory.StepVec.viaRed rr (GlobalTheory.StepVec.qLoc r PP ξ⁻¹) :=
    funext fun Y => GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc D v φ PP rr hred a b r mu ξ⁻¹ hmu' Y
  rw [heq]
  exact viaRed_mem_SB rr hred.2.1 _

end GlobalTheory.SBTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMemSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  first | exact @GlobalTheory.SBTwist.phiQ_mem_SB | exact GlobalTheory.SBTwist.phiQ_mem_SB | (intros; apply GlobalTheory.SBTwist.phiQ_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeasurableSetTwistPlaceChainStepDatumMatrixSuppo
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeasurableSetTwistPlaceChainStepDatumMatrixSuppo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem measurableSet_suppQ : ∀ (D : D7) (v : FinPl D) (a b r : ℕ),
    MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  intro D v a b r
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv D.host.F v)
  haveI : OpensMeasurableSpace (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
    inferInstanceAs (OpensMeasurableSpace (Fin b → Fin a → Fv D.host.F v))
  have hentry : ∀ i j, Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have htop : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => topL r x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold topL
    by_cases h : i.val < b ∧ j.val < a
    · simp only [dif_pos h]; exact hentry _ _
    · simp only [dif_neg h]; exact continuous_const
  have hdet : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => (topL r x).det :=
    htop.matrix_det
  have hball : IsOpen {y : Fv D.host.F v | Valued.v y < 1} := by
    simpa using Valued.isOpen_ball (Fv D.host.F v) 1
  have hsph : IsOpen {y : Fv D.host.F v | Valued.v y = 1} := by
    simpa using Valued.isOpen_sphere (Fv D.host.F v) (r := 1) one_ne_zero
  have hcb : IsOpen {y : Fv D.host.F v | Valued.v y ≤ 1} := by
    simpa using Valued.isOpen_closedBall (Fv D.host.F v) (r := 1) one_ne_zero
  have h1 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} =
        (fun x => (topL r x).det) ⁻¹' {0}ᶜ := by
      ext x; simp [isUnit_iff_ne_zero]
    rw [this]
    exact (isOpen_compl_singleton.preimage hdet).measurableSet
  have h2 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | Valued.v (topL r x).det = 1} :=
    (hsph.preimage hdet).measurableSet
  have h3 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} =
        ⋂ i, ⋂ j, (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (hcb.preimage (hentry i j)).measurableSet
  have h4 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
        ⋂ i, ⋂ j, {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : r ≤ i.val ∧ j.val < r
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y < 1} := by
        ext x; simp [hij.1, hij.2]
      rw [this]
      exact (hball.preimage (hentry i j)).measurableSet
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h h'
        exact absurd ⟨h, h'⟩ hij
      rw [this]
      exact MeasurableSet.univ
  have : suppQ (a := a) (b := b) v r =
      {x | IsUnit (topL r x).det} ∩ {x | Valued.v (topL r x).det = 1} ∩
        {x | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} ∩
        {x | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    ext x
    simp only [suppQ, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

end GlobalTheory.NrmVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeasurableSetTwistPlaceChainStepDatumMatrixSuppoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  first | exact @GlobalTheory.NrmVol.measurableSet_suppQ | exact GlobalTheory.NrmVol.measurableSet_suppQ | (intros; apply GlobalTheory.NrmVol.measurableSet_suppQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumSupportEqValuative
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumSupportEqValuative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.NrmVol

theorem suppQ_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  intro D v a b r
  have hC : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE : (ValuativeRel.valuation (Fv D.host.F v)).IsEquiv
      (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hle : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z ≤ 1 ↔ Valued.v z ≤ 1 :=
    fun z => hE.le_one_iff_le_one
  have hlt : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z < 1 ↔ Valued.v z < 1 :=
    fun z => hE.lt_one_iff_lt_one
  have heq : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z = 1 ↔ Valued.v z = 1 :=
    fun z => hE.eq_one_iff_eq_one
  have htop : ∀ (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (i j : Fin r),
      topL r x i j = 0 ∨ ∃ i' j', topL r x i j = x i' j' := by
    intro x i j
    unfold topL
    split_ifs with h
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl rfl
  refine ⟨?_, ?_⟩
  · ext x
    simp only [suppQ, Set.mem_setOf_eq, GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · rintro ⟨-, hdet, hint, hlow⟩
      refine ⟨⟨fun i j => ?_, (heq _).2 hdet⟩, fun i j => (hle _).2 (hint i j),
        fun i j hi hj => (hlt _).2 (hlow i j hi hj)⟩
      rcases htop x i j with h | ⟨i', j', h⟩
      · rw [h, map_zero]; exact zero_le_one
      · rw [h]; exact (hle _).2 (hint i' j')
    · rintro ⟨⟨-, hdet⟩, hint, hlow⟩
      have hd : Valued.v (topL r x).det = 1 := (heq _).1 hdet
      refine ⟨?_, hd, fun i j => (hle _).1 (hint i j), fun i j hi hj => (hlt _).1 (hlow i j hi hj)⟩
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, map_zero] at hd
      exact zero_ne_one hd
  · ext y
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => (hle _).symm

end GlobalTheory.NrmVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumSupportEqValuativeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  first | exact @GlobalTheory.NrmVol.suppQ_eq_valuative | exact GlobalTheory.NrmVol.suppQ_eq_valuative | (intros; apply GlobalTheory.NrmVol.suppQ_eq_valuative <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_ip : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hP a b r hra hrb ξ mu hL ν hν
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨?_, GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat D PP v φ hP a b r ξ mu hL⟩
  have h1 := GlobalTheory.T.twistPlaceChainStepDatum_mul_conj_eq_indicator D PP v φ hP a b r ξ mu hL
  have h3 := GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport D v a b r
  obtain ⟨e1, e2⟩ := GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative D v a b r
  have h4 := GlobalTheory.T.matrixMeasure_topBlock_integralGL_maxIdeal (Fv D.host.F v) ν hν a b r hra hrb
  rw [← e1, ← e2, (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2] at h4
  unfold GlobalTheory.SplitWeil.ip
  simp_rw [h1]
  have hI : ∫ x, (suppQ v r).indicator (fun _ => (1 : ℂ)) x ∂GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) =
      (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a)) (suppQ v r)).toReal : ℂ) := by
    erw [integral_indicator_const (μ := GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a)) (1 : ℂ) h3,
      measureReal_def]
    simp
  rw [hI, h4, zinv]

end GlobalTheory.NrmVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_phi_inner_product : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  first | exact @GlobalTheory.NrmVol.phiQ_ip | exact GlobalTheory.NrmVol.phiQ_ip | (intros; apply GlobalTheory.NrmVol.phiQ_ip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSqThetaLocalDatumAtTwistPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.ThetaNormTwist

theorem normSq_thetaLocalDatum_at_twistPlace_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) → ∀ r : ℕ, r ≤ S.rank → r ≤ T.rank → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v r mu)) x → nrm2 m X x = zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hcov hfS hfT PP v φ e he hP hA r hrS hrT ξ mu hmu x hx
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  obtain ⟨⟨Tm, hTm⟩, hxall⟩ := hx
  have hxT := hxall Tm hTm
  have hco := (GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he (frCo φ βS) (frCo φ βT)).1
  let ν : Measure (Fv D.host.F v) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hv0, hvT, hiso⟩ := GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ m X hB hcov v e he.1
    T.rank S.rank (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.mapCo φ S T (frCo φ βS) (frCo φ βT)) hco Tm hTm ν hν
  obtain ⟨hip, hSB⟩ := GlobalTheory.T.split_weil_phi_inner_product D PP v φ hP S.rank T.rank r hrS hrT ξ mu hmu ν hν

  obtain ⟨⟨a0, ha0, -, hmax, himg⟩, -⟩ :=
    GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hB.2.2.1 hB.2.2.2.1 hfS hfT v φ e he
  have hval : Valued.v (rdQ φ a0) = 1 := by
    obtain ⟨⟨a1, ha1, h1⟩, hle⟩ := hA
    exact le_antisymm (hle a0 ha0) (h1 ▸ hmax a1 ha1)
  rw [hval] at himg
  have key := hiso _ hSB _ hSB
  rw [himg, hip] at key
  rw [← GlobalTheory.PlaceTensor.onHalf_eq_pull] at key
  rw [← hxT] at key
  have hne : ((GlobalTheory.SplitWeil.volM ν (Fin T.rank) (Fin S.rank) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal : ℂ) ≠ 0 := by
    rw [← himg]
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO m X x x = ((nrm2 m X x : ℝ) : ℂ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO nrm2
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e2] at key
  push_cast at key
  have key2 := mul_left_cancel₀ hne key
  apply Complex.ofReal_injective
  rw [key2]
  push_cast
  ring

end GlobalTheory.ThetaNormTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSqThetaLocalDatumAtTwistPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_thetaLocalDatum_at_twistPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) → ∀ r : ℕ, r ≤ S.rank → r ≤ T.rank → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v r mu)) x → nrm2 m X x = zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ := by
  first | exact @GlobalTheory.ThetaNormTwist.normSq_thetaLocalDatum_at_twistPlace_alt | exact GlobalTheory.ThetaNormTwist.normSq_thetaLocalDatum_at_twistPlace_alt | (intros; apply GlobalTheory.ThetaNormTwist.normSq_thetaLocalDatum_at_twistPlace_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIdealIsUnitSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIdealIsUnitSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.NormIdealUnit

theorem unit_at_split_place : ∀ (D : D7) (PP : Pl D.host.E), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) := by
  intro D PP hPP v φ hφ
  have hq : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have unit : ∀ x : 𝓞 D.host.E, x ∉ PP.asIdeal → Valued.v (rdQ φ (x : D.host.E)) = 1 := fun x hx =>
    le_antisymm (GlobalTheory.TameLiftChar.val_rdQ_le_one φ x) (not_lt.1 fun h => hx ((hφ x).2 h))
  refine ⟨⟨_, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D, ?_⟩, ?_⟩
  · have := unit _ hN
    simpa using this
  · have hnot : ¬ D.host.𝔟 ≤ PP.asIdeal :=
      haveI := PP.isPrime; UpperTheory.Ram.half_not_le D.host _ hq
    obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
    have hz1 := unit z hzP
    have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
    have hAA0 : ∀ a : D.host.E, a ∈ D.host.AA0 → Valued.v (rdQ φ a) ≤ 1 := by
      intro a ha
      unfold Host.AA0 at ha
      rw [FractionalIdeal.mem_inv_iff hB] at ha
      obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
      have h3 := GlobalTheory.TameLiftChar.val_rdQ_le_one φ w
      rw [RingOfIntegers.coe_eq_algebraMap, hw, ← GlobalTheory.TameLiftChar.rdQHom_apply, map_mul, map_mul,
        GlobalTheory.TameLiftChar.rdQHom_apply, GlobalTheory.TameLiftChar.rdQHom_apply] at h3
      rw [← RingOfIntegers.coe_eq_algebraMap] at h3
      rw [hz1] at h3
      simpa using h3
    have hle : D.host.AA ≤ D.host.AA0 := by
      unfold Host.AA
      calc (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
          ≤ 1 * D.host.AA0 := by first | exact FractionalIdeal.mul_right_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | gcongr; exact FractionalIdeal.coeIdeal_le_one
        _ = D.host.AA0 := one_mul _
    exact fun a ha => hAA0 a (hle ha)

end GlobalTheory.NormIdealUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIdealIsUnitSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeIdeal_isUnit_splitPlace : ∀ (D : D7) (PP : Pl D.host.E), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) := by
  first | exact @GlobalTheory.NormIdealUnit.unit_at_split_place | exact GlobalTheory.NormIdealUnit.unit_at_split_place | (intros; apply GlobalTheory.NormIdealUnit.unit_at_split_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepTwistedNormSqEqUntwisted
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (ipO Place IsBaseOff)

noncomputable section

namespace GlobalTheory.TwistNorm

theorem level_trivial_eq_ofLocal {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) :
    LevelP.triv Pg r ℂ = LevelP.ofLocal (fun _ => ⊥) (fun _ => 1) := by
  have hH : (Subgroup.pi Set.univ fun PP : ↥Pg => (⊥ : Subgroup (GL (Fin r) (kP PP.1)))) = ⊥ := by
    ext g
    simp [Subgroup.mem_pi, funext_iff]
  haveI : Subsingleton (↥(⊥ : Subgroup (G0 Pg r)) →* ℂˣ) :=
    ⟨fun f g => MonoidHom.ext fun y => by rw [Subsingleton.elim y 1, map_one, map_one]⟩
  unfold LevelP.triv LevelP.ofLocal
  congr 1
  · exact hH.symm
  · exact Subsingleton.helim (congrArg (fun H : Subgroup (G0 Pg r) => (↥H →* ℂˣ)) hH.symm) _ _

theorem norm_sq_eq_inner_product {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (g : WO S T → ℂ) :
    ((nrm2 μ 𝓕 g : ℝ) : ℂ) = ipO μ 𝓕 g g := by
  unfold nrm2 ipO
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem chainStep_twisted_normSq_eq_untwisted_mul_localFactors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT r t j t' hr ht Pg Q hdisj hQ2 χ χj ξ ξ' f f' hf hf'
  have hP : (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  have hP' : (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  obtain ⟨⟨x, hx⟩, hall⟩ := GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj Q ξ f₀ f m X t' ht _ _ hP hB hC
    hFS hFT hdisj hf
  have hall' := (GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj ∅ ξ' f₀ f' m X t' ht _ _ hP' hB hC hFS hFT
    (Finset.disjoint_empty_right _) hf').2
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, -⟩ := hf
  have hes' : ∀ PP ∈ Pg ∪ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP := hes
  have hce' : (∑ PP ∈ Pg ∪ Q, es PP) * cA D (∑ PP ∈ Pg ∪ Q, es PP) = 0 := hce
  have hsum := GlobalTheory.SplitIdemDict.idem_dictionary D
  choose vA φA hφA hprA using fun i : ↥(Pg ∪ Q) => hsum.1 (es i.1) i.1 (hes' i.1 i.2)
  have hunder : ∀ i : ↥(Pg ∪ Q), (i.1).asIdeal.under (𝓞 D.host.F) = (vA i).asIdeal := fun i =>
    (hsum.2 _ _ _ (hprA i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (Pg ∪ Q)
    (fun i hi => (hes' i hi).1.1) hce'
  have hinj : Function.Injective vA := by
    intro i j hij
    have h1 := (hφA i).2.1
    have h2 := (hφA j).2.1
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes' i.1 i.2).1.1 (hes' i.1 i.2).1.2.1 (hes' j.1 j.2).1.1
      (hes' j.1 j.2).1.2.1 (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (GlobalTheory.StepVec.prime_eq_of_idem (hes' i.1 i.2) (h3 ▸ hes' j.1 j.2))

  obtain ⟨x', hx'l, hx'r⟩ : ∃ x' : Place D → WO S T → ℂ, (∀ τ, x' (.inr τ) = f₀) ∧
      ∀ v, x' (.inl v) = if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀ :=
    ⟨Sum.elim (fun v => if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀) fun _ => f₀,
      fun _ => rfl, fun _ => rfl⟩
  have hpure' := hall' x' ⟨⟨hx'l, fun v hv => by
      rw [hx'r, if_neg]
      rintro ⟨PP, h1, h2⟩
      exact hv PP (Finset.mem_union_left _ h1) h2⟩,
    fun v φ e' he' mu => ⟨fun PP hpp hmu J lam hJ => by
      have h := (hx.2 v φ e' he' mu).1 PP hpp hmu J lam hJ
      rw [hx'r, if_pos ⟨PP.1, PP.2, (hsum.2 v φ PP.1 hpp).1⟩]
      exact h, fun PP hq => by simp at hq⟩⟩
  have hpure := hall x hx
  obtain ⟨hfin, hxx⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x x f f
    hpure hpure
  obtain ⟨-, hxx'⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x' x' f' f'
    hpure' hpure'
  have h0 : ipO m X f₀ f₀ = 1 := by
    rw [← norm_sq_eq_inner_product, hvac.2.norm.2 (m, X) hC]
    simp

  let iq : ↥Q → ↥(Pg ∪ Q) := fun i => ⟨i.1, Finset.mem_union_right _ i.2⟩
  let U : Finset (Place D) := Q.attach.image fun i => (Sum.inl (vA (iq i)) : Place D)
  have hnotPg : ∀ i : ↥Q, ¬ ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = (vA (iq i)).asIdeal := by
    rintro i ⟨PP, hPP, hu⟩
    have h1 : vA ⟨PP, Finset.mem_union_left _ hPP⟩ = vA (iq i) := HeightOneSpectrum.ext ((hunder _).symm.trans hu)
    have h2 : PP = i.1 := congrArg Subtype.val (hinj h1)
    exact Finset.disjoint_left.1 hdisj hPP (by rw [h2]; exact i.2)
  have hpt : ∀ p, ipO m X (x p) (x p) =
      ipO m X (x' p) (x' p) * (if p ∈ U then ipO m X (x p) (x p) else 1) := by
    intro p
    by_cases hp : p ∈ U
    · rw [if_pos hp]
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [hx'r, if_neg (hnotPg i), h0, one_mul]
    · rw [if_neg hp, mul_one]
      rcases p with v | τ
      · rw [hx'r]
        by_cases hv : ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal
        · rw [if_pos hv]
        · rw [if_neg hv]
          have hxv : x (.inl v) = f₀ := hx.1.2 v fun PP hPP hu => by
            rcases Finset.mem_union.1 hPP with h | h
            · exact hv ⟨PP, h, hu⟩
            · exact hp (Finset.mem_image.2 ⟨⟨PP, h⟩, Finset.mem_attach _ _,
                congrArg Sum.inl (HeightOneSpectrum.ext ((hunder _).symm.trans hu))⟩)
          rw [hxv]
      · rw [hx'l, hx.1.1 τ]
  let s0 : Finset (Place D) := hfin.toFinset ∪ U
  have hA : ∏ᶠ p, ipO m X (x p) (x p) = ∏ p ∈ s0, ipO m X (x p) (x p) :=
    finprod_eq_prod_of_mulSupport_subset _ fun p hp => Finset.mem_union_left _ (hfin.mem_toFinset.2 hp)
  have hA' : ∏ᶠ p, ipO m X (x' p) (x' p) = ∏ p ∈ s0, ipO m X (x' p) (x' p) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
    by_cases hU : p ∈ U
    · exact Finset.mem_union_right _ hU
    · refine Finset.mem_union_left _ (hfin.mem_toFinset.2 ?_)
      have h := hpt p
      rw [if_neg hU, mul_one] at h
      rw [Function.mem_mulSupport] at hp ⊢
      rwa [h]
  have hsplit : ∏ p ∈ s0, ipO m X (x p) (x p) =
      (∏ p ∈ s0, ipO m X (x' p) (x' p)) * ∏ p ∈ U, ipO m X (x p) (x p) := by
    rw [Finset.prod_congr rfl fun p _ => hpt p, Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.inter_eq_right.2 Finset.subset_union_right]
  have hU : ∏ p ∈ U, ipO m X (x p) (x p) = ∏ i ∈ Q.attach, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) := by
    refine Finset.prod_image fun i _ j _ h => ?_
    have h1 := hinj (Sum.inl_injective h)
    have h2 : (iq i).1 = (iq j).1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hloc : ∀ i : ↥Q, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) =
      ((zinv i.1 0 r * ((Ideal.absNorm i.1.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ) := by
    intro i
    obtain ⟨mu, hmu⟩ := (GlobalTheory.PlaceRed.red_dict D (vA (iq i)) (φA (iq i)) i.1 (hprA (iq i))).2 (ξ i.1)⁻¹
    have hθ := (hx.2 (vA (iq i)) (φA (iq i)) (es i.1) (hφA (iq i)) mu).2 i.1 i.2 (hprA (iq i)) hmu
    rw [← norm_sq_eq_inner_product, GlobalTheory.T.normSq_thetaLocalDatum_at_twistPlace D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT i.1 (vA (iq i)) (φA (iq i)) (es i.1)
      (hφA (iq i)) (hprA (iq i)) (GlobalTheory.T.homLatticeIdeal_isUnit_splitPlace D i.1 (hQ2 i.1 i.2) (vA (iq i)) (φA (iq i)) (hprA (iq i))) r hr (by omega)
      (ξ i.1)⁻¹ mu hmu _ hθ]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_prod, norm_sq_eq_inner_product, norm_sq_eq_inner_product, hxx, hxx', hA, hA', hsplit, hU,
    Finset.prod_congr rfl fun i _ => hloc i,
    Finset.prod_attach Q fun PP => ((zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ)]

end GlobalTheory.TwistNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepTwistedNormSqEqUntwistedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  first | exact @GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors | exact GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors | (intros; apply GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.RNrmProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rNrm_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG
  have hL := hG.core.lev
  have hC := hG.core.chain
  have hQ : R.Q A.μ0 = ∅ := GlobalTheory.ChainTw.RModel.Q_base R hL
  have hm := D.R.two_le_m
  intro t
  refine ⟨fun k hk m X hX => ?_, fun m X hX => ?_⟩
  · obtain ⟨c, hc⟩ := hL.βY k (by omega)
    obtain ⟨c', hc'⟩ := hL.βY (k + 1) hk
    have h1 := hC.vY t k hk
    have h2 := hC.vY A.μ0 k hk
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k) :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hrk : (Yc D k).rank + D.R.t = (Yc D (k + 1)).rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), GlobalTheory.Chain.StepVac.rank_Yc (by omega)]; ring
    have key := GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv D R.ψ R.θ (Yc D k) (Yc D (k + 1)) _ _ _ _ _ _ (R.vac k) m X hb hX hc.1 hc'.1
      D.R.r D.R.t k D.R.t (r_le_Y k) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi (k + 1)) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega)]
    congr 4
    simp
  · obtain ⟨c, hc⟩ := hL.βY (D.R.m - 1) (by omega)
    obtain ⟨c', hc'⟩ := hL.βX
    have h1 := hC.vX t
    have h2 := hC.vX A.μ0
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hX' : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
    have hrk : (Yc D (D.R.m - 1)).rank + D.R.t = D.sp.X'.rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), hX']
      obtain ⟨n, hn⟩ : ∃ n, D.R.m = n + 1 := ⟨D.R.m - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel]; ring
    have key := GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' _ _ _ _ _ _ R.vacX m X hb hX hc.1 hc'.1
      D.R.r D.R.t (D.R.m - 1) D.R.t (r_le_Y _) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi D.R.m) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [hX']
    congr 4
    simp

end GlobalTheory.ChainTw.RNrmProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypothesesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realDatumNormShrink_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  first | exact @GlobalTheory.ChainTw.RNrmProof.rNrm_of_given | exact GlobalTheory.ChainTw.RNrmProof.rNrm_of_given | (intros; apply GlobalTheory.ChainTw.RNrmProof.rNrm_of_given <;> assumption)
end
