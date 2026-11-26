module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.NumFam

theorem eps_adj (k r : ℕ) (a c : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) (hc : c.val = a.val + 1) :
    PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r c := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : ¬ c.val < k - 1 := by omega
  simp only [PI.BesselPeriodGGP.eps48]
  rw [if_neg h1, if_neg h2, hc]
  rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
    simp [h3, h4]
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
    simp [h3, h4]

theorem abs_le_of_lOneNorm_le_coord {n : ℕ} (ν : Fin n → ℤ) (q0 : ℕ) (h : n1 ν ≤ q0) (a : Fin n) : |(ν a : ℝ)| ≤ q0 := by
  have h1 : (ν a).natAbs ≤ n1 ν := by
    unfold n1
    exact Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [h2]
  exact_mod_cast h1.trans h

theorem gapOK_mono (k r : ℕ) {h h' : ℝ} (hh : h ≤ h') (H : GapOK k r h) : GapOK k r h' := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  have ha : aOf r h ≤ aOf r h' := by
    unfold aOf
    gcongr
  exact ⟨h1, h2.trans hh, h3.trans ha, h4.trans ha⟩

private lemma le_bv_and_lam_gap_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ)
    (q0 : ℕ) (H : Num k r lam u b bv ga h q0) :
    h ≤ bv ∧ ∀ a c : Fin (2 * r + k + 1), a < c → 100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hgap, -, hq1, hq2, -⟩ := H
  have hhb : h ≤ bv := by
    have he := eps_adj k r ⟨k - 1, by omega⟩ ⟨k, by omega⟩ (show k ≤ k - 1 + 1 by omega)
      (show k = k - 1 + 1 by omega)
    have h0 := hnd ⟨k - 1, by omega⟩ (show k ≤ k - 1 + 1 by omega)
    have h1 := hnd ⟨k, by omega⟩ (show k ≤ k + 1 by omega)
    have hg := hgap _ _ he
    have hb : |lam ⟨k - 1, by omega⟩ - lam ⟨k, by omega⟩| ≤ bv :=
      abs_sub_le_iff.mpr ⟨by linarith [h0.1, h0.2, h1.1, h1.2], by linarith [h0.1, h0.2, h1.1, h1.2]⟩
    linarith
  have hadj : ∀ a c : Fin (2 * r + k + 1), c.val = a.val + 1 →
      100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
    intro a c hac
    have hlt : a < c := Fin.lt_def.mpr (by omega)
    have hlam : lam c < lam a := hanti hlt
    by_cases h1 : k ≤ a.val + 1
    · have hg := hgap a c (eps_adj k r a c h1 hac)
      rw [abs_of_pos (by linarith)] at hg
      linarith
    · by_cases h2 : c.val + 1 < k
      · linarith [hga a c hlt h2]
      · have h3 := hcl a (by omega)
        have h4 := hnd c (by omega)
        linarith [h3.1, h4.2]
  refine ⟨hhb, fun a c hac => ?_⟩
  have h5 : a.val < c.val := hac
  have hcN := c.isLt
  have hle : a ≤ ⟨c.val - 1, by omega⟩ := Fin.le_def.mpr (show a.val ≤ c.val - 1 by omega)
  have h6 := hadj ⟨c.val - 1, by omega⟩ c (show c.val = c.val - 1 + 1 by omega)
  have h7 := hanti.antitone hle
  linarith

theorem num_fam : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  intro k r lam u b bv ga h q0 H
  obtain ⟨hhb, hgaps⟩ := le_bv_and_lam_gap_of_num k r lam u b bv ga h q0 H
  obtain ⟨hk, ⟨hanti, hint⟩, -, -, -, hcl, hnd, hlb, -, -, hgap, hok, hq1, hq2, hbv⟩ := H
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hN7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hN1 (by norm_num)
  have hNc : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have hL := hnd ⟨2 * r + k, by omega⟩ (show k ≤ 2 * r + k + 1 by omega)
  have hLb := hlb ⟨2 * r + k, by omega⟩
  have hLa := neg_le_abs (lam ⟨2 * r + k, by omega⟩)
  have hbvb : bv ≤ b := by linarith [hL.2]
  have h100 : 100 * (q0 : ℝ) ≤ bv := by linarith
  refine ⟨⟨hbvb, by linarith, by linarith, h100, gapOK_mono k r (by linarith) hok⟩, fun ν hν => ?_⟩
  have hνb : ∀ a, -(q0 : ℝ) ≤ ν a ∧ (ν a : ℝ) ≤ q0 := fun a => abs_le.mp (abs_le_of_lOneNorm_le_coord ν q0 hν a)
  have hgap2 : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    linarith [hgaps a c hac, (hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]
  refine ⟨⟨fun a c hac => ?_, fun a => ?_⟩, ⟨hk, by omega, fun a c hac => hgap2 a c hac, fun a ha => ?_,
    fun a ha => ?_, hbv⟩, fun a c he => ?_, fun a c hac => hgap2 a c hac⟩
  · show lam c + (ν c : ℝ) < lam a + ν a
    linarith [hgap2 a c hac]
  · obtain ⟨m, hm⟩ := hint a
    refine ⟨m + ν a, ?_⟩
    show lam a + (ν a : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = ((m + ν a : ℤ) : ℝ)
    push_cast
    linarith
  · refine ⟨?_, ?_, ?_⟩
    · simp [PI.BesselPeriodGGP.eps48, show a.val < k - 1 by omega]
    · show -(bv / 100) ≤ lam a + (ν a : ℝ)
      linarith [(hcl a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ bv / 8 + bv / 100
      linarith [(hcl a ha).2, (hνb a).2]
  · refine ⟨?_, ?_⟩
    · show -2 * bv - bv / 100 ≤ lam a + (ν a : ℝ)
      linarith [(hnd a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ -bv + bv / 100
      linarith [(hnd a ha).2, (hνb a).2]
  · show h / 2 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
    have hg := hgap a c he
    rcases le_abs.mp hg with h1 | h1
    · exact le_abs.mpr (Or.inl (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))
    · exact le_abs.mpr (Or.inr (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))

end GlobalTheory.NumFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numericalFamily_shape_gaps : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  first | exact @GlobalTheory.NumFam.num_fam | exact GlobalTheory.NumFam.num_fam | (intros; apply GlobalTheory.NumFam.num_fam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarNotions


open Formalism.FourierDecayAlt.P.B2x1 in
theorem finite_compact_of_sigmaFinite {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [SigmaFinite μ] (hc : μ Uᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) (K : Set (Formalism.QuantumDeterminants.Mt k r)) (hK : IsCompact K) : μ K < ∞ := by
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have : SigmaFinite (pull hU μ) := by
    have h : SigmaFinite ((pull hU μ).map inc) := by rw [map_pull μ hc]; infer_instance
    exact SigmaFinite.of_map _ inc_memb.measurable.aemeasurable h
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Gp U hU)) := inferInstance
  have huniq := Measure.haarMeasure_unique (pull hU μ) K₀
  have hfin : pull hU μ K₀ ≠ ∞ := by
    intro hinf
    rw [hinf] at huniq
    have hzero : ∀ n, Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) = 0 := by
      intro n
      by_contra hne
      have h1 := measure_spanningSets_lt_top (pull hU μ) n
      have h2 : pull hU μ (spanningSets (pull hU μ) n) =
          ∞ * Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) :=
        congrArg (fun m : Measure (Gp U hU) => m (spanningSets (pull hU μ) n)) huniq
      rw [h2, ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have huniv : Measure.haarMeasure K₀ Set.univ = 0 := by
      rw [← iUnion_spanningSets (pull hU μ)]
      exact measure_iUnion_null hzero
    have h1 : Measure.haarMeasure K₀ K₀ = 0 := measure_mono_null (Set.subset_univ _) huniv
    rw [Measure.haarMeasure_self] at h1
    exact one_ne_zero h1
  have hK' : IsCompact ((inc : Gp U hU → Formalism.QuantumDeterminants.Mt k r) ⁻¹' K) := inc_closedEmb.isCompact_preimage hK
  have h3 : pull hU μ (inc ⁻¹' K) = pull hU μ K₀ * Measure.haarMeasure K₀ (inc ⁻¹' K) :=
    congrArg (fun m : Measure (Gp U hU) => m (inc ⁻¹' K)) huniq
  rw [← map_pull (hU := hU) μ hc, inc_memb.map_apply, h3]
  exact ENNReal.mul_lt_top hfin.lt_top hK'.measure_lt_top

theorem isHaarOn_iff {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (hex : ∃ ν : Measure (Formalism.QuantumDeterminants.Mt k r), B.IsHaarOn U ν) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ B.IsHaarOn U μ := by
  constructor
  · rintro ⟨hσ, h0, hc, hl⟩
    obtain ⟨ν, hν⟩ := hex
    have hfin := finite_compact_of_sigmaFinite hU μ hc hl
    obtain ⟨c, hcν⟩ := P.haar_measure_unique_up_to_scalar k r U ν μ hU hν hc hl hfin
    refine { ne_zero := h0, conc := hc, left := hl, right := ?_, finite_compact := hfin }
    intro a ha
    rw [hcν, Measure.map_smul, hν.right a ha]
    exact (show Continuous (B.rmulF a) from by
      unfold B.rmulF
      exact continuous_id.matrix_mul continuous_const).measurable.aemeasurable
  · intro h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem isHaarOn_iff_groups : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) :=
  fun k r μ =>
    ⟨isHaarOn_iff (P.unitary_group_closed k r) (P.unitary_group_haar_exists k r) μ,
      isHaarOn_iff (P.unipotent_radical_closed k r) (P.unipotent_haar_exists k r) μ,
      fun z hz hT _ => isHaarOn_iff (P.weyl_subgroup_closed k r z) (P.weyl_haar_exists k r z hz hT) μ⟩

end GlobalTheory.HaarNotions
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) := by
  first | exact @GlobalTheory.HaarNotions.isHaarOn_iff_groups | exact GlobalTheory.HaarNotions.isHaarOn_iff_groups | (intros; apply GlobalTheory.HaarNotions.isHaarOn_iff_groups <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPsi

open Formalism.QuantumDeterminants

theorem hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem inv_fix {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) {v : Fin n → ℂ}
    (h : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]

theorem uw_inv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g⁻¹ ∈ UWset k r z := by
  obtain ⟨hu, hi⟩ := (uHGroup _ _ (hpk_unit k r)).2.2 g hg.1
  exact ⟨hi, fun a => ⟨inv_fix hu (hg.2.1 a).1, inv_fix hu (hg.2.1 a).2⟩, inv_fix hu hg.2.2⟩

theorem uw_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) (hg' : g' ∈ UWset k r z) : g * g' ∈ UWset k r z := by
  refine ⟨(uHGroup _ _ (hpk_unit k r)).2.1 g hg.1 g' hg'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hg'.2.1 a).1, (hg.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hg'.2.1 a).2, (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hg'.2.2, hg.2.2]

theorem psi_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  intro k r z c hz
  refine ⟨fun g => ?_, fun m hm m' hm' => ⟨(nSubgroup k r).2.1 m hm m' hm', (psiChar k r z c hz m hm).1 m' hm'⟩,
    fun m hm => ⟨(nSubgroup k r).2.2 m hm, ?_⟩, fun g hg m hm => ?_,
    fun g hg g' hg' => ⟨uw_mul hg hg', uw_inv hg, hg.1⟩, fun m hm => hm.1⟩
  · unfold psi
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  · rw [← BesselUnipotentEquiv.star_psi_inv z c hz m hm, star_star]
  · have hu := ((uHGroup _ _ (hpk_unit k r)).2.2 g hg.1).1
    have h1 := uWNormal k r z hz g hg m hm
    have h2 := uWNormal k r z hz g⁻¹ (uw_inv hg) m hm
    rw [Matrix.nonsing_inv_nonsing_inv _ hu] at h2
    refine ⟨h1.1, h2.1, ?_, ?_⟩
    · unfold psi; rw [h1.2]
    · unfold psi; rw [h2.2]

end GlobalTheory.BesselPsi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  first | exact @GlobalTheory.BesselPsi.psi_character | exact GlobalTheory.BesselPsi.psi_character | (intros; apply GlobalTheory.BesselPsi.psi_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section
namespace GlobalTheory.MatHaar

open PI Topology

variable {m : ℕ}

abbrev Mx (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

def invA (x : MtM m) : MtM m := Matrix.of.symm ((Matrix.of x : Mx m)⁻¹)

def mulA (p : MtM m × MtM m) : MtM m := (Matrix.of p.1 : Mx m) * (Matrix.of p.2 : Mx m)

def adjA (x : MtM m) : MtM m := (Matrix.of x : Mx m).adjugate

def detA (x : MtM m) : ℂ := (Matrix.of x : Mx m).det

theorem detA_cont : Continuous (detA (m := m)) := Continuous.matrix_det (continuous_id (X := Mx m))
theorem adjA_cont : Continuous (adjA (m := m)) := Continuous.matrix_adjugate (continuous_id (X := Mx m))

theorem invA_smul : (invA : MtM m → MtM m) = fun x => (detA x)⁻¹ • adjA x := by
  funext x
  show (Ring.inverse (Matrix.of x : Mx m).det • (Matrix.of x : Mx m).adjugate : Mx m) = _
  rw [Ring.inverse_eq_inv']; rfl

theorem invA_contOn : ContinuousOn (invA : MtM m → MtM m) {x | detA x ≠ 0} := by
  rw [invA_smul]
  exact (detA_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjA_cont.continuousOn

theorem lmulQ_cont (a : Mx m) : Continuous (lmulQ a : MtM m → MtM m) := by
  unfold lmulQ
  exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mx m))

theorem mulA_cont : Continuous (mulA : MtM m × MtM m → MtM m) := by
  unfold mulA
  exact Continuous.matrix_mul (A := fun p : MtM m × MtM m => (Matrix.of p.1 : Mx m))
    (B := fun p : MtM m × MtM m => (Matrix.of p.2 : Mx m)) continuous_fst continuous_snd

theorem isUnit_det {G : Set (Mx m)} (hG : IsMatGroup G) {a : Mx m} (ha : a ∈ G) : IsUnit a.det :=
  Matrix.isUnit_det_of_right_inverse (hG.2.2.2 a ha).2

def amb (G : Set (Mx m)) : Set (MtM m) := {x | Matrix.of x ∈ G}

theorem amb_closed {G : Set (Mx m)} (hG : IsMatGroup G) : IsClosed (amb G) := hG.1

def Grp (G : Set (Mx m)) (_hG : IsMatGroup G) : Type := {x : MtM m // x ∈ amb G}

variable {G : Set (Mx m)} {hG : IsMatGroup G}

instance : TopologicalSpace (Grp G hG) := inferInstanceAs (TopologicalSpace {x : MtM m // x ∈ amb G})
instance : MeasurableSpace (Grp G hG) := inferInstanceAs (MeasurableSpace {x : MtM m // x ∈ amb G})
instance : BorelSpace (Grp G hG) := inferInstanceAs (BorelSpace {x : MtM m // x ∈ amb G})
instance : SecondCountableTopology (Grp G hG) :=
  inferInstanceAs (SecondCountableTopology {x : MtM m // x ∈ amb G})

def inc (x : Grp G hG) : MtM m := x.1

theorem inc_mem (x : Grp G hG) : Matrix.of (inc x) ∈ G := x.2

theorem inc_cont : Continuous (inc : Grp G hG → MtM m) := continuous_subtype_val

theorem inc_closedEmb : IsClosedEmbedding (inc : Grp G hG → MtM m) :=
  (amb_closed hG).isClosedEmbedding_subtypeVal

theorem inc_memb : MeasurableEmbedding (inc : Grp G hG → MtM m) :=
  MeasurableEmbedding.subtype_coe (amb_closed hG).measurableSet

theorem range_inc : Set.range (inc : Grp G hG → MtM m) = amb G := Subtype.range_coe

instance : LocallyCompactSpace (Grp G hG) := inc_closedEmb.locallyCompactSpace

instance : Group (Grp G hG) where
  mul a b := ⟨mulA (a.1, b.1), hG.2.2.1 _ a.2 _ b.2⟩
  one := ⟨(1 : Mx m), hG.2.1⟩
  inv a := ⟨invA a.1, (hG.2.2.2 _ a.2).1⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mx m) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mx m))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mx m))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mx m) (isUnit_det hG a.2))

theorem inc_mul (a b : Grp G hG) : inc (a * b) = lmulQ (Matrix.of (inc a)) (inc b) := rfl

instance : IsTopologicalGroup (Grp G hG) where
  continuous_mul := by
    refine Continuous.subtype_mk (mulA_cont.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invA_contOn.comp_continuous continuous_subtype_val (fun x => (isUnit_det hG x.2).ne_zero)

def pull (hG : IsMatGroup G) (μ : Measure (MtM m)) : Measure (Grp G hG) := μ.comap inc

theorem map_pull (μ : Measure (MtM m)) (h : μ {x | Matrix.of x ∉ G} = 0) : (pull hG μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)

theorem pull_left (μ : Measure (MtM m)) (h : ∀ a ∈ G, μ.map (lmulQ a) = μ) : (pull hG μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulQ (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun n : Measure (MtM m) => n (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulQ_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
  rw [← e1, e2]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · show g * (g⁻¹ * z) ∈ s
      rw [mul_inv_cancel_left]; exact hz
    · rw [inc_mul, hzx]
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mx m) (Matrix.of x : Mx m)
        (isUnit_det hG (inc_mem g))

theorem pull_sigmaFinite (μ : Measure (MtM m)) [SigmaFinite μ] : SigmaFinite (pull hG μ) := by
  refine ⟨⟨⟨fun n => inc ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem factor_pos_lt_top {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] (h0 : μ ≠ 0)
    (c : ℝ≥0∞) (h : μ = c • ν) : 0 < c ∧ c < ⊤ := by
  refine ⟨pos_iff_ne_zero.2 fun hc => h0 (by rw [h, hc, zero_smul]), lt_top_iff_ne_top.2 fun hc => h0 ?_⟩
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top μ n
  have h2 : μ (spanningSets μ n) = ⊤ * ν (spanningSets μ n) := by
    have := congrArg (fun ρ : Measure X => ρ (spanningSets μ n)) h
    simpa [hc] using this
  by_cases h3 : ν (spanningSets μ n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

def haar0 (hG : IsMatGroup G) : Measure (Grp G hG) := Measure.haar

instance : (haar0 hG).IsHaarMeasure := inferInstanceAs (Measure.IsHaarMeasure Measure.haar)

theorem eq_smul_haar (hG : IsMatGroup G) (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ = c • (haar0 hG).map inc := by
  obtain ⟨h1, h2, h3, h4⟩ := hμ
  have := pull_sigmaFinite (hG := hG) μ
  have := pull_left (hG := hG) μ h4
  have e := Measure.haarMeasure_unique (pull hG μ) (Classical.arbitrary _)
  have e' : μ = (pull hG μ (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Grp G hG)) :
      TopologicalSpace.PositiveCompacts (Grp G hG))) • (haar0 hG).map inc := by
    rw [← Measure.map_smul _ inc_cont.measurable.aemeasurable]
    refine (map_pull (hG := hG) μ h3).symm.trans ?_
    exact congrArg (Measure.map inc) e
  obtain ⟨a, b⟩ := factor_pos_lt_top μ _ h2 _ e'
  exact ⟨_, a, b, e'⟩

theorem haar_unique_locFinite_openPos :
    ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ →
      (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧
      (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧
      ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  intro m G μ hG hμ
  obtain ⟨c, hc0, hct, hc⟩ := eq_smul_haar hG μ hμ
  refine ⟨fun μ' hμ' => ?_, fun K hK _ => ?_, fun U hU hx => ?_⟩
  · obtain ⟨d, hd0, hdt, hd⟩ := eq_smul_haar hG μ' hμ'
    refine ⟨d / c, ENNReal.div_pos hd0.ne' hct.ne, ENNReal.div_lt_top hdt.ne hc0.ne', ?_⟩
    rw [hd, hc, smul_smul, ENNReal.div_mul_cancel hc0.ne' hct.ne]
  · rw [hc, Measure.smul_apply, smul_eq_mul, inc_memb.map_apply]
    exact ENNReal.mul_lt_top hct (inc_closedEmb.isCompact_preimage hK).measure_lt_top
  · obtain ⟨x, hxU, hxG⟩ := hx
    rw [hc, Measure.smul_apply, smul_eq_mul, inc_memb.map_apply]
    exact ENNReal.mul_pos hc0.ne' ((hU.preimage inc_cont).measure_ne_zero _ ⟨⟨x, hxG⟩, hxU⟩)

end GlobalTheory.MatHaar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPosStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos : ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ → (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧ (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧ ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  first | exact @GlobalTheory.MatHaar.haar_unique_locFinite_openPos | exact GlobalTheory.MatHaar.haar_unique_locFinite_openPos | (intros; apply GlobalTheory.MatHaar.haar_unique_locFinite_openPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensLen

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

section general

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem infDist_add_mem (S : Submodule ℂ V) (x w : V) (hw : w ∈ S) :
    Metric.infDist (x + w) (S : Set V) = Metric.infDist x (S : Set V) := by
  have h := Metric.infDist_image (isometry_add_right w) (x := x) (t := (S : Set V))
  have h2 : (fun y => y + w) '' (S : Set V) = S := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact S.add_mem hy hw
    · intro hv
      exact ⟨v - w, S.sub_mem hv hw, by simp⟩
  rwa [h2] at h

theorem len_eq_of_unitriangular {n : ℕ} (y y' : Fin n → V) (U : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ c a, a < c → U c a = 0) (h1 : ∀ c, U c c = 1) (h : ∀ a, y a = ∑ c, U c a • y' c) (a : Fin n) :
    majorantDistance y a = majorantDistance y' a := by
  have hrest : ∀ (S : Submodule ℂ V) (b : Fin n), (∀ c, c < b → y' c ∈ S) →
      ∑ c ∈ univ.erase b, U c b • y' c ∈ S := by
    intro S b hS
    refine S.sum_mem fun c hc => ?_
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · exact S.smul_mem _ (hS c hcb)
    · exact absurd hcb (Finset.ne_of_mem_erase hc)
    · rw [h0 c b hcb, zero_smul]; exact S.zero_mem
  have hy : ∀ b, y b = y' b + ∑ c ∈ univ.erase b, U c b • y' c := by
    intro b
    rw [h b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h1, one_smul]
  have hspan : Submodule.span ℂ (y '' {b | b < a}) = Submodule.span ℂ (y' '' {b | b < a}) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rw [hy b]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
        (hrest _ b fun c hc => Submodule.subset_span ⟨c, lt_trans hc hb, rfl⟩)
    · rw [Submodule.span_le]
      have key : ∀ b, b < a → y' b ∈ Submodule.span ℂ (y '' {b | b < a}) := by
        intro b
        induction b using WellFoundedLT.induction with
        | ind b ih =>
          intro hb
          rw [eq_sub_of_add_eq (hy b).symm]
          exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
            (hrest _ b fun c hc => ih c hc (lt_trans hc hb))
      rintro _ ⟨b, hb, rfl⟩
      exact key b hb
  unfold majorantDistance
  rw [hspan, hy a]
  exact infDist_add_mem _ _ _ (hrest _ a fun c hc => Submodule.subset_span ⟨c, hc, rfl⟩)

theorem len_pos {n : ℕ} (y : Fin n → V) (hy : LinearIndependent ℂ y) (a : Fin n) : 0 < majorantDistance y a := by
  unfold majorantDistance
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (y '' {b | b < a})) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos ⟨0, Submodule.zero_mem _⟩).1 ?_
  exact hy.notMem_span_image (by simp)

theorem len_zero {n : ℕ} (y : Fin (n + 1) → V) : majorantDistance y 0 = ‖y 0‖ := by
  unfold majorantDistance
  have : y '' {b | b < 0} = ∅ := by simp
  rw [this, Submodule.span_empty, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]

end general

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (g.submatrix (I.1.orderEmbOfFin I.2) id)
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  refine Eq.trans ?_ (h.symm.trans ?_)
  · simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_comm]
    rfl
  · rfl

theorem sum_norm_wedge {n l : ℕ} (f : Fin l → Fin n → ℂ) :
    ∑ J, ‖wedge f J‖ ^ 2 =
      ∏ a, majorantDistance (fun b => (WithLp.toLp 2 (f b) : EuclideanSpace ℂ (Fin n))) a ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula (EuclideanSpace ℂ (Fin n)) l (fun b => WithLp.toLp 2 (f b))
  have h2 := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  have h3 : (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ *
      (Matrix.of fun (i : Fin n) (b : Fin l) => f b i) =
      Matrix.of fun a b => inner ℂ (WithLp.toLp 2 (f a) : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 (f b)) := by
    ext a b
    simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  rw [h3, h] at h2
  apply Complex.ofReal_injective
  rw [h2]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, Complex.mul_conj']
  rfl

theorem sum_norm_sq_eq {n : ℕ} (v : Fin n → ℂ) : ((∑ c, ‖v c‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj']

theorem sum_norm_dual {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) (hu : IsUnit g.det) (f : Fin n → ℂ) :
    ∑ c, ‖(dualM g⁻¹ *ᵥ (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f)) c‖ ^ 2 = ∑ c, ‖(g⁻¹ *ᵥ f) c‖ ^ 2 := by
  have h1 : (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f) = star f ᵥ* H := by
    funext c
    simp [Formalism.QuantumDeterminants.herm, vecMul, dotProduct]
  have h2 : H * g = (g⁻¹)ᴴ * H := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hu,
      conjTranspose_one, Matrix.one_mul]
  have h3 : dualM g⁻¹ *ᵥ (star f ᵥ* H) = star (H *ᵥ (g⁻¹ *ᵥ f)) := by
    rw [dualM, nonsing_inv_nonsing_inv _ hu, mulVec_transpose, vecMul_vecMul, h2, star_mulVec, star_mulVec,
      vecMul_vecMul, hH]
  rw [h1, h3]
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, star_star, star_mulVec, hH, dotProduct_mulVec, vecMul_vecMul, hHH,
    vecMul_one, dotProduct_comm]

theorem fvec_indep (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : LinearIndependent ℂ (Formalism.QuantumDeterminants.fvec k r z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm] at hT
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz0
  have hir : r ≤ i.val := by
    by_contra hlt
    exact hi (hz i (Or.inl (by omega)))
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  by_cases ha : a.val < r
  · have := congrFun hc ⟨a.val, by omega⟩
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha] at this
      simpa using this
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha, if_neg (fun h => hb (Fin.ext h)), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have := congrFun hc i
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir, if_pos (by omega)] at this
      exact (mul_eq_zero.1 this).resolve_right hi
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir,
        if_neg (fun h => hb (Fin.ext (by omega))), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem isUnit_det_of_unitary {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) : IsUnit g.det := by
  have h : (H * (gᴴ * H)) * g = 1 := by rw [Matrix.mul_assoc, hg, hHH]
  exact Matrix.isUnit_det_of_left_inverse h

theorem lengths : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, (∑ J, ‖(cmp (r + 1) g⁻¹ *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z))) J‖ ^ 2 = ∏ a, lenA k r z g a ^ 2) ∧ (∑ c, ‖(dualM g⁻¹ *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0))) c‖ ^ 2 = lenA k r z g 0 ^ 2) ∧ (∀ a, 0 < lenA k r z g a) ∧ ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ a, lenA k r z (s * g) a = lenA k r z g a := by
  intro k r z hz hT g hg
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := isUnit_det_of_unitary hHH hg
  have hl : ∀ g a, lenA k r z g a = majorantDistance (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a := fun _ _ => rfl
  refine ⟨?_, ?_, fun a => ?_, fun s hs a => ?_⟩
  · rw [cmp_mulVec_wedge, sum_norm_wedge]
    rfl
  · rw [hl, len_zero, EuclideanSpace.norm_sq_eq]
    exact sum_norm_dual _ g hH hHH hg hu _
  · rw [hl]
    refine len_pos _ ?_ a
    have hinj : Function.Injective (g⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det g hu))
    have h1 := (fvec_indep k r z hz hT).map' (Matrix.mulVecLin g⁻¹) (LinearMap.ker_eq_bot.2 hinj)
    exact h1.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  · obtain ⟨U, h0, h1, hF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    have hsu : IsUnit s.det := isUnit_det_of_unitary hHH (Formalism.QuantumDeterminants.Sset_UH hs)
    rw [hl, hl]
    symm
    refine len_eq_of_unitriangular _ _ U h0 h1 (fun b => ?_) a
    have hcol : s *ᵥ Formalism.QuantumDeterminants.fvec k r z b = ∑ c, U c b • Formalism.QuantumDeterminants.fvec k r z c := by
      funext i
      have := congrFun (congrFun hF i) b
      simpa [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, mulVec, dotProduct, mul_comm] using this
    have h2 : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b = (s * g)⁻¹ *ᵥ (s *ᵥ Formalism.QuantumDeterminants.fvec k r z b) := by
      rw [mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hsu, Matrix.mul_one]
    rw [h2, hcol, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, WithLp.toLp_sum, WithLp.toLp_smul]

end GlobalTheory.TensLen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace DualFRep

theorem gram_transpose (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᵀ = Formalism.QuantumDeterminants.Hpk k r := by
  have h := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [conjTranspose_apply] at h1
  rw [transpose_apply, ← h1]
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> simp

variable {n : ℕ}

theorem left_inv {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    H * gᴴ * H * g = 1 := by
  calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, h2]

theorem inv_eq {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H :=
  Matrix.inv_eq_left_inv (left_inv h2 hg)

theorem entry_le {k r : ℕ} (g : Mx k r) (a b : Fin (2 * r + k + 1)) : ‖g a b‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g a b) ≤ ∑ j, Complex.normSq (g a j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (g a j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

end DualFRep


open DualFRep in
theorem isFRep_dualM (k r : ℕ) : IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  have h1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 := gram_transpose k r
  have hmem : ∀ g ∈ GG k r, gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := fun g hg => hg
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 h3 hmem ⊢
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dualM]
  · intro g hg h hh
    simp only [dualM]
    rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  · intro g hg
    have key : g⁻¹ * H * (g⁻¹)ᴴ = H := by
      rw [inv_eq h2 (hmem g hg)]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1]
      calc H * gᴴ * H * H * (H * (g * H)) = H * (gᴴ * (H * H) * H * g) * H := by
            simp only [Matrix.mul_assoc]
        _ = H := by rw [h2, Matrix.mul_one, hmem g hg, h2, Matrix.one_mul]
    have e : ((g⁻¹)ᵀ)ᴴ = ((g⁻¹)ᴴ)ᵀ := rfl
    have := congrArg Matrix.transpose key
    rw [transpose_mul, transpose_mul, h3] at this
    simp only [dualM]
    rw [e, Matrix.mul_assoc, this]
  · intro i j
    have hc : Continuous (fun g : Mx k r => (H * gᴴ * H) j i) := by
      have : Continuous (fun g : Mx k r => H * gᴴ * H) :=
        (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
      exact this.matrix_elem j i
    refine hc.continuousOn.congr ?_
    intro g hg
    simp only [dualM, transpose_apply]
    rw [inv_eq h2 (hmem g hg)]
  · refine ⟨∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖, ?_⟩
    intro g hg i j
    simp only [dualM, transpose_apply, pow_one]
    rw [inv_eq h2 (hmem g hg)]
    have hN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc ‖(H * gᴴ * H) j i‖ = ‖∑ b, ∑ a, H j a * star (g b a) * H b i‖ := by
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
      _ ≤ ∑ b, ∑ a, ‖H j a * star (g b a) * H b i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
      _ ≤ ∑ b, ∑ a, ‖H j a‖ * ‖H b i‖ * B.gN g := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_mul, norm_star, mul_right_comm]
          exact mul_le_mul_of_nonneg_left (entry_le g b a) (by positivity)
      _ = (∑ b, ∑ a, ‖H j a‖ * ‖H b i‖) * B.gN g := by simp only [Finset.sum_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact Finset.single_le_sum
            (f := fun p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖)
            (fun p _ => by positivity) (Finset.mem_univ (i, j))
  · intro g hg hu
    have hl : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
    have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv hl
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [dualM]
    rw [hinv]
    have e : star ((star g)ᵀ) = gᵀ := by
      ext a b
      simp [Matrix.star_apply]
    rw [e, ← transpose_mul, (Matrix.mem_unitaryGroup_iff).1 hu, transpose_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRepStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFRep_dual_standard_unitaryRep : ∀ (k r : ℕ), IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  first | exact @GlobalTheory.isFRep_dualM | exact GlobalTheory.isFRep_dualM | (intros; apply GlobalTheory.isFRep_dualM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem thresholds_of_gapOK : ∀ (k r : ℕ) (h : ℝ), GapOK k r h →
    JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  intro k r h hg
  obtain ⟨hk, -, -, h4⟩ := hg
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hA : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 2 ≤ aOf r h - 1 := by linarith
  have hN : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold JF.TransportedAlt
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ (by positivity)]
    nlinarith
  · have hAB : B.AB k r = AG k r / 2 + 1 := by unfold B.AB AG; ring
    rw [hAB]
    linarith
  · linarith
  · linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapConditionStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decayThresholds_of_spectralGapCondition : ∀ (k r : ℕ) (h : ℝ), GapOK k r h → JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  first | exact @GlobalTheory.thresholds_of_gapOK | exact GlobalTheory.thresholds_of_gapOK | (intros; apply GlobalTheory.thresholds_of_gapOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselLine

theorem psi_const : PsiConst := by
  intro k r z c g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem bessel_line : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  intro hH k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l l₁ hDS hS hl hnz hl₁
  obtain ⟨w, hw, hne⟩ := hnz
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hc : Formalism.QuantumDeterminants.cStd ≠ 0 := by
    unfold Formalism.QuantumDeterminants.cStd
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact Formalism.FourierDecayAlt.P.DDSmoothness.jsz_line hH.1.2.2.2 psi_const hDS.1 hDS.2 hz hT hc hπ hl hl₁ hw hne

end GlobalTheory.BesselLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowthStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_side_growth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  first | exact @GlobalTheory.BesselLine.bessel_line | exact GlobalTheory.BesselLine.bessel_line | (intros; apply GlobalTheory.BesselLine.bessel_line <;> assumption)
end
end
