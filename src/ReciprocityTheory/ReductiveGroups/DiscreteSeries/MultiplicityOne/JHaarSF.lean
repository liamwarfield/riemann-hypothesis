module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
open MeasureTheory
open scoped NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def HaarUniqueSF : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ₀ μ : Measure (Mt k r)), IsClosedSubgroup U → Formalism.FourierDecayAlt.B.IsHaarOn U μ₀ →
    Formalism.MainNotions.S.IsHaarOn U μ → ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • μ₀

theorem haarUniqueSF' : HaarUniqueSF := by
  intro k r U μ₀ μ hU h₀ hμ
  have : Fact (IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hσ, hne, hconc, hleft⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨h₀.finite_compact⟩
  have hcμ : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hconc
  have hcν : μ₀ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := h₀.conc
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ₀
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ hcμ hleft
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ₀ hcν h₀.left
  have hμS : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => hne (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, h0, Measure.map_zero])
  have hνS : μ₀.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => h₀.ne_zero (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν, h0, Measure.map_zero])
  obtain ⟨c, hc0, hc⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hμS hνS
  refine ⟨c, hc0, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, hc, Measure.map_smul,
    HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν]
  exact (HaarSigmaFiniteUniqueness.mEmb (U := U)).measurable.aemeasurable

theorem haarUniqueSF (_h : UnitaryGroupStructuralFacts) : HaarUniqueSF := haarUniqueSF'

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem bc_continuous_ell (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ (fun a _ => ?_)
  split_ifs <;> fun_prop

theorem bc_norm_psiD {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    ‖psiD D m‖ = 1 := by
  simp [psiD, psi, Complex.norm_exp]

theorem stBeConv (h : UnitaryGroupStructuralFacts) : StBeConv := by
  intro k r Wp _ _ _ D X hD hsq b hb u v ⟨C, hC⟩
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGL, -, -, -, hCG, hCN, hCW, -⟩, -⟩ := id h
  have sW := bc_isHaarOn_sigmaFinite D.haarW
  have sN := bc_isHaarOn_sigmaFinite D.haarN
  have hint := (stSInt h k r Wp D hD b (bc_AB_le_of b hb)).const_mul C
  set S : Set (Mt k r × Mt k r) := {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧
    (Matrix.of p.2 : Mat k r) ∈ Nset k r} with hSdef
  have aeS : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ S :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  have hinvW : ∀ x ∈ UWset k r D.z, x⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem
  have hnorm : ∀ p ∈ S, ‖beInt D X u v p‖ ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by
    intro p hp
    have hG : (Matrix.of p.2 : Mat k r) * Matrix.of p.1 ∈ GV k r := (hCG k r).mul_mem _ hp.2.1 _ hp.1.1
    have h1 := hC _ hG
    have hπ : ‖D.π (Matrix.of p.1 : Mat k r)⁻¹‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
      rw [D.π_unitary _ (hinvW _ hp.1) w, one_mul]
    unfold beInt
    rw [norm_smul, norm_mul, norm_star, bc_norm_psiD, mul_one]
    calc ‖mc X u v (Matrix.of p.2 * Matrix.of p.1)‖ * ‖D.π (Matrix.of p.1 : Mat k r)⁻¹‖
        ≤ ‖mc X u v (Matrix.of p.2 * Matrix.of p.1)‖ * 1 :=
          mul_le_mul_of_nonneg_left hπ (norm_nonneg _)
      _ ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by rw [mul_one]; exact h1
  refine Integrable.mono' hint ?_ ?_
  · have cW : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} := (hCW k r D.z).closed
    have cN : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Nset k r} := (hCN k r).closed
    have hSmeas : MeasurableSet S :=
      (cW.measurableSet.preimage measurable_fst).inter (cN.measurableSet.preimage measurable_snd)
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => mc X u v (Matrix.of p.2 * Matrix.of p.1)) S := by
      have hm : ContinuousOn (fun p : Mt k r × Mt k r => X.σ (Matrix.of p.2 * Matrix.of p.1) u) S :=
        (X.rep.2.2 u).comp (bc_continuous_mulM.comp continuous_swap).continuousOn
          (fun p hp => (hCG k r).mul_mem _ hp.2.1 _ hp.1.1)
      exact continuousOn_const.inner hm
    have c2 : Continuous (fun p : Mt k r × Mt k r => star (psiD D (Matrix.of p.2))) := by
      unfold psiD psi
      exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul ((bc_continuous_ell k r D.z).comp continuous_snd)))))).star
    have c3 : ContinuousOn (fun p : Mt k r × Mt k r => D.π (Matrix.of p.1 : Mat k r)⁻¹) S := by
      refine D.π_cont.comp (f := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)⁻¹) ?_
        (fun p hp => hinvW _ hp.1)
      intro p hp
      apply ContinuousAt.continuousWithinAt
      have hdet : (Matrix.of p.1 : Mat k r).det ≠ 0 := ((hCW k r D.z).unit _ hp.1).ne_zero
      have hi : ContinuousAt (fun x : Mat k r => x⁻¹) (Matrix.of p.1) :=
        continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
      exact hi.comp (f := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) continuous_fst.continuousAt
    have hcont : ContinuousOn (beInt D X u v) S := (c1.mul c2.continuousOn).smul c3
    have hm := hcont.aestronglyMeasurable (μ := D.μW.prod D.μN) hSmeas
    rwa [Measure.restrict_eq_self_of_ae_mem aeS] at hm
  · filter_upwards [aeS] with p hp
    exact hnorm p hp

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepro
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem second_joint_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2) (D.μG.prod (D.μW.prod D.μN)) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  obtain ⟨Cu, hCu0, hCu⟩ := dec_adj X hCG hL ha hu
  obtain ⟨Cv, hCv0, hCv⟩ := dec_adj X hCG hL ha hv
  have hform : ∀ q ∈ EE k r D.z,
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2 =
        ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • ((⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ *
          star (psiD D (Matrix.of q.2.2))) • ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))) := by
    intro q hq
    obtain ⟨_, hh, _⟩ := hq
    simp only [beInt, mc]
    rw [pi_inv D hCW hh]
  have hcont : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2) (EE k r D.z) := by
    refine ContinuousOn.congr ?_ hform
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (cont_sig_fst X D.z X.w)).smul
      (((ContinuousOn.inner (𝕜 := ℂ) (cont_sig_fst X D.z X.w) (representation_continuousOn_product X D.z hCG u)).mul
        (cont_psi D).continuousOn).smul (cont_adj_pi D))
  have hmeas : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2)
      (D.μG.prod (D.μW.prod D.μN)) := by
    have := hcont.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) (EE_closed D.z hCG hCW hCN).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_EE D)] at this
  have hbd : ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)),
      ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2‖ ≤
        Cv * Cu * KH k r ^ (X.a / 2) * KH k r ^ (X.a / 2) *
          (gN (Matrix.of q.1) ^ (-(X.a / 2)) * gN (Matrix.of q.2.2 * Matrix.of q.2.1) ^ (-(X.a / 2))) := by
    filter_upwards [ae_EE D] with q hq
    rw [hform q hq]
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have hsi := inv_mem_G hCG hs
    have A1 : ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ ≤ Cv * gN (Matrix.of q.1) ^ (-X.a) := hCv _ hy
    have e : ⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ =
        ⟪X.σ ((Matrix.of q.2.2 * Matrix.of q.2.1)⁻¹ * Matrix.of q.1) X.w, u⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← sig_inv X hCG hs, X.rep.1.2 _ hsi _ hy]; rfl
    have A2 : ‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ ≤
        Cu * gN ((Matrix.of q.2.2 * Matrix.of q.2.1)⁻¹ * Matrix.of q.1) ^ (-X.a) := by
      rw [e, norm_inner_symm]; exact hCu _ (hCG.mul_mem _ hsi _ hy)
    have B := second_pointwise_bound hCG hL ha hs hy A1 A2 (norm_nonneg _) (norm_nonneg _) hCv0 hCu0
    have hT : ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact opNorm_le_one_of_iso (D.π_unitary _ hh)
    have hψ : ‖star (psiD D (Matrix.of q.2.2))‖ ≤ 1 := by rw [norm_star]; exact norm_psi_le _ _ _
    rw [norm_smul, norm_smul, norm_mul]
    calc ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          (‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ *
          ‖star (psiD D (Matrix.of q.2.2))‖ * ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖)
        ≤ ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          (‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ * 1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hψ (norm_nonneg _)) hT
            (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          ‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ := by ring
      _ ≤ _ := B
  exact ((hIG.mul_prod hIS).const_mul (Cv * Cu * KH k r ^ (X.a / 2) * KH k r ^ (X.a / 2))).mono' hmeas hbd

theorem reproducing_snd (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {d : ℝ} (hd : IsFdegG D X d) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    beOp D X u v = (d : ℂ) •
      ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  have hint := second_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv
  have hpt : ∀ p : Mt k r × Mt k r,
      ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of y) X.w) p ∂D.μG =
        ((d : ℂ)⁻¹) • beInt D X u v p := by
    intro p
    simp only [beInt, smul_smul]
    rw [integral_smul_const]
    congr 1
    have e : ∀ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ *
        (mc X u (X.σ (Matrix.of y) X.w) (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) =
        ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of p.2 * Matrix.of p.1) u⟫_ℂ * ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ *
          star (psiD D (Matrix.of p.2)) := by
      intro y; rw [mc]; ring
    simp_rw [e]
    rw [integral_mul_const, schur_pt D X hd v (X.σ (Matrix.of p.2 * Matrix.of p.1) u), mc]
    ring
  have hsw := swap_smul D.μG (D.μW.prod D.μN) (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ)
    (fun (y : Mt k r) (p : Mt k r × Mt k r) => beInt D X u (X.σ (Matrix.of y) X.w) p) hint
  have key : ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG =
      ((d : ℂ)⁻¹) • beOp D X u v := by
    simp only [beOp]
    rw [hsw]
    simp_rw [hpt]
    rw [integral_smul]
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  rw [key, smul_smul, mul_inv_cancel₀ hd0, one_smul]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReproducingFormula

section

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_setup (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a) :
    IsClosedSubgroup (GV k r) ∧ IsClosedSubgroup (UWset k r D.z) ∧ IsClosedSubgroup (Nset k r) ∧
      (∀ g ∈ GV k r, 1 ≤ gN g) ∧ 0 ≤ X.a ∧
      Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG ∧
      Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
        (D.μW.prod D.μN) := by
  have h' := h
  obtain ⟨hB2, -⟩ := h'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCG, hCN, hCW, -⟩ := hB2
  have ha : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) haM
  have hAB := AB_le_half k r haM
  exact ⟨hCG k r, hCW k r D.z, hCN k r, hGL k r, ha, int_G hGI D.μG D.haarG hAB,
    stSInt h k r Wp D hD (X.a / 2) hAB⟩

end

theorem stRepro (h : UnitaryGroupStructuralFacts) : StRepro := by
  intro k r Wp _ _ _ D X hD _ haM d hd u hu v hv
  obtain ⟨hCG, hCW, hCN, hL, ha, hIG, hIS⟩ := repro_setup h D X hD haM
  exact ⟨reproducing_fst D X hCG hCW hCN hL ha hIG hIS hd hu hv, reproducing_snd D X hCG hCW hCN hL ha hIG hIS hd hu hv⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoG
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiM_inv' {k r : ℕ} (u : Formalism.REAL.UJ (epsG k r)) : psiM k r u⁻¹ = (psiM k r u)⁻¹ := by
  exact (Matrix.inv_eq_right_inv (by rw [← psiM_mul, mul_inv_cancel, psiM_one])).symm

theorem stDichoG (h : UnitaryGroupStructuralFacts) : StDichoG := by
  intro k r Wp _ _ _ D X hD hSq γ hγ
  obtain ⟨hgbG, -, -, -, hanti', hinv', hμG, -, -⟩ := stInvGroup h k r Wp D X hD hSq γ hγ
  have hG := D.haarG
  haveI := nuG_left hG
  haveI := nuG_inv hG
  haveI := nuG_openPos hG
  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun e => by have hw := X.w_norm; simp [e] at hw⟩⟩
  have inj := (isClosedEmbedding_psiM k r).injective

  have hex : ∀ u : Formalism.REAL.UJ (epsG k r), ∃ u', psiM k r u' = gbar k r γ (psiM k r u) := by
    intro u
    have hm : gbar k r γ (psiM k r u) ∈ Set.range (psiM k r) := by
      rw [range_psiM]
      exact hgbG _ (psiM_mem u)
    exact hm
  choose G hGs using hex
  let θ : Formalism.REAL.UJ (epsG k r) → Formalism.REAL.UJ (epsG k r) := fun u => (G u)⁻¹
  have hθ : ∀ u, psiM k r (θ u) = th k r γ (psiM k r u) := by
    intro u
    simp only [θ, th, psiM_inv', hGs]
  have hanti : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply inj
    rw [hθ, psiM_mul, psiM_mul, hθ, hθ]
    exact hanti' _ (psiM_mem a) _ (psiM_mem b)
  have hinv : ∀ u, θ (θ u) = u := by
    intro u
    apply inj
    rw [hθ, hθ]
    exact hinv' _ (psiM_mem u)
  have hgbar : Continuous (gbar k r γ) := by
    unfold gbar
    exact ((continuous_const.matrix_mul ((((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_map Complex.continuous_conj))).matrix_mul continuous_const)
  have hGc : Continuous G := by
    rw [(isClosedEmbedding_psiM k r).toIsEmbedding.continuous_iff]
    have e : psiM k r ∘ G = gbar k r γ ∘ psiM k r := funext hGs
    rw [e]
    exact hgbar.comp (continuous_psiM k r)
  have hθc : Continuous θ := continuous_inv.comp hGc
  have hE := measurableEmbedding_psiG k r
  let T : Mt k r → Mt k r := fun x => fun i j => th k r γ (Matrix.of x) i j
  have hT : AEMeasurable T D.μG := by
    have hc : Continuous (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) := by
      exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply i).comp (hgbar.comp continuous_id))
    exact (InvGrp.measurable_invM.comp hc.measurable).aemeasurable
  have hcomp : psiG k r ∘ θ = T ∘ psiG k r := by
    funext u
    show Matrix.of.symm (psiM k r (θ u)) = fun i j => th k r γ (Matrix.of (psiG k r u)) i j
    rw [of_psiG, hθ]
    rfl
  have key : ((nuG D.μG).map θ).map (psiG k r) = (nuG D.μG).map (psiG k r) := by
    rw [Measure.map_map hE.measurable hθc.measurable, hcomp,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [map_nuG hG]; exact hT) hE.measurable.aemeasurable,
      map_nuG hG]
    exact hμG
  have hmap : (nuG D.μG).map θ = nuG D.μG := by
    calc (nuG D.μG).map θ = (((nuG D.μG).map θ).map (psiG k r)).comap (psiG k r) := (hE.comap_map _).symm
      _ = ((nuG D.μG).map (psiG k r)).comap (psiG k r) := by rw [key]
      _ = nuG D.μG := hE.comap_map _
  have hSR : Formalism.MainNotions.BridgeCSchur.SqRep (nuG D.μG)
      (fun u => X.σ (psiM k r u)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [psiM_one]; exact X.rep.1.1
    · intro a b
      rw [psiM_mul]; exact X.rep.1.2 _ (psiM_mem a) _ (psiM_mem b)
    · intro g v
      exact X.rep.2.1 _ (psiM_mem g) v
    · intro v
      exact (X.rep.2.2 v).comp_continuous (continuous_psiM k r) psiM_mem
    · intro v w
      have hs := hSq v w
      rw [← map_nuG hG] at hs
      have hs' := (hE.memLp_map_measure_iff).mp hs
      convert hs' using 1
      simp [mc, Function.comp_def, of_psiG]
  have hI : ∀ S : Submodule ℂ X.Hs, IsClosed (S : Set X.Hs) →
      (∀ u : Formalism.REAL.UJ (epsG k r), ∀ v ∈ S, X.σ (psiM k r u) v ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    apply X.irr S hS
    intro g hg v hv
    obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
    exact hinv u v hv
  rcases schurDichotomy (Formalism.REAL.UJ (epsG k r)) (nuG D.μG) X.Hs θ (fun u => X.σ (psiM k r u)) hθc hanti hinv
      hmap hSR.one hSR.mul hSR.iso hSR.cont hSR.sq hI with h0 | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← map_nuG hG, hE.integral_map]
    simp only [of_psiG, ← hθ]
    exact h0 x y x' y'
  · right
    refine ⟨C, ?_, ?_⟩
    · intro g hg x y
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ]
      exact hC1 u x y
    · intro g hg v
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ, ← psiM_inv']
      exact hC2 u v

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoW
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stDichoW (h : UnitaryGroupStructuralFacts) : StDichoW := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -, -, -, hHI, -, -, -, hClW, -⟩ := h.1
  intro k r Wp _ _ _ D X hD hX γ hγ
  obtain ⟨-, -, hgW, -, hth_mul, hth_th, -, -, hμgbar⟩ := stInvGroup h k r Wp D X hD hX γ hγ
  by_cases hWp : Subsingleton Wp
  · left
    intro x y x' y'
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  have : Nontrivial Wp := not_subsingleton_iff_nontrivial.1 hWp
  have hU : IsClosedSubgroup (UWset k r D.z) := hClW k r D.z
  have hμW := D.haarW
  have hme := MatrixSubsetMeasurability.me_val hU
  have hleft : (MatrixSubsetMeasurability.nu hU D.μW).IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμW
  have hinvI : (MatrixSubsetMeasurability.nu hU D.μW).IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμW
  have hmapnu : (MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := MatrixSubsetMeasurability.map_nu hμW
  have hνuniv : MatrixSubsetMeasurability.nu hU D.μW Set.univ = 1 := by
    have e := congrArg (fun m : Measure (Mt k r) => m Set.univ) hmapnu
    simp only [Measure.map_apply hme.measurable MeasurableSet.univ, Set.preimage_univ] at e
    rw [e, hD.mass]
  have hcpt : IsCompact {x : Mt k r | Matrix.of x ∈ UWset k r D.z} := hCW k r D.z D.z_mem D.T_pos
  have : CompactSpace (MatrixSubsetMeasurability.SG hU) := isCompact_iff_compactSpace.1 hcpt
  have hpos : (MatrixSubsetMeasurability.nu hU D.μW).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by rw [hνuniv]; exact one_ne_zero)
  have hfin : IsFiniteMeasure (MatrixSubsetMeasurability.nu hU D.μW) := ⟨by rw [hνuniv]; exact ENNReal.one_lt_top⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MatrixSubsetMeasurability.SG hU → MatrixSubsetMeasurability.SG hU, θ = fun g =>
      (MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)))⁻¹ := ⟨_, rfl⟩
  have hmθ : ∀ g, MatrixSubsetMeasurability.mat (θ g) = th k r γ (MatrixSubsetMeasurability.mat g) := by
    intro g
    simp only [hθ]
    rw [MatrixSubsetMeasurability.mat_inv, MatrixSubsetMeasurability.mat_mk]
    rfl
  have hgc : Continuous fun A : Mat k r => gbar k r γ A := by
    have h1 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A := continuous_const.matrix_mul continuous_id
    have h2 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A * embWb k r γ := h1.matrix_mul continuous_const
    have h3 : Continuous fun A : Mat k r => ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      h2.matrix_map Complex.continuous_conj
    have h4 : Continuous fun A : Mat k r =>
        embWb k r γ * ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      continuous_const.matrix_mul h3
    exact h4.matrix_mul continuous_const
  have hgbc : Continuous fun g : MatrixSubsetMeasurability.SG hU =>
      MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)) := by
    apply continuous_induced_rng.2
    exact hgc.comp MatrixSubsetMeasurability.continuous_mat
  have hθc : Continuous θ := by
    rw [hθ]
    exact hgbc.inv
  have hθmul : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply MatrixSubsetMeasurability.ext'
    rw [MatrixSubsetMeasurability.mat_mul, hmθ, hmθ, hmθ, MatrixSubsetMeasurability.mat_mul]
    exact hth_mul _ (MatrixSubsetMeasurability.mat_mem a).1 _ (MatrixSubsetMeasurability.mat_mem b).1
  have hθθ : ∀ g, θ (θ g) = g := by
    intro g
    apply MatrixSubsetMeasurability.ext'
    rw [hmθ, hmθ]
    exact hth_th _ (MatrixSubsetMeasurability.mat_mem g).1
  have hgF : Measurable fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp (hgc.comp continuous_id))
  have hθμ : (MatrixSubsetMeasurability.nu hU D.μW).map θ = MatrixSubsetMeasurability.nu hU D.μW := by
    have hval : (fun g : MatrixSubsetMeasurability.SG hU => g.1) ∘ θ =
        (invM ∘ fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) ∘ fun g : MatrixSubsetMeasurability.SG hU => g.1 := by
      funext g
      exact hmθ g
    have key : ((MatrixSubsetMeasurability.nu hU D.μW).map θ).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := by
      rw [Measure.map_map hme.measurable hθc.measurable, hval,
        ← Measure.map_map (InvGrp.measurable_invM.comp hgF) hme.measurable, hmapnu,
        ← Measure.map_map InvGrp.measurable_invM hgF, hμgbar]
      exact hHI k r _ D.μW hU hμW
    rw [← hme.comap_map ((MatrixSubsetMeasurability.nu hU D.μW).map θ), key]
    rfl
  have hπc : Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) :=
    D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat fun g => MatrixSubsetMeasurability.mat_mem g
  have hρ1 : D.π (MatrixSubsetMeasurability.mat (1 : MatrixSubsetMeasurability.SG hU)) = 1 := by
    rw [MatrixSubsetMeasurability.mat_one]
    exact D.π_rep.1
  have hρmul : ∀ a b : MatrixSubsetMeasurability.SG hU,
      D.π (MatrixSubsetMeasurability.mat (a * b)) = (D.π (MatrixSubsetMeasurability.mat a)).comp (D.π (MatrixSubsetMeasurability.mat b)) := by
    intro a b
    rw [MatrixSubsetMeasurability.mat_mul]
    exact D.π_rep.2 _ (MatrixSubsetMeasurability.mat_mem a) _ (MatrixSubsetMeasurability.mat_mem b)
  have hρn : ∀ (g : MatrixSubsetMeasurability.SG hU) (v : Wp), ‖D.π (MatrixSubsetMeasurability.mat g) v‖ = ‖v‖ :=
    fun g v => D.π_unitary _ (MatrixSubsetMeasurability.mat_mem g) v
  have hρc : ∀ v : Wp, Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) v :=
    fun v => hπc.clm_apply continuous_const
  have hmem : ∀ v w : Wp, MemLp (fun g : MatrixSubsetMeasurability.SG hU => ⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ) 2
      (MatrixSubsetMeasurability.nu hU D.μW) := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hρc v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ‖ ≤ ‖w‖ * ‖D.π (MatrixSubsetMeasurability.mat g) v‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖v‖ := by rw [hρn]
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) →
      (∀ (g : MatrixSubsetMeasurability.SG hU), ∀ v ∈ S, D.π (MatrixSubsetMeasurability.mat g) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    refine hD.irr S hS fun g hg v hv => ?_
    have e := hinv (MatrixSubsetMeasurability.mk hU g hg) v hv
    rwa [MatrixSubsetMeasurability.mat_mk] at e
  rcases schurDichotomy (MatrixSubsetMeasurability.SG hU) (MatrixSubsetMeasurability.nu hU D.μW) Wp θ (fun g => D.π (MatrixSubsetMeasurability.mat g))
      hθc hθmul hθθ hθμ hρ1 hρmul hρn hρc hmem hirr with hL | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← hmapnu, hme.integral_map]
    have e := hL x y x' y'
    simp only [hmθ] at e
    exact e
  · right
    refine ⟨C, fun g hg x y => ?_, fun g hg v => ?_⟩
    · have e := hC1 (MatrixSubsetMeasurability.mk hU g hg) x y
      simp only [hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e
    · have e := hC2 (MatrixSubsetMeasurability.mk hU g hg) v
      simp only [MatrixSubsetMeasurability.mat_inv, hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
