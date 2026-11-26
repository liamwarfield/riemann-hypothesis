module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.MeasureBoxRingEquivLe
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.MeasureBoxGLLe
open MeasureTheory Measure Set Matrix
open scoped NNReal ENNReal
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace PositivityTheory.Rg.Rs.boxvol

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ}

def pairSum (m : ℕ) (x : Fin (m + 1) → ℝ) : ℝ :=
  ∑ p : StrictUpperIndex (Fin (m + 1)), (x p.1.1 - x p.1.2)

def boxGL (ω : Set (GL (Fin (m + 1)) 𝕜)) (B : ℝ) (x : Fin (m + 1) → ℝ) : Set (GL (Fin (m + 1)) 𝕜) :=
  {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k : unitaryGroup (Fin (m + 1)) 𝕜,
    g = b * (diagPosOf ⟨fun i => Real.exp (x i + y i), fun _ => Real.exp_pos _⟩ : GL (Fin (m + 1)) 𝕜) *
      Unitary.toUnits k}

theorem measure_boxGL_le [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]
    [MeasurableSpace (unitaryGroup (Fin (m + 1)) 𝕜)] [BorelSpace (unitaryGroup (Fin (m + 1)) 𝕜)]
    (μ : Measure (GL (Fin (m + 1)) 𝕜))
    (hANK : ∀ (μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜)) [μK.IsHaarMeasure]
      (μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜)) [μA.IsHaarMeasure]
      (μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜)) [μN.IsHaarMeasure],
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA)
    {ω : Set (GL (Fin (m + 1)) 𝕜)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).IsUpperTriangular) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : Fin (m + 1) → ℝ,
      μ (boxGL ω B x) ≤ C * ENNReal.ofReal (Real.exp (-((Module.finrank ℝ 𝕜 : ℝ) * pairSum m x))) := by
  classical
  set e : ℝ := (Module.finrank ℝ 𝕜 : ℝ) with he
  have he0 : 0 ≤ e := Nat.cast_nonneg _
  have hent : ∀ i j, Continuous fun g : GL (Fin (m + 1)) 𝕜 =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i j := fun i j =>
    (continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜))
  have hb0 : ∀ b ∈ ω, ∀ i, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i ≠ 0 := fun b hb i =>
    apply_self_ne_zero_of_isUpperTriangular (hωB b hb) i

  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, ∀ b ∈ ω, ∀ i,
      |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖| ≤ B₀ := by
    have hcont : ContinuousOn (fun b : GL (Fin (m + 1)) 𝕜 => ∑ i,
        |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖|) ω :=
      continuousOn_finsetSum _ fun i _ => ((hent i i).norm.continuousOn.log
        fun b hb => norm_ne_zero_iff.2 (hb0 b hb i)).abs
    obtain ⟨M, hM⟩ := hω.exists_bound_of_continuousOn hcont
    refine ⟨M, fun b hb i => ?_⟩
    calc _ ≤ ∑ i, |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖| :=
          Finset.single_le_sum (f := fun i => |Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ M := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM b hb)
  set L : ℝ := B₀ + B with hL

  set Vset : Set (StrictUpperIndex (Fin (m + 1)) → 𝕜) :=
    (fun b : GL (Fin (m + 1)) 𝕜 => unipotentPart (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜)) '' ω
    with hVset
  have hVc : IsCompact Vset := hω.image_of_continuousOn (continuousOn_pi.2 fun p =>
    ContinuousOn.div (hent _ _).continuousOn (hent _ _).continuousOn fun b hb => hb0 b hb _)
  set Nc : Set (upperUnipotentSubgroup (Fin (m + 1)) 𝕜) := unipotentCoordsHomeomorph '' Vset
    with hNc
  have hNcc : IsCompact Nc := hVc.image unipotentCoordsHomeomorph.continuous
  have hNcm : MeasurableSet Nc := hNcc.isClosed.measurableSet

  set μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜) := Measure.haar with hμK
  set μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜) := Measure.haar with hμN
  have := isHaarMeasure_map_expDiag (𝕜 := 𝕜) (m := m)
  set μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜) :=
    Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ)) with hμA
  obtain ⟨c, -, hc⟩ := hANK μK μA μN
  set P : ℝ := (Fintype.card (StrictUpperIndex (Fin (m + 1))) : ℝ) with hP
  set V : ℝ≥0∞ := ∏ _i : Fin (m + 1), ENNReal.ofReal (2 * L) with hV
  refine ⟨(c : ℝ≥0∞) * (μK univ * μN Nc) * (ENNReal.ofReal (Real.exp (e * (2 * L * P))) * V), ?_, fun x => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top
      (measure_ne_top μK univ) hNcc.measure_lt_top.ne)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top))

  set box : Set (Fin (m + 1) → ℝ) := Set.Icc (x - fun _ => L) (x + fun _ => L) with hbox
  set R : Set (diagPosSubgroup (Fin (m + 1)) 𝕜) := expDiag 𝕜 m '' box with hR
  have hRm : MeasurableSet R := ((expDiag 𝕜 m).isClosed_image.2 isClosed_Icc).measurableSet
  have hSc : IsCompact (boxGL ω B x) := by
    have : boxGL ω B x = (fun p : GL (Fin (m + 1)) 𝕜 × (Fin (m + 1) → ℝ) × unitaryGroup (Fin (m + 1)) 𝕜 =>
        p.1 * ((expDiag 𝕜 m (x + p.2.1) : diagPosSubgroup (Fin (m + 1)) 𝕜) : GL (Fin (m + 1)) 𝕜) *
          Unitary.toUnits p.2.2) '' (ω ×ˢ (Set.univ.pi fun _ => Set.Icc (-B) B) ×ˢ Set.univ) := by
      ext g
      constructor
      · rintro ⟨b, hb, y, hy, k, rfl⟩
        exact ⟨(b, y, k), ⟨hb, fun i _ => abs_le.1 (hy i), Set.mem_univ _⟩, rfl⟩
      · rintro ⟨⟨b, y, k⟩, ⟨hb, hy, -⟩, rfl⟩
        exact ⟨b, hb, y, fun i => abs_le.2 (hy i (Set.mem_univ i)), k, rfl⟩
    rw [this]
    refine (hω.prod ((isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_univ)).image ?_
    exact (continuous_fst.mul (continuous_subtype_val.comp ((expDiag 𝕜 m).continuous.comp
      (continuous_const.add (continuous_fst.comp continuous_snd))))).mul
      (continuous_unitary_toUnits.comp (continuous_snd.comp continuous_snd))
  have hSm : MeasurableSet (boxGL ω B x) := hSc.isClosed.measurableSet

  have hpt : ∀ (a : diagPosSubgroup (Fin (m + 1)) 𝕜) (u : upperUnipotentSubgroup (Fin (m + 1)) 𝕜)
      (k : unitaryGroup (Fin (m + 1)) 𝕜),
      (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ≤
        R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a *
          Nc.indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) (diagConj a u) := by
    intro a u k
    by_cases hS : (a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k ∈ boxGL ω B x
    swap
    · rw [indicator_of_notMem hS]; exact zero_le
    obtain ⟨b, hbω, y, hy, k₀, hg⟩ := hS
    obtain ⟨a', u', k', heq', hdiag', hconj'⟩ :=
      exists_ANK_of_siegel (hωB b hbω) ⟨fun i => Real.exp (x i + y i), fun i => Real.exp_pos _⟩ k₀
    obtain ⟨rfl, rfl⟩ := ANK_unique (hg.trans heq')
    have haR : a ∈ R := by
      refine ⟨fun i => Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ + (x i + y i),
        ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
      · have h1 := abs_le.1 (hB₀ b hbω i); have h2 := abs_le.1 (hy i)
        simp only [Pi.sub_apply]; linarith
      · have h1 := abs_le.1 (hB₀ b hbω i); have h2 := abs_le.1 (hy i)
        simp only [Pi.add_apply]; linarith
      · apply Subtype.ext
        apply Units.ext
        rw [coe_expDiag, coe_diagPosOf, eq_diagonal_of_mem_diagPos a.2]
        congr 1
        funext i
        rw [hdiag' i, RCLike.ofReal_re]
        congr 1
        exact (by rw [Real.exp_add, Real.exp_log (norm_pos_iff.2 (hb0 b hbω i))] :
          Real.exp (Real.log ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ + (x i + y i)) =
            ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ * Real.exp (x i + y i))
    have hnc : diagConj a u ∈ Nc := by
      rw [hconj']
      exact ⟨_, ⟨b, hbω, rfl⟩, rfl⟩
    rw [indicator_of_mem (show _ ∈ boxGL ω B x from ⟨b, hbω, y, hy, k₀, hg⟩), indicator_of_mem haR,
      indicator_of_mem hnc]
    simp
  set δi : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞ :=
    fun a => ((iwasawaDelta (a : GL (Fin (m + 1)) 𝕜) : ℝ≥0∞))⁻¹ with hδi
  have hinner : ∀ a : diagPosSubgroup (Fin (m + 1)) 𝕜,
      ∫⁻ u, ∫⁻ k, (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN ≤
      μK univ * μN Nc * R.indicator δi a := by
    intro a
    have hpre : μN (diagConj a ⁻¹' Nc) = δi a * μN Nc := by
      rw [← Measure.map_apply (continuous_diagConj a).measurable hNcm, map_diagConj_haar,
        smul_apply, smul_eq_mul]
    calc ∫⁻ u, ∫⁻ k, (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
          ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN
        ≤ ∫⁻ u, ∫⁻ _k, R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a *
            Nc.indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) (diagConj a u) ∂μK ∂μN :=
          lintegral_mono fun u => lintegral_mono fun k => hpt a u k
      _ = ∫⁻ u, (R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a * μK univ) *
            (diagConj a ⁻¹' Nc).indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) u ∂μN := by
          refine lintegral_congr fun u => ?_
          rw [lintegral_const]
          simp only [indicator, mem_preimage, Pi.one_apply]
          split_ifs <;> ring
      _ = (R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a * μK univ) *
            μN (diagConj a ⁻¹' Nc) := by
          rw [lintegral_const_mul _ (measurable_one.indicator
            (hNcm.preimage (continuous_diagConj a).measurable)),
            lintegral_indicator_one (hNcm.preimage (continuous_diagConj a).measurable)]
      _ = μK univ * μN Nc * R.indicator δi a := by
          rw [hpre]
          simp only [indicator, Pi.one_apply]
          split_ifs <;> ring
  have hmeasF : Measurable (R.indicator δi) :=
    (ENNReal.continuous_coe.comp continuous_iwasawaDelta_diagPos).measurable.inv.indicator hRm

  have hA : ∫⁻ a, R.indicator δi a ∂μA ≤
      ENNReal.ofReal (Real.exp (-(e * pairSum m x))) * (ENNReal.ofReal (Real.exp (e * (2 * L * P))) * V) := by
    rw [hμA, lintegral_map hmeasF (expDiag 𝕜 m).continuous.measurable]
    calc ∫⁻ z, R.indicator δi (expDiag 𝕜 m z)
        ≤ ∫⁻ z, box.indicator (fun _ => ENNReal.ofReal (Real.exp (-(e * pairSum m x))) *
            ENNReal.ofReal (Real.exp (e * (2 * L * P)))) z := by
          refine lintegral_mono fun z => ?_
          by_cases hz : expDiag 𝕜 m z ∈ R
          · have hzb : z ∈ box := by
              obtain ⟨z', hz', hzz⟩ := hz
              rwa [← (expDiag 𝕜 m).injective hzz]
            rw [indicator_of_mem hz, indicator_of_mem hzb]
            have hD : ((iwasawaDelta (diagPosOf ⟨fun i => Real.exp (z i), fun i => Real.exp_pos _⟩ :
                GL (Fin (m + 1)) 𝕜) : ℝ)) = Real.exp (e * pairSum m z) := by
              rw [iwasawaDelta_diagPosOf, pairSum, Finset.mul_sum, Real.exp_sum]
              refine Finset.prod_congr rfl fun p _ => ?_
              rw [← Real.exp_sub, ← Real.exp_nat_mul]
            rw [hδi]
            dsimp only
            rw [coe_expDiag, ← ENNReal.ofReal_coe_nnreal,
              ← ENNReal.ofReal_inv_of_pos (by rw [hD]; exact Real.exp_pos _), hD, ← Real.exp_neg,
              ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have hdiff : pairSum m x - pairSum m z ≤ 2 * L * P := by
              rw [pairSum, pairSum, ← Finset.sum_sub_distrib, hP]
              calc _ ≤ ∑ _p : StrictUpperIndex (Fin (m + 1)), 2 * L := Finset.sum_le_sum fun p _ => by
                    have h1 := hzb.1 p.1.1; have h2 := hzb.2 p.1.1
                    have h3 := hzb.1 p.1.2; have h4 := hzb.2 p.1.2
                    simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3 h4
                    linarith
                _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
            nlinarith [mul_le_mul_of_nonneg_left hdiff he0]
          · rw [indicator_of_notMem hz]; exact zero_le
      _ = ENNReal.ofReal (Real.exp (-(e * pairSum m x))) *
            ENNReal.ofReal (Real.exp (e * (2 * L * P))) * volume box := by
          rw [lintegral_indicator_const measurableSet_Icc]
      _ = _ := by
          rw [hbox, Real.volume_Icc_pi, mul_assoc, hV]
          congr 2
          refine Finset.prod_congr rfl fun i _ => ?_
          congr 1
          simp only [Pi.add_apply, Pi.sub_apply]
          ring

  rw [← lintegral_indicator_one hSm, hc _ (measurable_one.indicator hSm)]
  calc (c : ℝ≥0∞) * ∫⁻ a, ∫⁻ u, ∫⁻ k, (boxGL ω B x).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN ∂μA
      ≤ (c : ℝ≥0∞) * ∫⁻ a, μK univ * μN Nc * R.indicator δi a ∂μA :=
        mul_le_mul_of_nonneg_left (lintegral_mono hinner) zero_le
    _ = (c : ℝ≥0∞) * (μK univ * μN Nc * ∫⁻ a, R.indicator δi a ∂μA) := by
        rw [lintegral_const_mul _ hmeasF]
    _ ≤ (c : ℝ≥0∞) * (μK univ * μN Nc * (ENNReal.ofReal (Real.exp (-(e * pairSum m x))) *
          (ENNReal.ofReal (Real.exp (e * (2 * L * P))) * V))) := by gcongr
    _ = _ := by ring

end PositivityTheory.Rg.Rs.boxvol

end
end

open MeasureTheory Measure Set Matrix NumberField
open scoped NNReal ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace PositivityTheory.Rg.Rs.boxvol

section Transport

variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {m : ℕ}
  [MeasurableSpace (GL (Fin (m + 1)) E)] [BorelSpace (GL (Fin (m + 1)) E)]
  [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]

theorem measure_box_ringEquiv_le (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
    [MeasurableSpace (unitaryGroup (Fin (m + 1)) 𝕜)] [BorelSpace (unitaryGroup (Fin (m + 1)) 𝕜)]
    (hANK : ∀ (ν : Measure (GL (Fin (m + 1)) 𝕜)) [ν.IsHaarMeasure]
      (μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜)) [μK.IsHaarMeasure]
      (μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜)) [μA.IsHaarMeasure]
      (μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜)) [μN.IsHaarMeasure],
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂ν = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA)
    (μ : Measure (GL (Fin (m + 1)) E)) [μ.IsHaarMeasure]
    (D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) E)
    (hD : ∀ r, ((D r : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
      diagonal fun i => ((r.1 i : ℝ) : 𝕜))
    {ω : Set (GL (Fin (m + 1)) E)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) E).IsUpperTriangular) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : Fin (m + 1) → ℝ,
      μ {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k : GL (Fin (m + 1)) E,
        (∀ z : Fin (m + 1) → E, euclidNorm (z ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) = euclidNorm z) ∧
        g = b * D ⟨fun i => Real.exp (x i + y i), fun _ => Real.exp_pos _⟩ * k} ≤
        C * ENNReal.ofReal (Real.exp (-((Module.finrank ℝ 𝕜 : ℝ) * pairSum m x))) := by
  classical
  have hφc : Continuous φ := (AddMonoidHomClass.isometry_of_norm φ hφ).continuous
  have hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖ := fun x => by rw [← hφ, RingEquiv.apply_symm_apply]
  have hφc' : Continuous φ.symm := (AddMonoidHomClass.isometry_of_norm φ.symm hφ').continuous
  set e : Matrix (Fin (m + 1)) (Fin (m + 1)) E ≃* Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
    φ.mapMatrix.toMulEquiv with he
  set Φ : GL (Fin (m + 1)) E ≃ₜ* GL (Fin (m + 1)) 𝕜 :=
    unitsCongr e (continuous_id.matrix_map hφc) (continuous_id.matrix_map hφc') with hΦ
  have hΦv : ∀ g : GL (Fin (m + 1)) E,
      ((Φ g : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ := fun g => rfl
  set ν : Measure (GL (Fin (m + 1)) 𝕜) := Measure.map Φ μ with hν
  have hνH : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hω' : IsCompact (Φ '' ω) := hω.image Φ.continuous
  have hωB' : ∀ b ∈ Φ '' ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).IsUpperTriangular := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    rw [hΦv, Matrix.map_apply, hωB b hb hij, map_zero]
  obtain ⟨C, hC, hCb⟩ := measure_boxGL_le ν (fun μK _ μA _ μN _ => hANK ν μK μA μN) hω' hωB' B
  refine ⟨C, hC, fun x => le_trans ?_ (hCb x)⟩
  refine (measure_mono ?_).trans (Measure.le_map_apply Φ.continuous.measurable.aemeasurable _)
  rintro g ⟨b, hbω, y, hy, k, hk, rfl⟩
  change Φ (b * D _ * k) ∈ boxGL (Φ '' ω) B x
  have hkU : ((Φ k : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) ∈
      unitaryGroup (Fin (m + 1)) 𝕜 := by
    refine mem_unitaryGroup_of_euclidNorm fun z => ?_
    have hz : z = fun i => φ (φ.symm (z i)) := by funext i; simp
    rw [hz, hΦv]
    have : (fun i => φ (φ.symm (z i))) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
        fun j => φ.toRingHom (((fun i => φ.symm (z i)) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) j) := by
      ext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [vecMul, dotProduct, _root_.map_sum, map_mul]
    rw [this, euclidNorm_map φ.toRingHom hφ, hk, ← euclidNorm_map φ.toRingHom hφ]
    rfl
  refine ⟨Φ b, ⟨b, hbω, rfl⟩, y, hy, ⟨_, hkU⟩, ?_⟩
  rw [map_mul, map_mul]
  congr 1
  · congr 1
    apply Units.ext
    rw [hΦv, hD, coe_diagPosOf]
  · apply Units.ext
    rfl

end Transport

variable {K : Type*} [Field K] {m : ℕ}

def boxPlace (w : InfinitePlace K) (ω : Set (GL (Fin (m + 1)) w.Completion)) (B : ℝ) (x : Fin (m + 1) → ℝ) :
    Set (GL (Fin (m + 1)) w.Completion) :=
  {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k ∈ archCompact w,
    g = b * diagUnits (m + 1) (fun i => posRealToUnits w
      ⟨Real.exp (x i + y i) ^ w.mult, pow_pos (Real.exp_pos _) _⟩) * k}

theorem measure_boxPlace_le (w : InfinitePlace K)
    [MeasurableSpace (GL (Fin (m + 1)) w.Completion)] [BorelSpace (GL (Fin (m + 1)) w.Completion)]
    (μ : Measure (GL (Fin (m + 1)) w.Completion)) [μ.IsHaarMeasure]
    {ω : Set (GL (Fin (m + 1)) w.Completion)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).IsUpperTriangular) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : Fin (m + 1) → ℝ,
      μ (boxPlace w ω B x) ≤ C * ENNReal.ofReal (Real.exp (-((w.mult : ℝ) * pairSum m x))) := by
  classical
  set D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) w.Completion := fun r =>
    diagUnits (m + 1) (fun i => posRealToUnits w ⟨r.1 i ^ w.mult, pow_pos (r.2 i) _⟩) with hDdef
  have hsub : ∀ x, boxPlace w ω B x ⊆
      {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k : GL (Fin (m + 1)) w.Completion,
        (∀ z : Fin (m + 1) → w.Completion,
          euclidNorm (z ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion)) = euclidNorm z) ∧
        g = b * D ⟨fun i => Real.exp (x i + y i), fun i => Real.exp_pos _⟩ * k} := by
    rintro x g ⟨b, hb, y, hy, k, hk, rfl⟩
    exact ⟨b, hb, y, hy, k, hk, rfl⟩
  by_cases hw : w.IsReal
  · have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivRealOfIsReal hw x‖ = ‖x‖ := fun x =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) x
    have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
    have hD : ∀ r : PosDiag (Fin (m + 1)), ((D r : GL (Fin (m + 1)) w.Completion) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).map (InfinitePlace.Completion.ringEquivRealOfIsReal hw) =
        diagonal fun i => ((r.1 i : ℝ) : ℝ) := fun r => by
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      simp [posRealToUnits, posRealElem, hw, hm]
    obtain ⟨C, hC, hCb⟩ := measure_box_ringEquiv_le (𝕜 := ℝ)
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw) hφ
      (fun ν _ μK _ μA _ μN _ => lintegral_GLReal_ANK ν μK μA μN) μ D hD hω hωB B
    refine ⟨C, hC, fun x => (measure_mono (hsub x)).trans ?_⟩
    have h := hCb x
    rw [Module.finrank_self] at h
    rwa [hm]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hc x‖ = ‖x‖ := fun x =>
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
    have hm : w.mult = 2 := by simp [InfinitePlace.mult, hw]
    have hD : ∀ r : PosDiag (Fin (m + 1)), ((D r : GL (Fin (m + 1)) w.Completion) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) =
        diagonal fun i => ((r.1 i : ℝ) : ℂ) := fun r => by
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      simp [posRealToUnits, posRealElem, hw, hm, Real.sqrt_sq (r.2 i).le]
    obtain ⟨C, hC, hCb⟩ := measure_box_ringEquiv_le (𝕜 := ℂ)
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) hφ
      (fun ν _ μK _ μA _ μN _ => lintegral_GLComplex_ANK ν μK μA μN) μ D hD hω hωB B
    refine ⟨C, hC, fun x => (measure_mono (hsub x)).trans ?_⟩
    have h := hCb x
    rw [Complex.finrank_real_complex] at h
    rwa [hm]

end PositivityTheory.Rg.Rs.boxvol

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.SumRangeSuccMulSubPred
open Finset

namespace PositivityTheory.Rg.Rs.boxvol

theorem sum_range_succ_mul_sub_pred (y : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) = ∑ i ∈ range n, y i - n * y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem sum_range_pairs_sub (y : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j)
      = ∑ r ∈ range n, ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ r ∈ range (n + 1), ((r : ℝ) * (((n + 1 : ℕ) : ℝ) - r)) * (y (r - 1) - y r)
        = ∑ r ∈ range (n + 1), ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r)
          + ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      push_cast
      ring
    rw [h1, sum_range_succ_mul_sub_pred, sum_range_succ, ih, sum_range_succ _ n]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring

theorem sum_pairs_sub (n : ℕ) (x : Fin n → ℝ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ r ∈ Finset.range n, ((r : ℝ) * ((n : ℝ) - r)) *
          (if h : 0 < r ∧ r < n then x ⟨r - 1, by omega⟩ - x ⟨r, h.2⟩ else 0) := by
  set y : ℕ → ℝ := fun k => if h : k < n then x ⟨k, h⟩ else 0 with hy
  have hyx : ∀ i : Fin n, y i = x i := fun i => by simp [hy, i.2]
  have hL : ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j) := by
    rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
      (fun p : Fin n × Fin n => x p.1 - x p.2), Finset.sum_filter, Fintype.sum_prod_type_right,
      ← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range j, (y i - y j)) n]
    refine sum_congr rfl fun j _ => ?_
    have hj : range (j : ℕ) = (range n).filter (· < (j : ℕ)) := by
      ext i
      simp only [mem_range, mem_filter]
      have := j.2
      omega
    rw [hj, Finset.sum_filter,
      ← Fin.sum_univ_eq_sum_range (fun i => if i < (j : ℕ) then y i - y j else 0) n]
    refine sum_congr rfl fun i _ => ?_
    simp only [Fin.lt_def, hyx]
  rw [hL, sum_range_pairs_sub]
  refine sum_congr rfl fun r hr => ?_
  have hrn : r < n := mem_range.mp hr
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · simp
  · have h : 0 < r ∧ r < n := ⟨h0, hrn⟩
    have h1 : r - 1 < n := by omega
    simp [hy, h0, hrn, h1]

end PositivityTheory.Rg.Rs.boxvol
end

open NumberField MeasureTheory Set Matrix
open scoped NNReal ENNReal Pointwise
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace PositivityTheory.Rg.Rs.boxvol

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_measure_le_prod (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (E : Set (AdelicGLn.AdelicGL K n))
      (S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion)) (F : Set (AdelicGLn.FiniteAdelicGL K n)),
      (∀ g ∈ E, (∀ w, infAt w g ∈ S w) ∧ (AdelicGLn.prodEquiv K n g).2 ∈ F) →
      μ E ≤ c * ((∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
        (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F) := by
  set e := infFinEquiv (K := K) (n := n) with he
  set ρ : Measure ((Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n) :=
    (Measure.pi fun w => (Measure.haar : Measure (GL (Fin n) w.Completion))).prod
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) with hρ
  have hν : (Measure.map e μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ e.toMulEquiv e.continuous e.symm.continuous
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map e μ) ρ
  set s := (Measure.map e μ).haarScalarFactor ρ with hs
  refine ⟨(s : ℝ≥0∞), ENNReal.coe_ne_top, fun E S F hE => ?_⟩
  have hρT : ρ ((Set.univ.pi S) ×ˢ F) = (∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F := by
    rw [hρ, Measure.prod_prod, Measure.pi_pi]
  have hET : E ⊆ e ⁻¹' ((Set.univ.pi S) ×ˢ F) := fun g hg => ⟨fun w _ => (hE g hg).1 w, (hE g hg).2⟩
  calc μ E ≤ μ (e ⁻¹' ((Set.univ.pi S) ×ˢ F)) := measure_mono hET
    _ = Measure.map e μ ((Set.univ.pi S) ×ˢ F) := (e.toHomeomorph.toMeasurableEquiv.map_apply _).symm
    _ = (s • ρ) ((Set.univ.pi S) ×ˢ F) := by rw [← heq]
    _ = _ := by rw [Measure.smul_apply, hρT, ENNReal.smul_def, smul_eq_mul]

end PositivityTheory.Rg.Rs.boxvol

namespace PositivityTheory.Rg.Rs

open boxvol in
theorem boxvol_holds : An.BoxVol := by
  intro K _ _ n μ _ ω hω hωB
  rcases n with _ | m
  · have hs : (Set.univ : Set (AdelicGLn.AdelicGL K 0)).Subsingleton := fun x _ y _ =>
      Units.ext (Subsingleton.elim _ _)
    have hfin : μ univ ≠ ⊤ := hs.isCompact.measure_lt_top.ne
    refine ⟨(μ univ).toReal, fun x => ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty, neg_zero, Real.exp_zero, mul_one]
    rw [ENNReal.ofReal_toReal hfin]
    exact measure_mono (subset_univ _)
  obtain ⟨c, hc, hμ⟩ := exists_measure_le_prod μ
  set p2 : AdelicGLn.AdelicGL K (m + 1) → AdelicGLn.FiniteAdelicGL K (m + 1) :=
    fun g => (AdelicGLn.prodEquiv K (m + 1) g).2 with hp2
  have hp2c : Continuous p2 := continuous_snd.comp (AdelicGLn.prodEquiv K (m + 1)).continuous
  set F : Set (AdelicGLn.FiniteAdelicGL K (m + 1)) :=
    (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := m + 1) : Set (AdelicGLn.AdelicGL K (m + 1)))) with hFdef
  have hF : IsCompact F := (hω.image hp2c).mul (isCompact_maxCompact.image hp2c)
  have hex : ∀ w : InfinitePlace K, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x,
      (Measure.haar : Measure (GL (Fin (m + 1)) w.Completion))
        (boxPlace w (infAt w '' ω) ((m + 1 : ℕ) : ℝ) x) ≤
        C * ENNReal.ofReal (Real.exp (-((w.mult : ℝ) * pairSum m x))) := fun w =>
    measure_boxPlace_le w (Measure.haar : Measure (GL (Fin (m + 1)) w.Completion))
      (hω.image (continuous_infAt w))
      (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ((m + 1 : ℕ) : ℝ)
  choose C hC hCb using hex
  set D : ℝ≥0∞ := c * ((∏ w, C w) * (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K (m + 1))) F) with hDdef
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top hc (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => hC w)
    hF.measure_lt_top.ne)
  refine ⟨D.toReal, fun x => ?_⟩
  have key : ∑ r ∈ Finset.range (m + 1), 2 * An.rho K (m + 1) r * An.sr x r =
      (Module.finrank ℚ K : ℝ) * pairSum m x := by
    rw [pairSum, sum_pairs_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [An.rho, An.sr]
    ring
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  rw [key]
  calc μ _ ≤ c * ((∏ w, (Measure.haar : Measure (GL (Fin (m + 1)) w.Completion))
        (boxPlace w (infAt w '' ω) ((m + 1 : ℕ) : ℝ) x)) *
        (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K (m + 1))) F) := by
        refine hμ _ _ _ fun g hg => ?_
        obtain ⟨b, hb, y, hy, k, hk, rfl⟩ := hg
        refine ⟨fun w => ⟨infAt w b, ⟨b, hb, rfl⟩, y, hy, infAt w k, hk.1 w, ?_⟩, ?_⟩
        · rw [infAt_mul, infAt_mul]
          congr 2
          exact infAt_diagUnits_posIdele w (fun i => Real.exp (x i + y i)) (fun i => Real.exp_pos _)
        · refine ⟨p2 b, ⟨b, hb, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩
          simp only [hp2, map_mul, Prod.snd_mul, An.tor]
          rw [prodEquiv_diagUnits_posIdele_snd (fun i => Real.exp ((x + y) i)) (fun i => Real.exp_pos _),
            mul_one]
    _ ≤ c * ((∏ w, (C w * ENNReal.ofReal (Real.exp (-((w.mult : ℝ) * pairSum m x))))) *
        (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K (m + 1))) F) := by
        gcongr with w
        exact hCb w x
    _ = D * ENNReal.ofReal (Real.exp (-((Module.finrank ℚ K : ℝ) * pairSum m x))) := by
        rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun w _ => (Real.exp_pos _).le),
          ← Real.exp_sum, ← hsum, Finset.sum_mul, ← Finset.sum_neg_distrib, hDdef]
        ring
    _ = ENNReal.ofReal (D.toReal * Real.exp (-((Module.finrank ℚ K : ℝ) * pairSum m x))) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD]

end PositivityTheory.Rg.Rs

end
