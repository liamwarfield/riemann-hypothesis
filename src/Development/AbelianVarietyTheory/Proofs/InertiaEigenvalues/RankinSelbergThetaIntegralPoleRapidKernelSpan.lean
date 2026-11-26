module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSupSFinGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProduct
noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.CuspRep.CuspidalL2GL
open scoped nonZeroDivisors ENNReal

namespace GlobalTheory.RSThetaRes

def lowSum (T s t : ℝ) : ℝ := ∑' n : ℤ, if T ^ n * t ≤ 1 then (T ^ n * t) ^ s else 0

theorem hasSum_lowSum {L s t : ℝ} (hL : 0 < L) (hs : 0 < s) (ht : 0 < t) :
    ∃ u : ℝ, Real.exp (-L) < u ∧ u ≤ 1 ∧
      HasSum (fun n : ℤ => if Real.exp L ^ n * t ≤ 1 then (Real.exp L ^ n * t) ^ s else 0)
        (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) := by
  have hT : 1 < Real.exp L := Real.one_lt_exp_iff.2 hL
  have hT0 : 0 < Real.exp L := Real.exp_pos L
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow (inv_pos.2 ht) hT
  have hm : ∀ n : ℤ, Real.exp L ^ n * t ≤ 1 ↔ n ≤ m := by
    intro n
    constructor
    · intro hn
      by_contra hc
      push_neg at hc
      have h3 : Real.exp L ^ (m + 1) ≤ Real.exp L ^ n := zpow_le_zpow_right₀ hT.le (by omega)
      have h4 : t⁻¹ < Real.exp L ^ n := h2.trans_le h3
      have h5 := mul_lt_mul_of_pos_right h4 ht
      rw [inv_mul_cancel₀ ht.ne'] at h5
      linarith
    · intro hn
      have h3 : Real.exp L ^ n ≤ t⁻¹ := (zpow_le_zpow_right₀ hT.le hn).trans h1
      calc Real.exp L ^ n * t ≤ t⁻¹ * t := mul_le_mul_of_nonneg_right h3 ht.le
        _ = 1 := inv_mul_cancel₀ ht.ne'
  refine ⟨Real.exp L ^ m * t, ?_, (hm m).2 le_rfl, ?_⟩
  · have h3 : t⁻¹ < Real.exp L ^ m * Real.exp L := by rwa [zpow_add_one₀ hT0.ne'] at h2
    have h4 : 1 < Real.exp L ^ m * t * Real.exp L := by
      have h5 := mul_lt_mul_of_pos_right h3 ht
      rw [inv_mul_cancel₀ ht.ne'] at h5
      linarith
    rw [Real.exp_neg]
    calc (Real.exp L)⁻¹ = (Real.exp L)⁻¹ * 1 := (mul_one _).symm
      _ < (Real.exp L)⁻¹ * (Real.exp L ^ m * t * Real.exp L) := mul_lt_mul_of_pos_left h4 (inv_pos.2 hT0)
      _ = Real.exp L ^ m * t := by field_simp
  · have hq0 : 0 ≤ Real.exp (-(s * L)) := (Real.exp_pos _).le
    have hq1 : Real.exp (-(s * L)) < 1 := by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 (mul_pos hs hL))
    have hg : Function.Injective (fun k : ℕ => m - (k : ℤ)) := fun i j h => by simpa using h
    rw [← hg.hasSum_iff]
    · have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((Real.exp L ^ m * t) ^ s)
      have hfun : ((fun n : ℤ => if Real.exp L ^ n * t ≤ 1 then (Real.exp L ^ n * t) ^ s else 0) ∘
          fun k : ℕ => m - (k : ℤ)) = fun i : ℕ => (Real.exp L ^ m * t) ^ s * Real.exp (-(s * L)) ^ i := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos ((hm _).2 (by omega)), zpow_sub₀ hT0.ne', zpow_natCast]
        have hk : Real.exp L ^ m / Real.exp L ^ k * t = (Real.exp L ^ m * t) * (Real.exp L ^ k)⁻¹ := by
          field_simp
        rw [hk, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity)]
        congr 1
        rw [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1
        ring
      rw [hfun]
      exact this
    · intro n hn
      have hnm : ¬ n ≤ m := fun h => hn ⟨(m - n).toNat, by simp only; omega⟩
      rw [if_neg (fun h => hnm ((hm n).1 h))]

theorem lowSum_bounds {L s u : ℝ} (hL : 0 < L) (hs : 0 < s) (hu : Real.exp (-L) < u) (hu1 : u ≤ 1) :
    Real.exp (-(s * L)) / L ≤ s * (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) ∧
      s * (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) ≤ Real.exp (s * L) / L := by
  have hu0 : 0 < u := (Real.exp_pos _).trans hu
  have hy0 : 0 < s * L := mul_pos hs hL
  have hv1 : u ^ s ≤ 1 := Real.rpow_le_one hu0.le hu1 hs.le
  have hv0 : Real.exp (-(s * L)) < u ^ s := by
    have h := Real.rpow_lt_rpow (Real.exp_pos _).le hu hs
    rwa [← Real.exp_mul, neg_mul, mul_comm L s] at h
  have hD : 0 < 1 - Real.exp (-(s * L)) := by linarith
  have hDy : 1 - Real.exp (-(s * L)) ≤ s * L := by have := Real.add_one_le_exp (-(s * L)); linarith
  have hE : Real.exp (s * L) * Real.exp (-(s * L)) = 1 := by rw [← Real.exp_add]; simp
  have hey : s * L + 1 ≤ Real.exp (s * L) := Real.add_one_le_exp _
  have hre : s * (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) = s * u ^ s / (1 - Real.exp (-(s * L))) := by
    field_simp
  rw [hre]
  have hsv : s * u ^ s * L = u ^ s * (s * L) := by ring
  constructor
  · rw [div_le_div_iff₀ hL hD, hsv]
    nlinarith [mul_le_mul_of_nonneg_left hDy (Real.exp_pos (-(s * L))).le,
      mul_le_mul_of_nonneg_right hv0.le hy0.le]
  · rw [div_le_div_iff₀ hD hL, hsv]
    nlinarith [mul_le_mul_of_nonneg_right hv1 hy0.le]

theorem tendsto_mul_lowSum {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    Tendsto (fun s : ℝ => s * lowSum (Real.exp L) s t) (𝓝[>] 0) (𝓝 (1 / L)) := by
  have hb : ∀ s : ℝ, 0 < s → Real.exp (-(s * L)) / L ≤ s * lowSum (Real.exp L) s t ∧
      s * lowSum (Real.exp L) s t ≤ Real.exp (s * L) / L := by
    intro s hs
    obtain ⟨u, hu, hu1, hsum⟩ := hasSum_lowSum hL hs ht
    rw [lowSum, hsum.tsum_eq]
    exact lowSum_bounds hL hs hu hu1
  have hlo : Tendsto (fun s : ℝ => Real.exp (-(s * L)) / L) (𝓝[>] 0) (𝓝 (1 / L)) := by
    have hc : Continuous fun s : ℝ => Real.exp (-(s * L)) / L := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun s : ℝ => Real.exp (s * L) / L) (𝓝[>] 0) (𝓝 (1 / L)) := by
    have hc : Continuous fun s : ℝ => Real.exp (s * L) / L := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs using (hb s hs).1
  · filter_upwards [self_mem_nhdsWithin] with s hs using (hb s hs).2

end GlobalTheory.RSThetaRes

namespace GlobalTheory.RSThetaRes

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem tendsto_residue (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) (h𝓕' : IsFundamentalDomain (latticeGL E a) 𝓕' μ)
    {F : GA E a → ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ g, ‖F g‖ ≤ C)
    (hinv : ∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) :
    Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
      F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1)
      (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef
  have hd0 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  have hL : 0 < L := mul_pos (Nat.cast_pos.2 ha) hd0
  have hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L := by
    rw [Real.exp_one_pow, hLdef]
    push_cast
    rfl
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = Real.exp L ^ n * δ g := fun n g => by
    rw [← hTL]; exact GlobalTheory.RSTheta.absDet_zpow_mul n g
  have hT1 : 1 < Real.exp L := Real.one_lt_exp_iff.2 hL
  have hm : MeasurableSet {g | δ g ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hμ' : μ 𝓕' < ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕']; exact measure_lt_top _ _

  have key : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun g => F g * ((lowSum (Real.exp L) s (δ g) : ℝ) : ℂ)) 𝓕' μ ∧
      ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ =
        ∫ g in 𝓕', F g * ((lowSum (Real.exp L) s (δ g) : ℝ) : ℂ) ∂μ := by
    intro s hs
    set f : GA E a → ℂ := {g | δ g ≤ 1}.indicator (fun g => F g * ((δ g ^ s : ℝ) : ℂ)) with hf
    have hsum : ∀ g, ∑' n : ℤ, f (splitCentre E a 1 ^ n * g) = F g * ((lowSum (Real.exp L) s (δ g) : ℝ) : ℂ) := by
      intro g
      rw [lowSum, Complex.ofReal_tsum, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      simp only [hf, Set.indicator_apply, Set.mem_setOf_eq, hδz, hinv _ (zpow_mem_latticeGL n)]
      split_ifs <;> simp
    have hfm : AEStronglyMeasurable f μ :=
      ((hF.mul (Complex.continuous_ofReal.comp (hδc.rpow_const fun g => Or.inl (hδ0 g).ne'))).aestronglyMeasurable).indicator hm
    have hfin : ∫⁻ g in 𝓕', ∑' n : ℤ, ‖f (splitCentre E a 1 ^ n * g)‖ₑ ∂μ ≠ ⊤ := by
      obtain ⟨B, hB, hBle⟩ := GlobalTheory.RSThetaLow.exists_tsum_zpow_le_low hT1 hs
      have hpt : ∀ g, ∑' n : ℤ, ‖f (splitCentre E a 1 ^ n * g)‖ₑ ≤ ENNReal.ofReal C * B := by
        intro g
        refine le_trans ?_ (mul_le_mul_of_nonneg_left (hBle _ (hδ0 g)) zero_le)
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun n => ?_
        simp only [hf, Set.indicator_apply, Set.mem_setOf_eq, hδz, hinv _ (zpow_mem_latticeGL n)]
        split_ifs with h
        · have hp : 0 ≤ (Real.exp L ^ n * δ g) ^ s := Real.rpow_nonneg (mul_pos (zpow_pos (Real.exp_pos L) n) (hδ0 g)).le _
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hC0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
          exact mul_le_mul_of_nonneg_right (hC g) hp
        · simp
      refine (lt_of_le_of_lt (lintegral_mono hpt) ?_).ne
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.lt_top) hμ'
    obtain ⟨-, hI, -, heq⟩ := GlobalTheory.ThetaUnfold.integral_unfold μ (latticeGL E a) (ratGL E a).range
      (fun n : ℤ => splitCentre E a 1 ^ n) (Equiv.ofBijective φ hφ) (fun _ => rfl) h𝓕' h𝓕 f
      (by
        rintro _ ⟨γ, rfl⟩ g
        simp only [hf, Set.indicator_apply, Set.mem_setOf_eq, hδr, hinv _ (ratGL_mem_latticeGL γ)])
      hfm hfin
    refine ⟨?_, ?_⟩
    · exact Integrable.congr hI (ae_of_all _ hsum)
    · calc ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ = ∫ g in 𝓕, f g ∂μ := by
            rw [hf, integral_indicator hm, Measure.restrict_restrict hm, Set.inter_comm]
        _ = _ := by rw [← heq]; exact integral_congr_ae (.of_forall hsum)

  have hlim0 : Tendsto (fun s : ℝ => ((s : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ)
      (𝓝[>] 0) (𝓝 (((1 / L : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
    have hev : (fun s : ℝ => ((s : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ) =ᶠ[𝓝[>] 0]
        fun s => ∫ g in 𝓕', F g * ((s * lowSum (Real.exp L) s (δ g) : ℝ) : ℂ) ∂μ := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [(key s hs).2, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun g => ?_)
      simp only
      push_cast
      ring
    rw [mul_comm, ← integral_mul_const]
    refine Tendsto.congr' hev.symm ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C * (Real.exp L / L)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine (((key s hs).1.const_mul (s : ℂ)).aestronglyMeasurable).congr (.of_forall fun g => ?_)
      simp only
      push_cast
      ring
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with s hs hs1
      refine .of_forall fun g => ?_
      obtain ⟨u, hu, hu1, hsum⟩ := hasSum_lowSum hL hs (hδ0 g)
      have hb := lowSum_bounds hL hs hu hu1
      rw [← hsum.tsum_eq, ← lowSum] at hb
      have hnn : 0 ≤ s * lowSum (Real.exp L) s (δ g) := (div_nonneg (Real.exp_pos _).le hL.le).trans hb.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      refine mul_le_mul (hC g) (hb.2.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) hL.le)) hnn hC0
      have := hs1.2
      nlinarith
    · exact integrableOn_const hμ'.ne
    · refine .of_forall fun g => ?_
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp (tendsto_mul_lowSum hL (hδ0 g)))
  have hsub : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 0) := by
        have h := ((continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ))
        rwa [sub_self] at h
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.2 (Set.mem_Ioi.1 hx)
  exact hlim0.comp hsub

end GlobalTheory.RSThetaRes

namespace GlobalTheory.RSThetaRes

theorem residue_geometric : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∀ F : GA E a → ℂ, Continuous F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → (∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) → Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) :=
  fun _ _ _ _ _ ha μ _ _ _ h𝓕 h𝓕' _ hF ⟨_, hC⟩ hinv => tendsto_residue ha μ h𝓕 h𝓕' hF hC hinv

end GlobalTheory.RSThetaRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProductStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∀ F : GA E a → ℂ, Continuous F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → (∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) → Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
  first | exact @GlobalTheory.RSThetaRes.residue_geometric | exact GlobalTheory.RSThetaRes.residue_geometric | (intros; apply GlobalTheory.RSThetaRes.residue_geometric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpan
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaLimR

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mspanR_le_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) :
    GlobalTheory.JSW.mspanR π ≤ bddForms E a ω := by
  rw [← GlobalTheory.JSW.rspan_eq_mspanR]
  exact GlobalTheory.JSW.rspan_le (fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ)
    (fun F hF h => mul_right_mem_bddForms hF h) (fun F hF X _ ν _ k γ hk => GlobalTheory.JSW.kerInf_mem_bddForms hF hk)

theorem mem_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) : φ.1 ∈ bddForms E a ω :=
  hφ.elim (fun h => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ h)
    (fun h => mspanR_le_bddForms hω hπ h)

theorem mem_rsm {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) :
    φ ∈ GlobalTheory.RSThetaLowM.rsm π := by
  change φ.1 ∈ GlobalTheory.JSW.mspanR π
  rcases hφ with h | h
  · rw [← GlobalTheory.JSW.rspan_eq_mspanR]; exact GlobalTheory.JSW.mem_rspan h
  · exact h

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem resConst_ne_zero {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ2 : HasCompactSupport Φ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (hpos : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (hne : Φ ≠ 0) :
    ((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a ≠ 0 := by
  have hv : (finiteMeasurePi E (latt a J)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨((isOpen_latt J).measure_pos _ ⟨0, fun i => (idealFiniteAdeles J).zero_mem⟩).ne',
      (isCompact_latt J).measure_lt_top.ne⟩
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 hv) ?_
  have e : (fun u => Φ u) = fun u => (((Φ u).re : ℝ) : ℂ) := funext fun u => Complex.ext rfl (by simp [(hpos u).2])
  obtain ⟨x, hx⟩ : ∃ x, Φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hre : (Φ x).re ≠ 0 := fun h0 => hx (Complex.ext h0 (hpos x).2)
  have hpos' : 0 < ∫ u, (Φ u).re ∂(volume : Measure (Fin a → Cinf E)) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (Complex.continuous_re.comp hΦ1.continuous)
      (hΦ2.comp_left Complex.zero_re) (fun u => (hpos u).1) hre
  rw [e, integral_complex_ofReal, infMeasure, integral_smul_measure]
  refine Complex.ofReal_ne_zero.2 (smul_ne_zero ?_ hpos'.ne')
  simp

theorem setIntegral_rsHat_zero_of_bdd {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦ2 : HasCompactSupport Φ) (hΦ3 : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) {ω : HChar E} (hω : ω.IsUnitary) {φ φ' : Sm E a}
    (hb : φ.1 ∈ bddForms E a ω) (hb' : φ'.1 ∈ bddForms E a ω) :
    ∫ g in 𝓕', adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 ∂μ =
      (((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a) *
        ∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ := by
  have hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ1, hΦ2, hΦ3⟩
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  haveI : IsFiniteMeasure (μ.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]; exact measure_lt_top _ _⟩
  haveI : SFinite (μ.restrict 𝓕') :=
    ⟨⟨fun n => if n = 0 then μ.restrict 𝓕' else 0,
      fun n => by dsimp only; split_ifs <;> infer_instance,
      Measure.ext fun s hs => by
        rw [Measure.sum_apply _ hs, tsum_eq_single 0 (fun n hn => by simp [hn])]
        simp⟩⟩
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  obtain ⟨C, hC⟩ := hb.2.2.2
  obtain ⟨D, hD⟩ := hb'.2.2.2
  have hΦi : Integrable Φ (infMeasure E a) := by
    unfold infMeasure
    exact (hΦ1.continuous.integrable_of_hasCompactSupport hΦ2).smul_measure (by simp)
  have hi : Integrable (fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2)
      ((μ.restrict 𝓕').prod (infMeasure E a)) := by
    refine ((integrable_const (C * D)).mul_prod hΦi.norm).mono'
      (continuous_rsInf hb.1 hb'.1 hΦ1.continuous hΦ3).aestronglyMeasurable (.of_forall fun p => ?_)
    simp only [rsInf, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1)))
      (norm_nonneg _)
  have hx : ∀ x, ∫ g in 𝓕', rsInf ℓ φ.1 φ'.1 Φ g x ∂μ = (∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ) * Φ x := by
    intro x
    simp only [rsInf]
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.RSResidue.setIntegral_mul_right h𝓕 (f := fun g => φ.1 g * conj (φ'.1 g))
      (GlobalTheory.Petersson.leftInv_mul_conj hω hb hb') _
  simp only [GlobalTheory.RSResidue.rsHat_zero J η φ φ' hΦ]
  rw [integral_mul_const, integral_integral_swap hi]
  simp only [hx, integral_const_mul]
  ring

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem theta_integral_low_mspanR {ℓ : Fin a} {π π' : CuspSub E a} (hπ : π.IsUnitary) (hπ' : π'.IsUnitary)
    {φ φ' : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) (hφ' : φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π')
    (hc : Continuous φ.1) (hc' : Continuous φ'.1) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hcs : HasCompactSupport Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, 1 < x →
      IntegrableOn (fun g : GA E a =>
        (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      IntegrableOn (fun g : GA E a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ)) ∂μ =
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ +
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ := by
  have h := mem_rsm hφ
  have h' := mem_rsm hφ'
  have hT : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ, hcs, hs⟩
  obtain ⟨-, -, b3⟩ := GlobalTheory.RSThetaLowM.partB_entire J η hπ hπ' h h' hc hc' hT h𝓕
  simp only [Complex.ofReal_cpow (ideleModule E _).2.le, Complex.ofReal_sub, Complex.ofReal_one]
  exact ⟨fun x hx => ⟨(GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).1,
      GlobalTheory.RSThetaLowM.integrableOn_partA J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx,
      (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).2⟩,
    b3.continuous.comp Complex.continuous_ofReal⟩

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

theorem theta_integral_pole_mspanR : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → (∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ) ∧ Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 (c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ)) := by
  intro E _ _ _ a ℓ Φ hΦ hc hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ, K = ((GroundTheory.Automorphic.GJMatrix.finiteMeasurePi E (GlobalTheory.ThetaPoisson.latt a J)).toReal : ℂ) * ∫ x, Φ x ∂GlobalTheory.ThetaPoisson.infMeasure E a := ⟨_, rfl⟩
  have hK0 : (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → K ≠ 0 := fun h1 h2 => hKdef ▸ resConst_ne_zero hΦ hc J h1 h2
  have had : ((a : ℝ) * (Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 ℓ.pos)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  refine ⟨((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ)) * K,
    fun h1 h2 => mul_ne_zero (Complex.ofReal_ne_zero.2 (one_div_ne_zero had)) (hK0 h1 h2), ?_⟩
  intro π π' ω hω hπ hπ' φ φ' hφ hφ'
  have hu : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩
  have hu' : π'.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ'⟩
  have hb := mem_bddForms hω hπ hφ
  have hb' := mem_bddForms hω hπ' hφ'
  obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous hc hs J η μ 𝓕 h𝓕
  obtain ⟨l1, l2⟩ := theta_integral_low_mspanR hu hu' hφ hφ' hb.1 hb'.1 hΦ hc hs J η h𝓕
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.RSResidue.rsHat_zero_props hω hb hb' ⟨hΦ, hc, hs⟩ J η
  have hres := GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct E a ℓ.pos μ 𝓕 𝓕' h𝓕 h𝓕' _ f1 f2 f3
  rw [setIntegral_rsHat_zero_of_bdd hΦ hc hs J η h𝓕' hω hb hb', ← hKdef] at hres
  have hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)
  have hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := fun g => (ideleModule E _).2
  have hT : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hsum : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := fun g =>
    GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g
  have hint : ∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ := by
    intro x hx
    have iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
      simp only [hsum]; exact (l1 x hx).1
    have iHi : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ))
        (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ := by
      simp only [Complex.ofReal_cpow (hδ0 _).le]; exact u3 x
    refine (iLo.union iHi).mono_set fun g hg => ?_
    by_cases h : (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, (not_le.1 h).le⟩
  refine ⟨hint, ?_⟩

  set U : ℝ → ℂ := fun x => ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ with hU
  set B : ℝ → ℂ := fun x => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ with hB
  have hsplit : ∀ x : ℝ, 1 < x → ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ =
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ + B x + U x := by
    intro x hx
    rw [← integral_inter_add_diff hT (hint x hx)]
    congr 1
    simp only [hsum]
    exact (l1 x hx).2.2

  set M : ℝ := ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
    (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (2 : ℝ) ∂μ with hM
  have hUb : ∀ x : ℝ, x ≤ 2 → ‖U x‖ ≤ M := by
    intro x hx2
    refine norm_integral_le_of_norm_le ((u2 2).mono_set fun g hg => ⟨hg.1, by have h := hg.2; simp only [Set.mem_setOf_eq, not_le] at h ⊢; exact h.le⟩) ?_
    refine (ae_restrict_of_ae_restrict_of_subset (Set.diff_subset_compl _ _) (ae_restrict_mem hT.compl)).mono
      fun g hg => ?_
    have h1 : 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
      have h := hg; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h; exact h.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hδ0 g).le _)]
    exact mul_le_mul (norm_tsum_le_tsum_norm (u1 g)) (Real.rpow_le_rpow_of_exponent_le h1 hx2)
      (Real.rpow_nonneg (hδ0 g).le _) (tsum_nonneg fun _ => norm_nonneg _)
  have hx1 : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝 1) (𝓝 ((((1 : ℝ) - 1 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have tB : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * B x) (𝓝[>] 1) (𝓝 0) := by
    simpa using hx1.mul ((l2.tendsto 1).mono_left nhdsWithin_le_nhds)
  have tU : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * U x) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => ‖((x - 1 : ℝ) : ℂ)‖ * M) ?_
      (by have h := hx1.norm.mul_const M; rwa [norm_zero, zero_mul] at h)
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hUb x hx.2) (norm_nonneg _)
  have tot := (hres.add tB).add tU
  rw [add_zero, add_zero, mul_assoc] at *
  refine tot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx]
  ring

end GlobalTheory.RSThetaLimR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpanStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → (∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ) ∧ Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 (c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ)) := by
  first | exact @GlobalTheory.RSThetaLimR.theta_integral_pole_mspanR | exact GlobalTheory.RSThetaLimR.theta_integral_pole_mspanR | (intros; apply GlobalTheory.RSThetaLimR.theta_integral_pole_mspanR <;> assumption)
end
