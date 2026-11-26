module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowLePowRatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeIntegralsAndCardCompositions
open MeasureTheory Finset

namespace GlobalTheory

theorem setIntegral_cube_prod (a : ℕ) (S : Set ℝ) (f : Fin a → ℝ → ℝ) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => S), ∏ i, f i (τ i) = ∏ i, ∫ t in S, f i t := by
  have hμ : (volume : Measure (Fin a → ℝ)).restrict (Set.pi Set.univ (fun _ : Fin a => S)) =
      Measure.pi (fun _ : Fin a => (volume : Measure ℝ).restrict S) := by
    rw [volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin a => (volume : Measure ℝ)) (fun _ => S)
  rw [hμ]
  exact integral_fintype_prod_eq_prod (ι := Fin a) f

theorem setIntegral_Icc_const_div (c lo : ℝ) (h0 : 0 < lo) (h1 : lo ≤ 1 / 2) :
    ∫ t in Set.Icc lo (1 / 2), c / t = c * Real.log (1 / (2 * lo)) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
  have hfun : (fun t : ℝ => c / t) = fun t => c * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos h0 hhalf]
  congr 2
  field_simp

private lemma setIntegral_Ioo_pow_mul_div_eq (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) =
      (c : ℝ) * ((1 / 2 : ℝ) ^ (c * m) / ((c * m : ℕ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, c * m = k + 1 := ⟨c * m - 1, by have := Nat.mul_le_mul hc hm; omega⟩
  have hcongr : Set.EqOn (fun t : ℝ => t ^ (c * m) * ((c : ℝ) / t)) (fun t => (c : ℝ) * t ^ k)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht.1
    simp only
    rw [hk, pow_succ]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    integral_pow, hk]
  push_cast
  ring

theorem setIntegral_Ioo_pow_mul_div (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    0 ≤ ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ∧
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ≤ 1 := by
  rw [setIntegral_Ioo_pow_mul_div_eq c m hm hc]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * m) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (c * m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcm : ((c * m : ℕ) : ℝ) = (c : ℝ) * m := by push_cast; ring
  rw [hcm]
  have hden : (0 : ℝ) < (c : ℝ) * m := by positivity
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_one hden]
  calc (c : ℝ) * (1 / 2 : ℝ) ^ (c * m) ≤ (c : ℝ) * 1 := by gcongr
    _ ≤ (c : ℝ) * m := by gcongr

theorem sum_card_composition_lt (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), composition_card, Nat.add_sub_cancel, pow_succ]
    omega

theorem sizeIntegrals_and_card_compositions :
    (∀ (a : ℕ) (c : Fin a → ℝ) (lo : ℝ), 0 < lo → lo ≤ 1 / 2 → (∀ i, 0 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc lo (1 / 2)), ∏ i, c i / τ i = ∏ i, c i * Real.log (1 / (2 * lo))) ∧ (∀ (a : ℕ) (c : Fin a → ℕ) (m : ℕ), 1 ≤ m → (∀ i, 1 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Ioo (0 : ℝ) (1 / 2)), ∏ i, τ i ^ (c i * m) * ((c i : ℝ) / τ i) ≤ 1) ∧ ∀ q : ℕ, ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  refine ⟨fun a c lo h0 h1 _ => ?_, fun a c m hm hc => ?_, sum_card_composition_lt⟩
  · refine (setIntegral_cube_prod a (Set.Icc lo (1 / 2)) (fun i t => c i / t)).trans ?_
    exact Finset.prod_congr rfl fun i _ => setIntegral_Icc_const_div (c i) lo h0 h1
  · refine (setIntegral_cube_prod a (Set.Ioo (0 : ℝ) (1 / 2))
      (fun i t => t ^ (c i * m) * ((c i : ℝ) / t))).trans_le ?_
    exact Finset.prod_le_one₀ (fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).1)
      fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTypeLe
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPush

open GlobalTheory.FlagMeas

theorem simplex_meas (a : ℕ) : MeasurableSet (simplexH a) := by
  have h : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, {τ : Fin a → ℝ | i < k → τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ | τ i < 1 / 2}) := by
    ext τ
    simp only [simplexH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 hik, fun i => h2 i⟩,
      fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 i k hik, fun i => h2 i⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_)
    (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  by_cases hik : i < k
  · simpa [hik] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · simp [hik]

theorem dens_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) : Measurable (FlagMeas.dens n f j) := by
  show Measurable fun τ => FlagMeas.dens n f j τ
  simp only [FlagMeas.dens, layerProd, id]
  fun_prop

theorem mem_simplex {I : AutInst} {x : I.GA} {a : ℕ} {j : Fin a → ℕ} {τ : Fin a → ℝ}
    (h : HasType I x j τ) : τ ∈ simplexH a := by
  obtain ⟨S, ⟨-, -, -, hmono, hτ, -⟩, -⟩ := h
  exact ⟨hmono, fun i => ⟨(hτ i).1, (hτ i).2.1⟩⟩

theorem lintegral_type_le : GlobalTheory.FlagMeas.FlagMeasureBound → ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 2 * q + 2 ≤ B.I.n → ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∀ (G : (Fin a → ℝ) → ENNReal) (Φ : B.I.GA → ENNReal), Measurable G → (∀ x τ, HasType B.I x j τ → Φ x ≤ G τ) → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
  intro hFMB B p q hSig hn a j ha hj hsum G Φ hG hΦ
  have := B.haar
  have := B.sf
  obtain ⟨s, hs, hT, hsτ⟩ := GlobalTheory.FlagMeas.type_measurable B.I a j
  set T : Set B.I.GA := {x | ∃ τ, HasType B.I x j τ} with hTdef
  set μ := B.I.muA B.μf with hμ
  set K : ENNReal := μ B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) with hK
  set ρ : Measure (Fin a → ℝ) := (volume.restrict (GlobalTheory.FlagMeas.simplexH a)).withDensity
    (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) with hρ
  have hd : Measurable (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) :=
    (dens_meas B.I.n B.I.f j).ennreal_ofReal

  have h1 : ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := by
    rw [← Measure.restrict_restrict hT]
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hT).2 (Filter.Eventually.of_forall ?_)
    rintro x ⟨τ, hx⟩
    rw [hsτ x τ hx]
    exact hΦ x τ hx

  have h2 : Measure.map s (μ.restrict (T ∩ B.fund)) ≤ K • ρ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply hs hA, Measure.restrict_apply (hs hA), Measure.smul_apply, smul_eq_mul,
      hρ, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hsub : s ⁻¹' A ∩ (T ∩ B.fund) ⊆
        GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund := by
      rintro x ⟨hxA, ⟨τ, hx⟩, hxf⟩
      refine ⟨⟨τ, ⟨?_, mem_simplex hx⟩, hx⟩, hxf⟩
      have hxs : s x = τ := hsτ x τ hx
      rw [← hxs]
      exact hxA
    obtain ⟨-, h0, htop, hle⟩ := hFMB B.I B.μf B.fund B.fund_spec p q hSig hn a j ha hj hsum
      (A ∩ GlobalTheory.FlagMeas.simplexH a) (hA.inter (simplex_meas a)) Set.inter_subset_right
    calc μ (s ⁻¹' A ∩ (T ∩ B.fund))
        ≤ μ (GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund) := measure_mono hsub
      _ ≤ ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            (∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) *
            μ B.fund := (ENNReal.div_le_iff h0.ne' htop.ne).1 hle
      _ = K * ∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
          rw [hK]; ring
  calc ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := h1
    _ = ∫⁻ τ, G τ ∂(Measure.map s (μ.restrict (T ∩ B.fund))) := (lintegral_map hG hs).symm
    _ ≤ ∫⁻ τ, G τ ∂(K • ρ) := lintegral_mono' h2 le_rfl
    _ = K * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
        rw [lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hd hG, smul_eq_mul]
        congr 1
        exact lintegral_congr fun τ => mul_comm _ _

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBound
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearType

open GlobalTheory.FlagMeas

theorem layerProd_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (de : ℝ) :
    Measurable fun τ : Fin a → ℝ => layerProd n f j τ (fun la => 1 + 12 * de / la) := by
  unfold layerProd
  fun_prop

theorem layerProd_nonneg (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (de : ℝ) (hde : 0 ≤ de) (τ : Fin a → ℝ)
    (hτ : ∀ i, 0 < τ i) : 0 ≤ layerProd n f j τ (fun la => 1 + 12 * de / la) := by
  have hG : ∀ la : ℝ, 0 < la → 0 ≤ 1 + 12 * de / la := fun la hla =>
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (by norm_num) hde) hla.le)
  unfold layerProd
  apply mul_nonneg
  · refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_
    exact mul_nonneg (pow_nonneg (hG _ (div_pos (hτ i) (hτ k))) _)
      (pow_nonneg (hG _ (mul_pos (hτ i) (hτ k))) _)
  · refine Finset.prod_nonneg fun i _ => ?_
    exact mul_nonneg (pow_nonneg (hG _ (hτ i)) _) (pow_nonneg (hG _ (pow_pos (hτ i) 2)) _)

theorem integral_count_dens (n f q a : ℕ) (j : Fin a → ℕ) (de lo M : ℝ) (hj : ∑ i, j i ≤ q) (hq : 2 * q ≤ n)
    (hde : 0 ≤ de) (hd : de * q * n * f ≤ 1 / 100) (hlo : 0 < lo) (hlo2 : lo ≤ 1 / 2) (hM : 0 ≤ M) :
    ∫⁻ τ in simplexH a, {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
        (fun τ => ENNReal.ofReal (M * layerProd n f j τ (fun la => 1 + 12 * de / la))) τ *
        ENNReal.ofReal (FlagMeas.dens n f j τ) ≤
      ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i * Real.log (1 / (2 * lo))) := by
  let S : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ => Set.Icc lo (1 / 2))
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hc : ∀ i, 0 ≤ 2 * (f : ℝ) * j i := fun i => by positivity

  have hpt : ∀ τ ∈ simplexH a,
      {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
          (fun τ => ENNReal.ofReal (M * layerProd n f j τ (fun la => 1 + 12 * de / la))) τ *
        ENNReal.ofReal (FlagMeas.dens n f j τ) ≤
      S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ := by
    intro τ hτ
    obtain ⟨hmono, h01⟩ := hτ
    by_cases hl : ∀ i, lo ≤ τ i
    · have hmem : τ ∈ S := fun i _ => ⟨hl i, (h01 i).2.le⟩
      rw [Set.indicator_of_mem (show τ ∈ {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} from hl),
        Set.indicator_of_mem hmem,
        ← ENNReal.ofReal_mul (mul_nonneg hM (layerProd_nonneg n f j de hde τ fun i => (h01 i).1))]
      apply ENNReal.ofReal_le_ofReal
      have h2 : layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ id ≤ 2 :=
        (GlobalTheory.Count.layerProd_count_mul_density_le_two n f q a j τ de hj hq hmono h01 hde hd).1
      have hP : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
        Finset.prod_nonneg fun i _ => div_nonneg (hc i) (h01 i).1.le
      rw [FlagMeas.dens]
      calc M * layerProd n f j τ (fun la => 1 + 12 * de / la) *
            (layerProd n f j τ id * ∏ i, 2 * (f : ℝ) * j i / τ i)
          = M * (layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ id) *
              ∏ i, 2 * (f : ℝ) * j i / τ i := by ring
        _ ≤ M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM) hP
    · simp [Set.indicator_apply, hl]
  have hcont : ContinuousOn (fun τ : Fin a → ℝ => M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) S := by
    refine continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    exact continuousOn_const.div (continuous_apply i).continuousOn
      fun τ hτ => ne_of_gt (lt_of_lt_of_le hlo (hτ i (Set.mem_univ _)).1)
  have hint : IntegrableOn (fun τ : Fin a → ℝ => M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) S :=
    hcont.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hnn : ∀ᵐ τ ∂(volume.restrict S), (0 : (Fin a → ℝ) → ℝ) τ ≤ M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i := by
    refine ae_restrict_of_forall_mem hSm fun τ hτ => ?_
    have hpos : ∀ i, 0 < τ i := fun i => lt_of_lt_of_le hlo (hτ i (Set.mem_univ _)).1
    exact mul_nonneg (mul_nonneg hM (by norm_num))
      (Finset.prod_nonneg fun i _ => div_nonneg (hc i) (hpos i).le)
  have key := (GlobalTheory.sizeIntegrals_and_card_compositions).1 a (fun i => 2 * (f : ℝ) * j i) lo hlo hlo2 hc
  calc _ ≤ ∫⁻ τ in simplexH a,
          S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ :=
        setLIntegral_mono' (GlobalTheory.FlagPush.simplex_meas a) hpt
    _ ≤ ∫⁻ τ, S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ τ in S, ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) := lintegral_indicator hSm _
    _ = ENNReal.ofReal (∫ τ in S, M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i * Real.log (1 / (2 * lo))) := by
        rw [integral_const_mul]
        exact congrArg (fun r => ENNReal.ofReal (M * 2 * r)) key

theorem tsum_le_card {α : Type} (s t : Set α) (hst : s ⊆ t) (ht : t.Finite) (g : α → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ y, ‖g y‖ ≤ M) : ∑' y : s, ‖g y.1‖ₑ ≤ ENNReal.ofReal (M * (t.ncard : ℝ)) := by
  have hs : s.Finite := ht.subset hst
  haveI : Fintype s := hs.fintype
  calc ∑' y : s, ‖g y.1‖ₑ ≤ ∑' _ : s, ENNReal.ofReal M := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hg y.1)
    _ = (Fintype.card s : ENNReal) * ENNReal.ofReal M := by
        rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ (t.ncard : ENNReal) * ENNReal.ofReal M := by
        gcongr
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hst ht
    _ = ENNReal.ofReal (M * (t.ncard : ℝ)) := by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_natCast, mul_comm]

theorem near_terms_one_type : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  intro hF hN hP B Cg n₀ d p q b hn0 hq hC
  obtain ⟨-, -, hf1, -, -, h2q, -, hmin, hdpos, hX16, htpos, hsmall, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn0 hC
  obtain ⟨hDS, hSig, hn0n, hq2, -, -, -, -, -, -, -, hg0p, hg0, hsplit, -⟩ := hC
  have hn1 : 1 ≤ B.I.n := by omega
  have hnpos : (0 : ℝ) < B.I.n := by exact_mod_cast (show 0 < B.I.n by omega)
  have hfpos : (0 : ℝ) < B.I.f := by exact_mod_cast (show 0 < B.I.f by omega)
  have hrad : (Ideal.span {(B.g₀ : 𝓞 B.I.E)}).IsRadical :=
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver B.I.E B.g₀ hg0p hsplit

  set δ : ℝ := 3 * Real.sqrt (B.I.n * epN B) with hδdef
  obtain ⟨hnear, hδ4, hδq⟩ := hN B d (1 / 10 ^ 6) (by norm_num) (by norm_num) hn1 hg0 hrad (epN B) δ rfl rfl
  have hep : 0 < epN B := by
    unfold epN
    exact div_pos (by norm_num) (mul_pos (pow_pos hnpos 8) (pow_pos hfpos 2))
  have hδpos : 0 < δ := mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos hnpos hep))
  have h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by rw [hmin]; exact h120
  obtain ⟨-, hbd, -, -, he1, -, -⟩ := hP B d p q h hDS hSig hgap h120'
  refine ⟨fun x hx => ?_, fun a j ha hj hjq => ?_⟩
  ·
    refine GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs_eq_zero B d x fun γ hγ => ?_
    have hmem := (hnear x γ hγ).2.2
    rw [GlobalTheory.NearLower.nearSet_eq B.I x δ hδpos hδ4 hx] at hmem
    exact hmem
  · set M : ℝ := (∏ v, d v) * (B.e 1).re with hMdef
    have hM : 0 ≤ M := mul_nonneg hdpos.le he1
    set lo : ℝ := tauStar B q b with hlodef
    have hlo2 : lo ≤ 1 / 2 := (hsmall hq).1.le
    have hmeasS : MeasurableSet {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
    have hGm : Measurable (fun τ : Fin a → ℝ => {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
        (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul (layerProd_meas B.I.n B.I.f j δ))).indicator
        hmeasS

    have hΦ : ∀ x τ, HasType B.I x j τ →
        {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ≤
          {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
            (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ := by
      intro x τ hx
      by_cases hl : tauStar B q b ≤ least B.I x
      · obtain ⟨S, hS, -⟩ := id hx
        have h0 := ((GlobalTheory.PointFlag.flag_spec B.I x).2.2 a S τ hS).2 hn1
        have hapos : 0 < a := by omega
        have hlo : ∀ i, lo ≤ τ i := by
          intro i
          have hm : τ ⟨0, hapos⟩ ≤ τ i := hS.2.2.2.1.monotone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
          rw [h0.2 hapos] at hm
          exact le_trans hl hm
        rw [Set.indicator_of_mem (show x ∈ {x | tauStar B q b ≤ least B.I x} from hl),
          Set.indicator_of_mem (show τ ∈ {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} from hlo)]
        obtain ⟨hfin, hcount⟩ := GlobalTheory.NearCount.near_count B.I x δ hδpos hδ4 a j τ hx
        have hsub : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ nearSet B.I x δ := fun γ hγ => (hnear x γ hγ.1).2.2
        calc GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x
            ≤ ENNReal.ofReal (M * ((nearSet B.I x δ).ncard : ℝ)) :=
              tsum_le_card _ _ hsub hfin (fun y => phe B d (x⁻¹ * y * x)) M hM fun y => hbd _
          _ ≤ ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la)) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcount hM)
      · simp [Set.indicator_apply, hl]
    have hfund := hF B.I B.μf B.fund B.fund_spec p q hSig h2q a j ha hj hjq (simplexH a)
      (GlobalTheory.FlagPush.simplex_meas a) le_rfl
    have hfin : B.I.muA B.μf B.fund ≠ ⊤ := hfund.2.2.1.ne
    have hint := integral_count_dens B.I.n B.I.f q a j δ lo M hjq (by omega) hδpos.le (hδq q hq2)
      htpos hlo2 hM

    have hX : 0 < bigX B b := lt_of_lt_of_le (by norm_num) hX16
    have hloX : lo * bigX B b ^ (11 * q) = 1 := by
      rw [hlodef]; unfold tauStar; rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hX.ne')]
    have hL0 : 0 ≤ Real.log (1 / (2 * lo)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hL : Real.log (1 / (2 * lo)) ≤ 11 * q * Real.log (bigX B b) := by
      have h1 : 1 / (2 * lo) ≤ bigX B b ^ (11 * q) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hloX]
      calc Real.log (1 / (2 * lo)) ≤ Real.log (bigX B b ^ (11 * q)) :=
            Real.log_le_log (by positivity) h1
        _ = 11 * q * Real.log (bigX B b) := by rw [Real.log_pow]; push_cast; ring
    have hPQ : ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)) ≤
        (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a := by
      calc ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))
          ≤ ∏ _i : Fin a, 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) := by
            refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
            have hji : (j i : ℝ) ≤ q := by
              exact_mod_cast le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (j k))
                (Finset.mem_univ i)) hjq
            have : 0 ≤ 2 * (B.I.f : ℝ) := by positivity
            calc 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))
                ≤ 2 * (B.I.f : ℝ) * q * Real.log (1 / (2 * lo)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hji this) hL0
              _ ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
                  mul_le_mul_of_nonneg_left hL (by positivity)
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hmain : mainTerm B d = (B.I.muA B.μf B.fund).toReal * M := by
      rw [hMdef]; unfold mainTerm Formalism.MainNotions.S.AutInst.Dstar Formalism.MainNotions.S.AutInst.vol; ring
    calc ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf)
        ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            ∫⁻ τ in simplexH a, {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
              (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ *
              ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) :=
          GlobalTheory.FlagPush.lintegral_type_le hF B p q hSig h2q a j ha hj hjq _ _ hGm hΦ
      _ ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            ENNReal.ofReal (M * 2 * ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))) :=
          mul_le_mul' le_rfl hint
      _ ≤ _ := by
          by_cases hk : GlobalTheory.FlagMeas.kapBd B.I.E p q j ≤ 0
          · rw [ENNReal.ofReal_of_nonpos hk, mul_zero, zero_mul]
            positivity
          · push_neg at hk
            have hvol : 0 ≤ (B.I.muA B.μf B.fund).toReal := ENNReal.toReal_nonneg
            rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hvol,
              ← ENNReal.ofReal_mul (mul_nonneg hvol hk.le)]
            apply ENNReal.ofReal_le_ofReal
            rw [hmain]
            have hc : 0 ≤ (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) :=
              mul_nonneg (mul_nonneg hvol hM) (by linarith)
            calc (B.I.muA B.μf B.fund).toReal * GlobalTheory.FlagMeas.kapBd B.I.E p q j *
                  (M * 2 * ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)))
                = (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
                    ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)) := by ring
              _ ≤ (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
                    (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a :=
                  mul_le_mul_of_nonneg_left hPQ hc
              _ = _ := by ring

end GlobalTheory.NearType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearTerms_moderate_points_one_type_bound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  first | exact @GlobalTheory.NearType.near_terms_one_type | exact GlobalTheory.NearType.near_terms_one_type | (intros; apply GlobalTheory.NearType.near_terms_one_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeSumTypes
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.TypeDecomp

theorem lintegral_biUnion_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (A : ι → Set α) (f : α → ENNReal) :
    ∫⁻ x in ⋃ i ∈ s, A i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in A i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem hasType_cast (I : AutInst) (x : I.GA) {a a' : ℕ} (h : a' = a) (j : Fin a → ℕ) (τ : Fin a → ℝ)
    (H : HasType I x j τ) : ∃ τ', HasType I x (fun i : Fin a' => j (Fin.cast h i)) τ' := by
  subst h
  exact ⟨τ, H⟩

theorem sum_diff (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ)
    (h : ∀ i, r i.succ = r i.castSucc + j i) : r (Fin.last a) = r 0 + ∑ i, j i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have key := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => by
      have := h i.castSucc
      rwa [Fin.succ_castSucc] at this)
    have hl := h (Fin.last a)
    rw [Fin.succ_last] at hl
    simp only [Fin.castSucc_zero] at key
    rw [Fin.sum_univ_castSucc, hl, key]
    ring

theorem exists_type (B : RowsAut) (p q : ℕ) (hs : SigIs B p q) (hn : 1 ≤ B.I.n) (x : B.I.GA)
    (hx : least B.I x < 1 / 2) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, ∃ τ, HasType B.I x c.blocksFun τ := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hprop⟩ := GlobalTheory.PointFlag.flag_spec B.I x
  obtain ⟨hsteps, hlast⟩ := hprop a S τ hF
  have hlt : ∀ i : Fin a, Formalism.HN.rkK (S i.castSucc) < Formalism.HN.rkK (S i.succ) := fun i => (hsteps i).2.1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hj
  have hstep : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hjpos : ∀ i, 0 < j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hT : HasType B.I x j τ := ⟨S, hF, hstep⟩
  have hsum : Formalism.HN.rkK (S (Fin.last a)) = Formalism.HN.rkK (S 0) + ∑ i, j i :=
    GlobalTheory.TypeDecomp.sum_diff a (fun i => Formalism.HN.rkK (S i)) j hstep
  have ha : a ≠ 0 := by
    intro h0
    have := (hlast hn).1.mp h0
    linarith
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  have hiso : Formalism.HN.rkK (stepLt B.I x (1 / 2)) ≤ rkR (B.I.ε v) := (GlobalTheory.FlagIso.flag_isotropic B.I x).2.1 v
  have hq : rkR (B.I.ε v) ≤ q := (min_le_right _ _).trans (hs v).2.le
  have hSl : S (Fin.last a) = stepLt B.I x (1 / 2) := hF.2.2.1
  have h1 : 1 ≤ ∑ i, j i := by
    have := Finset.single_le_sum (f := j) (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero ha⟩)
    have := hjpos ⟨0, Nat.pos_of_ne_zero ha⟩
    omega
  have h2 : ∑ i, j i ≤ q := by
    rw [hSl] at hsum
    omega
  let c : Composition (∑ i, j i) :=
    ⟨List.ofFn j, fun {b} hb => by
      simp only [List.mem_ofFn, Set.mem_range] at hb
      obtain ⟨k, rfl⟩ := hb
      exact hjpos k, by simp [List.sum_ofFn]⟩
  have hlen : c.length = a := by simp [c, Composition.length]
  have hc : c.blocksFun = fun i => j (Fin.cast hlen i) := by
    funext i
    show (List.ofFn j).get i = j (Fin.cast hlen i)
    first
      | rw [List.get_ofFn]
      | simp [List.get_eq_getElem, Fin.cast]
  obtain ⟨τ', h'⟩ := GlobalTheory.TypeDecomp.hasType_cast B.I x hlen j τ hT
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨h1, h2⟩, c, τ', ?_⟩
  rw [hc]
  exact h'

theorem lintegral_le_sum_types : ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 1 ≤ B.I.n → ∀ Φ : B.I.GA → ENNReal, (∀ x, 1 / 2 ≤ least B.I x → Φ x = 0) → ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf) ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) := by
  intro B p q hs hn Φ hΦ
  have hT : ∀ (J : ℕ) (c : Composition J),
      MeasurableSet {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} := fun J c => by
    obtain ⟨s, -, h, -⟩ := GlobalTheory.FlagMeas.type_measurable B.I c.length c.blocksFun
    exact h
  set P : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} with hP
  set U : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund with hU
  have hPm : MeasurableSet P :=
    Finset.measurableSet_biUnion _ fun J _ => Finset.measurableSet_biUnion _ fun c _ => hT J c
  have hcover : B.fund ⊆ U ∪ Pᶜ := by
    intro x hx
    by_cases hxP : x ∈ P
    · left
      simp only [hP, hU, Set.mem_iUnion, Set.mem_inter_iff] at hxP ⊢
      obtain ⟨J, hJ, c, hc, hxc⟩ := hxP
      exact ⟨J, hJ, c, hc, hxc, hx⟩
    · exact Or.inr hxP
  have hzero : ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) = 0 := by
    have hae : ∀ᵐ x ∂((B.I.muA B.μf).restrict Pᶜ), Φ x = 0 := by
      rw [ae_restrict_iff' hPm.compl]
      refine ae_of_all _ fun x hx => hΦ x ?_
      by_contra hlt
      push_neg at hlt
      obtain ⟨J, hJ, c, τ, hτ⟩ := GlobalTheory.TypeDecomp.exists_type B p q hs hn x hlt
      apply hx
      simp only [hP, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨J, hJ, c, Finset.mem_univ c, τ, hτ⟩
    rw [lintegral_congr_ae hae, lintegral_zero]
  calc ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf)
      ≤ ∫⁻ x in U ∪ Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) + ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_union_le _ _ _
    _ = ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) := by rw [hzero, add_zero]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∫⁻ x in ⋃ c ∈ (Finset.univ : Finset (Composition J)),
          {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _
    _ ≤ _ := Finset.sum_le_sum fun J _ => GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _

end GlobalTheory.TypeDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ModerateLogFactorAbsorbed
open Matrix Finset Real

namespace GlobalTheory

theorem moderate_log_factor_absorbed : ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (n f q : ℕ) (rd g b : ℝ), n₀ ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log rd ≤ Real.exp n → Real.log f ≤ Real.sqrt n → 2 ≤ b → Real.log b ≤ Real.exp (1 / 16 * n * f * Real.log n) → 1 ≤ g → g ≤ b ^ Cg → 2 * f * q * (11 * q * Real.log (n * f * rd * g * b)) ≤ Real.exp (1 / 8 * n * f * Real.log n) ∧ 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * Real.log n) ≤ Real.exp (-(1 / 4) * n * f * Real.log n) := by
  intro Cg
  set K : ℝ := 22 * (|Cg| + 4) with hK
  have hC : 0 ≤ |Cg| := abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⌈Real.exp (16 * (1 + K))⌉₊, ?_⟩
  intro n f q rd g b hn hf hq hqn hrd hlrd hlf hb hlb hg hgb
  have hn' : Real.exp (16 * (1 + K)) ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_exp (by positivity)) hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 16 * (1 + K) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn'
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  set L := Real.log n with hLdef
  have hm1 : (n : ℝ) ≤ n * f := by nlinarith
  have hm : (1 : ℝ) ≤ n * f := by linarith
  have hX : (n * f : ℝ) * (1 + K) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX1 : (n * f : ℝ) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX2 : (n * f : ℝ) + K ≤ 1 / 16 * n * f * L := by nlinarith
  set E := Real.exp (1 / 16 * n * f * L) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEn : Real.exp n ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hnE : (n : ℝ) ≤ E := by
    have := Real.add_one_le_exp (n : ℝ); linarith
  constructor
  · have hb0 : 0 < b := by linarith
    have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have h1 : L ≤ E := by
      have := Real.log_le_sub_one_of_pos hn0; linarith
    have h2 : Real.log f ≤ E := by
      have : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
      linarith
    have h3 : Real.log g ≤ |Cg| * E := by
      have h4 : Real.log g ≤ Real.log (b ^ Cg) := Real.log_le_log (by linarith) hgb
      rw [Real.log_rpow hb0] at h4
      have h5 : Cg * Real.log b ≤ |Cg| * Real.log b :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlb0
      have h6 : |Cg| * Real.log b ≤ |Cg| * E := mul_le_mul_of_nonneg_left hlb hC
      linarith
    have hlog : Real.log (n * f * rd * g * b) ≤ (|Cg| + 4) * E := by
      have hf0 : (0 : ℝ) < f := by linarith
      have hrd0 : 0 < rd := by linarith
      have hg0 : 0 < g := by linarith
      rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hg0.ne',
        Real.log_mul (by positivity) hrd0.ne', Real.log_mul hn0.ne' hf0.ne']
      linarith
    have hKE : (n * f : ℝ) * K ≤ E := by
      have a1 : (n * f : ℝ) ≤ Real.exp (n * f) := by
        have := Real.add_one_le_exp (n * f : ℝ); linarith
      have a2 : K ≤ Real.exp K := by
        have := Real.add_one_le_exp K; linarith
      calc (n * f : ℝ) * K ≤ Real.exp (n * f) * Real.exp K :=
            mul_le_mul a1 a2 hK0 (Real.exp_pos _).le
        _ = Real.exp (n * f + K) := (Real.exp_add _ _).symm
        _ ≤ E := Real.exp_le_exp.mpr hX2
    have hEE : Real.exp (1 / 8 * n * f * L) = E * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [hEE]
    calc 2 * (f : ℝ) * q * (11 * q * Real.log (n * f * rd * g * b))
        = (22 * f * q ^ 2) * Real.log (n * f * rd * g * b) := by ring
      _ ≤ (22 * f * q ^ 2) * ((|Cg| + 4) * E) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (22 * f * n) * ((|Cg| + 4) * E) := by gcongr
      _ = (n * f * K) * E := by rw [hK]; ring
      _ ≤ E * E := by gcongr
  · have hqn2 : (q : ℝ) ≤ n := by nlinarith
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : (2 : ℝ) ^ q ≤ Real.exp q := by
      calc (2 : ℝ) ^ q ≤ (Real.exp 1) ^ q := by gcongr
        _ = Real.exp q := by rw [← Real.exp_nat_mul]; simp
    calc 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * L)
        ≤ Real.exp 1 * Real.exp q * Real.exp (-(3 / 8) * n * f * L) := by gcongr
      _ = Real.exp (1 + q + -(3 / 8) * n * f * L) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end GlobalTheory
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearMod

theorem fDeg_eq (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by

  have hE : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hdeg : Module.finrank ℚ I.E = Module.finrank ℚ I.F * 2 := by
    rw [← I.cm.deg2, Module.finrank_mul_finrank]
  have hc := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.E
  have hr : NumberField.InfinitePlace.nrRealPlaces I.E = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr hE
  unfold Formalism.HermitianLatticesTheory.fDeg AutInst.f
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem two_vInv_eq (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_eq]
  ring

theorem one_type_arith (L κ Y : ℝ) (a J : ℕ) (hL : 0 ≤ L) (hJ : 1 ≤ J) (haJ : a ≤ J)
    (hκ : κ ≤ Real.exp (-(1 / 2 * J * L))) (hY0 : 0 ≤ Y) (hY : Y ≤ Real.exp (1 / 8 * L)) :
    2 * κ * Y ^ a ≤ 2 * Real.exp (-(3 / 8) * L) := by

  have hYa : Y ^ a ≤ Real.exp (a * (1 / 8 * L)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hY0 hY a
  have hYa0 : 0 ≤ Y ^ a := pow_nonneg hY0 a
  rcases lt_or_ge κ 0 with hκ0 | hκ0
  · have : κ * Y ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ0.le hYa0
    nlinarith [Real.exp_pos (-(3 / 8) * L)]
  · have h1 : κ * Y ^ a ≤ Real.exp (-(1 / 2 * J * L)) * Real.exp (a * (1 / 8 * L)) :=
      mul_le_mul hκ hYa hYa0 (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have ha' : (a : ℝ) ≤ J := by exact_mod_cast haJ
    have h2 : -(1 / 2 * J * L) + a * (1 / 8 * L) ≤ -(3 / 8) * L := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha') hL, mul_nonneg (sub_nonneg.2 hJ') hL]
    have h3 := Real.exp_le_exp.2 h2
    nlinarith

theorem nearModerate : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.FlagMeas.ConstantBound → GlobalTheory.Dec.NearUnip →
    GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate := by
  intro hFM hCB hNU hPB
  unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate
  intro Cg hCg
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.moderate_log_factor_absorbed Cg
  refine ⟨max n₁ (3 ^ 15), ?_⟩
  intro B d p q b hq hC
  have h8 : 8 ≤ max n₁ (3 ^ 15) := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨-, hrd, hf, -, hpq, -, -, hmin, hd, hX, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b h8 hC
  obtain ⟨hDS, hSig, hn₀, hq2, hlrd, hlf, hb, hlb, -, hg1, hgb, -⟩ := id hC

  have hPt := hPB B d p q h hDS hSig hgap (by rw [hmin]; exact h120)
  have hm : 0 ≤ mainTerm B d := by
    show 0 ≤ (∏ v, d v) * B.I.vol B.μf B.fund * (B.e 1).re
    exact mul_nonneg (mul_nonneg hd.le ENNReal.toReal_nonneg) hPt.2.2.2.2.1

  have hn3 : 3 ^ 15 ≤ B.I.n := (le_max_right _ _).trans hn₀
  have hn1 : 1 ≤ B.I.n := le_trans (by norm_num) hn3
  have hlogn : 15 ≤ Real.log B.I.n := by
    have h3 : Real.exp 15 ≤ (B.I.n : ℝ) := by
      have e1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le e1 15
        _ ≤ (B.I.n : ℝ) := by exact_mod_cast hn3
    have := Real.log_le_log (Real.exp_pos 15) h3
    rwa [Real.log_exp] at this
  have hL : 0 ≤ (B.I.n : ℝ) * B.I.f * Real.log B.I.n := by
    have : (0 : ℝ) ≤ Real.log B.I.n := by linarith
    positivity

  have hY := hn₁ B.I.n B.I.f q B.I.rd (B.g : ℝ) b ((le_max_left _ _).trans hn₀) hf hq hq2 hrd hlrd hlf
    hb hlb (by exact_mod_cast hg1) hgb
  have hlX : 0 ≤ Real.log (bigX B b) := Real.log_nonneg (by linarith)
  have hY0 : 0 ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlX)
  have hY1 : 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) ≤
      Real.exp (1 / 8 * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
    hY.1.trans_eq (by congr 1; ring)

  have hA := GlobalTheory.T.nearTerms_moderate_points_one_type_bound hFM hNU hPB B Cg _ d p q b h8 hq hC
  have hper : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (mainTerm B d *
          (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)))) := by
    intro J hJmem c
    have hJ := Finset.mem_Icc.1 hJmem
    have hsum : ∑ i, c.blocksFun i = J := c.sum_blocksFun
    have ha : 1 ≤ c.length := c.length_pos_of_pos (by omega)
    have hj1 : ∀ i, 1 ≤ c.blocksFun i := fun i => c.one_le_blocksFun i
    refine (hA.2 c.length c.blocksFun ha hj1 (by rw [hsum]; exact hJ.2)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hm
    have hκ := hCB B.I.E B.I.cm.cmUnram p q c.length c.blocksFun hj1 (by rw [hsum]; exact hJ.2)
      (by rw [hpq]; exact hlogn) (by rw [hpq]; exact hq2) (by rw [two_vInv_eq, hpq]; exact hlrd)
      (by rw [fDeg_eq, hpq]; exact hlf)
    rw [hsum, hpq, fDeg_eq] at hκ
    exact one_type_arith _ _ _ c.length J hL hJ.1 c.length_le (hκ.trans_eq (by congr 1; ring)) hY0 hY1

  have hSm : MeasurableSet {x : B.I.GA | tauStar B q b ≤ least B.I x} :=
    measurableSet_le measurable_const (GlobalTheory.LeastVar.continuous_least B.I hn1).measurable
  have hΦ0 : ∀ x, 1 / 2 ≤ least B.I x →
      {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x = 0 :=
    fun x hx => Set.indicator_apply_eq_zero.2 (fun _ => hA.1 x hx)
  set M : ℝ := mainTerm B d * (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))) with hM
  have h2q : (2 : ENNReal) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x ∂(B.I.muA B.μf)
      = ∫⁻ x in B.fund, {x | tauStar B q b ≤ least B.I x}.indicator
          (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]; rfl
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
          ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
            {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_le_sum_types B p q hSig hn1 _ hΦ0
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal M :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hper J hJ c
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ENNReal) * ENNReal.ofReal M := by
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 : ENNReal) ^ q * ENNReal.ofReal M := by
        gcongr
        exact_mod_cast (GlobalTheory.sum_card_composition_lt q).le
    _ = ENNReal.ofReal (2 ^ q * M) := by
        rw [h2q]; exact (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d) := by
        apply ENNReal.ofReal_le_ofReal
        have e2 : Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) =
            Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        have e1 : Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) =
            Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
        rw [e2, hM, e1]
        calc (2 : ℝ) ^ q * (mainTerm B d * (2 * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)))
            = mainTerm B d * (2 * 2 ^ q * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)) := by ring
          _ ≤ mainTerm B d * Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) :=
            mul_le_mul_of_nonneg_left hY.2 hm
          _ = _ := mul_comm _ _

end GlobalTheory.NearMod
