module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalfStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumTwoPowPredMulExpNegLeExpNegThird
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumTwoPowPredMulExpNegLeExpNegThird
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem sum_two_pow_pred_mul_pow_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4) (q : ℕ) :
    ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * r ^ J ≤ 2 * r * (1 - (1 / 2) ^ q) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have h2 : (2 * r) ^ n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have h3 : (2 : ℝ) ^ n * r ^ (n + 1) = r * (2 * r) ^ n := by rw [mul_pow]; ring
    have h4 : r * (2 * r) ^ n ≤ r * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left h2 h0
    have h5 : 2 * r * (1 - (1 / 2 : ℝ) ^ (n + 1))
        = 2 * r * (1 - (1 / 2) ^ n) + r * (1 / 2 : ℝ) ^ n := by ring
    rw [h3, h5]
    linarith

theorem sum_two_pow_pred_mul_exp_neg_le :
    ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  intro q x hx
  have hr : ∀ J : ℕ, Real.exp (-(1 / 2 * J * x)) = Real.exp (-(x / 2)) ^ J := by
    intro J
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hr]
  have h0 : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
  have h1 : Real.exp (-(x / 2)) ≤ 1 / 4 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    have := Real.add_one_le_exp (x / 2)
    linarith
  refine (sum_two_pow_pred_mul_pow_le _ h0.le h1 q).trans ?_
  have h2 : Real.exp (-(1 / 3 * x)) = Real.exp (x / 6) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (2 : ℝ) ≤ Real.exp (x / 6) := by
    have := Real.add_one_le_exp (x / 6)
    linarith
  have h4 : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  rw [h2]
  nlinarith [mul_nonneg h0.le h4, mul_le_mul_of_nonneg_right h3 h0.le]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumTwoPowPredMulExpNegLeExpNegThirdStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_two_pow_pred_mul_exp_neg_le_exp_neg_third : ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  first | exact @GlobalTheory.sum_two_pow_pred_mul_exp_neg_le | exact GlobalTheory.sum_two_pow_pred_mul_exp_neg_le | (intros; apply GlobalTheory.sum_two_pow_pred_mul_exp_neg_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagSizeDensityLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagSizeDensityLeOne
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DensityIntegral

theorem integral_cube (a : ℕ) (c : Fin a → ℕ) (hc : ∀ i, 1 ≤ c i) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1), ∏ i, (c i : ℝ) * τ i ^ (c i - 1) = 1 := by
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (i : Fin a) (t : ℝ) => (c i : ℝ) * t ^ (c i - 1))]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, integral_pow]
  obtain ⟨m, hm⟩ : ∃ m, c i = m + 1 := ⟨c i - 1, by have := hc i; omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel, one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero]
  push_cast
  field_simp

theorem dens_le (n f a : ℕ) (j : Fin a → ℕ) (hf : 1 ≤ f) (hj : ∀ i, 1 ≤ j i) (hn : 2 * ∑ i, j i + 1 ≤ n)
    (τ : Fin a → ℝ) (hτ : τ ∈ simplexH a) :
    FlagMeas.dens n f j τ ≤ ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) := by
  have h2 := (GlobalTheory.Count.layerProd_count_mul_density_le_two n f (∑ i, j i) a j τ 0 le_rfl (by omega)
    hτ.1 hτ.2 le_rfl (by norm_num)).2
  have h3 : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
    Finset.prod_nonneg fun i _ => by have := (hτ.2 i).1; positivity
  refine (mul_le_mul_of_nonneg_right h2 h3).trans ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => by have := (hτ.2 i).1; positivity) fun i _ => ?_
  obtain ⟨h0, h1⟩ := hτ.2 i
  have hc : 1 ≤ 2 * f * j i := Nat.mul_pos (by omega) (hj i)
  have he : 2 * f * j i ≤ 2 * j i * (n - 2 * ∑ l, j l) * f := by
    calc 2 * f * j i = 2 * j i * 1 * f := by ring
      _ ≤ _ := by gcongr; omega
  have h4 : τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) ≤ τ i ^ (2 * f * j i - 1) * τ i := by
    rw [← pow_succ]
    exact pow_le_pow_of_le_one h0.le (by linarith) (by omega)
  calc _ ≤ τ i ^ (2 * f * j i - 1) * τ i * (2 * (f : ℝ) * j i / τ i) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = _ := by push_cast; field_simp

theorem lintegral_dens_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  intro n f a j hf hj hn
  set box : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1) with hbox
  have hc : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : simplexH a ⊆ box := fun τ hτ i _ => ⟨(hτ.2 i).1.le, by linarith [(hτ.2 i).2]⟩
  have hm : MeasurableSet (simplexH a) := by
    have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
        ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
      ext τ
      simp [simplexH, StrictMono]
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k))
      (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const))
  set g : (Fin a → ℝ) → ℝ := fun τ => ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) with hg
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hint : IntegrableOn g box := hcont.continuousOn.integrableOn_compact hc
  calc _ ≤ ∫⁻ τ in simplexH a, ENNReal.ofReal (g τ) :=
        setLIntegral_mono' hm fun τ hτ => ENNReal.ofReal_le_ofReal (dens_le n f a j hf hj hn τ hτ)
    _ ≤ ∫⁻ τ in box, ENNReal.ofReal (g τ) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ τ in box, g τ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        refine (ae_restrict_iff' hc.measurableSet).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
        refine Finset.prod_nonneg fun i _ => ?_
        have := (hτ i trivial).1
        positivity
    _ = 1 := by
        rw [integral_cube a (fun i => 2 * f * j i) fun i => Nat.mul_pos (by omega) (hj i), ENNReal.ofReal_one]

end GlobalTheory.DensityIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagSizeDensityLeOneStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagSizeDensity_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  first | exact @GlobalTheory.DensityIntegral.lintegral_dens_le_one | exact GlobalTheory.DensityIntegral.lintegral_dens_le_one | (intros; apply GlobalTheory.DensityIntegral.lintegral_dens_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.NonzeroFlag

theorem telescope : ∀ (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ),
    (∀ i : Fin a, r i.succ = r i.castSucc + j i) → r (Fin.last a) = r 0 + ∑ i, j i := by
  intro a
  induction a with
  | zero => intro r j _; simp
  | succ a ih =>
    intro r j h
    have h1 := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => h i.castSucc)
    have h2 := h (Fin.last a)
    rw [Fin.sum_univ_castSucc]
    have h3 : r (Fin.last (a + 1)) = r (Fin.last a).castSucc + j (Fin.last a) := h2
    have h4 : r (Fin.last a).castSucc = r 0 + ∑ i : Fin a, j i.castSucc := h1
    omega

theorem exists_composition (a : ℕ) (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (J : ℕ) (hJ : ∑ i, j i = J)
    (P : ∀ a : ℕ, (Fin a → ℕ) → Prop) (h : P a j) :
    ∃ c : Composition J, P c.length c.blocksFun := by
  have key : ∀ (b : ℕ) (e : b = a) (j' : Fin b → ℕ), (∀ i, j' i = j (Fin.cast e i)) → P b j' := by
    intro b e j' hh
    subst e
    have : j' = j := funext hh
    rw [this]; exact h
  refine ⟨⟨List.ofFn j, ?_, ?_⟩, key _ (by simp [Composition.length]) _ ?_⟩
  · intro i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
    exact hj k
  · rw [List.sum_ofFn, hJ]
  · intro i
    simp [Composition.blocksFun]
    rfl

theorem measurableSet_simplexH (a : ℕ) : MeasurableSet (simplexH a) := by
  have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
    ext τ
    simp [simplexH, StrictMono]
  rw [this]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · exact MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem mem_typeSet (I : AutInst) (p q : ℕ) (hs : HasSig I p q) (x : I.GA) (hx : stepLt I x (1 / 2) ≠ ⊥) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, x ∈ typeSet I c.blocksFun (simplexH c.length) := by
  obtain ⟨⟨a, S, τ, hF⟩, -, h3⟩ := GlobalTheory.PointFlag.flag_spec I x
  have h3 := (h3 a S τ hF).1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hjdef
  have hj1 : ∀ i, 1 ≤ j i := fun i => by have := (h3 i).2.1; simp only [hjdef]; omega
  have hj2 : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := (h3 i).2.1; simp only [hjdef]; omega
  have htel := telescope a (fun i => Formalism.HN.rkK (S i)) j hj2
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hr := (GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual I x).2.1 v
  have hq : rkR (I.ε v) ≤ q := by
    rw [← (hs v).2]; exact min_le_right _ _
  have hle : ∑ i, j i ≤ q := by
    simp only [hF.2.2.1] at htel
    omega
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    rw [← hF.2.2.1, ← hF.1]; rfl
  have hge : 1 ≤ ∑ i, j i :=
    (hj1 ⟨0, Nat.pos_of_ne_zero ha⟩).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (mem_univ _))
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨hge, hle⟩, ?_⟩
  refine exists_composition a j hj1 _ rfl (fun a j => x ∈ typeSet I j (simplexH a)) ?_
  exact ⟨τ, ⟨hF.2.2.2.1, fun i => ⟨(hF.2.2.2.2.1 i).1, (hF.2.2.2.2.1 i).2.1⟩⟩, S, hF, hj2⟩

theorem nonzeroFlagBound : VolumeStep → NonzeroFlagBound := by
  intro hV I μf _ _ fund hfund p q hs hn hq hrd hf
  obtain ⟨hfd, hv, -, hf1, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq := hpq p q hs
  have hn16 : 16 ≤ I.n := by
    have hpos : (0 : ℝ) < I.n := by
      rcases Nat.eq_zero_or_pos I.n with h | h
      · rw [h] at hn; simp at hn; linarith
      · exact_mod_cast h
    have := Real.log_le_sub_one_of_pos hpos
    have : (16 : ℝ) ≤ I.n := by linarith
    exact_mod_cast this
  have h2q : 2 * q + 2 ≤ I.n := by nlinarith
  set X : ℝ := I.n * I.f * Real.log I.n with hX
  have hX15 : 15 ≤ X := by
    have h1 : (1 : ℝ) ≤ I.n := by exact_mod_cast (by omega : 1 ≤ I.n)
    have h2 : (1 : ℝ) ≤ I.f := by exact_mod_cast hf1
    have h3 : (1 : ℝ) ≤ I.n * I.f := one_le_mul_of_one_le_of_one_le h1 h2
    rw [hX]; nlinarith
  have hone : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) := by
    intro J hJ c
    obtain ⟨hJ1, hJq⟩ := Finset.mem_Icc.mp hJ
    have hsum := c.sum_blocksFun
    have hT := (GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV I μf fund hfund p q hs h2q c.length c.blocksFun
      (c.length_pos_of_pos hJ1) c.one_le_blocksFun (by omega) _ (measurableSet_simplexH _) subset_rfl).2.2.2
    have hD := GlobalTheory.T.lintegral_flagSizeDensity_le_one I.n I.f c.length c.blocksFun hf1 c.one_le_blocksFun (by omega)
    have hK := GlobalTheory.T.flag_explicit_constant_le_exp_neg_half I.E I.cm.cmUnram p q c.length c.blocksFun c.one_le_blocksFun (by omega)
      (by rw [hpq]; exact hn) (by rw [hpq]; exact hq) (by rw [hpq, hv]; exact hrd) (by rw [hpq, hfd]; exact hf)
    rw [hpq, hfd, hsum] at hK
    refine hT.trans ((mul_le_mul_right hD _).trans ?_)
    rw [mul_one]
    refine ENNReal.ofReal_le_ofReal (hK.trans (le_of_eq ?_))
    rw [hX]; congr 1; ring
  have hsub : {x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund ⊆
      ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
        typeSet I c.blocksFun (simplexH c.length) ∩ fund := by
    rintro x ⟨hx, hxf⟩
    obtain ⟨J, hJ, c, hc⟩ := mem_typeSet I p q hs x hx
    simp only [Set.mem_iUnion]
    exact ⟨J, hJ, c, mem_univ _, hc, hxf⟩
  have hμ : I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) ≤
      ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) :=
    (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun J _ => measure_biUnion_finset_le _ _))
  calc I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) / I.muA μf fund
      ≤ (∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund)) / I.muA μf fund :=
        ENNReal.div_le_div_right hμ _
    _ = ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hone J hJ c
    _ = ENNReal.ofReal (∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * X))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun J _ => by positivity)]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((GlobalTheory.T.sum_two_pow_pred_mul_exp_neg_le_exp_neg_third q X hX15).trans (le_of_eq ?_))
        rw [hX]; congr 1; ring

end GlobalTheory.NonzeroFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductioStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction : VolumeStep → NonzeroFlagBound := by
  first | exact @GlobalTheory.NonzeroFlag.nonzeroFlagBound | exact GlobalTheory.NonzeroFlag.nonzeroFlagBound | (intros; apply GlobalTheory.NonzeroFlag.nonzeroFlagBound <;> assumption)
end
