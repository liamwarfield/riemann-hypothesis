module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KsetMulConj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PhiIntegrable
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JKFinA
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

section abstract

variable {K : Type} [Group K] [TopologicalSpace K]

def Fin2 (α : C(K, ℂ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → K → ℂ) (β : ι → C(K, ℂ)), ∀ k₀ κ, α (k₀ * κ) = ∑ i, a i k₀ * β i κ

def finAlg (K : Type) [Group K] [TopologicalSpace K] : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {α | Fin2 α}
  mul_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι × ι', inferInstance, fun i k => a i.1 k * a' i.2 k, fun i => β i.1 * β' i.2, fun k₀ κ => ?_⟩
    rw [ContinuousMap.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousMap.mul_apply]; ring
  add_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim β β', fun k₀ κ => ?_⟩
    rw [ContinuousMap.add_apply, h, h', Fintype.sum_sum_type]
    rfl
  algebraMap_mem' c := ⟨Unit, inferInstance, fun _ _ => c, fun _ => 1, fun k₀ κ => by simp⟩
  star_mem' := by
    rintro α ⟨ι, _, a, β, h⟩
    refine ⟨ι, inferInstance, fun i k => star (a i k), fun i => star (β i), fun k₀ κ => ?_⟩
    rw [ContinuousMap.star_apply, h, star_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul', ContinuousMap.star_apply]

end abstract

variable {k r : ℕ}

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ContinuousDSWOrbit
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inG_rsum {ι : Type*} (s : Finset ι) (r : ι → ℝ) (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i ∈ s, inG ε (X i)) : inG ε (∑ i ∈ s, (r i : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.inG_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact smc_inG_add (smc_inG_rsmul (hX a (Finset.mem_insert_self a s)) (r a))
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

theorem dS_rsum (hσ : IsURepOn (UJset ε) σ) {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (X : ι → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ i ∈ s, inG ε (X i)) {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ (∑ i ∈ s, (r i : ℂ) • X i) v = ∑ i ∈ s, (r i : ℂ) • dS σ (X i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.dS_zero_mat (σ := σ) v
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, inG ε (X i) := fun i hi => hX i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, dS_add_smul hσ (inG_rsum s r X hs)
      (hX a (Finset.mem_insert_self a s)) (r a) hv, ih hs, add_comm]

theorem dS_vsum (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → H) (hv : ∀ i ∈ s, IsSmoothVecU ε σ (v i)) :
    dS σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dS σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dS_smul_vec (σ := σ) 0 X 0
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSmoothVecU ε σ (v i) := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hsum : IsSmoothVecU ε σ (∑ i ∈ s, c i • v i) := by
      clear ih
      induction s using Finset.induction_on with
      | empty => simpa using (isSmoothVecU_zero : IsSmoothVecU ε σ (0 : H))
      | insert b t hb ih2 =>
        rw [Finset.sum_insert hb]
        exact ((hs b (Finset.mem_insert_self b t)).smul (c b)).add
          (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) (fun i hi => hv i (by
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))
            (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dS_add_vec hσ hX ((hv a (Finset.mem_insert_self a s)).smul _)
      hsum, dS_smul_vec, ih hs]

theorem inG_expand {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    Y = ∑ p : (Fin n × Fin n) × Bool, ((cond p.2 (Y p.1.1 p.1.2).re (-(Y p.1.1 p.1.2).im) : ℝ) : ℂ) •
      cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1)) := by
  classical
  have hY1 : S7.cpart1 ε Y = Y := ((smc_cpart Y).2.2.2 hY).1
  set L : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ :=
    { toFun := S7.cpart1 ε, map_zero' := by simpa using smc_cpart1_real (ε := ε) 0 0,
      map_add' := smc_cpart1_add }
  have hdec : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • Matrix.single p.1 p.2 1 +
      ((Y p.1 p.2).im : ℂ) • (Complex.I • Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    rw [smul_smul, ← add_smul, Complex.re_add_im, Matrix.smul_single, smul_eq_mul, mul_one]
  have h2 : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • S7.cpart1 ε (Matrix.single p.1 p.2 1) +
      ((-(Y p.1 p.2).im : ℝ) : ℂ) • S7.cpart2 ε (Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [← hY1, hdec]
    change L (∑ p : Fin n × Fin n, _) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    change S7.cpart1 ε _ = _
    rw [smc_cpart1_add, smc_cpart1_real, smc_cpart1_real, smc_cpart1_I, Complex.ofReal_neg, smul_neg, neg_smul]
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool]
  simp only [cond_true, cond_false]

def FinCont (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (z : S7.KG ε → H) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → S7.KG ε → ℂ) (v : ι → H),
    (∀ i, Continuous (d i)) ∧ (∀ i, IsSmoothVecU ε σ (v i)) ∧ ∀ k, z k = ∑ i, d i k • v i

theorem finCont_step (hσ : IsURepOn (UJset ε) σ) {z : S7.KG ε → H} (hz : FinCont ε σ z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    FinCont ε σ (fun k => dS σ ((S7.toMK k)ᴴ * X * S7.toMK k) (z k)) := by
  classical
  obtain ⟨ι, _, d, v, hd, hv, hz⟩ := hz
  set Y : S7.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => (S7.toMK k)ᴴ * X * S7.toMK k
  have hYc : Continuous Y := by
    have hc := S7.IdA.continuous_toMK (ε := ε)
    exact (hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc
  have hYg : ∀ k, inG ε (Y k) := fun k => inG_conj_K k.2 hX
  set B : (Fin n × Fin n) × Bool → Matrix (Fin n) (Fin n) ℂ := fun p =>
    cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1))
  have hB : ∀ p, inG ε (B p) := by
    rintro ⟨q, _ | _⟩
    · exact (smc_cpart _).2.1
    · exact (smc_cpart _).1
  set r : S7.KG ε → (Fin n × Fin n) × Bool → ℝ := fun k p =>
    cond p.2 (Y k p.1.1 p.1.2).re (-(Y k p.1.1 p.1.2).im)
  refine ⟨ι × ((Fin n × Fin n) × Bool), inferInstance, fun q k => d q.1 k * (r k q.2 : ℂ),
    fun q => dS σ (B q.2) (v q.1), fun q => ?_, fun q => dS_smooth hσ (hB q.2) (hv q.1), fun k => ?_⟩
  · refine (hd q.1).mul (Complex.continuous_ofReal.comp ?_)
    have hent : Continuous fun k => Y k q.2.1.1 q.2.1.2 :=
      (continuous_apply q.2.1.2).comp ((continuous_apply q.2.1.1).comp hYc)
    rcases q with ⟨i, q, _ | _⟩
    · exact (Complex.continuous_im.comp hent).neg
    · exact Complex.continuous_re.comp hent
  · show dS σ (Y k) (z k) = _
    rw [hz k, dS_vsum hσ (hYg k) _ _ _ fun i _ => hv i, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [inG_expand (hYg k)]
    rw [dS_rsum hσ _ _ _ (fun p _ => hB p) (hv i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [r]
    rw [smul_smul, mul_comm]

theorem finCont_dSW (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {u : H} (hu : IsSmoothVecU ε σ u) :
    FinCont ε σ (fun k => dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u) := by
  induction w with
  | nil => exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => u, fun _ => continuous_const, fun _ => hu,
      fun k => by simp [dSW]⟩
  | cons X w ih =>
    exact finCont_step hσ (ih fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (hw X List.mem_cons_self)

theorem continuous_dSW_orbit (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)}
    (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u) :
    Continuous fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u) := by
  obtain ⟨ι, _, d, v, hd, -, hz⟩ := finCont_dSW hσ hw hu
  have e : (fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u)) =
      fun k => ∑ i, d i k • σ (S7.toMK k) (v i) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dSW_conj hσ (k := S7.toMK k) k.2 hw hu, show dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u = _ from hz k, map_sum]
    simp only [map_smul]
  rw [e]
  refine continuous_finsetSum _ fun i _ => (hd i).smul ?_
  exact (hσ.2.2 (v i)).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2
end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FinAlgSepKG
set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem approx_id {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hsep : (Mult1.Down.KF.finAlg K).SeparatesPoints) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (F : ι → K → E) (hF : ∀ i, Continuous (F i)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ α : C(K, ℂ), Mult1.Down.KF.Fin2 α ∧ ∀ i, ‖∫ k, α k • F i k ∂μ - F i 1‖ < δ := by
  classical
  have hint : ∀ (a : C(K, ℂ)) i, Integrable (fun k => a k • F i k) μ := fun a i =>
    integrableOn_univ.mp ((a.continuous.smul (hF i)).continuousOn.integrableOn_compact isCompact_univ)

  set U : Set K := ⋂ i, {k | ‖F i k - F i 1‖ < δ / 3}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt ((hF i).sub continuous_const).norm continuous_const
  have h1U : (1 : K) ∈ U := mem_iInter.2 fun i => by simp [hδ]

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := (1 : K)))
    hU.isClosed_compl (disjoint_singleton_left.2 fun h => h h1U)
  set b : K → ℝ := fun k => 1 - f k
  have hbc : Continuous b := continuous_const.sub f.continuous
  have hb0 : ∀ k, 0 ≤ b k := fun k => by simp only [b]; linarith [(hf01 k).2]
  have hb1 : b 1 = 1 := by simp only [b]; rw [hf0 (mem_singleton 1)]; simp
  have hbU : ∀ k, k ∉ U → b k = 0 := fun k hk => by simp only [b]; rw [hf1 hk]; simp
  have hbcs : HasCompactSupport b := isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  have hcpos : 0 < ∫ k, b k ∂μ :=
    hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbcs hb0 (by rw [hb1]; exact one_ne_zero)
  set c := ∫ k, b k ∂μ
  have hbint : Integrable b μ := integrableOn_univ.mp (hbc.continuousOn.integrableOn_compact isCompact_univ)
  set β : C(K, ℂ) := ⟨fun k => ((b k / c : ℝ) : ℂ), Complex.continuous_ofReal.comp (hbc.div_const c)⟩
  have hβ : ∀ i, ‖∫ k, β k • F i k ∂μ - F i 1‖ ≤ δ / 3 := by
    intro i
    have hβ1 : ∫ k, β k • F i 1 ∂μ = F i 1 := by
      rw [integral_smul_const]
      have : ∫ k, β k ∂μ = 1 := by
        show ∫ k, ((b k / c : ℝ) : ℂ) ∂μ = 1
        rw [integral_complex_ofReal, integral_div]
        rw [show ∫ k, b k ∂μ = c from rfl, div_self hcpos.ne', Complex.ofReal_one]
      rw [this, one_smul]
    have hc : Integrable (fun k => β k • F i 1) μ :=
      integrableOn_univ.mp ((β.continuous.smul continuous_const).continuousOn.integrableOn_compact isCompact_univ)
    rw [← hβ1, ← integral_sub (hint β i) hc]
    calc ‖∫ k, (β k • F i k - β k • F i 1) ∂μ‖ ≤ ∫ k, b k / c * (δ / 3) ∂μ := by
          refine norm_integral_le_of_norm_le ((hbint.div_const c).mul_const _) (Filter.Eventually.of_forall fun k => ?_)
          rw [← smul_sub, norm_smul]
          by_cases hk : k ∈ U
          · have := (mem_iInter.1 hk) i
            simp only [mem_ofPred_eq] at this
            have hn : ‖β k‖ = b k / c := by
              show ‖((b k / c : ℝ) : ℂ)‖ = _
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb0 k) hcpos.le)]
            rw [hn]
            exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hb0 k) hcpos.le)
          · have hn : β k = 0 := by show ((b k / c : ℝ) : ℂ) = 0; rw [hbU k hk]; simp
            rw [hn, norm_zero, zero_mul, hbU k hk, zero_div, zero_mul]
      _ = δ / 3 := by
          rw [integral_mul_const, integral_div]
          rw [show (∫ k, b k ∂μ) = c from rfl, div_self hcpos.ne', one_mul]

  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_finsetSum Finset.univ fun i _ => (hF i).norm).continuousOn
  have hMi : ∀ i k, ‖F i k‖ ≤ M := fun i k => by
    have := hM k (mem_univ k)
    rw [Real.norm_eq_abs] at this
    refine le_trans ?_ ((le_abs_self _).trans this)
    exact Finset.single_le_sum (f := fun i => ‖F i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  set R := |M| * μ.real univ + 1
  have hR : 0 < R := by positivity
  have hη : 0 < δ / 3 / R := by positivity
  have hmem : β ∈ closure ((Mult1.Down.KF.finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
    have : β ∈ (Mult1.Down.KF.finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨α, hα, hαβ⟩ := Metric.mem_closure_iff.1 hmem _ hη
  refine ⟨α, hα, fun i => ?_⟩
  have hdiff : ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ ≤ δ / 3 / R * |M| * μ.real univ := by
    rw [← integral_sub (hint α i) (hint β i)]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [← sub_smul, norm_smul]
    have h1 : ‖α k - β k‖ ≤ δ / 3 / R := by
      have := (β - α).norm_coe_le_norm k
      rw [dist_eq_norm] at hαβ
      rw [norm_sub_rev]
      exact this.trans hαβ.le
    exact mul_le_mul h1 ((hMi i k).trans (le_abs_self M)) (norm_nonneg _) hη.le
  have hsmall : δ / 3 / R * |M| * μ.real univ < δ / 3 := by
    rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ hR]
    have : |M| * μ.real univ < R := by simp [R]
    nlinarith [measureReal_nonneg (μ := μ) (s := univ), abs_nonneg M]
  calc ‖∫ k, α k • F i k ∂μ - F i 1‖
      ≤ ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ + ‖∫ k, β k • F i k ∂μ - F i 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ / 3 + δ / 3 := add_lt_add_of_lt_of_le (hdiff.trans_lt hsmall) (hβ i)
    _ < δ := by linarith

theorem finAlg_sep_KG {n : ℕ} (ε : Fin n → Bool) : (Mult1.Down.KF.finAlg (S7.KG ε)).SeparatesPoints := by
  intro k k' hne
  have hne' : S7.toMK k ≠ S7.toMK k' := fun h => hne (Subtype.ext (Subtype.ext (Units.ext h)))
  obtain ⟨i, j, hij⟩ : ∃ i j, S7.toMK k i j ≠ S7.toMK k' i j := by
    by_contra hc
    push Not at hc
    exact hne' (Matrix.ext hc)
  have hcont : ∀ a b : Fin n, Continuous fun κ : S7.KG ε => S7.toMK κ a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp S7.IdA.continuous_toMK)
  refine ⟨_, ⟨⟨fun κ => S7.toMK κ i j, hcont i j⟩, ?_, rfl⟩, hij⟩
  refine ⟨Fin n, inferInstance, fun l k₀ => S7.toMK k₀ i l, fun l => ⟨fun κ => S7.toMK κ l j, hcont l j⟩,
    fun k₀ κ => ?_⟩
  show (S7.toMK k₀ * S7.toMK κ) i j = _
  rw [Matrix.mul_apply]
  rfl

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem intK {E : Type*} [NormedAddCommGroup E] {f : S7.KG ε → E} (hf : Continuous f) :
    Integrable f (S7.muK ε) := by
  have := S7.compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (S7.muK ε) := by unfold S7.muK; infer_instance
  exact integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem orbitK_continuous (hσ : IsURepOn (UJset ε) σ) (u : H) :
    Continuous fun k : S7.KG ε => σ (S7.toMK k) u :=
  (hσ.2.2 u).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2

theorem toMK_mul_apply (hσ : IsURepOn (UJset ε) σ) (k₀ k : S7.KG ε) (u : H) :
    σ (S7.toMK (k₀ * k)) u = σ (S7.toMK k₀) (σ (S7.toMK k) u) := by
  rw [show S7.toMK (k₀ * k) = S7.toMK k₀ * S7.toMK k from rfl,
    hσ.1.2 _ (smd_inUJ_of_Kset k₀.2) _ (smd_inUJ_of_Kset k.2)]
  rfl

theorem kfin_integral (hσ : IsURepOn (UJset ε) σ) (u : H) {α : C(S7.KG ε, ℂ)} (hα : Mult1.Down.KF.Fin2 α) :
    Formalism.MainNotions.S.IsKFin ε σ (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)) := by
  classical
  have := S7.compactSpace_KG ε
  set x := ∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)
  obtain ⟨ι, _, a, β, hab⟩ := hα
  have hint : ∀ γ : C(S7.KG ε, ℂ), Integrable (fun k => γ k • σ (S7.toMK k) u) (S7.muK ε) := fun γ =>
    intK (γ.continuous.smul (orbitK_continuous hσ u))
  set T : Submodule ℂ H := Submodule.span ℂ (Set.range fun i => ∫ κ, β i κ • σ (S7.toMK κ) u ∂(S7.muK ε))
  have hT : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have key : ∀ k₀ : S7.KG ε, σ (S7.toMK k₀) x ∈ T := by
    intro k₀
    have e1 : σ (S7.toMK k₀) x = ∫ k, α k • σ (S7.toMK (k₀ * k)) u ∂(S7.muK ε) := by
      rw [← (σ (S7.toMK k₀)).integral_comp_comm (hint α)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, toMK_mul_apply hσ]
    set f : S7.KG ε → H := fun κ => α (k₀⁻¹ * κ) • σ (S7.toMK κ) u
    have e2 : ∫ k, α k • σ (S7.toMK (k₀ * k)) u ∂(S7.muK ε) = ∫ κ, f κ ∂(S7.muK ε) := by
      rw [← integral_mul_left_eq_self f k₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [f, inv_mul_cancel_left]
    have e3 : ∫ κ, f κ ∂(S7.muK ε) =
        ∑ i, a i k₀⁻¹ • ∫ κ, β i κ • σ (S7.toMK κ) u ∂(S7.muK ε) := by
      have : f = fun κ => ∑ i, a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u) := by
        funext κ
        simp only [f, hab, Finset.sum_smul, smul_smul]
      rw [this]
      show ∫ κ, ∑ i, a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u) ∂(S7.muK ε) = _
      rw [integral_finsetSum Finset.univ (f := fun i κ => a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u))
        (fun i _ => (hint (β i)).smul (a i k₀⁻¹))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul]
    rw [e1, e2, e3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set S : Submodule ℂ H := Submodule.span ℂ (Set.range fun k : S7.KG ε => σ (S7.toMK k) x)
  have hST : S ≤ T := Submodule.span_le.2 fun v ⟨k, hk⟩ => hk ▸ key k
  refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
  · have : σ (S7.toMK (1 : S7.KG ε)) x = x := by
      rw [show S7.toMK (1 : S7.KG ε) = 1 from rfl, hσ.1.1]
      rfl
    exact this ▸ Submodule.subset_span ⟨1, rfl⟩
  · intro g hg v hv
    obtain ⟨k', rfl⟩ := ffa_Kset (ε := ε) hg
    have hle : S ≤ S.comap (σ (S7.toMK k')) := Submodule.span_le.2 fun w ⟨k, hk⟩ => by
      rw [← hk]
      show σ (S7.toMK k') (σ (S7.toMK k) x) ∈ S
      rw [← toMK_mul_apply hσ]
      exact Submodule.subset_span ⟨k' * k, rfl⟩
    exact hle hv

theorem dSW_integral (hσ : IsURepOn (UJset ε) σ)
    (hsep : ∀ z : H, (∀ y, IsSmoothVecU ε σ y → inner ℂ y z = 0) → z = 0)
    {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u)
    (α : C(S7.KG ε, ℂ)) (hx : IsSmoothVecU ε σ (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε))) :
    dSW σ w (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)) =
      ∫ k, α k • dSW σ w (σ (S7.toMK k) u) ∂(S7.muK ε) := by
  have := S7.compactSpace_KG ε
  have hint1 : Integrable (fun k => α k • σ (S7.toMK k) u) (S7.muK ε) :=
    intK (α.continuous.smul (orbitK_continuous hσ u))
  have hint2 : Integrable (fun k => α k • dSW σ w (σ (S7.toMK k) u)) (S7.muK ε) :=
    intK (α.continuous.smul (continuous_dSW_orbit hσ hw hu))
  refine sub_eq_zero.1 (hsep _ fun y hy => ?_)
  have hwr : ∀ X ∈ w.reverse, inG ε X := fun X hX => hw X (List.mem_reverse.1 hX)
  rw [inner_sub_right, sub_eq_zero, inner_dSW hσ hw hy hx, ← integral_inner hint1, ← integral_inner hint2,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_dSW hσ hw hy (IsSmoothVecU.kStable hσ k.2 hu)]
  ring

section abelian₂

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem sigLam_smooth_of_genSub {y : smD ε (rreg ε)}
    (hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀) :
    IsSmoothVecU ε (sigLam ε Ψ v₀) (⟨(y : L2 ε), hyH⟩ : Hlam ε Ψ v₀) := by
  have h := (mem_smD_iff ε (rreg ε) (y : L2 ε)).1 y.2
  exact smoothOnGV_clm (Hlam ε Ψ v₀).orthogonalProjectionOnto h

theorem sigLam_sep (z : Hlam ε Ψ v₀)
    (hz : ∀ y, IsSmoothVecU ε (sigLam ε Ψ v₀) y → inner ℂ y z = 0) : z = 0 := by
  have hcl : IsClosed {v : L2 ε | inner ℂ v (z : L2 ε) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : (((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype : Submodule ℂ (L2 ε)) :
      Set (L2 ε)) ⊆ {v : L2 ε | inner ℂ v (z : L2 ε) = 0} := by
    rintro v ⟨y, hy, rfl⟩
    have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ :=
      Submodule.le_topologicalClosure _ ⟨y, hy, rfl⟩
    have := hz _ (sigLam_smooth_of_genSub hyH)
    rwa [Submodule.coe_inner] at this
  have hzc : (z : L2 ε) ∈ closure (((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype :
      Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    have := z.2
    unfold Hlam closGen at this
    rwa [← Submodule.topologicalClosure_coe]
  have h0 : inner ℂ (z : L2 ε) (z : L2 ε) = (0 : ℂ) := hcl.closure_subset_iff.2 hsub hzc
  exact Subtype.ext (inner_self_eq_zero.1 h0)

end abelian₂

end ReciprocityTheory.ChartRestriction.DS.DecInf
