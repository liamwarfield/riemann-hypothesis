module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSum
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
noncomputable section

namespace GlobalTheory.CompactDualQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def sg {P Q : ℕ} : Fin P ⊕ Fin Q → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

def SignCompat (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Prop :=
  ∀ i, sg (e (some i)) = sg i

def l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : ℝ := ∑ i, ∑ j, ‖Z i j‖

def gauge (g : UpqT P Q) : ℝ := l1 (UpqT.mat g - 1)

def baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Sp P Q := Pi.single (e none) 1

def ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ + 2 * ∑ i, ‖y (e (some i))‖

def tanGauge (t : ℝ × Sp P' Q') : ℝ := |t.1| + 2 * ∑ i, ‖t.2 i‖

def polarPt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim
    ((Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I)) t.2

def IsBlockEmb (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  ∀ g, UpqT.mat (j g) (e none) (e none) = 1 ∧ (∀ b, UpqT.mat (j g) (e none) (e (some b)) = 0) ∧
    (∀ a, UpqT.mat (j g) (e (some a)) (e none) = 0) ∧
    ∀ a b, UpqT.mat (j g) (e (some a)) (e (some b)) = UpqT.mat g a b

def expBall (P Q : ℕ) (r : ℝ) : Set (UpqT P Q) :=
  {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
    NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}

theorem sg_eq (i : Fin P ⊕ Fin Q) : sg i = 1 ∨ sg i = -1 := by
  rcases i with i | i <;> simp [sg]

theorem sg_ne_zero (i : Fin P ⊕ Fin Q) : sg i ≠ 0 := by
  rcases sg_eq i with h | h <;> rw [h] <;> norm_num

theorem qf_eq_sum (x : Sp P Q) : qf x = ∑ i, sg i * Complex.normSq (x i) := by
  simp [qf, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem qf_baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    qf (baseVec e) = sg (e none) := by
  rw [qf_eq_sum, Finset.sum_eq_single (e none)]
  · simp [baseVec]
  · intro b _ hb; simp [baseVec, hb]
  · simp

theorem card_eq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : P + Q = P' + Q' + 1 := by
  simpa using (Fintype.card_congr e).symm

theorem polarPt_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') :
    polarPt e t (e none) =
      (Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I) := by
  simp [polarPt]

theorem polarPt_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : polarPt e t (e (some i)) = t.2 i := by
  simp [polarPt]

theorem weightAbsEntrySum_nonneg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : 0 ≤ l1 Z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_matrixEntryAbsSum : Continuous (l1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm

theorem continuous_gauge : Continuous (gauge : UpqT P Q → ℝ) :=
  continuous_matrixEntryAbsSum.comp
    ((Units.continuous_val.comp continuous_subtype_val : Continuous UpqT.mat).sub continuous_const)

theorem ptGauge_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) :
    0 ≤ ptGauge e y := by
  unfold ptGauge; positivity

theorem continuous_ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (ptGauge e) := by
  unfold ptGauge; fun_prop

theorem tanGauge_nonneg (t : ℝ × Sp P' Q') : 0 ≤ tanGauge t := by
  unfold tanGauge; positivity

theorem continuous_tanGauge : Continuous (tanGauge : ℝ × Sp P' Q' → ℝ) := by
  unfold tanGauge; fun_prop

theorem tendsto_div_of_squeeze {F V A : ℝ → ℝ≥0∞} {n : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hV : ∀ t r : ℝ, 0 < t → 0 < r → V (t * r) = ENNReal.ofReal (t ^ n) * V r)
    (hF : Tendsto (fun r => F r / V r) (𝓝[>] 0) (𝓝 c))
    (hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), F (t⁻¹ * r) ≤ A r ∧ A r ≤ F (t * r)) :
    Tendsto (fun r => A r / V r) (𝓝[>] 0) (𝓝 c) := by
  have key : ∀ t : ℝ, 0 < t →
      Tendsto (fun r => F (t * r) / V r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ n) * c)) := by
    intro t ht
    have h1 : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos ht hr
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) (hF.comp h1)
      (Or.inr ENNReal.ofReal_ne_top)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h0 : ENNReal.ofReal (t ^ n) ≠ 0 := by simpa using pow_pos ht n
    simp only [Function.comp, hV t r ht hr]
    rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top]
  have lim : ∀ u : ℝ → ℝ, ContinuousAt u 1 → u 1 = 1 →
      Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n) * c) (𝓝[>] 1) (𝓝 c) := by
    intro u hu h1
    have h3 : Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n)) (𝓝 1) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.continuousAt.comp (hu.pow n)).tendsto
      simp only [Function.comp, Pi.pow_apply, h1, one_pow, ENNReal.ofReal_one] at this
      exact this
    have := ENNReal.Tendsto.mul_const (b := c) h3 (Or.inr hc)
    rw [one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t⁻¹) (continuousAt_inv₀ one_ne_zero) inv_one).eventually
      (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t⁻¹ (inv_pos.2 (by linarith))).eventually (lt_mem_nhds h1), hA t ht]
      with r h3 h4 using h3.trans_le (ENNReal.div_le_div_right h4.1 _)
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t) continuousAt_id rfl).eventually
      (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t (by linarith)).eventually (gt_mem_nhds h1), hA t ht]
      with r h3 h4 using (ENNReal.div_le_div_right h4.2 _).trans_lt h3

end GlobalTheory.CompactDualQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChange
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChange
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq_zcHom {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) : zc x = zcHom q x := rfl

theorem zc_continuous' {q : ℕ} [Fact q.Prime] : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def linZ {q : ℕ} [Fact q.Prime] {κ κ' : Type} [Fintype κ] (a : κ' → κ → ℤ_[q]) :
    C(κ → ℤ_[q], κ' → ℤ_[q]) :=
  ⟨fun x i => ∑ j, a i j * x j, by fun_prop⟩

def pullCLM {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : C(Y, ℂ_[q]) →L[ℂ_[q]] C(X, ℂ_[q]) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp A
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } 1 (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
        exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => f.norm_coe_le_norm (A x))

theorem pullCLM_norm_le {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : ‖(pullCLM (q := q) A)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem pullCLM_apply {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) (f : C(Y, ℂ_[q])) : pullCLM A f = f.comp A := rfl

def monoC {q : ℕ} [Fact q.Prime] {κ : Type} {k : ℕ} (σ : Fin k → κ) : C(κ → ℤ_[q], ℂ_[q]) :=
  ⟨fun x => ∏ l, zc (x (σ l)), by
    exact continuous_finsetProd _ fun l _ => zc_continuous'.comp (continuous_apply (σ l))⟩

theorem momInt_push (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q])
    (G : V → ℂ) (hc : ∀ i j, ι (c i j) = zc (a i j)) (hw : ∀ i, w i = ∑ j, c i j • v j) (h : MomInt ι v G) :
    MomInt ι w G := by
  classical
  obtain ⟨μ, hμ, hm⟩ := h
  refine ⟨μ.comp (pullCLM (linZ a)), ?_, ?_⟩
  · calc ‖μ.comp (pullCLM (linZ a))‖ ≤ ‖μ‖ * ‖pullCLM (q := q) (linZ a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hμ (pullCLM_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro k j f hf
    have hfe : pullCLM (linZ a) f = ∑ σ : Fin k → κ, (∏ l, zc (a (j l) (σ l))) • monoC σ := by
      ext x
      rw [pullCLM_apply, ContinuousMap.comp_apply, hf]
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        monoC, ContinuousMap.coe_mk, linZ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [zc_eq_zcHom, map_sum, map_mul]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]
    have hd : iteratedFDeriv ℂ k G 0 (fun l => w (j l)) =
        ∑ σ : Fin k → κ, (∏ l, c (j l) (σ l)) • iteratedFDeriv ℂ k G 0 (fun l => v (σ l)) := by
      simp only [hw]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousLinearMap.comp_apply, hfe, hd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_eq_mul, map_mul, map_prod, map_smul, smul_eq_mul, ← hm k σ (monoC σ) (fun _ => rfl)]
    simp only [hc]

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChangeStatement
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q]) (G : V → ℂ), (∀ i j, ι (c i j) = zc (a i j)) → (∀ i, w i = ∑ j, c i j • v j) → MomInt ι v G → MomInt ι w G := by
  first | exact @GlobalTheory.MomN.momInt_push | exact GlobalTheory.MomN.momInt_push | (intros; apply GlobalTheory.MomN.momInt_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.RealZeroNearOne

theorem analyticAt_L {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) (z : ℂ) :
    AnalyticAt ℂ (LFunction χ) z := (differentiable_LFunction h).analyticAt z

theorem order_ne_top {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) (z : ℂ) :
    analyticOrderAt (LFunction χ) z ≠ ⊤ := by
  intro htop
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => analyticAt_L h w)] at htop
  have h2 : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl h) (by norm_num)
  exact h2 (by rw [htop, Pi.zero_apply])

theorem le_order {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) (z : ℂ) (n : ℕ)
    (hn : ∀ i < n, iteratedDeriv i (LFunction χ) z = 0) :
    n ≤ analyticOrderNatAt (LFunction χ) z := by
  have hn' : (n : ℕ∞) ≤ analyticOrderAt (LFunction χ) z :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_L h z)).mpr hn
  rw [← Nat.cast_analyticOrderNatAt (order_ne_top h z)] at hn'
  exact_mod_cast hn'

theorem re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) {z : ℂ}
    (hz : LFunction χ z = 0) : z.re < 1 := by
  by_contra hc
  exact LFunction_ne_zero_of_one_le_re χ (.inl h) (not_lt.mp hc) hz

theorem exists_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ T : Finset ℝ,
    (∀ β ∈ T, 2 / 3 ≤ β ∧ LFunction χ β = 0) →
    -(deriv (LFunction χ) σ / LFunction χ σ).re ≤ C * Real.log (2 * q)
      - ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) := by
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum
  refine ⟨C, hC, fun q _ χ hχ σ hσ hσ2 T hT => ?_⟩
  have hs : ‖(σ : ℂ) - (3 / 2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 2 / 3 := by
    have e : (σ : ℂ) - (3 / 2 + ((0 : ℝ) : ℂ) * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hLσ : LFunction χ σ ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by rw [Complex.ofReal_re]; linarith)
  obtain ⟨hfin, hbd⟩ := hb q χ hχ 0 σ hs hLσ
  set f : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (σ - w) with hf
  set D := deriv (LFunction χ) σ / LFunction χ σ with hD
  have hlog : Real.log (q * (|(0 : ℝ)| + 2)) = Real.log (2 * q) := by
    congr 1; rw [abs_zero, zero_add, mul_comm]
  rw [hlog] at hbd
  have hre := (Complex.abs_re_le_norm _).trans hbd
  rw [Complex.sub_re] at hre
  have hsub : T.map ⟨((↑) : ℝ → ℂ), Complex.ofReal_injective⟩ ⊆ hfin.toFinset := by
    intro w hw
    rw [Finset.mem_map] at hw
    obtain ⟨β, hβ, rfl⟩ := hw
    obtain ⟨hβ1, hβ2⟩ := hT β hβ
    have hβlt : β < 1 := by simpa using re_lt_one hχ hβ2
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, hβ2⟩
    have e : (β : ℂ) - (3 / 2 + ((0 : ℝ) : ℂ) * I) = ((β - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    simp only [Function.Embedding.coeFn_mk]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hST : ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) ≤
      (∑ᶠ w ∈ {w : ℂ | ‖w - (3 / 2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 5 / 6 ∧ LFunction χ w = 0}, f w).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    calc ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β)
        = ∑ w ∈ T.map ⟨((↑) : ℝ → ℂ), Complex.ofReal_injective⟩, (f w).re := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun β _ => ?_
          simp only [Function.Embedding.coeFn_mk, hf]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, ← Complex.ofReal_div,
            Complex.ofReal_re]
      _ ≤ ∑ w ∈ hfin.toFinset, (f w).re := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun w hw _ => ?_
          rw [Set.Finite.mem_toFinset] at hw
          have hwre : w.re < 1 := re_lt_one hχ hw.2
          simp only [hf]
          rw [div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re]
          refine mul_nonneg (Nat.cast_nonneg _) (div_nonneg ?_ (Complex.normSq_nonneg _))
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith
  have := neg_abs_le (D.re - (∑ᶠ w ∈ {w : ℂ | ‖w - (3 / 2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 5 / 6 ∧
    LFunction χ w = 0}, f w).re)
  linarith

theorem main : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) (β β' : ℝ), χ ≠ 1 → ψ ≠ 1 → χ ^ 2 = 1 → ψ ^ 2 = 1 → 1 - c / Real.log (2 * q) ≤ β → 1 - c / Real.log (2 * q) ≤ β' → LFunction χ β = 0 → LFunction ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (LFunction χ) β ≠ 0 := by
  obtain ⟨C1, hC1, h1⟩ := GlobalTheory.T.neg_re_logDeriv_principalLFunction_le
  obtain ⟨C2, hC2, h2⟩ := exists_bound
  set K := C1 + 3 * C2 with hKdef
  have hK : 0 < K := by positivity
  set ε : ℝ := min (1 / 2) (1 / (4 * K)) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := min_le_left _ _
  have hKε : K * ε ≤ 1 / 4 := by
    calc K * ε ≤ K * (1 / (4 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = 1 / 4 := by field_simp
  refine ⟨ε / 8, by positivity, ?_⟩
  intro q _ χ ψ β β' hχ hψ hχ2 hψ2 hβ hβ' hLβ hLβ'
  set L := Real.log (2 * q) with hLdef
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL : 1 / 2 < L := by
    have h2q : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hLpos : 0 < L := by linarith
  have hcL : (ε / 8) / L ≤ 1 / 3 := by
    rw [div_le_iff₀ hLpos]; linarith
  have hβ23 : 2 / 3 ≤ β := by linarith
  have hβ23' : 2 / 3 ≤ β' := by linarith
  have hb1 : β < 1 := by simpa using re_lt_one hχ hLβ
  have hb1' : β' < 1 := by simpa using re_lt_one hψ hLβ'
  have hu : (1 - β) * L ≤ ε / 8 := (le_div_iff₀ hLpos).mp (by linarith)
  have hu' : (1 - β') * L ≤ ε / 8 := (le_div_iff₀ hLpos).mp (by linarith)
  set σ : ℝ := 1 + ε / L with hσdef
  have hεL : ε / L * L = ε := div_mul_cancel₀ ε (ne_of_gt hLpos)
  have hσ1 : 1 < σ := by have := div_pos hε hLpos; linarith
  have hσ2 : σ ≤ 2 := by
    have : ε / L ≤ 1 := (div_le_one hLpos).mpr (by linarith)
    linarith
  have hs1 : 1 / (σ - 1) = L / ε := by
    rw [hσdef, add_sub_cancel_left, one_div_div]
  have hwε : ε * (L / ε) = L := mul_div_cancel₀ L (ne_of_gt hε)
  have hP : -(deriv (LFunction (1 : DirichletCharacter ℂ q)) σ /
      LFunction (1 : DirichletCharacter ℂ q) σ).re ≤ L / ε + C1 * L := by
    have := h1 q σ 0 hσ1 hσ2
    simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at this
    have e : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
      rw [show (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    rw [e, hs1, mul_comm (q : ℝ) 2] at this
    exact this
  have o1 : (1 : ℝ) ≤ analyticOrderNatAt (LFunction χ) β := by
    exact_mod_cast le_order hχ β 1 (by intro i hi; interval_cases i; simpa using hLβ)
  have o1' : (1 : ℝ) ≤ analyticOrderNatAt (LFunction ψ) β' := by
    exact_mod_cast le_order hψ β' 1 (by intro i hi; interval_cases i; simpa using hLβ')
  have hpos : 0 < σ - β := by linarith
  have hpos' : 0 < σ - β' := by linarith
  have t1 : 1 / (σ - β) ≤ (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) :=
    div_le_div_of_nonneg_right o1 hpos.le
  have t1' : 1 / (σ - β') ≤ (analyticOrderNatAt (LFunction ψ) β' : ℝ) / (σ - β') :=
    div_le_div_of_nonneg_right o1' hpos'.le
  have hKL : K * L = C1 * L + 3 * (C2 * L) := by rw [hKdef]; ring
  have hC2L : 0 ≤ C2 * L := by positivity
  by_contra hne
  have hX : 1 / (σ - β) + 1 / (σ - β') ≤ L / ε + K * L := by
    by_cases hcp : χ = ψ
    · subst hcp
      have hcc : χ * χ = 1 := by rw [← sq]; exact hχ2
      have hsum := GlobalTheory.TwoRealCharacters.neg_sum_logDeriv_nonneg q χ χ σ hχ2 hχ2 hσ1
      rw [hcc] at hsum
      by_cases hbb : β = β'
      · subst hbb
        have hd : deriv (LFunction χ) β = 0 := by
          by_contra hd; exact hne ⟨rfl, rfl, hd⟩
        have o2 : (2 : ℝ) ≤ analyticOrderNatAt (LFunction χ) β := by
          exact_mod_cast le_order hχ β 2 (by
            intro i hi; interval_cases i
            · simpa using hLβ
            · simpa using hd)
        have t2 : 2 / (σ - β) ≤ (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) :=
          div_le_div_of_nonneg_right o2 hpos.le
        have hB := h2 q χ hχ σ hσ1 hσ2 {β} (by simp [hβ23, hLβ])
        rw [Finset.sum_singleton, ← hLdef] at hB
        have e2 : 1 / (σ - β) + 1 / (σ - β) = 2 / (σ - β) := by ring
        rw [e2]
        linarith
      · have hB := h2 q χ hχ σ hσ1 hσ2 {β, β'} (by simp [hβ23, hLβ, hβ23', hLβ'])
        rw [Finset.sum_pair hbb, ← hLdef] at hB
        linarith
    · have hcψ : χ * ψ ≠ 1 := by
        intro h; apply hcp
        have h' : χ * χ = 1 := by rw [← sq]; exact hχ2
        rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right h']
      have hsum := GlobalTheory.TwoRealCharacters.neg_sum_logDeriv_nonneg q χ ψ σ hχ2 hψ2 hσ1
      have hBχ := h2 q χ hχ σ hσ1 hσ2 {β} (by simp [hβ23, hLβ])
      have hBψ := h2 q ψ hψ σ hσ1 hσ2 {β'} (by simp [hβ23', hLβ'])
      have hBχψ := h2 q (χ * ψ) hcψ σ hσ1 hσ2 ∅ (by simp)
      rw [Finset.sum_singleton, ← hLdef] at hBχ hBψ
      rw [Finset.sum_empty, ← hLdef] at hBχψ
      linarith
  have hy : 1 / (σ - β) * ((σ - β) * L) = L := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hpos), one_mul]
  have hy' : 1 / (σ - β') * ((σ - β') * L) = L := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hpos'), one_mul]
  have hsL : (σ - β) * L ≤ ε + ε / 8 := by
    have : (σ - β) * L = (1 - β) * L + ε / L * L := by rw [hσdef]; ring
    linarith
  have hsL' : (σ - β') * L ≤ ε + ε / 8 := by
    have : (σ - β') * L = (1 - β') * L + ε / L * L := by rw [hσdef]; ring
    linarith
  have y0 : 0 ≤ 1 / (σ - β) := by positivity
  have y0' : 0 ≤ 1 / (σ - β') := by positivity
  have k1 := mul_le_mul_of_nonneg_left hsL y0
  have k1' := mul_le_mul_of_nonneg_left hsL' y0'
  have k2 := mul_le_mul_of_nonneg_left hX hε.le
  have k3 := mul_le_mul_of_nonneg_left hKε hLpos.le
  nlinarith

end GlobalTheory.RealZeroNearOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular

theorem modularCharacter_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (hG : IsUnimodular G) (g : G) :
    Measure.modularCharacter g = 1 := by
  haveI := hG Measure.haar inferInstance
  change Measure.modularCharacterFun g = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G) g]
  have key : ∀ (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant],
      μ' = Measure.haar → Measure.haarScalarFactor μ' (Measure.haar : Measure G) = 1 := by
    intro μ' _ _ h
    subst h
    exact Measure.haarScalarFactor_self _
  exact key _ (map_mul_right_eq_self _ g)

theorem invariantMeasureClause : InvariantMeasureClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH uG uH
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH fun h => ?_
  rw [modularCharacter_eq_one uG, modularCharacter_eq_one uH]

end GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodularStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular : InvariantMeasureClause := by
  first | exact @GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause | exact GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause | (intros; apply GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrt
open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem exists_local_sqrt_near_one (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : ∃ (N : Set K) (g : K → K), IsOpen N ∧ (1 : K) ∈ N ∧ ContinuousOn g N ∧
      ∀ u ∈ N, g u ^ 2 = u := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  refine ⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, fun u hu => ?_⟩
  · simpa using hf.image_mem_toOpenPartialHomeomorph_target
  · have := e.right_inv hu
    rwa [he] at this

theorem exists_isSqrtOn (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by
  classical
  obtain ⟨N, g, hN, h1, hg, hsq⟩ := exists_local_sqrt_near_one K h2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hN 1 h1
  set r : ℝ := min (ε / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.closedBall (1 : K) r ⊆ N :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hclopen : IsClopen (Metric.closedBall (1 : K) r) := ⟨Metric.isClosed_closedBall, hopen⟩
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  refine ⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen,
    isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩
  · intro a ha b hb
    have hna := hnorm a ha
    rw [mem_closedBall_iff_norm] at ha hb ⊢
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rwa [norm_mul, hna, one_mul]
  · intro a ha
    have hna := hnorm a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hna
    rw [mem_closedBall_iff_norm] at ha ⊢
    have : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by field_simp; ring
    rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]
  · refine continuous_piecewise ?_ ?_ continuousOn_const
    · simp [hclopen.frontier_eq]
    · rw [Metric.isClosed_closedBall.closure_eq]
      exact hg.mono hsub
  · intro a ha
    rw [Set.piecewise_eq_of_mem _ _ _ ha]
    exact hsq a (hsub ha)

end GlobalTheory.QuadFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K], (2 : K) ≠ 0 → ∃ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s := by
  first | exact @GlobalTheory.QuadFibre.exists_isSqrtOn | exact GlobalTheory.QuadFibre.exists_isSqrtOn | (intros; apply GlobalTheory.QuadFibre.exists_isSqrtOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteBox
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroBand

theorem finite_box (f : ℂ → ℂ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0}.Finite := by
  refine Set.Finite.subset
    ((Finset.Icc ⌊-T⌋ ⌊T⌋).finite_toSet.biUnion fun k _ => hW (k : ℝ)) ?_
  rintro ρ ⟨h0, h1, h2, h3⟩
  rw [abs_lt] at h2
  refine Set.mem_iUnion₂.2 ⟨⌊ρ.im⌋, ?_, h0, h1, ?_, h3⟩
  · rw [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.floor_mono h2.1.le, Int.floor_mono h2.2.le⟩
  · rw [abs_le]
    constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]

theorem norm_term_le (m : ℕ) {u T : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) {ρ : ℂ} (h1 : ρ.re < 1)
    (h2 : T ≤ |ρ.im|) : ‖(m : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (m : ℝ) * (u / T) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hρ : T ≤ ‖ρ‖ := h2.trans (Complex.abs_im_le_norm ρ)
  have hρ0 : 0 < ‖ρ‖ := hT0.trans_le hρ
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  have hup : u ^ ρ.re ≤ u := by
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1.le
      _ = u := Real.rpow_one u
  calc u ^ ρ.re / ‖ρ‖ ≤ u / ‖ρ‖ := div_le_div_of_nonneg_right hup hρ0.le
    _ ≤ u / T := div_le_div_of_nonneg_left hu0.le hT0 hρ

theorem band_le (f : ℂ → ℂ) (m : ℂ → ℕ) (B : ℝ → ℝ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}, (m ρ : ℝ) ≤ B t)
    {u T T' : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (B T + B (-T)) * (u / T) := by
  classical
  have hT0 : 0 < T := by linarith
  have hS' := finite_box f (fun t => (hW t).1) T'
  have hS := finite_box f (fun t => (hW t).1) T
  have hA := (hW T).1
  have hA' := (hW (-T)).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS', finsum_mem_eq_finite_toFinset_sum _ hS]
  have hsub : hS.toFinset ⊆ hS'.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨a, b, c, d⟩ := hρ
    exact ⟨a, b, c.trans_le hT1, d⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hD : ∀ ρ ∈ hS'.toFinset \ hS.toFinset,
      ρ ∈ hA.toFinset ∪ hA'.toFinset ∧ ρ.re < 1 ∧ T ≤ |ρ.im| := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hρ
    rw [Set.Finite.mem_toFinset] at h1 h2
    obtain ⟨a, b, c, d⟩ := h1
    have hT' : T ≤ |ρ.im| := not_lt.1 fun h => h2 ⟨a, b, h, d⟩
    refine ⟨?_, b, hT'⟩
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rw [abs_lt] at c
    rcases le_or_gt 0 ρ.im with h | h
    · left
      rw [abs_of_nonneg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
    · right
      rw [abs_of_neg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
  have hm : ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) ≤ B T + B (-T) := by
    calc ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)
        ≤ ∑ ρ ∈ hA.toFinset ∪ hA'.toFinset, (m ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (hD ρ hρ).1)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hA.toFinset, (m ρ : ℝ) + ∑ ρ ∈ hA'.toFinset, (m ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      _ ≤ B T + B (-T) := by
          rw [← finsum_mem_eq_finite_toFinset_sum _ hA, ← finsum_mem_eq_finite_toFinset_sum _ hA']
          exact add_le_add (hW T).2 (hW (-T)).2
  calc _ ≤ ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) * (u / T) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
        obtain ⟨-, h1, h2⟩ := hD ρ hρ
        exact norm_term_le (m ρ) hT hu h1 h2
    _ = (∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]
    _ ≤ (B T + B (-T)) * (u / T) :=
        mul_le_mul_of_nonneg_right hm (div_nonneg (by linarith) hT0.le)

theorem zeros_band : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)) - ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T) := by
  obtain ⟨C, hC, hcount⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨2 * C, by linarith, ?_⟩
  intro N _ χ hχ u T T' hT hu hT1 hT2
  have hw := hcount N χ hχ
  refine ⟨finite_box _ (fun t => (hw t).1) T, ?_⟩
  refine (band_le (LFunction χ) (fun ρ => analyticOrderNatAt (LFunction χ) ρ)
    (fun t => C * Real.log (N * (|t| + 2))) hw hT hu hT1 hT2).trans ?_
  have hT0 : 0 < T := by linarith
  rw [abs_neg, abs_of_pos hT0]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have huT : T + 2 ≤ u * T := by nlinarith
  have hx : (N : ℝ) * (T + 2) ≤ N * u * T := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left huT (by linarith)
  have hpos : 0 < (N : ℝ) * (T + 2) := by positivity
  have hL1 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) := Real.log_le_log hpos hx
  have h4 : (4 : ℝ) ≤ N * u * T := by nlinarith
  have hL : 1 ≤ Real.log (N * u * T) := by
    have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
    exact ((Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)).le
  have hL2 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) ^ 2 := hL1.trans (by nlinarith)
  have hq : 0 ≤ u / T := div_nonneg (by linarith) hT0.le
  calc (C * Real.log (N * (T + 2)) + C * Real.log (N * (T + 2))) * (u / T)
      = 2 * C * Real.log (N * (T + 2)) * (u / T) := by ring
    _ ≤ 2 * C * Real.log (N * u * T) ^ 2 * (u / T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 (by linarith)) hq
    _ = 2 * C * (u * Real.log (N * u * T) ^ 2 / T) := by ring

end GlobalTheory.ZeroBand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AveragedFibreMeasureComplFibreEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AveragedFibreMeasureComplFibreEqZero
open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem fibOf_compl_fibre : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  intro K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ q hq hh U s hs t
  obtain ⟨hUo, hUc, h1, hmul, hinv, hn, hsc, hsq⟩ := hs
  by_cases ht : t = 0
  · subst ht; rw [fibOf_zero]; rfl
  have hm : Measurable (fun x : V => s (t / q x) • x) := by
    have h1 : Measurable (fun x : V => s (t / q x)) :=
      hsc.measurable.comp (measurable_const.div hq.measurable)
    exact h1.smul measurable_id
  have hA : MeasurableSet (q ⁻¹' {t})ᶜ :=
    ((isClosed_singleton.preimage hq).measurableSet).compl
  rw [fibOf_ne _ _ _ _ _ ht, Measure.smul_apply, Measure.map_apply hm hA,
    Measure.restrict_apply (hm hA)]
  convert smul_zero _
  convert measure_empty (μ := μ)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, u, hu, hx2⟩
  apply hx1
  have hu0 : u ≠ 0 := by
    intro h
    have := hn u hu
    rw [h] at this
    simp at this
  have hx2' : q x = t * u := by simpa using hx2.symm
  have h3 : t / q x = u⁻¹ := by rw [hx2']; field_simp
  show q (s (t / q x) • x) = t
  rw [hh, h3, hsq _ (hinv u hu), hx2']
  field_simp

end GlobalTheory.QuadFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AveragedFibreMeasureComplFibreEqZeroStatement
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averagedFibreMeasure_compl_fibre_eq_zero : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  first | exact @GlobalTheory.QuadFibre.fibOf_compl_fibre | exact GlobalTheory.QuadFibre.fibOf_compl_fibre | (intros; apply GlobalTheory.QuadFibre.fibOf_compl_fibre <;> assumption)
end
end
