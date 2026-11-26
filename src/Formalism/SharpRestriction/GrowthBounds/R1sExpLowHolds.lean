module

public import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.AlongCvSmul
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoeffIdentityPlainChartOfThree
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MaximalIdealCongruence

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem sg_lin (X : RawChart C d I κ) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    X.sg (fun i => ∑ q, m q * u q i) = ∑ q, m q • X.sg (u q) := by
  apply MvPowerSeries.ext
  intro μ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPowerSeries.coeff_smul]
  show -∑ i, (∑ q, m q * u q i) * _ = ∑ q, m q * -∑ i, u q i * _
  simp only [Finset.sum_mul, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem alongCv_lin {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {ι : Type} [Fintype ι]
    (m : ι → C) (f : ι → MvPowerSeries κ C) : alongCv γ (∑ q, m q • f q) = ∑ q, m q • alongCv γ (f q) := by
  have hS : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  unfold alongCv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← MvPowerSeries.substAlgHom_apply hS, map_sum, map_smul]

theorem phi_lin (X : RawChart C d I κ) (l : ℕ) (hl : 0 < l) (ζ : C) {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    phi X l ζ γ δ (fun i => ∑ q, m q * u q i) = ∑ q, m q • phi X l ζ γ δ (u q) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  unfold phi
  rw [sg_lin, alongCv_lin hγ, alongCv_lin hδ]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [← PowerSeries.coe_substAlgHom hS, map_sum, map_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
    ring

theorem ge_of_mm {V : VF C} {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.MM at h
  unfold VF.Ge
  exact_mod_cast le_of_lt h

theorem mm_pow_sub {V : VF C} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.MM (a - b)) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  rw [← geom_sum₂_mul]
  exact mm_mul_ge' (VF.Ge.sum fun i _ => by simpa using (ha.pow i).mul (hb.pow (n - 1 - i))) h

theorem coeffIdentity_plainChart_of_three [IsAlgClosed C] [CharZero C] (X : RawChart C d I κ) (V : VF C) (H : ∀ g, X.CartHyp V g)
    (hA : StepA X V H) (hB : StepB X V) (hC : LemC X V) : IndependenceBoundPlain.PlainCoefficientIdentity X H := by
  intro _ g a _
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have hl0 : 0 < V.l := V.l_prime.pos
  choose z ε m hz hε hrel hz1 hε1 hm using hB ζ hζ g
  refine ⟨fun q' q => m q q', fun w x hg hV => ?_⟩
  obtain ⟨γ, δ, hγ, hδ, hrel', hmm, hq⟩ := hA ζ hζ g a w x hg hV
  refine ⟨fun q' => (V.l : C) * x 2 (Sum.inr q'), fun q hne => ?_, fun q => ?_⟩
  · have h2 := hg.1.2.2 2 (Sum.inr q) (by
      show X.ty (1 - g) q ≠ a + ((2 : ℕ) : ZMod d)
      simpa using hne)
    show (V.l : C) * x 2 (Sum.inr q) = 0
    rw [h2, mul_zero]
  · have h1 := hC ζ hζ γ δ (z q) (ε q) hγ hδ (hz q) (hε q) hrel' (hrel q) hmm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [funext (hz1 q), funext (hε1 q), phi_lin X V.l hl0 ζ (fun i => (hγ i).1) (fun i => (hδ i).1), map_sum] at h1
    simp only [PowerSeries.coeff_smul, smul_eq_mul] at h1
    obtain ⟨hc0, hcA, _⟩ := hq q
    have hAint : V.Ge 0 (PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q))) := by
      have := (ge_of_mm hcA).add hc0
      simpa using this
    have h3 := mm_pow_sub hAint hc0 hcA V.l
    have h4 : V.MM (∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
        (V.l : C) * x 2 (Sum.inr q'))) := mm_sum _ _ fun q' _ => mm_mul_ge' (hm q q') (hq q').2.2
    have e : (RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' =
        -(PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l - (RawChart.cart (H g)).c0' x q ^ V.l) +
        ((PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l -
          ∑ q', m q q' * PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q'))) +
        ∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
          (V.l : C) * x 2 (Sum.inr q'))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have : ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' = ∑ q', m q q' * ((V.l : C) * x 2 (Sum.inr q')) :=
        Finset.sum_congr rfl fun q' _ => by ring
      rw [this]
      ring
    rw [e]
    exact mm_add (mm_neg h3) (mm_add h1 h4)

end SelfConjCharts

section Self

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

theorem FBChart.rawSelf_axis1 (Y : FBChart C V O dd) (p : SelfData Y d I0) (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ 1) : MvPowerSeries.coeff e (Y.rawSelf p).h = 0 := by
  show MvPowerSeries.coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 1 Y.h (gauge_axes Y 1)) e he

theorem FBChart.rawSelf_basic (Y : FBChart C V O dd) (p : SelfData Y d I0) : SelfConjCharts.Basic (Y.rawSelf p) V := by
  exact
    { lg0 := Y.self_chart_log_constantCoeff p
      exlg := Y.rawSelf_exlg p
      lin := Y.rawSelf_lin p
      axis0 := Y.rawSelf_axis0 p
      axis1 := Y.rawSelf_axis1 p
      uint := Y.rawSelf_u_integral p
      hmis := hStabSelf_holds C V O dd Y d I0 p }

end Self

theorem coeffIdentity_selfConj_of_four (hA : GoodCurveClosed) (hB : OtherGroupCurvesClosed) (hC : MixedCoefficientClosed) (hD : BiadditiveOnColumns) : CoefficientIdentitySelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p _ H
  have := Y.algClosed
  have hb := Y.rawSelf_basic p
  exact SelfConjCharts.coeffIdentity_plainChart_of_three (Y.rawSelf p) V H (hA C V d _ _ _ hb H) (hB C V d _ _ _ hb H)
    (hC C V d _ _ _ hb (hD C V O dd Y d I0 p))

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MaximalIdealCongruence MvPowerSeries

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem ee_zero (i j : ℕ) : ee i j 0 = i := by simp [ee]

theorem ee_one (i j : ℕ) : ee i j 1 = j := by simp [ee]

theorem eq_ee (μ : Fin 2 →₀ ℕ) : μ = ee (μ 0) (μ 1) := by
  ext x
  fin_cases x <;> simp [ee]

theorem ee_00 : ee 0 0 = 0 := by simp [ee]

theorem ee_ne {i j : ℕ} (h : j ≠ 0) : ee i j ≠ 0 := fun e => h (by
  have := DFunLike.congr_fun e 1
  simpa [ee_one] using this)

theorem smul_ee (l i j : ℕ) : l • ee i j = ee (l * i) (l * j) := by
  simp [ee, smul_add, Finsupp.smul_single]

theorem kmul {f g : MvPowerSeries (Fin 2) C} {a b : ℕ} (hf : ∀ i j, j < a → coeff (ee i j) f = 0)
    (hg : ∀ i j, j < b → coeff (ee i j) g = 0) (i j : ℕ) (h : j < a + b) : coeff (ee i j) (f * g) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have e1 : p 1 + q 1 = j := by
    have := DFunLike.congr_fun e 1
    simpa [ee_one] using this
  show coeff p f * coeff q g = 0
  by_cases hp : p 1 < a
  · have : coeff p f = 0 := by rw [eq_ee p]; exact hf _ _ hp
    rw [this, zero_mul]
  · have : coeff q g = 0 := by rw [eq_ee q]; exact hg _ _ (by omega)
    rw [this, mul_zero]

theorem jmul {V : VF C} {f g : MvPowerSeries (Fin 2) C} {N : ℕ} (hf : ∀ i j, i ≤ N → V.MM (coeff (ee i j) f))
    (hg : IntS V g) (i j : ℕ) (h : i ≤ N) : V.MM (coeff (ee i j) (f * g)) := by
  rw [MvPowerSeries.coeff_mul]
  refine mm_sum _ _ ?_
  rintro ⟨p, q⟩ hpq
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have e1 : p 0 + q 0 = i := by
    have := DFunLike.congr_fun e 0
    simpa [ee_zero] using this
  show V.MM (coeff p f * coeff q g)
  have : V.MM (coeff p f) := by rw [eq_ee p]; exact hf _ _ (by omega)
  exact mm_mul_ge this (hg q)

theorem mvExp_rs (j : Fin 2) (c : C) (F : MvPowerSeries (Fin 2) C) : mvExp (rs j c F) = rs j c (mvExp F) := by
  apply MvPowerSeries.ext
  intro m
  unfold rs
  rw [MvPowerSeries.coeff_rescale]
  show ∑ k ∈ Finset.range (m.degree + 1), coeff m ((MvPowerSeries.rescale _ F) ^ k) / (k.factorial : C) =
    _ * ∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, MvPowerSeries.coeff_rescale, mul_div_assoc]

theorem alongCv_rc {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (c : C)
    (f : MvPowerSeries κ C) : alongCv (rc c γ) f = PowerSeries.rescale c (alongCv γ f) := by
  unfold rc
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

theorem alongCv_pw {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {n : ℕ} (hn : 0 < n)
    (f : MvPowerSeries κ C) :
    alongCv (pw n γ) f = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv γ f) := by
  unfold pw
  exact alongCv_repar hγ (by simp [hn.ne']) f

theorem rc_cc {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (c : C) (i : κ) :
    PowerSeries.constantCoeff (rc c γ i) = 0 := by
  unfold rc
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i, mul_zero]

theorem pw_low {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {n : ℕ} (hn : 0 < n) (i : κ)
    (j : ℕ) (hj : j < n) : PowerSeries.coeff j (pw n γ i) = 0 := by
  unfold pw
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have := coeff_subst_X_pow hn (γ i) 0
    rw [mul_zero] at this
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i]
  · exact coeff_subst_X_pow_of_not_dvd hn _ j (Nat.not_dvd_of_pos_of_lt hj0 hj)

theorem pw_lead (γ : κ → PowerSeries C) {n : ℕ} (hn : 0 < n) (i : κ) :
    PowerSeries.coeff n (pw n γ i) = PowerSeries.coeff 1 (γ i) := by
  unfold pw
  have := coeff_subst_X_pow hn (γ i) 1
  rwa [mul_one] at this

theorem sg_smul (X : RawChart C d I κ) (c : C) (v : κ → C) : X.sg (fun i => c * v i) = c • X.sg v := by
  simpa using sg_lin X (fun _ : Unit => c) (fun _ => v)

theorem alongCv_smul {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (c : C)
    (f : MvPowerSeries κ C) : alongCv γ (c • f) = c • alongCv γ f := by
  simpa using alongCv_lin hγ (fun _ : Unit => c) (fun _ => f)

end SelfConjCharts

open SelfConjCharts MaximalIdealCongruence MvPowerSeries

theorem r1sRestC_of (hFr : PowerSeriesFrobeniusCongruence) (hRo : RootsOfUnityProductCongruence) (hEx : ExpLowOrderTruncation) (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry)
    (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : MixedCoefficientClosed := by
  intro C _ _ V d I _ κ _ X hb hBi ζ hζ γ δ z ε hγ hδ hz hε hrel hrel' hmm
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hll : 0 < V.l ^ 2 := by positivity
  have hζ1 := hζ.pow_eq_one
  have cγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have cδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0 := fun i => (hδ i).1
  have cz : ∀ i, PowerSeries.constantCoeff (z i) = 0 := fun i => (hz i).1
  have cε : ∀ i, PowerSeries.constantCoeff (ε i) = 0 := fun i => (hε i).1
  have low1 : ∀ c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (c i) = 0) →
      ∀ i j, j < 1 → PowerSeries.coeff j (c i) = 0 := by
    intro c hc i j hj
    obtain rfl : j = 0 := by omega
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hc i]
  have cX : ∀ i, PowerSeries.constantCoeff (pw (V.l ^ 2) δ i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact pw_low cδ hll i 0 hll
  have cZ : ∀ i, PowerSeries.constantCoeff (pw V.l ε i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact pw_low cε hl0 i 0 hl0
  have HL := hHL C d I κ X hb.axis1
  set aC : (κ → PowerSeries C) → MvPowerSeries (Fin 2) C := fun c =>
    ∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw (V.l ^ 2) δ) c with haC
  set bC : (κ → PowerSeries C) → MvPowerSeries (Fin 2) C := fun c =>
    ∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) z) - HH X c (pw V.l ε) with hbC

  have aK : ∀ (c : κ → PowerSeries C) (m : ℕ), 1 ≤ m → (∀ i j, j < m → PowerSeries.coeff j (c i) = 0) →
      (∀ n j, j < m → coeff (ee n j) (aC c) = 0) ∧
        ∀ n, coeff (ee n m) (aC c) = PowerSeries.coeff n (phi X V.l ζ γ δ fun i => PowerSeries.coeff m (c i)) := by
    intro c m hm hc
    constructor
    · intro n j hj
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [haC, map_sub, map_sum]
      rw [(HL _ c cX m hm hc).1 n j hj, Finset.sum_eq_zero fun k _ => (HL _ c (rc_cc cγ _) m hm hc).1 n j hj, sub_zero]
    · intro n
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [haC, map_sub, map_sum]
      rw [(HL _ c cX m hm hc).2 n, Finset.sum_congr rfl fun k _ => (HL _ c (rc_cc cγ (ζ ^ k)) m hm hc).2 n]
      unfold phi
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, alongCv_rc cγ, alongCv_pw cδ hll, Finset.sum_neg_distrib]
      ring

  have bK : ∀ x : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (x i) = 0) →
      (∀ n, coeff (ee n 0) (bC x) = 0) ∧ ∀ n, coeff (ee n 1) (bC x) = 0 := by
    intro x hx
    constructor
    · intro n
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hbC, map_sub, map_sum]
      rw [(HL x _ hx 1 le_rfl (low1 _ cZ)).1 n 0 one_pos,
        Finset.sum_eq_zero fun k _ => (HL x _ hx 1 le_rfl (low1 _ (rc_cc cz (ζ ^ k)))).1 n 0 one_pos, sub_zero]
    · intro n
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hbC, map_sub, map_sum]
      rw [(HL x _ hx V.l hl0 (pw_low cε hl0)).1 n 1 (by omega),
        Finset.sum_congr rfl fun k _ => (HL x _ hx 1 le_rfl (low1 _ (rc_cc cz (ζ ^ k)))).2 n, sub_zero]
      have e : ∀ k, (fun i => PowerSeries.coeff 1 (rc (ζ ^ k) z i)) = fun i => ζ ^ k * PowerSeries.coeff 1 (z i) := by
        intro k
        funext i
        unfold rc
        rw [PowerSeries.coeff_rescale, pow_one]
      simp only [e, sg_smul, alongCv_smul hx, PowerSeries.coeff_smul, smul_eq_mul]
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hζ.geom_sum_eq_zero (by omega), zero_mul, neg_zero]
  have ccOf : ∀ F : MvPowerSeries (Fin 2) C, coeff (ee 0 0) F = 0 → constantCoeff F = 0 := by
    intro F h
    rwa [ee_00, coeff_zero_eq_constantCoeff_apply] at h
  have cca : ∀ c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (c i) = 0) → constantCoeff (aC c) = 0 :=
    fun c hc => ccOf _ ((aK c 1 le_rfl (low1 c hc)).1 0 0 one_pos)
  have ccb : ∀ c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (c i) = 0) → constantCoeff (bC c) = 0 :=
    fun c hc => ccOf _ ((bK c hc).1 0)

  have hid : bC (pw (V.l ^ 2) δ) + ∑ k ∈ Finset.range V.l, aC (rc (ζ ^ k) z) =
      aC (pw V.l ε) + ∑ k ∈ Finset.range V.l, bC (rc (ζ ^ k) γ) := by
    simp only [haC, hbC, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    ring
  have hE : mvExp (bC (pw (V.l ^ 2) δ)) * ∏ k ∈ Finset.range V.l, mvExp (aC (rc (ζ ^ k) z)) =
      mvExp (aC (pw V.l ε)) * ∏ k ∈ Finset.range V.l, mvExp (bC (rc (ζ ^ k) γ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun k _ => cca _ (rc_cc cz _)),
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun k _ => ccb _ (rc_cc cγ _)),
      ← VP.exp_add (ccb _ cX) (by rw [map_sum]; exact Finset.sum_eq_zero fun k _ => cca _ (rc_cc cz _)),
      ← VP.exp_add (cca _ cZ) (by rw [map_sum]; exact Finset.sum_eq_zero fun k _ => ccb _ (rc_cc cγ _)), hid]
  have ars : ∀ c : C, aC (rc c z) = rs 1 c (aC z) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [haC, map_sub, map_sum]
    rw [(hHR C d I κ X _ z cX cz c).2, Finset.sum_congr rfl fun k _ => (hHR C d I κ X _ z (rc_cc cγ (ζ ^ k)) cz c).2]
  have brs : ∀ c : C, bC (rc c γ) = rs 0 c (bC γ) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hbC, map_sub, map_sum]
    rw [(hHR C d I κ X γ _ cγ cZ c).1, Finset.sum_congr rfl fun k _ => (hHR C d I κ X γ _ cγ (rc_cc cz (ζ ^ k)) c).1]
  set Aa := mvExp (aC z) with hAa
  set Bb := mvExp (bC γ) with hBb
  set A1 := mvExp (bC (pw (V.l ^ 2) δ)) with hA1
  set A2 := mvExp (aC (pw V.l ε)) with hA2
  set B1 := ∏ k ∈ Finset.range V.l, rs 1 (ζ ^ k) Aa with hB1
  set B2 := ∏ k ∈ Finset.range V.l, rs 0 (ζ ^ k) Bb with hB2
  have hE' : A1 * B1 = A2 * B2 := by
    have e1 : ∏ k ∈ Finset.range V.l, mvExp (aC (rc (ζ ^ k) z)) = B1 :=
      Finset.prod_congr rfl fun k _ => by rw [ars, mvExp_rs]
    have e2 : ∏ k ∈ Finset.range V.l, mvExp (bC (rc (ζ ^ k) γ)) = B2 :=
      Finset.prod_congr rfl fun k _ => by rw [brs, mvExp_rs]
    rw [← e1, ← e2]
    exact hE
  have iAa : IntS V Aa := (hHI C V d I κ X hb hBi ζ hζ1 (V.l ^ 2) hll γ δ z hγ hδ hz hrel).1
  have iBb : IntS V Bb := (hHI C V d I κ X hb hBi ζ hζ1 V.l hl0 z ε γ hz hε hγ hrel').2
  have rB1 := hRo C V ζ hζ1 1 Aa iAa
  have rB2 := hRo C V ζ hζ1 0 Bb iBb
  have iB1 : IntS V B1 := by
    intro μ
    have := (ge_of_mm (rB1 μ)).add (IntS.pow iAa V.l μ)
    rwa [← map_add, sub_add_cancel] at this
  have hμ0 : V.l • ee V.l 1 = ee (V.l ^ 2) V.l := by rw [smul_ee, mul_one, sq]
  have one0 : ∀ i j : ℕ, j ≠ 0 → coeff (ee i j) (1 : MvPowerSeries (Fin 2) C) = 0 := by
    intro i j hj
    rw [MvPowerSeries.coeff_one, if_neg (ee_ne hj)]

  have cAa : coeff (ee V.l 1) Aa = PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) := by
    rw [hAa, hEx C (aC z) 1 le_rfl (aK z 1 le_rfl (low1 z cz)).1 V.l 1 (by omega), one0 _ _ one_ne_zero, zero_add,
      (aK z 1 le_rfl (low1 z cz)).2]
  have lowerFactorEntryConstant : V.MM (coeff (ee (V.l ^ 2) V.l) B1 -
      PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l) := by
    have h1 := rB1 (ee (V.l ^ 2) V.l)
    have h2 := hFr C V (Fin 2) Aa iAa (ee V.l 1)
    rw [hμ0, cAa] at h2
    have := mm_add h1 h2
    rwa [map_sub, sub_add_sub_cancel] at this

  have cBb : coeff (ee V.l 1) Bb = 0 := by
    rw [hBb, hEx C (bC γ) 1 le_rfl (fun i j hj => by
      obtain rfl : j = 0 := by omega
      exact (bK γ cγ).1 i) V.l 1 (by omega), one0 _ _ one_ne_zero, zero_add, (bK γ cγ).2]
  have cB2 : V.MM (coeff (ee (V.l ^ 2) V.l) B2) := by
    have h1 := rB2 (ee (V.l ^ 2) V.l)
    have h2 := hFr C V (Fin 2) Bb iBb (ee V.l 1)
    rw [hμ0, cBb, zero_pow hl0.ne', sub_zero] at h2
    have := mm_add h1 h2
    rwa [map_sub, sub_add_cancel] at this
  have kB2 : ∀ i j, j < 1 → coeff (ee i j) (B2 - 1) = 0 := by
    intro i j hj
    have e2 : B2 = mvExp (∑ k ∈ Finset.range V.l, bC (rc (ζ ^ k) γ)) := by
      rw [Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun k _ => ccb _ (rc_cc cγ _))]
      exact Finset.prod_congr rfl fun k _ => by rw [brs, mvExp_rs]
    have hK : ∀ i j, j < 1 → coeff (ee i j) (∑ k ∈ Finset.range V.l, bC (rc (ζ ^ k) γ)) = 0 := by
      intro i j hj
      obtain rfl : j = 0 := by omega
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => (bK _ (rc_cc cγ _)).1 i
    rw [map_sub, e2, hEx C _ 1 le_rfl hK i j (by omega), hK i j hj, add_zero, sub_self]

  have lowZ := pw_low cε hl0
  have cA2 : coeff (ee (V.l ^ 2) V.l) A2 =
      PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (ε i)) := by
    rw [hA2, hEx C _ V.l hl0 (aK _ V.l hl0 lowZ).1 (V.l ^ 2) V.l (by omega), one0 _ _ hl0.ne', zero_add,
      (aK _ V.l hl0 lowZ).2]
    congr 2
    funext i
    exact pw_lead ε hl0 i
  have kA2 : ∀ i j, j < V.l → coeff (ee i j) (A2 - 1) = 0 := by
    intro i j hj
    rw [map_sub, hA2, hEx C _ V.l hl0 (aK _ V.l hl0 lowZ).1 i j (by omega), (aK _ V.l hl0 lowZ).1 i j hj, add_zero,
      sub_self]

  have jA1 : ∀ i j, i ≤ V.l ^ 2 → V.MM (coeff (ee i j) (A1 - 1)) :=
    hGe C V d I κ X hb hBi ζ hζ1 V.l hl0 z ε δ hz hε hδ hrel' hmm (V.l ^ 2) hll
  have hL : coeff (ee (V.l ^ 2) V.l) (A1 * B1) =
      coeff (ee (V.l ^ 2) V.l) B1 + coeff (ee (V.l ^ 2) V.l) ((A1 - 1) * B1) := by
    rw [← map_add (f := _)]
    congr 1
    ring
  have hR : coeff (ee (V.l ^ 2) V.l) (A2 * B2) = coeff (ee (V.l ^ 2) V.l) A2 + coeff (ee (V.l ^ 2) V.l) B2 := by
    have e : A2 * B2 = A2 + B2 - 1 + (A2 - 1) * (B2 - 1) := by ring
    rw [e, map_add (f := _), map_sub, map_add (f := _), one0 _ _ hl0.ne', kmul kA2 kB2 _ _ (by omega), sub_zero, add_zero]
  have hJ := jmul jA1 iB1 (V.l ^ 2) V.l le_rfl
  rw [hE', hR, cA2] at hL
  have fin : PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l -
      PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (ε i)) =
      -(coeff (ee (V.l ^ 2) V.l) B1 -
        PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l) +
      (coeff (ee (V.l ^ 2) V.l) B2 - coeff (ee (V.l ^ 2) V.l) ((A1 - 1) * B1)) := by
    linear_combination (-1 : C) * hL
  rw [fin]
  exact mm_add (mm_neg lowerFactorEntryConstant) (mm_sub cB2 hJ)

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds SelfConjCharts MvPowerSeries

theorem r1sExpLow_holds : ExpLowOrderTruncation := by
  intro C _ _ F m hm hK i j hj
  have h2 : ∀ k, coeff (ee i j) (F ^ (k + 1 + 1)) = 0 := by
    intro k
    have e : F ^ (k + 1 + 1) = (F * F) * F ^ k := by ring
    rw [e]
    exact kmul (a := 2 * m) (b := 0) (fun i j h => kmul hK hK i j (by omega))
      (fun _ _ h => absurd h (Nat.not_lt_zero _)) i j (by omega)
  show ∑ k ∈ Finset.range ((ee i j).degree + 1), coeff (ee i j) (F ^ k) / (k.factorial : C) = _
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [add_comm]
  congr 1
  cases hd : (ee i j).degree with
  | zero =>
    rw [Finset.sum_range_zero]
    have h0 : ee i j = 0 := (Finsupp.degree_eq_zero_iff _).1 hd
    have hj0 : j = 0 := by
      have := DFunLike.congr_fun h0 1
      simpa [ee_one] using this
    exact (hK i j (by omega)).symm
  | succ n =>
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun k _ => by rw [h2 k, zero_div])]
    simp

end Formalism.L2.FormalSeriesBounds
