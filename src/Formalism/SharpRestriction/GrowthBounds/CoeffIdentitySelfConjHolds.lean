module

public import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfTwo

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoeffGaugeSquareLowDegree
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MvPowerSeries

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def Kd (r : ℕ) (f : MvPowerSeries (Fin 2) C) : Prop := ∀ i j, j < r → coeff (ee i j) f = 0

theorem Kd.mul {a b : ℕ} {f g : MvPowerSeries (Fin 2) C} (hf : Kd a f) (hg : Kd b g) : Kd (a + b) (f * g) :=
  fun i j h => kmul hf hg i j h

theorem Kd.zero' (f : MvPowerSeries (Fin 2) C) : Kd 0 f := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem Kd.pow {m : ℕ} {f : MvPowerSeries (Fin 2) C} (hf : Kd m f) (k : ℕ) : Kd (m * k) (f ^ k) := by
  induction k with
  | zero => exact Kd.zero' _
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hf

def zdeg (e : Fin 2 × κ →₀ ℕ) : ℕ := ∑ i, e (1, i)

theorem zdeg_add (e e' : Fin 2 × κ →₀ ℕ) : zdeg (e + e') = zdeg e + zdeg e' := by
  unfold zdeg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem zdeg_single1 (i : κ) (k : ℕ) : zdeg (Finsupp.single ((1 : Fin 2), i) k) = k := by
  unfold zdeg
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (Prod.mk.inj h).2.symm
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem Kd_prod {a : Fin 2 × κ → MvPowerSeries (Fin 2) C} {m : ℕ} (ha : ∀ i, Kd m (a (1, i)))
    (e : Fin 2 × κ →₀ ℕ) : Kd (m * zdeg e) (e.prod fun s k => a s ^ k) := by
  induction e using Finsupp.induction_linear with
  | zero =>
    have : zdeg (0 : Fin 2 × κ →₀ ℕ) = 0 := by simp [zdeg]
    rw [this, mul_zero]
    exact Kd.zero' _
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), zdeg_add, mul_add]
    exact hf.mul hg
  | single s k =>
    rw [Finsupp.prod_single_index (h := fun s k => a s ^ k) (pow_zero _)]
    obtain ⟨g, i⟩ := s
    by_cases hg : g = 1
    · subst hg
      rw [zdeg_single1]
      exact (ha i).pow k
    · have : zdeg (Finsupp.single (g, i) k) = 0 := by
        unfold zdeg
        apply Finset.sum_eq_zero
        intro b _
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hg (Prod.mk.inj h).1
      rw [this, mul_zero]
      exact Kd.zero' _

theorem Kd_subst {a : Fin 2 × κ → MvPowerSeries (Fin 2) C} (ha0 : ∀ s, constantCoeff (a s) = 0) {m : ℕ}
    (ha : ∀ i, Kd m (a (1, i))) {f : MvPowerSeries (Fin 2 × κ) C} {r : ℕ} (hf : ∀ e, zdeg e < r → coeff e f = 0) :
    Kd (m * r) (subst a f) := by
  intro i j hj
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : zdeg e < r
  · rw [hf e he, zero_smul]
  · rw [Kd_prod ha e i j (lt_of_lt_of_le hj (Nat.mul_le_mul_left m (not_lt.1 he))), smul_zero]

theorem ee_eq_single0 {a b k : ℕ} : ee a b = Finsupp.single 0 k ↔ a = k ∧ b = 0 := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    rw [ee_zero] at h0
    rw [ee_one] at h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [ee]

theorem ee_eq_single1 {a b k : ℕ} : ee a b = Finsupp.single 1 k ↔ a = 0 ∧ b = k := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    rw [ee_zero] at h0
    rw [ee_one] at h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [ee]

theorem coeff_embedFirstVar (a b : ℕ) (f : PowerSeries C) :
    coeff (ee a b) (inV 0 f) = if b = 0 then PowerSeries.coeff a f else 0 := by
  unfold inV
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 0))]
  simp only [coeff_X_pow, ee_eq_single0]
  by_cases hb : b = 0
  · rw [if_pos hb, finsum_eq_single _ a]
    · simp [hb]
    · intro k hk
      rw [if_neg (fun h => hk h.1.symm), smul_zero]
  · rw [if_neg hb]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [if_neg (fun h => hb h.2), smul_zero]

theorem coeff_embedSecondVar (a b : ℕ) (f : PowerSeries C) :
    coeff (ee a b) (inV 1 f) = if a = 0 then PowerSeries.coeff b f else 0 := by
  unfold inV
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 1))]
  simp only [coeff_X_pow, ee_eq_single1]
  by_cases ha : a = 0
  · rw [if_pos ha, finsum_eq_single _ b]
    · simp [ha]
    · intro k hk
      rw [if_neg (fun h => hk h.2.symm), smul_zero]
  · rw [if_neg ha]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [if_neg (fun h => ha h.1), smul_zero]

theorem coeff_inV_mul (n j : ℕ) (P Q : PowerSeries C) :
    coeff (ee n j) (inV 1 P * inV 0 Q) = PowerSeries.coeff j P * PowerSeries.coeff n Q := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (ee 0 j, ee n 0)]
  · rw [coeff_embedSecondVar, coeff_embedFirstVar, if_pos rfl, if_pos rfl]
  · rintro ⟨p, q⟩ hpq hne
    have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
    have e0 : p 0 + q 0 = n := by
      have := DFunLike.congr_fun e 0
      simpa [ee_zero] using this
    have e1 : p 1 + q 1 = j := by
      have := DFunLike.congr_fun e 1
      simpa [ee_one] using this
    show coeff p (inV 1 P) * coeff q (inV 0 Q) = 0
    rw [eq_ee p, eq_ee q, coeff_embedSecondVar, coeff_embedFirstVar]
    by_cases hp : p 0 = 0
    · by_cases hq : q 1 = 0
      · exfalso
        apply hne
        rw [eq_ee p, eq_ee q, hp, hq]
        have h1 : p 1 = j := by omega
        have h2 : q 0 = n := by omega
        rw [h1, h2]
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  · intro h
    exfalso
    apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext x
    fin_cases x <;> simp [ee]

def rho (F : MvPowerSeries κ C) : MvPowerSeries (Fin 2 × κ) C :=
  subst (fun x : κ => (X ((0 : Fin 2), x) : MvPowerSeries (Fin 2 × κ) C)) F

def h2 (X : RawChart C d I κ) : MvPowerSeries (Fin 2 × κ) C :=
  X.h + ∑ i, MvPowerSeries.X ((1 : Fin 2), i) * rho (X.sg (Pi.single i 1))

theorem iota_inj : Function.Injective (fun x : κ => ((0 : Fin 2), x)) := fun _ _ h => (Prod.mk.inj h).2

theorem coeff_X_mul_rho (i : κ) (F : MvPowerSeries κ C) (e : Fin 2 × κ →₀ ℕ) (h : e (1, i) = 0) :
    coeff e (MvPowerSeries.X ((1 : Fin 2), i) * rho F) = 0 := by
  rw [X_def, coeff_monomial_mul, if_neg]
  intro hle
  have := hle (1, i)
  rw [Finsupp.single_eq_same, h] at this
  omega

theorem coeff_gaugeSquare_low_degree (X : RawChart C d I κ)
    (hax : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → coeff e X.h = 0) (e : Fin 2 × κ →₀ ℕ)
    (he : zdeg e < 2) : coeff e (h2 X) = 0 := by
  unfold h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum]
  by_cases h0 : ∀ i, e (1, i) = 0
  · rw [Finset.sum_eq_zero fun i _ => coeff_X_mul_rho i _ e (h0 i), add_zero]
    apply hax
    rintro ⟨g, i⟩ hs hg
    simp only at hg
    subst hg
    exact (Finsupp.mem_support_iff.1 hs) (h0 i)
  · push Not at h0
    obtain ⟨i0, hi0⟩ := h0
    have hsum : e (1, i0) + ∑ i ∈ Finset.univ.erase i0, e (1, i) = zdeg e :=
      Finset.add_sum_erase Finset.univ (fun i => e (1, i)) (Finset.mem_univ i0)
    have h1 : e (1, i0) = 1 := by omega
    have hrest : ∑ i ∈ Finset.univ.erase i0, e (1, i) = 0 := by omega
    have hoth : ∀ i, i ≠ i0 → e (1, i) = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff.1 hrest) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rw [Finset.sum_eq_single i0 (fun i _ hi => coeff_X_mul_rho i _ e (hoth i hi))
      (fun h => absurd (Finset.mem_univ i0) h)]
    have hle : Finsupp.single ((1 : Fin 2), i0) 1 ≤ e := by
      intro s
      by_cases hs : s = (1, i0)
      · subst hs; rw [Finsupp.single_eq_same, h1]
      · rw [Finsupp.single_apply, if_neg (fun h => hs h.symm)]; exact Nat.zero_le _
    rw [X_def, coeff_monomial_mul, if_pos hle, one_mul]
    set e' := e - Finsupp.single ((1 : Fin 2), i0) 1 with he'
    have hee : e' + Finsupp.single ((1 : Fin 2), i0) 1 = e := tsub_add_cancel_of_le hle
    have hran : (↑e'.support : Set (Fin 2 × κ)) ⊆ Set.range (fun x : κ => ((0 : Fin 2), x)) := by
      rintro ⟨g, i⟩ hs
      have hs' : e' (g, i) ≠ 0 := Finsupp.mem_support_iff.1 hs
      rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
      · exact ⟨i, rfl⟩
      · exfalso
        apply hs'
        rw [he', Finsupp.tsub_apply]
        by_cases hi : i = i0
        · subst hi; rw [Finsupp.single_eq_same, h1]
        · rw [hoth i hi]; simp
    have hmap := Finsupp.mapDomain_comapDomain (fun x : κ => ((0 : Fin 2), x)) iota_inj e' hran
    unfold rho
    rw [← hmap, coeff_subst_rename_inj _ iota_inj]
    show coeff e X.h + -∑ j, (Pi.single i0 (1 : C) : κ → C) j * coeff _ X.h = 0
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i0) h), Pi.single_eq_same, one_mul, hmap, hee, add_neg_cancel]

end SelfConjCharts

open SelfConjCharts MvPowerSeries

theorem r1sHLin_holds : GaugeLeadingTermLinear := by
  intro C _ d I _ κ _ X hax x c hx m hm hc
  set a : Fin 2 × κ → MvPowerSeries (Fin 2) C := pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (c i)) with ha
  have hc0 : ∀ i, PowerSeries.constantCoeff (c i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc i 0 (by omega)
  have cc0 : ∀ (j : Fin 2) (f : PowerSeries C), PowerSeries.constantCoeff f = 0 → constantCoeff (inV j f) = 0 := by
    intro j f hf
    rw [← coeff_zero_eq_constantCoeff_apply, ← ee_00]
    fin_cases j
    · show coeff (ee 0 0) (inV 0 f) = 0
      rw [coeff_embedFirstVar, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · show coeff (ee 0 0) (inV 1 f) = 0
      rw [coeff_embedSecondVar, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  have ha0 : ∀ s, constantCoeff (a s) = 0 := by
    rintro ⟨g, i⟩
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact cc0 0 _ (hx i)
    · exact cc0 1 _ (hc0 i)
  have haK : ∀ i, Kd m (a (1, i)) := by
    intro i n j hj
    show coeff (ee n j) (inV 1 (c i)) = 0
    rw [coeff_embedSecondVar]
    split_ifs
    · exact hc i j hj
    · rfl
  have hS := hasSubst_of_constantCoeff_zero ha0
  have hdec : HH X x c = subst a (h2 X) - ∑ i, inV 1 (c i) * inV 0 (alongCv x (X.sg (Pi.single i 1))) := by
    have e1 : subst a (h2 X) = subst a X.h + ∑ i, a (1, i) * subst a (rho (X.sg (Pi.single i 1))) := by
      unfold h2
      rw [subst_add hS]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← substAlgHom_apply hS, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [substAlgHom_apply hS, subst_mul hS, subst_X hS]
    have e2 : ∀ F : MvPowerSeries κ C, subst a (rho F) = inV 0 (alongCv x F) := by
      intro F
      unfold SelfConjCharts.rho
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hS]
      simp only [subst_X hS]
      exact SelfConjGauge.subst_inV 0 hx F
    simp only [e2] at e1
    rw [e1]
    show subst a X.h = _
    have : ∀ i, a (1, i) = inV 1 (c i) := fun i => rfl
    simp only [this]
    ring
  have hK2 : Kd (m * 2) (subst a (h2 X)) := Kd_subst ha0 haK (coeff_gaugeSquare_low_degree X hax)
  constructor
  · intro n j hj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec, map_sub, hK2 n j (by omega), map_sum, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_inV_mul, hc i j hj, zero_mul]
  · intro n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec, map_sub, hK2 n m (by omega), map_sum, zero_sub]
    congr 1
    simp only [coeff_inV_mul]
    have hv : (fun i => PowerSeries.coeff m (c i)) =
        fun k => ∑ q, PowerSeries.coeff m (c q) * (Pi.single q (1 : C) : κ → C) k := by
      funext k
      rw [Finset.sum_eq_single k (fun q _ hq => by rw [Pi.single_eq_of_ne (Ne.symm hq), mul_zero])
        (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, sg_lin, alongCv_lin hx, map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul]

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.GenIntSPsubst
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

section GenPieces

variable {V : VF C}

theorem gen_mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem gen_mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

def GenLow (V : VF C) (N : ℕ) (A : MvPowerSeries (Fin 2) C) : Prop :=
  ∀ μ : Fin 2 →₀ ℕ, μ 0 ≤ N → V.MM (MvPowerSeries.coeff μ A)

theorem GenLow.mul {N : ℕ} {A R : MvPowerSeries (Fin 2) C} (hA : GenLow V N A) (hR : IntS V R) :
    GenLow V N (A * R) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => V.MM x) (fun _ _ => gen_mm_add) gen_mm_zero ?_
  rintro ⟨a, b⟩ hab
  have hab' : a + b = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have ha0 : a 0 ≤ N := by
    have : a 0 + b 0 = μ 0 := by rw [← hab', Finsupp.add_apply]
    omega
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' (hR b) (hA a ha0)

theorem gen_pw {N : ℕ} (hN : 0 < N) {f : PowerSeries C}
    (hf : PowerSeries.constantCoeff f = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m f)) :
    PowerSeries.constantCoeff (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f) = 0 ∧
      ∀ m, V.Ge 0 (PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f)) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, _root_.PowerSeries.coeff_subst_X_pow (by omega)]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf.1]
  · rw [_root_.PowerSeries.coeff_subst_X_pow (by omega)]
    split_ifs
    · simpa using hf.2 _
    · exact VF.Ge.zero 0

theorem gen_mm_pw {N : ℕ} (hN : 0 < N) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : V.MM (PowerSeries.coeff 1 f)) (m : ℕ) (hm : m ≤ N) :
    V.MM (PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f)) := by
  rw [_root_.PowerSeries.coeff_subst_X_pow (by omega)]
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have hk : k ≤ 1 := by
      by_contra h
      have : N * 2 ≤ N * k := Nat.mul_le_mul_left N (by omega)
      omega
    rw [Nat.mul_div_cancel_left k hN]
    interval_cases k
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, gen_mm_zero]
    · simpa using hf1
  · exact gen_mm_zero

theorem gen_low_inV {N : ℕ} (hN : 0 < N) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : V.MM (PowerSeries.coeff 1 f)) :
    GenLow V N (inV 0 (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f)) := by
  intro μ hμ
  unfold inV
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact gen_mm_pw hN hf0 hf1 _ hμ
  · exact gen_mm_zero

theorem gen_intS_X {τ : Type} (x : τ) : IntS V (MvPowerSeries.X x : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem gen_intS_psubst {τ : Type} {a : MvPowerSeries τ C} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : IntS V a)
    {f : PowerSeries C} (hf : ∀ m, V.Ge 0 (PowerSeries.coeff m f)) : IntS V (PowerSeries.subst a f) :=
  IntS.subst (σ := Unit) (fun _ => ha0) (fun _ => ha) (intS_ps.2 hf)

theorem gen_cc_psubst {τ : Type} {a : MvPowerSeries τ C} (ha0 : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
  VP.cc_subst (σ := Unit) (fun _ => ha0) hf

theorem gen_van_exp {τ : Type} {T : Set τ} {E : MvPowerSeries τ C} (hE : Van T E) : Van T (mvExp E - 1) := by
  intro ν hν
  have hk : ∀ k, k ≠ 0 → MvPowerSeries.coeff ν (E ^ k) = 0 := fun k hk => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ']
    exact (hE.mul_right _) ν hν
  have e : MvPowerSeries.coeff ν (mvExp E) =
      ∑ k ∈ Finset.range (ν.degree + 1), MvPowerSeries.coeff ν (E ^ k) / (k.factorial : C) := rfl
  rw [map_sub, e, Finset.sum_eq_single 0 (fun k _ h => by rw [hk k h, zero_div]) (by simp)]
  simp

end GenPieces

section GenChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def genS (κ : Type) : MvPowerSeries (κ ⊕ Unit) C := MvPowerSeries.X (Sum.inr ())

def genL (κ : Type) (f : PowerSeries C) : MvPowerSeries (κ ⊕ Unit) C := PowerSeries.subst (genS (C := C) κ) f

def genPhi (N : ℕ) (δ : κ → PowerSeries C) : κ ⊕ Unit → MvPowerSeries (Fin 2) C :=
  Sum.elim (fun i => inV 0 (pw N δ i)) fun _ => MvPowerSeries.X 1

theorem genS_cc : MvPowerSeries.constantCoeff (genS (C := C) κ) = 0 := by
  simp [genS]

theorem subst_genL {ρ : Type} {b : κ ⊕ Unit → MvPowerSeries ρ C} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : PowerSeries C) : MvPowerSeries.subst b (genL κ f) = PowerSeries.subst (b (Sum.inr ())) f := by
  show MvPowerSeries.subst b (MvPowerSeries.subst (fun _ : Unit => genS (C := C) κ) f) =
    MvPowerSeries.subst (fun _ : Unit => b (Sum.inr ())) f
  rw [VP.subst_subst (fun _ => genS_cc) hb]
  congr 1
  funext u
  exact VP.subst_X hb _

theorem genL_alongCv {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (f : MvPowerSeries κ C) : MvPowerSeries.subst (fun i => genL κ (γ i)) f = genL κ (alongCv γ f) := by
  show _ = MvPowerSeries.subst (fun _ : Unit => genS (C := C) κ) (MvPowerSeries.subst γ f)
  rw [VP.subst_subst hγ (fun _ => genS_cc)]
  rfl

theorem genL_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) :
    genL κ (∑ k ∈ s, f k) = ∑ k ∈ s, genL κ (f k) := by
  unfold genL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero genS_cc), map_sum]

theorem hAt_subst (X : RawChart C d I κ) {τ ρ : Type} [Finite τ] {c b : κ → MvPowerSeries τ C}
    (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    {Φ : τ → MvPowerSeries ρ C} (hΦ : ∀ s, MvPowerSeries.constantCoeff (Φ s) = 0) :
    MvPowerSeries.subst Φ (hAt X c b) =
      hAt X (fun i => MvPowerSeries.subst Φ (c i)) (fun i => MvPowerSeries.subst Φ (b i)) := by
  have hP : ∀ q, MvPowerSeries.constantCoeff (pairSubst c b q) = 0 := by
    intro q
    unfold pairSubst
    split_ifs
    · exact hc _
    · exact hb _
  unfold hAt
  rw [VP.subst_subst hP hΦ]
  congr 1
  funext q
  unfold pairSubst
  split_ifs <;> rfl

theorem gen_van_X (i : κ) :
    Van (Set.range (Sum.inl : κ → κ ⊕ Unit)) (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (κ ⊕ Unit) C) := by
  intro ν hν
  rw [MvPowerSeries.coeff_X, if_neg]
  rintro rfl
  exact hν (Sum.inl i) (by simp) ⟨i, rfl⟩

theorem gen_van_hAt (X : RawChart C d I κ)
    (h0 : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    {b : κ → MvPowerSeries (κ ⊕ Unit) C} (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    Van (Set.range (Sum.inl : κ → κ ⊕ Unit)) (hAt X (fun i => MvPowerSeries.X (Sum.inl i)) b) := by
  unfold hAt
  refine Van.subst {q : Fin 2 × κ | q.1 = 0} ?_ ?_ ?_
  · intro q
    unfold pairSubst
    split_ifs
    · simp
    · exact hb _
  · intro q hq
    unfold pairSubst
    rw [if_pos (show q.1 = 0 from hq)]
    exact gen_van_X _
  · intro e he
    exact h0 e fun s hs => he s hs

end GenChart

end SelfConjCharts

open SelfConjCharts in
theorem generic_point_unit_congruence : GenericPointUnitCongruence := by
  intro C _ _ V d I _ κ _ X hB hBi ζ hζ n hn z ε δ hz hε hδ hNR hδ1 N hN0 p q hp
  have hζint : V.Ge 0 ζ := V.ge_of_pow_eq_one V.l_prime.ne_zero hζ
  have hzk : ∀ (k : ℕ) (i : κ), PowerSeries.constantCoeff (PowerSeries.rescale (ζ ^ k) (z i)) = 0 ∧
      ∀ m, V.Ge 0 (PowerSeries.coeff m (PowerSeries.rescale (ζ ^ k) (z i))) := by
    intro k i
    refine ⟨?_, fun m => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hz i).1, mul_zero]
    · rw [PowerSeries.coeff_rescale]
      exact ((hζint.pow k).pow m).mul_int ((hz i).2 m)
  have hεn : ∀ i, PowerSeries.constantCoeff (pw n ε i) = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m (pw n ε i)) :=
    fun i => gen_pw hn (hε i)
  have hδN : ∀ i, PowerSeries.constantCoeff (pw N δ i) = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m (pw N δ i)) :=
    fun i => gen_pw hN0 (hδ i)
  have hpt : ∀ f : PowerSeries C, (PowerSeries.constantCoeff f = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m f)) →
      MvPowerSeries.constantCoeff (genL κ f) = 0 ∧ IntS V (genL κ f) := fun f hf =>
    ⟨gen_cc_psubst genS_cc hf.1, gen_intS_psubst genS_cc (gen_intS_X _) hf.2⟩

  have BI := (hBi (κ ⊕ Unit) V.l (fun k i => genL κ (PowerSeries.rescale (ζ ^ k) (z i)))
    (fun i => genL κ (pw n ε i)) (fun i => MvPowerSeries.X (Sum.inl i))
    (fun k i => hpt _ (hzk k i)) (fun i => hpt _ (hεn i)) (fun i => ⟨by simp, gen_intS_X _⟩) (by
      intro i
      have e1 : alongCv (pw n ε) (X.lg i) =
          PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv ε (X.lg i)) :=
        alongCv_repar (fun i => (hε i).1) (by simp [hn.ne']) _
      have e2 : ∀ k, PowerSeries.rescale (ζ ^ k) (alongCv z (X.lg i)) =
          alongCv (fun i => PowerSeries.rescale (ζ ^ k) (z i)) (X.lg i) := by
        intro k
        simp only [PowerSeries.rescale_eq_subst]
        exact (alongCv_repar (fun i => (hz i).1) (by simp) _).symm
      rw [genL_alongCv (fun i => (hεn i).1), e1, hNR i, genL_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [genL_alongCv (fun i => (hzk k i).1), e2 k])).2
  set E : MvPowerSeries (κ ⊕ Unit) C :=
    ∑ k ∈ Finset.range V.l, hAt X (fun i => MvPowerSeries.X (Sum.inl i))
        (fun i => genL κ (PowerSeries.rescale (ζ ^ k) (z i))) -
      hAt X (fun i => MvPowerSeries.X (Sum.inl i)) (fun i => genL κ (pw n ε i)) with hEdef
  have hEV : Van (Set.range (Sum.inl : κ → κ ⊕ Unit)) E := by
    intro ν hν
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hEdef, map_sub, map_sum,
      Finset.sum_eq_zero fun k _ => gen_van_hAt X hB.axis0 (fun i => (hpt _ (hzk k i)).1) ν hν,
      gen_van_hAt X hB.axis0 (fun i => (hpt _ (hεn i)).1) ν hν, sub_zero]
  have hΦ0 : ∀ s, MvPowerSeries.constantCoeff (genPhi N δ s) = 0 := by
    intro s
    cases s with
    | inl i => exact gen_cc_psubst (by simp) (hδN i).1
    | inr u => simp [genPhi]
  have hΦint : ∀ s, IntS V (genPhi N δ s) := by
    intro s
    cases s with
    | inl i => exact gen_intS_psubst (by simp) (gen_intS_X _) (hδN i).2
    | inr u => exact gen_intS_X _
  have hXc : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (κ ⊕ Unit) C) = 0 :=
    fun i => by simp
  have hsE : MvPowerSeries.subst (genPhi N δ) E =
      ∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hEdef, ← MvPowerSeries.substAlgHom_apply (VP.hs hΦ0), map_sub, map_sum]
    simp only [MvPowerSeries.substAlgHom_apply]
    rw [hAt_subst X hXc (fun i => (hpt _ (hεn i)).1) hΦ0]
    refine congrArg₂ _ (Finset.sum_congr rfl fun k _ => ?_) ?_
    · rw [hAt_subst X hXc (fun i => (hpt _ (hzk k i)).1) hΦ0]
      simp only [VP.subst_X hΦ0, subst_genL hΦ0]
      rfl
    · simp only [VP.subst_X hΦ0, subst_genL hΦ0]
      rfl
  have hG : mvExp (∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε)) - 1 =
      MvPowerSeries.subst (genPhi N δ) (mvExp E - 1) := by
    rw [← MvPowerSeries.substAlgHom_apply (VP.hs hΦ0), map_sub, map_one, MvPowerSeries.substAlgHom_apply,
      VP.subst_exp hΦ0 hEV.const, hsE]
  have hF : IntS V (mvExp E - 1) := fun μ => by
    rw [map_sub]
    exact (BI μ).sub (IntS.one μ)
  have hFV := gen_van_exp hEV
  rw [hG, MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hΦ0)]
  refine finsum_induction (fun x => V.MM x) gen_mm_zero (fun _ _ => gen_mm_add) fun e => ?_
  rw [smul_eq_mul]
  by_cases h : ∀ s ∈ e.support, s ∉ Set.range (Sum.inl : κ → κ ⊕ Unit)
  · rw [hFV e h, zero_mul]
    exact gen_mm_zero
  · push Not at h
    obtain ⟨s0, hs0, i0, rfl⟩ := h
    have hp' : GenLow V N (e.prod fun s m => genPhi N δ s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hs0]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs0)
      dsimp only
      rw [hm, Nat.succ_eq_add_one, pow_succ', mul_assoc]
      exact (gen_low_inV hN0 (hδ i0).1 (hδ1 i0)).mul ((IntS.pow (hΦint _) m).mul
        (Finset.prod_induction _ (IntS V) (fun _ _ h1 h2 => h1.mul h2) IntS.one fun s _ => (hΦint s).pow _))
    exact MaximalIdealCongruence.mm_mul_ge' (hF e) (hp' _ (by simpa [ee] using hp))

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem coeffIdentity_selfConj_holds : CoefficientIdentitySelfConjugate := coeffIdentity_selfConj_of_two r1sHLin_holds generic_point_unit_congruence

theorem independence_bound_self_conjugate : IndependenceBoundSelfConjugate := independence_bound_self_conj coeffIdentity_selfConj_holds

end Formalism.L2.FormalSeriesBounds
