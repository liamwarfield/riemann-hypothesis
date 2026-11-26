module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
noncomputable section

open Classical Filter Topology MvPowerSeries.WithPiTopology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section Calc

variable (hE : CalcEquiv)
include hE

theorem sRefl {σ : Type} (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := (hE p σ f f f f).1

theorem sOfEq {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : f = g) : Simeq f g := h ▸ sRefl hE f

theorem sSymm {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f :=
  (hE p σ f g f f).2.1 h

theorem sTrans {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g k) : Simeq f k :=
  (hE p σ f g k f).2.2.1 h1 h2

theorem sAdd {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := (hE p σ f g h k).2.2.2.1 h1 h2

theorem sNeg {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) : Simeq (-f) (-g) :=
  (hE p σ f g f f).2.2.2.2.1 h1

theorem sSub {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f - h) (g - k) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact sAdd hE h1 (sNeg hE h2)

end Calc

theorem int_X {σ : Type*} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem coeff_subst_sum {τ : Type*} (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d f • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hd
  rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simp [ha]) (by omega),
    smul_zero]

theorem cont_subst {τ : Type*} (G : ℂ_[p] → MvPowerSeries τ ℂ_[p])
    (hG : Continuous G) (h0 : ∀ x, MvPowerSeries.constantCoeff (G x) = 0) (f : PowerSeries ℂ_[p]) :
    Continuous fun x => (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p]) := by
  refine continuous_pi fun e => ?_
  change Continuous fun x => MvPowerSeries.coeff e (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p])
  simp_rw [coeff_subst_sum _ (h0 _), smul_eq_mul]
  refine continuous_finsetSum _ fun d _ => continuous_const.mul ?_
  exact (continuous_coeff ℂ_[p] e).comp (hG.pow d)

theorem tendsto_coeff_of_cont {τ : Type*} (F : ℂ_[p] → MvPowerSeries τ ℂ_[p]) (hF : Continuous F)
    {u : ℕ → ℂ_[p]} {c : ℂ_[p]} (hu : Tendsto u atTop (𝓝 c)) (e : τ →₀ ℕ) :
    Tendsto (fun k => MvPowerSeries.coeff e (F (u k))) atTop (𝓝 (MvPowerSeries.coeff e (F c))) :=
  (((continuous_coeff ℂ_[p] e).comp hF).tendsto c).comp hu

section Lin

variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hex0 hinv

theorem cont_mulBy {τ : Type*} (y : MvPowerSeries τ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => mulBy l ex c y :=
  cont_subst (fun c => MvPowerSeries.C c * PowerSeries.subst y l) (continuous_C.mul continuous_const)
    (fun c => by rw [map_mul, constantCoeff_subst_log hex0 hinv y hy, mul_zero]) ex

theorem cont_be {τ : Type*} (ph : PowerSeries ℂ_[p]) (z y : MvPowerSeries τ ℂ_[p])
    (hz : MvPowerSeries.constantCoeff z = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => be l ex ph z (mulBy l ex c y) := by
  have hA : Continuous fun c : ℂ_[p] => add l ex z (mulBy l ex c y) := by
    have : (fun c : ℂ_[p] => add l ex z (mulBy l ex c y)) = fun c =>
        PowerSeries.subst (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) ex := by
      funext c; unfold add; rw [L_mulBy hex0 hinv c y hy]
    rw [this]
    exact cont_subst (fun c : ℂ_[p] => PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l)
      (continuous_const.add (continuous_C.mul continuous_const))
      (fun c => by
        show MvPowerSeries.constantCoeff (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) = 0
        rw [map_add (f := _), map_mul, constantCoeff_subst_log hex0 hinv y hy, constantCoeff_subst_log hex0 hinv z hz]; simp) ex
  unfold be
  refine ((cont_subst _ hA (fun c => constantCoeff_formalAdd hex0 hinv _ _ hz (constantCoeff_formalSMul hex0 hinv c y hy)) ph).sub
    continuous_const).sub ?_
  exact cont_subst _ (cont_mulBy hex0 hinv y hy) (fun c => constantCoeff_formalSMul hex0 hinv c y hy) ph

end Lin

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
noncomputable section

open Classical Filter Topology MvPowerSeries.WithPiTopology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_var {σ : Type*} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X i

theorem const_phAt {τ : Type*} (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries τ ℂ_[p])
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (phAt ph a) = PowerSeries.constantCoeff ph := by

  unfold phAt
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [map_pow, ha, zero_pow hd, smul_zero]

section Lin2

variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hSub hex0 hinv in
theorem int_add (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x y : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hx : IntegralMv x) (hy : IntegralMv y) :
    IntegralMv (add l ex x y) := by

  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := by
    intro i
    fin_cases i <;> simp [hx0, hy0]
  have hsI : ∀ i, IntegralMv (![x, y] i) := by
    intro i
    fin_cases i <;> simp [hx, hy]
  have h1 := (hSub p (Fin 2) τ ![x, y] hs0 hsI).2 _ hIA
  rw [sb_add ![x, y] hs0 hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1), sb_X, sb_X] at h1
  · exact h1
  all_goals exact hs0

include hSub hex0 hinv in
theorem int_mulBy_of (c : ℂ_[p]) (hc : IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    {τ : Type} (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) :
    IntegralMv (mulBy l ex c x) := by

  have hs0 : ∀ i : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => x) i) = 0 := fun _ => hx0
  have hsI : ∀ i : Unit, IntegralMv ((fun _ : Unit => x) i) := fun _ => hx
  have h1 := (hSub p Unit τ (fun _ : Unit => x) hs0 hsI).2 _ hc
  rw [sb_mulBy (fun _ : Unit => x) hs0 hex0 hinv _ _ (constantCoeff_var ()), sb_X] at h1
  · exact h1
  all_goals exact hs0

include hSub hex0 hinv in
theorem int_mulBy_nat (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (k : ℕ) :
    IntegralMv (mulBy l ex (k : ℂ_[p]) x) := by

  have hz : ∀ c, MvPowerSeries.constantCoeff (mulBy l ex c x) = 0 := by
    intro c
    unfold mulBy
    refine z0_pt_zero_pt_one_L3 hex0 _ ?_
    rw [map_mul, constantCoeff_subst_log hex0 hinv x hx0, mul_zero]
  induction k with
  | zero =>
    rw [Nat.cast_zero, mulBy_zero' hex0]
    intro n
    simp [IsIntP]
  | succ k ih =>
    rw [mulBy_succ hex0 hinv k x hx0]
    exact int_add hSub hex0 hinv hIA _ _ (hz _) hx0 ih hx

include hSub hex0 hinv in
theorem int_mulBy_zp (hC : CalcClosed) (hD : NatDense)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (n : ℤ_[p]) :
    IntegralMv (mulBy l ex (zc n) x) := by

  obtain ⟨u, hu⟩ := hD p n
  have hcont := cont_mulBy hex0 hinv x hx0
  have hconv : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (mulBy l ex ((u k : ℕ) : ℂ_[p]) x)) atTop
      (𝓝 (MvPowerSeries.coeff e (mulBy l ex (zc n) x))) :=
    fun e => tendsto_coeff_of_cont (fun c => mulBy l ex c x) hcont hu e
  exact (hC p τ _ _ hconv).2 (fun k => int_mulBy_nat hSub hex0 hinv hIA x hx0 hx (u k))

theorem ph_const_of {ph : PowerSeries ℂ_[p]}
    (h2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ()))) (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff ph = 0 := by

  have hm0 : MvPowerSeries.constantCoeff (mulBy l ex 2 (Xv () : MvPowerSeries Unit ℂ_[p])) = 0 := by
    unfold mulBy
    refine z0_pt_zero_pt_one_L3 hex0 _ ?_
    rw [map_mul, constantCoeff_subst_log hex0 hinv _ (constantCoeff_var ()), mul_zero]
  have hc1 : MvPowerSeries.constantCoeff (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.constantCoeff ph := const_phAt ph _ hm0
  have hc2 : MvPowerSeries.constantCoeff (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.constantCoeff ph := const_phAt ph _ (constantCoeff_var ())
  have hc3 : MvPowerSeries.constantCoeff (MvPowerSeries.C (2 * 2 : ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) = 2 * 2 :=
    MvPowerSeries.constantCoeff_C _
  have h1 := h2.1
  rw [map_sub, map_mul, hc1, hc2, hc3] at h1
  have h3 : (3 : ℂ_[p]) ≠ 0 := by norm_num
  have h4 : 3 * PowerSeries.constantCoeff ph = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h h3
  · exact h

include hex0 hinv in
theorem add_zero'' {τ : Type*} (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) :
    add l ex z 0 = z := by

  calc add l ex z 0 = add l ex (mulBy l ex 1 z) (mulBy l ex 0 z) := by
        rw [mulBy_one hex0 hinv z hz, mulBy_zero' hex0 z]
    _ = mulBy l ex (1 + 0) z := add_mulBy hex0 hinv 1 0 z hz
    _ = z := by rw [add_zero, mulBy_one hex0 hinv z hz]

include hex0 hinv in
theorem be_zero {τ : Type*} {ph : PowerSeries ℂ_[p]} (hph : PowerSeries.constantCoeff ph = 0)
    (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) : be l ex ph z 0 = 0 := by

  unfold be
  rw [add_zero'' hex0 hinv z hz]
  unfold phAt
  rw [PowerSeries.subst_zero_of_constantCoeff_zero hph]
  ring

variable {ph : PowerSeries ℂ_[p]}
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hSub hex0 hinv hB in
theorem be_add_left {τ : Type} (x y z : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hx : IntegralMv x) (hy : IntegralMv y) (hz : IntegralMv z) :
    Simeq (be l ex ph (add l ex x y) z) (be l ex ph x z + be l ex ph y z) := by

  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y, z] i) = 0 := by
    intro i
    fin_cases i <;> simp [hx0, hy0, hz0]
  have hsI : ∀ i, IntegralMv (![x, y, z] i) := by
    intro i
    fin_cases i <;> simp [hx, hy, hz]
  have hA01 : MvPowerSeries.constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    constantCoeff_formalAdd hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1)
  have h1 := (hSub p (Fin 3) τ ![x, y, z] hs0 hsI).1 _ _ hB
  rw [sb_be ![x, y, z] hs0 hex0 hinv ph _ _ hA01 (constantCoeff_var 2), sb_add ![x, y, z] hs0 hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1),
    sb_add', sb_be ![x, y, z] hs0 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_var 2),
    sb_be ![x, y, z] hs0 hex0 hinv ph _ _ (constantCoeff_var 1) (constantCoeff_var 2), sb_X, sb_X, sb_X] at h1
  · exact h1
  all_goals first | exact hs0 | exact hex0 | exact hinv

include hSub hex0 hinv hB in
theorem be_add_right {τ : Type} (x y z : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hx : IntegralMv x) (hy : IntegralMv y) (hz : IntegralMv z) :
    Simeq (be l ex ph z (add l ex x y)) (be l ex ph z x + be l ex ph z y) := by

  have hsym : ∀ a b : MvPowerSeries τ ℂ_[p], be l ex ph a b = be l ex ph b a := by
    intro a b
    unfold be
    rw [add_comm']
    ring
  rw [hsym z (add l ex x y), hsym z x, hsym z y]
  exact be_add_left hSub hex0 hinv hB x y z hx0 hy0 hz0 hx hy hz

include hE hSub hex0 hinv hB in
theorem be_nat (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (k : ℕ) :
    Simeq (be l ex ph z (mulBy l ex (k : ℂ_[p]) y)) (MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y) := by

  induction k with
  | zero =>
    rw [Nat.cast_zero, mulBy_zero' hex0, be_zero hex0 hinv hph z hz0, map_zero, zero_mul]
    exact (hE p τ 0 0 0 0).1
  | succ k ih =>
    rw [mulBy_succ hex0 hinv k y hy0]
    have hmk0 : MvPowerSeries.constantCoeff (mulBy l ex (k : ℂ_[p]) y) = 0 := by
      unfold mulBy
      refine z0_pt_zero_pt_one_L3 hex0 _ ?_
      rw [map_mul, constantCoeff_subst_log hex0 hinv y hy0, mul_zero]
    have hmkI : IntegralMv (mulBy l ex (k : ℂ_[p]) y) := int_mulBy_nat hSub hex0 hinv hIA y hy0 hy k
    have h1 := be_add_right hSub hex0 hinv hB (mulBy l ex (k : ℂ_[p]) y) y z hmk0 hy0 hz0 hmkI hy hz
    have h2 := (hE p τ _ _ _ _).2.2.2.1 ih
      (hE p τ (be l ex ph z y) (be l ex ph z y) (be l ex ph z y) (be l ex ph z y)).1
    have h3 := (hE p τ _ _ _ 0).2.2.1 h1 h2
    have h4 : MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y + be l ex ph z y =
        MvPowerSeries.C ((k + 1 : ℕ) : ℂ_[p]) * be l ex ph z y := by
      rw [Nat.cast_succ, map_add (f := _), map_one]
      ring
    rw [← h4]
    exact h3

include hE hSub hex0 hinv hB in
theorem be_zp (hC : CalcClosed) (hD : NatDense) (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (n : ℤ_[p]) :
    Simeq (be l ex ph z (mulBy l ex (zc n) y)) (MvPowerSeries.C (zc n) * be l ex ph z y) := by

  obtain ⟨u, hu⟩ := hD p n
  let F : ℂ_[p] → MvPowerSeries τ ℂ_[p] := fun c => be l ex ph z (mulBy l ex c y) - MvPowerSeries.C c * be l ex ph z y
  have hcont : Continuous F := by
    refine (cont_be hex0 hinv ph z y hz0 hy0).sub ?_
    refine continuous_pi (fun e => ?_)
    show Continuous (fun c : ℂ_[p] => MvPowerSeries.coeff e (MvPowerSeries.C c * be l ex ph z y))
    simp only [MvPowerSeries.coeff_C_mul]
    exact continuous_id.mul continuous_const
  have hconv : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F ((u k : ℕ) : ℂ_[p]))) atTop
      (𝓝 (MvPowerSeries.coeff e (F (zc n)))) :=
    fun e => tendsto_coeff_of_cont F hcont hu e
  have hk : ∀ k, Simeq (F ((u k : ℕ) : ℂ_[p])) 0 := fun k =>
    ((hE p τ _ _ 0 0).2.2.2.2.2).mp (be_nat hE hSub hex0 hinv hB hph hIA z y hz0 hy0 hz hy (u k))
  have h1 := (hC p τ (fun k => F ((u k : ℕ) : ℂ_[p])) (F (zc n)) hconv).1 hk
  exact ((hE p τ _ _ 0 0).2.2.2.2.2).mpr h1

end Lin2

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1
noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

theorem zc_mul (a b : ℤ_[p]) : zc (a * b) = zc a * zc b := by
  simp only [PI.PhNormUnits.zc, PadicInt.coe_mul, map_mul]

theorem zc_one : zc (1 : ℤ_[p]) = 1 := by
  simp only [PI.PhNormUnits.zc, PadicInt.coe_one, map_one]

theorem zc_two : zc (2 : ℤ_[p]) = 2 := by
  have h : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
    have := PadicInt.coe_natCast (p := p) 2
    simpa using this
  simp only [PI.PhNormUnits.zc, h, map_ofNat]

theorem norm_zc (a : ℤ_[p]) : ‖zc a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ = ‖a‖
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem norm_two_of (hp2 : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h2 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hp2)
  have h2' : ‖(2 : ℚ_[p])‖ = 1 := by exact_mod_cast h2
  have e : algebraMap ℚ_[p] ℂ_[p] 2 = 2 := map_ofNat _ 2
  rw [← e, norm_algebraMap', h2']

theorem zc_inv_of (n : ℤ_[p]) (h : ‖zc n‖ = 1) : ∃ m : ℤ_[p], zc n * zc m = 1 := by
  rw [norm_zc] at h
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr h
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  rw [← zc_mul, ← hu, Units.mul_inv, zc_one]

section

variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hSub hex0 hinv in

include hSub hex0 hinv in
theorem simeq_subst1 {τ : Type} (w : MvPowerSeries τ ℂ_[p]) (hw0 : MvPowerSeries.constantCoeff w = 0)
    (hw : IntegralMv w) {f g : MvPowerSeries Unit ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst (fun _ => w) f) (MvPowerSeries.subst (fun _ => w) g) :=
  (hSub p Unit τ (fun _ => w) (fun _ => hw0) (fun _ => hw)).1 f g h

include hSub hex0 hinv in
theorem simeq_subst2 {τ : Type} (x y : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hx : IntegralMv x) (hy : IntegralMv y)
    {f g : MvPowerSeries (Fin 2) ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst ![x, y] f) (MvPowerSeries.subst ![x, y] g) := by
  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i
    · simpa using hx0
    · simpa using hy0
  have hsI : ∀ i, PI.PhNormUnits.IntegralMv (![x, y] i) := by
    intro i; fin_cases i
    · simpa using hx
    · simpa using hy
  exact (hSub p (Fin 2) τ ![x, y] hs0 hsI).1 f g h

include hSub hex0 hinv in

include hSub hex0 hinv in
theorem norm_at {ph : PowerSeries ℂ_[p]} (c N : ℂ_[p])
    (h : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ())))
    {τ : Type} (w : MvPowerSeries τ ℂ_[p]) (hw0 : MvPowerSeries.constantCoeff w = 0) (hw : IntegralMv w) :
    Simeq (phAt ph (mulBy l ex c w)) (MvPowerSeries.C N * phAt ph w) := by
  have hs : ∀ i : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => w) i) = 0 := fun _ => hw0
  have hv : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hsm : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv c _ hv
  have eL : MvPowerSeries.subst (fun _ : Unit => w)
      (PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p]))) = PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c w) := by
    rw [sb_phAt (fun _ : Unit => w) hs ph _ hsm,
      sb_mulBy (fun _ : Unit => w) hs hex0 hinv c _ hv, sb_X (fun _ : Unit => w) hs ()]
  have eR : MvPowerSeries.subst (fun _ : Unit => w)
      (MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p])) = MvPowerSeries.C N * PI.PhNormUnits.phAt ph w := by
    rw [sb_C_mul (fun _ : Unit => w) hs N, sb_phAt (fun _ : Unit => w) hs ph _ hv,
      sb_X (fun _ : Unit => w) hs ()]
  have key := simeq_subst1 hSub hex0 hinv w hw0 hw h
  rw [eL, eR] at key
  exact key

end

section Units

variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hE hSub hex0 hinv hIA in
theorem units_i (c N : ℂ_[p])
    (hU : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ()))) :
    Simeq (be l ex ph (mulBy l ex c (Xv 0)) (mulBy l ex c (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C N * be l ex ph (Xv 0) (Xv 1)) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hA := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (constantCoeff_formalAdd hex0 hinv _ _ h0 h1) hIA
  have hX := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) h0 (int_X 0)
  have hY := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) h1 (int_X 1)
  have hsum := sSub hE (sSub hE hA hX) hY
  have eL : PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)) =
      PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1))) - PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0))
        - PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)) := by
    rw [mulBy_add hex0 hinv c _ _ h0 h1]
    rfl
  have eR : MvPowerSeries.C N * PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.Xv 1) =
      MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1)) - MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv 0)
        - MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv 1) := by
    simp only [PI.PhNormUnits.be]
    ring
  rw [eL, eR]
  exact hsum

include hE hSub hC hD hex0 hinv hph hIA hB in
theorem units_ii (c d : ℂ_[p]) (n : ℤ_[p]) (hn : c * d = zc n) :
    Simeq (MvPowerSeries.C (c * d) * be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (mulBy l ex c (Xv 1)))) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hcomp : PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      PI.PhNormUnits.mulBy l ex (PI.PhNormUnits.zc n) (PI.PhNormUnits.Xv 1) := by
    rw [mulBy_mulBy hex0 hinv d c _ h1, mul_comm d c, hn]
  have key := be_zp hE hSub hex0 hinv hB hC hD hph hIA
    (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.Xv 1) h0 h1 (int_X 0) (int_X 1) n
  rw [hcomp, hn]
  exact sSymm hE key

include hE hSub hex0 hinv in
theorem units_iv (c d : ℂ_[p]) (hc : c ≠ 0)
    (hw : IntegralMv (mulBy l ex c⁻¹ (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (h : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (mulBy l ex c (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (mulBy l ex c (Xv 1))))) :
    Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hy0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h1
  have hcs0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h0
  have hcs1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h1
  have hdc1 : MvPowerSeries.constantCoeff
      (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]))) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ hcs1
  have hs : ∀ i, MvPowerSeries.constantCoeff (![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] i) = 0 := by
    intro i; fin_cases i
    · simp
    · simpa using hy0
  have hs0 : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = PI.PhNormUnits.Xv 0 := by
    rw [sb_X _ hs 0]; simp
  have hs1 : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1) := by
    rw [sb_X _ hs 1]; simp
  have hcc : PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = PI.PhNormUnits.Xv 1 := by
    rw [mulBy_mulBy hex0 hinv c c⁻¹ _ h1, mul_inv_cancel₀ hc, mulBy_one hex0 hinv _ h1]
  have eL : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)]
      (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1))) =
      PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) := by
    rw [sb_be _ hs hex0 hinv ph _ _ hcs0 hcs1, sb_mulBy _ hs hex0 hinv c _ h0,
      sb_mulBy _ hs hex0 hinv c _ h1, hs0, hs1, hcc]
  have eR : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)]
      (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)))) =
      PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.Xv 1)) := by
    rw [sb_be _ hs hex0 hinv ph _ _ h0 hdc1, sb_mulBy _ hs hex0 hinv d _ hcs1,
      sb_mulBy _ hs hex0 hinv c _ h1, hs0, hs1, hcc]
  have key := simeq_subst2 hSub hex0 hinv (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)) h0 hy0 (int_X 0) hw h
  rw [eL, eR] at key
  exact key

end Units

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.StepUnitsOf
noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepUnits_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) : StepUnits := by
  intro p _ l ex ph S hS α hα h1 h2
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hint_r, hIA, -, hprod, -, hB, hNorm⟩ := hS
  have hph : PowerSeries.constantCoeff ph = 0 := by
    have h2n : ‖(2 : ℂ_[p])‖ = 1 := norm_two_of hp2
    have h2' := hNorm ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 h2n h2n
    dsimp only at h2'
    exact ph_const_of h2' hex0 hinv
  obtain ⟨n, hn⟩ := hprod α hα
  have hU := hNorm α hα h1 h2
  have hc : α.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hnorm : ‖PI.PhNormUnits.zc n‖ = 1 := by rw [← hn, norm_mul, h1, h2, one_mul]
  obtain ⟨m, hm⟩ := zc_inv_of n hnorm
  have hinvc : α.1⁻¹ = α.2 * PI.PhNormUnits.zc m := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hn, hm]
  have h1v : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have hd : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.2 (PI.PhNormUnits.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    have h := hint_r _ (hswap α hα)
    rw [Prod.fst_swap] at h
    exact h
  have hw : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.1⁻¹ (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hinvc, ← mulBy_mulBy hex0 hinv α.2 (PI.PhNormUnits.zc m) (PI.PhNormUnits.Xv (1 : Fin 2)) h1v]
    exact int_mulBy_of hSub hex0 hinv α.2 hd _
      (constantCoeff_formalSMul hex0 hinv _ _ h1v)
      (int_mulBy_zp hSub hex0 hinv hC hD hIA _ h1v
        (int_X _) m)
  have step1 := units_i hE hSub hex0 hinv hIA α.1 (α.1 * α.2) hU
  have step2 := units_ii hE hSub hC hD hex0 hinv hph hIA hB α.1 α.2 n hn
  exact units_iv hE hSub hex0 hinv α.1 α.2 hc hw (sTrans hE step1 step2)

theorem stepAll_of (hE : CalcEquiv) (hSub : CalcSubst) : StepAll := by
  intro p _ l ex ph S hS hU α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, -, hint_r, hIA, -, -, hdec, hB, -⟩ := hS
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have i0 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have i1 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have hI1 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.1 x) :=
    fun δ hδ x hx0 hx => int_mulBy_of hSub hex0 hinv δ.1 (hint_r δ hδ) x hx0 hx
  have hI2 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.2 x) :=
    fun δ hδ x hx0 hx => by
      have h := hint_r _ (hswap δ hδ)
      rw [Prod.fst_swap] at h
      exact int_mulBy_of hSub hex0 hinv δ.2 h x hx0 hx
  have c0 : ∀ (c : ℂ_[p]) (x : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c x) = 0 :=
    fun c x hx => constantCoeff_formalSMul hex0 hinv c x hx
  show PI.PhNormUnits.Simeq (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex (β.1 + γ.1) (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex (β.2 + γ.2) (PI.PhNormUnits.Xv 1)))
  rw [← add_mulBy hex0 hinv β.1 γ.1 _ h0,
    ← add_mulBy hex0 hinv β.2 γ.2 _ h1]
  have L := be_add_left hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.1 (PI.PhNormUnits.Xv 0))
    (PI.PhNormUnits.mulBy l ex γ.1 (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) (c0 _ _ h0) (c0 _ _ h0) h1
    (hI1 β hβ _ h0 i0) (hI1 γ hγ _ h0 i0) i1
  have R := be_add_right hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.2 (PI.PhNormUnits.Xv 1))
    (PI.PhNormUnits.mulBy l ex γ.2 (PI.PhNormUnits.Xv 1)) (PI.PhNormUnits.Xv 0) (c0 _ _ h1) (c0 _ _ h1) h0
    (hI2 β hβ _ h1 i1) (hI2 γ hγ _ h1 i1) i0
  exact sTrans hE L (sTrans hE
    (sAdd hE (hU β hβ hb1 hb2) (hU γ hγ hg1 hg2)) (sSymm hE R))

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TraceAt
noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section

variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) (hZ : CalcZpScale)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hE hSub hC hD hZ hex0 hinv hph hIA hB in
theorem trace_at (c d : ℂ_[p]) (hc : IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hd : IntegralMv (mulBy l ex d (Xv ()) : MvPowerSeries Unit ℂ_[p])) (t : ℤ_[p]) (ht : c + d = zc t)
    (hsw : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))))
    (hU2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ())))
    (h2inv : ∃ h : ℤ_[p], 2 * zc h = 1) {τ : Type} (w : MvPowerSeries τ ℂ_[p])
    (w0 : MvPowerSeries.constantCoeff w = 0) (wI : IntegralMv w) :
    Simeq (be l ex ph w (mulBy l ex c w)) (MvPowerSeries.C (c + d) * phAt ph w) := by
  have hw2 : ∀ i, MvPowerSeries.constantCoeff (![w, w] i) = 0 := by
    intro i; fin_cases i <;> simpa using w0
  have hcw0 : MvPowerSeries.constantCoeff (mulBy l ex c w) = 0 := constantCoeff_formalSMul hex0 hinv c w w0
  have hdw0 : MvPowerSeries.constantCoeff (mulBy l ex d w) = 0 := constantCoeff_formalSMul hex0 hinv d w w0
  have hcw : IntegralMv (mulBy l ex c w) := int_mulBy_of hSub hex0 hinv c hc w w0 wI
  have hdw : IntegralMv (mulBy l ex d w) := int_mulBy_of hSub hex0 hinv d hd w w0 wI
  have S1 : Simeq (be l ex ph (mulBy l ex c w) w) (be l ex ph w (mulBy l ex d w)) := by
    have e := simeq_subst2 hSub hex0 hinv w w w0 w0 wI wI hsw
    rw [sb_be (![w, w]) hw2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv c _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be (![w, w]) hw2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv d _ (constantCoeff_var 1)),
      sb_mulBy (![w, w]) hw2 hex0 hinv c _ (constantCoeff_var 0), sb_mulBy (![w, w]) hw2 hex0 hinv d _ (constantCoeff_var 1),
      sb_X (![w, w]) hw2, sb_X (![w, w]) hw2] at e
    simpa using e
  have A : Simeq (be l ex ph w (mulBy l ex c w)) (be l ex ph w (mulBy l ex d w)) := by
    rw [be_comm]; exact S1
  have S3 : Simeq (be l ex ph w (mulBy l ex (zc t) w))
      (be l ex ph w (mulBy l ex c w) + be l ex ph w (mulBy l ex d w)) := by
    rw [← ht, ← add_mulBy hex0 hinv c d w w0]
    exact be_add_right hSub hex0 hinv hB _ _ _ hcw0 hdw0 w0 hcw hdw wI
  have S4 := be_zp hE hSub hex0 hinv hB hC hD hph hIA w w w0 w0 wI wI t
  have S5 : Simeq (be l ex ph w w) (MvPowerSeries.C 2 * phAt ph w) := by
    have n2 := PI.PhNormUnits.UnitaryGroupMassFormula.norm_at hSub hex0 hinv 2 (2 * 2) hU2 w w0 wI
    have e : be l ex ph w w = phAt ph (mulBy l ex 2 w) - phAt ph w - phAt ph w := by
      rw [be, add_self hex0 hinv w w0]
    rw [e]
    refine sTrans hE (sSub hE (sSub hE n2 (sRefl hE _)) (sRefl hE _)) (sOfEq hE ?_)
    simp only [map_mul, map_ofNat]
    ring
  have T1 : Simeq (MvPowerSeries.C 2 * be l ex ph w (mulBy l ex c w))
      (MvPowerSeries.C 2 * (MvPowerSeries.C (c + d) * phAt ph w)) := by
    have e1 : MvPowerSeries.C (2 : ℂ_[p]) * be l ex ph w (mulBy l ex c w) =
        be l ex ph w (mulBy l ex c w) + be l ex ph w (mulBy l ex c w) := by
      simp only [map_ofNat]; ring
    rw [e1]
    refine sTrans hE (sAdd hE (sRefl hE _) A) (sTrans hE (sSymm hE S3) (sTrans hE S4 ?_))
    refine sTrans hE (hZ p τ _ _ t S5) (sOfEq hE ?_)
    rw [← ht]
    ring
  obtain ⟨h, hh⟩ := h2inv
  have T2 := hZ p τ _ _ h T1
  refine sTrans hE (sOfEq hE ?_) (sTrans hE T2 (sOfEq hE ?_))
  · rw [← mul_assoc, ← map_mul, mul_comm (zc h), hh, map_one, one_mul]
  · rw [← mul_assoc, ← map_mul, mul_comm (zc h), hh, map_one, one_mul]

include hE hSub hex0 hinv in
theorem sum_at (β γ : ℂ_[p] × ℂ_[p]) (iγ : IntegralMv (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hsw : Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))))
    (htr : Simeq (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.2 * γ.1 + β.1 * γ.2) * phAt ph (Xv ())))
    (nβ : Simeq (phAt ph (mulBy l ex β.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.1 * β.2) * phAt ph (Xv ())))
    (nγ : Simeq (phAt ph (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (γ.1 * γ.2) * phAt ph (Xv ()))) :
    Simeq (phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C ((β.1 + γ.1) * (β.2 + γ.2)) * phAt ph (Xv ())) := by
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hg0 : MvPowerSeries.constantCoeff (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv γ.1 _ hX0
  have hb0 : MvPowerSeries.constantCoeff (mulBy l ex β.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv β.1 _ hX0
  have hs2 : ∀ i, MvPowerSeries.constantCoeff
      (![Xv (), mulBy l ex γ.1 (Xv ())] i : MvPowerSeries Unit ℂ_[p]) = 0 := by
    intro i; fin_cases i
    · simp [hX0]
    · simpa using hg0
  have S1 : Simeq (be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ()))) := by
    have e := simeq_subst2 hSub hex0 hinv (Xv ()) (mulBy l ex γ.1 (Xv ())) hX0 hg0 (int_X ()) iγ hsw
    rw [sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv β.1 _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv β.2 _ (constantCoeff_var 1)),
      sb_mulBy _ hs2 hex0 hinv β.1 _ (constantCoeff_var 0), sb_mulBy _ hs2 hex0 hinv β.2 _ (constantCoeff_var 1),
      sb_X _ hs2, sb_X _ hs2] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rwa [mulBy_mulBy hex0 hinv β.2 γ.1 _ hX0] at e
  have e : phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) =
      be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) +
        phAt ph (mulBy l ex β.1 (Xv ())) + phAt ph (mulBy l ex γ.1 (Xv ())) := by
    rw [be, add_mulBy hex0 hinv β.1 γ.1 _ hX0]
    ring
  rw [e]
  refine sTrans hE (sAdd hE (sAdd hE (sTrans hE S1 htr) nβ) nγ) (sOfEq hE ?_)
  simp only [map_add (f := _), map_mul]
  ring

end

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepTrace_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : StepTrace := by
  intro p _ l ex ph S hH hA δ hδ
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hintS, hIA, htr, -, -, hB, hunit⟩ := hH
  have hU2 := hunit ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 (norm_two_of hp2) (norm_two_of hp2)
  have hph := ph_const_of hU2 hex0 hinv
  obtain ⟨t, ht⟩ := htr δ hδ
  have h2inv : ∃ h : ℤ_[p], 2 * zc h = 1 := by
    obtain ⟨h, hh⟩ := zc_inv_of (2 : ℤ_[p]) (by rw [zc_two]; exact norm_two_of hp2)
    exact ⟨h, by rwa [zc_two] at hh⟩
  exact trace_at hE hSub hC hD hZ hex0 hinv hph hIA hB δ.1 δ.2 (hintS δ hδ) (hintS δ.swap (hswap δ hδ)) t ht
    (hA δ hδ) hU2 h2inv (Xv ()) (constantCoeff_var ()) (int_X ())

theorem stepSum_of (hE : CalcEquiv) (hSub : CalcSubst) : StepSum := by
  intro p _ l ex ph S hH hA hT α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, hmul, hintS, -, -, -, hdec, -, hunit⟩ := hH
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  exact sum_at hE hSub hex0 hinv β γ (hintS γ hγ) (hA β hβ) (hT (β.swap * γ) (hmul β.swap (hswap β hβ) γ hγ))
    (hunit β hβ hb1 hb2) (hunit γ hγ hg1 hg2)

theorem target_of_calc (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : Target :=
  target_of_steps (stepUnits_of hE hSub hC hD) (stepAll_of hE hSub) (stepTrace_of hE hSub hC hD hZ)
    (stepSum_of hE hSub)

theorem norm_units_of_calculation : Target :=
  target_of_calc norm_units_equivalence norm_units_substitution norm_units_closed_form natCast_dense_p_adic norm_units_zp_scaling

end PI.PhNormUnits.UnitaryGroupMassFormula
