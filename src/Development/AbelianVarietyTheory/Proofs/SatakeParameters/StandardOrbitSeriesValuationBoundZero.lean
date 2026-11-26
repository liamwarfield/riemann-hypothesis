module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HurwitzSubstituteTwoSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AddCoordExponentIntegralJetsUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AddCoordExponentIntegralJetsUnramified
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2)
open Formalism.L2.Th1.D (expF IsMul)

section Ball

variable (K : Type) [NormedField K] [IsUltrametricDist K]

def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem mem_ball {x : K} : x ∈ ball K ↔ ‖x‖ ≤ 1 := Iff.rfl

end Ball

section Exp

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem norm_natCast_le (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

theorem lgF_deriv_int (l : ℕ) (hl : 2 ≤ l) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative (lgF K l)) ∈ ball K := by
  rw [PowerSeries.coeff_derivative]
  unfold lgF
  rw [PowerSeries.coeff_mk, Finset.sum_mul]
  refine (ball K).sum_mem fun j _ => ?_
  split_ifs with h
  · have hp : (l : K) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
    have e : ((n : K) + 1) = (l : K) ^ j * (l : K) ^ j := by
      rw [← pow_add, ← two_mul]
      have h' : ((n + 1 : ℕ) : K) = (((l ^ 2) ^ j : ℕ) : K) := by rw [h]
      push_cast at h'
      rw [h', ← pow_mul]
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]
    exact (ball K).pow_mem (norm_natCast_le l) j
  · rw [zero_mul]
    exact (ball K).zero_mem

theorem hur_expF (l : ℕ) (hl : 2 ≤ l) :
    Hur (ball K) ((expF K l : PowerSeries K) : MvPowerSeries Unit K) := by
  rw [Formalism.L2.Th1.D.FormalExponential.expF_eq l hl]
  refine hur_substInv (ball K) (Formalism.L2.Th1.D.Pair.cc_lgF hl) _ ?_ (lgF_deriv_int l hl)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add,
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hl]
  simp

theorem cc_expF (l : ℕ) (hl : 2 ≤ l) : PowerSeries.constantCoeff (expF K l) = 0 :=
  (Formalism.L2.Th1.D.exponential_specification K l hl).1

theorem hurwitz_integral_expSeries_single_variable {ι : Type} [Fintype ι] [DecidableEq ι] (l : ℕ) (hl : 2 ≤ l) (i : ι) :
    Hur (ball K) (at1 i (expF K l) : MvPowerSeries ι K) := by
  unfold at1
  rw [PowerSeries.subst_def]
  exact hur_subst (ball K) (fun _ => constantCoeff_X i) (fun _ => hur_X (ball K) i) (hur_expF l hl)

theorem hur_of_simeq0 {τ : Type} [Fintype τ] [DecidableEq τ] (l : ℕ) (hl : 2 ≤ l)
    {h : MvPowerSeries τ K} (hs : Simeq h 0) :
    Hur (ball K) (subst (fun i => (at1 i (expF K l) : MvPowerSeries τ K)) h) := by
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hφ0 : ∀ i : τ, constantCoeff (at1 i (expF K l) : MvPowerSeries τ K) = 0 :=
    fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (cc_expF l hl)
  have hE : Hur (ball K) (Formalism.L2.Th1.C.mvExp h) := hur_of_int _ fun n => hI n
  have hS := hur_subst (ball K) hφ0 (fun i => hurwitz_integral_expSeries_single_variable l hl i) hE
  rw [Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp h0 hφ0] at hS
  set g := subst (fun i => (at1 i (expF K l) : MvPowerSeries τ K)) h with hg
  have hg0 : constantCoeff g = 0 := by rw [hg, cc_subst hφ0, h0]
  have h1 : constantCoeff (Formalism.L2.Th1.C.mvExp g) = 1 := Formalism.L2.Th1.C.constantCoeff_mvExp hg0
  have hEi : Hur (ball K) (Formalism.L2.Th1.C.mvExp g)⁻¹ := hur_inv _ hS h1
  refine hur_of_pderiv _ (by rw [hg0]; exact (ball K).zero_mem) fun i => ?_
  have e : pderiv i g = pderiv i (Formalism.L2.Th1.C.mvExp g) * (Formalism.L2.Th1.C.mvExp g)⁻¹ := by
    rw [Formalism.L2.Th1.C.pderiv_mvExp hg0, mul_assoc,
      MvPowerSeries.mul_inv_cancel _ (by rw [h1]; exact one_ne_zero), mul_one]
  rw [e]
  exact hur_mul _ (hur_pderiv _ hS i) hEi

end Exp

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet Formalism.L2.Th1.D.Pair
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob)
open Formalism.L2.Th1.D (expF IsMul addC)

section Transfer

variable {K : Type} [Field K]

theorem subst_addC (l : ℕ) (hl : 2 ≤ l) {τ : Type} {u w : MvPowerSeries τ K} (hu : constantCoeff u = 0)
    (hw : constantCoeff w = 0) (be0 : MvPowerSeries (Fin 2) K) :
    subst ![u, w] (addC l be0) =
      subst ![PowerSeries.subst u (expF K l), PowerSeries.subst w (expF K l)] be0 := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have hs := hs2 hu hw
  unfold addC
  rw [subst2_comp hs (constantCoeff_inVar_eq_zero _ h0) (constantCoeff_inVar_eq_zero _ h0), subst_single_var hs, subst_single_var hs]
  rfl

theorem logSeries_subst_expSeries_variable (l : ℕ) (hl : 2 ≤ l) {τ : Type} (x : τ) :
    PowerSeries.subst (at1 x (expF K l) : MvPowerSeries τ K) (lgF K l) = X x := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  unfold at1
  rw [ps_comp (constantCoeff_X x) h0, (Formalism.L2.Th1.D.exponential_specification K l hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)]

theorem law_at_exp (l : ℕ) (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0)
    (hF : cob F (lgF K l) = 0) :
    subst ![(at1 0 (expF K l) : MvPowerSeries (Fin 3) K), at1 1 (expF K l)] F =
      PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 3) K) (expF K l) := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have ha := constantCoeff_inVar_eq_zero (0 : Fin 3) h0
  have hb := constantCoeff_inVar_eq_zero (1 : Fin 3) h0
  have hc : constantCoeff (subst ![(at1 0 (expF K l) : MvPowerSeries (Fin 3) K), at1 1 (expF K l)] F) = 0 :=
    constantCoeff_subst_eq_zero (hs2 ha hb) (by intro i; fin_cases i <;> simp [ha, hb]) hF0
  have hlog := log_law hF0 hF ha hb
  rw [logSeries_subst_expSeries_variable l hl, logSeries_subst_expSeries_variable l hl] at hlog
  rw [← hlog, exp_log Formalism.L2.Th1.D.exponential_specification hl hc]

theorem exp_mul_root (l : ℕ) (hl : 2 ≤ l) {ζ : K} (hζ : ζ ^ (l ^ 2 - 1) = 1) {τ : Type} (x : τ) :
    PowerSeries.subst (C ζ * X x : MvPowerSeries τ K) (expF K l) = C ζ * at1 x (expF K l) := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have ha := constantCoeff_inVar_eq_zero x h0
  have hm := Formalism.L2.Th1.D.FormalExponential.isMul_root (K := K) hl hζ
  have hw : PowerSeries.subst (at1 x (expF K l) : MvPowerSeries τ K) (PowerSeries.C ζ * PowerSeries.X) =
      C ζ * at1 x (expF K l) := by
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_C, PowerSeries.subst_X hs]
  have hwc : constantCoeff (C ζ * at1 x (expF K l) : MvPowerSeries τ K) = 0 := by
    rw [map_mul, ha, mul_zero]
  have hl2 := log_mul hm ha
  rw [hw, logSeries_subst_expSeries_variable l hl] at hl2
  rw [← hl2, exp_log Formalism.L2.Th1.D.exponential_specification hl hwc]

end Transfer

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet

section Deriv

variable {K : Type} [Field K]

theorem constantCoeff_X_fin_three (i : Fin 3) : constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := constantCoeff_X i

theorem dd_first (B : MvPowerSeries (Fin 2) K) :
    pderiv 0 (pderiv 1 (subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] B -
      subst ![(X 0 : MvPowerSeries (Fin 3) K), X 2] B - subst ![(X 1 : MvPowerSeries (Fin 3) K), X 2] B)) =
      subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] (pderiv 0 (pderiv 0 B)) := by
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  simp only [map_sub]
  rw [pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
  simp only [map_add (f := _), pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]
  rw [pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
  simp [pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

theorem dd_second (B : MvPowerSeries (Fin 2) K) :
    pderiv 0 (pderiv 1 (subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] B -
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0] B - subst ![(X 2 : MvPowerSeries (Fin 3) K), X 1] B)) =
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] (pderiv 1 (pderiv 1 B)) := by
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  simp only [map_sub]
  rw [pd2 _ (constantCoeff_X_fin_three 2) h01, pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 0), pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]
  simp only [map_add (f := _), pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]
  rw [pd2 _ (constantCoeff_X_fin_three 2) h01, pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]
  simp [pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

theorem restr' (g : MvPowerSeries (Fin 2) K) (u w : MvPowerSeries (Fin 3) K)
    (b : Fin 3 → MvPowerSeries (Fin 2) K)
    (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (hbu : subst b u = X 0) (hbw : subst b w = X 1) :
    subst b (subst ![u, w] g) = g := by
  have ha : HasSubst (![u, w] : Fin 2 → MvPowerSeries (Fin 3) K) :=
    hasSubst_of_constantCoeff_zero (cc2 hu hw)
  have hbs : HasSubst b := hasSubst_of_constantCoeff_zero hb
  rw [subst_comp_subst_apply ha hbs]
  have e : (fun s => subst b ((![u, w] : Fin 2 → MvPowerSeries (Fin 3) K) s)) = X := by
    funext s
    fin_cases s
    · simpa using hbu
    · simpa using hbw
  rw [e, subst_self]
  rfl

theorem conj_dd' (be : MvPowerSeries (Fin 2) K) (a' b' : K) :
    constantCoeff (pderiv 0 (pderiv 1 (subst ![C a' * X 0, X 1] be - subst ![X 0, C b' * X 1] be :
      MvPowerSeries (Fin 2) K))) =
      constantCoeff (pderiv 0 (pderiv 1 be)) * (a' - b') := by
  have hu : constantCoeff (C a' * X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hw : constantCoeff (C b' * X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
  have hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 1
  have hu0 : pderiv 0 (C a' * X 0 : MvPowerSeries (Fin 2) K) = C a' := by
    rw [Derivation.leibniz]; simp
  have hu1 : pderiv 1 (C a' * X 0 : MvPowerSeries (Fin 2) K) = 0 := by
    rw [Derivation.leibniz]; simp [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  have hw0 : pderiv 0 (C b' * X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    rw [Derivation.leibniz]; simp [pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have hw1 : pderiv 1 (C b' * X 1 : MvPowerSeries (Fin 2) K) = C b' := by
    rw [Derivation.leibniz]; simp
  have A1 : pderiv 1 (subst ![C a' * X 0, X 1] be : MvPowerSeries (Fin 2) K) =
      subst ![C a' * X 0, X 1] (pderiv 1 be) := by
    rw [pd2 _ hu hX1, hu1, pderiv_X_self]; ring
  have A0 : pderiv 0 (subst ![C a' * X 0, X 1] (pderiv 1 be) : MvPowerSeries (Fin 2) K) =
      subst ![C a' * X 0, X 1] (pderiv 0 (pderiv 1 be)) * C a' := by
    rw [pd2 _ hu hX1, hu0, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; ring
  have B1 : pderiv 1 (subst ![X 0, C b' * X 1] be : MvPowerSeries (Fin 2) K) =
      subst ![X 0, C b' * X 1] (pderiv 1 be) * C b' := by
    rw [pd2 _ hX0 hw, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), hw1]; ring
  have B0 : pderiv 0 (subst ![X 0, C b' * X 1] (pderiv 1 be) * C b' : MvPowerSeries (Fin 2) K) =
      subst ![X 0, C b' * X 1] (pderiv 0 (pderiv 1 be)) * C b' := by
    rw [Derivation.leibniz, pd2 _ hX0 hw, pderiv_C, pderiv_X_self, hw0]; simp [mul_comm]
  rw [map_sub, map_sub, A1, A0, B1, B0, map_sub, map_mul, map_mul, cc_subst (cc2 hu hX1),
    cc_subst (cc2 hX0 hw), constantCoeff_C, constantCoeff_C]
  ring

end Deriv

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet Formalism.L2.Th1.D.Pair
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob)
open Formalism.L2.Th1.D (expF IsMul addC)

section Main

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

omit [CharZero K] in
theorem norm_sub_le_max'' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])

theorem norm_root_sub_pow (l : ℕ) (hl : 2 ≤ l) (hlt1 : ‖(l : K)‖ < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) : ‖ζ - ζ ^ l‖ = 1 := by
  have hq0 : l * 2 ≤ l * l := Nat.mul_le_mul_left l hl
  have hpos : 0 < l ^ 2 - 1 := by rw [sq]; omega
  have hζ1 : ζ ^ (l ^ 2 - 1) = 1 := hζ.pow_eq_one
  have hnζ : ‖ζ‖ = 1 := Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow hpos.ne' hζ1
  have hN : ‖((l ^ 2 - 1 : ℕ) : K)‖ = 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
    have hq : ‖(l : K) ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt1 (by norm_num)
    apply le_antisymm
    · exact (norm_sub_le_max'' _ _).trans (max_le hq.le (by simp))
    · by_contra hc
      push_neg at hc
      have h1 : ‖(1 : K)‖ ≤ max ‖(l : K) ^ 2‖ ‖(l : K) ^ 2 - 1‖ := by
        have := norm_sub_le_max'' ((l : K) ^ 2) ((l : K) ^ 2 - 1)
        simpa using this
      rw [norm_one] at h1
      exact absurd h1 (not_le.2 (max_lt hq hc))
  have hle : ‖ζ - ζ ^ l‖ ≤ 1 :=
    (norm_sub_le_max'' _ _).trans (max_le hnζ.le (by rw [norm_pow, hnζ, one_pow]))
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have heq := Formalism.L2.Th1.D.FormalExponential.root_eq_of_norm_lt hN hζ1 hζl hlt
  have hz : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnζ
    exact zero_ne_one hnζ
  have hp : ζ ^ (l - 1) = 1 := by
    have : ζ ^ (l - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← heq]
    exact mul_right_cancel₀ hz this
  have hd := (hζ.pow_eq_one_iff_dvd (l - 1)).1 hp
  have hle' : l ^ 2 - 1 ≤ l - 1 := Nat.le_of_dvd (by omega) hd
  rw [sq] at hle'
  omega

theorem hur_addC (l : ℕ) (σ : K →+* K) (hU : Formalism.InvariantFactorPaths.G7.UnrOK K l σ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) {F be0 : MvPowerSeries (Fin 2) K}
    (hF : Formalism.InvariantFactorPaths.G7.IsLawOfLog l F) (h1 : Formalism.L2.Th1.D.F1 F be0) (h2 : Formalism.L2.Th1.D.F2 l σ be0) :
    Hur (ball K) (addC l be0) := by
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨hF0, -, hcob⟩ := hF
  obtain ⟨hab, hd1, hd2⟩ := h1
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have e3 : (fun i : Fin 3 => (at1 i (expF K l) : MvPowerSeries (Fin 3) K)) =
      ![at1 0 (expF K l), at1 1 (expF K l), at1 2 (expF K l)] := by
    funext i; fin_cases i <;> rfl
  have c3 : ∀ i : Fin 3, constantCoeff (at1 i (expF K l) : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => constantCoeff_inVar_eq_zero i h0
  have hlaw := law_at_exp l hl hF0 hcob
  have hX01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have hD1 : Hur (ball K) (subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] (addC l be0) -
      subst ![(X 0 : MvPowerSeries (Fin 3) K), X 2] (addC l be0) -
      subst ![(X 1 : MvPowerSeries (Fin 3) K), X 2] (addC l be0)) := by
    have H := hur_of_simeq0 (τ := Fin 3) l hl hd1
    rw [e3, subst_first_coboundary_three hF0 (c3 0) (c3 1) (c3 2), hlaw] at H
    rw [subst_addC l hl hX01 (constantCoeff_X_fin_three 2), subst_addC l hl (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2),
      subst_addC l hl (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
    exact H
  have hD2 : Hur (ball K) (subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] (addC l be0) -
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0] (addC l be0) -
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 1] (addC l be0)) := by
    have H := hur_of_simeq0 (τ := Fin 3) l hl hd2
    rw [e3, subst_first_coboundary_three hF0 (c3 0) (c3 1) (c3 2), hlaw, subst_swap2 (cc_ps hX01 h0) (c3 2),
      subst_swap2 (c3 0) (c3 2), subst_swap2 (c3 1) (c3 2)] at H
    rw [subst_addC l hl (constantCoeff_X_fin_three 2) hX01, subst_addC l hl (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 0),
      subst_addC l hl (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]
    exact H
  have h00 : Hur (ball K) (pderiv 0 (pderiv 0 (addC l be0))) := by
    have H := hur_pderiv _ (hur_pderiv _ hD1 1) 0
    rw [dd_first] at H
    have hb0 : ∀ j, constantCoeff ((![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) K) j) = 0 := by
      intro j; fin_cases j <;> simp
    have hb : HasSubst (![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) K) :=
      hasSubst_of_constantCoeff_zero hb0
    have := hur_subst (ball K) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H
    rwa [restr' _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)
      (by rw [subst_X hb]; simp)] at this
  have h11 : Hur (ball K) (pderiv 1 (pderiv 1 (addC l be0))) := by
    have H := hur_pderiv _ (hur_pderiv _ hD2 1) 0
    rw [dd_second] at H
    have hb0 : ∀ j, constantCoeff ((![X 1, 0, X 0] : Fin 3 → MvPowerSeries (Fin 2) K) j) = 0 := by
      intro j; fin_cases j <;> simp
    have hb : HasSubst (![X 1, 0, X 0] : Fin 3 → MvPowerSeries (Fin 2) K) :=
      hasSubst_of_constantCoeff_zero hb0
    have := hur_subst (ball K) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H
    rwa [restr' _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_X hb]; simp)
      (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)] at this
  have hζ1 : ζ ^ (l ^ 2 - 1) = 1 := hζ.pow_eq_one
  have hσζ : σ ζ = ζ ^ l := Formalism.L2.Th1.D.teichmuller_sigma K l 2 σ hU (by norm_num) ζ hζ1
  have hζ'1 : (σ ζ) ^ (l ^ 2 - 1) = 1 := by rw [hσζ, ← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have hq0 : l * 2 ≤ l * l := Nat.mul_le_mul_left l hl
  have hnζ : ‖ζ‖ = 1 :=
    Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow (by rw [sq]; omega) hζ1
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul]
    have : l * l = (l ^ 2 - 1) + 1 := by rw [sq]; omega
    rw [this, pow_succ, hζ1, one_mul]
  have hC := h2 ζ hnζ.le hσσ _ _ (Formalism.L2.Th1.D.FormalExponential.isMul_root hl hζ1)
    (Formalism.L2.Th1.D.FormalExponential.isMul_root hl hζ'1)
  rw [Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X, Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X] at hC
  have hC' : Simeq (subst ![C ζ * X 0, X 1] be0 - subst ![X 0, C (σ ζ) * X 1] be0 :
      MvPowerSeries (Fin 2) K) 0 := by
    unfold Simeq at hC ⊢
    rwa [sub_zero]
  have H := hur_of_simeq0 (τ := Fin 2) l hl hC'
  have e2 : (fun i : Fin 2 => (at1 i (expF K l) : MvPowerSeries (Fin 2) K)) =
      ![at1 0 (expF K l), at1 1 (expF K l)] := by
    funext i; fin_cases i <;> rfl
  have hs2' : HasSubst ![(at1 0 (expF K l) : MvPowerSeries (Fin 2) K), at1 1 (expF K l)] :=
    hs2 (constantCoeff_inVar_eq_zero _ h0) (constantCoeff_inVar_eq_zero _ h0)
  rw [e2, subst_sub hs2', subst2_comp hs2' (by simp) (by simp),
    subst2_comp hs2' (by simp) (by simp), subst_mul hs2', subst_mul hs2', subst_C, subst_C,
    subst_X hs2', subst_X hs2'] at H
  have hD3 : Hur (ball K) (subst ![C ζ * X 0, X 1] (addC l be0) -
      subst ![X 0, C (σ ζ) * X 1] (addC l be0) : MvPowerSeries (Fin 2) K) := by
    rw [subst_addC l hl (by simp) (by simp), subst_addC l hl (by simp) (by simp),
      exp_mul_root l hl hζ1, exp_mul_root l hl hζ'1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at H
    exact H
  have hlt1 : ‖(l : K)‖ < 1 := by
    rw [hU.2.2.1]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hU.1.one_lt)
  have hsep : ‖ζ - σ ζ‖ = 1 := by rw [hσζ]; exact norm_root_sub_pow l hl hlt1 hζ
  have h01 : constantCoeff (pderiv 0 (pderiv 1 (addC l be0))) ∈ ball K := by
    have hc := hur_cc _ (hur_pderiv _ (hur_pderiv _ hD3 1) 0)
    rw [conj_dd', mem_ball, norm_mul, hsep, mul_one] at hc
    exact hc
  have hDiv : DivAB (addC l be0) := Formalism.L2.Th1.D.TorusDerivation.divAB_addC l hab
  intro n
  by_cases hz : n 0 = 0 ∨ n 1 = 0
  · rw [hDiv n hz, mul_zero]
    exact (ball K).zero_mem
  · push_neg at hz
    by_cases h2' : 2 ≤ n 0
    · have e1 := decomp n 0 hz.1
      have hm : (n - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 ≠ 0 := by simp; omega
      have e2 := decomp (n - Finsupp.single 0 1) 0 hm
      rw [e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]
      exact h00 _
    · by_cases h2'' : 2 ≤ n 1
      · have e1 := decomp n 1 hz.2
        have hm : (n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 ≠ 0 := by simp; omega
        have e2 := decomp (n - Finsupp.single 1 1) 1 hm
        rw [e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]
        exact h11 _
      · have en : n = (0 + Finsupp.single 0 1) + Finsupp.single 1 1 := by
          ext x
          fin_cases x <;> simp <;> omega
        rw [en, ← fc_coeff_pderiv, ← fc_coeff_pderiv, fc_zero, one_mul,
          coeff_zero_eq_constantCoeff_apply]
        exact h01

end Main

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open Formalism.L2.KerInert.Jet

theorem addC_integral_jets : ∀ (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)),
    UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F → F1 F be0 → F2 l σ be0 → ∀ n : Fin 2 →₀ ℕ,
      ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1 := by
  intro l _ σ F be0 hU hF h1 h2 n
  have hl : 2 ≤ l := hU.1.two_le
  have hq0 : l * 2 ≤ l * l := Nat.mul_le_mul_left l hl
  have hpos : 0 < l ^ 2 - 1 := by rw [sq]; omega
  have hnd : ¬ l ∣ l ^ 2 - 1 := by
    intro hd
    have h' : l ∣ (l ^ 2 - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
      exact dvd_pow_self l (by norm_num)
    have h1' : l ∣ 1 := (Nat.dvd_add_right hd).1 h'
    exact hU.1.one_lt.ne' (Nat.dvd_one.1 h1')
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.unramified_completion_roots l (l ^ 2 - 1) hpos hnd
  have H := hur_addC l σ hU hζ hF h1 h2 n
  have e : (fc n : MaximalUnramifiedExtension l) = (((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) := by
    rw [fc_of_subset (S := Finset.univ) (Finset.subset_univ _), Fin.prod_univ_two]
    push_cast
    ring
  rw [← e]
  exact H

end GlobalTheory.AddJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AddCoordExponentIntegralJetsUnramifiedStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addCoord_exponent_integral_jets_unramified : ∀ (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F → F1 F be0 → F2 l σ be0 → ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1 := by
  first | exact @GlobalTheory.AddJet.addC_integral_jets | exact GlobalTheory.AddJet.addC_integral_jets | (intros; apply GlobalTheory.AddJet.addC_integral_jets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZero
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE expF xOfZ)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob lgF at1)
open Formalism.L2.KerInert.Jet (Hur fc fc_of_subset hur_subst hur_mul hur_sum hur_zero hur_neg hur_C hur_X hur_of_int hur_substInv cc_subst)

namespace GlobalTheory.KerZero

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_ball {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} : x ∈ ball K ↔ ‖x‖ ≤ 1 := Iff.rfl

section Gen

variable {K : Type} [Field K] [CharZero K] (R : Subring K)

theorem coeff_one_lgF {l : ℕ} (hl : 2 ≤ l) : PowerSeries.coeff 1 (lgF K l) = 1 := by
  unfold lgF
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    have h1 : 1 < (l ^ 2) ^ j := Nat.one_lt_pow hj (Nat.one_lt_pow two_ne_zero (by omega))
    omega
  · simp

theorem cc_lgF (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold lgF
  rw [PowerSeries.coeff_mk]
  simp

theorem lgF_deriv_int {l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative (R := K) (lgF K l)) ∈ R := by
  rw [PowerSeries.coeff_derivative]
  unfold lgF
  rw [PowerSeries.coeff_mk, Finset.sum_mul]
  refine R.sum_mem fun j _ => ?_
  split_ifs with h
  · have hp : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
    have e : ((n : K) + 1) = (l : K) ^ j * (l : K) ^ j := by
      rw [← pow_add, ← two_mul, pow_mul]
      exact_mod_cast h
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]
    exact R.pow_mem (natCast_mem R l) j
  · rw [zero_mul]
    exact R.zero_mem

theorem hur_expF {l : ℕ} (hl : 2 ≤ l) : Hur R ((expF K l : PowerSeries K) : MvPowerSeries Unit K) := by
  have hu : IsUnit (PowerSeries.coeff 1 (lgF K l)) := by rw [coeff_one_lgF hl]; exact isUnit_one
  unfold expF
  rw [dite_eq_left hu]
  refine hur_substInv R (cc_lgF l) hu ?_ (lgF_deriv_int R hl)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, coeff_one_lgF hl]
  simp

theorem hur_psubst {τ : Type} [Finite τ] {a : MvPowerSeries τ K} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : Hur R a)
    {g : PowerSeries K} (hg : Hur R (g : MvPowerSeries Unit K)) : Hur R (PowerSeries.subst a g) := by
  rw [PowerSeries.subst_def]
  exact hur_subst R (fun _ => ha0) (fun _ => ha) hg

theorem cc_psubst {τ : Type} [Finite τ] {a : MvPowerSeries τ K} (ha0 : MvPowerSeries.constantCoeff a = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a g) = 0 := by
  rw [PowerSeries.subst_def, cc_subst (fun _ => ha0)]
  exact hg

theorem hur_exp : Hur R ((PowerSeries.exp K : PowerSeries K) : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext u
    simp
  have hc : MvPowerSeries.coeff n (PowerSeries.exp K : MvPowerSeries Unit K) = PowerSeries.coeff (n ()) (PowerSeries.exp K) := by
    conv_lhs => rw [hn]
    rfl
  have hf : (fc n : K) = ((n ()).factorial : K) := by
    rw [fc_of_subset (S := Finset.univ) (Finset.subset_univ _)]
    simp
  rw [hc, hf, PowerSeries.coeff_exp]
  have : ((n ()).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp [this]

end Gen

section Cp

variable {l : ℕ} [Fact l.Prime]

theorem norm_frob_le {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {a : MaximalUnramifiedExtension l} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ l‖ ≤ 1 := (hσ.2.2.2.2 a ha).trans (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖a ^ l‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have e : ((σ a : MaximalUnramifiedExtension l) : ℂ_[l]) = ((σ a - a ^ l : MaximalUnramifiedExtension l) : ℂ_[l]) + ((a ^ l : MaximalUnramifiedExtension l) : ℂ_[l]) := by
    push_cast; ring
  show ‖((σ a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ 1
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_iter_le {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {a : MaximalUnramifiedExtension l} (ha : ‖a‖ ≤ 1) (k : ℕ) : ‖σ^[k] a‖ ≤ 1 := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [Function.iterate_succ_apply']; exact norm_frob_le hσ ih

variable {d N0 N1 : ℕ} [NeZero d]

theorem hur_linTerm (c : ℂ_[l]) (hc : ‖c‖ ≤ 1) (v : ZMod d × Fin N0 × Fin N1) :
    Hur (ball ℂ_[l]) (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) :=
  hur_mul _ (hur_C _ hc) (hur_X _ v)

def uL (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (c : MaximalUnramifiedExtension l) (a : Fin N0) (b : Fin N1) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l] :=
  ∑ s : ZMod d, if s.val % 2 = 0 then
    MvPowerSeries.C ((MaximalUnramifiedExtension l).subtype (σ^[s.val] c)) * (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) else 0

def vL (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (c : MaximalUnramifiedExtension l) (a : Fin N0) (b : Fin N1) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l] :=
  ∑ s : ZMod d, if s.val % 2 = 0 then 0 else
    MvPowerSeries.C ((MaximalUnramifiedExtension l).subtype (σ^[s.val] c)) * (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l])

theorem uL_spec {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {c : MaximalUnramifiedExtension l} (hc : ‖c‖ ≤ 1) (a : Fin N0) (b : Fin N1) :
    Hur (ball ℂ_[l]) (uL (d := d) σ c a b) ∧ MvPowerSeries.constantCoeff (uL (d := d) σ c a b) = 0 := by
  constructor
  · refine hur_sum _ _ _ fun s _ => ?_
    split_ifs
    · exact hur_linTerm _ (norm_iter_le hσ hc _) _
    · exact hur_zero _
  · unfold uL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs <;> simp

theorem vL_spec {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {c : MaximalUnramifiedExtension l} (hc : ‖c‖ ≤ 1) (a : Fin N0) (b : Fin N1) :
    Hur (ball ℂ_[l]) (vL (d := d) σ c a b) ∧ MvPowerSeries.constantCoeff (vL (d := d) σ c a b) = 0 := by
  constructor
  · refine hur_sum _ _ _ fun s _ => ?_
    split_ifs
    · exact hur_zero _
    · exact hur_linTerm _ (norm_iter_le hσ hc _) _
  · unfold vL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs <;> simp

theorem cc_expF (hl : 2 ≤ l) : PowerSeries.constantCoeff (expF ℂ_[l] l) = 0 :=
  (Formalism.L2.Th1.D.expSpec ℂ_[l] l hl).1

variable {ι : Type}

theorem xOfZ_false (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (om oms : ι → MaximalUnramifiedExtension l) (r : ι) (a : Fin N0) (b : Fin N1) :
    xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms (false, r, a, b) = PowerSeries.subst (uL (d := d) σ (oms r) a b) (expF ℂ_[l] l) := by
  simp [xOfZ, uL]

theorem xOfZ_true (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (om oms : ι → MaximalUnramifiedExtension l) (r : ι) (a : Fin N0) (b : Fin N1) :
    xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms (true, r, a, b) = PowerSeries.subst (vL (d := d) σ (om r) a b) (expF ℂ_[l] l) := by
  simp [xOfZ, vL]

theorem xOfZ_spec (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (om oms : ι → MaximalUnramifiedExtension l)
    (hO : ∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1) (x : Bool × ι × Fin N0 × Fin N1) :
    Hur (ball ℂ_[l]) (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) ∧
      MvPowerSeries.constantCoeff (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) = 0 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨t, r, a, b⟩ := x
  cases t
  · rw [xOfZ_false]
    have h := uL_spec (d := d) hσ (hO r).2 a b
    exact ⟨hur_psubst _ h.2 h.1 (hur_expF _ hl), cc_psubst h.2 (cc_expF hl)⟩
  · rw [xOfZ_true]
    have h := vL_spec (d := d) hσ (hO r).1 a b
    exact ⟨hur_psubst _ h.2 h.1 (hur_expF _ hl), cc_psubst h.2 (cc_expF hl)⟩

theorem hur_addC (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (h : ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1) :
    Hur (ball ℂ_[l]) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0)) := by
  intro n
  have hf : (fc n : ℂ_[l]) = (((n 0).factorial * (n 1).factorial : ℕ) : ℂ_[l]) := by
    rw [fc_of_subset (S := Finset.univ) (Finset.subset_univ _), Fin.prod_univ_two]
    push_cast
    rfl
  rw [hf, MvPowerSeries.coeff_map]
  have := h n
  rw [mem_ball]
  simpa using this

theorem map_addC (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) :
    MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0) =
      MvPowerSeries.subst ![at1 (0 : Fin 2) (expF ℂ_[l] l), at1 (1 : Fin 2) (expF ℂ_[l] l)]
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hcc : ∀ (K : Type) [Field K] [CharZero K] (i : Fin 2), MvPowerSeries.constantCoeff (at1 i (expF K l)) = 0 :=
    fun K _ _ i => cc_psubst (by simp) (Formalism.L2.Th1.D.expSpec K l hl).1
  unfold addC
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    fin_cases i
    · exact hcc _ 0
    · exact hcc _ 1))]
  congr 1
  funext i
  have hat : ∀ i : Fin 2, MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (at1 i (expF (MaximalUnramifiedExtension l) l)) = at1 i (expF ℂ_[l] l) := by
    intro i
    unfold at1
    have := PowerSeries.map_subst (PowerSeries.HasSubst.X (S := MaximalUnramifiedExtension l) i) (h := (MaximalUnramifiedExtension l).subtype) (expF (MaximalUnramifiedExtension l) l)
    rw [this, Formalism.L2.Th1.Top.PAdicPowerSeriesCoefficients.map_expF _ hl, MvPowerSeries.map_X]
  fin_cases i
  · exact hat 0
  · exact hat 1

end Cp

section Main

variable {l : ℕ} [Fact l.Prime] {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]

theorem hur_pair (u v : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) (hu : Hur (ball ℂ_[l]) u)
    (hu0 : MvPowerSeries.constantCoeff u = 0) (hv : Hur (ball ℂ_[l]) v) (hv0 : MvPowerSeries.constantCoeff v = 0)
    (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (hb : Hur (ball ℂ_[l]) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0))) :
    Hur (ball ℂ_[l]) (MvPowerSeries.subst ![PowerSeries.subst u (expF ℂ_[l] l), PowerSeries.subst v (expF ℂ_[l] l)]
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0)) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff ((![u, v] : Fin 2 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) i) = 0 := by
    intro i; fin_cases i
    · exact hu0
    · exact hv0
  have h1 : ∀ i : Fin 2, Hur (ball ℂ_[l]) ((![u, v] : Fin 2 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) i) := by
    intro i; fin_cases i
    · exact hu
    · exact hv
  have hs2 := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  have hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff (at1 i (expF ℂ_[l] l)) = 0 :=
    fun i => cc_psubst (by simp) (cc_expF hl)
  have hs1 : MvPowerSeries.HasSubst (![at1 (0 : Fin 2) (expF ℂ_[l] l), at1 (1 : Fin 2) (expF ℂ_[l] l)] :
      Fin 2 → MvPowerSeries (Fin 2) ℂ_[l]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
      fin_cases i
      · exact hc 0
      · exact hc 1)
  have hat : ∀ i : Fin 2, MvPowerSeries.subst ![u, v] (at1 i (expF ℂ_[l] l)) =
      PowerSeries.subst ((![u, v] : Fin 2 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) i) (expF ℂ_[l] l) := by
    intro i
    unfold at1
    rw [PowerSeries.subst_def, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)) hs2]
    congr 1
    funext _
    rw [MvPowerSeries.subst_X hs2]
  have e : MvPowerSeries.subst ![PowerSeries.subst u (expF ℂ_[l] l), PowerSeries.subst v (expF ℂ_[l] l)]
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) =
      MvPowerSeries.subst ![u, v] (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0)) := by
    rw [map_addC, MvPowerSeries.subst_comp_subst_apply hs1 hs2]
    congr 1
    funext i
    fin_cases i
    · exact (hat 0).symm
    · exact (hat 1).symm
  rw [e]
  exact hur_subst _ h0 h1 hb

theorem subst_sumE {a : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]}
    (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0) (B : MvPowerSeries (Fin 2) ℂ_[l]) :
    MvPowerSeries.subst a (sumE (ι := ι) (N0 := N0) (N1 := N1) B) =
      ∑ e : ι × Fin N0 × Fin N1, MvPowerSeries.subst ![a (false, e), a (true, e)] B := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold sumE
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)) hs]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hs]
  fin_cases i <;> simp

theorem cc_sumE (B : MvPowerSeries (Fin 2) ℂ_[l]) (h : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) B) = 0 := by
  unfold sumE
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [cc_subst (fun _ => by simp), h]

theorem hur_theta (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (hb0 : MvPowerSeries.constantCoeff be0 = 0)
    (hj : ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1)
    (om oms : ι → MaximalUnramifiedExtension l) (hO : ∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1)
    (U0 : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) ℂ_[l]) (hU : Formalism.DworkPowerSeriesWeights.Integral U0) :
    Hur (ball ℂ_[l]) (thetaInZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms
      (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) * U0)) := by
  have ha0 : ∀ x : Bool × ι × Fin N0 × Fin N1, MvPowerSeries.constantCoeff (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) = 0 :=
    fun x => (xOfZ_spec σ hσ om oms hO x).2
  have ha1 : ∀ x : Bool × ι × Fin N0 × Fin N1, Hur (ball ℂ_[l]) (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) :=
    fun x => (xOfZ_spec σ hσ om oms hO x).1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hB0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hb0, map_zero]
  have hS0 := cc_sumE (ι := ι) (N0 := N0) (N1 := N1) _ hB0
  have hadd := hur_addC be0 hj
  have hS : Hur (ball ℂ_[l]) (MvPowerSeries.subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l (MaximalUnramifiedExtension l).subtype σ om oms)
      (sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) := by
    rw [subst_sumE ha0]
    refine hur_sum _ _ _ fun e _ => ?_
    obtain ⟨r, a, b⟩ := e
    rw [xOfZ_false, xOfZ_true]
    have h1 := uL_spec (d := d) hσ (hO r).2 a b
    have h2 := vL_spec (d := d) hσ (hO r).1 a b
    exact hur_pair _ _ h1.1 h1.2 h2.1 h2.2 be0 hadd
  unfold thetaInZ
  rw [MvPowerSeries.subst_mul hs]
  refine hur_mul _ ?_ (hur_subst _ ha0 ha1 (hur_of_int _ hU))
  have hN : MvPowerSeries.constantCoeff (-(sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) = 0 := by
    rw [map_neg, hS0, neg_zero]
  unfold Formalism.DworkPowerSeriesWeights.mvExp
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hN)) hs]
  have hneg : MvPowerSeries.subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l (MaximalUnramifiedExtension l).subtype σ om oms)
      (-(sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) =
      -MvPowerSeries.subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l (MaximalUnramifiedExtension l).subtype σ om oms)
        (sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0)) := by
    rw [← MvPowerSeries.coe_substAlgHom hs, map_neg]
  refine hur_subst _ (fun _ => ?_) (fun _ => ?_) (hur_exp _)
  · rw [cc_subst ha0, hN]
  · rw [hneg]
    exact hur_neg _ hS

theorem jets_of_scaled {τ : Type} [Finite τ] (ep : ℂ_[l]) (hep : ‖ep‖ = 1) (Th : MvPowerSeries τ ℂ_[l])
    (h : Hur (ball ℂ_[l]) (MvPowerSeries.subst (fun v : τ => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries τ ℂ_[l])) Th))
    (n : τ →₀ ℕ) : ‖(fc n : ℂ_[l]) * MvPowerSeries.coeff n Th‖ ≤ 1 := by
  have e : (fun v : τ => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries τ ℂ_[l])) =
      ((fun _ : τ => ep) • (MvPowerSeries.X : τ → MvPowerSeries τ ℂ_[l])) := by
    funext v
    simp [MvPowerSeries.smul_eq_C_mul]
  have hn := h n
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, mem_ball, norm_mul, norm_mul] at hn
  have hp : ‖n.prod fun _ m => ep ^ m‖ = 1 := by
    unfold Finsupp.prod
    rw [norm_prod]
    exact Finset.prod_eq_one fun x _ => by rw [norm_pow, hep, one_pow]
  rw [norm_mul]
  simpa [hp] using hn

end Main

theorem kvalGe_zero : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th 0 := by
  rintro Lc ep be hep ⟨σ, F, be0, om, oms, ζ, hD, rfl⟩ hB
  obtain ⟨U0, hU, hTh⟩ := GlobalTheory.T.exists_integral_orbit_series Lc ep σ F be0 om oms ζ hD hB
  obtain ⟨hσ, hF, h1, h2, hO, hT, -⟩ := hD
  have hb0 : MvPowerSeries.constantCoeff be0 = 0 := h1.1 0 (Or.inl rfl)
  have hH := hur_theta (d := Lc.d) (N0 := Lc.N0) (N1 := Lc.N1) σ hσ be0 hb0 (GlobalTheory.T.addCoord_exponent_integral_jets_unramified Lc.l σ F be0 hσ hF h1 h2) om oms hO.1 U0 hU
  rw [← hTh] at hH
  have hJ := jets_of_scaled ep hep Lc.Th hH
  intro I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine (ball ℂ_[Lc.l]).sum_mem fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc]
    exact (ball ℂ_[Lc.l]).mul_mem (intCast_mem _ _) (hJ _)
  · exact (ball ℂ_[Lc.l]).zero_mem

end GlobalTheory.KerZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZeroStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardOrbitSeries_valuationBound_zero : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th 0 := by
  first | exact @GlobalTheory.KerZero.kvalGe_zero | exact GlobalTheory.KerZero.kvalGe_zero | (intros; apply GlobalTheory.KerZero.kvalGe_zero <;> assumption)
end
