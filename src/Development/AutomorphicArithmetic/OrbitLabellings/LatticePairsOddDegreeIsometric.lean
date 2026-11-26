module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.Orthonormal
public import Development.AutomorphicArithmetic.OrbitLabellings.StdSeriesOrbitCoordinateChangeOfOddInert

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.IntegralMvExpSumLogSOfOddPeriod
open UpperTheory.G2 Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual phFF thetaS NormRel)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob at1 lgF)

namespace UpperTheory.G2.ConjugatePartitionShape

open MvPowerSeries Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

private theorem pos_add_mul {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) (a k : ℕ) :
    pos z (a + i * k) = pos z a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, ← h.add, ih, h.period]

private theorem pos_congr {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) {a b : ℕ}
    (hab : a ≡ b [MOD i]) : pos z a = pos z b := by
  rw [← Nat.mod_add_div a i, ← Nat.mod_add_div b i, pos_add_mul h, pos_add_mul h, hab]

private theorem pos_cast {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) {a b : ℕ}
    (hab : ((a : ℕ) : ZMod (2 * i)) = (b : ℕ)) : pos z a = pos z b := by
  apply pos_congr h
  rw [ZMod.natCast_eq_natCast_iff] at hab
  exact Nat.ModEq.of_mul_left 2 hab

private theorem iter_pred {Lt β : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) (b : β) (e : ℕ) :
    (fun y : Lt × β => (pos y.1 (2 * (i - 1)), y.2))^[e] (z, b) = (pos z (2 * (i - 1) * e), b) := by
  induction e with
  | zero => simp [h.zero]
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [h.add]
    congr 2

private theorem logS_eq_gLog {K Lt β : Type} [Field K] [DecidableEq Lt] [DecidableEq β] (l : ℕ) {i : ℕ} [NeZero i]
    {pos : Lt → ℕ → Lt} (h : IsPos i pos) (r : Lt) (b : β) (s : ZMod (2 * i)) :
    logS (K := K) l i pos (pos r s.val, b) =
      KernelCokernelKilling.gLog K l (fun s : ZMod (2 * i) => (pos r s.val, b)) s := by
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  have key : ∀ e : ℕ, pos r (s.val + 2 * (i - 1) * e) = pos r ((s - 2 * (e : ZMod (2 * i))).val) := by
    intro e
    apply pos_cast h
    have hi : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr (NeZero.ne i)
    push_cast [Nat.cast_sub hi, ZMod.natCast_zmod_val]
    have h2i : ((2 * i : ℕ) : ZMod (2 * i)) = 0 := ZMod.natCast_self _
    push_cast at h2i
    linear_combination (e : ZMod (2 * i)) * h2i
  ext n
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  simp only [logS, Formalism.DworkPowerSeriesWeights.genLog, KernelCokernelKilling.gLog]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [iter_pred h, h.add, key]

private theorem val_add_i {i : ℕ} [NeZero i] (s : ZMod (2 * i)) :
    ∃ k : ℕ, s.val + i = (s + (i : ZMod (2 * i))).val + 2 * i * k := by
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  have hi : 0 < i := Nat.pos_of_ne_zero (NeZero.ne i)
  refine ⟨(s.val + i) / (2 * i), ?_⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : i < 2 * i)]
  exact (Nat.mod_add_div _ _).symm

private theorem linOL_eq {K τ : Type} [NormedField K] {i : ℕ} [NeZero i] (hi : Odd i) (σ : K →+* K) {c : K}
    (hc : σ^[2 * i] c = c) (L : ZMod (2 * i) → MvPowerSeries τ K) (hL : ∀ s, L (s + (i : ZMod (2 * i))) = L s) :
    linOL σ c L = linEL σ (σ^[i] c) L := by
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  unfold linOL linEL
  refine Fintype.sum_equiv (Equiv.addRight (i : ZMod (2 * i))) _ _ fun s => ?_
  simp only [Equiv.coe_addRight]
  rw [hL s, ← Function.iterate_add_apply]
  obtain ⟨k, hk⟩ := val_add_i s
  obtain ⟨m, hm⟩ := hi
  have hs := ZMod.val_lt s
  have hk1 : k ≤ 1 := by
    by_contra hc'
    push_neg at hc'
    nlinarith
  have hit : σ^[(s + (i : ZMod (2 * i))).val + i] c = σ^[s.val] c := by
    interval_cases k
    · rw [show (s + (i : ZMod (2 * i))).val + i = s.val + 2 * i by omega, Function.iterate_add_apply, hc]
    · rw [show (s + (i : ZMod (2 * i))).val + i = s.val by omega]
  have hpar : s.val % 2 = 0 ↔ ¬ (s + (i : ZMod (2 * i))).val % 2 = 0 := by
    interval_cases k <;> omega
  by_cases h0 : s.val % 2 = 0
  · have h1 := hpar.mp h0
    simp [h0, h1]
  · have h1 : (s + (i : ZMod (2 * i))).val % 2 = 0 := by
      by_contra h1
      exact h0 (hpar.mpr h1)
    simp [h0, h1, hit]

private theorem diag (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i : ℕ) [NeZero i]
    (σ : K →+* K) (hU : UnrOK K l σ) (hi : Odd i) (F : MvPowerSeries (Fin 2) K) (hF : IsLawOfLog l F)
    (be0 : MvPowerSeries (Fin 2) K) (hF1 : F1 F be0) (hF2 : F2 l σ be0) (om : Fin i → K)
    (hOw : OwOK (2 * i) σ om (fun r => σ^[i] (om r))) (hTr : TrDual (2 * i) σ om (fun r => σ^[i] (om r)))
    (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ (2 * i) - 1)) (ph : PowerSeries K)
    (hph : Simeq (C (2 : K) * ph) (subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) be0))
    (τ : Type) [Finite τ] (L : ZMod (2 * i) → MvPowerSeries τ K) (hS : ShiftType l σ L)
    (hL : ∀ s, L (s + (i : ZMod (2 * i))) = L s) :
    ∃ x : Fin i → MvPowerSeries τ K, (∀ ρ, constantCoeff (x ρ) = 0) ∧ (∀ ρ, Integral (x ρ)) ∧
      (∀ ρ, PowerSeries.subst (x ρ) (lgF K l) = linEL σ (σ^[i] (om ρ)) L) ∧
      Simeq (∑ ρ, PowerSeries.subst (x ρ) ph)
        (C ((2 : K)⁻¹) * subst L (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)) := by
  have hlp : Nat.Prime l := hU.1
  have hl2 : 2 ≤ l := hlp.two_le
  have hd2 : 2 ≤ 2 * i := by have := NeZero.ne i; omega
  have hde : Even (2 * i) := even_two_mul i
  have hIP : ∀ ρ, IP l σ (linEL σ (σ^[i] (om ρ)) L) := fun ρ =>
    (shiftIP K l (2 * i) σ hU hde τ L hS _ (hOw.1 ρ).2 (hOw.2 ρ).2).1
  choose x hx0 hxI hxL using fun ρ => ipLemma K l σ hU τ _ (hIP ρ)
  refine ⟨x, hx0, hxI, hxL, ?_⟩
  obtain ⟨-, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ
  have hsubU := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit).2.2.2.2 τ
  have hM := meanSimeqL K l (2 * i) σ hU hd2 hde F hF be0 hF1 hF2 (Fin i) om (fun r => σ^[i] (om r))
    hOw hTr ζ hζ τ L hS
  rw [substTil K l (2 * i) σ hl2 be0 (Fin i) om _ τ L (fun s => (hS s).1)] at hM
  have ha : MvPowerSeries.HasSubst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have hterm : ∀ r : Fin i, Simeq (subst ![linEL σ (σ^[i] (om r)) L, linOL σ (om r) L] (addC l be0))
      (C (2 : K) * PowerSeries.subst (x r) ph) := by
    intro r
    rw [linOL_eq hi σ (hOw.2 r).1 L hL, ← hxL r, Pair.addC_log expSpec hl2 (hx0 r) (hx0 r) be0]
    have hb : MvPowerSeries.HasSubst (fun _ : Unit => x r) :=
      PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero (hx0 r))
    have h1 := hsubU (C (2 : K) * ph) _ (fun _ => x r) (fun _ => hx0 r) (fun _ => hxI r) hph
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply ha hb] at h1
    have e : (fun _ : Fin 2 => subst (fun _ : Unit => x r) (PowerSeries.X : PowerSeries K)) = ![x r, x r] := by
      funext j
      rw [PowerSeries.X, MvPowerSeries.subst_X hb]
      fin_cases j <;> rfl
    rw [e] at h1
    exact hsymm _ _ h1
  have hsum := B4.simeq_sum Finset.univ _ _ fun r _ => hterm r
  rw [← Finset.mul_sum] at hsum
  have h2 := htrans _ _ _ hM hsum
  have hl3 : 2 < l := hU.2.1
  have hnd : ¬ l ∣ 2 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hlam := Formalism.InvariantFactorPaths.G7.Top.lamModule K τ l σ hlp hU.2.2.1 hU.2.2.2.2 _ 2 hnd (B4.simeq_sub_zero h2)
  apply hsymm
  have key : C ((2 : K)⁻¹) * subst L (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)
      - ∑ ρ, PowerSeries.subst (x ρ) ph
      = C ((2 : ℕ) : K)⁻¹ * (subst L (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)
        - C (2 : K) * ∑ ρ, PowerSeries.subst (x ρ) ph) := by
    rw [mul_sub, ← mul_assoc, ← map_mul, Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  unfold Formalism.InvariantFactorPaths.G7.Simeq at hlam ⊢
  rw [sub_zero] at hlam
  rw [key]
  exact hlam

private theorem map_logS {K K' Lt β : Type} [Field K] [Field K'] [DecidableEq Lt] [DecidableEq β] (j : K →+* K') (l i : ℕ)
    (pos : Lt → ℕ → Lt) (v : Lt × β) : map j (logS (K := K) l i pos v) = logS (K := K') l i pos v := by
  ext n
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  simp only [logS, Formalism.DworkPowerSeriesWeights.genLog]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, apply_ite j]

private theorem cc_logS {K Lt β : Type} [Field K] [DecidableEq Lt] [DecidableEq β] {l : ℕ} (hl : 2 ≤ l) (i : ℕ)
    (pos : Lt → ℕ → Lt) (v : Lt × β) : constantCoeff (logS (K := K) l i pos v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
  simp only [logS, Formalism.DworkPowerSeriesWeights.genLog]
  simp only [map_zero, zero_add, Finset.sum_range_one, pow_zero, Function.iterate_zero, id_eq, ite_eq_right_iff]
  intro h0
  exact absurd h0.symm (Finsupp.single_ne_zero.mpr one_ne_zero)

end UpperTheory.G2.ConjugatePartitionShape

namespace UpperTheory.G2.ConjugatePartitionShape

open MvPowerSeries Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

private theorem diagJ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (hj : ∀ a, ‖j a‖ = ‖a‖) (l i : ℕ) [NeZero i]
    (σ : K0 →+* K0) (hU : UnrOK K0 l σ) (hi : Odd i) (F : MvPowerSeries (Fin 2) K0) (hF : IsLawOfLog l F)
    (be0 : MvPowerSeries (Fin 2) K0) (hF1 : F1 F be0) (hF2 : F2 l σ be0) (om : Fin i → K0)
    (hOw : OwOK (2 * i) σ om (fun r => σ^[i] (om r))) (hTr : TrDual (2 * i) σ om (fun r => σ^[i] (om r)))
    (ζ : K0) (hζ : IsPrimitiveRoot ζ (l ^ (2 * i) - 1)) (ph : PowerSeries K0)
    (hph : Simeq (C (2 : K0) * ph) (subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0))
    (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt) (hpos : IsPos i pos)
    (r : Lt) (b : β) :
    ∃ x : Fin i → MvPowerSeries (Lt × β) K, (∀ ρ, constantCoeff (x ρ) = 0) ∧ (∀ ρ, Integral (x ρ)) ∧
      (∀ ρ, PowerSeries.subst (x ρ) (lgF K l) =
        subst (logS (K := K) (β := β) l i pos) (linS j σ i pos (σ^[i] (om ρ)) r b)) ∧
      Simeq (∑ ρ, PowerSeries.subst (x ρ) (PowerSeries.map j ph))
        (C ((2 : K)⁻¹) * subst (fun s : ZMod (2 * i) => logS (K := K) l i pos (pos r s.val, b))
          (map j (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ))) := by
  have hlp : Nat.Prime l := hU.1
  have hl2 : 2 ≤ l := hlp.two_le
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  set L0 : ZMod (2 * i) → MvPowerSeries (Lt × β) K0 := fun s => logS (K := K0) l i pos (pos r s.val, b) with hL0
  have hS : ShiftType l σ L0 := by
    have e : L0 = fun s => KernelCokernelKilling.gLog K0 l (fun s : ZMod (2 * i) => (pos r s.val, b)) s :=
      funext fun s => logS_eq_gLog l hpos r b s
    rw [e]
    exact KernelCokernelKilling.shiftType_gLog hlp σ _
  have hLp : ∀ s, L0 (s + (i : ZMod (2 * i))) = L0 s := by
    intro s
    obtain ⟨k, hk⟩ := val_add_i s
    have e1 : (s.val + i) % i = s.val % i := Nat.add_mod_right _ _
    have e2 : ((s + (i : ZMod (2 * i))).val + 2 * i * k) % i = (s + (i : ZMod (2 * i))).val % i := by
      rw [show 2 * i * k = i * (2 * k) by ring, Nat.add_mul_mod_self_left]
    have hmod : (s + (i : ZMod (2 * i))).val ≡ s.val [MOD i] := by
      unfold Nat.ModEq
      rw [← e2, ← hk, e1]
    simp only [hL0, pos_congr hpos r hmod]
  obtain ⟨x, hx0, hxI, hxL, hsim⟩ :=
    diag K0 l i σ hU hi F hF be0 hF1 hF2 om hOw hTr ζ hζ ph hph (Lt × β) L0 hS hLp
  have hs : MvPowerSeries.HasSubst (logS (K := K) (β := β) l i pos) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logS hl2 i pos v)
  have hs0 : MvPowerSeries.HasSubst L0 :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => cc_logS hl2 i pos _)
  refine ⟨fun ρ => map j (x ρ), fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hx0, map_zero]
  · exact Formalism.DworkPowerSeriesWeights.Transfer.integral_map j hj (hxI ρ)
  · rw [← Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF j l,
      ← PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hx0 ρ)), hxL ρ]
    unfold linEL linS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Pair.subst_sum hs]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C,
        MvPowerSeries.subst_X hs]
      simp only [hL0, map_logS]
    · rw [map_zero, Pair.subst_zero' hs]
  · have hm := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K (Lt × β) j hj).1 _ _ hsim
    have e1 : map j (∑ ρ, PowerSeries.subst (x ρ) ph)
        = ∑ ρ, PowerSeries.subst (map j (x ρ)) (PowerSeries.map j ph) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun ρ _ =>
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hx0 ρ)) ph
    have e2 : map j (C ((2 : K0)⁻¹) * subst L0 (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ))
        = C ((2 : K)⁻¹) * subst (fun s : ZMod (2 * i) => logS (K := K) l i pos (pos r s.val, b))
          (map j (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)) := by
      rw [map_mul, MvPowerSeries.map_C, map_inv₀, map_ofNat, MvPowerSeries.map_subst hs0]
      congr 2
      funext s
      exact map_logS j l i pos (pos r s.val, b)
    rw [e1, e2] at hm
    exact hm

end UpperTheory.G2.ConjugatePartitionShape

open MvPowerSeries Formalism.L2.Th1.D UpperTheory.G2.ConjugatePartitionShape in
open Formalism.InvariantFactorPaths.G7 (Simeq) in
open Formalism.DworkPowerSeriesWeights (Integral mvExp) in
theorem UpperTheory.integral_mvExp_sum_logS_of_odd_period :
    ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)),
    (5 ≤ p ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) ∧
      UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsLawOfLog p F ∧ ∀ α : MaximalUnramifiedExtension p, ‖α‖ = 1 → σ (σ α) = α → NormRel p σ (phFF p g2 g3 s2 ε) α) →
     ∀ (i : ℕ) [NeZero i], Odd i → ∀ om : Fin i → MaximalUnramifiedExtension p,
    OwOK (2 * i) σ om (fun r => σ^[i] (om r)) → TrDual (2 * i) σ om (fun r => σ^[i] (om r)) →
    ∀ (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt), IsPos i pos →
    ∀ (R : Finset Lt) (Θ : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p]),
    Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (∑ e : ({r // r ∈ R} × Fin i) × β,
              at1 e (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p]) *
      (MvPowerSeries.subst (fun e : ({r // r ∈ R} × Fin i) × β => (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) Θ :
        MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) →
    ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (Lt × β) ℂ_[p]), ‖ep‖ = 1 →
    (MvPowerSeries.subst (fun v : Lt × β => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (Lt × β) ℂ_[p])) Th : MvPowerSeries (Lt × β) ℂ_[p]) =
      MvPowerSeries.subst (fun e : ({r // r ∈ R} × Fin i) × β => linS (MaximalUnramifiedExtension p).subtype σ i pos (σ^[i] (om e.1.2)) e.1.1.1 e.2) Θ →
    HasThetaProductForm p i pos Th := by
  intro p _ g2 g3 s2 ε σ F ⟨hp5, hg2, hg3, hε, hθ, hU, hF, hNR⟩ i _ hi om hOw hTr Lt β _ _ _ _ pos hpos R Θ hI ep Th hep hTh
  set j : ↥(MaximalUnramifiedExtension p) →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype with hjdef
  have hj : ∀ a, ‖j a‖ = ‖a‖ := FAux.norm_coe p
  have hl2 : 2 ≤ p := hU.1.two_le
  have hd2 : 2 ≤ 2 * i := by have := NeZero.ne i; omega
  have hde : Even (2 * i) := even_two_mul i
  obtain ⟨hF1, hF2, hph⟩ := FAux.ffs p first_level_on_curve g2 g3 ε hg2 hg3 hε hθ σ hU F hF s2 hNR
  have hgt : 1 < p ^ (2 * i) := Nat.one_lt_pow (by omega) (by omega)
  have hpos' : 0 < p ^ (2 * i) - 1 := by omega
  have hndvd : ¬ p ∣ p ^ (2 * i) - 1 := by
    intro hd
    have h1 : p ∣ p ^ (2 * i) := dvd_pow_self p (by omega)
    have h2 := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self (by omega)] at h2
    have := Nat.le_of_dvd one_pos h2
    omega
  obtain ⟨ζ0, hζ0⟩ := kurRoots p (p ^ (2 * i) - 1) hpos' hndvd
  set ph := phFF p g2 g3 s2 ε with hphdef
  set be0 := cob F ph with hbe0
  set bM := beMean (d := 2 * i) p σ be0 om (fun r => σ^[i] (om r)) ζ0 with hbM
  have hB := biextension_hypotheses_of_level_one (MaximalUnramifiedExtension p) p (2 * i) σ hU hd2 hde F hF be0 hF1 (Fin i) om _ hOw ζ0 hζ0
  have hB' := (Formalism.DworkPowerSeriesWeights.admissibleTransfer (MaximalUnramifiedExtension p) ℂ_[p] j hj p (2 * i) 0 0 ⊤ ζ0 bM).2.1 hB
  have hK : Subfield.map j ⊤ = MaximalUnramifiedExtension p := by
    rw [← RingHom.fieldRange_eq_map, hjdef, Subfield.fieldRange_subtype]
  rw [hK] at hB'
  choose x hx0 hxI hxL hxS using fun (r : {r // r ∈ R}) (b : β) =>
    diagJ (MaximalUnramifiedExtension p) ℂ_[p] j hj p i σ hU hi F hF be0 hF1 hF2 om hOw hTr ζ0 hζ0 ph hph Lt β pos hpos r.1 b
  refine ⟨MaximalUnramifiedExtension p, j ζ0, R, ep, fun _ => -1, fun _ => map j bM, kurUnram p,
    hζ0.map_of_injective j.injective, hep, fun _ _ => Or.inr rfl, fun _ _ => hB', ?_⟩
  set Λ : Lt × β → MvPowerSeries (Lt × β) ℂ_[p] := logS (K := ℂ_[p]) p i pos with hΛ
  have hΛs : MvPowerSeries.HasSubst Λ :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logS hl2 i pos v)
  set y : ({r // r ∈ R} × Fin i) × β → MvPowerSeries (Lt × β) ℂ_[p] := fun e => x e.1.1 e.2 e.1.2 with hy
  have hy0 : ∀ e, constantCoeff (y e) = 0 := fun e => hx0 _ _ _
  have hyI : ∀ e, Integral (y e) := fun e => hxI _ _ _
  have hys : MvPowerSeries.HasSubst y := MvPowerSeries.hasSubst_of_constantCoeff_zero hy0
  have hat : MvPowerSeries.HasSubst (fun e : ({r // r ∈ R} × Fin i) × β =>
      (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun e => Pair.constantCoeff_inVar_eq_zero e (Pair.cc_lgF hl2))
  have hlin : MvPowerSeries.HasSubst (fun e : ({r // r ∈ R} × Fin i) × β =>
      linS j σ i pos (σ^[i] (om e.1.2)) e.1.1.1 e.2) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun e => ?_)
    unfold linS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs
    · rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
    · exact map_zero _
  have hcx : MvPowerSeries.HasSubst (fun v : Lt × β => (C ep * X v : MvPowerSeries (Lt × β) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by simp)
  have step1 : subst (fun v => C ep * Λ v) Th = subst y (subst (fun e : ({r // r ∈ R} × Fin i) × β =>
      (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) Θ) := by
    have e1 : (fun v => C ep * Λ v) = fun v => subst Λ (C ep * X v : MvPowerSeries (Lt × β) ℂ_[p]) := by
      funext v
      rw [MvPowerSeries.subst_mul hΛs, MvPowerSeries.subst_C, MvPowerSeries.subst_X hΛs]
    rw [e1, ← MvPowerSeries.subst_comp_subst_apply hcx hΛs, hTh,
      MvPowerSeries.subst_comp_subst_apply hlin hΛs, MvPowerSeries.subst_comp_subst_apply hat hys]
    congr 1
    funext e
    rw [Pair.subst_single_var hys]
    exact (hxL _ _ _).symm
  have hph0 : PowerSeries.constantCoeff (PowerSeries.map j ph) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hphdef, FAux.cc_phFF hl2, map_zero]
  have hP0 : constantCoeff (∑ e : ({r // r ∈ R} × Fin i) × β,
      (at1 e (PowerSeries.map j ph) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => Pair.constantCoeff_inVar_eq_zero e hph0
  have hW := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' hy0 hyI hI
  rw [MvPowerSeries.subst_mul hys, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hys hP0, Pair.subst_sum hys] at hW
  simp only [Pair.subst_single_var hys] at hW
  set Q := ∑ e : ({r // r ∈ R} × Fin i) × β, PowerSeries.subst (y e) (PowerSeries.map j ph) with hQdef
  set Q2 := ∑ r : {r // r ∈ R}, ∑ b : β, C ((2 : ℂ_[p])⁻¹) *
    subst (fun s : ZMod (2 * i) => Λ (pos r.1 s.val, b)) (map j bM) with hQ2def
  have hQ : Simeq Q Q2 := by
    have eQ : Q = ∑ r : {r // r ∈ R}, ∑ b : β, ∑ ρ : Fin i,
        PowerSeries.subst (x r b ρ) (PowerSeries.map j ph) := by
      rw [hQdef, Fintype.sum_prod_type, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    rw [eQ]
    exact B4.simeq_sum _ _ _ fun r _ => B4.simeq_sum _ _ _ fun b _ => hxS r b
  set G := subst (fun e : ({r // r ∈ R} × Fin i) × β =>
      (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) Θ with hG
  have hbe0c : constantCoeff (map j bM) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, Formalism.DworkPowerSeriesWeights.Transfer.cc_of_noLow hB.2.2.1, map_zero]
  have hXs : ∀ (r : Lt) (b : β), MvPowerSeries.HasSubst
      (fun s : ZMod (2 * i) => (X (pos r s.val, b) : MvPowerSeries (Lt × β) ℂ_[p])) :=
    fun r b => MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => MvPowerSeries.constantCoeff_X _)
  have hbeS0 : constantCoeff (beS i pos R (fun _ => (-1 : ℂ_[p])) (fun _ => map j bM) :
      MvPowerSeries (Lt × β) ℂ_[p]) = 0 := by
    unfold beS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum,
      Finset.sum_eq_zero (fun b _ => MvPowerSeries.constantCoeff_subst_eq_zero (hXs r b)
        (fun s => MvPowerSeries.constantCoeff_X _) hbe0c), mul_zero]
  have hsub : subst Λ (beS i pos R (fun _ => (-1 : ℂ_[p])) (fun _ => map j bM)) = -Q2 := by
    unfold beS
    rw [Pair.subst_sum hΛs, hQ2def, ← Finset.sum_coe_sort R, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MvPowerSeries.subst_smul hΛs, Pair.subst_sum hΛs, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MvPowerSeries.subst_comp_subst_apply (hXs r.1 b) hΛs]
    simp only [MvPowerSeries.subst_X hΛs]
    rw [show ((-1 : ℂ_[p]) / 2) = -(2⁻¹) by ring, map_neg, neg_mul]
  have hQc : constantCoeff Q = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQdef, map_sum]
    exact Finset.sum_eq_zero fun e _ => Pair.cc_ps (hy0 e) hph0
  have hQ2c : constantCoeff Q2 = 0 := by
    have := hQ.1
    rw [map_sub, hQc, zero_sub, neg_eq_zero] at this
    exact this
  obtain ⟨-, hsymm, -, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] (Lt × β)
  have hQ' := hsymm _ _ hQ
  refine ⟨mvExp Q * subst y G * mvExp (Q2 - Q), Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hW hQ'.2, ?_⟩
  rw [step1, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hΛs hbeS0, hsub]
  have h1 : mvExp Q * mvExp (Q2 - Q) * mvExp (-Q2) = (1 : MvPowerSeries (Lt × β) ℂ_[p]) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add hQc (by rw [map_sub, hQc, hQ2c, sub_zero]),
      ← Formalism.InvariantFactorPaths.G7.mvExp_add (by rw [map_add (f := _), map_sub, hQc, hQ2c]; simp) (by rw [map_neg, hQ2c, neg_zero])]
    rw [show Q + (Q2 - Q) + -Q2 = 0 by ring, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
  calc subst y G = subst y G * (mvExp Q * mvExp (Q2 - Q) * mvExp (-Q2)) := by rw [h1, mul_one]
    _ = _ := by ring
end

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.ExistsUnitQuotientOfNormOneUnramifiedUltrametric
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual)
open Formalism.InvariantFactorPaths.G7 (UnrOK)

namespace UpperTheory.NormSurjectiveFixedIntegers

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private lemma nadd {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

private lemma naddlt {a b : K} {r : ℝ} (ha : ‖a‖ < r) (hb : ‖b‖ < r) : ‖a + b‖ < r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)

private lemma norm_one_of_close {a b : K} (hb : ‖b‖ = 1) (h : ‖a - b‖ < 1) : ‖a‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b)
    (by rw [hb]; exact h.ne)
  rw [sub_add_cancel, hb, max_eq_right h.le] at this
  exact this

private lemma sqrt_near [CompleteSpace K] (h2 : ‖(2 : K)‖ = 1) (w : K) (hw : ‖w‖ < 1) :
    ∃ t : K, ‖t‖ < 1 ∧ t ^ 2 + 2 * t = w := by
  have h20 : (2 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact zero_ne_one h2
  let f : K → K := fun t => (w - t ^ 2) / 2
  let s : Set K := Metric.closedBall 0 ‖w‖
  have hs : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hmem : ∀ t, t ∈ s ↔ ‖t‖ ≤ ‖w‖ := fun t => mem_closedBall_zero_iff
  have hmaps : Set.MapsTo f s s := by
    intro t ht
    rw [hmem] at ht ⊢
    show ‖(w - t ^ 2) / 2‖ ≤ _
    rw [norm_div, h2, div_one, sub_eq_add_neg]
    refine nadd le_rfl ?_
    rw [norm_neg, norm_pow]
    nlinarith [norm_nonneg t]
  have hc : ContractingWith ‖w‖₊ (hmaps.restrict f s s) := by
    refine ⟨by exact_mod_cast hw, LipschitzWith.of_dist_le_mul ?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hmem] at ha hb
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    show ‖(w - a ^ 2) / 2 - (w - b ^ 2) / 2‖ ≤ ‖w‖ * ‖a - b‖
    have : (w - a ^ 2) / 2 - (w - b ^ 2) / 2 = -((a + b) * (a - b)) / 2 := by ring
    rw [this, norm_div, h2, div_one, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_right (nadd ha hb) (norm_nonneg _)
  obtain ⟨t, ht, hfix, -⟩ := ContractingWith.exists_fixedPoint' hs hmaps hc
    (x := 0) ((hmem 0).2 (by simp)) (edist_ne_top _ _)
  refine ⟨t, ((hmem t).1 ht).trans_lt hw, ?_⟩
  have : (w - t ^ 2) / 2 = t := hfix
  field_simp at this
  linear_combination -this

variable {l : ℕ} {σ : K →+* K}

private lemma linv_lt (hU : UnrOK K l σ) : (l : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hU.1.one_lt)

private lemma sig_close (hU : UnrOK K l σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a - a ^ l‖ < 1 :=
  (hU.2.2.2.2 a ha).trans_lt (linv_lt hU)

private lemma sig_le (hU : UnrOK K l σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have := nadd (sig_close hU ha).le (show ‖a ^ l‖ ≤ 1 by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
  rwa [sub_add_cancel] at this

private lemma sig_lt (hU : UnrOK K l σ) {a : K} (ha : ‖a‖ < 1) : ‖σ a‖ < 1 := by
  have := naddlt (sig_close hU ha.le)
    (show ‖a ^ l‖ < 1 by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) ha hU.1.ne_zero)
  rwa [sub_add_cancel] at this

private lemma sig_iter_le (hU : UnrOK K l σ) (n : ℕ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ^[n] a‖ ≤ 1 := by
  induction n with
  | zero => exact ha
  | succ n ih => rw [Function.iterate_succ_apply']; exact sig_le hU ih

private lemma norm_two (hU : UnrOK K l σ) : ‖(2 : K)‖ = 1 := by
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := K) hU.1
    (by rw [hU.2.2.1]; exact linv_lt hU) (m := 2)
    (fun h => absurd (Nat.le_of_dvd two_pos h) (not_le.2 hU.2.1))
  exact_mod_cast this

private lemma norm_onto [CompleteSpace K] [CharZero K] (hU : UnrOK K l σ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) (u : K) (hu : ‖u‖ = 1) (hs : σ u = u) :
    ∃ a : K, ‖a‖ ≤ 1 ∧ σ (σ a) = a ∧ a * σ a = u := by
  have hl := hU.2.1
  have hσζ : σ ζ = ζ ^ l := Formalism.L2.Th1.D.teichSigma K l 2 σ hU (by omega) ζ hζ.pow_eq_one
  have hfac : l ^ 2 - 1 = (l + 1) * (l - 1) := by
    have := Nat.sq_sub_sq l 1
    simpa using this
  have hN0 : 0 < l ^ 2 - 1 := by rw [hfac]; exact Nat.mul_pos (by omega) (by omega)
  have nζ : ‖ζ‖ = 1 := Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow hN0.ne' hζ.pow_eq_one
  have hη : IsPrimitiveRoot (ζ ^ (l + 1)) (l - 1) := hζ.pow hN0 hfac
  have h1 : ‖u ^ (l - 1) - 1‖ < 1 := by
    have h := sig_close hU hu.le
    have e : σ u - u ^ l = -(u * (u ^ (l - 1) - 1)) := by
      rw [hs, mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega)]; ring
    rwa [e, norm_neg, norm_mul, hu, one_mul] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖u - (ζ ^ (l + 1)) ^ k‖ < 1 := by
    by_contra hcon
    push Not at hcon
    have hp := congrArg (Polynomial.eval u) (X_pow_sub_C_eq_prod hη (α := 1) (a := 1) (by omega) (one_pow _))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod, mul_one] at hp
    rw [hp, norm_prod] at h1
    exact absurd h1 (not_lt.2 (Finset.prod_induction _ (fun y : ℝ => 1 ≤ y) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun j _ => hcon j))
  set x : K := ζ ^ k with hx
  have hxx : x * σ x = (ζ ^ (l + 1)) ^ k := by
    rw [hx, map_pow, hσζ, ← mul_pow, ← pow_succ']
  have hx2 : σ (σ x) = x := by
    rw [hx, map_pow, map_pow, hσζ, map_pow, hσζ, ← pow_mul ζ l l, ← sq,
      show l ^ 2 = (l ^ 2 - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have nx : ‖x‖ = 1 := by rw [hx, norm_pow, nζ, one_pow]
  rw [← hxx] at hk
  set n : K := x * σ x with hn
  have nn : ‖n‖ = 1 := by rw [hxx, norm_pow, norm_pow, nζ, one_pow, one_pow]
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, norm_zero] at nn
    exact zero_ne_one nn
  have hsn : σ n = n := by rw [hn, map_mul, hx2, mul_comm]
  obtain ⟨t, ht, htw⟩ := sqrt_near (norm_two hU) ((u - n) / n) (by rwa [norm_div, nn, div_one])
  have htw' : σ t ^ 2 + 2 * σ t = (u - n) / n := by
    have := congrArg σ htw
    rwa [map_add, map_pow, map_mul, map_ofNat, map_div₀, map_sub, hs, hsn] at this
  have hst : σ t = t := by
    have e : (σ t - t) * (σ t + t + 2) = 0 := by linear_combination htw' - htw
    have h3 : ‖σ t + t + 2‖ = 1 := norm_one_of_close (norm_two hU)
      (by rw [add_sub_cancel_right]; exact naddlt (sig_lt hU ht) ht)
    rcases mul_eq_zero.1 e with h | h
    · exact sub_eq_zero.1 h
    · rw [h, norm_zero] at h3
      exact absurd h3 zero_ne_one
  refine ⟨x * (1 + t), ?_, ?_, ?_⟩
  · rw [norm_mul, nx, one_mul]
    exact nadd norm_one.le ht.le
  · simp only [map_mul, map_add (f := _), map_one, hst, hx2]
  · simp only [map_mul, map_add (f := _), map_one, hst]
    have : (t ^ 2 + 2 * t) * n = u - n := by rw [htw]; field_simp
    linear_combination this + (1 + t) ^ 2 * hn

private def intFix (hU : UnrOK K l σ) : Subring K where
  carrier := {x | ‖x‖ ≤ 1 ∧ σ (σ x) = x}
  mul_mem' := fun {a b} ha hb => ⟨by
    rw [norm_mul]; exact mul_le_one₀ ha.1 (norm_nonneg _) hb.1, by
    rw [map_mul, map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨norm_one.le, by rw [map_one, map_one]⟩
  add_mem' := fun {a b} ha hb => ⟨nadd ha.1 hb.1, by rw [map_add (f := _), map_add (f := _), ha.2, hb.2]⟩
  zero_mem' := ⟨by simp, by rw [map_zero, map_zero]⟩
  neg_mem' := fun {a} ha => ⟨by rw [norm_neg]; exact ha.1, by rw [map_neg, map_neg, ha.2]⟩

private lemma unit_of_norm (hU : UnrOK K l σ) (a : intFix hU) (ha : ‖(a : K)‖ = 1) : IsUnit a := by
  have h0 : (a : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact zero_ne_one ha
  refine IsUnit.of_mul_eq_one ⟨(a : K)⁻¹, by rw [norm_inv, ha, inv_one], by
    rw [map_inv₀, map_inv₀, a.2.2]⟩ (Subtype.ext ?_)
  exact mul_inv_cancel₀ h0

private lemma norm_of_unit (hU : UnrOK K l σ) (a : intFix hU) (ha : IsUnit a) : ‖(a : K)‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h : ‖(a : K)‖ * ‖(b : K)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, hb, Subring.coe_one, norm_one]
  refine le_antisymm a.2.1 ?_
  nlinarith [b.2.1, norm_nonneg (a : K)]

private lemma congr_one [CompleteSpace K] [CharZero K] (hU : UnrOK K l σ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) {n : Type} [Fintype n] [DecidableEq n]
    (H G : Matrix n n K) (hH : ∀ i j, ‖H i j‖ ≤ 1 ∧ σ (σ (H i j)) = H i j)
    (hG : ∀ i j, ‖G i j‖ ≤ 1 ∧ σ (σ (G i j)) = G i j) (hh : ∀ i j, σ (H j i) = H i j)
    (hHG : H * G = 1) :
    ∃ P : Matrix n n K, (∀ i j, ‖P i j‖ ≤ 1 ∧ σ (σ (P i j)) = P i j) ∧
      ∀ r r', ∑ k, (∑ j, P r j * H j k) * σ (P r' k) = if r = r' then 1 else 0 := by
  letI : StarRing (intFix hU) :=
    { star := fun a => ⟨σ a, sig_le hU a.2.1, by rw [a.2.2]⟩
      star_involutive := fun a => Subtype.ext a.2.2
      star_mul := fun a b => Subtype.ext (by
        show σ ((a : K) * b) = σ b * σ a
        rw [map_mul, mul_comm])
      star_add := fun a b => Subtype.ext (map_add σ (a : K) b) }
  have hst : ∀ a : intFix hU, ((star a : intFix hU) : K) = σ a := fun a => rfl
  haveI : IsLocalRing (intFix hU) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases a.2.1.lt_or_eq with h | h
    · refine Or.inr (unit_of_norm hU _ (norm_one_of_close norm_one ?_))
      simpa using h
    · exact Or.inl (unit_of_norm hU _ h)
  have hD : KStar.Cstarloc.UnramDatum (intFix hU) := by
    constructor
    · refine ⟨⟨(2 : K)⁻¹, by rw [norm_inv, norm_two hU, inv_one], by simp only [map_inv₀, map_ofNat]⟩,
        Subtype.ext ?_⟩
      show (2 : K)⁻¹ + σ (2 : K)⁻¹ = 1
      rw [map_inv₀, map_ofNat]
      norm_num
    · intro u hu hs
      obtain ⟨a, h1, h2, h3⟩ := norm_onto hU ζ hζ u (norm_of_unit hU u hu)
        (congrArg Subtype.val hs)
      exact ⟨⟨a, h1, h2⟩, Subtype.ext h3⟩
  let H' : Matrix n n (intFix hU) := Matrix.of fun i j => ⟨H i j, hH i j⟩
  let G' : Matrix n n (intFix hU) := Matrix.of fun i j => ⟨G i j, hG i j⟩
  have hHG' : H' * G' = 1 := by
    ext i j
    have := congrFun (congrFun hHG i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, AddSubmonoidClass.coe_finsetSum]
    refine this.trans ?_
    split_ifs <;> rfl
  obtain ⟨P, -, hP⟩ := KStar.Cstarloc.exists_congr_one hD H'
    (by ext i j; exact hh i j) (Matrix.isUnit_det_of_right_inverse hHG')
  refine ⟨Matrix.of fun i j => (P i j : K), fun i j => (P i j).2, fun r r' => ?_⟩
  have := congrArg (intFix hU).subtype (congrFun (congrFun hP r) r')
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul, Matrix.conjTranspose_apply,
    Subring.coe_subtype, hst] at this
  refine this.trans ?_
  split_ifs <;> rfl

private def tr (σ : K →+* K) (i : ℕ) (x : K) : K := ∑ k ∈ Finset.range i, (σ ^ (2 * k)) x

omit [IsUltrametricDist K] in
private lemma pp (a b : ℕ) (x : K) : (σ ^ a) ((σ ^ b) x) = (σ ^ (a + b)) x := by
  rw [pow_add]; rfl

omit [IsUltrametricDist K] in
private lemma tr_shift (i : ℕ) (x : K) (hx : (σ ^ (2 * i)) x = x) : tr σ i ((σ ^ 2) x) = tr σ i x := by
  have h1 := Finset.sum_range_succ (fun k => (σ ^ (2 * k)) x) i
  have h2 := Finset.sum_range_succ' (fun k => (σ ^ (2 * k)) x) i
  simp only [mul_zero, pow_zero, RingHom.coe_one, id] at h2
  rw [h1, hx] at h2
  unfold tr
  simp only [pp]
  exact (add_right_cancel h2).symm

omit [IsUltrametricDist K] in
private lemma tr_map (i m : ℕ) (x : K) : (σ ^ m) (tr σ i x) = tr σ i ((σ ^ m) x) := by
  unfold tr
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, pp, add_comm]

omit [IsUltrametricDist K] in
private lemma tr_shift' (i : ℕ) (x : K) (hx : (σ ^ (2 * i)) x = x) (j : ℕ) :
    tr σ i ((σ ^ (2 * j)) x) = tr σ i x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [mul_add, add_comm, mul_one, ← pp, tr_shift, ih]
    rw [pp, add_comm, ← pp, hx]

omit [IsUltrametricDist K] in
private lemma fix_even {c : K} (hc : σ (σ c) = c) (k : ℕ) : (σ ^ (2 * k)) c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mul_add, ← pp]
    exact (congrArg _ hc).trans ih

omit [IsUltrametricDist K] in
private lemma tr_eq (i : ℕ) [NeZero i] (x : K) :
    (∑ s : ZMod (2 * i), if s.val % 2 = 0 then σ^[s.val] x else 0) = tr σ i x := by
  rw [Formalism.L2.Th1.D.TraceDualSums.sum_zmod (2 * i) (fun k => if k % 2 = 0 then σ^[k] x else 0),
    Formalism.L2.Th1.D.TraceDualSums.sum_range_even i (fun k => σ^[k] x)]
  simp only [tr, RingHom.coe_pow]

private lemma tr_mem (hU : UnrOK K l σ) (i : ℕ) (x : K) (hn : ‖x‖ ≤ 1)
    (hx : (σ ^ (2 * i)) x = x) : ‖tr σ i x‖ ≤ 1 ∧ σ (σ (tr σ i x)) = tr σ i x := by
  refine ⟨IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_, ?_⟩
  · rw [RingHom.coe_pow]; exact sig_iter_le hU _ hn
  · show (σ ^ 2) (tr σ i x) = _
    rw [tr_map, tr_shift i x hx]

private lemma main [CompleteSpace K] [CharZero K] (hU : UnrOK K l σ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) (i : ℕ) [NeZero i] (hi : Odd i) (om oms : Fin i → K)
    (h1 : OwOK (2 * i) σ om oms) (h2 : TrDual (2 * i) σ om oms) :
    ∃ om : Fin i → K, OwOK (2 * i) σ om (fun r => σ^[i] (om r)) ∧
      TrDual (2 * i) σ om (fun r => σ^[i] (om r)) := by
  obtain ⟨hn, hf⟩ := h1
  have hd := h2.2
  simp only [tr_eq] at hd
  simp only [← RingHom.coe_pow] at hf
  obtain ⟨j, hj⟩ := hi
  have hle : ∀ {a : K}, ‖a‖ ≤ 1 → ‖(σ ^ i) a‖ ≤ 1 := fun ha => by
    rw [RingHom.coe_pow]; exact sig_iter_le hU _ ha
  have hfi : ∀ {a : K}, (σ ^ (2 * i)) a = a → (σ ^ (2 * i)) ((σ ^ i) a) = (σ ^ i) a := fun ha => by
    rw [pp, add_comm, ← pp, ha]
  have hmul : ∀ {a b : K}, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun ha hb => by
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  let V : Matrix (Fin i) (Fin i) K := Matrix.of fun k r => (σ ^ (2 * k.val)) (om r)
  let Q : Matrix (Fin i) (Fin i) K := Matrix.of fun r k => (σ ^ (2 * k.val)) (oms r)
  have hQV : Q * V = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := hd r' r
    rw [tr, Finset.sum_range] at this
    simp only [map_mul] at this
    simp only [V, Q, Matrix.of_apply, mul_comm ((σ ^ _) (oms r)), this, eq_comm]
  have hVQ : V * Q = 1 := mul_eq_one_comm.1 hQV
  let H : Matrix (Fin i) (Fin i) K := Matrix.of fun r r' => tr σ i (om r * (σ ^ i) (om r'))
  let G : Matrix (Fin i) (Fin i) K := Matrix.of fun r r' => tr σ i ((σ ^ i) (oms r) * oms r')
  have eH : H = V.transpose * V.map (σ ^ i) := by
    ext r r'
    simp only [H, V, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply,
      tr, Finset.sum_range, map_mul, pp, add_comm]
  have eG : G = Q.map (σ ^ i) * Q.transpose := by
    ext r r'
    simp only [G, Q, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply,
      tr, Finset.sum_range, map_mul, pp, add_comm]
  have hHG : H * G = 1 := by
    rw [eH, eG, Matrix.mul_assoc, ← Matrix.mul_assoc (V.map _), ← Matrix.map_mul, hVQ,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.transpose_mul, hQV,
      Matrix.transpose_one]
  have hh : ∀ r r', σ (H r' r) = H r r' := by
    intro r r'
    show (σ ^ 1) (tr σ i (om r' * (σ ^ i) (om r))) = tr σ i (om r * (σ ^ i) (om r'))
    rw [tr_map, ← tr_shift' i _ _ j]
    · rw [map_mul, map_mul, pp, pp, pp, ← hj, show i + i = 2 * i by ring, (hf r).1, mul_comm]
    · rw [pp, add_comm, ← pp, map_mul (σ ^ (2 * i)), (hf r').1, hfi (hf r).1]
  obtain ⟨P, hP, hPH⟩ := congr_one hU ζ hζ H G
    (fun r r' => tr_mem hU i _ (hmul (hn r).1 (hle (hn r').1))
      (by rw [map_mul, (hf r).1, hfi (hf r').1]))
    (fun r r' => tr_mem hU i _ (hmul (hle (hn r).2) (hn r').2)
      (by rw [map_mul, (hf r').2, hfi (hf r).2])) hh hHG
  have n1 : ∀ r, ‖∑ a, P r a * om a‖ ≤ 1 := fun r =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ =>
      hmul (hP r a).1 (hn a).1
  have f1 : ∀ r, (σ ^ (2 * i)) (∑ a, P r a * om a) = ∑ a, P r a * om a := fun r => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, fix_even (hP _ _).2, (hf _).1]
  have hPi : ∀ r a, (σ ^ i) (P r a) = σ (P r a) := fun r a => by
    rw [hj, add_comm, ← pp, fix_even (hP _ _).2, pow_one]
  have hPs : ∀ r a k, (σ ^ (2 * k)) (σ (P r a)) = σ (P r a) := fun r a k =>
    fix_even (by rw [(hP r a).2]) k
  refine ⟨fun r => ∑ a, P r a * om a, ⟨fun r => ⟨n1 r, sig_iter_le hU _ (n1 r)⟩, fun r => ?_⟩,
    by rw [Fintype.card_fin], fun r r' => ?_⟩
  · simp only [← RingHom.coe_pow]
    exact ⟨f1 r, hfi (f1 r)⟩
  · rw [tr_eq, ← hPH r r', ← RingHom.coe_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, Matrix.of_apply, tr, map_sum, map_mul, hPi, hPs, fix_even (hP _ _).2,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    ring

private lemma not_dvd {l d : ℕ} (hp : l.Prime) (hd : d ≠ 0) : 0 < l ^ d - 1 ∧ ¬ l ∣ l ^ d - 1 := by
  have h0 : 1 < l ^ d := Nat.one_lt_pow hd hp.one_lt
  refine ⟨by omega, fun h => ?_⟩
  have h2 := Nat.dvd_sub (dvd_pow_self l hd) h
  rw [Nat.sub_sub_self h0.le] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

end UpperTheory.NormSurjectiveFixedIntegers

theorem UpperTheory.exists_unit_quotient_of_normOne_unramified_ultrametric :
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → ∀ (i : ℕ) [NeZero i], Odd i →
    ∃ om : Fin i → MaximalUnramifiedExtension l, OwOK (2 * i) σ om (fun r => σ^[i] (om r)) ∧ TrDual (2 * i) σ om (fun r => σ^[i] (om r)) := by
  intro l _ _ σ hU i _ hi
  haveI : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have a1 := UpperTheory.NormSurjectiveFixedIntegers.not_dvd (d := 2) hU.1 two_ne_zero
  have a2 := UpperTheory.NormSurjectiveFixedIntegers.not_dvd (d := 2 * i) hU.1 (NeZero.ne _)
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots l _ a1.1 a1.2
  obtain ⟨ξ, hξ⟩ := Formalism.L2.Th1.D.kurRoots l _ a2.1 a2.2
  have h := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension l) l (2 * i) σ hU (even_two_mul i) ξ hξ
  rw [show 2 * i / 2 = i by omega] at h
  obtain ⟨om, oms, h1, h2⟩ := h
  exact UpperTheory.NormSurjectiveFixedIntegers.main hU ζ hζ i hi om oms h1 h2
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd UpperTheory.G2 Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace UpperTheory.LinearSubstitutionRepresentatives

private lemma exists_reps {Lt : Type} [Fintype Lt] {i : ℕ} [NeZero i] {pos : Lt → ℕ → Lt} (hp : IsPos i pos) :
    ∃ R : Finset Lt, ∀ z, ∃! r, r ∈ R ∧ ∃ e : ℕ, pos r e = z := by
  have hmul : ∀ z k, pos z (i * k) = z := fun z k => by
    induction k with
    | zero => rw [mul_zero, hp.zero]
    | succ k ih => rw [mul_add, mul_one, ← hp.add, ih, hp.period]
  let S : Setoid Lt :=
    { r := fun a b => ∃ e : ℕ, pos a e = b
      iseqv :=
        { refl := fun a => ⟨0, hp.zero a⟩
          symm := by
            rintro a _ ⟨e, rfl⟩
            obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne i)
            refine ⟨j * e, ?_⟩
            rw [hp.add, show e + j * e = i * e by rw [hj, Nat.succ_mul, add_comm], hmul]
          trans := by
            rintro a _ _ ⟨e, rfl⟩ ⟨f, rfl⟩
            exact ⟨e + f, (hp.add a e f).symm⟩ } }
  refine ⟨Finset.univ.image fun z => (Quotient.mk S z).out, fun z => ⟨(Quotient.mk S z).out,
    ⟨Finset.mem_image.2 ⟨z, Finset.mem_univ _, rfl⟩, Quotient.mk_out (s := S) z⟩, ?_⟩⟩
  rintro r ⟨hr, hz⟩
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hr
  have h : Quotient.mk S (Quotient.mk S w).out = Quotient.mk S z := Quotient.sound hz
  rw [Quotient.out_eq] at h
  rw [h]

private lemma subst_lin_comp {K n m τ : Type} [Field K] [Fintype n] [Fintype m] (γ : n → m → K)
    (a : m → MvPowerSeries τ K) (ha : ∀ e, MvPowerSeries.constantCoeff (a e) = 0) (Θ : MvPowerSeries n K) :
    (MvPowerSeries.subst (fun k => (∑ e, MvPowerSeries.C (γ k e) * a e : MvPowerSeries τ K)) Θ : MvPowerSeries τ K) =
      MvPowerSeries.subst a (MvPowerSeries.subst
        (fun k => (∑ e, MvPowerSeries.C (γ k e) * MvPowerSeries.X e : MvPowerSeries m K)) Θ : MvPowerSeries m K) := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs]
  congr 1
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs, MvPowerSeries.subst_C]

private lemma cc_linS {K K0 Lt β : Type} [Field K] [Field K0] (j : K0 →+* K) (σ : K0 →+* K0) (i : ℕ) [NeZero i]
    (pos : Lt → ℕ → Lt) (c : K0) (r : Lt) (b : β) : MvPowerSeries.constantCoeff (linS j σ i pos c r b) = 0 := by
  unfold linS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp

end UpperTheory.LinearSubstitutionRepresentatives

open UpperTheory.LinearSubstitutionRepresentatives in
theorem UpperTheory.lattice_pairs_odd_degree_isometric :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → ∀ [NeZero (nP D p)], Odd (nP D p) →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
    admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' →
    ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → HasThetaProductForm p (nP D p) (posPl D p) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC _ hi N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  have hσ : UnrOK (MaximalUnramifiedExtension p) p σ := hcd.2.2.2.2.2.1
  have hp : IsPos (nP D p) (posPl D p) := ⟨posPl_zero D p, posPl_add D p, posPl_period D p⟩
  obtain ⟨om, hOw, hTr⟩ := UpperTheory.exists_unit_quotient_of_normOne_unramified_ultrametric p h5 σ hσ (nP D p) hi
  obtain ⟨R, hR⟩ := exists_reps hp
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := UpperTheory.stdSeries_orbit_coordinate_change_of_odd_inert D p lam σ hσ h5 hC hi om hOw hTr R hR N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := GlobalTheory.T.subst_unitary_logarithmic_coordinates p g2 g3 s2 ε σ F hcd (Fin r) (({z // z ∈ R} × Fin (nP D p)) × Fin N × Fin N') γ hγ1
    (by convert hγ2) _ (hInt G hG)
  refine UpperTheory.integral_mvExp_sum_logS_of_odd_period p g2 g3 s2 ε σ F hcd (nP D p) hi om hOw hTr _ _ (posPl D p) hp R _ hU c _ hc ?_
  exact (hγ3 c G).trans (subst_lin_comp (fun k e => (γ k e : ℂ_[p])) _ (fun e => cc_linS _ _ _ _ _ _ _) _)
