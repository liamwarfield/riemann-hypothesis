module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LazardBinomialNormUltrametric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLe
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_add_pow_sub_pow_le (c e : K) {r : ℝ} (hc : ‖c‖ ≤ 1) (hce : ‖c + e‖ ≤ 1) (he : ‖e‖ ≤ r)
    (n : ℕ) : ‖(c + e) ^ n - c ^ n‖ ≤ r := by
  rw [← Commute.geom_sum₂_mul (Commute.all _ _), add_sub_cancel_left, norm_mul]
  have hs : ‖∑ k ∈ Finset.range n, (c + e) ^ k * c ^ (n - 1 - k)‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hce) (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
  calc _ ≤ 1 * r := mul_le_mul hs he (norm_nonneg _) zero_le_one
    _ = r := one_mul r

theorem isFrobLift_pow (l : ℕ) (σ : K →+* K) (hU : Unr K l σ) (i : ℕ) :
    Formalism.G.IsFrobLift l (l ^ i) (σ ^ i) ∧ ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := by
  obtain ⟨_, _, hl1, hmax, hiso, hfr⟩ := hU
  induction i with
  | zero => exact ⟨fun a _ => by simp, fun x => by simp⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun a ha => ?_, fun x => ?_⟩
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
      set b := (σ ^ i) a
      have hb : ‖b‖ ≤ 1 := (ih2 a).le.trans ha
      have h1 : ‖σ b - b ^ l‖ ≤ ‖(l : K)‖ := hmax _ (hfr b hb)
      have hc : ‖a ^ l ^ i‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
      have h2 : ‖b ^ l - (a ^ l ^ i) ^ l‖ ≤ ‖(l : K)‖ := by
        have := norm_add_pow_sub_pow_le (a ^ l ^ i) (b - a ^ l ^ i) hc (by simpa using hb) (ih1 a ha) l
        simpa using this
      have : σ b - a ^ l ^ (i + 1) = (σ b - b ^ l) + (b ^ l - (a ^ l ^ i) ^ l) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hiso, ih2]

theorem pow_frob_sub_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU s A hA i h m
  have hpr : l.Prime := hU.1
  have hl1 : ‖(l : K)‖ < 1 := hU.2.2.1
  have hp0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact Formalism.LT.FrobP.main l i hpr (σ ^ i) hp0 hl1 (isFrobLift_pow l σ hU i).1 A hA m

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLeStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.pow_frob_sub_le | exact GlobalTheory.Honda.pow_frob_sub_le | (intros; apply GlobalTheory.Honda.pow_frob_sub_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SubstCongrModPrimeOfIntegralDerivativeStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 → ∀ (f : K⟦X⟧), CoefLe 1 (PowerSeries.derivative f) → ∀ (s : Type) (A B : MvPowerSeries s K), MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 → (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) → ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l hl hlt f hf s A B hA0 hB0 hA hB hAB m
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero hA0
  have hsB : HasSubst B := HasSubst.of_constantCoeff_zero hB0
  have hterm : ∀ d : ℕ, ‖coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hcong := Formalism.LT.PowCongr_valid K s l hl A B hA hB 1 le_rfl
      (by intro e; simpa using hAB e) (padicValNat l d) (d / l ^ padicValNat l d) m
    have hdecomp : l ^ padicValNat l d * (d / l ^ padicValNat l d) = d :=
      Nat.mul_div_cancel' (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [hdecomp, norm_pow, pow_add, pow_one] at hcong
    have hnd : ‖(d : K)‖ = ‖(l : K)‖ ^ padicValNat l d :=
      Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hl hlt hd.ne'
    have hder : ‖coeff d f‖ * ‖(d : K)‖ ≤ 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := hf k
      rw [coeff_derivative, norm_mul] at this
      simpa using this
    rw [norm_mul]
    calc ‖coeff d f‖ * ‖MvPowerSeries.coeff m (A ^ d - B ^ d)‖
        ≤ ‖coeff d f‖ * (‖(l : K)‖ * ‖(d : K)‖) := by
          rw [hnd]; exact mul_le_mul_of_nonneg_left hcong (norm_nonneg _)
      _ = ‖(l : K)‖ * (‖coeff d f‖ * ‖(d : K)‖) := by ring
      _ ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left hder (norm_nonneg _)
      _ = ‖(l : K)‖ := mul_one _
  rw [map_sub, coeff_subst hsA, coeff_subst hsB,
    ← finsum_sub_distrib (coeff_subst_finite hsA f m) (coeff_subst_finite hsB f m)]
  have heq : (fun d : ℕ => coeff d f • MvPowerSeries.coeff m (A ^ d) - coeff d f • MvPowerSeries.coeff m (B ^ d))
      = fun d => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d) := by
    funext d; rw [map_sub, smul_eq_mul, smul_eq_mul, mul_sub]
  have hfin : (Function.support fun d : ℕ => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)).Finite := by
    rw [← heq]
    exact ((coeff_subst_finite hsA f m).union (coeff_subst_finite hsB f m)).subset
      (Function.support_sub _ _)
  rw [heq, finsum_eq_sum _ hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => hterm d
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogEigenModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogEigenModPrime
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

theorem coefLe_mv_of_ps {K : Type} [NormedField K] {r : ℝ} {A : K⟦X⟧} (h : ∀ n, ‖coeff n A‖ ≤ r) :
    ∀ m : Unit →₀ ℕ, ‖MvPowerSeries.coeff m A‖ ≤ r := by
  intro m
  have hm : m = Finsupp.single () (m ()) := by
    ext
    simp
  rw [hm]
  exact h (m ())

theorem norm_ringHom_pow_apply {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∀ (j : ℕ) (x : K), ‖(σ ^ j) x‖ = ‖x‖ := by
  intro j x
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

private theorem norm_coeff_pow_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {s : Type}
    (M : MvPowerSeries s K) (hM : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1) :
    ∀ (N : ℕ) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (M ^ N)‖ ≤ 1 := by
  classical
  intro N
  induction N with
  | zero =>
    intro m
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih =>
    intro m
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hM _)

theorem frobLog_eigen : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) →
    ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) -
      C ((σ ^ i) w) * frobOp σ l i f) := by
  intro K _ _ _ l σ hU f e hf w hw i hi
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := norm_ringHom_pow_apply σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hef' : PowerSeries.subst e' g = PowerSeries.X := by
    have := congrArg (MvPowerSeries.map (σ ^ i)) hef
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
    exact this
  have hd' : CoefLe 1 (d⁄dX g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add (f := _), map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set M := Formalism.L2.Th1.C.mulBy f e w with hMdef
  have hCf0 : PowerSeries.constantCoeff (PowerSeries.C w * f) = 0 := by
    rw [map_mul, h0, mul_zero]
  have hM0 : MvPowerSeries.constantCoeff M = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hCf0 _ h0'
  have hMint : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1 := coefLe_mv_of_ps hw
  have hAB := GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' Unit M hMint i hn
  set A := M ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) M) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hM0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hM0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => norm_coeff_pow_le_one M hMint _ m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' Unit A B hA0 hB0 hA1 hB1 hAB
  have hsM : PowerSeries.subst M (frobOp σ l i f) = PowerSeries.subst A g := by
    have has := PowerSeries.HasSubst.of_constantCoeff_zero hM0
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  set c := (σ ^ i) w with hc
  have hq0 : PowerSeries.constantCoeff (PowerSeries.C c * g) = 0 := by
    rw [map_mul, hg0, mul_zero]
  have hmapM : MvPowerSeries.map (σ ^ i) M = PowerSeries.subst (PowerSeries.C c * g) e' := by
    have hm : MvPowerSeries.map (σ ^ i) (PowerSeries.C w * f) = PowerSeries.C c * g := by
      change PowerSeries.map (σ ^ i) (PowerSeries.C w * f) = _
      rw [map_mul, PowerSeries.map_C]
    rw [hMdef]
    unfold Formalism.L2.Th1.C.mulBy
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hCf0), hm]
  have hexp : MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)
      = PowerSeries.C c * PowerSeries.subst (PowerSeries.X ^ l ^ i) g := by
    change PowerSeries.expand (l ^ i) hn (PowerSeries.C c * g) = _
    rw [PowerSeries.expand_apply, PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow hn),
      PowerSeries.subst_C]
    rfl
  have hexp0 : MvPowerSeries.constantCoeff (MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand]
    exact hq0
  have hBg : PowerSeries.subst B g = PowerSeries.C c * frobOp σ l i f := by
    rw [hB, hmapM, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' he0)
        (PowerSeries.HasSubst.of_constantCoeff_zero hexp0),
      hef', PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hexp0), hexp]
    rfl
  intro k
  rw [hsM, ← hBg]
  exact key (Finsupp.single () k)

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogEigenModPrimeStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_eigen_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) - C ((σ ^ i) w) * frobOp σ l i f) := by
  first | exact @GlobalTheory.Honda.frobLog_eigen | exact GlobalTheory.Honda.frobLog_eigen | (intros; apply GlobalTheory.Honda.frobLog_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogAdditiveModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogAdditiveModPrime
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

open Formalism.L2.Th1.C

theorem twistLog_norm_iterate {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x : K, ‖σ x‖ = ‖x‖) (i : ℕ)
    (x : K) : ‖(σ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

theorem twistLog_additive_mod : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m,
      ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2))
        (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU f e hf i hi m
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  have hlog0 := hlog
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := twistLog_norm_iterate σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hlog' : IsLogPair g e' := by
    refine ⟨hg0, ?_, he0, ?_, ?_⟩
    · rw [hg, PowerSeries.coeff_map, h1, map_one]
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hfe
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0), hXm] at this
      exact this
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hef
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
      exact this
  have hd' : CoefLe 1 (d⁄dX g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add (f := _), map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set X0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hX1
  have hX00 : MvPowerSeries.constantCoeff X0 = 0 := by simp [X0]
  have hX10 : MvPowerSeries.constantCoeff X1 = 0 := by simp [X1]
  set F := fadd f e X0 X1 with hF
  have hF0 : MvPowerSeries.constantCoeff F = 0 := Pts.constantCoeff_fadd hlog0 hX00 hX10
  have hFint : ∀ m, ‖MvPowerSeries.coeff m F‖ ≤ 1 := fun m => hint m
  have hAB := GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' (Fin 2) F hFint i hn
  set A := F ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) F) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hF0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hF0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => IntegralMvPolynomialLemmas.intMv_pow hint (l ^ i) m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' (Fin 2) A B hA0 hB0 hA1 hB1 hAB m
  have hsX : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (frobOp σ l i f) = PowerSeries.subst (a ^ l ^ i) g := by
    intro a ha
    have has := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  have hs0 : MvPowerSeries.constantCoeff (PowerSeries.subst X0 g + PowerSeries.subst X1 g) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero hX00 _ hg0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ hg0, add_zero]
  have hs0f : MvPowerSeries.constantCoeff (PowerSeries.subst X0 f + PowerSeries.subst X1 f) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero hX00 _ h0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ h0, add_zero]
  have hmapF : MvPowerSeries.map (σ ^ i) F
      = PowerSeries.subst (PowerSeries.subst X0 g + PowerSeries.subst X1 g) e' := by
    rw [hF]
    unfold fadd
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0f), map_add (f := _),
      PowerSeries.map_subst (PowerSeries.HasSubst.X 0), PowerSeries.map_subst (PowerSeries.HasSubst.X 1),
      hX0, hX1, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hBf : B = fadd g e' (X0 ^ l ^ i) (X1 ^ l ^ i) := by
    rw [hB, hmapF, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hs0),
      map_add, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 0),
      PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 1), hX0, hX1,
      MvPowerSeries.expand_X, MvPowerSeries.expand_X]
    rfl
  have hBeq : PowerSeries.subst B g
      = PowerSeries.subst (X0 ^ l ^ i) g + PowerSeries.subst (X1 ^ l ^ i) g := by
    rw [hBf]
    exact Pts.l_fadd hlog' (by rw [map_pow, hX00, zero_pow hn]) (by rw [map_pow, hX10, zero_pow hn])
  have hbe : be0 f e (frobOp σ l i f) X0 X1 = PowerSeries.subst A g - PowerSeries.subst B g := by
    unfold be0
    rw [← hF, hsX F hF0, hsX X0 hX00, hsX X1 hX10, hBeq]
    abel
  rw [hbe]
  exact key

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogAdditiveModPrimeStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_additive_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m, ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.twistLog_additive_mod | exact GlobalTheory.Honda.twistLog_additive_mod | (intros; apply GlobalTheory.Honda.twistLog_additive_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHondaTypeEvenFrobeniusPowers
open PowerSeries GlobalTheory.Honda

noncomputable section

namespace GlobalTheory.Honda

namespace EvenType

open Formalism.L2.Th1.C

section Order

variable {K : Type} [Field K] {ι : Type}

theorem ord_add {k : ℕ∞} {A B : MvPowerSeries ι K} (hA : k ≤ A.order) (hB : k ≤ B.order) :
    k ≤ (A + B).order := (le_min hA hB).trans MvPowerSeries.min_order_le_add

theorem ord_mul {j k : ℕ∞} {A B : MvPowerSeries ι K} (hA : j ≤ A.order) (hB : k ≤ B.order) :
    j + k ≤ (A * B).order := (add_le_add hA hB).trans MvPowerSeries.le_order_mul

theorem ord_pow_sub {A B : MvPowerSeries ι K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (h : (2 : ℕ∞) ≤ (A - B).order) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (A ^ n - B ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show A ^ (n + 1) - B ^ (n + 1) = A * (A ^ n - B ^ n) + (A - B) * B ^ n by ring]
    refine ord_add ?_ ?_
    · refine le_trans (le_of_eq ?_)
        (ord_mul (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 hA) ih)
      push_cast; ring
    · refine le_trans (le_of_eq ?_)
        (ord_mul h (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hB))
      push_cast; ring

theorem ord_subst_sub {g : K⟦X⟧} (h0 : constantCoeff g = 0) (h1 : coeff 1 g = 1)
    {A : MvPowerSeries ι K} (hA : MvPowerSeries.constantCoeff A = 0) :
    (2 : ℕ∞) ≤ (g.subst A - A).order := by
  obtain ⟨q, hq⟩ : (X : K⟦X⟧) ^ 2 ∣ g - X := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [h0]
    · simp [h1]
  have hs := Pts.hasSubst hA
  have : g.subst A - A = A ^ 2 * q.subst A := by
    have := congrArg (PowerSeries.subst A) hq
    rwa [subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs] at this
  rw [this]
  simpa using ord_mul (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero 2 hA)
    (zero_le : (0 : ℕ∞) ≤ (q.subst A : MvPowerSeries ι K).order)

theorem subst_comb {A : MvPowerSeries ι K} (hA : MvPowerSeries.constantCoeff A = 0) (a : K) (f : K⟦X⟧)
    (s : Finset ℕ) (c : ℕ → K) (g : ℕ → K⟦X⟧) :
    (C a * f - ∑ k ∈ s, C (c k) * g k).subst A =
      MvPowerSeries.C a * f.subst A - ∑ k ∈ s, MvPowerSeries.C (c k) * (g k).subst A := by
  have hs := Pts.hasSubst hA
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_sub hs, subst_mul hs, subst_C, ← coe_substAlgHom hs, map_sum]
  simp only [coe_substAlgHom hs, subst_mul hs, subst_C]

end Order

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}

theorem norm_sub_le_of {x y : K} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x - y‖ ≤ r := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rwa [norm_neg]))

theorem norm_coeff_subst_sub {r : ℝ} (hr : 0 ≤ r) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0)
    (hAB : (2 : ℕ∞) ≤ (A - B).order) (hI : IntMv (Formalism.G.unitBall K) A) (h : K⟦X⟧) (d : ι →₀ ℕ)
    (hlow : ∀ m < d.degree, ‖coeff m h‖ ≤ r) :
    ‖MvPowerSeries.coeff d (h.subst A) - coeff d.degree h * MvPowerSeries.coeff d (B ^ d.degree)‖ ≤ r := by
  have hAn : MvPowerSeries.coeff d (A ^ d.degree) = MvPowerSeries.coeff d (B ^ d.degree) := by
    rw [← sub_eq_zero, ← map_sub]
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (ord_pow_sub hA hB hAB d.degree))
    exact_mod_cast Nat.lt_succ_self _
  rw [coeff_subst (Pts.hasSubst hA), finsum_eq_sum_of_support_subset (s := Finset.range (d.degree + 1)),
    Finset.sum_range_succ, hAn, smul_eq_mul, add_sub_cancel_right]
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun m hm => ?_
    rw [smul_eq_mul, norm_mul]
    have h1 : ‖MvPowerSeries.coeff d (A ^ m)‖ ≤ 1 := IntegralMvPolynomialLemmas.intMv_pow hI m d
    exact (mul_le_of_le_one_right (norm_nonneg _) h1).trans (hlow m (Finset.mem_range.1 hm))
  · intro m hm
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    refine hm ?_
    have : MvPowerSeries.coeff d (A ^ m) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega : d.degree < m))
        (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero m hA))
    simp [this]

end Norm

theorem cob_degree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l : ℕ) (f e : K⟦X⟧), IntLog f e → ∀ (h : K⟦X⟧), (∀ m, ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e h (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖) → ∀ n : ℕ, (∀ m < n, ‖coeff m h‖ ≤ ‖(l : K)‖) → ∀ k : ℕ, 0 < k → k < n → ‖coeff n h * (n.choose k : K)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ l f e hf h hb n hlow k hk0 hkn
  classical
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hp := hf.1
  obtain ⟨d, hd0, hd1⟩ : ∃ d : Fin 2 →₀ ℕ, d 0 = k ∧ d 1 = n - k :=
    ⟨Finsupp.single 0 k + Finsupp.single 1 (n - k), by simp, by simp⟩
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]; omega
  have hord : (2 : ℕ∞) ≤ (fadd f e (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) -
      (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2))).order := by
    have a1 := ord_subst_sub hp.2.2.1 (Pts.coeff_one_linv hp) (Pts.constantCoeff_add_l hp h0 h1)
    have a2 := ord_add (ord_add a1 (ord_subst_sub hp.1 hp.2.1 h0)) (ord_subst_sub hp.1 hp.2.1 h1)
    convert a2 using 2
    rw [fadd]; ring
  have key := norm_coeff_subst_sub (norm_nonneg (l : K)) (Pts.constantCoeff_fadd hp h0 h1)
    (by rw [map_add (f := _), h0, h1, add_zero]) hord hf.2.2 h d (by rwa [hdeg])
  have hch : MvPowerSeries.coeff d ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) :
      MvPowerSeries (Fin 2) K) ^ n) = (n.choose k : K) := by
    rw [← MvPolynomial.coe_X, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
      MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow, if_pos, hd0]
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp only; omega
  have hX : ∀ s : Fin 2, MvPowerSeries.coeff d (h.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) K)) = 0 := by
    intro s
    rw [coeff_subst (HasSubst.X s)]
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
    rintro rfl
    fin_cases s
    · simp at hd1; omega
    · simp at hd0; omega
  have hb' := hb d
  rw [be0, map_sub, map_sub, hX, hX, sub_zero, sub_zero] at hb'
  rw [hdeg, hch] at key
  simpa using norm_sub_le_of hb' key

theorem eig_degree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l : ℕ) (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → ∀ h : K⟦X⟧, CoefLe ‖(l : K)‖ (h.subst (Formalism.L2.Th1.C.mulBy f e w) - C w * h) → ∀ n : ℕ, (∀ m < n, ‖coeff m h‖ ≤ ‖(l : K)‖) → ‖coeff n h * (w ^ n - w)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ l f e hf w hw h hb n hlow
  have hp := hf.1
  have hord : (2 : ℕ∞) ≤ MvPowerSeries.order (mulBy f e w - C w * X : K⟦X⟧) := by
    refine MvPowerSeries.nat_le_order (n := 2) fun d hd => ?_
    obtain ⟨m, rfl⟩ : ∃ m, d = Finsupp.single () m := ⟨d (), by ext; simp⟩
    rw [Finsupp.degree_single] at hd
    show coeff m (mulBy f e w - C w * X) = 0
    interval_cases m
    · simp [Pts.constantCoeff_mulBy hp w]
    · simp [Formalism.L2.Th1.G.coeff_one_mulBy hp w]
  have key := norm_coeff_subst_sub (norm_nonneg (l : K)) (Pts.constantCoeff_mulBy hp w)
    (show constantCoeff (C w * X : K⟦X⟧) = 0 by simp) hord
    (Pts.intMv_of_intPS (R := Formalism.G.unitBall K) hw) h (Finsupp.single () n)
    (by rwa [Finsupp.degree_single])
  rw [Finsupp.degree_single] at key
  replace key : ‖coeff n (h.subst (mulBy f e w) : K⟦X⟧) - coeff n h * coeff n ((C w * X : K⟦X⟧) ^ n)‖ ≤
    ‖(l : K)‖ := key
  rw [mul_pow, ← map_pow, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one] at key
  have hb' := hb n
  rw [map_sub, coeff_C_mul] at hb'
  convert norm_sub_le_of hb' key using 2
  ring

theorem pow_cong_frob : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ w : K, ‖w‖ ≤ 1 → ∀ i : ℕ, ‖w ^ (l ^ i) - (σ ^ i) w‖ < 1 := by
  intro K _ _ l σ hU w hw i
  obtain ⟨-, -, -, -, hiso, hfr⟩ := hU
  have hσ : ∀ i : ℕ, ‖(σ ^ i) w‖ ≤ 1 := by
    intro i
    induction i with
    | zero => simpa using hw
    | succ i ih => rwa [pow_succ', RingHom.mul_def, RingHom.comp_apply, hiso]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ' σ, RingHom.mul_def, RingHom.comp_apply, pow_succ, pow_mul,
      show (w ^ l ^ i) ^ l - σ ((σ ^ i) w) =
        ((w ^ l ^ i) ^ l - ((σ ^ i) w) ^ l) + -(σ ((σ ^ i) w) - ((σ ^ i) w) ^ l) by ring]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · have hx : w ^ l ^ i ∈ Formalism.G.unitBall K := pow_mem (show w ∈ Formalism.G.unitBall K from hw) _
      have hy : (σ ^ i) w ∈ Formalism.G.unitBall K := hσ i
      rw [← Commute.geom_sum₂_mul (Commute.all _ _), norm_mul]
      have h1 : ‖∑ j ∈ Finset.range l, (w ^ l ^ i) ^ j * ((σ ^ i) w) ^ (l - 1 - j)‖ ≤ 1 :=
        (sum_mem fun j _ => mul_mem (pow_mem hx _) (pow_mem hy _) : _ ∈ Formalism.G.unitBall K)
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) h1) ih
    · rw [norm_neg]; exact hfr _ (hσ i)

theorem coeff_frobOp_ite : ∀ (K : Type) [NormedField K] (τ : K →+* K) (q i : ℕ) (f : K⟦X⟧), 0 < q → ∀ m : ℕ, coeff m (frobOp τ q i f) = if q ^ i ∣ m then (τ ^ i) (coeff (m / q ^ i) f) else 0 := by
  intro K _ τ q i f hq n
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ hq.ne')]
  simp [coeff_map]

theorem cob_even_sum : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (s : Finset ℕ) (c : ℕ → K), (∀ k ∈ s, ‖c k‖ ≤ 1) → ∀ m, ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f) (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU f e hf s c hc m
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hp := hf.1
  have : be0 f e (C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f)
      (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) =
      -∑ k ∈ s, MvPowerSeries.C (c k) * be0 f e (frobOp σ l (2 * k + 2) f)
        (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := by
    simp only [be0]
    rw [subst_comb (Pts.constantCoeff_fadd hp h0 h1), subst_comb h0, subst_comb h1, Pts.l_fadd hp h0 h1]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_neg, norm_neg, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  rw [MvPowerSeries.coeff_C_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc k hk)).trans
    (GlobalTheory.T.hondaFrobeniusTwistLog_additive_mod_prime K l σ hU f e hf _ (by omega) m)

theorem eig_even_sum : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ∀ (s : Finset ℕ) (c : ℕ → K), (∀ k ∈ s, ‖c k‖ ≤ 1) → CoefLe ‖(l : K)‖ ((C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f).subst (Formalism.L2.Th1.C.mulBy f e w) - C w * (C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f)) := by
  intro K _ _ _ l σ hU f e hf w hw hσw s c hc m
  have hp := hf.1
  have hσ2 : ∀ t, (σ ^ (2 * t + 2)) w = w := by
    intro t
    induction t with
    | zero => exact hσw
    | succ t ih =>
      rw [show 2 * (t + 1) + 2 = 2 * t + 2 + 1 + 1 by ring, pow_succ', pow_succ', RingHom.mul_def,
        RingHom.mul_def, RingHom.comp_apply, RingHom.comp_apply, ih, hσw]
  have hl : (f.subst (mulBy f e w) : K⟦X⟧) = C w * f :=
    Pts.subst_l_linv hp (show constantCoeff (C w * f) = 0 by rw [map_mul, hp.1, mul_zero])
  have hcomb : ((C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f).subst (mulBy f e w) : K⟦X⟧) =
      C (l : K) * f.subst (mulBy f e w) -
        ∑ k ∈ s, C (c k) * (frobOp σ l (2 * k + 2) f).subst (mulBy f e w) :=
    subst_comb (Pts.constantCoeff_mulBy hp w) _ _ _ _ _
  have : (C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f).subst (mulBy f e w) -
      C w * (C (l : K) * f - ∑ k ∈ s, C (c k) * frobOp σ l (2 * k + 2) f) =
      -∑ k ∈ s, C (c k) * ((frobOp σ l (2 * k + 2) f).subst (mulBy f e w) -
        C ((σ ^ (2 * k + 2)) w) * frobOp σ l (2 * k + 2) f) := by
    rw [hcomb, hl]
    simp only [hσ2, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_left_comm (C w)]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_neg, norm_neg, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  rw [coeff_C_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc k hk)).trans
    (GlobalTheory.T.hondaFrobeniusTwistLog_eigen_mod_prime K l σ hU f e hf w hw _ (by omega) m)

theorem mulBy_low_coeff : ∀ (K : Type) [Field K] (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ w : K, constantCoeff (Formalism.L2.Th1.C.mulBy f e w) = 0 ∧ coeff 1 (Formalism.L2.Th1.C.mulBy f e w) = w := fun _ _ _ _ h w => ⟨Pts.constantCoeff_mulBy h w, Formalism.L2.Th1.G.coeff_one_mulBy h w⟩

theorem exists_triangular {K : Type} [Field K] (a : ℕ → K) (b : ℕ → ℕ → K) :
    ∃ c : ℕ → K, ∀ j, c j = a j - ∑ k ∈ Finset.range j, c k * b j k := by
  refine ⟨fun j => Nat.strongRec (motive := fun _ => K)
    (fun j ih => a j - ∑ k : Fin j, ih k k.isLt * b j k) j, fun j => ?_⟩
  rw [← Fin.sum_univ_eq_sum_range (fun k => Nat.strongRec (motive := fun _ => K)
    (fun j ih => a j - ∑ k : Fin j, ih k k.isLt * b j k) k * b j k) j]
  exact Nat.strongRec_eq _ j

end EvenType

open EvenType in
theorem exists_even_type : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → ∃ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) := by
  intro K _ _ _ l σ hU f e hf w hw hσw hw1
  classical
  have hlp := hU.1
  have hl2 : 2 < l := hU.2.1
  have hl1 : ‖(l : K)‖ < 1 := hU.2.2.1
  have hf0 : coeff 0 f = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact hf.1.1
  have hf1 : coeff 1 f = 1 := hf.1.2.1
  have hl0 : 0 < l := by omega
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ j, N j = l ^ (2 * j + 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → K⟦X⟧, ∀ k, Φ k = frobOp σ l (2 * k + 2) f := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → K, ∀ j, c j = (l : K) * coeff (N j) f -
      ∑ k ∈ Finset.range j, c k * coeff (N j) (Φ k) :=
    exists_triangular (fun j => (l : K) * coeff (N j) f) fun j k => coeff (N j) (Φ k)
  have hΦc : ∀ k m, coeff m (Φ k) = if N k ∣ m then (σ ^ (2 * k + 2)) (coeff (m / N k) f) else 0 :=
    fun k m => by rw [hN, hΦ]; exact coeff_frobOp_ite K σ l (2 * k + 2) f hl0 m
  have hΦlow : ∀ k m, m < N k → coeff m (Φ k) = 0 := by
    intro k m hm
    rw [hΦc, Nat.div_eq_of_lt hm, hf0, map_zero, ite_self]
  have hNmono : StrictMono N := fun a b hab => by
    rw [hN, hN]; exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hNgt : ∀ k, k + 2 < N k := fun k => by
    have := Nat.lt_pow_self (n := 2 * k + 2) (show 1 < l by omega)
    rw [hN]; omega
  have hΦtop : ∀ k, coeff (N k) (Φ k) = 1 := by
    intro k
    rw [hΦc, if_pos dvd_rfl, Nat.div_self (by have := hNgt k; omega), hf1, map_one]
  obtain ⟨G, hG⟩ : ∃ G, G = C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f := ⟨_, rfl⟩
  have hGc : ∀ m, coeff m G = (l : K) * coeff m f - ∑ j ∈ Finset.range m, c j * coeff m (Φ j) := by
    intro m
    rw [hG, map_sub, coeff_C_mul, hondaSum, coeff_mk]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, frobOp, frobOp, ← pow_mul, ← pow_mul, show 2 * (j + 1) = 2 * j + 2 by ring]
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ → K, ∀ n k, d n k = if N k < n then c k else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ → K⟦X⟧, ∀ n, H n = C (l : K) * f -
      ∑ k ∈ Finset.range n, C (d n k) * frobOp σ l (2 * k + 2) f := ⟨_, fun _ => rfl⟩
  have hHc : ∀ n m, coeff m (H n) =
      (l : K) * coeff m f - ∑ k ∈ Finset.range n, d n k * coeff m (Φ k) := by
    intro n m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, hΦ, map_sub, map_sum, coeff_C_mul]
  have hlow : ∀ n m, m ≤ n → (∀ k, N k = n → m < n) → coeff m (H n) = coeff m G := by
    intro n m hmn hk'
    rw [hHc, hGc, Finset.sum_subset (Finset.range_mono hmn) (f := fun j => c j * coeff m (Φ j)) ?_]
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd]
      split_ifs with hk
      · rfl
      · rw [hΦlow k m (by have := hk' k; omega), mul_zero, mul_zero]
    · intro j _ hj'
      rw [Finset.mem_range] at hj'
      rw [hΦlow j m (by have := hNgt j; omega), mul_zero]
  have htopH : ∀ j, c j = coeff (N j) (H (N j)) := by
    intro j
    rw [hc, hHc, ← Finset.sum_subset (Finset.range_mono (show j ≤ N j by have := hNgt j; omega))
      (f := fun k => d (N j) k * coeff (N j) (Φ k)) ?_]
    · congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hd, if_pos (hNmono (Finset.mem_range.mp hk))]
    · intro k _ hk'
      rw [Finset.mem_range, not_lt] at hk'
      rw [hd, if_neg (not_lt.mpr (hNmono.monotone hk')), zero_mul]
  have htopG : ∀ j, coeff (N j) G = 0 := by
    intro j
    rw [hGc, ← Finset.sum_subset (Finset.range_mono (show j + 1 ≤ N j by have := hNgt j; omega))
      (f := fun k => c k * coeff (N j) (Φ k)) ?_]
    · rw [Finset.sum_range_succ, hΦtop, mul_one, hc j]; ring
    · intro k _ hk'
      rw [Finset.mem_range, not_lt] at hk'
      rw [hΦlow k _ (hNmono hk'), mul_zero]
  have hσ2 : ∀ t, (σ ^ (2 * t)) w = w := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, pow_succ', pow_succ', RingHom.mul_def, RingHom.mul_def,
        RingHom.comp_apply, RingHom.comp_apply, ih, hσw]
  have hwint : ‖w‖ ≤ 1 := by rw [← (mulBy_low_coeff K f e hf.1 w).2]; exact hw 1
  have key : ∀ n, (∀ m < n, ‖coeff m G‖ ≤ ‖(l : K)‖) ∧ (∀ k, N k < n → ‖c k‖ ≤ 1) := by
    intro n
    induction n with
    | zero => exact ⟨fun m hm => absurd hm (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨ihG, ihc⟩ := ih
      have hd1 : ∀ k ∈ Finset.range n, ‖d n k‖ ≤ 1 := by
        intro k _
        rw [hd]
        split_ifs with hk
        · exact ihc k hk
        · simp
      have hA := cob_even_sum K l σ hU f e hf (Finset.range n) (d n) hd1
      have hB := eig_even_sum K l σ hU f e hf w hw hσw (Finset.range n) (d n) hd1
      rw [← hH] at hA hB
      have hlowH : ∀ m < n, ‖coeff m (H n)‖ ≤ ‖(l : K)‖ := fun m hm => by
        rw [hlow n m hm.le fun _ _ => hm]; exact ihG m hm
      have claim : ‖coeff n (H n)‖ ≤ 1 ∧ (‖coeff n (H n)‖ ≤ ‖(l : K)‖ ∨ ∃ t, N t = n) := by
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · have h0 : ‖coeff n (H n)‖ ≤ ‖(l : K)‖ := by
            rw [hHc, Finset.sum_eq_zero fun k _ => by
              rw [hΦlow k n (by have := hNgt k; omega), mul_zero], sub_zero]
            interval_cases n
            · simp [hf0]
            · simp [hf1]
          exact ⟨h0.trans hl1.le, Or.inl h0⟩
        · rcases GlobalTheory.T.lazard_binomial_norm_ultrametric K l hlp hl1 _ n hn2 (cob_degree K l f e hf (H n) hA n hlowH) with
            h1 | ⟨h1, i, hi0, hni⟩
          · exact ⟨h1.trans hl1.le, Or.inl h1⟩
          · refine ⟨h1, ?_⟩
            rcases Nat.even_or_odd' i with ⟨t, ht | ht⟩
            · right
              refine ⟨t - 1, ?_⟩
              rw [hN, hni]; congr 1; omega
            · left
              have hcong := pow_cong_frob K l σ hU w hwint i
              rw [← hni, ht, pow_succ' σ, RingHom.mul_def, RingHom.comp_apply, hσ2] at hcong
              have hnorm : ‖w ^ n - w‖ = 1 := by
                rw [show w ^ n - w = (w ^ n - σ w) + (σ w - w) by ring,
                  IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hw1]; exact hcong.ne), hw1]
                exact max_eq_right hcong.le
              have := eig_degree K l f e hf w hw (H n) hB n hlowH
              rwa [norm_mul, hnorm, mul_one] at this
      refine ⟨fun m hm => ?_, fun k hk => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
        · exact ihG m hm
        · rw [hm]
          by_cases hex : ∃ t, N t = n
          · obtain ⟨t, ht⟩ := hex
            rw [← ht, htopG t, norm_zero]; exact norm_nonneg _
          · rw [← hlow n n le_rfl fun k hk => absurd ⟨k, hk⟩ hex]
            exact claim.2.resolve_right hex
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · exact ihc k hk
        · rw [htopH k, hk]; exact claim.1
  refine ⟨c, fun j => (key (N j + 1)).2 j (Nat.lt_succ_self _), fun n => ?_⟩
  rw [← hG]
  exact (key (n + 1)).1 n (Nat.lt_succ_self n)

end GlobalTheory.Honda
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHondaTypeEvenFrobeniusPowersStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hondaType_evenFrobeniusPowers : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → ∃ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) := by
  first | exact @GlobalTheory.Honda.exists_even_type | exact GlobalTheory.Honda.exists_even_type | (intros; apply GlobalTheory.Honda.exists_even_type <;> assumption)
end
