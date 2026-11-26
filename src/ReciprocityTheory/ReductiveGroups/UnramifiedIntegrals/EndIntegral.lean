module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgTorInt
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnEndo
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnTrans
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem trans_ev (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    ∀ᶠ z in nhds (0 : ℂ), z + t ∉ L.lattice := by
  have ho : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hc : ContinuousAt (fun z : ℂ => z + t) 0 := by fun_prop
  have : (L.lattice : Set ℂ)ᶜ ∈ nhds ((fun z : ℂ => z + t) 0) := by
    apply ho.mem_nhds
    simpa using ht
  exact hc.eventually this

theorem trans_an (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    AnalyticAt ℂ (fun z => L.weierstrassP (z + t)) 0 ∧
      AnalyticAt ℂ (fun z => L.derivWeierstrassP (z + t)) 0 := by
  have h1 : AnalyticAt ℂ L.weierstrassP ((fun z : ℂ => z + t) 0) :=
    L.analyticOnNhd_weierstrassP _ (by simpa using ht)
  have h2 : AnalyticAt ℂ L.derivWeierstrassP ((fun z : ℂ => z + t) 0) :=
    L.analyticOnNhd_derivWeierstrassP _ (by simpa using ht)
  have h3 : AnalyticAt ℂ (fun z : ℂ => z + t) 0 := by fun_prop
  exact ⟨AnalyticAt.comp (g := L.weierstrassP) (f := fun z : ℂ => z + t) h1 h3,
    AnalyticAt.comp (g := L.derivWeierstrassP) (f := fun z : ℂ => z + t) h2 h3⟩

theorem trans_taylor_quad (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b : ℂ) :
    F.taylor0 (fun z => a * (f z * f z) + b) = C a * (F.taylor0 f * F.taylor0 f) + C b := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff : AnalyticAt ℂ (fun z => f z * f z) 0 := hf.mul hf
  have haff : AnalyticAt ℂ (fun z => a * (f z * f z)) 0 := analyticAt_const.mul hff
  have h1 := (hR f f hf hf).2
  have h2 := (hR (fun _ => a) (fun z => f z * f z) analyticAt_const hff).2
  have h3 := (hR (fun z => a * (f z * f z)) (fun _ => b) haff analyticAt_const).1
  rw [h3, h2, h1, hC, hC]

theorem trans_taylor_cubic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b c : ℂ) :
    F.taylor0 (fun z => a * (f z * (f z * f z)) + (b * f z + c))
      = C a * (F.taylor0 f * (F.taylor0 f * F.taylor0 f)) + (C b * F.taylor0 f + C c) := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff : AnalyticAt ℂ (fun z => f z * f z) 0 := hf.mul hf
  have hfff : AnalyticAt ℂ (fun z => f z * (f z * f z)) 0 := hf.mul hff
  have hafff : AnalyticAt ℂ (fun z => a * (f z * (f z * f z))) 0 := analyticAt_const.mul hfff
  have hbf : AnalyticAt ℂ (fun z => b * f z) 0 := analyticAt_const.mul hf
  have hbfc : AnalyticAt ℂ (fun z => b * f z + c) 0 := hbf.add analyticAt_const
  have h1 := (hR f f hf hf).2
  have h2 := (hR f (fun z => f z * f z) hf hff).2
  have h3 := (hR (fun _ => a) (fun z => f z * (f z * f z)) analyticAt_const hfff).2
  have h4 := (hR (fun _ => b) f analyticAt_const hf).2
  have h5 := (hR (fun z => b * f z) (fun _ => c) hbf analyticAt_const).1
  have h6 := (hR (fun z => a * (f z * (f z * f z))) (fun z => b * f z + c) hafff hbfc).1
  rw [h6, h5, h4, h3, h2, h1, hC, hC, hC]

theorem trans_taylor (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    PowerSeries.derivative (F.taylor0 (fun z => L.weierstrassP (z + t)))
        = F.taylor0 (fun z => L.derivWeierstrassP (z + t)) ∧
    PowerSeries.derivative (F.taylor0 (fun z => L.derivWeierstrassP (z + t)))
        = C 6 * (F.taylor0 (fun z => L.weierstrassP (z + t))
            * F.taylor0 (fun z => L.weierstrassP (z + t))) + C (-(L.g₂ / 2)) ∧
    F.taylor0 (fun z => L.derivWeierstrassP (z + t)) * F.taylor0 (fun z => L.derivWeierstrassP (z + t))
        = C 4 * (F.taylor0 (fun z => L.weierstrassP (z + t))
            * (F.taylor0 (fun z => L.weierstrassP (z + t))
              * F.taylor0 (fun z => L.weierstrassP (z + t))))
          + (C (-L.g₂) * F.taylor0 (fun z => L.weierstrassP (z + t)) + C (-L.g₃)) := by
  obtain ⟨haf, hag⟩ := trans_an L t ht
  obtain ⟨hR, hC, -, hG⟩ := F.taylorRing
  obtain ⟨hD, -, -⟩ := F.taylorDeriv
  have hev := trans_ev L t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← hD _ haf]
    congr 1
    funext z
    rw [deriv_comp_add_const, L.deriv_weierstrassP]
  · rw [← hD _ hag, ← trans_taylor_quad _ haf]
    apply hG
    filter_upwards [hev] with z hz
    rw [deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]
    ring
  · rw [← (hR _ _ hag hag).2, ← trans_taylor_cubic _ haf]
    apply hG
    filter_upwards [hev] with z hz
    have := L.derivWeierstrassP_sq (z + t) hz
    linear_combination this

theorem trans_derivative_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    PowerSeries.derivative (PowerSeries.map φ f) = PowerSeries.map φ (PowerSeries.derivative f) := by
  ext n
  simp [coeff_derivative]

theorem trans_constSubst {K : Type*} [CommRing K] (f a : K⟦X⟧) (ha : constantCoeff a = 0) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have h1 := constantCoeff_subst_eq_zero (S := K) ha (f - C (constantCoeff f)) h0
  rw [subst_sub hs, subst_C] at h1
  have h2 : constantCoeff (subst a f - C (constantCoeff f)) = 0 := h1
  rw [map_sub, constantCoeff_C, sub_eq_zero] at h2
  exact h2

theorem trans_plus_const {K : Type} [Field K] (g2 g3 xP yP : K) :
    constantCoeff (A.yPlus (A.shortW g2 g3) xP yP) = yP ∧
    constantCoeff (A.xPlus (A.shortW g2 g3) xP yP) = xP := by
  obtain ⟨-, -, -, hx, hy⟩ := A.wSerFactor K (A.shortW g2 g3)
  have ht : constantCoeff (A.tDen (A.shortW g2 g3) xP) = 1 := by simp [A.tDen, hx]
  have h1 : (A.shortW g2 g3).a₁ = 0 := rfl
  have h3 : (A.shortW g2 g3).a₃ = 0 := rfl
  constructor
  · simp [A.yPlus, A.xPlus, A.nS, hx, hy, ht, h1, h3]
    ring
  · simp [A.xPlus]

theorem trans_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ)
    (ht : t ∉ L.lattice) :
    PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 (fun z => L.weierstrassP (z + t)))
      = (A.xPlus (A.shortW (ι L.g₂) (ι L.g₃)) (ι (L.weierstrassP t))
          (ι (L.derivWeierstrassP t) / 2)).subst (A.expSer (A.shortW (ι L.g₂) (ι L.g₃))) := by
  obtain ⟨e1, e2, e3⟩ := trans_taylor L t ht
  set p := F.taylor0 (fun z => L.weierstrassP (z + t)) with hp
  set q := F.taylor0 (fun z => L.derivWeierstrassP (z + t)) with hq
  set W := A.shortW (ι L.g₂) (ι L.g₃) with hW
  have a1 : W.a₁ = 0 := rfl
  have a2 : W.a₂ = 0 := rfl
  have a3 : W.a₃ = 0 := rfl
  have a4 : W.a₄ = -ι L.g₂ / 4 := rfl
  have a6 : W.a₆ = -ι L.g₃ / 4 := rfl
  have hpt : W.toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    rw [WeierstrassCurve.Affine.equation_iff, a1, a2, a3, a4, a6]
    have := congrArg ι (L.derivWeierstrassP_sq t ht)
    simp only [map_pow, map_sub, map_mul, map_ofNat] at this
    linear_combination (1 / 4 : ℂ_[l]) * this
  obtain ⟨hfl, -, -⟩ := A.plusZ ℂ_[l] W _ _ hpt
  set P := PowerSeries.map (ι : ℂ →+* ℂ_[l]) p with hP
  set Q := PowerSeries.map (ι : ℂ →+* ℂ_[l]) q with hQ
  have i2 : ι 2 = 2 := map_ofNat ι 2
  have i4 : ι 4 = 4 := map_ofNat ι 4
  have i6 : ι 6 = 6 := map_ofNat ι 6
  have E1 : PowerSeries.derivative P = Q := by rw [hP, trans_derivative_map, e1]
  have E2 : PowerSeries.derivative Q = C 6 * (P * P) + C (-(ι L.g₂ / 2)) := by
    rw [hQ, trans_derivative_map, e2]
    simp [hP, i2, i6]
  have E3 : Q * Q = C 4 * (P * (P * P)) + (C (-ι L.g₂) * P + C (-ι L.g₃)) := by
    rw [hQ, ← map_mul, e3]
    simp [hP, i4]
  have h2 : (C (1 / 2 : ℂ_[l]) : ℂ_[l]⟦X⟧) * 2 = 1 := by
    rw [← map_ofNat (C : ℂ_[l] →+* ℂ_[l]⟦X⟧) 2, ← map_mul]
    norm_num
  have hfl' : A.IsFlow (A.curveS W) PowerSeries.derivative P (C (1 / 2 : ℂ_[l]) * Q) := by
    have c4 : (C (-ι L.g₂ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul, ← map_mul]; congr 1; ring
    have c6 : (C (-ι L.g₃ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₃) := by
      rw [← map_mul, ← map_mul]; congr 1; ring
    have c2 : (C (-(ι L.g₂ / 2)) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul]; congr 1; ring
    have k4 : (C 4 : ℂ_[l]⟦X⟧) = 4 := map_ofNat _ 4
    have k6 : (C 6 : ℂ_[l]⟦X⟧) = 6 := map_ofNat _ 6
    refine ⟨?_, ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, a1, a2, a3, a4, a6, map_zero, c4, c6]
      rw [k4] at E3
      linear_combination (C (1 / 2 : ℂ_[l]) * C (1 / 2)) * E3 +
        (P ^ 3 * (C (1 / 2 : ℂ_[l]) * 2 + 1)) * h2
    · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, a1, a3, map_zero]
      rw [E1]
      linear_combination (-Q) * h2
    · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
        a1, a2, a4, map_zero, c4]
      rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul, E2, k6, c2]
      linear_combination (3 * P ^ 2) * h2
  have hc0 : constantCoeff (A.expSer W) = 0 := (A.expSpec ℂ_[l] W).1
  refine (A.flowUniqueZ ℂ_[l] W _ _ _ _ hfl' hfl ?_ ?_).1
  · rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).2, hP, hp]
    simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
  · rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).1, hQ, hq]
    simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
    ring

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem endo_curve (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    ∃ neg : S → S, C.IsEndoCurve (A.shortW (ι L.g₂) (ι L.g₃)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun P : S => ι (L.derivWeierstrassP (P : ℂ)) / 2)
      (ι α) := by
  obtain ⟨neg, hneg, hinv, -, hid⟩ := F.endoZInstance L α S hα hst hS
  have hb2 : (A.shortW (ι L.g₂) (ι L.g₃)).b₂ = 0 := by
    simp [A.shortW, WeierstrassCurve.b₂]
  have hnegeq : ∀ P : S, (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
    intro P
    simp
  refine ⟨neg, ?_, hinv, ?_, ?_⟩
  · intro P
    have h := L.derivWeierstrassP_sq (P : ℂ) (hS.1 P P.2).2
    have h' := congrArg ι h
    simp only [map_pow, map_sub, map_mul, map_ofNat] at h'
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW]
    linear_combination (1 / 4 : ℂ_[l]) * h'
  · intro P
    constructor
    · show ι (L.weierstrassP (neg P : ℂ)) = _
      rw [hnegeq P, L.weierstrassP_add_coe, L.weierstrassP_neg]
    · show ι (L.derivWeierstrassP (neg P : ℂ)) / 2 = _
      rw [hnegeq P, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
      simp [WeierstrassCurve.Affine.negY, A.shortW, neg_div]
  · have h := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) hid
    rw [wp_bridge]
    simp only [C.wTr, hb2, zero_div, add_zero, map_zero]
    simp only [← trans_bridge l L ι _ (hS.1 _ (Subtype.coe_prop _)).2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_add (f := _), map_sum, map_sub, PowerSeries.map_C, map_pow] at h
    have hr : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (PowerSeries.rescale α (F.pSeries L))
        = PowerSeries.rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L)) := by
      ext n
      simp [PowerSeries.coeff_rescale]
    rw [hr] at h
    simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem end_not_dvd (d : ℕ) (hd : d % 4 = 3) (l : ℕ) [Fact l.Prime]
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : ¬ l ∣ (d + 1) / 4 := by
  intro h
  apply hin
  refine ⟨1, ?_⟩
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h0 : ((d + 1 : ℕ) : ZMod l) = 0 := by
    rw [← h4, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left h 4
  push_cast at h0
  linear_combination h0

theorem end_unit (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : ¬ l ∣ n) (a : ℂ_[l]) (ha : ‖a‖ ≤ 1)
    (hq : a ^ 2 - a + (n : ℂ_[l]) = 0) : ‖a‖ = 1 := by
  have hnn : ‖(n : ℂ_[l])‖ = 1 := by
    simpa using kq_int_unit l (n : ℤ) (by exact_mod_cast hn)
  have hprod : a * (1 - a) = n := by linear_combination -hq
  have hb : ‖1 - a‖ ≤ 1 := by
    have e : 1 - a = 1 + -a := by ring
    rw [e]
    exact kq_add_le l _ _ 1 (by simp) (by rwa [norm_neg])
  refine le_antisymm ha ?_
  rw [← hnn, ← hprod, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

theorem end_card (d : ℕ) (hd : d % 4 = 3) (L : PeriodPair) (hCM : HasCMBy d L) (S : Finset ℂ)
    (h0 : omegaK d ≠ 0) (hS : Formalism.L2.Th1.F.IsKerReps L (omegaK d) S) :
    S.card + 1 = (d + 1) / 4 := by
  have h1 := Formalism.L2.Th1.F.kerRepsCard L (omegaK d) S h0 hCM hS
  have h2 := (Formalism.L2.Th1.F.hasCMByStable d L hCM 0 1).2
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ℝ) * (((d + 1) / 4 : ℕ) : ℝ) = (d : ℝ) + 1 := by exact_mod_cast h4
  have e : ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * omegaK d = omegaK d := by simp
  rw [e] at h2
  have h3 : ((S.card + 1 : ℕ) : ℝ) = (((d + 1) / 4 : ℕ) : ℝ) := by
    push_cast
    rw [h1, h2]
    push_cast
    linarith
  exact_mod_cast h3

theorem end_integral (d : ℕ) (L : PeriodPair) (hd : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (hl : 5 ≤ l) (hld : ¬ l ∣ d) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l))
    (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    IntegralPS ((uSer g2 g3).subst (C (ι (omegaK d)) * lgS g2 g3)) := by
  obtain ⟨L', hM, hCM'⟩ := good_lattice l L ι g2 g3 hg
  have hCM1 : HasCMBy d L' := hCM' d hCM
  have hl2 : l ≠ 2 := by omega
  have hquadC := omegaK_quad d hd
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι hquadC
    simpa using this
  have hln := end_not_dvd d hd l hin
  have hn0 : 0 < (d + 1) / 4 := by omega
  obtain ⟨ha1, -, -⟩ := kur_quad l d hd hl2 hld hin _ hquad
  have hau : ‖ι (omegaK d)‖ = 1 := end_unit l _ hln _ ha1 hquad
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have hα : omegaK d ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hau
    exact zero_ne_one hau
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L' (omegaK d) hα hCM1
  have hcard := end_card d hd L' hCM1 S hα hS
  obtain ⟨neg, hE⟩ := endo_curve l L' ι (omegaK d) S hα hCM1 hS
  rw [← hM.eq2, ← hM.eq3] at hE
  have htor : ∀ P : S, ‖ι (L'.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L'.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    obtain ⟨hP1, hP2⟩ := hS.1 P P.2
    refine tor_integral l hl2 L' ι g2 g3 hM _ hn0 hln P ?_ hP2
    have e : (((d + 1) / 4 : ℕ) : ℂ) * (P : ℂ) = omegaK d * (P : ℂ) - omegaK d * (omegaK d * (P : ℂ)) := by
      linear_combination (P : ℂ) * hquadC
    rw [e]
    exact sub_mem hP1 (hCM1 _ hP1)
  have hc : Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[l]) (Formalism.L2.Th1.A.shortW g2 g3) :=
    shortW_intModel g2 g3 hM.n2 hM.n3 h2
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := Formalism.L2.Th1.C.inv_mem_unitBall h2
  obtain ⟨hlp, hwp, hAx, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[l] (unitBall ℂ_[l]) _ hc
  have hDat := Formalism.L2.Th1.C.curveEndoR ℂ_[l] (unitBall ℂ_[l]) _ hc S neg _ _ (ι (omegaK d))
    (1 - ι (omegaK d)) hE (fun P => (htor P).1)
    (fun P => by
      change ‖ι (L'.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
      rw [norm_div, h2, div_one]
      exact (htor P).2)
    (by
      rw [Fintype.card_coe]
      have : ((S.card : ℂ_[l]) + 1) = (((d + 1) / 4 : ℕ) : ℂ_[l]) := by exact_mod_cast hcard
      rw [this]
      linear_combination -hquad)
    hau.le (Formalism.L2.Th1.C.inv_mem_unitBall hau)
    (by
      have : (Formalism.L2.Th1.A.shortW g2 g3).b₂ = 0 := by
        simp [Formalism.L2.Th1.A.shortW, WeierstrassCurve.b₂]
      rw [this]
      simp)
  have hEnd := Formalism.L2.Th1.C.endIntFromDatum ℂ_[l] (unitBall ℂ_[l]) _ _ _ _ _ S neg _ _ _ _ _
    hlp hwp hAx h2R hDat
  rw [lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq]
  exact hEnd

end ReciprocityTheory.ChartRestriction.L1
