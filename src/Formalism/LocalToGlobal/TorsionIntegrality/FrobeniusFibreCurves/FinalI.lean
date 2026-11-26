module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CocycleDiffExpEquiv
noncomputable section

namespace Formalism.L2.Th1.B.BeE

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem cob_sub {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f - g) = cob F f - cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_sub h0, PowerSeries.subst_sub (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_sub (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_add h0, PowerSeries.subst_add (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_add (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_zero {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    cob F (0 : PowerSeries K) = 0 := by
  simpa using cob_sub hF (0 : PowerSeries K) 0

theorem cob_neg {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) : cob F (-f) = -cob F f := by
  have h := cob_sub hF (0 : PowerSeries K) f
  rwa [zero_sub, cob_zero hF, zero_sub] at h

theorem psubst_fLog {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.subst U (fLog g) = fLog (PowerSeries.subst U g) := by
  have hg1 : PowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  unfold fLog
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg1) hU',
    PowerSeries.subst_sub hU']
  congr 2
  rw [← map_one (PowerSeries.C (R := K)), PowerSeries.subst_C, map_one]

theorem cc_psubst {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} {c : K} (hg : PowerSeries.constantCoeff g = c) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = c := by
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hgc : PowerSeries.constantCoeff (g - PowerSeries.C c) = 0 := by simp [hg]
  have e : g = PowerSeries.C c + (g - PowerSeries.C c) := by ring
  rw [e, PowerSeries.subst_add hU', PowerSeries.subst_C, map_add (f := _),
    PowerSeries.constantCoeff_subst_eq_zero hU _ hgc]
  simp

theorem cob_fLog {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    cob F (fLog g) = fLog (PowerSeries.subst F g) - fLog (at1 0 g) - fLog (at1 1 g) := by
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  simp only [cob, at1]
  rw [psubst_fLog hF hg, psubst_fLog (hX 0) hg, psubst_fLog (hX 1) hg]

theorem two_ne {ι : Type} : (2 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg MvPowerSeries.constantCoeff h
  have e2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries ι K) = 2 := map_ofNat _ 2
  rw [e2, map_zero] at h2
  exact two_ne_zero h2

end Alg

theorem BeESim_of (hG : GCob) (hL : LDiv) : BeESim := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨nu, hnuI, hnu0, hLT⟩ := hL K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hy, hcub, hx, -, -, hk⟩ := hT
  have hGC := hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hy hcub
  have hF0 := hF.1
  have hce : c0 - (xT + c0) = -xT := by ring
  have hn : ‖c0 - (xT + c0)‖ ≤ 1 := by rw [hce, norm_neg]; exact hx
  have hg : ep + PowerSeries.C (c0 - (xT + c0)) * PowerSeries.X ^ 2 = gT ep xT := by
    rw [hce, map_neg, gT]; ring
  have hD := (diffPh K g2 g3 s2 c0 (xT + c0) P l i ep F hP hcub hF hC).1
  obtain ⟨hw, hwI⟩ := wIntegral K c0 (xT + c0) P l i ep F hF hC hn
  rw [hg] at hD hw
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by
    rw [gT, map_sub, hC.2.1]; simp
  have hw0 : PowerSeries.constantCoeff (PowerSeries.subst l (wOf (xT + c0) P)) = 0 := by
    have := congrArg PowerSeries.constantCoeff hw
    rw [map_mul, hg0, mul_one] at this
    rw [this]; simp
  generalize PowerSeries.subst l (wOf (xT + c0) P) = wl at hGC hwI hw0
  generalize phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l = ph' at hD ⊢
  generalize 3 * (xT + c0) ^ 2 - g2 / 4 = kap at hGC hk
  generalize phO s2 P l = ph at hD ⊢
  generalize gT ep xT = g at hGC hD hg0
  obtain ⟨d, hd⟩ : ∃ d : MvPowerSeries (Fin 2) K,
      d = 1 - MvPowerSeries.C kap * at1 0 wl * at1 1 wl := ⟨_, rfl⟩
  rw [← hd, hLT] at hGC
  have hdI : Integral d := by
    rw [hd]
    exact ParE.integral_sub' Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_one'
      (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (ParE.integral_C' hk)
        (integral_series_at_variable 0 wl hwI)) (integral_series_at_variable 1 wl hwI))
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, map_mul, constantCoeff_series_at_variable 0 wl hw0]; simp
  have hFne : F ≠ 0 := by
    intro h
    have := law_coeff_single hF 0
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hmain : PowerSeries.subst F g * (nu * nu) = at1 0 g * at1 1 g * (d * d) := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hFne) ?_
    linear_combination hGC
  have cF := cc_psubst hF0 hg0
  have cA : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have cB : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have hlog := congrArg fLog hmain
  rw [ParO.fLog_mul cF (by rw [map_mul, hnu0, mul_one]), ParO.fLog_mul hnu0 hnu0,
    ParO.fLog_mul (by rw [map_mul, cA, cB, mul_one]) (by rw [map_mul, hd0, mul_one]),
    ParO.fLog_mul cA cB, ParO.fLog_mul hd0 hd0] at hlog
  have h2 : cob F (2 * (ph' - ph)) = 2 * (cob F ph' - cob F ph) := by
    rw [two_mul, cob_add hF0, cob_sub hF0]; ring
  have h3 := congrArg (cob F) hD
  rw [h2, cob_neg hF0, cob_fLog hF0 hg0] at h3
  have e : cob F ph' - cob F ph = fLog nu - fLog d := by
    refine mul_left_cancel₀ (two_ne (K := K)) ?_
    linear_combination h3 - hlog
  have s := (simeqInt K (Fin 2) _ _ _ _ (simeqLog K (Fin 2) nu hnu0 hnuI).1
    (simeqLog K (Fin 2) d hd0 hdI).1).1
  unfold Simeq at s ⊢
  rw [e]
  simpa using s

theorem cocycle_diff_exp_equiv : CocycleDiffExpEquiv := by
  intro K _ _ _ F H H' hF0 hFi hHH'
  obtain ⟨-, -, -, -, hsub⟩ := equivalence_rules K (Fin 2)
  obtain ⟨hrefl, hsymm, -, hadd, -⟩ := equivalence_rules K (Fin 3)
  have hneg : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a b → Simeq (-a) (-b) := by
    intro a b h
    have h' := hadd b a (-a - b) (-a - b) (hsymm a b h) (hrefl _)
    have e1 : b + (-a - b) = -a := by ring
    have e2 : a + (-a - b) = -b := by ring
    rwa [e1, e2] at h'
  have hsub' : ∀ a b c d : MvPowerSeries (Fin 3) K, Simeq a b → Simeq c d → Simeq (a - c) (b - d) := by
    intro a b c d h1 h2
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact hadd _ _ _ _ h1 (hneg _ _ h2)
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have iX : ∀ j : Fin 3, Integral (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) :=
    fun j => integral_mvPowerSeries_X j
  have c3 : MvPowerSeries.constantCoeff (in3 F) = 0 := Formalism.L2.Th1.B.E2.constantCoeff_law_first_two_of_three hF0
  have i3 : Integral (in3 F) := integral_subst_two_variables hFi _ _ (hX 0) (hX 1) (iX 0) (iX 1)
  unfold d1
  refine hsub' _ _ _ _ (hsub' _ _ _ _ ?_ ?_) ?_
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [c3, i3, hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]

theorem CubeE_of (hB : BeESim) (hD : CocycleDiffExpEquiv) : CubeE := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  intro ph'
  have hl0 : PowerSeries.constantCoeff l = 0 := hLaw.2.2.1
  have hcc : PowerSeries.constantCoeff ph' = 0 :=
    (phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l ph' hLaw hcc
  have hO := (first_level_all_formal_groups K g2 g3 s2 c0 a1 a3 P l i ep F hW hLaw hI hC hC3).2.2.1
  have hBE := hB K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  have hDD := hD K F _ _ hLaw.1 hLaw.2.1 hBE
  obtain ⟨-, -, htrans, -, -⟩ := equivalence_rules K (Fin 3)
  have h3 : Simeq (d1 F (cob F ph')) 0 := htrans _ _ _ hDD hO
  exact ⟨hdiv, hsw, h3, by rw [hsw]; exact h3⟩

end Formalism.L2.Th1.B.BeE
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.DivLaw
noncomputable section

namespace Formalism.L2.Th1.B.LDiv

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_mul' integral_one' integral_of_mul_eq_one)
open Formalism.L2.Th1.B.ParE (integral_add' integral_sub' integral_C')
open Formalism.G.LogP (hs2 subst2_subst subst_XX)

section Div

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem div_law {F G : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (hF : LawLog F l)
    (hi : IsInv l i) (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = F * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  have ii : Integral (at1 (0 : Fin 2) i) := integral_series_at_variable 0 i hi.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst
      ![at1 (0 : Fin 2) i, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] F := ⟨_, rfl⟩
  have cD : MvPowerSeries.constantCoeff D = 0 := by
    rw [hD]
    exact law_constantCoeff_subst2 F hF.1 _ _ ci c1
  have iD : Integral D := by
    rw [hD]
    exact integral_subst_two_variables hF.2.1 _ _ ci c1 ii i1
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), D] G := ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ c0 cD i0 iD
  have hH0 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0 := by
    have hb := hs2 c0 cz
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, 0] F] G
      = 0
    rw [law_right_zero hF _ ci]
    exact hd
  have hdvd : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis0 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 1 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 c0 hF.1
  refine ⟨MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H1,
    integral_subst_two_variables iH1 _ _ c0 hF.1 i0 hF.2.1, ?_⟩
  have e3 : MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F =
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
    refine law_eq_of_log hF _ _ _ ci hF.1 c1 ?_
    have e4 := law_subst hF (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (MvPowerSeries.X 1) c0 c1
    rw [subst_XX] at e4
    rw [e4, log_subst_formal_inverse hi 0]
    change -at1 0 l + (at1 0 l + _) = _
    rw [neg_add_cancel_left]
  have e2 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H = G := by
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F] G
      = G
    rw [e3]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl

end Div

theorem LDiv_of (hG : GCob) : LDiv := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hT1, hT2, nx, ny, na, -⟩ := hT
  have hep := hC.1
  have hep0 := hC.2.1
  have c0' : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1' : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)

  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hX3 : Integral (ι := Unit) (PowerSeries.X ^ 3 : PowerSeries K) := by
    rw [pow_succ]
    exact integral_mul' hX2 hX
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by simp [gT, hep0]
  have hgi : Integral (ι := Unit) (gT ep xT) :=
    integral_sub' hep (integral_mul' (integral_C' nx) hX2)
  have hinv : (gT ep xT)⁻¹ * gT ep xT = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hg0]; exact one_ne_zero)
  have hginv : Integral (ι := Unit) (gT ep xT)⁻¹ := integral_of_mul_eq_one hgi hg0 hinv
  have hth : Integral (ι := Unit) (thT ep xT yT) :=
    integral_mul' (integral_add' hep (integral_mul' (integral_C' ny) hX3)) hginv
  have hth0 : PowerSeries.constantCoeff (thT ep xT yT) = 1 := by
    have e := congrArg PowerSeries.constantCoeff hinv
    rw [map_mul, hg0, mul_one, map_one] at e
    unfold thT
    rw [map_mul, e]
    simp [hep0]
  have hL : Integral (LT ep xT yT a1) :=
    integral_sub' (integral_add' (integral_mul' i1 (integral_series_at_variable 0 _ hth))
      (integral_mul' i0 (integral_series_at_variable 1 _ hth)))
      (integral_mul' (integral_mul' (integral_C' na) i0) i1)

  have hb := hs2 c0' ci
  have eF : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] F = 0 := by
    refine law_eq_of_log hF _ _ 0 c0' ci cz ?_
    rw [law_subst_zero l hF.2.2.1, log_subst_formal_inverse hi 0]
    exact add_neg_cancel _
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] (LT ep xT yT a1) = 0 := by
    have e := congrArg (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i])
      (hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hT1 hT2)
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb,
      MvPowerSeries.subst_pow hb F, eF, psubst_msubst _ hF.1 hb, eF] at e
    have e5 : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (gT ep xT) ≠ 0 := by
      intro h
      rw [PowerSeries.subst_zero_eq_C_constantCoeff, hg0] at h
      simp at h
    rw [MvPowerSeries.subst_pow hb] at e
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul] at e
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h e5
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  obtain ⟨nu, hnu, e⟩ := div_law hF hi hL hd
  refine ⟨nu, hnu, ?_, e⟩

  have a0 : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 1 * n) =
      MvPowerSeries.constantCoeff n := by
    intro n
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (1 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1' : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 0 * n) = 0 := by
    intro n
    have hx : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 0 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  have h1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (LT ep xT yT a1) = 1 := by
    unfold LT
    have e6 : MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1 =
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * (MvPowerSeries.C a1 * MvPowerSeries.X 1) := by
      ring
    rw [e6, map_sub, map_add (f := _), a0, a1', a1', add_zero, sub_zero]
    exact (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (thT ep xT yT)
      (b := fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (fun _ => c0')).trans hth0
  have h2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (F * nu) =
      MvPowerSeries.constantCoeff nu := by
    classical
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
    simp [Finset.Nat.antidiagonal_succ, law_coeff_single hF 1, hF.1]
  rw [e, h2] at h1
  exact h1

end Formalism.L2.Th1.B.LDiv
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionCurveToSeries
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Crv2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS tS xPlus bridgeWp bridgeLaw
  bridgeCurve bridgeCurve3)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) :=
  (Formalism.L2.Th1.C.curveFrame K ⊤ W ⟨trivial, trivial, trivial, trivial, trivial⟩).1

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem twoHyp (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (hE : W.toAffine.Equation xT yT) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1)
    (hy : ‖yT‖ ≤ 1) : TwoHyp (g₂ W) (g₃ W) (W.b₂ / 12) W.a₁ W.a₃ xT yT :=
  ⟨h2, Crv.two_torsion_x_root_of_cubic W xT yT hE h2, hx, hy, hW.1, Crv.norm_kap W xT yT hW h2 hx hy⟩

end Norm

end Formalism.L2.Th1.B.Crv2
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoAdicScalarConditions
noncomputable section

namespace Formalism.L2.Th1.B.Van

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (IsLogPair mulBy EndInt PhNormAt IsBinomScalar FGInt LG)

theorem Th0Vanish_of (hC : CubeE) (hN : PhENorm) : ThetaZeroVanishing := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT al albar S P l linv i ep F ι _ xQ wp wm hP hL hI hlp hCu
    hCu3 hT hQ hFib hN1 hS hEnd hcl h0 hne h1 hb1 hb2
  have hl0 : PowerSeries.constantCoeff l = 0 := hL.2.2.1
  obtain ⟨hc0, hth⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0
  obtain ⟨-, -, hd1, -⟩ := hC K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hL hI hCu hCu3 hT
  obtain ⟨-, hFG, hF1⟩ := Formalism.L2.Th1.C.first_level_from_universal_law K F l linv _ hlp hL hc0 hd1
  have hPN := hN K g2 g3 s2 c0 xT al albar S P l linv i ep F ι xQ wp wm hP hT.2.1 hlp hCu
    hT.2.2.1 hQ hFib hN1 hS
  have hLG : LG (unitBall K) (phTw g2 s2 c0 xT P l) :=
    Split.split_vanishing_at_two K (unitBall K) (Formalism.L2.Th1.C.unitBallClosed K) l linv _ al albar
      ⟨hlp, hFG, hc0⟩ hF1 hEnd hcl hPN h0 hne h1 hb1 hb2
  have hth' : PowerSeries.subst l (thTw g2 s2 c0 xT P) = fExp (-phTw g2 s2 c0 xT P l) := hth
  have hneg : LG (unitBall K) (-phTw g2 s2 c0 xT P l) :=
    (Formalism.L2.Th1.C.lGSubgroup K (unitBall K) Unit).2.2 _ hLG
  refine ⟨?_, ?_, ?_⟩
  · refine (Formalism.L2.Th1.C.simeqIffCong K Unit _ _).2 ?_
    rw [Formalism.L2.Th1.C.Cong, sub_zero]
    exact hLG
  · rw [hth']
    exact constantCoeff_fExp hneg.1
  · rw [hth']
    exact hneg.2

section Two

variable {K : Type} [NormedField K] [NormedAlgebra ℚ_[2] K]

def phi (K : Type) [NormedField K] [NormedAlgebra ℚ_[2] K] : ℤ_[2] →+* K :=
  (algebraMap ℚ_[2] K).comp PadicInt.Coe.ringHom

theorem continuous_phi : Continuous (phi K) := by
  exact (continuous_algebraMap ℚ_[2] K).comp continuous_subtype_val

theorem phi_mem_closure (x : ℤ_[2]) : phi K x ∈ closure (Set.range (fun n : ℤ => (n : K))) := by
  have hd : DenseRange (Int.cast : ℤ → ℤ_[2]) := PadicInt.denseRange_intCast
  have h1 : x ∈ closure (Set.range (Int.cast : ℤ → ℤ_[2])) := by rw [hd.closure_eq]; trivial
  refine map_mem_closure continuous_phi h1 ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by rw [map_intCast]⟩

theorem phi_mem_of_closed {s : Set K} (hs : IsClosed s) (hn : ∀ n : ℤ, (n : K) ∈ s) (x : ℤ_[2]) :
    phi K x ∈ s := closure_minimal (Set.range_subset_iff.mpr hn) hs (phi_mem_closure x)

theorem phi_injective : Function.Injective (phi K) := (algebraMap ℚ_[2] K).injective.comp Subtype.val_injective

theorem phi_inv {x : ℤ_[2]} (hx : ‖x‖ = 1) : ∃ y : ℤ_[2], (phi K x)⁻¹ = phi K y := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr hx
  exact ⟨((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), by rw [map_units_inv]⟩

end Two

theorem norm_sub_eq_one {b b' : ℤ_[2]} (hb : ‖b‖ = 1) (hb' : ‖b'‖ < 1) : ‖b - b'‖ = 1 := by
  have h1 : ‖b - b'‖ ≤ max ‖b‖ ‖b'‖ := by
    have h3 := PadicInt.nonarchimedean b (-b')
    rwa [norm_neg, ← sub_eq_add_neg] at h3
  have h2 : ‖b‖ ≤ max ‖b - b'‖ ‖b'‖ := by
    have h3 := PadicInt.nonarchimedean (b - b') b'
    rwa [sub_add_cancel] at h3
  rw [hb] at h1 h2
  rcases le_total ‖b - b'‖ ‖b'‖ with h | h
  · rw [max_eq_right h] at h2
    linarith
  · rw [max_eq_left (by linarith)] at h1
    rw [max_eq_left h] at h2
    linarith

theorem endInt_int {K : Type} [Field K] (R : Subring K) {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by
  obtain ⟨-, -, h0, h1, hm, hadd, -⟩ := Formalism.L2.Th1.C.ptClosure K R l linv h hF
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    have := hadd _ _ ih h1
    simpa using this
  | pred n ih =>
    have := hadd _ _ ih hm
    simpa [sub_eq_add_neg] using this

theorem two_adic_scalar_conditions : TwoAdicScalars := by
  intro K _ _ _ _ F l linv b b' hL hlp hb hb' al albar
  have hcl := Formalism.L2.Th1.C.unitBallClosed K
  have hFG : FGInt (unitBall K) l linv := by
    rw [FGInt, ← Formalism.L2.Th1.C.Dict.law_eq hlp hL.1 hL.2.2.2.2]
    exact hL.2.1
  have hbin : ∀ x : ℤ_[2], IsBinomScalar (unitBall K) (phi K x) :=
    phi_mem_of_closed (Formalism.L2.Th1.C.binomClosed K (unitBall K) hcl)
      (Formalism.L2.Th1.C.intBinomScalar K (unitBall K))
  have hal : al = phi K b := rfl
  have halb : albar = phi K b' := rfl
  have h1b' : ‖(1 : ℤ_[2]) - b'‖ = 1 := norm_sub_eq_one norm_one hb'
  have hbb' : ‖b - b'‖ = 1 := norm_sub_eq_one hb hb'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact phi_mem_of_closed (Formalism.L2.Th1.C.endIntClosed K (unitBall K) hcl l linv hlp.1)
      (endInt_int (unitBall K) hlp hFG) b
  · exact phi_mem_closure b
  · rw [hal, ← map_zero (phi K)]
    intro h
    have := phi_injective h
    rw [this, norm_zero] at hb
    exact zero_ne_one hb
  · rw [hal, halb]
    intro h
    have := phi_injective h
    rw [this] at hb
    exact hb'.ne hb
  · rw [halb, ← map_one (phi K)]
    intro h
    have := phi_injective h
    rw [this, norm_one] at hb'
    exact lt_irrefl _ hb'
  · have e : al * (al - albar) = phi K (b * (b - b')) := by
      rw [hal, halb, map_mul, map_sub]
    obtain ⟨y, hy⟩ := phi_inv (K := K) (x := b * (b - b')) (by rw [norm_mul, hb, hbb', one_mul])
    rw [e, hy]
    exact hbin y
  · have e : al * (1 - albar) = phi K (b * (1 - b')) := by
      rw [hal, halb, map_mul, map_sub, map_one]
    obtain ⟨y, hy⟩ := phi_inv (K := K) (x := b * (1 - b')) (by rw [norm_mul, hb, h1b', one_mul])
    rw [e, hy]
    exact hbin y

end Formalism.L2.Th1.B.Van
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffQuotientXSq
noncomputable section

namespace Formalism.L2.Th1.B.SAdd

open Formalism.InvariantFactorPaths.G7 (at1)

section One

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

theorem eq_X_sq_mul_quotient {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0) :
    w = X ^ 2 * divByXSq w := by
  ext n
  rw [coeff_X_pow_mul']
  by_cases h : 2 ≤ n
  · rw [if_pos h, divByXSq, coeff_mk, Nat.sub_add_cancel h]
  · rw [if_neg h]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · rw [coeff_zero_eq_constantCoeff_apply, h0]
    · exact h1

theorem constantCoeff_quotient_X_sq {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (divByXSq w) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, divByXSq, coeff_mk, zero_add, h2]

theorem constantCoeff_half_log {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (C (1 / 2 : K) * fLog (divByXSq w)) = 0 := by
  have h : constantCoeff (fLog (divByXSq w)) = 0 := constantCoeff_fLog (constantCoeff_quotient_X_sq h2)
  rw [map_mul, h, mul_zero]

theorem sW_sq {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0)
    (h2 : coeff 2 w = 1) : sW w ^ 2 = w := by
  have hL := constantCoeff_half_log h2
  have hadd : C (1 / 2 : K) * fLog (divByXSq w) + C (1 / 2 : K) * fLog (divByXSq w) = fLog (divByXSq w) := by
    rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]
  have hE := fExp_add (K := K) (ι := Unit) hL hL
  rw [hadd, fExp_fLog (constantCoeff_quotient_X_sq h2)] at hE
  conv_rhs => rw [eq_X_sq_mul_quotient h0 h1, hE]
  rw [sW]
  ring

theorem constantCoeff_sW (w : PowerSeries K) : constantCoeff (sW w) = 0 := by
  rw [sW, map_mul, constantCoeff_X, zero_mul]

theorem coeff_one_sW {w : PowerSeries K} (h2 : coeff 2 w = 1) : coeff 1 (sW w) = 1 := by
  rw [sW, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  exact constantCoeff_fExp (constantCoeff_half_log h2)

theorem constantCoeff_dz_sW {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (dz (sW w)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, dz, coeff_derivative, zero_add, coeff_one_sW h2]
  simp

end One

theorem sigma_rules_hold : SRules := by
  intro K _ _ A kap w hw
  obtain ⟨hw1, -⟩ := wSecond K A kap w hw
  obtain ⟨hw0, hw2, hwE⟩ := hw
  have hsq := sW_sq hw0 hw1 hw2
  have hd : 2 * sW w * dz (sW w) = dz w := by
    rw [← dz_sq, hsq]
  have hwne : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw2
    exact zero_ne_one hw2
  have h4 : (4 : PowerSeries K) ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact absurd this (by norm_num)
  have hs1 : dz (sW w) ^ 2 = 1 + PowerSeries.C A * w + PowerSeries.C kap * w ^ 2 := by
    refine mul_left_cancel₀ (mul_ne_zero h4 hwne) ?_
    linear_combination (-4 * dz (sW w) ^ 2) * hsq + (2 * sW w * dz (sW w) + dz w) * hd + hwE
  have hds : dz (sW w) ≠ 0 := by
    intro h
    have := constantCoeff_dz_sW hw2
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨hsq, constantCoeff_sW w, coeff_one_sW hw2, hd, hs1, ?_⟩
  have h5 := congrArg dz hs1
  rw [dz_sq, dz_add, dz_add, dz_one, dz_mul, dz_mul, dz_C, dz_C, dz_sq] at h5
  refine mul_left_cancel₀ (mul_ne_zero two_ne hds) ?_
  linear_combination h5 - (PowerSeries.C A + 2 * PowerSeries.C kap * w) * hd

theorem eq_zero_of_shear {K : Type} [Field K] [CharZero K] {k : MvPowerSeries (Fin 2) K}
    (hk : pd 0 k = pd 1 k) (h0 : ev0 k = 0) : k = 0 := by
  have key : ∀ j : ℕ, ∀ n : Fin 2 →₀ ℕ, n 1 = j → MvPowerSeries.coeff n k = 0 := by
    intro j
    induction j with
    | zero => exact fun n hn => coeff_eq_zero_of_eval_second_zero h0 n hn
    | succ j ih =>
      intro n hn
      have hle : Finsupp.single (1 : Fin 2) 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      set m := n - Finsupp.single (1 : Fin 2) 1 with hm
      have hmn : m + Finsupp.single 1 1 = n := by
        rw [hm, tsub_add_cancel_of_le hle]
      have hm1 : m 1 = j := by simp [hm, hn]
      have e := congrArg (MvPowerSeries.coeff m) hk
      rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, hmn,
        ih (m + Finsupp.single 0 1) (by simp [hm1]), zero_mul] at e
      rcases mul_eq_zero.mp e.symm with h | h
      · exact h
      · exact absurd h (Nat.cast_add_one_ne_zero _)
  ext n
  rw [map_zero]
  exact key _ n rfl

theorem shear_two_variables_holds : ShearTwo := by
  intro K _ _ h hh
  have hk : pd 0 (h - atS (ev0 h)) = pd 1 (h - atS (ev0 h)) := by
    rw [Add1.pd_sub, Add1.pd_sub, pd_atS, pd_atS, hh]
  have h0 : ev0 (h - atS (ev0 h)) = 0 := by
    rw [eval_second_zero_sub, eval_second_zero_at_sum, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_shear hk h0)

section Two

variable {K : Type} [Field K] [CharZero K]

theorem eval_second_zero_one : ev0 (1 : MvPowerSeries (Fin 2) K) = 1 := by
  rw [eval_second_zero_eq_algHom, map_one]

theorem atS_sq (f : PowerSeries K) : atS (f ^ 2) = atS f ^ 2 := by
  have hs : PowerSeries.HasSubst
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [atS, atS, ← PowerSeries.coe_substAlgHom hs, map_pow]

theorem shear_alg {R : Type} [CommRing R] (k a x y x1 y1 : R)
    (hx : x1 ^ 2 = 1 + a * x ^ 2 + k * (x ^ 2) ^ 2)
    (hy : y1 ^ 2 = 1 + a * y ^ 2 + k * (y ^ 2) ^ 2) :
    (1 - k * x ^ 2 * y ^ 2) *
        (y * ((a + 2 * k * x ^ 2) * x) - x * ((a + 2 * k * y ^ 2) * y)) =
      (x * y1 + y * x1) *
        (-(k * (2 * x * x1) * y ^ 2) + k * x ^ 2 * (2 * y * y1)) := by
  linear_combination (2 * k * x * y * y ^ 2) * hx - (2 * k * x * y * x ^ 2) * hy

end Two

theorem sigma_addition_holds : SAdd := by
  intro K _ _ A kap w hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sigma_rules_hold K A kap w hw
  obtain ⟨hw0, hw2, -⟩ := hw
  have E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2 := by
    intro i
    have := congrArg (at1 i) h1
    simpa only [Add1.triple_lintegral_eq, map_pow] using this.symm
  have E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w)) := by
    intro i
    have := congrArg (at1 i) h4
    simpa only [Add1.triple_lintegral_eq, map_mul, map_ofNat] using this.symm
  have E5 : ∀ i : Fin 2, at1 i (dz (sW w)) ^ 2 =
      1 + MvPowerSeries.C A * at1 i (sW w) ^ 2 + MvPowerSeries.C kap * (at1 i (sW w) ^ 2) ^ 2 := by
    intro i
    have := congrArg (at1 i) h5
    rw [← E1]
    simpa only [Add1.triple_lintegral_eq, map_pow, map_add (f := _), map_mul, map_one, Add1.inVarAlgHom_C] using this
  have E6 : ∀ i : Fin 2, at1 i (dz (dz (sW w))) =
      (MvPowerSeries.C A + 2 * MvPowerSeries.C kap * at1 i (sW w) ^ 2) * at1 i (sW w) := by
    intro i
    have := congrArg (at1 i) h6
    rw [← E1]
    simpa only [Add1.triple_lintegral_eq, map_add (f := _), map_mul, map_ofNat, Add1.inVarAlgHom_C] using this
  set d : MvPowerSeries (Fin 2) K := 1 - MvPowerSeries.C kap * at1 0 w * at1 1 w with hd
  set n : MvPowerSeries (Fin 2) K :=
    at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w)) with hn
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, Add1.constantCoeff_inVar_eq_zero 1 hw0, mul_zero, map_one, sub_zero]
  have hdne : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd0
    exact zero_ne_one hd0
  have hdi : d⁻¹ * d = 1 := MvPowerSeries.inv_mul_cancel d (by rw [hd0]; exact one_ne_zero)
  have hhd : n * d⁻¹ * d = n := by rw [mul_assoc, hdi, mul_one]
  have n01 : (1 : Fin 2) ≠ 0 := by decide
  have n10 : (0 : Fin 2) ≠ 1 := by decide
  have pn0 : pd 0 n = at1 1 (dz (sW w)) * at1 0 (dz (sW w)) +
      at1 1 (sW w) * at1 0 (dz (dz (sW w))) := by
    rw [hn, pd, map_add (f := _)]
    change pd 0 _ + pd 0 _ = _
    rw [Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01, pderiv_at_variable_of_ne n01]
    ring
  have pn1 : pd 1 n = at1 0 (sW w) * at1 1 (dz (dz (sW w))) +
      at1 0 (dz (sW w)) * at1 1 (dz (sW w)) := by
    rw [hn, pd, map_add (f := _)]
    change pd 1 _ + pd 1 _ = _
    rw [Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10, pderiv_at_variable_of_ne n10]
    ring
  have pC : ∀ i : Fin 2, pd i (MvPowerSeries.C kap : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.pderiv_C
  have p1 : ∀ i : Fin 2, pd i (1 : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.pderiv_one
  have pd0 : pd 0 d = -(MvPowerSeries.C kap * at1 0 (dz w) * at1 1 w) := by
    rw [hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01]
    ring
  have pd1 : pd 1 d = -(MvPowerSeries.C kap * at1 0 w * at1 1 (dz w)) := by
    rw [hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10]
    ring
  have halg : d * (pd 0 n - pd 1 n) = n * (pd 0 d - pd 1 d) := by
    have := shear_alg (MvPowerSeries.C kap) (MvPowerSeries.C A) (at1 0 (sW w)) (at1 1 (sW w))
      (at1 0 (dz (sW w))) (at1 1 (dz (sW w))) (E5 0) (E5 1)
    rw [pn0, pn1, pd0, pd1, hd, hn, E6, E6, E4, E4, E1, E1]
    linear_combination this
  have q0 := congrArg (pd 0) hhd
  have q1 := congrArg (pd 1) hhd
  rw [Add1.pd_mul] at q0 q1
  have hsh : pd 0 (n * d⁻¹) = pd 1 (n * d⁻¹) := by
    refine sub_eq_zero.mp ?_
    refine (mul_eq_zero.mp (?_ : (d * d) * (pd 0 (n * d⁻¹) - pd 1 (n * d⁻¹)) = 0)).resolve_left
      (mul_ne_zero hdne hdne)
    linear_combination d * q0 - d * q1 + halg - (pd 0 d - pd 1 d) * hhd
  have hS := shear_two_variables_holds K (n * d⁻¹) hsh
  have hev : ev0 (n * d⁻¹) = sW w := by
    have e := congrArg ev0 hhd
    have ed : ev0 d = 1 := by
      rw [hd, eval_second_zero_sub, evalYZero_mul, restrictSecondZero_inVar_one, hw0, map_zero, mul_zero, eval_second_zero_one, sub_zero]
    have en : ev0 n = sW w := by
      rw [hn, evalYZero_add, evalYZero_mul, evalYZero_mul, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, restrictSecondZero_inVar_one, h2,
        constantCoeff_dz_sW hw2, map_zero, map_one, mul_one, zero_mul, add_zero]
    rwa [evalYZero_mul, ed, mul_one, en] at e
  rw [hev] at hS
  rw [← hS, hhd]

theorem weierstrass_addition_holds : WAdd := by
  intro K _ _ A kap w hw
  have H := sigma_addition_holds K A kap w hw
  obtain ⟨h1, -, -, h4, -, -⟩ := sigma_rules_hold K A kap w hw
  have E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2 := by
    intro i
    have := congrArg (at1 i) h1
    simpa only [Add1.triple_lintegral_eq, map_pow] using this.symm
  have E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w)) := by
    intro i
    have := congrArg (at1 i) h4
    simpa only [Add1.triple_lintegral_eq, map_mul, map_ofNat] using this.symm
  have ES : atS w = atS (sW w) ^ 2 := by rw [← atS_sq, h1]
  rw [E1, E1] at H
  rw [ES, E4, E4, E1, E1]
  linear_combination (4 * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2 *
    (atS (sW w) * (1 - MvPowerSeries.C kap * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2) +
      (at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w))))) * H

end Formalism.L2.Th1.B.SAdd
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalE
namespace Formalism.L2.Th1.B

theorem wAdd : WAdd := SAdd.weierstrass_addition_holds
theorem wPrimeU : WPrimeU := GCob.weierstrass_derivative_unit_holds
theorem gCob : GCob := GCob.GCob_of wAdd wPrimeU
theorem lDiv : LDiv := LDiv.LDiv_of gCob
theorem beESim : BeESim := BeE.BeESim_of gCob lDiv
theorem first_cocycle_simeq_zero : CocycleDiffExpEquiv := BeE.cocycle_diff_exp_equiv
theorem cubeE : CubeE := BeE.CubeE_of beESim first_cocycle_simeq_zero

end Formalism.L2.Th1.B
end

namespace Formalism.L2.Th1.B

theorem th0Isogeny : Th0Isogeny := Iso.theta_zero_isogeny_holds
theorem phENorm : PhENorm := Nrm.PhENorm_of th0Isogeny
theorem th0Vanish : ThetaZeroVanishing := Van.Th0Vanish_of cubeE phENorm
theorem twoAdicScalars : TwoAdicScalars := Van.two_adic_scalar_conditions

end Formalism.L2.Th1.B
