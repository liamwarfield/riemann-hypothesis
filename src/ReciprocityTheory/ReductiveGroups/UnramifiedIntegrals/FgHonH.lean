module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SubstOfLog

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonF
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem HD.map_frobenius_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map (σ.comp σ) lam) (MvPowerSeries.map (σ.comp σ) Φ)
      (PowerSeries.map (σ.comp σ) A) a := by
  have hτa : (σ.comp σ) a = a := h.a_sq
  have e := congrArg (PowerSeries.map (σ.comp σ)) h.Alog
  rw [map_mul, PowerSeries.map_C, hτa] at e
  have e2 := congrArg (MvPowerSeries.map (σ.comp σ)) h.log
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, h.a_ne, h.a_sq⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, map_zero]
  · rw [PowerSeries.coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact (integralMv_iff_divBy_one Φ).mp h.Φint d
  · have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    unfold atX atY at e2 ⊢
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0), map_add (f := _),
      PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), MvPowerSeries.map_X,
      MvPowerSeries.map_X] at e2
    exact e2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.A0, map_zero]
  · unfold IntegralPS
    intro n
    rw [PowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact h.Aint n
  · have e' : MvPowerSeries.map (σ.comp σ) (lam.subst A) = C a * PowerSeries.map (σ.comp σ) lam := e
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h.A0)] at e'
    exact e'

theorem HD.map_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by
  induction i with
  | zero =>
    simp only [pow_zero, RingHom.one_def, MvPowerSeries.map_id, PowerSeries.map_id, RingHom.id_apply]
    exact h
  | succ i ih =>
    have h1 := HD.map_frobenius_sq hF ih
    simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
      RingHom.comp_apply]
    exact h1

theorem honF_subst_subst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem honF_integral_subst {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS (f.subst g) :=
  (integralPS_iff_mv _).mpr (integralMv_subst hf hg0 ((integralPS_iff_mv g).mp hg))

theorem hon_mu (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by
  have hl := hF.prime
  have hl1 := hF.norm_l
  have hlam' : IntegralPS (PowerSeries.derivative lam) := h.toLawD.deriv_integral
  have h' := h.map_frobenius_sq hF
  have Hh : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh1.g0
  have HΦ' : PowerSeries.HasSubst (MvPowerSeries.map (σ.comp σ) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h'.Φ0
  have HA' : PowerSeries.HasSubst (PowerSeries.map (σ.comp σ) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h'.A0
  have HA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' h.A0
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hXq0 : constantCoeff ((X : PowerSeries K) ^ (l ^ 2)) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have HXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXq0
  have hX0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have HX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (hX0 i)
  have hp0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (![atX hh, atY hh] i) = 0 := by
    intro i
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 0) hh hh1.g0
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 1) hh hh1.g0
  have hpI : ∀ i : Fin 2, IntegralMv (![atX hh, atY hh] i) := by
    intro i
    fin_cases i
    · exact integralMv_subst hh1.gInt (hX0 0) (integralMv_X 0)
    · exact integralMv_subst hh1.gInt (hX0 1) (integralMv_X 1)
  have Hp : MvPowerSeries.HasSubst ![atX hh, atY hh] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hp0
  refine ⟨⟨PowerSeries.constantCoeff_subst_eq_zero hh1.g0 lam h.lam0, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [derivative_subst Hh]
    exact integralPS_mul (honF_integral_subst hlam' hh1.g0 hh1.gInt) (integralPS_derivative hh1.gInt)
  · have key := qls hl hl1 lam h.lam0 hlam' (hh.subst (MvPowerSeries.map (σ.comp σ) Φ))
      (Φ.subst ![atX hh, atY hh])
      (PowerSeries.constantCoeff_subst_eq_zero h'.Φ0 hh hh1.g0)
      (MvPowerSeries.constantCoeff_subst_eq_zero Hp hp0 h.Φ0)
      (integralMv_subst hh1.gInt h'.Φ0 h'.Φint) (integralMv_subst2 h.Φint hp0 hpI) hh1.add
    have ex : atX (lam.subst hh) = lam.subst (atX hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 0) lam
    have ey : atY (lam.subst hh) = lam.subst (atY hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 1) lam
    have ax : (atX lam).subst ![atX hh, atY hh] = lam.subst (atX hh) :=
      (honF_subst_subst lam (hX0 0) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have ay : (atY lam).subst ![atX hh, atY hh] = lam.subst (atY hh) :=
      (honF_subst_subst lam (hX0 1) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have e1 : lam.subst (Φ.subst ![atX hh, atY hh]) = atX (lam.subst hh) + atY (lam.subst hh) := by
      rw [ex, ey, ← honF_subst_subst lam h.Φ0 Hp, h.log, MvPowerSeries.subst_add Hp, ax, ay]
    rw [e1] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HΦ', sub_sub]
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' (hh.subst (PowerSeries.map (σ.comp σ) A))
      (A.subst hh) (PowerSeries.constantCoeff_subst_eq_zero h'.A0 hh hh1.g0)
      (PowerSeries.constantCoeff_subst_eq_zero hh1.g0 A h.A0)
      (honF_integral_subst hh1.gInt h'.A0 h'.Aint) (honF_integral_subst h.Aint hh1.g0 hh1.gInt) hh1.eig
    rw [← PowerSeries.subst_comp_subst_apply HA Hh, h.Alog, PowerSeries.subst_mul Hh,
      PowerSeries.subst_C] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HA']
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' e (hh.subst ((X : PowerSeries K) ^ (l ^ 2))) he0
      (PowerSeries.constantCoeff_subst_eq_zero hXq0 hh hh1.g0) he
      (honF_integral_subst hh1.gInt hXq0 (integralPS_pow integralPS_X _)) hh2
    rw [hlog] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HXq]
    exact key
  · rw [Formalism.LT.PadicP.coeff_one_subst lam hh h.lam0 hh1.g0, h.lam1, one_mul]

theorem lemmaQ_tw (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) {D : PowerSeries K}
    (hD : QCls l (MvPowerSeries.map ((σ.comp σ) ^ i) Φ) (PowerSeries.map ((σ.comp σ) ^ i) A) a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
        (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * PowerSeries.map ((σ.comp σ) ^ i) lam
        - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  obtain ⟨Dp, hDp, hdiv⟩ := lemmaQ hF (HD.map_sq hF h i) hD
  refine ⟨Dp, ?_, hdiv⟩
  simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
    RingHom.comp_apply]
  exact hDp

theorem hon_series (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : ℕ → K, ‖c 0‖ = 1 ∧ (∀ i, ‖c i‖ ≤ 1) ∧ ∀ N : ℕ, ∃ R : PowerSeries K,
      constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam).subst
              ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1)))) := by
  obtain ⟨hh, hhom, hdiv, hc1⟩ := hon_shape hF h he0 he hlog
  obtain ⟨hQ, hmod, hcoef⟩ := hon_mu hF h he0 he hlog hhom hdiv
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hQ' : QCls l (MvPowerSeries.map ((σ.comp σ) ^ (0 + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (0 + 1)) A) a (lam.subst hh) := by
    simpa using hQ

  let seq : (i : ℕ) → {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D} := fun i =>
    Nat.rec (motive := fun i => {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D}) ⟨lam.subst hh, hQ'⟩
      (fun i D => ⟨Classical.choose (lemmaQ_tw hF h (i + 1) D.2),
        (Classical.choose_spec (lemmaQ_tw hF h (i + 1) D.2)).1⟩) i
  have hstep : ∀ i, DivBy (l : K) ((seq i).1 - C (coeff 1 (seq i).1) *
      PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam - (seq (i + 1)).1.subst ((X : PowerSeries K) ^ (l ^ 2))) :=
    fun i => (Classical.choose_spec (lemmaQ_tw hF h (i + 1) (seq i).2)).2

  have hsub : ∀ m : ℕ, m ≠ 0 → PowerSeries.HasSubst ((X : PowerSeries K) ^ m) := fun m hm =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hm])
  have hcomp : ∀ (f : PowerSeries K) (m q : ℕ), m ≠ 0 → q ≠ 0 →
      PowerSeries.subst ((X : PowerSeries K) ^ m) (f.subst ((X : PowerSeries K) ^ q) : PowerSeries K) =
        f.subst ((X : PowerSeries K) ^ (m * q)) := by
    intro f m q hm hq
    rw [PowerSeries.subst_comp_subst_apply (hsub q hq) (hsub m hm)]
    congr 1
    rw [← PowerSeries.coe_substAlgHom (hsub m hm), map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (hsub m hm), ← pow_mul]
  refine ⟨fun i => coeff 1 (seq i).1, ?_, fun i => (seq i).2.norm_coeff_one,
    fun N => ⟨(seq N).1, (seq N).2.D0, ?_⟩⟩
  · show ‖coeff 1 (lam.subst hh)‖ = 1
    rw [hcoef, hc1]
    exact hon_level hF h he0 he hlog hlev
  · induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, pow_one]
      exact hmod
    | succ N ih =>
      have hm : (l ^ 2) ^ (N + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl0)
      have h1 := (divBy_expand_iff (l : K) ((l ^ 2) ^ (N + 1)) hm _).2 (hstep N)
      rw [← PowerSeries.coe_substAlgHom (hsub _ hm), map_sub, map_sub, ← PowerSeries.smul_eq_C_mul,
        map_smul, PowerSeries.smul_eq_C_mul, PowerSeries.coe_substAlgHom, hcomp _ _ _ hm (pow_ne_zero _ hl0), ← pow_succ] at h1
      have := divBy_add ih h1
      convert this using 1
      simp only [Finset.sum_range_succ]
      ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonG
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

def triSol {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) : ℕ → K
  | m => (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m

theorem triSol_eq {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) (ha : ∀ m, a m m ≠ 0)
    (m : ℕ) : ∑ i ∈ Finset.range (m + 1), triSol a b i * a i m = b m := by
  have h : triSol a b m = (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m := by
    rw [triSol]
  rw [Finset.sum_range_succ, Finset.sum_range, h, div_mul_cancel₀ _ (ha m)]
  ring

theorem triSol_norm (a : ℕ → ℕ → K) (b : ℕ → K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (r : ℝ) (hb : ∀ m, ‖b m‖ ≤ r) (m : ℕ) : ‖triSol a b m‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans (hb 0)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [triSol, norm_div, ha, div_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb m) ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i _ => ?_
    rw [norm_mul]
    calc ‖triSol a b i.1‖ * ‖a i.1 m‖ ≤ r * 1 :=
          mul_le_mul (ih i.1 i.2) (ha1 _ _) (norm_nonneg _) hr
      _ = r := mul_one r

theorem norm_pow_apply_of_isometric (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

def triIter {K : Type} [Field K] (a : ℕ → ℕ → K) (π : K) : ℕ → ℕ → K
  | 0 => triSol a (fun m => if m = 0 then a 0 0 else 0)
  | k + 1 => triSol a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1))

theorem triIter_norm (a : ℕ → ℕ → K) (π : K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (k m : ℕ) : ‖triIter a π k m‖ ≤ ‖π‖ ^ k := by
  induction k generalizing m with
  | zero =>
    rw [triIter, pow_zero]
    refine triSol_norm a _ ha1 ha 1 (fun j => ?_) m
    split_ifs
    · exact ha1 0 0
    · simp
  | succ k ih =>
    rw [triIter]
    refine triSol_norm a _ ha1 ha _ (fun j => ?_) m
    split_ifs
    · simp
    · rw [norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)

theorem twisted_division (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (hπ : ‖π‖ < 1)
    (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  set a : ℕ → ℕ → K := fun i m => (τ ^ i) (c (m - i)) with ha_def
  have ha1 : ∀ i m, ‖a i m‖ ≤ 1 := fun i m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ]; exact hc _
  have ha : ∀ m, ‖a m m‖ = 1 := fun m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ, Nat.sub_self]; exact hc0
  have ha0 : ∀ m, a m m ≠ 0 := fun m h => by
    have := ha m; rw [h, norm_zero] at this; exact zero_ne_one this
  have hsum : ∀ m, Summable fun k => triIter a π k m := fun m =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      (fun k => triIter_norm a π ha1 ha k m)
  have hz0 : triIter a π 0 0 = 1 := by
    have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact mul_right_cancel₀ (ha0 0) (h.trans (one_mul _).symm)
  have hzs : ∀ k, triIter a π (k + 1) 0 = 0 := fun k => by
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact (mul_eq_zero.mp h).resolve_right (ha0 0)
  refine ⟨fun m => ∑' k, triIter a π k m, ?_, fun n => ?_, fun n hn => ?_⟩
  · simp only
    rw [(hsum 0).tsum_eq_zero_add, hz0]
    simp [hzs]
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
    exact (triIter_norm a π ha1 ha k n).trans (pow_le_one₀ (norm_nonneg _) hπ.le)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hterm : ∀ i, (∑' k, triIter a π k i) * (τ ^ i) (c (m + 2 - 1 - i))
        = ∑' k, triIter a π k i * a i (m + 1) := fun i => by
      rw [tsum_mul_right]
      rfl
    simp only [hterm]
    rw [← Summable.tsum_finsetSum (fun i _ => (hsum i).mul_right _)]
    have hS : Summable fun k => ∑ i ∈ Finset.range (m + 2), triIter a π k i * a i (m + 1) :=
      summable_sum fun i _ => (hsum i).mul_right _
    rw [hS.tsum_eq_zero_add, ← tsum_mul_left]
    have h0 : ∑ i ∈ Finset.range (m + 2), triIter a π 0 i * a i (m + 1) = 0 := by
      have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 (m + 1)
      simpa [triIter] using h
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 (m + 1)
    simpa [triIter] using h.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Regroup

variable {K : Type} [Field K]

theorem hon_regroup (τ : K →+* K) (π : K) (c t w : ℕ → K) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ m, M ≤ m → w m = 0) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) :
    ∑ i ∈ Finset.range M, t i * (π * w i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * w (i + j + 1))
      = π * w 0 - (c 0 - π * t 1) * w 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', M = K' + 1 := ⟨M - 1, by omega⟩

  have hS : ∑ i ∈ Finset.range (K' + 1), ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
      = ∑ n ∈ Finset.range (K' + 1), w (n + 1) * ∑ i ∈ Finset.range (n + 1), t i * (τ ^ i) (c (n - i)) := by
    have hA : ∀ i ∈ Finset.range (K' + 1),
        ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
          = ∑ j ∈ Finset.range (K' + 1 - i), t i * (τ ^ i) (c j) * w (i + j + 1) := by
      intro i _
      symm
      refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
        fun j _ hj => ?_
      simp only [Finset.mem_range, not_lt] at hj
      rw [hw _ (by omega), mul_zero]
    rw [Finset.sum_congr rfl hA]
    have hflip := Finset.sum_range_diag_flip (K' + 1)
      (fun i j => t i * (τ ^ i) (c j) * w (i + j + 1))
    beta_reduce at hflip
    rw [← hflip]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have e : i + (n - i) + 1 = n + 1 := by omega
    rw [e]
    ring
  have hsplit : ∀ i, t i * (π * w i - ∑ j ∈ Finset.range (K' + 1), (τ ^ i) (c j) * w (i + j + 1))
      = π * (t i * w i) - ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1) := by
    intro i
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hF : ∀ n ∈ Finset.range K',
      w (n + 1 + 1) * ∑ i ∈ Finset.range (n + 1 + 1), t i * (τ ^ i) (c (n + 1 - i))
        = π * (t (n + 1 + 1) * w (n + 1 + 1)) := by
    intro n _
    have h2 := ht (n + 1 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h2
    rw [← mul_assoc, h2]
    ring
  have hF0 : w (0 + 1) * ∑ i ∈ Finset.range (0 + 1), t i * (τ ^ i) (c (0 - i)) = c 0 * w 1 := by
    simp [ht0] <;> ring
  have htel := Finset.sum_range_sub' (fun m => t (m + 1) * w (m + 1)) K'
  beta_reduce at htel
  rw [Finset.sum_sub_distrib, zero_add] at htel
  have hwM : w (K' + 1) = 0 := hw _ le_rfl
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib, ← Finset.mul_sum, hS,
    Finset.sum_range_succ', Finset.sum_range_succ']
  try beta_reduce
  rw [Finset.sum_congr rfl hF, ← Finset.mul_sum, hF0, ht0]
  linear_combination π * htel - π * t (K' + 1) * hwM

end Regroup

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem hon_lt_sq_pow (hl : 2 ≤ l) (n : ℕ) : n < (l ^ 2) ^ n := by
  have h4 : 1 < l ^ 2 := by nlinarith
  first
  | exact Nat.lt_pow_self h4
  | exact Nat.lt_pow_self h4 n

private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]

theorem hon_series_coeff (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K)
    (h : ∀ N : ℕ, ∃ R : PowerSeries K, constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1))))) (n : ℕ) :
    ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨R, hR0, hR⟩ := h n
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hRn : coeff n (R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (n + 1)))) = 0 := by
    rw [coeff_subst_X_pow_eq_ite_dvd' R (pow_ne_zero _ hq)]
    split_ifs
    · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (hon_lt_sq_pow hl n)
          (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) (Nat.le_succ n))),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0]
    · rfl
  have hsum : coeff n (∑ i ∈ Finset.range n, C (c i) *
        (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1))))
      = ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
          c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, coeff_subst_X_pow_eq_ite_dvd' _ (pow_ne_zero _ hq)]
    split_ifs
    · rw [PowerSeries.coeff_map]
    · rw [mul_zero]
  unfold DivBy at hR
  have hcoef := hR n
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, hsum, hRn, sub_zero] at hcoef
  exact hcoef

def twC (l : ℕ) (τ : K →+* K) (lam : PowerSeries K) (n m : ℕ) : K :=
  if (l ^ 2) ^ m ∣ n then (τ ^ m) (coeff (n / (l ^ 2) ^ m) lam) else 0

theorem twC_zero (τ : K →+* K) (n : ℕ) : twC l τ lam n 0 = coeff n lam := by
  simp [twC]

theorem twC_one (τ : K →+* K) (n : ℕ) :
    twC l τ lam n 1 = if l ^ 2 ∣ n then τ (coeff (n / l ^ 2) lam) else 0 := by
  simp [twC]

theorem twC_eq_zero (hl : 2 ≤ l) (τ : K →+* K) (h0 : constantCoeff lam = 0) {n m : ℕ}
    (hnm : n ≤ m) : twC l τ lam n m = 0 := by
  unfold twC
  split_ifs with hd
  · have hlt : n < (l ^ 2) ^ m := lt_of_le_of_lt hnm (hon_lt_sq_pow hl m)
    rw [Nat.div_eq_of_lt hlt, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rfl

theorem twC_shift (τ : K →+* K) {n i : ℕ} (hd : (l ^ 2) ^ i ∣ n) (j : ℕ) :
    (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) j) = twC l τ lam n (i + j) := by
  unfold twC
  simp only [pow_add, RingHom.mul_def, RingHom.comp_apply, Nat.dvd_div_iff_mul_dvd hd,
    Nat.div_div_eq_div_mul]
  split_ifs <;> simp

theorem twC_of_not_dvd (τ : K →+* K) {n i : ℕ} (hd : ¬ (l ^ 2) ^ i ∣ n) (j : ℕ) :
    twC l τ lam n (i + j) = 0 := by
  unfold twC
  rw [if_neg]
  intro h
  exact hd (dvd_trans (pow_dvd_pow _ (Nat.le_add_right i j)) h)

theorem hon_norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

theorem hon_coeff_unif (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K) (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M) :
    ‖(l : K) * coeff n lam - ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1)‖ ≤ ‖(l : K)‖ := by
  have h1 : ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)
      = ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold twC
    split_ifs <;> simp
  have h2 : ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1)
      = ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1) := by
    refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
      fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [twC_eq_zero hl τ h0 (by omega), mul_zero]
  rw [← h2, ← h1]
  exact E n

theorem hon_coeff_shift (hl : 2 ≤ l) (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (c : ℕ → K)
    (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M)
    (i : ℕ) :
    ‖(l : K) * twC l τ lam n i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * twC l τ lam n (i + j + 1)‖
      ≤ ‖(l : K)‖ := by
  by_cases hd : (l ^ 2) ^ i ∣ n
  · have e1 : twC l τ lam n i = (τ ^ i) (coeff (n / (l ^ 2) ^ i) lam) := by
      rw [← twC_zero (l := l) τ (n / (l ^ 2) ^ i), twC_shift τ hd 0, add_zero]
    have e2 : ∀ j, twC l τ lam n (i + j + 1) = (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) (j + 1)) := by
      intro j
      rw [twC_shift τ hd (j + 1), add_assoc]
    have hn' : n / (l ^ 2) ^ i ≤ M := le_trans (Nat.div_le_self _ _) hM
    have key := hon_coeff_unif hl τ c h0 E hn'
    rw [← hon_norm_pow_apply τ hτ i] at key
    convert key using 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_mul, map_natCast, e1, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, e2]
  · have e1 : twC l τ lam n i = 0 := by simpa using twC_of_not_dvd (lam := lam) τ hd 0
    have e2 : ∀ j, twC l τ lam n (i + j + 1) = 0 := fun j => by
      rw [add_assoc]
      exact twC_of_not_dvd τ hd (j + 1)
    simp only [e1, e2, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
    exact norm_nonneg _

theorem hon_main (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : K, ‖c‖ = 1 ∧ IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl : 2 ≤ l := hF.prime.two_le
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨c, hc0, hc, hN⟩ := hon_series hF h he0 he hlog hlev
  have hτ : ∀ x, ‖(σ.comp σ) x‖ = ‖x‖ := fun x => (hF.isom _).trans (hF.isom x)
  obtain ⟨t, ht0, htn, ht⟩ := twisted_division (σ.comp σ) hτ (l : K) hF.norm_l c hc0 hc
  have E := hon_series_coeff hl (σ.comp σ) c hN
  have hlt : ‖(l : K) * t 1‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (htn 1)).trans_lt hF.norm_l
  refine ⟨c 0 - (l : K) * t 1, ?_, fun n => ?_⟩
  · rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, hc0]; exact hlt.ne'), norm_neg, hc0]
    exact max_eq_left hlt.le
  · have key := hon_regroup (σ.comp σ) (l : K) c t (twC l (σ.comp σ) lam n) (n + 1) (by omega)
      (fun m hm => twC_eq_zero hl _ h.lam0 (by omega)) ht0 ht
    have bd : ‖(l : K) * twC l (σ.comp σ) lam n 0
        - (c 0 - (l : K) * t 1) * twC l (σ.comp σ) lam n 1‖ ≤ ‖(l : K)‖ := by
      rw [← key]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
      rw [norm_mul]
      exact (mul_le_mul (htn i) (hon_coeff_shift hl _ hτ c h.lam0 E (Nat.le_succ n) i)
        (norm_nonneg _) zero_le_one).trans (one_mul _).le
    rw [twC_zero, twC_one] at bd
    rw [map_sub, coeff_smul, coeff_subst_X_pow (pow_ne_zero _ (by omega)), smul_eq_mul]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have : coeff n lam - (c 0 - (l : K) * t 1) / (l : K) *
        (if l ^ 2 ∣ n then coeff (n / l ^ 2) (PowerSeries.map (σ.comp σ) lam) else 0)
        = ((l : K) * coeff n lam - (c 0 - (l : K) * t 1) *
          (if l ^ 2 ∣ n then (σ.comp σ) (coeff (n / l ^ 2) lam) else 0)) / (l : K) := by
      rw [coeff_map]; field_simp
    rw [this, norm_div]
    exact div_le_one_of_le₀ bd (norm_nonneg _)

end ReciprocityTheory.ChartRestriction.L1
