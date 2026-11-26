module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem coeC (z : Om l) : (z : ℂ_[l]) = algebraMap (Om l) ℂ_[l] z := rfl

theorem norm_l_C : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]

theorem norm_l_Om : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.norm_extends l (l : Om l), coeC, map_natCast, norm_l_C]

theorem norm_OC_le (x : OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_pi_lt {K : FinExt l} (bk : BK K) : ‖((Per.θ l (bk.ev X) : OC l) : ℂ_[l])‖ < 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  set φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom) with hφ
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  have hπ1 : ‖π‖ ≤ 1 := norm_OC_le _
  have h0 : bk.Ep.eval₂ φ π = 0 := by
    have h1 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    have h2 := congrArg (PadicComplexInt l).toSubring.subtype h1
    change (PadicComplexInt l).toSubring.subtype (Per.θ l (bk.ev (bk.Ep : (Wq l bk.a)⟦X⟧))) =
      (PadicComplexInt l).toSubring.subtype 0 at h2
    rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.hom_eval₂, Polynomial.hom_eval₂,
      Polynomial.hom_eval₂, map_zero] at h2
    have hc : (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (bk.ev.comp C)) = φ :=
      RingHom.ext fun w => by simp [hφ, bk.ev_C]
    rw [hc] at h2
    exact h2
  have hcoef : ∀ i < bk.Ep.natDegree, ‖φ (bk.Ep.coeff i)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨c, hc⟩ := bk.dvd_coeff i hi
    rw [hc, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le (Per.θ l (wA l bk.a c)))
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree, map_one, one_mul] at h0
  have h3 : π ^ bk.Ep.natDegree = -∑ i ∈ Finset.range bk.Ep.natDegree, φ (bk.Ep.coeff i) * π ^ i := by
    linear_combination h0
  have h4 : ‖π‖ ^ bk.Ep.natDegree ≤ ‖(l : ℂ_[l])‖ := by
    rw [← norm_pow, h3, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i hi => ?_
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ1)).trans
      (hcoef i (Finset.mem_range.1 hi))
  rw [norm_l_C] at h4
  by_contra h5
  push_neg at h5
  have h6 := one_le_pow₀ (n := bk.Ep.natDegree) h5
  have h7 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem step {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ (w : Wq l bk.a) (y' : Om l), y' ∈ K.1 ∧ y' ∈ MaximalUnramifiedExtension l ∧ ‖y'‖ ≤ 1 ∧
      (y : ℂ_[l]) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) + (l : ℂ_[l]) * (y' : ℂ_[l]) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let r : ↥(OL K) := ⟨⟨y, hyK⟩, mem_OL_of_norm_le K _ hy1⟩
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (bk.str r)
  have hθ : (y : ℂ_[l]) = ((Per.θ l (bk.ev f) : OC l) : ℂ_[l]) := by
    rw [bk.θ_ev r f hf, coe_intToOC]
  set z : Fq l bk.a := (constantCoeff f).coeff 0 with hz
  obtain ⟨u, hu⟩ : (l : Wq l bk.a) ∣ constantCoeff f - WittVector.teichmuller l z := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply, hz]
  set f' : bk.S := PowerSeries.mk fun p => coeff (p + 1) f
  have hfe : f = X * f' + C (constantCoeff f) := eq_X_mul_shift_add_const f
  have hc : constantCoeff f = WittVector.teichmuller l z + (l : Wq l bk.a) * u := by rw [← hu]; ring
  set Ψ : bk.S →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp bk.ev) with hΨ
  have hΨC : ∀ w, Ψ (C w) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun w => by simp [hΨ, bk.ev_C]
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  set t : ℂ_[l] := ((Per.θ l (wA l bk.a (WittVector.teichmuller l z)) : OC l) : ℂ_[l]) with ht
  set A : ℂ_[l] := ((Per.θ l (wA l bk.a u) : OC l) : ℂ_[l]) with hA
  set B : ℂ_[l] := ((Per.θ l (bk.ev f') : OC l) : ℂ_[l]) with hB
  have hdec : (y : ℂ_[l]) = t + (l : ℂ_[l]) * A + π * B := by
    have e1 : (y : ℂ_[l]) = Ψ f := hθ
    have e2 : Ψ X = π := rfl
    have e3 : Ψ f' = B := rfl
    rw [e1, hfe, hc]
    simp only [map_add (f := _), map_mul, map_natCast, hΨC, e2, e3]
    rw [ht, hA]
    ring

  set rt : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (C (WittVector.teichmuller l z))) with hrt
  have htK : t = (((rt : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← bk.θ_ev rt (C (WittVector.teichmuller l z)) (by rw [hrt, RingEquiv.apply_symm_apply]), bk.ev_C]
  set yt : Om l := ((rt : ↥K.1) : Om l) with hyt
  have hytK : yt ∈ K.1 := (rt : ↥K.1).2
  have hteich : (WittVector.teichmuller l z) ^ (l ^ bk.a) = WittVector.teichmuller l z := by
    rw [← map_pow, Fq.pow_card]
  have hyt_pow : yt ^ (l ^ bk.a) = yt := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_pow, ← coeC, ← htK, ht, ← SubmonoidClass.coe_pow, ← map_pow, ← map_pow, hteich]
  have hytU : yt ∈ MaximalUnramifiedExtension l := by
    by_cases h0 : yt = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ bk.a := one_lt_pow_l l bk.a
      refine IntermediateField.subset_adjoin ℚ_[l] _ ⟨l ^ bk.a - 1, by omega, fun h => ?_, ?_⟩
      · exact hl.out.not_dvd_one ((Nat.dvd_sub_iff_right hq.le (dvd_pow_self l (NeZero.ne bk.a))).1 h)
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, hyt_pow, one_mul]

  have hdK : y - yt ∈ K.1 := sub_mem hyK hytK
  have hdU : y - yt ∈ MaximalUnramifiedExtension l := sub_mem hyU hytU
  have hdC : ((y - yt : Om l) : ℂ_[l]) = (l : ℂ_[l]) * A + π * B := by
    rw [coeC, map_sub, ← coeC, ← coeC, hdec, ← htK]
    ring
  have hd1 : ‖y - yt‖ < 1 := by
    rw [← PadicComplex.norm_extends, hdC]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul, norm_l_C]
      exact (mul_le_of_le_one_right (by positivity) (norm_OC_le _)).trans_lt (inv_lt_one_of_one_lt₀ hl1)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le _)).trans_lt (norm_pi_lt bk)
  have hd2 : ‖y - yt‖ ≤ (l : ℝ)⁻¹ := by
    by_cases h0 : y - yt = 0
    · rw [h0, norm_zero]; positivity
    obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hdU h0
    rw [hk] at hd1 ⊢
    have hk0 : k < 0 := by
      by_contra hk0
      push_neg at hk0
      exact absurd hd1 (not_lt.2 (one_le_zpow₀ hl1.le hk0))
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le (by omega)
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine ⟨WittVector.teichmuller l z, (y - yt) / (l : Om l), div_mem hdK (natCast_mem _ l),
    div_mem hdU (natCast_mem _ l), ?_, ?_⟩
  · rw [norm_div, norm_l_Om, div_inv_eq_mul]
    calc ‖y - yt‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  · have hlC : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
    rw [coeC ((y - yt) / (l : Om l)), map_div₀, map_natCast, ← coeC, hdC, hdec]
    field_simp
    ring

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_of_int {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ w : Wq l bk.a, ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = (y : ℂ_[l]) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let N : Type := {y : Om l // y ∈ K.1 ∧ y ∈ MaximalUnramifiedExtension l ∧ ‖y‖ ≤ 1}
  let Φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom)
  have hΦ : ∀ w, Φ w = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun _ => rfl
  have hΦ1 : ∀ w, ‖Φ w‖ ≤ 1 := fun w => norm_OC_le _
  have hs : ∀ v : N, ∃ p : Wq l bk.a × N,
      ((v.1 : Om l) : ℂ_[l]) = Φ p.1 + (l : ℂ_[l]) * ((p.2.1 : Om l) : ℂ_[l]) := by
    intro v
    obtain ⟨w, y', h1, h2, h3, h⟩ := step bk v.1 v.2.1 v.2.2.1 v.2.2.2
    exact ⟨(w, ⟨y', h1, h2, h3⟩), h⟩
  choose g hg using hs
  let ys : ℕ → N := fun k => Nat.rec (motive := fun _ => N) ⟨y, hyK, hyU, hy1⟩ (fun _ v => (g v).2) k
  have hys : ∀ k, ys (k + 1) = (g (ys k)).2 := fun _ => rfl
  let s : ℕ → Wq l bk.a := fun k => ∑ i ∈ Finset.range k, (l : Wq l bk.a) ^ i * (g (ys i)).1
  have hinv : ∀ k, (y : ℂ_[l]) = Φ (s k) + (l : ℂ_[l]) ^ k * (((ys k).1 : Om l) : ℂ_[l]) := by
    intro k
    induction k with
    | zero => simp [s, ys]
    | succ k ih =>
      have h := hg (ys k)
      rw [← hys] at h
      simp only [s, Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
      linear_combination ih + (l : ℂ_[l]) ^ k * h
  have hcau : ∀ m n, m ≤ n → (l : Wq l bk.a) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : s (n + 1) - s m = (s n - s m) + (l : Wq l bk.a) ^ n * (g (ys n)).1 := by
        simp only [s, Finset.sum_range_succ]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : Wq l bk.a)}) s fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hcau m n hmn)
  refine ⟨L, ?_⟩
  rw [← hΦ]
  have hbd : ∀ n : ℕ, ‖(y : ℂ_[l]) - Φ L‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    intro n
    have h := hL n
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨v, hv⟩ := h
    have e : (y : ℂ_[l]) - Φ L = (l : ℂ_[l]) ^ n * (Φ v + (((ys n).1 : Om l) : ℂ_[l])) := by
      have := congrArg Φ hv
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination hinv n + this
    rw [e, norm_mul, norm_pow, norm_l_C]
    refine mul_le_of_le_one_right (by positivity) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hΦ1 v) ?_))
    rw [PadicComplex.norm_extends]
    exact (ys n).2.2.2
  by_contra hne
  have hpos : 0 < ‖(y : ℂ_[l]) - Φ L‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  exact absurd (hbd n) (not_le.2 hn)

theorem exists_pow_mul_eq_theta : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 →
    x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a),
      ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  intro l _ K bk x hxK hxU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hl1
  have h1 : ‖(l : Om l) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_l_Om, inv_pow]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact hn.le
  obtain ⟨w, hw⟩ := exists_of_int bk _ (mul_mem (pow_mem (natCast_mem _ l) n) hxK)
    (mul_mem (pow_mem (natCast_mem _ l) n) hxU) h1
  exact ⟨n, w, hw⟩

end GlobalTheory.UnrWitt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWittStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 → x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a), ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  first | exact @GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | exact GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | (intros; apply GlobalTheory.UnrWitt.exists_pow_mul_eq_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeight
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finsetSum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeightStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  first | exact @GlobalTheory.ExpImage.PosWeight.formula_pos | exact GlobalTheory.ExpImage.PosWeight.formula_pos | (intros; apply GlobalTheory.ExpImage.PosWeight.formula_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsComp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsComp
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.coeff_mem_of_mem_map {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (i : ι) (J : Ideal S) {y : A} (hy : y ∈ J.map s) : TB.c i y ∈ J := by
  have key : ∀ a, TB.c i (a * y) ∈ J := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      intro a
      rw [mul_comm, TB.c_mul]
      exact J.mul_mem_right _ hw
    | zero => intro a; rw [mul_zero, map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact J.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

def TopBasis.comp {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) {A' : Type} [CommRing A'] {t : A →+* A'} {κ : Type}
    (TB' : TopBasis t (I.map s) κ) : TopBasis (t.comp s) I (ι × κ) where
  b p := t (TB.b p.1) * TB'.b p.2
  c p := (TB.c p.1).comp (TB'.c p.2)
  c_mul p a x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp]
    rw [TB'.c_mul, TB.c_mul]
  c_self p := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul, TB'.c_self, mul_one, TB.c_self]
  c_ne p q h := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul]
    by_cases hj : p.2 = q.2
    · rw [hj, TB'.c_self, mul_one, TB.c_ne]
      intro hi; exact h (Prod.ext hi hj)
    · rw [TB'.c_ne _ _ hj, mul_zero, map_zero]
  fin x n := by
    have hS := TB'.fin x n
    refine ((Set.Finite.biUnion hS fun j _ => TB.fin (TB'.c j x) n).prod hS).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, AddMonoidHom.coe_comp, Function.comp_apply] at hp
    have h2 : TB'.c p.2 x ∉ (I.map s) ^ n := fun h =>
      hp (TB.coeff_mem_of_mem_map p.1 _ (by rwa [← Ideal.map_pow] at h))
    exact ⟨Set.mem_biUnion (x := p.2) h2 hp, h2⟩
  approx x n F hF := by
    classical
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp] at hF ⊢
    have hS := TB'.fin x n
    set G : Finset κ := F.image Prod.snd ∪ hS.toFinset with hG
    set Fi : Finset ι := F.image Prod.fst with hFi
    have h1 : x - ∑ j ∈ G, t (TB'.c j x) * TB'.b j ∈ (I ^ n).map (t.comp s) := by
      have := TB'.approx x n G (fun j hj => by
        by_contra h
        exact hj (Finset.mem_union_right _ (hS.mem_toFinset.2 h)))
      rwa [← Ideal.map_pow, Ideal.map_map] at this
    have h2 : ∀ j, t (TB'.c j x) * TB'.b j - ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F),
        t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) ∈ (I ^ n).map (t.comp s) := by
      intro j
      have := TB.approx (TB'.c j x) n (Fi.filter (fun i => (i, j) ∈ F)) (fun i hi => by
        apply hF (i, j)
        intro hij
        exact hi (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hij, hij⟩))
      have h' := Ideal.mem_map_of_mem t this
      rw [Ideal.map_map] at h'
      have h'' := Ideal.mul_mem_right (TB'.b j) _ h'
      convert h'' using 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    have hsub : F ⊆ Fi ×ˢ G := fun p hp =>
      Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)⟩
    have h3 : ∑ p ∈ F, t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) =
        ∑ j ∈ G, ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F), t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) := by
      simp_rw [Finset.sum_filter]
      rw [← Finset.sum_product_right (s := Fi) (t := G)
        (f := fun p => if p ∈ F then t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) else 0)]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    rw [h3]
    have := Ideal.add_mem _ h1 (Ideal.sum_mem (t := G) _ fun j _ => h2 j)
    convert this using 1
    rw [Finset.sum_sub_distrib]; ring
  complete := by rw [← Ideal.map_map]; exact TB'.complete
  i₀ := (TB.i₀, TB'.i₀)
  b_i₀ := by simp [TB.b_i₀, TB'.b_i₀]

theorem topBasis_comp_exists : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type)
    (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ),
      (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  intro S A _ _ s I ι TB A' _ t I' κ TB' hI
  subst hI
  exact ⟨TB.comp TB', fun _ _ => rfl, fun _ _ _ => rfl⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsCompStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicTopologicalBasis_exists_comp : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type) (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ), (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  first | exact @GlobalTheory.BSP.topBasis_comp_exists | exact GlobalTheory.BSP.topBasis_comp_exists | (intros; apply GlobalTheory.BSP.topBasis_comp_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envelopes_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X))
    (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)),
    Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧
      ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  intro l _ K bk En En₂
  have h1 : bk.J.map (BK.hf En.inl) =
      Ideal.span {(BK.hf En.inl) (l : bk.S)} ⊔ Ideal.span {(BK.hf En.inl) bk.E} := by
    simp only [BK.J, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h2 : (BK.hf En.inl) (l : bk.S) = (l : En.Q.A) := map_natCast (BK.hf En.inl) l
  have h3 : En.Q.I = Ideal.span {(BK.hf En.inl) bk.E} := En.I_eq
  have hI : Ideal.span {(l : En.Q.A)} ⊔ En.Q.I = bk.J.map (BK.hf En.inl) :=
    (h1.trans (congrArg₂ (· ⊔ ·) (congrArg (fun x => Ideal.span {x}) h2) h3.symm)).symm
  have T₁ : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have T₂ : TopBasis En₂.inl.f (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) := En₂.tb
  have key := GlobalTheory.T.adicTopologicalBasis_exists_comp bk.S En.Q.A (BK.hf En.inl) bk.J (Digits l) T₁ En₂.Q.A En₂.inl.f
    (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) T₂ hI
  exact ⟨⟨T₁⟩, Digits l × Digits l, key.elim fun TC _ => ⟨TC⟩⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)), Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧ ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  first | exact @GlobalTheory.BSP.envelopes_topBasis | exact GlobalTheory.BSP.envelopes_topBasis | (intros; apply GlobalTheory.BSP.envelopes_topBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycle
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.TameRel

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]


omit [IsTopologicalGroup Γ] in
theorem hom_trivial {l : ℕ} (hU : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → U.index.Coprime l)
    {C : Type} [Group C] (f : Γ →* C) (hf : IsOpen (f.ker : Set Γ)) (n : ℕ) (hC : ∀ x : C, x ^ l ^ n = 1) (j : Γ) :
    f j = 1 := by
  have h1 : f j ^ f.ker.index = 1 := by
    rw [← map_pow]
    exact f.ker.pow_index_mem j
  have h2 := (hU _ inferInstance hf).pow_right n
  have h3 := pow_gcd_eq_one.2 ⟨h1, hC (f j)⟩
  rwa [h2, pow_one] at h3


omit [IsTopologicalGroup Γ] in
theorem vanish_of_additive {l : ℕ} {J : Subgroup Γ}
    (hU : ∀ U : Subgroup J, U.Normal → IsOpen (U : Set J) → U.index.Coprime l)
    (K : Type) [Field K] [CharP K l] {W : Type} [AddCommGroup W] [Module K W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ J, ∀ h ∈ J, w (g * h) = w g + w h) : ∀ j ∈ J, w j = 0 := by
  intro j hj
  let f : J →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hf : IsOpen (f.ker : Set J) := (hw {0}).preimage continuous_subtype_val
  refine hom_trivial hU f hf 1 (fun x => ?_) ⟨j, hj⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, pow_one, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, toAdd_one]


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem additive_zpow {D : Subgroup Γ} {W : Type} [AddCommGroup W] (w : Γ → W)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (k : ℤ) : w (γ ^ k) = k • w γ := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  exact congrArg Multiplicative.toAdd (map_zpow f ⟨γ, hγ⟩ k)

theorem vanish_closure {D J : Subgroup Γ} (hJ : J ≤ D) {W : Type} [AddCommGroup W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (h0 : w γ = 0) (h1 : ∀ j ∈ J, w j = 0) :
    ∀ σ ∈ (Subgroup.zpowers γ ⊔ J).topologicalClosure, w σ = 0 := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hle : Subgroup.zpowers γ ⊔ J ≤ f.ker.map D.subtype := by
    refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨γ, hγ⟩, ?_, rfl⟩) fun j hj => ⟨⟨j, hJ hj⟩, ?_, rfl⟩
    · exact congrArg Multiplicative.ofAdd h0
    · exact congrArg Multiplicative.ofAdd (h1 j hj)
  have hsub : ((Subgroup.zpowers γ ⊔ J : Subgroup Γ) : Set Γ) ⊆ {x | w x = 0} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    exact congrArg Multiplicative.toAdd hy
  intro σ hσ
  exact closure_minimal hsub (hw.isClosed_fiber 0) hσ


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem second_pow {D : Subgroup Γ} {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] (z0 z1 : Γ → W)
    (lam : Γ → K) (hlam : ∀ g ∈ D, ∀ h ∈ D, lam (g * h) = lam g + lam h)
    (h1 : ∀ g ∈ D, ∀ h ∈ D, z1 (g * h) = z1 g + z1 h + lam g • z0 h) (h01 : z0 1 = 0) {γ : Γ} (hγ : γ ∈ D) (n : ℕ) :
    z1 (γ ^ n) = (n : K) • z1 γ + ((n.choose 2 : ℕ) : K) • lam γ • z0 γ := by
  induction n with
  | zero =>
    have := h1 1 D.one_mem 1 D.one_mem
    rw [mul_one, h01, smul_zero, add_zero] at this
    simpa using this
  | succ n ih =>
    have e : lam (γ ^ n) = (n : K) * lam γ := by
      have := additive_zpow lam hlam hγ n
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast] at this
    rw [pow_succ, h1 _ (D.pow_mem hγ n) _ hγ, ih, e, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast
    module

end Abstract

theorem cast_of_mod {K : Type} [Field K] {l M q : ℕ} [CharP K l] (hM : 1 ≤ M) (hq : q % (2 * l ^ M) = 1) :
    (q : K) = 1 ∧ ((q.choose 2 : ℕ) : K) = 0 := by
  have h := Nat.div_add_mod q (2 * l ^ M)
  rw [hq] at h
  generalize q / (2 * l ^ M) = t at h
  have hl : ((l ^ M : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero K l, zero_pow (by omega)]
  refine ⟨?_, ?_⟩
  · rw [← h, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hl]
    simp
  · have : q.choose 2 = q * (l ^ M * t) := by
      rw [Nat.choose_two_right]
      have : q - 1 = 2 * (l ^ M * t) := by rw [← h, Nat.add_sub_cancel, mul_assoc]
      rw [this, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this, Nat.cast_mul, Nat.cast_mul, hl]
    simp

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  intro hT F Ω _ _ _ _ _ l _ M A v hA hl hM hq d hd hsurj φ hφ
  obtain ⟨-, -, hU, -, ⟨γ0, hγ0⟩, hrel⟩ := hT F Ω l A v hA hl
  have hID : Ine (F := F) A ≤ Dec (F := F) A := fun σ hσ => hσ.1
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := F) A l
  have hJD := hJI.trans hID
  have hγD : γ0 ∈ Dec (F := F) A := hID hγ0.1
  have hφD : φ ∈ Dec (F := F) A := hφ.1
  have hdJ : ∀ j ∈ GlobalTheory.TameQuot.ineKer F A l, d j = 1 := fun j hj => by
    refine hom_trivial hU (d.comp (GlobalTheory.TameQuot.ineKer F A l).subtype) (hd.preimage continuous_subtype_val) M
      (fun x => ?_) ⟨j, hj⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, d γ0 ^ k = Multiplicative.ofAdd 1 := by
    obtain ⟨σ, hσ, hσd⟩ := hsurj (Multiplicative.ofAdd 1)
    have ho : IsOpen (((Subgroup.zpowers (d γ0)).comap d : Subgroup (G F Ω)) : Set (G F Ω)) :=
      Subgroup.isOpen_mono (H₁ := d.ker) (fun x hx => by
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact Subgroup.one_mem _) hd
    have hle : (Subgroup.zpowers γ0 ⊔ GlobalTheory.TameQuot.ineKer F A l).topologicalClosure ≤
        (Subgroup.zpowers (d γ0)).comap d := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ fun j hj => ?_) (Subgroup.isClosed_of_isOpen _ ho)
      · exact Subgroup.zpowers_le.2 (Subgroup.mem_zpowers _)
      · rw [Subgroup.mem_comap, hdJ j hj]; exact Subgroup.one_mem _
    obtain ⟨k, hk⟩ := hle (hγ0.2 hσ)
    exact ⟨k, hk.trans hσd⟩
  refine ⟨γ0 ^ k, Subgroup.zpow_mem _ hγ0.1 k, by rw [map_zpow, hk], ?_⟩
  intro K _ _ W _ _ z0 hz0 hadd0
  have hkK : (k : K) ≠ 0 := by
    intro h0
    have h1 : (k : ZMod (l ^ M)) * (d γ0).toAdd = 1 := by
      have := congrArg Multiplicative.toAdd hk
      rwa [toAdd_zpow, zsmul_eq_mul] at this
    have h2 := congrArg (ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) K) h1
    rw [map_mul, map_intCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  have hz0J := vanish_of_additive hU K z0 hz0 fun g hg h hh => hadd0 g (hJD hg) h (hJD hh)
  have e0 : z0 (γ0 ^ k) = (k : K) • z0 γ0 := by rw [additive_zpow z0 hadd0 hγD, Int.cast_smul_eq_zsmul]
  refine ⟨fun h σ hσ => ?_, fun lam z1 hlam hz1 haddl hadd1 => ?_⟩
  · rw [e0] at h
    exact vanish_closure hJD z0 hz0 hadd0 hγD ((smul_eq_zero.1 h).resolve_left hkK) hz0J σ (hγ0.2 hσ)
  · have hlJ := vanish_of_additive hU K lam hlam fun g hg h hh => haddl g (hJD hg) h (hJD hh)
    have hz1J := vanish_of_additive hU K z1 hz1 fun g hg h hh => by
      rw [hadd1 g (hJD hg) h (hJD hh), hz0J h hh, smul_zero, add_zero]
    have el : lam (γ0 ^ k) = (k : K) * lam γ0 := by rw [additive_zpow lam haddl hγD, zsmul_eq_mul]
    obtain ⟨hq1, hq2⟩ := cast_of_mod (K := K) hM hq
    have hj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) ∈ GlobalTheory.TameQuot.ineKer F A l :=
      (hrel ⟨φ, hφD⟩ ⟨γ0, hγD⟩ hφ hγ0).2.1
    generalize hjj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) = j at hj
    have hmul : φ * γ0 = γ0 ^ normV v * j * φ := by rw [← hjj]; group
    have hp : γ0 ^ normV v ∈ Dec (F := F) A := Subgroup.pow_mem _ hγD _
    have a1 := hadd1 φ hφD γ0 hγD
    have a2 : z1 (γ0 ^ normV v) = z1 γ0 := by
      rw [second_pow z0 z1 lam haddl hadd1 (hz0J 1 (Subgroup.one_mem _)) hγD, hq1, hq2, one_smul, zero_smul, add_zero]
    have a3 : lam (γ0 ^ normV v) = lam γ0 := by
      have := additive_zpow lam haddl hγD (normV v)
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast, hq1, one_mul] at this
    rw [hmul, hadd1 _ (Subgroup.mul_mem _ hp (hJD hj)) φ hφD, hadd1 _ hp j (hJD hj), haddl _ hp j (hJD hj), a2, a3,
      hz0J j hj, hz1J j hj, hlJ j hj, smul_zero, add_zero, add_zero, add_zero, add_comm (z1 φ), add_right_inj] at a1
    rw [el, e0, mul_smul, a1, smul_comm]

end GlobalTheory.TameRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_local_relation_dualNumber_cocycle : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  first | exact @GlobalTheory.TameRel.tame_relation | exact GlobalTheory.TameRel.tame_relation | (intros; apply GlobalTheory.TameRel.tame_relation <;> assumption)
end
end
