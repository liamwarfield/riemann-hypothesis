module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOne
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiXiUnit

variable {l : ℕ} [Fact l.Prime]

theorem phiA_alg (x : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l x) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg x

theorem φA_tm (x : Per.Fl l) : Per.φA l (Per.tm x) = Per.tm x ^ l := by
  rw [← map_pow]
  exact GlobalTheory.RingIface.phiA_teich l x

theorem φA_tm_root (e : Per.Fl l) :
    Per.φA l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) = Per.tm e := by
  rw [φA_tm, ← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem φA_xi (e : Per.Fl l) :
    Per.φA l (xi e) = ∑ i ∈ Finset.range l, Per.tm e ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xi, map_sum]
  simp only [map_pow, φA_tm_root]

theorem φA_mu (e : Per.Fl l) : Per.φA l (mu e) = mu e * Per.φA l (xi e) := by
  rw [φA_xi, mu, map_sub, map_one, φA_tm, mul_comm, geom_sum_mul]

theorem φA_xi_sub (e : Per.Fl l) :
    ∃ s : Per.Ainf l, Per.φA l (xi e) - (l : Per.Ainf l) = mu e * s := by
  refine ⟨∑ i ∈ Finset.range l, ∑ j ∈ Finset.range i, Per.tm e ^ j, ?_⟩
  have h : (l : Per.Ainf l) = ∑ i ∈ Finset.range l, (1 : Per.Ainf l) := by simp
  rw [φA_xi, mu, Finset.mul_sum, h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, geom_sum_mul]

theorem cancel_mu (C : Core l) (x y : Per.Acris l)
    (h : algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * y) : x = y := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  have hU : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε))) :=
    GlobalTheory.MemLoc.TFil.isUnit_mu he
  apply GlobalTheory.MemLoc.AwayT.acris_injective C
  apply hU.mul_left_cancel
  rw [← map_mul, ← map_mul, h]

theorem exists_unit (C : Core l) : ∃ u : Per.Acris l, IsUnit u ∧
    (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨t, ρ, ht, hρ, htρ⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
  have h1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he.1 C.t_log).1 t ht
  have hφt := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  rw [← h1, htρ, map_mul, phiA_alg, φA_mu, map_mul, mul_assoc, mul_left_comm (l : Per.Acris l)] at hφt
  have h2 := cancel_mu C _ _ hφt
  have hφρ : IsUnit (phiA l ρ) := hρ.map _
  refine ⟨ρ * ↑hφρ.unit⁻¹, hρ.mul (Units.isUnit _), ?_⟩
  rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]

theorem iterate_sub_one (C : Core l) (u : Per.Acris l)
    (hu : (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε))) :
    ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  set a := algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) with ha_def
  have ha : phiA l a = a * ((l : Per.Acris l) * u) := by
    rw [ha_def, phiA_alg, φA_mu, map_mul, hu]
  have hdvd : ∀ m : ℕ, (l : Per.Acris l) ^ m ∣ (phiA l ^ m) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [RingHom.coe_pow, Function.iterate_succ_apply, ha, ← RingHom.coe_pow, map_mul, map_mul,
        map_natCast, pow_succ]
      obtain ⟨c, hc⟩ := ih
      rw [hc]
      exact ⟨c * (phiA l ^ m) u, by ring⟩
  obtain ⟨s, hs⟩ := φA_xi_sub C.ε
  have hls : (l : Per.Acris l) * u - l = a * algebraMap (Per.Ainf l) (Per.Acris l) s := by
    rw [hu, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, ← map_sub, hs, map_mul]
  have key : ∀ m : ℕ, (l : Per.Acris l) * ((phiA l ^ m) u - 1) =
      (phiA l ^ m) a * (phiA l ^ m) (algebraMap (Per.Ainf l) (Per.Acris l) s) := by
    intro m
    rw [← map_mul, ← hls, map_sub, map_mul, map_natCast, mul_sub, mul_one]
  have tf := (GlobalTheory.MemLoc.acris_basic l).2.1
  intro r
  refine ⟨r + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← RingHom.coe_pow]
  obtain ⟨c, hc⟩ := hdvd (k + 1)
  have h3 : (phiA l ^ (k + 1)) u - 1 =
      (l : Per.Acris l) ^ k * (c * (phiA l ^ (k + 1)) (algebraMap (Per.Ainf l) (Per.Acris l) s)) := by
    rw [← sub_eq_zero]
    apply tf
    rw [mul_sub, key, hc, pow_succ]
    ring
  have h4 : (phiA l ^ (k + 1)) u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h3]
    exact dvd_mul_right _ _
  exact Ideal.pow_le_pow_right (by omega) h4

end GlobalTheory.MemLoc.PhiXiUnit

theorem GlobalTheory.MemLoc.phi_xi_unit_tendsto : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l),
    ∃ u : Per.Acris l, IsUnit u ∧
      (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧
      ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M,
        (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  intro l _ C
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.MemLoc.PhiXiUnit.exists_unit C
  exact ⟨u, hu, hlu, GlobalTheory.MemLoc.PhiXiUnit.iterate_sub_one C u hlu⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOneStatement
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobXi_div_prime_unit_tendsto_one : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l), ∃ u : Per.Acris l, IsUnit u ∧ (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧ ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  first | exact @GlobalTheory.MemLoc.phi_xi_unit_tendsto | exact GlobalTheory.MemLoc.phi_xi_unit_tendsto | (intros; apply GlobalTheory.MemLoc.phi_xi_unit_tendsto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMul
open Formalism
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem dvd_of_constantCoeff (x : Per.Ainf l) (h : WittVector.constantCoeff x = 0) :
    (l : Per.Ainf l) ∣ x := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
  rw [hI, Finset.sum_singleton] at h0
  rw [WittVector.constantCoeff_apply] at h
  simpa [h] using h0

theorem constantCoeff_natCast_mul (x : Per.Ainf l) :
    WittVector.constantCoeff ((l : Per.Ainf l) * x) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem iterate_tm (n : ℕ) (y : Per.Fl l) :
    (⇑(Per.φA l))^[n] (Per.tm y) = Per.tm (y ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem smod_iff (m : ℕ) (x y : Per.Ainf l) :
    x ≡ y [SMOD ((Ideal.span {(l : Per.Ainf l)}) ^ m • ⊤ : Submodule (Per.Ainf l) (Per.Ainf l))] ↔
      (l : Per.Ainf l) ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem xi_bar_ne_zero (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) :
    WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) ≠ 0 := by
  set e' := (frobeniusEquiv (Per.Fl l) l).symm e with he'
  have hxi : WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) = ∑ i ∈ Finset.range l, e' ^ i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.MemLoc.xi, map_sum, map_pow, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, he']
  have hpow : e' ^ l = e := by
    have := (frobeniusEquiv (Per.Fl l) l).apply_symm_apply e
    rwa [frobeniusEquiv_apply, ← he'] at this
  intro h0
  rw [hxi] at h0
  have h1 := geom_sum_mul e' l
  rw [h0, zero_mul, hpow] at h1
  have he1 : e = 1 := (sub_eq_zero.1 h1.symm)
  apply he.2
  rw [he1, map_one]
  simp

end GlobalTheory.PeriodSol

namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem exists_step (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) (c : Per.Ainf l) :
    ∃ y : Per.Fl l, (l : Per.Ainf l) ∣
      c + ((⇑(Per.φA l))^[n] (Per.tm y) - GlobalTheory.MemLoc.xi e * Per.tm y) := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  set b := WittVector.constantCoeff c
  have hdeg : (C b - C a * X : (Per.Fl l)[X]).degree < ((l ^ n : ℕ) : WithBot ℕ) := by
    have h1 : (C b - C a * X : (Per.Fl l)[X]).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt h1 (by exact_mod_cast hq)
  have hmon : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).Monic := monic_X_pow_add hdeg
  have hnd : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
    omega
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  refine ⟨y, dvd_of_constantCoeff _ ?_⟩
  rw [iterate_tm]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hy
  rw [map_add (f := _), map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
    WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero]
  rw [← hy]
  ring

theorem exists_start (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) :
    ∃ w₀ : Per.Fl l, w₀ ≠ 0 ∧ w₀ ^ (l ^ n) = WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) * w₀ := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  have hq1 : l ^ n - 1 ≠ 0 := by omega
  have hmon : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).Monic := monic_X_pow_sub_C a hq1
  have hnd : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_X_pow_sub_C _]; exact hq1
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow hq1] at hy
    exact xi_bar_ne_zero e he hy.symm
  · rw [← hy, ← pow_succ, Nat.sub_add_cancel hq.le]

theorem period_solution : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e →
    ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧
      (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  intro l _ e he n hn
  set ξ := GlobalTheory.MemLoc.xi e
  let Φ : Per.Ainf l →+* Per.Ainf l := Per.φA l ^ n
  have hΦ : ∀ x, (⇑(Per.φA l))^[n] x = Φ x := fun x => by simp [Φ, RingHom.coe_pow]
  let F : Per.Ainf l → Per.Ainf l := fun w => Φ w - ξ * w
  have F_sub : ∀ a b, F (a - b) = F a - F b := fun a b => by simp only [F, map_sub]; ring
  have F_lin : ∀ (m : ℕ) a b, F (a + (l : Per.Ainf l) ^ m * b) = F a + (l : Per.Ainf l) ^ m * F b :=
    fun m a b => by simp only [F, map_add (f := _), map_mul, map_pow, map_natCast]; ring
  have step : ∀ (k : ℕ) (w : Per.Ainf l), ∃ w' : Per.Ainf l,
      (l : Per.Ainf l) ^ (k + 1) ∣ F w →
        (l : Per.Ainf l) ^ (k + 2) ∣ F w' ∧ (l : Per.Ainf l) ^ (k + 1) ∣ w' - w := by
    intro k w
    by_cases hw : (l : Per.Ainf l) ^ (k + 1) ∣ F w
    · obtain ⟨c, hc⟩ := hw
      obtain ⟨y, d, hd⟩ := exists_step e he n hn c
      refine ⟨w + (l : Per.Ainf l) ^ (k + 1) * Per.tm y, fun _ => ⟨⟨d, ?_⟩, ⟨Per.tm y, by ring⟩⟩⟩
      rw [F_lin, hc, ← mul_add]
      have : F (Per.tm y) = (⇑(Per.φA l))^[n] (Per.tm y) - ξ * Per.tm y := by simp only [F, hΦ]
      rw [this, hd]; ring
    · exact ⟨w, fun h => absurd h hw⟩
  choose g hg using step
  obtain ⟨w₀, hw₀, hw₀q⟩ := exists_start e he n hn
  let seq : ℕ → Per.Ainf l := fun k => Nat.rec (Per.tm w₀) (fun k w => g k w) k
  have hseq0 : seq 0 = Per.tm w₀ := rfl
  have hseqS : ∀ k, seq (k + 1) = g k (seq k) := fun k => rfl
  have hF0 : (l : Per.Ainf l) ^ (0 + 1) ∣ F (seq 0) := by
    rw [zero_add, pow_one, hseq0]
    apply dvd_of_constantCoeff
    simp only [F, ← hΦ, iterate_tm, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
      WittVector.teichmuller_coeff_zero, hw₀q]
    exact sub_self _
  have hF : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ F (seq k) := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih => rw [hseqS]; exact (hg k (seq k) ih).1
  have hdiff : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ seq (k + 1) - seq k := fun k => by
    rw [hseqS]; exact (hg k (seq k) (hF k)).2
  have hcau : ∀ m d, (l : Per.Ainf l) ^ m ∣ seq m - seq (m + d) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : (l : Per.Ainf l) ^ m ∣ seq (m + d + 1) - seq (m + d) :=
        (pow_dvd_pow _ (by omega)).trans (hdiff (m + d))
      have : seq m - seq (m + (d + 1)) = (seq m - seq (m + d)) - (seq (m + d + 1) - seq (m + d)) := by
        rw [← add_assoc]; ring
      rw [this]; exact dvd_sub ih h2
  have hcomp : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := seq) (fun {m n} hmn => by
    rw [smod_iff]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcau m d)
  have hL' : ∀ k, (l : Per.Ainf l) ^ k ∣ seq k - L := fun k => (smod_iff k _ _).1 (hL k)
  have hFL : F L = 0 := by
    refine hcomp.toIsHausdorff.haus (F L) fun k => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨c, hc⟩ := hL' k
    have e1 : L = seq k + (l : Per.Ainf l) ^ k * (-c) := by rw [mul_neg, ← hc]; ring
    rw [e1, F_lin]
    exact dvd_add ((pow_dvd_pow _ (Nat.le_succ k)).trans (hF k)) (dvd_mul_right _ _)
  have hL0 : WittVector.constantCoeff L = w₀ := by
    obtain ⟨c, hc⟩ := hL' 1
    obtain ⟨c', hc'⟩ := hdiff 0
    have e1 : L = Per.tm w₀ + (l : Per.Ainf l) * (c' - c) := by
      rw [pow_one] at hc; rw [zero_add, pow_one] at hc'
      rw [mul_sub, ← hc, ← hc', ← hseq0]; ring
    rw [e1, map_add (f := _), constantCoeff_natCast_mul, add_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  refine ⟨L, fun h0 => ?_, ?_⟩
  · have := congrArg WittVector.constantCoeff h0
    rw [map_mul, map_zero, hL0] at this
    exact mul_ne_zero (xi_bar_ne_zero e he) hw₀ this
  · rw [hΦ]; exact sub_eq_zero.1 hFL

end GlobalTheory.PeriodSol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMulStatement
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e → ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧ (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  first | exact @GlobalTheory.PeriodSol.period_solution | exact GlobalTheory.PeriodSol.period_solution | (intros; apply GlobalTheory.PeriodSol.period_solution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEq
namespace GlobalTheory.FrobeniusProduct

theorem exists_adic_limit {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (s : ℕ → A) (hs : ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r) :
    ∃ L : A, ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s m - L ∈ I ^ r := by
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  choose N hN using hs
  have tele : ∀ r a b, (∀ k ≥ a, s (k + 1) - s k ∈ I ^ r) → a ≤ b → s b - s a ∈ I ^ r := by
    intro r a b h hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := (I ^ r).add_mem (h b hab) ih
      convert this using 1
      ring
  set N' : ℕ → ℕ := fun r => ∑ j ∈ Finset.range (r + 1), N j with hN'
  have hN'ge : ∀ r, N r ≤ N' r := fun r =>
    Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ r)
  have hN'mono : Monotone N' := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun r => s (N' r)) (by
      intro m n hmn
      rw [SModEq.sub_mem, hsm]
      have := tele m (N' m) (N' n) (fun k hk => hN m k (le_trans (hN'ge m) hk)) (hN'mono hmn)
      have := (I ^ m).neg_mem this
      simpa using this)
  refine ⟨L, fun r => ⟨N' r, fun m hm => ?_⟩⟩
  have h1 := tele r (N' r) m (fun k hk => hN r k (le_trans (hN'ge r) hk)) hm
  have h2 : s (N' r) - L ∈ I ^ r := by
    have := hL r
    rw [SModEq.sub_mem, hsm] at this
    exact this
  have := (I ^ r).add_mem h1 h2
  convert this using 1
  ring

theorem exists_unit_iterate_mul_eq :
    ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A →
      ∀ (φ : A →+* A) (u : A), IsUnit u →
        (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) →
          ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  intro A _ p hc φ u hu hconv n hn
  haveI := hc
  set I : Ideal A := Ideal.span {(p : A)} with hI
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  obtain ⟨w, hw⟩ : ∃ w : ℕ → A, w = fun k => (⇑φ)^[n * k + (n - 1)] u := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → A, s = fun N => ∏ k ∈ Finset.range N, w k := ⟨_, rfl⟩
  have hwconv : ∀ r, ∃ M, ∀ k ≥ M, w k - 1 ∈ I ^ r := fun r => by
    obtain ⟨M, hM⟩ := hconv r
    exact ⟨M, fun k hk => by rw [hw]; exact hM _ (by nlinarith)⟩
  have hcauchy : ∀ r, ∃ N, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r := by
    intro r
    obtain ⟨M, hM⟩ := hwconv r
    refine ⟨M, fun m hm => ?_⟩
    have e : s (m + 1) - s m = s m * (w m - 1) := by
      simp only [hs, Finset.prod_range_succ]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (hM m hm)
  obtain ⟨c, hc'⟩ := exists_adic_limit I s hcauchy
  have haus : ∀ x : A, (∀ r : ℕ, x ∈ I ^ r) → x = 0 := fun x hx =>
    IsHausdorff.haus (I := I) (M := A) inferInstance x (fun r => by rw [SModEq.zero, hsm]; exact hx r)
  have hmap : ∀ k (x : A) r, x ∈ I ^ r → (⇑φ)^[k] x ∈ I ^ r := by
    intro k x r hx
    have := Ideal.mem_map_of_mem (φ ^ k) hx
    rwa [Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton, map_natCast,
      RingHom.coe_pow] at this
  have hsub : ∀ x y : A, (⇑φ)^[n] (x - y) = (⇑φ)^[n] x - (⇑φ)^[n] y := by
    intro x y; rw [← RingHom.coe_pow]; exact map_sub _ _ _
  have key : ∀ N, (⇑φ)^[n] (s N) * (⇑φ)^[n - 1] u = s (N + 1) := by
    intro N
    simp only [hs, Finset.prod_range_succ']
    rw [← RingHom.coe_pow, map_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      simp only [RingHom.coe_pow, hw]
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    · simp [hw]
  have hwunit : ∀ k, IsUnit (w k) := fun k => by
    rw [hw]; show IsUnit ((⇑φ)^[n * k + (n - 1)] u)
    rw [← RingHom.coe_pow]; exact hu.map _
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hc' 1
    have h1 : s N - c ∈ I := by simpa using hN N le_rfl
    have hsN : IsUnit (s N) := by
      rw [hs]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun k _ => hwunit k)
    obtain ⟨v, hv⟩ := hsN
    have hy : -(s N - c) ∈ (⊥ : Ideal A).jacobson :=
      IsAdicComplete.le_jacobson_bot I (I.neg_mem h1)
    have hu' := (Ideal.mem_jacobson_bot.mp hy) (↑v⁻¹ : A)
    have heq : c = (-(s N - c) * (↑v⁻¹ : A) + 1) * ↑v := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hv]; ring
    rw [heq]
    exact hu'.mul v.isUnit
  · refine sub_eq_zero.mp (haus _ fun r => ?_)
    obtain ⟨N, hN⟩ := hc' r
    have e : (⇑φ)^[n] c * (⇑φ)^[n - 1] u - c =
        -((⇑φ)^[n] (s N - c) * (⇑φ)^[n - 1] u) + (s (N + 1) - c) := by
      rw [← key N, hsub]; ring
    rw [e]
    exact (I ^ r).add_mem ((I ^ r).neg_mem (Ideal.mul_mem_right _ _ (hmap n _ r (hN N le_rfl))))
      (hN (N + 1) (by omega))

end GlobalTheory.FrobeniusProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEqStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_frobenius_iterate_product_eq : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  first | exact @GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | exact GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | (intros; apply GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.LTPeriod

variable {l : ℕ} [Fact l.Prime]

theorem iter_φB_alg (k : ℕ) (y : Per.Acris l) :
    (⇑(Per.φB l))^[k] (algebraMap (Per.Acris l) (Per.Bcris l) y) =
      algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(GlobalTheory.MemLoc.phiA l))^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GlobalTheory.MemLoc.fund_phiB_alg, ih]

theorem phiA_alg (a : Per.Ainf l) :
    GlobalTheory.MemLoc.phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem iter_phiA_alg (k : ℕ) (a : Per.Ainf l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[k] (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[k] a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, phiA_alg, ih]

theorem iter_mul {A : Type} [CommRing A] (f : A →+* A) (k : ℕ) (a b : A) :
    (⇑f)^[k] (a * b) = (⇑f)^[k] a * (⇑f)^[k] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem iter_natCast {A : Type} [CommRing A] (f : A →+* A) (k m : ℕ) :
    (⇑f)^[k] (m : A) = m := by
  rw [← RingHom.coe_pow, map_natCast]

theorem concrete (C : GlobalTheory.MemLoc.Core l) (n : ℕ) (hn : 0 < n) :
    ∃ x : Per.Bcris l, IsUnit x ∧ (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x ∧ C.ι x ∈ Per.FilD l 1 ∧
      C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 ∧ C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul l C.ε he (m + 1) hn
  obtain ⟨u, hu, hlu, hconv⟩ := GlobalTheory.T.frobXi_div_prime_unit_tendsto_one l C
  obtain ⟨c, hc, hcφ⟩ :=
    GlobalTheory.T.exists_unit_frobenius_iterate_product_eq (Per.Acris l) l (GlobalTheory.MemLoc.acris_basic l).1 (GlobalTheory.MemLoc.phiA l) u hu hconv (m + 1) hn
  rw [Nat.add_sub_cancel] at hcφ
  set ξ := GlobalTheory.MemLoc.xi C.ε with hξ
  have h1 : (l : Per.Acris l) * (⇑(GlobalTheory.MemLoc.phiA l))^[m] u =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) := by
    rw [← iter_natCast (GlobalTheory.MemLoc.phiA l) m l, ← iter_mul, hlu, iter_phiA_alg,
      ← Function.iterate_succ_apply]
  have hkey : algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) *
      (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] c = (l : Per.Acris l) * c := by
    rw [← h1]
    linear_combination (l : Per.Acris l) * hcφ
  set a : Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w) * c with ha
  have hA : (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] a = (l : Per.Acris l) * a := by
    rw [ha, iter_mul, iter_phiA_alg, iter_mul, hw, map_mul, map_mul]
    linear_combination (algebraMap (Per.Ainf l) (Per.Acris l) ξ *
      algebraMap (Per.Ainf l) (Per.Acris l) w) * hkey
  set x : Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) a with hx
  have hxφ : (⇑(Per.φB l))^[m + 1] x = (l : Per.Bcris l) * x := by
    rw [hx, iter_φB_alg, hA, map_mul, map_natCast]
  have hxa : x = Per.aB l (ξ * w) * algebraMap (Per.Acris l) (Per.Bcris l) c := by
    have e : algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w)) =
        Per.aB l (ξ * w) := by
      apply (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.1
      rw [GlobalTheory.MemLoc.PrimeEx.iota_aB, C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris]
    rw [hx, ha, map_mul, e]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [hxa, (hc.map (algebraMap (Per.Acris l) (Per.Bcris l))).mul_left_eq_zero] at h0
    exact hw0 (GlobalTheory.MemLoc.PrimeEx.aB_inj C (h0.trans (map_zero _).symm))
  have hx1 : C.ι x ∈ Per.FilD l 1 := by
    rw [hxa, map_mul, C.ι_j, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ((GlobalTheory.MemLoc.PrimeEx.fil1 C _).2 ⟨w, rfl⟩)
  have hx0' : ∀ j : ℕ, j < m + 1 → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 := by
    intro j _
    rw [hx, iter_φB_alg, C.ι_j]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _
  obtain ⟨hunit, h2, hj⟩ := GlobalTheory.T.frobeniusEigen_fil_one_isUnit_exact_degree l C (m + 1) hn x hxφ hx0 hx1 hx0'
  exact ⟨x, hunit, hxφ, hx1, h2, fun j hj0 hjn => ⟨hx0' j hjn, hj j hj0 hjn⟩⟩

end GlobalTheory.LTPeriod

theorem GlobalTheory.LTPeriod.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧
      P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  intro l _ P AI T K n hn
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.concrete C n hn
  have hit : ∀ (k : ℕ) (b : P.R.B), T.eB ((⇑P.φB)^[k] b) = (⇑(Per.φB l))^[k] (T.eB b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hfil : ∀ (a : ℤ) (b : P.R.B), P.ιB b ∈ (P.PD K).Fil a ↔ C.ι (T.eB b) ∈ Per.FilD l a := by
    intro a b
    rw [T.fil, hC.ι]
  refine ⟨T.eB.symm x, hu.map T.eB.symm, T.eB.injective ?_, ?_, ?_, fun j hj0 hjn => ?_⟩
  · rw [hit, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h1
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h2
  · rw [hfil, hfil, hit, RingEquiv.apply_symm_apply]
    exact hj j hj0 hjn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_period_local_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧ P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  first | exact @GlobalTheory.LTPeriod.main | exact GlobalTheory.LTPeriod.main | (intros; apply GlobalTheory.LTPeriod.main <;> assumption)
end
