module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ker_localizedTheta_eq_span_of_dvd (l : ℕ) [Fact l.Prime] (x : Per.Ainf l)
    (hx : ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ x ∣ a) :
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) x} := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    have hy' : Per.θP l y = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one])
    have h0 : Per.θ l a = 0 := by
      have h1 := GlobalTheory.RingIface.fontaineTheta_algebraMap (l := l) a
      rw [← ha, map_mul, hy', zero_mul] at h1
      exact Subtype.ext h1.symm
    obtain ⟨c, rfl⟩ := (hx a).1 h0
    have hu : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) ((l : ℕ) : Per.Ainf l) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)).pow n
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, ha, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact GlobalTheory.RingIface.alg_mem_kerP (l := l) ((hx x).2 dvd_rfl)

theorem ker_localizedTheta_eq_span_xi : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} :=
  fun l _ e he => ker_localizedTheta_eq_span_of_dvd l (xi e) (theta_eq_zero_iff_xi_dvd l e he)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  first | exact @GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi | exact GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi | (intros; apply GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogEx

theorem mul_pred_lt_pow (l v : ℕ) (hl : 1 ≤ l) : v * (l - 1) + 1 ≤ l ^ v := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    nlinarith [Nat.zero_le (v * d * d)]

theorem exists_term {R : Type} [CommRing R] (l : ℕ) (hl : l.Prime)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) (k : ℕ) :
    ∃ c : R, ((k + 1 : ℕ) : R) * c = m ^ k ∧ (l : R) ^ (k / (l - 1) / l) ∣ c ∧
      (k ≠ 0 → c ∈ (Ideal.span {(l : R)}).radical) := by
  obtain ⟨v, a, ha, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
  obtain ⟨b, hb⟩ := (hu a ha).exists_right_inv
  have hl2 := hl.two_le
  have ha0 : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero _))
  have hv : v ≤ k / (l - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 := mul_pred_lt_pow l v hl.one_le
    have h2 : l ^ v ≤ l ^ v * a := Nat.le_mul_of_pos_right _ ha0
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hv
  have hqr := Nat.div_add_mod k (l - 1)
  set q := k / (l - 1) with hq
  set r := k % (l - 1) with hr
  have hwr : w ∈ (Ideal.span {(l : R)}).radical := ⟨l, Ideal.mem_span_singleton.2 hwl⟩
  have hmr : m ∈ (Ideal.span {(l : R)}).radical := ⟨l - 1, Ideal.mem_span_singleton.2 ⟨w, hw.symm⟩⟩
  refine ⟨b * (l : R) ^ d * m ^ r * w ^ q, ?_, ?_, fun hk0 => ?_⟩
  · have e : m ^ k = ((l : R) * w) ^ q * m ^ r := by
      rw [hw, ← pow_mul, ← pow_add, hqr]
    have e2 : ((k + 1 : ℕ) : R) = (l : R) ^ v * a := by
      rw [show k + 1 = l ^ v * a from hk]; push_cast; rfl
    rw [e, e2, mul_pow]
    have e3 : (l : R) ^ q = (l : R) ^ v * (l : R) ^ d := by rw [hd, pow_add]
    rw [e3]
    linear_combination ((l : R) ^ v * (l : R) ^ d * m ^ r * w ^ q) * hb
  · refine Dvd.dvd.mul_left ?_ _
    refine (pow_dvd_pow_of_dvd hwl _).trans ?_
    rw [← pow_mul]
    exact pow_dvd_pow _ (Nat.mul_div_le q l)
  · rcases Nat.eq_zero_or_pos q with h | h
    · have : 0 < r := by
        rw [h] at hqr
        omega
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hmr _ this))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hwr _ h)

theorem exists_sum {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A]
    (c : ℕ → A) (N : ℕ → ℕ) (hN : Monotone N) (hc : ∀ r k, N r ≤ k → p ^ r ∣ c k) :
    ∃ u : A, ∀ r n, N r ≤ n → p ^ r ∣ u - ∑ k ∈ Finset.range n, c k := by
  have key : ∀ r n, N r ≤ n →
      p ^ r ∣ ∑ k ∈ Finset.range n, c k - ∑ k ∈ Finset.range (N r), c k := by
    intro r n h
    rw [← Finset.sum_Ico_eq_sub _ h]
    exact Finset.dvd_sum fun k hk => hc r k (Finset.mem_Ico.1 hk).1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {p}) (M := A) inferInstance
    (f := fun r => ∑ k ∈ Finset.range (N r), c k) (fun {a b} hab => by
      rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact key a _ (hN hab))
  refine ⟨L, fun r n h => ?_⟩
  have h1 := hL r
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h1
  have := dvd_sub h1 (key r n h)
  rwa [sub_sub_sub_cancel_right] at this

theorem exists_unit {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : l.Prime)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) :
    ∃ (c : ℕ → R) (u : A), (∀ k, ((k + 1 : ℕ) : R) * c k = m ^ k) ∧ IsUnit u ∧
      ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        (l : A) ^ r ∣ u - f (∑ k ∈ Finset.range n, (-1) ^ k * c k) := by
  choose c h1 h2 h3 using exists_term l hl hu m w hw hwl
  have hl2 := hl.two_le
  obtain ⟨u, hs⟩ := exists_sum (l : A) (fun k => f ((-1) ^ k * c k)) (fun r => r * l * (l - 1))
    (fun a b hab => Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hab)) (fun r k hk => by
      have hr : r ≤ k / (l - 1) / l := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
        exact hk
      have := map_dvd f (((pow_dvd_pow (l : R) hr).trans (h2 k)).mul_left ((-1) ^ k))
      rwa [map_pow, map_natCast] at this)
  refine ⟨c, u, h1, ?_, fun r => ⟨_, fun n hn => by rw [map_sum]; exact hs r n hn⟩⟩
  have hc0 : c 0 = 1 := by simpa using h1 0
  have hrad : u - 1 ∈ (Ideal.span {(l : A)}).radical := by
    have h := hs 1 (1 * l * (l - 1) + 1) (Nat.le_succ _)
    rw [Finset.sum_range_succ', pow_one, hc0, pow_zero, mul_one, map_one] at h
    have h' := Ideal.le_radical (Ideal.mem_span_singleton.2 h)
    have h'' : ∑ k ∈ Finset.range (1 * l * (l - 1)), f ((-1) ^ (k + 1) * c (k + 1)) ∈
        (Ideal.span {(l : A)}).radical := by
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      obtain ⟨n, hn⟩ := h3 (k + 1) (Nat.succ_ne_zero k)
      refine ⟨n, Ideal.mem_span_singleton.2 ?_⟩
      have := map_dvd f (Ideal.mem_span_singleton.1 hn)
      rwa [map_pow, map_natCast] at this
    have := add_mem h' h''
    convert this using 1
    ring
  have hj : u - 1 ∈ Ideal.jacobson (⊥ : Ideal A) := by
    have h := Ideal.radical_le_jacobson hrad
    have h' := Ideal.jacobson_mono (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : A)})) h
    rwa [Ideal.jacobson_idem] at h'
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot u hj

theorem isUnit_nat_acris0 (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : ¬ l ∣ a) :
    IsUnit (a : Per.Acris0 l) := by
  have h : IsUnit (a : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ha
  have := h.map ((algebraMap (Per.Ainf l) (Per.Acris0 l)).comp (Per.zA l))
  rwa [map_natCast] at this

theorem algebraMap_acris (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem factorial_mul_sum {P : Type} [CommRing P] (m : P) (c : ℕ → P)
    (h : ∀ k, ((k + 1 : ℕ) : P) * c k = m ^ k) (n : ℕ) :
    ((n.factorial : ℕ) : P) * (m * ∑ k ∈ Finset.range n, (-1) ^ k * c k) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : P) * m ^ (k + 1) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
  have e : ((n.factorial : ℕ) : P) = ((n.factorial / (k + 1) : ℕ) : P) * ((k + 1 : ℕ) : P) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
  rw [pow_succ m, ← h k]
  linear_combination (m * (-1) ^ k * c k) * e

end GlobalTheory.MemLoc.LogEx

namespace GlobalTheory.MemLoc
open LogEx

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_isLogA : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧
      t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  intro l _ e he
  obtain ⟨w, hw, hwl⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he
  obtain ⟨c, u, h1, hu, h2⟩ := exists_unit (algebraMap (Per.Acris0 l) (Per.Acris l)) l Fact.out
    (acris_basic l).1 (isUnit_nat_acris0 l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) w
    (Subtype.ext (by simpa using hw)) hwl
  refine ⟨_, u, fun r => ?_, hu, rfl⟩
  obtain ⟨N, hN⟩ := h2 r
  refine ⟨N, fun n hn => ⟨algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) *
    ∑ k ∈ Finset.range n, (-1) ^ k * c k, ?_, ?_⟩⟩
  · have := congrArg (Per.Acris0 l).val
      (factorial_mul_sum (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) c h1 n)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_natCast, map_sum] at this
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_neg, map_one, AlgHom.commutes]
  · obtain ⟨z, hz⟩ := hN n hn
    refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * z, ?_⟩
    rw [map_mul, ← algebraMap_acris, ← mul_sub, hz]
    ring

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 → ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧ t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  first | exact @GlobalTheory.MemLoc.exists_isLogA | exact GlobalTheory.MemLoc.exists_isLogA | (intros; apply GlobalTheory.MemLoc.exists_isLogA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem exists_isTiltOf (c : Om l) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : c ^ m = 1) :
    ∃ xb : Per.Fl l, IsTiltOf c m xb := by
  have hcC : (c : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hc
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(c : ℂ_[l])‖ = 1 := by
    have := congrArg norm hcC
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  let C : Per.OC l := ⟨(c : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 hn.le⟩
  have hC : C ^ m = 1 := Subtype.ext (by simpa using hcC)
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (Nat.totient m - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hcop
  let y : ℕ → Per.OC l := fun k => C ^ (a ^ k)
  have hy : ∀ k, y (k + 1) ^ l = y k := by
    intro k
    simp only [y]
    rw [← pow_mul]
    refine pow_eq_pow_of_modEq ?_ hC
    rw [pow_succ, mul_assoc]
    simpa using ha.mul_left (a ^ k)
  have hy0 : ∀ k, y k ^ (l ^ k) = C := by
    intro k
    induction k with
    | zero => simp [y]
    | succ k ih => rw [pow_succ', pow_mul, hy, ih]
  refine ⟨(⟨fun k => Ideal.Quotient.mk _ (y k), fun k => ?_⟩ : Perfection (ModP (Per.OC l) l) l), fun k => ⟨y k, ?_, ?_, rfl⟩⟩
  · rw [← map_pow, hy]
  · have := congrArg Subtype.val (hy0 k)
    simpa using this
  · simp only [y]
    rw [← pow_mul, mul_comm, pow_mul, hC, one_pow]

theorem IsTiltOf.pow_eq_one {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) : xb ^ m = 1 := by
  refine Perfection.ext fun k => ?_
  obtain ⟨y, -, h2, h3⟩ := h k
  change PreTilt.coeff k (xb ^ m) = PreTilt.coeff k (1 : Per.Fl l)
  rw [map_pow, map_one, h3, ← map_pow, h2, map_one]

theorem IsTiltOf.untilt_eq {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) :
    ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
  obtain ⟨y0, h0, -, -⟩ := h 0
  rw [pow_zero, pow_one] at h0
  have : xb.untilt = y0 := by
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun n => ?_
    obtain ⟨y, h1, -, h3⟩ := h n
    refine ⟨y, h3.symm, ?_⟩
    have : y ^ l ^ n = y0 := Subtype.ext (by simpa [h0] using h1)
    rw [this]
  rw [this, h0]

theorem rootOfUnity_teichmuller : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  intro l _ o ho c m hm hl hc
  refine ⟨exists_isTiltOf c m hm hl hc, fun xb h => ⟨IsTiltOf.pow_eq_one h, IsTiltOf.untilt_eq h, ?_⟩⟩
  obtain ⟨-, -, hu, hθ, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have h1 : aDp l (Per.tm xb) ^ m = 1 := by
    rw [← map_pow, ← map_pow, IsTiltOf.pow_eq_one h, map_one, map_one]
  have h2 : o c ^ m = 1 := by rw [← map_pow, hc, map_one]
  have t1 : Per.θD l (aDp l (Per.tm xb)) = (c : ℂ_[l]) := by
    rw [hθ, WittVector.fontaineTheta_teichmuller, IsTiltOf.untilt_eq h]
  have t2 : Per.θD l (o c) = (c : ℂ_[l]) := ho.th c
  generalize aDp l (Per.tm xb) = y at h1 t1 ⊢
  have hc0 : (c : ℂ_[l]) ≠ 0 := by
    intro h0
    have := congrArg (Per.θD l) h2
    rw [map_pow, map_one, t2, h0, zero_pow hm.ne'] at this
    exact zero_ne_one this
  have hg := (Commute.all y (o c)).geom_sum₂_mul m
  rw [h1, h2, sub_self] at hg
  have hS : IsUnit (∑ i ∈ Finset.range m, y ^ i * o c ^ (m - 1 - i)) := by
    apply hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, t1, t2]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hc0)
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 hg)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLiftStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  first | exact @GlobalTheory.MemLoc.rootOfUnity_teichmuller | exact GlobalTheory.MemLoc.rootOfUnity_teichmuller | (intros; apply GlobalTheory.MemLoc.rootOfUnity_teichmuller <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem adjoin_dividedPowers_iff_span {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (P : R → Prop) (hP : ∀ a, P a ↔ ξ ∣ a) (s : A) :
    s ∈ Algebra.adjoin R {y : A | ∃ x : R, P x ∧ ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A x ^ n} ↔
      s ∈ Submodule.span R {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} := by
  set S : Set A := {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} with hS
  have hγ : ∀ n : ℕ, ∃ g : A, ((n.factorial : ℕ) : A) * g = algebraMap R A ξ ^ n := fun n => by
    obtain ⟨u, hu'⟩ := (hu n).exists_right_inv
    exact ⟨u * algebraMap R A ξ ^ n, by rw [← mul_assoc, hu', one_mul]⟩
  have hone : (1 : A) ∈ Submodule.span R S := Submodule.subset_span ⟨0, by simp⟩
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span R S := by
    rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    obtain ⟨g, hg⟩ := hγ (m + n)
    have hf : (((m + n).factorial : ℕ) : A) =
        (((m + n).choose n : ℕ) : A) * (m.factorial : ℕ) * (n.factorial : ℕ) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial m n]; push_cast; ring
    have : x * y = ((m + n).choose n : R) • g := by
      refine ((hu m).mul (hu n)).mul_left_cancel ?_
      rw [Algebra.smul_def, map_natCast]
      rw [hf, pow_add, ← hm, ← hn] at hg
      linear_combination -hg
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + n, hg⟩)
  constructor
  · intro hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨x, hx, n, hn⟩ := hy
      obtain ⟨a, rfl⟩ := (hP x).1 hx
      obtain ⟨g, hg⟩ := hγ n
      have : y = (a ^ n) • g := by
        refine (hu n).mul_left_cancel ?_
        rw [hn, Algebra.smul_def, map_mul, mul_pow, ← hg, map_pow]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hg⟩)
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ hone
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_le.2 ?_ this
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
  · intro hs
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin R _))).2 ?_ hs
    rintro y ⟨n, hn⟩
    exact Algebra.subset_adjoin ⟨ξ, (hP ξ).2 dvd_rfl, n, hn⟩

theorem mem_Acris0_iff_span : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l,
    s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  intro l _ e he s
  refine Iff.trans ?_ (adjoin_dividedPowers_iff_span (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (xi e)
    (fun a => Per.θ l a = 0) (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he) s)
  constructor
  · intro hs
    refine (?_ : Per.Acris0 l ≤ _) hs
    refine GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _ fun x n y hx hy => ?_
    exact Algebra.subset_adjoin ⟨x, hx, n, hy⟩
  · intro hs
    refine Algebra.adjoin_le (S := Per.Acris0 l) ?_ hs
    rintro y ⟨x, hx, n, hy⟩
    exact GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n y hx hy

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIffStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_membership_span_iff : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l, s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  first | exact @GlobalTheory.MemLoc.mem_Acris0_iff_span | exact GlobalTheory.MemLoc.mem_Acris0_iff_span | (intros; apply GlobalTheory.MemLoc.mem_Acris0_iff_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariant
noncomputable section
namespace GlobalTheory.MemLoc.SecUniq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem root_eq {K R C : Type} [Field K] [CommRing R] [Field C] (θ : R →+* C)
    (hu : ∀ y : R, θ y ≠ 0 → IsUnit y) (o : K →+* R) (x : K) (y : R) (f : Polynomial K)
    (hy : θ y = θ (o x)) (h0 : f.eval x = 0) (h1 : f.derivative.eval x ≠ 0)
    (h2 : (f.map o).eval y = 0) : y = o x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map o) (o x) (y - o x)
  rw [add_sub_cancel, h2, Polynomial.derivative_map, Polynomial.eval_map_apply,
    Polynomial.eval_map_apply, h0, map_zero, zero_add] at hk
  have hθ : θ (y - o x) = 0 := by rw [map_sub, hy, sub_self]
  have hun : IsUnit (o (f.derivative.eval x) + k * (y - o x)) := by
    apply hu
    rw [map_add (f := _), map_mul, hθ, mul_zero, add_zero]
    exact (map_ne_zero (θ.comp o)).2 h1
  have : (o (f.derivative.eval x) + k * (y - o x)) * (y - o x) = 0 := by
    rw [hk]; ring
  exact sub_eq_zero.1 ((hun.mul_right_eq_zero).1 this)

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_hom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {((l : ℕ) : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {((l : ℕ) : R)}) inferInstance _ fun n => ?_)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [← hw]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f w - g w, ?_⟩
  have h1 := congrArg f hz
  have h2 := congrArg g hz
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at h1 h2
  rw [h1, h2]
  ring

theorem sigA_zA (g : Per.Gq l) (z : ℤ_[l]) : Per.σA g (Per.zA l z) = Per.zA l z := by
  haveI : IsAdicComplete (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  exact padicInt_hom_ext_pt ((Per.σA g).comp (Per.zA l)) (Per.zA l) z

theorem sigDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply]
  rw [GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem sec_root (o : Om l →+* Per.BdRp l) (ho : IsSec o) (x : Om l) (y : Per.BdRp l)
    (f : Polynomial (Om l)) (hy : Per.θD l y = (x : ℂ_[l])) (h0 : f.eval x = 0)
    (h1 : f.derivative.eval x ≠ 0) (h2 : (f.map o).eval y = 0) : y = o x :=
  root_eq (Per.θD l) (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.1 o x y f (by rw [hy, ho.th]) h0 h1 h2

theorem sec_uniq (o : Om l →+* Per.BdRp l) (ho : IsSec o) (o' : Om l →+* Per.BdRp l) (ho' : IsSec o') :
    o' = o := by
  have hq : o'.comp (algebraMap ℚ_[l] (Om l)) = o.comp (algebraMap ℚ_[l] (Om l)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => ?_)
    exact (ho'.z z).trans (ho.z z).symm
  refine RingHom.ext fun x => ?_
  have hs : IsSeparable ℚ_[l] x := Algebra.IsSeparable.isSeparable ℚ_[l] x
  refine sec_root o ho x (o' x) ((minpoly ℚ_[l] x).map (algebraMap ℚ_[l] (Om l))) (ho'.th x) ?_ ?_ ?_
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]
  · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact Polynomial.Separable.aeval_derivative_ne_zero hs (minpoly.aeval _ _)
  · rw [Polynomial.map_map, ← hq, ← Polynomial.map_map, Polynomial.eval_map_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]

theorem sec_equiv (o : Om l →+* Per.BdRp l) (ho : IsSec o) (g : Per.Gq l) (x : Om l) :
    Per.σDp g (o x) = o (g x) := by
  have h : IsSec (((Per.σDp g).comp o).comp (g.symm : Om l →+* Om l)) := by
    constructor
    · intro x
      change Per.θD l (Per.σDp g (o (g.symm x))) = _
      rw [(GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2, ho.th, GlobalTheory.RingBasics.σC_coe, AlgEquiv.apply_symm_apply]
    · intro z
      change Per.σDp g (o (g.symm (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])))) = _
      rw [AlgEquiv.commutes, ho.z, sigDp_aDp, sigA_zA]
  have := RingHom.congr_fun (sec_uniq o ho _ h) (g x)
  rw [← this]
  change _ = Per.σDp g (o (g.symm (g x)))
  rw [AlgEquiv.symm_apply_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) :=
  fun _ _ o ho => ⟨sec_root o ho, sec_uniq o ho, sec_equiv o ho⟩

end GlobalTheory.MemLoc.SecUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) := by
  first | exact @GlobalTheory.MemLoc.SecUniq.main | exact GlobalTheory.MemLoc.SecUniq.main | (intros; apply GlobalTheory.MemLoc.SecUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiSat

section general
variable {R : Type} [CommRing R]

theorem smodEq_iff (p : R) (k : ℕ) (a b : R) :
    (a ≡ b [SMOD (Ideal.span {p} ^ k • ⊤ : Submodule R R)]) ↔ p ^ k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem sat_pow [IsDomain R] (p x : R) (h : ∀ a, x ∣ p * a → x ∣ a) (n : ℕ) :
    ∀ a, x ^ n ∣ p * a → x ^ n ∣ a := by
  by_cases hx : x = 0
  · cases n with
    | zero => intro a _; simp
    | succ n => subst hx; simpa using h
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := h a ((dvd_pow_self x n.succ_ne_zero).trans ha)
    rw [pow_succ'] at ha ⊢
    rw [mul_left_comm, mul_dvd_mul_iff_left hx] at ha
    exact mul_dvd_mul_left x (ih b ha)

theorem sat_ppow (p y : R) (h : ∀ a, y ∣ p * a → y ∣ a) (k : ℕ) :
    ∀ a, y ∣ p ^ k * a → y ∣ a := by
  induction k with
  | zero => intro a ha; simpa using ha
  | succ k ih =>
    intro a ha
    rw [pow_succ', mul_assoc] at ha
    exact ih a (h _ ha)

theorem quot_dvd_iff (p y : R) (k : ℕ) (a : R) :
    (Ideal.Quotient.mk (Ideal.span {y}) p) ^ k ∣ Ideal.Quotient.mk (Ideal.span {y}) a ↔
      ∃ b c, a = y * b + p ^ k * c := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    obtain ⟨b, hb⟩ := hc
    exact ⟨b, c, by linear_combination hb⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨b, by ring⟩

theorem complete_quot [IsDomain R] (p y : R) [hc : IsAdicComplete (Ideal.span {p}) R]
    (h : ∀ a, y ∣ p * a → y ∣ a) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {y}) p}) (R ⧸ Ideal.span {y}) := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [smodEq_iff, sub_zero, quot_dvd_iff] at hx
    choose b c hbc using hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hy : y = 0
    · subst hy
      have : a = 0 := IsHausdorff.haus' (I := Ideal.span {p}) a fun k => by
        rw [smodEq_iff]
        exact ⟨c k, by linear_combination hbc k⟩
      simp [this]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) b fun {m n} hmn => by
      rw [smodEq_iff]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have e : y * (b m - b (m + d)) = p ^ m * (p ^ d * c (m + d) - c m) := by
        linear_combination hbc (m + d) - hbc m
      obtain ⟨w, hw⟩ := sat_ppow p y h m _ ⟨_, e.symm⟩
      refine ⟨w, mul_left_cancel₀ hy ?_⟩
      rw [e, hw]; ring
    have : a - y * L = 0 := IsHausdorff.haus' (I := Ideal.span {p}) _ fun k => by
      obtain ⟨w, hw⟩ := (smodEq_iff p k _ _).1 (hL k)
      rw [smodEq_iff]
      exact ⟨c k + y * w, by linear_combination hbc k + y * hw⟩
    exact ⟨L, by linear_combination this⟩
  · intro f hf
    choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    have h1 : ∀ n, ∃ b c, g n - g (n + 1) = y * b + p ^ n * c := fun n => by
      have := (smodEq_iff _ n _ _).1 (hf (Nat.le_succ n))
      rwa [← hg, ← hg, ← map_sub, quot_dvd_iff] at this
    choose b c hbc using h1
    let u : ℕ → R := fun n => g n + y * ∑ i ∈ Finset.range n, b i
    have hu : ∀ n, p ^ n ∣ u n - u (n + 1) := fun n =>
      ⟨c n, by simp only [u, Finset.sum_range_succ]; linear_combination hbc n⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) u fun {m n} hmn => by
      rw [smodEq_iff]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow p hmn).trans (hu n))
        rwa [sub_add_sub_cancel] at this
    refine ⟨Ideal.Quotient.mk _ L, fun n => ?_⟩
    obtain ⟨w, hw⟩ := (smodEq_iff p n _ _).1 (hL n)
    rw [smodEq_iff, ← hg, ← map_sub, quot_dvd_iff]
    exact ⟨-∑ i ∈ Finset.range n, b i, w, by simp only [u] at hw; linear_combination hw⟩

end general

theorem xi_sat : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ (l : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ IsAdicComplete (Ideal.span {(l : Per.Ainf l ⧸ Ideal.span {xi e ^ n})}) (Per.Ainf l ⧸ Ideal.span {xi e ^ n}) := by
  intro l _ e he n
  have := (GlobalTheory.T.usage l).1
  have hk := GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he
  have h1 : ∀ a : Per.Ainf l, xi e ∣ (l : Per.Ainf l) * a → xi e ∣ a := fun a ha => by
    rw [← hk] at ha ⊢
    rw [map_mul, map_natCast, mul_eq_zero] at ha
    refine ha.resolve_left fun h0 => GlobalTheory.RingBasics.p_ne_zero (p := l) ?_
    simpa using congrArg Subtype.val h0
  have h2 := sat_pow _ _ h1 n
  refine ⟨h2, ?_⟩
  have : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  have := complete_quot (l : Per.Ainf l) (xi e ^ n) h2
  rwa [map_natCast] at this

end GlobalTheory.MemLoc.XiSat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientCompleteStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ (l : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ IsAdicComplete (Ideal.span {(l : Per.Ainf l ⧸ Ideal.span {xi e ^ n})}) (Per.Ainf l ⧸ Ideal.span {xi e ^ n}) := by
  first | exact @GlobalTheory.MemLoc.XiSat.xi_sat | exact GlobalTheory.MemLoc.XiSat.xi_sat | (intros; apply GlobalTheory.MemLoc.XiSat.xi_sat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ax_sen_tate : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]),
    (∀ g ∈ H, Per.σC g x = x) →
      x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  intro l _ H x hx
  obtain ⟨c, hc, hax⟩ := GlobalTheory.T.bounded_orbit_has_nearby_fixed_point l
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hd : DenseRange (fun y : Om l => (y : ℂ_[l])) := by
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_closure
    | ih a => exact subset_closure ⟨a, rfl⟩
  have hδ : 0 < ε / (2 * c + 2) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x hδ
  set δ := ε / (2 * c + 2) with hδdef
  have hmul : δ * (2 * c + 2) = ε := by
    rw [hδdef]; field_simp
  rw [dist_eq_norm] at ha
  have hsub : ∀ u v : Om l, ‖u - v‖ = ‖(u : ℂ_[l]) - (v : ℂ_[l])‖ := by
    intro u v
    rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, PadicComplex.coe_eq,
      PadicComplex.coe_eq, map_sub]
  obtain ⟨y, hy, hxy⟩ := hax H a (2 * δ) (by
    intro g hg
    have h1 : ((g a : Om l) : ℂ_[l]) - (a : ℂ_[l])
        = (x - (a : ℂ_[l])) - Per.σC g (x - (a : ℂ_[l])) := by
      rw [map_sub, hx g hg, GlobalTheory.RingBasics.σC_coe]; ring
    rw [hsub, h1]
    have h2 := norm_sub_le (x - (a : ℂ_[l])) (Per.σC g (x - (a : ℂ_[l])))
    rw [GlobalTheory.RingBasics.norm_σC] at h2
    linarith)
  refine ⟨(y : ℂ_[l]), ⟨y, hy, rfl⟩, ?_⟩
  rw [hsub] at hxy
  have h3 := norm_add_le (x - (a : ℂ_[l])) ((a : ℂ_[l]) - (y : ℂ_[l]))
  rw [sub_add_sub_cancel] at h3
  rw [dist_eq_norm]
  nlinarith

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosureStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]), (∀ g ∈ H, Per.σC g x = x) → x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  first | exact @GlobalTheory.MemLoc.ax_sen_tate | exact GlobalTheory.MemLoc.ax_sen_tate | (intros; apply GlobalTheory.MemLoc.ax_sen_tate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPower
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem dense_ker_of_bounded {A R C Q : Type} [CommRing A] [CommRing R] [CommRing C] [CommRing Q]
    (p : ℕ) (α : A →+* R) (i : R →+* C) (f : C →+* Q) (N : ℕ)
    (hd : ∀ (x : C) (r : ℕ), ∃ (s : R) (z : C), x = i s + (p : C) ^ r * z)
    (hb : ∀ x : C, ∃ a : A, (p : Q) ^ N * f x = f (i (α a)))
    (x : C) (hx : f x = 0) :
    ∃ (u : R) (z : C), f (i u) = 0 ∧ x = i u + (p : C) * z := by
  obtain ⟨s, z, rfl⟩ := hd x (N + 1)
  obtain ⟨a, ha⟩ := hb z
  refine ⟨s + (p : R) * α a, (p : C) ^ N * z - i (α a), ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_pow, map_natCast] at hx
    rw [map_add (f := _), map_mul, map_natCast, map_add (f := _), map_mul, map_natCast, ← ha, ← hx]
    ring
  · rw [map_add (f := _), map_mul, map_natCast]
    ring

theorem ev_algebraMap (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem fil_dense : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  intro l _ j hj n x hx
  obtain ⟨N, hN⟩ := hj.bdd n
  have h0 : ∀ u : Per.Acris0 l, ((Per.ev l n).comp j) (algebraMap (Per.Acris0 l) (Per.Acris l) u) =
      Ideal.Quotient.mk _ (u : Per.AinfP l) := fun u => by
    rw [RingHom.comp_apply, hj.on0, ev_algebraMap]
  obtain ⟨u, z, hu, hz⟩ := dense_ker_of_bounded l (algebraMap (Per.Ainf l) (Per.Acris0 l))
    (algebraMap (Per.Acris0 l) (Per.Acris l)) ((Per.ev l n).comp j) N (acris_basic l).2.2.1
    (fun y => by
      obtain ⟨a, ha⟩ := hN y
      refine ⟨a, ?_⟩
      rw [map_mul, map_pow, map_natCast] at ha
      rw [h0]
      exact ha) x ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l n (j x)).1 hx)
  refine ⟨u, z, ?_, hz⟩
  rw [h0] at hu
  exact Ideal.Quotient.eq_zero_iff_mem.1 hu

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_filtration_approx_by_envelope_kernel_power : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  first | exact @GlobalTheory.MemLoc.fil_dense | exact GlobalTheory.MemLoc.fil_dense | (intros; apply GlobalTheory.MemLoc.fil_dense <;> assumption)
end
end
