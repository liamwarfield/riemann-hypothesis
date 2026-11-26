module

public import Formalism.TorsionNormIteration.InvIntegralOfClass

@[expose] public section

section -- merged from Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
noncomputable section

universe u v

namespace Formalism.LT.FrobP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_sigma_le {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1)
    (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    first
      | exact pow_le_one₀ (norm_nonneg a) ha
      | exact pow_le_one q (norm_nonneg a) ha
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp.le) h2

def sigmaO {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1) :
    unitBall K →+* unitBall K :=
  (σ.comp (unitBall K).subtype).codRestrict (unitBall K)
    (fun x => norm_sigma_le hσ hp x.1 x.2)

theorem natCast_coe (p : ℕ) : (((p : unitBall K)) : K) = (p : K) := by
  first
    | exact map_natCast (unitBall K).subtype p
    | simp

theorem norm_le_of_mem_span {p : ℕ} (x : unitBall K)
    (hx : x ∈ Ideal.span {((p : ℕ) : unitBall K)}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hy : ‖(y : K)‖ ≤ 1 := y.2
  have e : ((y * ((p : ℕ) : unitBall K) : unitBall K) : K) = (y : K) * (p : K) := by
    rw [← natCast_coe p]
    rfl
  rw [e, norm_mul]
  calc ‖(y : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = ‖(p : K)‖ := one_mul _

theorem mem_span_of_norm_le {p : ℕ} (hp0 : (p : K) ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖(p : K)‖) : x ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
  have hy : ‖(x : K) / (p : K)‖ ≤ 1 := by
    rw [norm_div]
    first
      | exact div_le_one_of_le₀ hx (norm_nonneg _)
      | exact (div_le_one (norm_pos_iff.mpr hp0)).mpr hx
  refine Ideal.mem_span_singleton'.mpr ⟨⟨(x : K) / (p : K), hy⟩, ?_⟩
  apply Subtype.ext
  show (x : K) / (p : K) * ((p : unitBall K) : K) = (x : K)
  rw [natCast_coe, div_mul_cancel₀ _ hp0]

theorem natCast_nonunit {p : ℕ} (hp : ‖(p : K)‖ < 1) :
    ((p : ℕ) : unitBall K) ∈ nonunits (unitBall K) := by
  rw [mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  have h2 : (u : K) * (p : K) = 1 := by
    have h0 := congrArg Subtype.val hu'
    rw [← natCast_coe p]
    exact h0
  have hu1 : ‖(u : K)‖ ≤ 1 := u.2
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖(u : K)‖ * ‖(p : K)‖ ≤ ‖(p : K)‖ := by
    calc ‖(u : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _
  linarith

def liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries ι (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d A, hA d⟩

theorem map_liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries.map (unitBall K).subtype (liftO A hA) = A := by
  ext d
  rw [MvPowerSeries.coeff_map]
  rfl

theorem main {ι : Type v} (p h : ℕ) (hpr : p.Prime) (σ : K →+* K) (hp0 : (p : K) ≠ 0)
    (hp : ‖(p : K)‖ < 1) (hσ : IsFrobLift p (p ^ h) σ) (A : MvPowerSeries ι K)
    (hA : IntegralMv A) :
    DivByMv (p : K) (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero)
      (MvPowerSeries.map σ A)) := by
  classical
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI hchar : CharP (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p :=
    CharP.quotient (unitBall K) p (natCast_nonunit hp)
  haveI : ExpChar (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p := ExpChar.prime hpr
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have hkey : (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})).comp (sigmaO hσ hp)
      = (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h).comp
          (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    first
      | rw [Ideal.Quotient.eq]
      | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply mem_span_of_norm_le hp0
    first
      | exact hσ c.1 c.2
      | (push_cast; exact hσ c.1 c.2)
  have h1 : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h)
        (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) (liftO A hA)) := by
    ext d
    simp only [MvPowerSeries.coeff_map]
    exact RingHom.congr_fun hkey _
  have hmain : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
      ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) = 0 := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h1, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_iterateFrobenius_expand p hpr.ne_zero, sub_self]
  have hcoeffI : ∀ d, MvPowerSeries.coeff d ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
      (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
    intro d
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPowerSeries.coeff_map, hmain, map_zero]
  have h2 : MvPowerSeries.map (unitBall K).subtype (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map σ A := by
    ext d
    first
      | rfl
      | (simp only [MvPowerSeries.coeff_map]; rfl)
  have hsub : MvPowerSeries.map (unitBall K).subtype ((liftO A hA) ^ (p ^ h)
      - MvPowerSeries.expand (p ^ h) hq (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA)))
      = A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) (MvPowerSeries.map σ A) := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h2, map_liftO]
  intro d
  rw [← hsub, MvPowerSeries.coeff_map]
  exact norm_le_of_mem_span (p := p) _ (hcoeffI d)

end Formalism.LT.FrobP

namespace Formalism.LT

open Formalism.G

theorem FrobCongr_valid : Formalism.LT.FrobCongr.{u, v} := by
  intro K _ _ _ p q hq σ hset ι A hA
  obtain ⟨hpr, ⟨h, _, rfl⟩, hp, hσ⟩ := hset
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact FrobP.main p h hpr σ hp0 hp hσ A hA

end Formalism.LT
end
end

section -- merged from Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT.CoeffP

open Formalism.G

section Ball

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma sigma_norm_le_one {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    simpa using pow_le_pow_of_le_one (norm_nonneg a) ha (Nat.zero_le q)
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp) h2

lemma coeff_split (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (f : PowerSeries K) (n : ℕ) :
    coeff n f = coeff n (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst
        ((PowerSeries.X : PowerSeries K) ^ q)) +
      (p : K)⁻¹ * (if q ∣ n then σ (coeff (n / q) f) else 0) := by
  rw [map_sub, map_smul, PowerSeries.coeff_subst_X_pow hq, PowerSeries.coeff_map, smul_eq_mul]
  split_ifs <;> simp

end Ball

private lemma norm_add_inv_mul_mul_norm_pow_succ_le_one {L : Type*} [NormedField L] [IsUltrametricDist L] (a s π : L) (k : ℕ)
    (ha : ‖a‖ ≤ 1) (hs : ‖s‖ * ‖π‖ ^ k ≤ 1) (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) :
    ‖a + π⁻¹ * s‖ * ‖π‖ ^ (k + 1) ≤ 1 := by
  have hn : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hpow0 : 0 ≤ ‖π‖ ^ (k + 1) := pow_nonneg hn.le _
  have hpow1 : ‖π‖ ^ (k + 1) ≤ 1 := by
    simpa using pow_le_pow_of_le_one hn.le hπ (Nat.zero_le (k + 1))
  refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hpow0).trans ?_
  rw [max_mul_of_nonneg _ _ hpow0]
  refine max_le ?_ ?_
  · calc ‖a‖ * ‖π‖ ^ (k + 1) ≤ 1 * 1 := mul_le_mul ha hpow1 hpow0 zero_le_one
      _ = 1 := one_mul 1
  · calc ‖π⁻¹ * s‖ * ‖π‖ ^ (k + 1) = ‖s‖ * ‖π‖ ^ k * (‖π‖⁻¹ * ‖π‖) := by
          rw [norm_mul, norm_inv, pow_succ]; ring
      _ = ‖s‖ * ‖π‖ ^ k := by rw [inv_mul_cancel₀ hn.ne', mul_one]
      _ ≤ 1 := hs

theorem coeffBound : Formalism.LT.CoeffBound.{u} := by
  unfold Formalism.LT.CoeffBound
  intro K _ _ _ p q σ hset f hf0 hfe n
  have hset' : Nat.Prime p ∧ (∃ e, 0 < e ∧ q = p ^ e) ∧ ‖(p : K)‖ < 1 ∧ Formalism.G.IsFrobLift p q σ :=
    hset
  obtain ⟨hp, ⟨e, he, hqe⟩, hp1, hσ⟩ := hset'
  have hq2 : 2 ≤ q := by
    rw [hqe]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt he)
  have hq0 : q ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  have hσb : ∀ (x : K) (k : ℕ), ‖x‖ * ‖(p : K)‖ ^ k ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ k ≤ 1 := by
    intro x k hx
    have h1 : ‖x * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hx
    have h2 := sigma_norm_le_one hp1.le hσ _ h1
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    exact h2
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, dvd_zero _, ?_⟩
    have h0 : PowerSeries.coeff 0 f = 0 := by simpa using hf0
    rw [h0, norm_zero, zero_mul]
    exact zero_le_one
  · have hg : ‖PowerSeries.coeff n (f - (p : K)⁻¹ •
        (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q))‖ ≤ 1 := hfe n
    rw [coeff_split p q hq0 σ f n]
    by_cases hdiv : q ∣ n
    · have hlt : n / q < n := Nat.div_lt_self hn (by omega)
      obtain ⟨k, hk, hkb⟩ := ih (n / q) hlt
      refine ⟨k + 1, ?_, ?_⟩
      · have hnq : n = q * (n / q) := (Nat.mul_div_cancel' hdiv).symm
        rw [hnq, pow_succ']
        exact mul_dvd_mul_left q hk
      · rw [if_pos hdiv]
        exact norm_add_inv_mul_mul_norm_pow_succ_le_one _ _ _ k hg (hσb _ _ hkb) hp1.le hpK
    · refine ⟨0, by rw [pow_zero]; exact one_dvd n, ?_⟩
      rw [if_neg hdiv, mul_zero, add_zero, pow_zero, mul_one]
      exact hg

section Bd

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

def Bd (c : ℝ) (F : MvPowerSeries ι K) : Prop := ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ c

lemma Bd.mono {a b : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (h : a ≤ b) : Bd b F := by
  intro d
  exact (hF d).trans h

lemma Bd.mul {a b : ℝ} {F G : MvPowerSeries ι K} (hF : Bd a F) (hG : Bd b G) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Bd (a * b) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hF x.1) (hG x.2) (norm_nonneg _) ha

lemma Bd.one : Bd 1 (1 : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

lemma Bd.pow {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (ha : 0 ≤ a) :
    ∀ n : ℕ, Bd (a ^ n) (F ^ n)
  | 0 => by simpa using (Bd.one : Bd 1 (1 : MvPowerSeries ι K))
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Bd.pow hF ha n).mul hF (pow_nonneg ha n) ha

lemma Bd.sum {α : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset α} {F : α → MvPowerSeries ι K}
    (h : ∀ i ∈ s, Bd a (F i)) : Bd a (∑ i ∈ s, F i) := by
  intro d
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ha (fun i hi => h i hi d)

lemma Bd.mul_natCast {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (n : ℕ) :
    Bd (‖(n : K)‖ * a) (F * (n : MvPowerSeries ι K)) := by
  intro d
  rw [mul_comm F, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hF d) (norm_nonneg _)

private lemma bd_add' {c : ℝ} {F G : MvPowerSeries ι K} (hF : Bd c F) (hG : Bd c G) :
    Bd c (F + G) := by
  intro d
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))

lemma powp_step {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (_hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    Bd (‖(p : K)‖ ^ (r + 1)) (A ^ p - B ^ p) := by
  have hpn : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hp1 : ‖(p : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K p

  have hexp : A ^ p - B ^ p = ∑ m ∈ Finset.range p,
      (A - B) ^ (m + 1) * B ^ (p - (m + 1)) * ((p.choose (m + 1) : ℕ) : MvPowerSeries ι K) := by
    have h := add_pow (A - B) B p
    rw [sub_add_cancel, Finset.sum_range_succ'] at h
    rw [h, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      add_sub_cancel_right]
  rw [hexp]
  refine Bd.sum (pow_nonneg hpn _) (fun m hm => ?_)
  have hm' : m < p := Finset.mem_range.mp hm
  have hDm : Bd (‖(p : K)‖ ^ (r * (m + 1))) ((A - B) ^ (m + 1)) := by
    rw [pow_mul]
    exact Bd.pow hD (pow_nonneg hpn _) (m + 1)
  have hBm : Bd 1 (B ^ (p - (m + 1))) := by
    have h := Bd.pow hB zero_le_one (p - (m + 1))
    rwa [one_pow] at h
  have hprod : Bd (‖(p : K)‖ ^ (r * (m + 1))) ((A - B) ^ (m + 1) * B ^ (p - (m + 1))) := by
    have h := Bd.mul hDm hBm (pow_nonneg hpn _) zero_le_one
    rwa [mul_one] at h
  refine Bd.mono (Bd.mul_natCast hprod (p.choose (m + 1))) ?_
  rcases Nat.lt_or_ge (m + 1) p with hlt | hge
  ·
    obtain ⟨t, ht⟩ := hp.dvd_choose_self (Nat.succ_ne_zero m) hlt
    have hc : ‖((p.choose (m + 1) : ℕ) : K)‖ ≤ ‖(p : K)‖ := by
      rw [ht, Nat.cast_mul, norm_mul]
      calc ‖(p : K)‖ * ‖(t : K)‖ ≤ ‖(p : K)‖ * 1 :=
            mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one K t) hpn
        _ = ‖(p : K)‖ := mul_one _
    have hr' : ‖(p : K)‖ ^ (r * (m + 1)) ≤ ‖(p : K)‖ ^ r :=
      pow_le_pow_of_le_one hpn hp1 (Nat.le_mul_of_pos_right r (Nat.succ_pos m))
    calc ‖((p.choose (m + 1) : ℕ) : K)‖ * ‖(p : K)‖ ^ (r * (m + 1))
        ≤ ‖(p : K)‖ * ‖(p : K)‖ ^ r := mul_le_mul hc hr' (pow_nonneg hpn _) hpn
      _ = ‖(p : K)‖ ^ (r + 1) := by ring
  ·
    have hm1 : m + 1 = p := Nat.le_antisymm (Nat.succ_le_of_lt hm') hge
    rw [hm1, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
    apply pow_le_pow_of_le_one hpn hp1
    calc r + 1 ≤ r * 2 := by omega
      _ ≤ r * p := Nat.mul_le_mul_left r hp.two_le

lemma powpj {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    ∀ j : ℕ, Bd (‖(p : K)‖ ^ (r + j)) (A ^ (p ^ j) - B ^ (p ^ j))
  | 0 => by simpa using hD
  | j + 1 => by
    rw [pow_succ p j, pow_mul, pow_mul, ← add_assoc]
    exact powp_step hp (by omega) (by simpa using hA.pow zero_le_one (p ^ j))
      (by simpa using hB.pow zero_le_one (p ^ j)) (powpj hp hr hA hB hD j)

lemma pow_sub_pow_bd {c : ℝ} (hc : 0 ≤ c) {A B : MvPowerSeries ι K} (hA : Bd 1 A) (hB : Bd 1 B)
    (hD : Bd c (A - B)) (m : ℕ) : Bd c (A ^ m - B ^ m) := by
  induction m with
  | zero =>
    intro d
    simp [hc]
  | succ m ih =>
    have hAm : Bd 1 (A ^ m) := by simpa using Bd.pow hA zero_le_one m
    have e : A ^ (m + 1) - B ^ (m + 1) = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by ring
    rw [e]
    have h1 : Bd c (A ^ m * (A - B)) := by simpa using Bd.mul hAm hD zero_le_one hc
    have h2 : Bd c ((A ^ m - B ^ m) * B) := by simpa using Bd.mul ih hB hc zero_le_one
    exact bd_add' h1 h2

end Bd

theorem powCongr : Formalism.LT.PowCongr.{u, v} := by
  unfold Formalism.LT.PowCongr
  intro K _ _ ι p hp A B hA hB r hr hD j m
  have hA' : Bd 1 A := hA
  have hB' : Bd 1 B := hB
  have hD' : Bd (‖(p : K)‖ ^ r) (A - B) := by
    intro d
    rw [← norm_pow]
    exact hD d
  have h1 := powpj hp hr hA' hB' hD' j
  have hAj : Bd 1 (A ^ (p ^ j)) := by simpa using Bd.pow hA' zero_le_one (p ^ j)
  have hBj : Bd 1 (B ^ (p ^ j)) := by simpa using Bd.pow hB' zero_le_one (p ^ j)
  have h2 := pow_sub_pow_bd (pow_nonneg (norm_nonneg _) _) hAj hBj h1 m
  intro d
  rw [norm_pow, pow_mul, pow_mul]
  exact h2 d

end Formalism.LT.CoeffP

theorem Formalism.LT.CoeffBound_valid : Formalism.LT.CoeffBound.{u} := Formalism.LT.CoeffP.coeffBound

theorem Formalism.LT.PowCongr_valid : Formalism.LT.PowCongr.{u, v} := Formalism.LT.CoeffP.powCongr
end
end

section -- merged from Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd
noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.ExpP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_natCast_of_not_dvd {p m : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * m = 1 := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact ⟨Nat.gcdA p m, Nat.gcdB p m, by push_cast at h; linarith⟩
  have h1 : (1 : K) = (a : K) * (p : K) + (b : K) * (m : K) := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hle : (1 : ℝ) ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(a : K) * p + (b : K) * m‖ := by rw [← h1]
      _ ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := IsUltrametricDist.norm_add_le_max _ _
  have ha := IsUltrametricDist.norm_intCast_le_one K a
  have hb := IsUltrametricDist.norm_intCast_le_one K b
  rcases le_max_iff.1 hle with h | h
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (p : K), norm_nonneg (a : K)]
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (m : K), norm_nonneg (b : K)]

lemma norm_natCast_eq {p n : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(p : K)‖ ^ padicValNat p n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  haveI := Fact.mk hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hp.ne_zero) hm0, _root_.Nat.padicValNat_def, _root_.Nat.multiplicity_prime_pow, _root_.Nat.padicValNat_def,
    _root_.multiplicity_eq_zero_of_not_dvd hm, add_zero]
  push_cast
  rw [norm_mul, norm_pow, norm_natCast_of_not_dvd hp hp1 hm, mul_one]

end Formalism.LT.ExpP
end
end

section -- merged from Formalism.TorsionNormIteration.InverseIntegralClasses.NormSigmaLeOne
noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT

open Formalism.G

namespace InverseIntegralClassesKeyFacts

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

lemma norm_add_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma norm_sub_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  rw [sub_eq_add_neg]; exact norm_add_le_of ha (by simpa using hb)

lemma norm_sigma_le_one {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ 1 := (hσ a ha).trans hp1
  have h2 : ‖a ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have : σ a = (σ a - a ^ q) + a ^ q := by ring
  rw [this]; exact norm_add_le_of h1 h2

end InverseIntegralClassesKeyFacts

open InverseIntegralClassesKeyFacts

theorem FunEqSubst_of (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by
  intro K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hppos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hpne

  set fs : PowerSeries K := PowerSeries.map σ f with hfs
  set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg
  set β : MvPowerSeries ι K := MvPowerSeries.expand q hq (MvPowerSeries.map σ α) with hβ
  have hαS : PowerSeries.HasSubst α := HasSubst.of_constantCoeff_zero hα0
  have hαq0 : MvPowerSeries.constantCoeff (α ^ q) = 0 := by
    rw [map_pow, hα0, zero_pow hq]
  have hαqS : PowerSeries.HasSubst (α ^ q) := HasSubst.of_constantCoeff_zero hαq0
  have hmα0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ α) = 0 := by
    simp [hα0]
  have hmαS : PowerSeries.HasSubst (MvPowerSeries.map σ α) := HasSubst.of_constantCoeff_zero hmα0
  have hβ0 : MvPowerSeries.constantCoeff β = 0 := by
    rw [hβ, MvPowerSeries.constantCoeff_expand, hmα0]
  have hβS : PowerSeries.HasSubst β := HasSubst.of_constantCoeff_zero hβ0
  have hXqS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries K) ^ q) :=
    HasSubst.of_constantCoeff_zero' (by simp [hq])

  have hdec : f.subst α - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α))
      = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β) := by
    have e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) := by
      rw [hg]; abel
    have e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q) := by
      rw [PowerSeries.subst_comp_subst_apply hXqS hαS, PowerSeries.subst_pow hαS,
        PowerSeries.subst_X hαS]
    have e3 : MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = fs.subst β := by
      rw [PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]
    have e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q) := by
      conv_lhs => rw [e1]
      rw [PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]
    rw [e3, e4, smul_sub]; abel

  have hXqI : IntegralPS ((PowerSeries.X : PowerSeries K) ^ q) := by
    intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hαqI : IntegralMv (α ^ q) := by
    have := h4 K ι _ α hXqI hα0 hαI
    rwa [PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS] at this
  have hdiv : DivByMv (p : K) (α ^ q - β) := h7 K p q hq σ hS ι α hαI
  have hβI : IntegralMv β := by
    intro d
    have e : MvPowerSeries.coeff d β
        = MvPowerSeries.coeff d (α ^ q) - MvPowerSeries.coeff d (α ^ q - β) := by
      rw [map_sub]; ring
    rw [e]
    exact norm_sub_le_of (hαqI d) ((hdiv d).trans hp1')
  have hgI : IntegralMv (g.subst α) := h4 K ι g α hfT hα0 hαI

  have hbr : ∀ d, ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖ := by
    intro d
    rw [map_sub, PowerSeries.coeff_subst hαqS, PowerSeries.coeff_subst hβS,
      ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hαqS fs d)
        (PowerSeries.coeff_subst_finite hβS fs d)]
    apply norm_finsum_le (norm_nonneg _)
    intro n
    rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]
    obtain ⟨k, hkdvd, hk⟩ := h5 K p q σ hS f hf0 hfT n
    obtain ⟨m, rfl⟩ := hkdvd
    have hn : q ^ k * m = p ^ (h * k) * m := by rw [hqh, ← pow_mul]
    have hdiv' : DivByMv ((p : K) ^ 1) (α ^ q - β) := by simpa using hdiv
    have hc0 := h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d
    rw [← hn] at hc0
    have hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
      have h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hk
      have h' := norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hc : ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ := by
      refine hc0.trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k hh)) (norm_nonneg _)
    calc ‖σ (coeff (q ^ k * m) f)‖ * ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖σ (coeff (q ^ k * m) f)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = (‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _

  unfold IsFunEqTypeMv
  rw [hdec]
  intro d
  rw [map_add (f := _), MvPowerSeries.coeff_smul]
  refine norm_add_le_of (hgI d) ?_
  rw [norm_mul, norm_inv]
  calc ‖(p : K)‖⁻¹ * ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖
      ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ := mul_le_mul_of_nonneg_left (hbr d) (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := inv_mul_cancel₀ hppos.ne'

end Formalism.LT
end
end
