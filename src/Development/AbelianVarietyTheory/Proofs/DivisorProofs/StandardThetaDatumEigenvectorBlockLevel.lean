module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelMovesCosetVectorIntegralPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalAboveOfDvdNormHost
open NumberField

namespace GlobalTheory.MaximalIdealDividingNorm

theorem exists_maximal_above_of_dvd_norm {K : Type*} [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 K) ∈ P := by
  obtain ⟨P, hmax, hunder, hdiv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔪 hd
  refine ⟨P, hmax, Ideal.le_of_dvd hdiv, ?_⟩
  have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := Ideal.mem_comap.mp h1
  rwa [map_natCast] at h2

theorem exists_maximal_above_of_dvd_norm_host (D : Formalism.BasicNotions.D7)
    (𝔪 : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E)) (_h𝔪 : 𝔪 ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E),
      P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 (Formalism.BasicNotions.D7.host D).E) ∈ P :=
  exists_maximal_above_of_dvd_norm 𝔪 hp hd

end GlobalTheory.MaximalIdealDividingNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminant
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

open GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.SkewCentral

theorem nat_split (m : ℕ) : ∀ N : ℕ, 0 < N → ∃ a b : ℕ, N = a * b ∧ a ∣ m ^ N ∧ Nat.Coprime b m := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hc : Nat.Coprime N m
    · exact ⟨1, N, by ring, one_dvd _, hc⟩
    · obtain ⟨p, hp, hpN, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
      obtain ⟨N1, rfl⟩ := hpN
      have hN1 : 0 < N1 := Nat.pos_of_mul_pos_left hN
      have hlt : N1 < p * N1 := by nlinarith [hp.two_le]
      obtain ⟨a, b, e, ha, hb⟩ := ih N1 hlt hN1
      refine ⟨p * a, b, by rw [e]; ring, ?_, hb⟩
      calc p * a ∣ m * m ^ N1 := Nat.mul_dvd_mul hpm ha
        _ = m ^ (N1 + 1) := by ring
        _ ∣ m ^ (p * N1) := pow_dvd_pow m (by nlinarith [hp.two_le])

theorem exists_sym_idem (D : D7) (m : ℕ) (hm : 0 < m) : ∃ e ∈ OhE D, e * e = e ∧ sgA D e = e ∧
    (∀ n : ℕ, 0 < n → Nat.Coprime n m → ∃ w ∈ OhE D, e = (n : AE D) * w) ∧
    (∀ k : ℕ, ∃ w ∈ OhE D, 1 - e = (m : AE D) ^ k * w) := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl m hm
  have h2 : ∀ k : ℕ, ∃ v ∈ OhE D, f = (m : AE D) ^ k * v := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, h⟩ := ih
      refine ⟨v * w, mul_mem hv hw, ?_⟩
      calc f = f * f := hff.symm
        _ = ((m : AE D) ^ k * v) * ((m : AE D) * w) := by rw [← h, ← hfw]
        _ = _ := by ring
  have hsf : sgA D f * sgA D f = sgA D f := by rw [← map_mul, hff]
  refine ⟨1 - f * sgA D f, sub_mem (one_mem _) (mul_mem hf (VacMove.sgA_mem D hf)), ?_, ?_, ?_, ?_⟩
  · linear_combination (sgA D f * sgA D f) * hff + f * hsf - 0 * hff
  · rw [map_sub, map_one, map_mul, VacMove.sgA_sgA, mul_comm]
  · intro n hn hnm
    obtain ⟨v, hv, e⟩ := h3 n hn hnm.symm
    have e' := congrArg (sgA D) e
    rw [map_sub, map_one, map_mul, map_natCast] at e'
    refine ⟨v + f * sgA D v, add_mem hv (mul_mem hf (VacMove.sgA_mem D hv)), ?_⟩
    linear_combination e + f * e'
  · intro k
    obtain ⟨v, hv, e⟩ := h2 k
    exact ⟨v * sgA D f, mul_mem hv (VacMove.sgA_mem D hf), by rw [e]; ring⟩

theorem exists_max_over (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Ideal.absNorm 𝔪) : ∃ P : Ideal (𝓞 D.host.E), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 D.host.E) ∈ P := by
  first
  | exact @_root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host
  | exact _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host
  | (apply _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host <;> assumption)
  | (intros; apply _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host ..)

theorem coprime_of_inert (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) (hc : IsCoprime 𝔪 (D.host.conj • 𝔪))
    {q : ℕ} (hq : q.Prime) (hi : InertQ D q) : Nat.Coprime q (Ideal.absNorm 𝔪) := by
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  obtain ⟨P, hP, hle, hqP⟩ := exists_max_over D 𝔪 h0 hq hd
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have hcP := hi P hP.isPrime hP0 hqP
  have h2 : D.host.conj • 𝔪 ≤ P := hcP ▸ Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hle
  rw [Ideal.isCoprime_iff_sup_eq] at hc
  exact hP.ne_top (eq_top_iff.2 (hc ▸ sup_le hle h2))

theorem dvd_of_mem (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Ideal.absNorm 𝔪) {m : ℕ} (hm : (m : 𝓞 D.host.E) ∈ 𝔪) : p ∣ m := by
  by_contra h
  obtain ⟨P, hP, hle, hpP⟩ := exists_max_over D 𝔪 h0 hp hd
  have hcop : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  obtain ⟨u, v, e⟩ := hcop
  have e' := congrArg (Int.cast : ℤ → 𝓞 D.host.E) e
  push_cast at e'
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpP) (Ideal.mul_mem_left _ _ (hle hm))

end GlobalTheory.SkewCentral

namespace GlobalTheory.SkewCentral

def glue (D : D7) (e : AE D) (a : D.host.E) : AE D := e * inc D a + (1 - e)

theorem glue_mul (D : D7) {e : AE D} (he : e * e = e) (a b : D.host.E) :
    glue D e a * glue D e b = glue D e (a * b) := by
  unfold glue; rw [map_mul]
  linear_combination (inc D a * inc D b - inc D a - inc D b + 1) * he

theorem glue_one (D : D7) (e : AE D) : glue D e 1 = 1 := by
  unfold glue; rw [map_one]; ring

theorem sgA_glue (D : D7) {e : AE D} (hs : sgA D e = e) (a : D.host.E) :
    sgA D (glue D e a) = glue D e (D.host.conj a) := by
  unfold glue; rw [map_add (f := _), map_mul, map_sub, map_one, hs, PtsMem.sgA_inc]

def glueU (D : D7) {e : AE D} (he : e * e = e) (a : D.host.E) (ha : a ≠ 0) : (AE D)ˣ :=
  ⟨glue D e a, glue D e a⁻¹, by rw [glue_mul D he, mul_inv_cancel₀ ha, glue_one],
    by rw [glue_mul D he, inv_mul_cancel₀ ha, glue_one]⟩

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← AlgEquiv.mul_apply, VacInt.conj_mul_self]; rfl

end GlobalTheory.SkewCentral

namespace GlobalTheory.SkewCentral

theorem natCast_mem_conj (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {M : ℕ} (h : (M : 𝓞 D.host.E) ∈ 𝔪) :
    (M : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : D.host.conj⁻¹ • (M : 𝓞 D.host.E) = M :=
    map_natCast (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj⁻¹) M
  rwa [this]

theorem exists_skew_scalar (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) (hc : IsCoprime 𝔪 (D.host.conj • 𝔪)) :
    ∃ y s : (AE D)ˣ, s * sgU D s = 1 ∧ y = s * sgU D y ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((y : AE D) - 1) ∧ ZeroAt D q ((s : AE D) - 1)) ∧
      ∀ t : D.host.E, t ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
        ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) :
          FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ↔
        ((s⁻¹ : (AE D)ˣ) : AE D) * inc D t ∈ OhE D := by
  set ι := algebraMap (𝓞 D.host.E) D.host.E with hι
  set M := Ideal.absNorm 𝔪 with hMdef
  have hM : 0 < M := Nat.pos_of_ne_zero (by rwa [hMdef, Ne, Ideal.absNorm_eq_zero_iff])
  have hMm : (M : 𝓞 D.host.E) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  have hMc := natCast_mem_conj D 𝔪 hMm
  obtain ⟨m0, n0, β, hm0, hn0, hmn, hm0B, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator 𝔪 h0
  have hn0M : Nat.Coprime n0 M := by
    apply Nat.coprime_of_dvd
    intro p hp hpn hpM
    have h1 := dvd_of_mem D 𝔪 h0 hp hpM hm0B
    exact hp.not_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd h1 hpn)
  obtain ⟨e, heO, hee, hse, hen, hem⟩ := exists_sym_idem D M hM
  have hβE : ι β ≠ 0 := by
    rw [hι, Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]; exact hβ0
  set b' := D.host.conj (ι β) with hb'
  have hb'0 : b' ≠ 0 := by rw [hb', Ne, map_eq_zero_iff _ D.host.conj.injective]; exact hβE
  have hzero : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q e := by
    intro q hq hi k
    have hcop := coprime_of_inert D 𝔪 h0 hc hq hi
    obtain ⟨w, hw, he'⟩ := hen (q ^ k) (pow_pos hq.pos k) (Nat.Coprime.pow_left k hcop)
    exact ⟨1, one_pos, Nat.coprime_one_left _, w, hw, by rw [he']; push_cast; ring⟩
  refine ⟨glueU D hee (ι β) hβE, glueU D hee (ι β / b') (div_ne_zero hβE hb'0), ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    change glue D e _ * sgA D (glue D e _) = 1
    have : ι β / b' * D.host.conj (ι β / b') = 1 := by
      rw [map_div₀, ← hb', conj_conj]; field_simp
    rw [sgA_glue D hse, glue_mul D hee, this, glue_one]
  · apply Units.ext
    change glue D e _ = glue D e _ * sgA D (glue D e _)
    rw [sgA_glue D hse, glue_mul D hee, ← hb', div_mul_cancel₀ _ hb'0]
  · intro q hq hi
    constructor
    · have := VacMove.zeroAt_mul D hq (hzero q hq hi) (inc D (ι β) - 1)
      convert this using 1
      change glue D e _ - 1 = _
      unfold glue; ring
    · have := VacMove.zeroAt_mul D hq (hzero q hq hi) (inc D (ι β / b') - 1)
      convert this using 1
      change glue D e _ - 1 = _
      unfold glue; ring
  · intro t
    change _ ↔ glue D e (ι β / b')⁻¹ * inc D t ∈ OhE D
    rw [inv_div]
    have hc0 : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
      intro hb
      rw [hb, Ideal.mem_bot] at hMc
      exact hM.ne' (by exact_mod_cast hMc)
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero hc0]
    simp only [FractionalIdeal.mem_coeIdeal]

    constructor
    · intro ht
      obtain ⟨a1, ha1, e1⟩ := ht _ ⟨D.host.conj • β, Ideal.smul_mem_pointwise_smul _ _ _ hβB, rfl⟩
      obtain ⟨a2, ha2, e2⟩ := ht _ ⟨(M : 𝓞 D.host.E), hMc, rfl⟩
      rw [Formalism.L2.Pj.algebraMap_conj_smul, ← hι, ← hb'] at e1
      rw [map_natCast] at e2
      obtain ⟨c, hc⟩ := hdvd a1 ha1
      have hc' : ι c = (n0 : D.host.E) * (b' / ι β) * t := by
        have := congrArg ι hc
        rw [map_mul, map_mul, map_natCast, e1] at this
        field_simp
        linear_combination -this
      obtain ⟨w, hw, ew⟩ := hen n0 hn0 hn0M
      obtain ⟨w', hw', ew'⟩ := hem 1
      have key : glue D e (b' / ι β) * inc D t = w * inc D (ι c) + w' * inc D (ι a2) := by
        rw [hc', e2, map_mul, map_mul, map_mul, map_natCast, map_natCast]
        unfold glue
        linear_combination (inc D (b' / ι β) * inc D t) * ew + inc D t * ew'
      rw [key]
      exact add_mem (mul_mem hw ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (RingOfIntegers.isIntegral_coe c)))
        (mul_mem hw' ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (RingOfIntegers.isIntegral_coe a2)))
    · intro hX y ⟨b0, hb0, hy⟩
      subst hy
      have hX1 : e * inc D (b' / ι β * t) ∈ OhE D := by
        have := mul_mem heO hX
        convert this using 1
        unfold glue
        rw [map_mul]
        linear_combination (inc D t - inc D (b' / ι β) * inc D t) * hee
      have hX2 : (1 - e) * inc D t ∈ OhE D := by
        have := mul_mem (sub_mem (one_mem _) heO) hX
        convert this using 1
        unfold glue
        linear_combination (inc D (b' / ι β) * inc D t - inc D t) * hee

      obtain ⟨N, hN, hNu⟩ := VacMove.exists_nat_denom D (inc D (b' / ι β * t))
      obtain ⟨a, b, hab, ha, hb⟩ := nat_split M N hN
      obtain ⟨wN, hwN, ewN⟩ := hem N
      obtain ⟨a', ha'⟩ := ha
      have ewN' : 1 - e = (a : AE D) * (a' : AE D) * wN := by
        rw [ewN]; exact_mod_cast (congrArg (fun n : ℕ => (n : AE D) * wN) ha')
      have hNab : (N : AE D) = (a : AE D) * (b : AE D) := by exact_mod_cast congrArg (Nat.cast : ℕ → AE D) hab
      have hbU : inc D ((b : D.host.E) * (b' / ι β * t)) ∈ OhE D := by
        have e3 : inc D ((b : D.host.E) * (b' / ι β * t)) =
            (b : AE D) * (e * inc D (b' / ι β * t)) + (wN * a') * ((N : AE D) * inc D (b' / ι β * t)) := by
          rw [map_mul (inc D), map_natCast]
          linear_combination ((b : AE D) * inc D (b' / ι β * t)) * ewN' -
            (wN * a' * inc D (b' / ι β * t)) * hNab
        rw [e3]
        exact add_mem (mul_mem (natCast_mem _ _) hX1) (mul_mem (mul_mem hwN (natCast_mem _ _)) hNu)
      obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1
        ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 hbU)

      obtain ⟨N', hN', hNt⟩ := VacMove.exists_nat_denom D (inc D t)
      obtain ⟨a2, b2, hab2, ha2, hb2⟩ := nat_split M N' hN'
      have hb2pos : 0 < b2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hab2; omega)
      obtain ⟨w2, hw2, ew2⟩ := hen b2 hb2pos hb2
      have hNab2 : (N' : AE D) = (a2 : AE D) * (b2 : AE D) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → AE D) hab2
      have hat : inc D ((a2 : D.host.E) * t) ∈ OhE D := by
        have e3 : inc D ((a2 : D.host.E) * t) = (a2 : AE D) * ((1 - e) * inc D t) + w2 * ((N' : AE D) * inc D t) := by
          rw [map_mul (inc D), map_natCast]
          linear_combination ((a2 : AE D) * inc D t) * ew2 - (w2 * inc D t) * hNab2
        rw [e3]
        exact add_mem (mul_mem (natCast_mem _ _) hX2) (mul_mem hw2 hNt)
      obtain ⟨r2, hr2⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1
        ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 hat)
      obtain ⟨a2', ha2'⟩ := ha2
      have hbpos : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)

      have hinv : D.host.conj⁻¹ = D.host.conj := inv_eq_of_mul_eq_one_right (VacInt.conj_mul_self D)
      have hc0 : D.host.conj • b0 ∈ 𝔪 := by
        have := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hb0
        rwa [hinv] at this
      obtain ⟨c, hc⟩ := hdvd _ hc0
      have hE : (n0 : D.host.E) * ι b0 = b' * D.host.conj (ι c) := by
        have := congrArg (fun x => D.host.conj (ι x)) hc
        simp only [hι, map_mul, map_natCast, Formalism.L2.Pj.algebraMap_conj_smul, conj_conj] at this
        rw [hb']; exact this
      have hcop : IsCoprime ((b * n0 : ℕ) : ℤ) ((M ^ (N' + 1) : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hb hn0M))
      obtain ⟨u', v', huv⟩ := hcop
      have huv' := congrArg (Int.cast : ℤ → D.host.E) huv
      push_cast at huv'
      have hM' : (M : D.host.E) ^ N' = (a2 : D.host.E) * a2' := by exact_mod_cast ha2'
      have hr' : ι r * ι β = b * b' * t := by rw [hr]; field_simp
      refine ⟨(u' : 𝓞 D.host.E) * ((r * (D.host.conj • c)) * β) + (v' : 𝓞 D.host.E) * (((a2' : 𝓞 D.host.E) * r2 * b0) * M),
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hβB))
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hMm)), ?_⟩
      have fin : (u' : D.host.E) * (ι r * D.host.conj (ι c) * ι β) + (v' : D.host.E) * ((a2' : D.host.E) * ι r2 * ι b0 * M) =
          t * ι b0 := by
        rw [hr2]
        linear_combination (u' * D.host.conj (ι c)) * hr' - (u' * b * t) * hE -
          (v' * t * ι b0 * M) * hM' + (t * ι b0) * huv'
      simp only [map_add (f := _), map_mul, map_intCast, map_natCast, Formalism.L2.Pj.algebraMap_conj_smul]
      exact fin

end GlobalTheory.SkewCentral

namespace GlobalTheory.SkewCentral

theorem exists_central_skew_move : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ,
    ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧
      x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' ∧ ∀ h : GA D d, h * g' = g' * h := by
  intro D 𝔪 h0 hc d
  obtain ⟨y, s, hss, hys, hin, hmv⟩ := exists_skew_scalar D 𝔪 h0 hc
  let g : GL (Fin d) (AE D) :=
    Units.map (Matrix.scalar (Fin d) : AE D →+* Matrix (Fin d) (Fin d) (AE D)).toMonoidHom s
  have hgv : (g : Matrix (Fin d) (Fin d) (AE D)) = Matrix.scalar (Fin d) (s : AE D) := rfl
  have hgi : ((g⁻¹ : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) =
      Matrix.scalar (Fin d) ((s⁻¹ : (AE D)ˣ) : AE D) := rfl
  have hsg : sgA D (s : AE D) * s = 1 := by
    have := congrArg Units.val hss
    rw [Units.val_mul, Units.val_one, mul_comm] at this
    exact this
  have hgA : g ∈ GA D d := by
    rw [PtsMem.mem_GA, hgv]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, hsg]
    · simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  refine ⟨⟨g, hgA⟩, y ^ d, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hi i j
    change ZeroAt D q ((Matrix.scalar (Fin d) (s : AE D)) i j - (1 : Matrix (Fin d) (Fin d) (AE D)) i j)
    by_cases hij : i = j
    · subst hij
      simpa [Matrix.scalar_apply] using (hin q hq hi).2
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero]
      intro k
      exact ⟨1, one_pos, Nat.coprime_one_left _, 0, zero_mem _, by simp⟩
  · intro x
    change _ ↔ ∀ i, (Matrix.scalar (Fin d) ((s⁻¹ : (AE D)ˣ) : AE D)).mulVec (fun j => inc D (x j)) i ∈ OhE D
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_implies, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    exact forall_congr' fun i => hmv (x i)
  · intro q hq hi
    obtain ⟨c, hc'⟩ := sub_dvd_pow_sub_pow (y : AE D) 1 d
    have e : (y : AE D) ^ d - 1 = ((y : AE D) - 1) * c := by rw [← hc', one_pow]
    rw [Units.val_pow_eq_pow_val, e]
    exact VacMove.zeroAt_mul D hq (hin q hq hi).1 c
  · have hdet : Matrix.GeneralLinearGroup.det g = s ^ d := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, Units.val_pow_eq_pow_val, Matrix.scalar_apply,
        Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change y ^ d = Matrix.GeneralLinearGroup.det g * sgU D (y ^ d)
    rw [hdet, map_pow, ← mul_pow, ← hys]
  · intro h
    apply Subtype.ext
    apply Units.ext
    change (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) * Matrix.scalar (Fin d) (s : AE D) =
      Matrix.scalar (Fin d) (s : AE D) * ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))
    exact (Matrix.scalar_commute (s : AE D) (fun _ => Commute.all _ _) _).eq.symm

end GlobalTheory.SkewCentral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminantStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_lattice_mover_with_determinant : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ,
    ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧
      x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' ∧ ∀ h : GA D d, h * g' = g' * h := by
  first | exact @GlobalTheory.SkewCentral.exists_central_skew_move | exact GlobalTheory.SkewCentral.exists_central_skew_move | (intros; apply GlobalTheory.SkewCentral.exists_central_skew_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNat
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetApprox

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (y : AE D)
    (hy : y ∈ hatId D 𝔪) : ∃ b ∈ 𝔪, ∃ t ∈ IhE D ⊤, inc D (b : D.host.E) - y = (m : AE D) * t := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    obtain ⟨r, w, hw, e⟩ := GlobalTheory.AdelicApprox.exists_approx D m hm s hs
    have hr : inc D r ∈ OhE D := by
      have : inc D r = s - (m : AE D) * w := by rw [e]; ring
      rw [this]
      exact sub_mem hs (mul_mem (natCast_mem _ m) hw)
    have hri : IsIntegral ℤ r := Formalism.UG.P.csGlob_int (F := ℚ) _ hr
    let r' : 𝓞 D.host.E := ⟨r, hri⟩
    have hbr : b * r' ∈ 𝔪 := Ideal.mul_mem_right _ _ hb
    have hbw : inc D (b : D.host.E) * w ∈ OhE D := mul_mem (Formalism.UG.P.adelstab_incl_int b) hw
    refine ⟨b * r', hbr, -(inc D (b : D.host.E) * w), neg_mem ?_, ?_⟩
    · have := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ _ hbw
      simpa using this
    · have hc : ((b * r' : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) * r := rfl
      rw [hc, map_mul, e]
      ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    obtain ⟨b', hb', t', ht', e'⟩ := hy
    refine ⟨b + b', add_mem hb hb', t + t', add_mem ht ht', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination e + e'
  | neg x _ hx =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    refine ⟨-b, neg_mem hb, -t, neg_mem ht, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -e

theorem matrix_approx : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  intro D 𝔪 a d Y hY m hm
  choose b hb t ht e using fun i j => exists_mem_approx D 𝔪 m hm (Y i j) (hY i j)
  refine ⟨Matrix.of fun i j => ((b i j : 𝓞 D.host.E) : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩,
    fun i j => ⟨t i j, ht i j, ?_⟩⟩
  simpa using e i j

end GlobalTheory.FunObj.CosetApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNatStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  first | exact @GlobalTheory.FunObj.CosetApprox.matrix_approx | exact GlobalTheory.FunObj.CosetApprox.matrix_approx | (intros; apply GlobalTheory.FunObj.CosetApprox.matrix_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelMovesCosetVectorIntegralPoint
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetMove

theorem wd_wd_norm (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  have hn : ∀ x : VC D N N', ‖wdPh D T x‖ = 1 := fun x => by
    simp [wdPh, ee, Complex.norm_exp]
  have hc : Hf D T b a = (starRingEnd ℂ) (Hf D T a b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · rw [norm_mul, norm_div, norm_mul, hn, hn, hn, Complex.norm_exp, hc]
    have : (((Real.pi : ℂ) * ((starRingEnd ℂ) (Hf D T a b) - Hf D T a b) / 2)).re = 0 := by
      simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.div_re]
    rw [this]; simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this


set_option maxHeartbeats 1000000 in
theorem om_cosetV_block : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k ∈ intG D a, W.Om 1 h (cosetV D δ 𝔪 0 a d e0) = c • W.Om k 1 (cosetV D δ 𝔪 0 a d e0) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hcop _ h hh hblk
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨G, hGdef⟩ : ∃ G, G = Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := ⟨_, rfl⟩

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd, hcen⟩ := GlobalTheory.T.exists_skew_lattice_mover_with_determinant D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hJ : W.Om 1 g' e0 = χ • G := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (FixKey.suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using FixKey.zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm, hχ, hGdef]
    rfl
  have hc0 : χ ≠ 0 := by rw [hχ]; exact Units.ne_zero _
  have hJe : G = χ⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hgT : W.Om 1 g' e0 ∈ TT D (tor0 D ⊤ δ) a d := W.maps 1 g' e0 hT
  have hJT : G ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact FixKey.TT_smul _ hgT

  obtain ⟨xh, -, hxh⟩ := VacInt.om_vac_right he hT W ((mem_intG h).1 hh)
  obtain ⟨uh, huh⟩ : ∃ u : ℂ, u = ((W.chV.f xh ^ W.ep : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huh] at hxh
  have hhG : W.Om 1 h G = uh • G := by
    have e1 := W.mul 1 1 h g' e0 hT
    have e2 := W.mul 1 1 g' h e0 hT
    rw [mul_one] at e1 e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, hcen, e2, hxh, W.smul _ _ _ _ hT, smul_comm]
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock D 𝔪 h𝔪 hcop had h hh hblk
  obtain ⟨xk, -, hxk⟩ := VacInt.om_vac_left he hT W ((mem_intG k).1 hk)
  obtain ⟨uk, huk⟩ : ∃ u : ℂ, u = ((W.chV'.f xk ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huk] at hxk
  have hkG : W.Om k 1 G = uk • G := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one] at e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, e2, hxk, W.smul _ _ _ _ hT, smul_comm]
  have nuh : ‖uh‖ = 1 := by
    rw [huh, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV.unitary, one_zpow]
  have nuk : ‖uk‖ = 1 := by
    rw [huk, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV'.unitary, one_zpow]

  obtain ⟨x₀, hx₀⟩ : ∃ x, x = unitBlock D 0 a d := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁, hl₁⟩ := W.lift 1 h x₀ G hJT
  obtain ⟨m₂, hm₂, hl₂⟩ := W.lift k 1 x₀ G hJT
  obtain ⟨Y₁, hY₁⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y = ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * x₀.map (inc D) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y =
    x₀.map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) := ⟨_, rfl⟩
  have hkx' : ∀ i j, (Y₁ - Y₂) i j ∈ hatId D 𝔪 := by rw [hY₁, hY₂, hx₀]; exact hkx
  obtain ⟨z, hz⟩ := VacMove.MI_approx (cc := ⊤) top_ne_bot Y₂ (m₁ * m₂) (Nat.mul_pos hm₁ hm₂)
  obtain ⟨w, hw𝔪, hw⟩ := GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat D 𝔪 (Y₁ - Y₂) hkx' m₁ hm₁
  have hc2 : CloseTo D ⊤ m₂ (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ z := by
    have := hz.of_dvd (m := m₂) (dvd_mul_left _ _)
    intro i j
    obtain ⟨y, hy, e⟩ := this i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₂]; simp
  have hc1 : CloseTo D ⊤ m₁ ((1 : GA D a) : GL (Fin a) (AE D)) (h : GL (Fin d) (AE D)) x₀ (z + w) := by
    have h3 := (hz.of_dvd (m := m₁) (dvd_mul_right _ _)).add hw
    have key : z.map (inc D) - Y₂ + (w.map (inc D) - (Y₁ - Y₂)) = (z + w).map (inc D) - Y₁ := by
      ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add (f := _)]; abel
    rw [key] at h3
    intro i j
    obtain ⟨y, hy, e⟩ := h3 i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₁]; simp
  have hWh := hl₁ (z + w) hc1
  have hWk := hl₂ z hc2
  rw [hhG, FixKey.wd_smul, VacMove.pt_add] at hWh
  rw [hkG, FixKey.wd_smul] at hWk

  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_norm D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd
  rw [← hGdef] at hJB
  have hwB := (GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪).2
  have hfix : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ w) G = G := VacMove.wd_fix h1 hc hBk hJB hwB
  have hφ0 : φ ≠ 0 := by intro h0; rw [h0, norm_zero] at hφ1; exact zero_ne_one hφ1
  have hsum := hφ G
  rw [hfix] at hsum
  have hzw : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z + pt D (tor0 D ⊤ δ) δ w) G =
      φ⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hφ0, one_smul]
  have huk0 : uk ≠ 0 := by rw [huk]; exact Units.ne_zero _
  refine ⟨uh * φ⁻¹ * uk⁻¹, by rw [norm_mul, norm_mul, norm_inv, norm_inv, nuh, hφ1, nuk]; simp, k, hk, ?_⟩
  have hWT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G ∈ TT D (tor0 D ⊤ δ) a d :=
    GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT
  unfold cosetV
  rw [← hx₀, ← hGdef]
  rw [W.smul _ _ _ _ hWT, W.smul _ _ _ _ hWT]
  change _ • W.Om 1 h (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G) = _ • _ • W.Om k 1 (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G)
  rw [hWh, hWk, hzw, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FunObj.CosetMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelMovesCosetVectorIntegralPointStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLevel_moves_cosetVector_integral_point : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k ∈ intG D a, W.Om 1 h (cosetV D δ 𝔪 0 a d e0) = c • W.Om k 1 (cosetV D δ 𝔪 0 a d e0) := by
  first | exact @GlobalTheory.FunObj.CosetMove.om_cosetV_block | exact GlobalTheory.FunObj.CosetMove.om_cosetV_block | (intros; apply GlobalTheory.FunObj.CosetMove.om_cosetV_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumEigenvectorBlockLevel
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

theorem sum_mul_right_eq {G M : Type} [Group G] [AddCommMonoid M] (H K : Subgroup G)
    (hn : ∀ g ∈ H, ∀ κ ∈ K, g⁻¹ * κ * g ∈ K) (R : Finset G) (hR : ∀ r ∈ R, r ∈ H)
    (hR2 : ∀ x ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * x ∈ K) (f : G → M) (hf : ∀ x, ∀ κ ∈ K, f (x * κ) = f x)
    (g : G) (hg : g ∈ H) : ∑ r ∈ R, f (r * g) = ∑ r ∈ R, f r := by
  classical
  choose! σ hσ hσu using hR2
  have hmem : ∀ r ∈ R, r * g ∈ H := fun r hr => mul_mem (hR r hr) hg
  refine Finset.sum_nbij (fun r => σ (r * g)) (fun r hr => (hσ _ (hmem r hr)).1) ?_ ?_ ?_
  · intro r1 h1 r2 h2 e
    simp only at e
    have a1 := (hσ _ (hmem r1 h1)).2
    have a2 := (hσ _ (hmem r2 h2)).2
    rw [e] at a1
    have h3 : g⁻¹ * (r1⁻¹ * r2) * g ∈ K := by
      have := mul_mem (inv_mem a1) a2
      simpa [mul_assoc] using this
    have h4 : r1⁻¹ * r2 ∈ K := by
      have := hn g⁻¹ (inv_mem hg) _ h3
      simpa [mul_assoc] using this
    have u1 := hσu r1 (hR r1 h1) r1 ⟨h1, by simpa using K.one_mem⟩
    have u2 := hσu r1 (hR r1 h1) r2 ⟨h2, by simpa using inv_mem h4⟩
    exact u1.trans u2.symm
  · intro r' hr'
    have hx : r' * g⁻¹ ∈ H := mul_mem (hR r' hr') (inv_mem hg)
    obtain ⟨hr, hk⟩ := hσ _ hx
    refine ⟨σ (r' * g⁻¹), hr, ?_⟩
    have h5 : g⁻¹ * (g * r'⁻¹ * σ (r' * g⁻¹)) * g ∈ K := by
      refine hn g hg _ ?_
      have := inv_mem hk
      simpa [mul_assoc] using this
    exact (hσu _ (hmem _ hr) r' ⟨hr', by simpa [mul_assoc] using h5⟩).symm
  · intro r hr
    have := (hσ _ (hmem r hr)).2
    rw [← hf (σ (r * g)) _ this]
    simp

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

theorem congOne_conj {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {g κ : GA D N} (hg : g ∈ intG D N) (hκ : CongOne D 𝔪 κ) :
    CongOne D 𝔪 (g⁻¹ * κ * g) := by
  intro i j
  have e : (((g⁻¹ * κ * g : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((κ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) *
          ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
    have h1 : (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hgi := (mem_intG g).1 hg
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine mul_mem_hatId (hgi l j).1 ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem_hatId (hgi i m).2 (hκ m l)

theorem om_finsum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem stdSum_eig : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → ∀ h ∈ blockLev D 𝔪 d a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 h (stdSum W 𝔪 0 R) = c • stdSum W 𝔪 0 R := by
  intro D δ t0 hc a d e0 vac had W 𝔪 hm hcop hnu R hR1 hR2 _hfix h hh
  obtain ⟨hhi, hb⟩ := (GlobalTheory.T.mem_blockCongruenceLevelSubgroup_iff_stabilizer_entries D 𝔪 d a h).1 hh
  obtain ⟨c, hc1, k, hk, hk'⟩ := GlobalTheory.T.blockLevel_moves_cosetVector_integral_point D δ t0 hc e0 vac had W 𝔪 hm hcop hnu h hhi hb
  refine ⟨c, hc1, ?_⟩
  have hcv := GlobalTheory.T.unitBlockCosetThetaVector_mem_thetaFunctions D δ hc 𝔪 hm 0 a d e0 vac.1
  have hcong : ∀ x, x ∈ congLev D 𝔪 a ↔ x ∈ intG D a ∧ CongOne D 𝔪 x := GlobalTheory.T.mem_principalCongruenceLevelSubgroup_iff_integral_congruent D 𝔪 a
  unfold stdSum
  rw [om_finsum W 1 h R _ (fun r _ => W.maps _ _ _ hcv), Finset.smul_sum]
  have e1 : ∀ r, W.Om 1 h (W.Om r 1 (cosetV D δ 𝔪 0 a d e0)) = c • W.Om (r * k) 1 (cosetV D δ 𝔪 0 a d e0) := by
    intro r
    have m1 := W.mul 1 r h 1 _ hcv
    have m2 := W.mul r 1 1 h _ hcv
    have m3 := W.mul r k 1 1 _ hcv
    simp only [one_mul, mul_one] at m1 m2 m3
    rw [← m1, m2, hk', W.smul _ _ _ _ (W.maps _ _ _ hcv), ← m3]
  simp_rw [e1]
  refine sum_mul_right_eq (intG D a) (congLev D 𝔪 a) (fun g hg κ hκ => ?_) R hR1 (fun x hx => ?_)
    (fun x => c • W.Om x 1 (cosetV D δ 𝔪 0 a d e0)) (fun x κ hκ => ?_) k hk
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    exact (hcong _).2 ⟨mul_mem (mul_mem (inv_mem hg) h1) hg, congOne_conj hg h2⟩
  · obtain ⟨r, ⟨hr, hrx⟩, hu⟩ := hR2 x hx
    exact ⟨r, ⟨hr, (hcong _).2 ⟨mul_mem (inv_mem (hR1 r hr)) hx, hrx⟩⟩,
      fun r' ⟨hr', h'⟩ => hu r' ⟨hr', ((hcong _).1 h').2⟩⟩
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    have m4 := W.mul x κ 1 1 _ hcv
    rw [mul_one] at m4
    rw [m4, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W 𝔪 hm hcop hnu 0 (by omega) κ h1 h2]

end GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumEigenvectorBlockLevelStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → ∀ h ∈ blockLev D 𝔪 d a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 h (stdSum W 𝔪 0 R) = c • stdSum W 𝔪 0 R := by
  first | exact @GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig | exact GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig | (intros; apply GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig <;> assumption)
end
