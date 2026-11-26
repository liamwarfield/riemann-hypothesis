module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabCardOfStabTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLineStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGalois
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLog

theorem exists_full_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
    (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
    ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P _ K b b' hb h
  haveI := K.2
  haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen
  haveI := Fintype.ofFinite (GQ l ⧸ GK K)
  let ι : P.R.B →+* FractionRing P.R.B := algebraMap P.R.B (FractionRing P.R.B)
  have hι : Function.Injective ι := IsFractionRing.injective P.R.B (FractionRing P.R.B)
  let e : GQ l → FractionRing P.R.B ≃+* FractionRing P.R.B := fun g =>
    IsFractionRing.ringEquivOfRingEquiv (A := P.R.B) (B := P.R.B) (P.actQ g).toRingEquiv
  have he : ∀ g z, e g (ι z) = ι (P.actQ g z) := fun g z =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  have hmul : ∀ s g z, e s (e g z) = e (s * g) z := by
    intro s g
    have : (e s).toRingHom.comp (e g).toRingHom = (e (s * g)).toRingHom := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors P.R.B)
      ext z
      show e s (e g (ι z)) = e (s * g) (ι z)
      rw [he, he, he, map_mul, AlgEquiv.mul_apply]
    intro z
    exact RingHom.congr_fun this z
  have hne : ∀ g (z : P.R.B), z ≠ 0 → ι (P.actQ g z) ≠ 0 := fun g z hz =>
    (map_ne_zero_iff ι hι).2 ((map_ne_zero_iff _ (P.actQ g).injective).2 hz)
  let T : GQ l → FractionRing P.R.B := fun g => ι ((kummer P g : ℚ_[l]) • P.tB)
  have hT : ∀ s g, e s (T g) = T (s * g) - T s := by
    intro s g
    simp only [T, he, map_smul, localPrime_galoisAction_periodT, kummer_mul, smul_smul, add_smul, map_add (f := _)]
    rw [mul_comm]; abel
  let f : FractionRing P.R.B := ι b' / ι b
  have hb0 : ι b ≠ 0 := (map_ne_zero_iff ι hι).2 hb
  have hf : ∀ g ∈ GK K, e g f - f = T g := by
    intro g hg
    have h1 := congrArg ι (h g hg)
    simp only [map_sub, map_mul] at h1
    have h2 := hne g b hb
    simp only [f, map_div₀, he]
    field_simp
    linear_combination h1
  let Fn : GQ l → FractionRing P.R.B := fun g => e g f - T g
  have h1 : ∀ s g, e s (Fn g) = Fn (s * g) + T s := by
    intro s g
    simp only [Fn, map_sub, hmul, hT]
    abel
  have h2 : ∀ g (k : ↥(GK K)), Fn (g * k) = Fn g := by
    intro g k
    have e1 : Fn k = f := by simp only [Fn, ← hf k k.2]; abel
    have := h1 g k
    rw [e1] at this
    simp only [Fn] at this ⊢
    linear_combination -this
  have h3 : ∀ g, Fn (QuotientGroup.mk g : GQ l ⧸ GK K).out = Fn g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hk, h2]
  have hnB : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : P.R.B) ≠ 0 := by
    haveI := nontrivial_B P
    rw [← map_natCast (algebraMap ℚ_[l] P.R.B)]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℚ_[l] P.R.B)).2
      (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff ι hι).2 hnB
  let fa : FractionRing P.R.B := ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B)⁻¹ * ∑ q : GQ l ⧸ GK K, Fn q.out
  have hfa : ∀ s, e s fa - fa = T s := by
    intro s
    have h4 : ∑ q : GQ l ⧸ GK K, Fn (s * q.out) = ∑ q : GQ l ⧸ GK K, Fn q.out :=
      Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by
        rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fa, map_mul, map_inv₀, map_natCast, map_sum, h1]
    rw [Finset.sum_add_distrib, h4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  obtain ⟨y, x, hx, hxy⟩ := IsFractionRing.div_surjective (A := P.R.B) fa
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  refine ⟨x, y, hx0, fun g => ?_⟩
  have hxy' : ι y / ι x = fa := hxy
  have k := hfa g
  rw [← hxy', map_div₀, he, he] at k
  have k1 := hne g x hx0
  have k2 : ι x ≠ 0 := (map_ne_zero_iff ι hι).2 hx0
  apply hι
  simp only [map_sub, map_mul]
  field_simp at k
  linear_combination k

end GlobalTheory.Pst.NoLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGaloisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerFracCoboundary_full_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
  ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.Pst.NoLog.exists_full_frac | exact GlobalTheory.Pst.NoLog.exists_full_frac | (intros; apply GlobalTheory.Pst.NoLog.exists_full_frac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaImageDeRhamPlusDvdOfLAdicResidues
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaImageDeRhamPlusDvdOfLAdicResidues
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem betaD_dvd_of_res : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  intro l _ ϖ hk hF y hy
  obtain ⟨-, hker, hA, hD, -⟩ := GlobalTheory.MemLoc.thetaP_facts l
  have hb0 : Per.θP l (beta ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker, hk]; exact Ideal.mem_span_singleton_self _
  have hb : Per.θD l (betaD ϖ) = 0 := by rw [betaD, hD, hb0]
  have hS : ∀ a ∈ Sa ϖ, Per.θP l a ∈ 𝓞_ℂ_[l] := by
    intro a ha
    change a ∈ Algebra.adjoin _ _ at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hb0]; exact zero_mem _
    | algebraMap r => rw [hA]; exact (Per.θ l r).2
    | add x z _ _ hx hz => rw [map_add (Per.θP l)]; exact add_mem hx hz
    | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  have hs : ∀ s ∈ Sg ϖ, ‖Per.θD l s‖ ≤ 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hD]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (hS a ha)
  have h0 : Per.θD l y = 0 := by
    have hle : ∀ k : ℕ, ‖Per.θD l y‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ k := by
      intro k
      obtain ⟨s, hsS, c, hc⟩ := hy k
      have h1 := congrArg (Per.θD l) hc
      rw [map_sub, map_mul, map_mul, hb, zero_mul, sub_eq_zero, map_pow, map_natCast] at h1
      rw [h1, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hs s hsS)
    exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (GlobalTheory.RingBasics.norm_p_lt (p := l))) hle)
  have hmem : y ∈ Per.FilP l 1 := ((GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1 y).1 h0
  rw [hF 1, pow_one] at hmem
  exact Ideal.mem_span_singleton.1 hmem

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaImageDeRhamPlusDvdOfLAdicResiduesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  first | exact @GlobalTheory.Pst.StLat.betaD_dvd_of_res | exact GlobalTheory.Pst.StLat.betaD_dvd_of_res | (intros; apply GlobalTheory.Pst.StLat.betaD_dvd_of_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMem
open GlobalTheory.Pst.StLat

namespace GlobalTheory.Pst.StLat

theorem clos_eq_zero_of_mul_mem {R : Type} [CommRing R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hpu : IsUnit ((p : ℕ) : R)) (π : R) (hπ : π ≠ 0)
    (hsep : ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (S : Subring R)
    (hdiv : ∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s')
    (hres : ∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y)
    (u : R) (hlog : ∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
      π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m))
    (a : R) (r : ℕ) (ha : a ∈ Clos S π) (hau : ((p : ℕ) : R) ^ r * a * u ∈ Clos S π) : a = 0 := by
  obtain ⟨q, hPq⟩ : ∃ q : R, ((p : ℕ) : R) * q = 1 := ⟨((hpu.unit⁻¹ : Rˣ) : R), hpu.mul_val_inv⟩
  have hSC : ∀ s ∈ S, s ∈ Clos S π := fun s hs n => ⟨s, hs, by simp⟩
  have hPC : ((p : ℕ) : R) ∈ Clos S π := natCast_mem _ _

  have stepD : ∀ b ∈ Clos S π, ∀ r' : ℕ, ((p : ℕ) : R) ^ r' * b * u ∈ Clos S π →
      ∃ b' ∈ Clos S π, ((p : ℕ) : R) * b' = b := by
    intro b hb r' hbu
    refine ⟨q * b, ?_, by rw [← mul_assoc, hPq, one_mul]⟩
    intro n
    obtain ⟨s, hs, e, he, w, hw⟩ := hlog (r' + n + 1) (by omega)
    have hm : r' + n + 1 - 1 = r' + n := by omega
    rw [hm] at hw
    set M := p ^ (r' + n + 1) with hMdef
    have hnM : n ≤ M := by
      have h1 : r' + n + 1 < p ^ (r' + n + 1) := Nat.lt_pow_self hp.one_lt
      omega
    have h2M : π ^ (2 * M) = π ^ M * π ^ M := by rw [two_mul, pow_add]
    rw [h2M] at hw
    have hx : b * (((p : ℕ) : R) ^ (r' + n) * u - s) ∈ Clos S π := by
      have : b * (((p : ℕ) : R) ^ (r' + n) * u - s) =
          ((p : ℕ) : R) ^ n * (((p : ℕ) : R) ^ r' * b * u) - b * s := by ring
      rw [this]
      exact sub_mem (mul_mem (pow_mem hPC _) hbu) (mul_mem hb (hSC s hs))
    obtain ⟨s₁, hs₁, c, hc⟩ := hx (2 * M)
    rw [h2M] at hc
    have hs1eq : s₁ = π ^ M * (q * b * e + π ^ M * (q * b * w - c)) := by
      linear_combination (-1 : R) * hc + (q * b) * hw - (b * (((p : ℕ) : R) ^ (r' + n) * u - s)) * hPq
    obtain ⟨s₂, hs₂S, hs₂⟩ := hdiv s₁ hs₁ M ⟨_, hs1eq⟩
    have hcan : q * b * e - s₂ = π ^ M * (c - q * b * w) := by
      apply mul_left_cancel₀ (pow_ne_zero M hπ)
      linear_combination hs₂ - hs1eq
    have he2 : e * e = 1 := by rcases he with rfl | rfl <;> ring
    have heS : e * s₂ ∈ S := by
      rcases he with rfl | rfl
      · simpa using hs₂S
      · simpa using neg_mem hs₂S
    refine ⟨e * s₂, heS, dvd_trans (pow_dvd_pow π hnM) ⟨e * (c - q * b * w), ?_⟩⟩
    linear_combination e * hcan - (q * b) * he2

  have iter : ∀ k : ℕ, ∃ b ∈ Clos S π, ((p : ℕ) : R) ^ k * b = a ∧
      ((p : ℕ) : R) ^ (r + k) * b * u ∈ Clos S π := by
    intro k
    induction k with
    | zero => exact ⟨a, ha, by simp, by simpa using hau⟩
    | succ k ih =>
      obtain ⟨b, hb, hbk, hbu⟩ := ih
      obtain ⟨b', hb', hPb'⟩ := stepD b hb (r + k) hbu
      refine ⟨b', hb', ?_, ?_⟩
      · rw [pow_succ, mul_assoc, hPb', hbk]
      · have : ((p : ℕ) : R) ^ (r + (k + 1)) * b' * u =
            ((p : ℕ) : R) ^ (r + k) * (((p : ℕ) : R) * b') * u := by ring
        rw [this, hPb']
        exact hbu

  by_contra ha0
  classical
  have hex : ∃ n : ℕ, ¬ π ^ n ∣ a := by
    by_contra h
    push_neg at h
    exact ha0 (hsep a h)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    exact this (one_dvd a)
  set i := Nat.find hex - 1 with hidef
  have hi1 : i + 1 = Nat.find hex := by omega
  have hia : π ^ i ∣ a := by
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    simpa using this
  obtain ⟨a₁, ha₁⟩ := hia
  have hna₁ : ¬ π ∣ a₁ := by
    rintro ⟨t, ht⟩
    apply Nat.find_spec hex
    rw [← hi1]
    exact ⟨t, by rw [ha₁, ht, pow_succ]; ring⟩
  apply hna₁
  apply hres a₁
  intro k
  obtain ⟨b, hb, hbk, -⟩ := iter k
  obtain ⟨s, hs, hbs⟩ := hb (i + 1)
  have hib : π ^ i ∣ b := ⟨q ^ k * a₁, by
    have : b = q ^ k * (((p : ℕ) : R) ^ k * b) := by
      rw [← mul_assoc, ← mul_pow, mul_comm q, hPq, one_pow, one_mul]
    rw [this, hbk, ha₁]; ring⟩
  have his : π ^ i ∣ s := by
    have h1 : π ^ i ∣ b - s := dvd_trans (pow_dvd_pow π (Nat.le_succ i)) hbs
    have := dvd_sub hib h1
    simpa using this
  obtain ⟨s', hs'S, hs'⟩ := hdiv s hs i his
  refine ⟨s', hs'S, ?_⟩
  rw [← mul_dvd_mul_iff_left (pow_ne_zero i hπ), ← pow_succ]
  have : π ^ i * (a₁ - ((p : ℕ) : R) ^ k * s') = ((p : ℕ) : R) ^ k * (b - s) := by
    rw [mul_sub, ← ha₁, ← hbk, hs']; ring
  rw [this]
  exact dvd_mul_of_dvd_right hbs _

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos : ∀ {R : Type} [CommRing R] [IsDomain R] (p : ℕ), p.Prime → IsUnit ((p : ℕ) : R) → ∀ (π : R), π ≠ 0 →
  (∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) → ∀ (S : Subring R),
  (∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s') →
  (∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y) →
  ∀ u : R, (∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
    π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m)) →
  ∀ (a : R) (r : ℕ), a ∈ Clos S π → ((p : ℕ) : R) ^ r * a * u ∈ Clos S π → a = 0 := by
  first | exact @GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | exact GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | (intros; apply GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AcrisMemBetaAdicClosureAinfAdjoinBeta
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AcrisMemBetaAdicClosureAinfAdjoinBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris_mem_clos : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  intro l _ j hj ϖ hS hF x n
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x N
  obtain ⟨a, ha⟩ := hN z
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) ((s : Per.AinfP l) + algebraMap (Per.Ainf l) (Per.AinfP l) a),
    ⟨_, add_mem (hS s) (Subalgebra.algebraMap_mem _ a), rfl⟩, ?_⟩
  rw [← Ideal.mem_span_singleton, ← hF, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, map_add (f := _), map_add (f := _), map_mul, map_pow,
    map_natCast, hj.on0, ev_algebraMap, ev_algebraMap]
  rw [ha, map_add (f := _)]
  ring

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AcrisMemBetaAdicClosureAinfAdjoinBetaStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  first | exact @GlobalTheory.Pst.StLat.acris_mem_clos | exact GlobalTheory.Pst.StLat.acris_mem_clos | (intros; apply GlobalTheory.Pst.StLat.acris_mem_clos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomain
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.InvRatFun

variable {F : Type} [Field F]

noncomputable def shift (s : F ≃+* F) (t : F) : F[X] →+* F[X] :=
  (Polynomial.compRingHom (X + C t)).comp (Polynomial.mapRingHom (s : F →+* F))

theorem shift_apply (s : F ≃+* F) (t : F) (r : F[X]) :
    shift s t r = (r.map (s : F →+* F)).comp (X + C t) := rfl

theorem natDegree_shift (s : F ≃+* F) (t : F) (r : F[X]) :
    (shift s t r).natDegree = r.natDegree := by
  rw [shift_apply, natDegree_comp, natDegree_X_add_C, mul_one, natDegree_map]

theorem leadingCoeff_shift (s : F ≃+* F) (t : F) (r : F[X]) :
    (shift s t r).leadingCoeff = s r.leadingCoeff := by
  rw [shift_apply, leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
    leadingCoeff_X_add_C, one_pow, mul_one, leadingCoeff_map]
  rfl

theorem shift_eq_zero_iff (s : F ≃+* F) (t : F) (r : F[X]) : shift s t r = 0 ↔ r = 0 := by
  rw [← leadingCoeff_eq_zero, leadingCoeff_shift, map_eq_zero_iff _ s.injective,
    leadingCoeff_eq_zero]

theorem coeff_comp_X_add_C_sub' (P : F[X]) (r : F) (e : ℕ) (hP : P.degree ≤ (e + 1 : ℕ)) :
    (P.comp (X + C r) - P).coeff e = r * (e + 1) * P.coeff (e + 1) := by
  have h1 : P.natDegree ≤ e + 1 := natDegree_le_of_degree_le hP
  have h2 : (hasseDeriv e P).natDegree ≤ 1 := (natDegree_hasseDeriv_le P e).trans (by omega)
  rw [coeff_sub, ← taylor_apply, taylor_coeff, eq_X_add_C_of_natDegree_le_one h2,
    hasseDeriv_coeff, hasseDeriv_coeff]
  simp [add_comm 1 e]
  ring

variable [CharZero F]

theorem natDegree_eq_zero_of_fixed {ι : Type} (s : ι → F ≃+* F) (t : ι → F)
    (h : ¬ ∃ f : F, ∀ g, s g f - f = t g) (r : F[X]) (hr : r ≠ 0)
    (hfix : ∀ g, shift (s g) (t g) r = r) : r.natDegree = 0 := by
  by_contra hn
  obtain ⟨e, he⟩ : ∃ e, r.natDegree = e + 1 := ⟨r.natDegree - 1, by omega⟩
  set c := r.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hr
  have hsc : ∀ g, s g c = c := fun g => by
    rw [hc, ← leadingCoeff_shift (s g) (t g), hfix g]
  apply h
  refine ⟨-r.coeff e / ((e + 1 : F) * c), fun g => ?_⟩
  have key : (shift (s g) (t g) r).coeff e = r.coeff e := by rw [hfix g]
  have hdeg : (r.map (s g : F →+* F)).degree ≤ (e + 1 : ℕ) := by
    rw [degree_map]; exact (degree_le_natDegree).trans (by rw [he])
  have hsub := coeff_comp_X_add_C_sub' (r.map (s g : F →+* F)) (t g) e hdeg
  rw [coeff_sub, ← shift_apply, key, coeff_map, coeff_map] at hsub
  have hlc : r.coeff (e + 1) = c := by rw [hc, leadingCoeff, he]
  rw [hlc] at hsub
  change _ - s g (r.coeff e) = t g * (e + 1) * s g c at hsub
  rw [hsc g] at hsub
  have he1 : (e + 1 : F) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  rw [map_div₀, map_neg, map_mul, hsc g, map_add (f := _), map_natCast, map_one]
  field_simp
  linear_combination hsub

end GlobalTheory.InvRatFun

namespace GlobalTheory.InvRatFun

variable {F : Type} [Field F] [CharZero F]

theorem dvd_shift_mul {s : F ≃+* F} {t : F} {P Q r : F[X]} (hQ : Q ≠ 0)
    (hPQ : Q * shift s t P = shift s t Q * P) (hr : Q ∣ r * P) : Q ∣ shift s t r * P := by
  obtain ⟨w, hw⟩ := map_dvd (shift s t) hr
  rw [map_mul] at hw
  have hAQ : shift s t Q ≠ 0 := (shift_eq_zero_iff s t Q).not.mpr hQ
  refine ⟨w, ?_⟩
  apply mul_left_cancel₀ hAQ
  linear_combination (-(shift s t r)) * hPQ + Q * hw

theorem eq_C_mul_of_fixed {ι : Type} (s : ι → F ≃+* F) (t : ι → F)
    (h : ¬ ∃ f : F, ∀ g, s g f - f = t g) (P Q : F[X]) (hQ : Q ≠ 0)
    (hPQ : ∀ g, Q * shift (s g) (t g) P = shift (s g) (t g) Q * P) :
    ∃ c : F, P = C c * Q ∧ ∀ g, s g c = c := by
  classical
  have hex : ∃ n, ∃ r : F[X], r.Monic ∧ r.natDegree = n ∧ Q ∣ r * P :=
    ⟨_, Q * C Q.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hQ, rfl,
      ⟨C Q.leadingCoeff⁻¹ * P, by ring⟩⟩
  obtain ⟨q₀, hm, hdeg, hdvd⟩ := Nat.find_spec hex
  have hfix : ∀ g, shift (s g) (t g) q₀ = q₀ := by
    intro g
    set A := shift (s g) (t g)
    have hAm : (A q₀).Monic := by rw [shift_apply]; exact (hm.map _).comp_X_add_C _
    by_contra hne
    have hr : A q₀ - q₀ ≠ 0 := sub_ne_zero.mpr hne
    have hlt : (A q₀ - q₀).degree < (A q₀).degree :=
      degree_sub_lt (by rw [degree_eq_natDegree hAm.ne_zero, degree_eq_natDegree hm.ne_zero,
        natDegree_shift]) hAm.ne_zero (by rw [hAm.leadingCoeff, hm.leadingCoeff])
    have hlt' : (A q₀ - q₀).natDegree < Nat.find hex := by
      rw [← hdeg, ← natDegree_shift (s g) (t g) q₀]; exact natDegree_lt_natDegree hr hlt
    have hd : Q ∣ (A q₀ - q₀) * P := by
      rw [sub_mul]; exact dvd_sub (dvd_shift_mul hQ (hPQ g) hdvd) hdvd
    refine Nat.find_min hex hlt' ⟨(A q₀ - q₀) * C (A q₀ - q₀).leadingCoeff⁻¹,
      monic_mul_leadingCoeff_inv hr,
      natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hr)), ?_⟩
    rw [mul_right_comm]; exact dvd_mul_of_dvd_left hd _
  have h0 := natDegree_eq_zero_of_fixed s t h q₀ hm.ne_zero hfix
  have hq1 : q₀ = 1 := by
    have h1 : q₀.coeff 0 = 1 := by rw [← h0]; exact hm
    rw [eq_C_of_natDegree_eq_zero h0, h1, C_1]
  rw [hq1, one_mul] at hdvd
  obtain ⟨S, rfl⟩ := hdvd
  have hSfix : ∀ g, shift (s g) (t g) S = S := by
    intro g
    have hAQ : shift (s g) (t g) Q ≠ 0 := (shift_eq_zero_iff _ _ Q).not.mpr hQ
    have := hPQ g
    rw [map_mul] at this
    apply mul_left_cancel₀ (mul_ne_zero hQ hAQ)
    linear_combination this
  by_cases hS : S = 0
  · exact ⟨0, by simp [hS], fun g => map_zero _⟩
  have hS0 := natDegree_eq_zero_of_fixed s t h S hS hSfix
  refine ⟨S.leadingCoeff, ?_, fun g => ?_⟩
  · conv_lhs => rw [eq_C_of_natDegree_eq_zero hS0]
    rw [leadingCoeff, hS0, mul_comm]
  · rw [← leadingCoeff_shift (s g) (t g), hSfix g]

end GlobalTheory.InvRatFun

namespace GlobalTheory.InvRatFun

theorem fixed_ratio_const_of {B G : Type} (F : Type) [Field F] [CommRing B] [IsDomain B] [CharZero B] [Algebra B F] [IsFractionRing B F]
    (σ : G → B ≃+* B) (τ : G → B)
    (hτ : ∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g)
    (p q : Polynomial B) (hq : q ≠ 0)
    (hpq : ∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) =
      (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) :
    ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  classical
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  haveI : CharZero F := charZero_of_injective_algebraMap hinj
  have hι0 : ∀ x : B, x ≠ 0 → (algebraMap B F) x ≠ 0 := fun x hx => by
    rwa [Ne, ← map_zero (algebraMap B F), hinj.eq_iff]
  let s : G → F ≃+* F := fun g => IsFractionRing.ringEquivOfRingEquiv (σ g)
  have hs : ∀ g x, s g ((algebraMap B F) x) = (algebraMap B F) (σ g x) := fun g x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (σ g) x
  have hcomp : ∀ g, (algebraMap B F).comp (σ g : B →+* B) = (s g : F →+* F).comp (algebraMap B F) := fun g =>
    RingHom.ext fun x => (hs g x).symm
  have hmap : ∀ g (r : B[X]), ((r.map (σ g : B →+* B)).comp (X + C (τ g))).map (algebraMap B F) =
      shift (s g) ((algebraMap B F) (τ g)) (r.map (algebraMap B F)) := by
    intro g r
    rw [shift_apply, Polynomial.map_comp, Polynomial.map_map, Polynomial.map_map, hcomp g]
    simp

  have h : ¬ ∃ f : F, ∀ g, s g f - f = (algebraMap B F) (τ g) := by
    rintro ⟨f, hf⟩
    obtain ⟨d', d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) f
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    apply hτ d d' hd0
    intro g
    have e := hf g
    have h1 := hι0 d hd0
    have h2 := hι0 (σ g d) ((map_ne_zero_iff _ (σ g).injective).mpr hd0)
    rw [map_div₀, hs, hs] at e
    apply hinj
    simp only [map_sub, map_mul]
    field_simp at e
    linear_combination e
  have hQ : q.map (algebraMap B F) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hq
  obtain ⟨c, hc, hcs⟩ := eq_C_mul_of_fixed s (fun g => (algebraMap B F) (τ g)) h (p.map (algebraMap B F)) (q.map (algebraMap B F)) hQ
    (fun g => by
      have e := congrArg (Polynomial.map (algebraMap B F)) (hpq g)
      rwa [Polynomial.map_mul, Polynomial.map_mul, hmap, hmap] at e)
  obtain ⟨d', d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) c
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have h1 := hι0 d hd0
  refine ⟨d, d', hd0, ?_, fun g => ?_⟩
  · apply Polynomial.map_injective (algebraMap B F) hinj
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hc, ← mul_assoc,
      ← C_mul, mul_div_cancel₀ _ h1]
  · have e := hcs g
    have h2 := hι0 (σ g d) ((map_ne_zero_iff _ (σ g).injective).mpr hd0)
    rw [map_div₀, hs, hs] at e
    apply hinj
    simp only [map_mul]
    field_simp at e
    linear_combination e

theorem fixed_ratio_const {B G : Type} [CommRing B] [IsDomain B] [CharZero B]
    (σ : G → B ≃+* B) (τ : G → B)
    (hτ : ∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g)
    (p q : Polynomial B) (hq : q ≠ 0)
    (hpq : ∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) =
      (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) :
    ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' :=
  fixed_ratio_const_of (FractionRing B) σ τ hτ p q hq hpq

end GlobalTheory.InvRatFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomainStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedShift_fixed_ratio_const_domain : ∀ {B G : Type} [CommRing B] [IsDomain B] [CharZero B] (σ : G → B ≃+* B) (τ : G → B),
  (∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g) →
  ∀ p q : Polynomial B, q ≠ 0 →
  (∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) = (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) →
  ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  first | exact @GlobalTheory.InvRatFun.fixed_ratio_const | exact GlobalTheory.InvRatFun.fixed_ratio_const | (intros; apply GlobalTheory.InvRatFun.fixed_ratio_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem filtration_eq_span_pow : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  intro l _ Co ϖ hb n
  have he := core_isEps l Co
  obtain ⟨hfil, -, -, -⟩ := filtration_eq_xi_pow l Co.ε he
  obtain ⟨-, -, -, -, hdom, -, hk⟩ := thetaP_facts l
  haveI := hdom
  have hass : Associated (algebraMap (Per.Ainf l) (Per.AinfP l) (xi Co.ε)) (beta ϖ) :=
    Ideal.span_singleton_eq_span_singleton.1 ((hk Co.ε he).symm.trans hb)
  have hD : Associated (aDp l (xi Co.ε) ^ n) (betaD ϖ ^ n) :=
    (hass.map (algebraMap (Per.AinfP l) (Per.BdRp l))).pow_pow
  ext y
  rw [hfil, Ideal.mem_span_singleton]
  exact hD.dvd_iff_dvd_left

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  first | exact @GlobalTheory.Pst.StLat.filtration_eq_span_pow | exact GlobalTheory.Pst.StLat.filtration_eq_span_pow | (intros; apply GlobalTheory.Pst.StLat.filtration_eq_span_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivPowerEnvelopeMemAinfAdjoinBeta
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivPowerEnvelopeMemAinfAdjoinBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris0_le_sa : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  intro l _ ϖ hϖ a
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  refine GlobalTheory.RingIface.acris0_le l (Sa ϖ) ?_ a.2
  intro x hx n y hn
  have hx2 : x ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ RingHom.mem_ker.2 hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx2
  obtain ⟨c', hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
  have hc' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') =
      ((l : ℕ) : Per.AinfP l) ^ n := by
    have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
    rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
  have hX : algebraMap (Per.Ainf l) (Per.AinfP l) (c * (((l : ℕ) : Per.Ainf l) - Per.tm ϖ)) =
      -algebraMap (Per.Ainf l) (Per.AinfP l) c * (((l : ℕ) : Per.AinfP l) * beta ϖ) := by
    rw [l_mul_beta, map_mul, map_sub, map_natCast]; ring
  have key : y = algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') *
      (-algebraMap (Per.Ainf l) (Per.AinfP l) c) ^ n * beta ϖ ^ n := by
    apply (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).mul_left_cancel
    rw [hn, hX, mul_pow, mul_pow, ← hc']
    ring
  rw [key]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) _))
    (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivPowerEnvelopeMemAinfAdjoinBetaStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  first | exact @GlobalTheory.Pst.StLat.acris0_le_sa | exact GlobalTheory.Pst.StLat.acris0_le_sa | (intros; apply GlobalTheory.Pst.StLat.acris0_le_sa <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AinfAdjoinBetaImageDivBetaPow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AinfAdjoinBetaImageDivBetaPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat.BetaDiv

variable {l : ℕ} [Fact l.Prime]

theorem Sa_decomp (ϖ : Per.Fl l) (x : Per.AinfP l) (hx : x ∈ Sa ϖ) :
    ∃ a : Per.Ainf l, ∃ y ∈ Sa ϖ, x = algebraMap (Per.Ainf l) (Per.AinfP l) a + beta ϖ * y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, one_mem _, by rw [hx, map_zero, zero_add, mul_one]⟩
  | algebraMap r => exact ⟨r, 0, zero_mem _, by rw [mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    exact ⟨a + b, u + v, add_mem hu hv, by rw [map_add (f := _)]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    have hb : beta ϖ ∈ Sa ϖ := Algebra.subset_adjoin (Set.mem_singleton _)
    refine ⟨a * b, algebraMap (Per.Ainf l) (Per.AinfP l) a * v + u * algebraMap (Per.Ainf l) (Per.AinfP l) b
      + beta ϖ * u * v, ?_, by rw [map_mul]; ring⟩
    exact add_mem (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hv)
      (mul_mem hu (Subalgebra.algebraMap_mem _ _))) (mul_mem (mul_mem hb hu) hv)

theorem Sa_cancel_beta (ϖ : Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (c : Per.AinfP l) (hc : beta ϖ * c ∈ Sa ϖ) : c ∈ Sa ϖ := by
  obtain ⟨i1, i2, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  obtain ⟨hsurj, hker, hA, -, hdom, hinj, -⟩ := thetaP_facts l
  obtain ⟨hK1, hK2, -⟩ := hK ϖ hϖ
  obtain ⟨a, y, hy, hxy⟩ := Sa_decomp ϖ _ hc

  have ha : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    rw [hk, Ideal.mem_span_singleton']
    exact ⟨c - y, by linear_combination hxy⟩
  have hθ : Per.θ l a = 0 := by
    rw [← hker, RingHom.mem_ker, hA] at ha
    exact Subtype.ext (by simpa using ha)
  have hmem : a ∈ RingHom.ker (Per.θ l) := hθ
  have hK1' : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hK1
  rw [hK1', Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem

  have hne : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ≠ 0 := nonZeroDivisors.ne_zero hK2
  have hβ : beta ϖ ≠ 0 := by
    intro h0
    apply hne
    apply hinj
    have := l_mul_beta ϖ
    rw [h0, mul_zero] at this
    rw [map_sub, map_natCast, map_zero]
    linear_combination this
  have hlb := l_mul_beta ϖ
  have e : beta ϖ * c = beta ϖ * (y - ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) d) := by
    rw [hxy, ← hd, map_mul, map_sub, map_natCast]
    linear_combination (algebraMap (Per.Ainf l) (Per.AinfP l) d) * hlb
  rw [mul_left_cancel₀ hβ e]
  exact sub_mem hy (mul_mem (natCast_mem _ _) (Subalgebra.algebraMap_mem _ _))

theorem Sa_cancel_beta_pow (ϖ : Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (i : ℕ) : ∀ c : Per.AinfP l, beta ϖ ^ i * c ∈ Sa ϖ → c ∈ Sa ϖ := by
  induction i with
  | zero => intro c hc; simpa using hc
  | succ i ih =>
    intro c hc
    refine Sa_cancel_beta ϖ hϖ hk c (ih _ ?_)
    rwa [← mul_assoc, ← pow_succ]

theorem Sg_div_betaD_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  intro l _ ϖ hϖ hk hF s hs i hd
  obtain ⟨s₀, hs₀, rfl⟩ := Subring.mem_map.1 hs
  have hβ : beta ϖ ∈ Per.kerP l := by rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : s₀ ∈ Per.kerP l ^ i := by
    obtain ⟨z, hz⟩ := hd
    have hb : betaD ϖ ^ i = algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ ^ i) := by rw [map_pow, betaD]
    have h1 := congrArg (Per.ev l i) hz
    rw [hb, map_mul, GlobalTheory.MemLoc.ev_algebraMap, GlobalTheory.MemLoc.ev_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hβ i), zero_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have hcS : c ∈ Sa ϖ := Sa_cancel_beta_pow ϖ hϖ hk i c (by rw [mul_comm, hc]; exact hs₀)
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) c, Subring.mem_map.2 ⟨c, hcS, rfl⟩, ?_⟩
  rw [← hc, map_mul, map_pow, mul_comm, betaD]

end GlobalTheory.Pst.StLat.BetaDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AinfAdjoinBetaImageDivBetaPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  first | exact @GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow | exact GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow | (intros; apply GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow <;> assumption)
end
end

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem StLat.not_frac (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l)
    (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l)) (u : Per.BdRp l) (hu : IsLogP (beta ϖ) u) (x y : Per.Bcris l)
    (hx : Co.ι x ≠ 0) : Co.ι y ≠ Co.ι x * algebraMap (Per.BdRp l) (Per.BdR l) u := by
  intro h
  obtain ⟨hdom, hdvr, hmax, hmaxθ, -, hfilt, hfr⟩ := BdRDVR.core_dvr l Co
  have hker := GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ
  have hfil := GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta l Co ϖ hker
  have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
  have hβ0 : betaD ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, ← pow_one (Co.j Co.t), ← hfilt 1, hfil 1, h0, pow_one, Ideal.span_singleton_eq_bot]
  have hsep : ∀ z : Per.BdRp l, (∀ n : ℕ, betaD ϖ ^ n ∣ z) → z = 0 := by
    intro z hz
    have hne : Ideal.span {betaD ϖ} ≠ ⊤ := by
      rw [← pow_one (betaD ϖ), ← hfil 1, hfilt 1, pow_one, ← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal (Per.BdRp l)).ne_top
    have h1 : z ∈ ⨅ n : ℕ, Ideal.span {betaD ϖ} ^ n := by
      refine (Submodule.mem_iInf _).2 fun n => ?_
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.2 (hz n)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Ideal.mem_bot] at h1
  obtain ⟨r, ax, hax⟩ := bcris_eq_acris_localization_periodT_alt l Co x
  obtain ⟨r', ay, hay⟩ := bcris_eq_acris_localization_periodT_alt l Co y
  set tt := algebraMap (Per.Acris l) (Per.Bcris l) Co.t with htt
  have e1 : algebraMap (Per.Acris l) (Per.Bcris l) (ax * Co.t ^ r') = x * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hax, pow_add]; ring
  have e2 : algebraMap (Per.Acris l) (Per.Bcris l) (ay * Co.t ^ r) = y * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hay, pow_add]; ring
  have e3 : Co.j (ay * Co.t ^ r) = Co.j (ax * Co.t ^ r') * u := by
    apply hinjD
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← Co.ι_j, ← Co.ι_j, e1, e2, map_mul Co.ι, map_mul Co.ι, h]
    ring
  have hA := GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta l Co.j Co.j_cris ϖ (GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta l ϖ hϖ) hfil
  have hz := GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos l (Fact.out : l.Prime) (isUnit_l_BdRp l) (betaD ϖ) hβ0 hsep (Sg ϖ)
    (GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow l ϖ hϖ hker hfil) (GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues l ϖ hker hfil) u
    (GlobalTheory.T.log_period_congruence_bdr l ϖ hker hfil u hu) (Co.j (ax * Co.t ^ r')) 0 (hA _) (by
      rw [pow_zero, one_mul, ← e3]; exact hA _)
  have hz2 : Co.ι (x * tt ^ (r + r')) = 0 := by
    rw [← e1, Co.ι_j, hz, map_zero]
  have htne : Co.ι tt ≠ 0 := by
    rw [htt, Co.ι_j]
    intro h0
    have h3 : Co.j Co.t = 0 := hinjD (h0.trans (map_zero _).symm)
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, h3, Ideal.span_singleton_eq_bot]
  haveI : IsDomain (Per.BdR l) := IsFractionRing.isDomain (Per.BdRp l)
  rw [map_mul, map_pow] at hz2
  exact mul_ne_zero hx (pow_ne_zero _ htne) hz2

theorem StLat.kummer_not_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  ¬ ∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T K b b' hb h
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨x, y, hx, hxy⟩ := GlobalTheory.T.exists_kummerFracCoboundary_full_galois l P K b b' hb h
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  letI : Field P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).toField
  set U := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u) with hUdef
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  have hU : ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
    intro g
    apply T.eD.injective
    rw [T.actD, hUdef, RingEquiv.apply_symm_apply, map_add (f := _), RingEquiv.apply_symm_apply, hct]
    rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from
        GlobalTheory.RingIface.sigD_alg l g u, hg, map_add]
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  have hX : P.ιB x ≠ 0 := fun h0 => hx ((P.PD (botExt l)).ι_inj (by rw [P.PD_ι, h0, map_zero]))
  have hgX : ∀ g : GQ l, P.actQdR g (P.ιB x) ≠ 0 := fun g h0 =>
    hX ((P.actQdR g).injective (h0.trans (map_zero _).symm))
  have hW : ∀ g : GQ l, P.actQdR g (P.ιB y * (P.ιB x)⁻¹ - U) = P.ιB y * (P.ιB x)⁻¹ - U := by
    intro g
    have h1 := congrArg P.ιB (hxy g)
    simp only [map_sub, map_mul, hcomm] at h1
    rw [map_sub, map_mul, map_inv₀, hU]
    have hx1 := mul_inv_cancel₀ hX
    have hx2 := mul_inv_cancel₀ (hgX g)
    linear_combination ((P.ιB x)⁻¹ * (P.actQdR g (P.ιB x))⁻¹) * h1
      - (P.actQdR g (P.ιB y) * (P.actQdR g (P.ιB x))⁻¹) * hx1 + (P.ιB y * (P.ιB x)⁻¹) * hx2
      + (P.ιB ((kummer P g : ℚ_[l]) • P.tB) * P.actQdR g (P.ιB x) * (P.actQdR g (P.ιB x))⁻¹) * hx1
      + P.ιB ((kummer P g : ℚ_[l]) • P.tB) * hx2
  obtain ⟨c, hc⟩ := (P.PD (botExt l)).invdR (P.ιB y * (P.ιB x)⁻¹ - U) fun g => by
    rw [P.PD_actdR]; exact hW g
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 c.2
  have hca : algebraMap ↥(botExt l).1 P.R.BdR c = algebraMap ℚ_[l] P.R.BdR a := by
    have e : c = algebraMap ℚ_[l] ↥(botExt l).1 a := Subtype.ext ha.symm
    rw [e, ← IsScalarTower.algebraMap_apply]
  rw [hca] at hc
  have hY : P.ιB (y - a • x) = P.ιB x * U := by
    rw [map_sub, map_smul, Algebra.smul_def]
    have hx1 := mul_inv_cancel₀ hX
    linear_combination (-P.ιB x) * hc - P.ιB y * hx1
  apply StLat.not_frac l Co ϖ hϖ u hu (T.eB x) (T.eB (y - a • x))
  · rw [← hC.ι]
    exact fun h0 => hX (T.eD.injective (h0.trans (map_zero _).symm))
  · rw [← hC.ι, ← hC.ι, hY, map_mul, hUdef, RingEquiv.apply_symm_apply]

theorem stRegular : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    IsDomain (Bst P) ∧
    (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') →
      ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) ∧
    (∀ (K : FinExt l) (b : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b) := by
  intro l _ P AI ⟨T⟩
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinj : Co.TensorInj := GlobalTheory.Published.FontaineBcris_holds.tensorInj Co
  have hreg : Co.Regular := GlobalTheory.Published.FontaineBcris_holds.regular Co
  refine ⟨inferInstance, fun K b b' hb h => ?_, fun K b hb h => ?_⟩
  · haveI : CharZero P.R.B := by
      have := (algebraMap ℚ_[l] P.R.B).injective
      exact charZero_of_injective_algebraMap this
    have hA : ∀ (g : GQ l) (p : Bst P), actSt P g p = (p.map ((P.actQ g).toRingEquiv : P.R.B →+* P.R.B)).comp (X + C ((kummer P g : ℚ_[l]) • P.tB)) :=
      fun g p => stHom_apply P (P.actQ g) _ p
    obtain ⟨d, d', hd, e, hf⟩ := GlobalTheory.T.twistedShift_fixed_ratio_const_domain (fun g : ↥(GK K) => (P.actQ (g : GQ l)).toRingEquiv)
      (fun g => (kummer P (g : GQ l) : ℚ_[l]) • P.tB)
      (fun d d' hd hh => StLat.kummer_not_frac l P AI T K d d' hd fun g hg => hh ⟨g, hg⟩) b' b hb (fun g => by
        rw [← hA, ← hA]; exact h g)
    obtain ⟨c, hc⟩ := GlobalTheory.RegularRing.fracInv hC hinj K d d' hd fun g => by
      rw [P.PD_actB, P.PD_actB]; exact hf g
    refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
    have hd' : (C d : Bst P) ≠ 0 := C_ne_zero.2 hd
    apply mul_left_cancel₀ hd'
    have hK0 : algebraMap ↥(K0 K) P.R.B c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ := rfl
    rw [e, hc, Polynomial.algebraMap_apply, C_mul, hK0]
    ring
  · have hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB :=
      GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K
    exact GlobalTheory.T.isUnit_of_stable_line' l P K hK (GlobalTheory.RegularRing.lineUnit hC hreg K) b hb h

end GlobalTheory.Pst
