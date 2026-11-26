module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotient
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharValueLength

section
variable {l : ℕ} [Fact l.Prime]

private theorem isUnit_of_toZMod_ne_zero' {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hx

private theorem principalUnit_pow_prime_eq_one_add_pow_succ {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (h2 : l = 2 → 2 ≤ r) (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ l = 1 + (l : ℤ_[l]) ^ (r + 1) * w' := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  set x := (l : ℤ_[l]) ^ r * w with hx
  have hexp : u ^ l = (∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l])) + x * l + 1 := by
    rw [hu, add_comm, add_pow, show l + 1 = n + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, zero_add]
  have hdvd : (l : ℤ_[l]) ^ (r + 2) ∣ ∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j + 2 ≤ l := by rw [Finset.mem_range] at hj; omega
    have hxp : x ^ (j + 1 + 1) = (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * w ^ (j + 1 + 1) := by
      rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge (j + 2) l with hlt | hge
    · have hc : (l : ℤ_[l]) ∣ ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) :=
        Nat.cast_dvd_cast ((Fact.out : l.Prime).dvd_choose_self (by omega) (by omega))
      have h1 : (l : ℤ_[l]) ^ (r + 2) ∣ (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * l := by
        rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
      exact h1.trans (mul_dvd_mul (Dvd.intro _ hxp.symm) hc)
    · have hle : r + 2 ≤ r * (j + 1 + 1) := by
        rcases Nat.lt_or_ge l 3 with h | h
        · have := h2 (by omega); nlinarith
        · nlinarith
      exact ((pow_dvd_pow _ hle).trans (Dvd.intro _ hxp.symm)).mul_right _
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨w + l * c, isUnit_of_toZMod_ne_zero' ?_, ?_⟩
  · simpa [ZMod.natCast_self] using (hw.map PadicInt.toZMod).ne_zero
  · rw [hexp, hc, hx]; ring

private theorem toZMod_principalUnit_eq_one {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (hu : u = 1 + (l : ℤ_[l]) ^ r * w) : PadicInt.toZMod u = 1 := by
  rw [hu]
  simp [ZMod.natCast_self, zero_pow (Nat.one_le_iff_ne_zero.1 hr)]

private theorem principalUnit_pow_of_not_dvd {u w : ℤ_[l]} {r m : ℕ} (hr : 1 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) (hm : ¬ l ∣ m) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ m = 1 + (l : ℤ_[l]) ^ r * w' := by
  refine ⟨w * ∑ i ∈ Finset.range m, u ^ i, hw.mul (isUnit_of_toZMod_ne_zero' ?_), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
  · rw [map_sum]
    simp only [map_pow, toZMod_principalUnit_eq_one hr hu, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact fun h => hm ((ZMod.natCast_eq_zero_iff m l).1 h)
  · have hg := geom_sum_mul u m
    have hu1 : u - 1 = (l : ℤ_[l]) ^ r * w := by rw [hu]; ring
    rw [hu1] at hg
    linear_combination -hg

private theorem principalUnit_pow_eq_one_add_pow_add_padicValNat {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r) (h2 : l = 2 → 2 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) {k : ℕ} (hk : k ≠ 0) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ k = 1 + (l : ℤ_[l]) ^ (r + padicValNat l k) * w' := by
  have hpow : ∀ a : ℕ, ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ (l ^ a) = 1 + (l : ℤ_[l]) ^ (r + a) * w' := by
    intro a
    induction a with
    | zero => exact ⟨w, hw, by simpa using hu⟩
    | succ a ih =>
      obtain ⟨w', hw', h'⟩ := ih
      obtain ⟨w'', hw'', h''⟩ :=
        principalUnit_pow_prime_eq_one_add_pow_succ (by omega) (fun h => by have := h2 h; omega) hw' h'
      exact ⟨w'', hw'', by rw [pow_succ, pow_mul, h'', ← add_assoc]⟩
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk l (Fact.out : l.Prime).one_lt.ne'
  obtain ⟨w', hw', h'⟩ := hpow a
  obtain ⟨w'', hw'', h''⟩ := principalUnit_pow_of_not_dvd (by omega) hw' h' hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  refine ⟨w'', hw'', ?_⟩
  rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hm0,
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero, pow_mul, h'']
end

private theorem length_quotient_span_unit_mul_pow_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (w : Oˣ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {(w : O) * ϖ ^ n}) = n := by
  rw [Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n

theorem _root_.GlobalTheory.CharValueLength.injOn_and_lenUnit : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ _root_.Formalism.BasicNotions.lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  intro l _ O _ _ _ _ _ _ s t u v χ hs hs2 huv hχ
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hD : ∀ k : ℕ, k ≠ 0 → ∃ ε : Oˣ,
      algebraMap ℤ_[l] O u ^ k - 1 = ε * (l : O) ^ (s + padicValNat l k) := by
    intro k hk
    obtain ⟨w', hw', h'⟩ := principalUnit_pow_eq_one_add_pow_add_padicValNat hs hs2 v.isUnit huv hk
    refine ⟨(hw'.map (algebraMap ℤ_[l] O)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, h', map_add (f := _), map_one, map_mul, map_pow, map_natCast]
    ring
  have hrel : ∀ c, 1 ≤ c → c ≤ t → (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) = χ 1 := by
    intro c h1 h2
    have h : χ c * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (c - 1) = χ 1 := by
      rw [hχ c h1 h2, mul_assoc, ← zpow_natCast, ← zpow_add, Nat.cast_sub h1, Nat.cast_one,
        neg_add_cancel, zpow_zero, mul_one]
    have h' := congrArg (fun z : Oˣ => (z : O)) h
    simpa using h'
  have hφu : IsUnit (algebraMap ℤ_[l] O u) := u.isUnit.map _
  constructor
  · intro c hc c' hc' heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hc hc'
    simp only at heq
    have key : ∀ a b : ℕ, 1 ≤ a ∧ a ≤ t → 1 ≤ b ∧ b ≤ t → (χ a : O) = χ b → a ≤ b → a = b := by
      intro c c' hc hc' heq hle
      by_contra hne
      obtain ⟨ε, hε⟩ := hD (c' - c) (by omega)
      have e1 := hrel c hc.1 hc.2
      have e2 := hrel c' hc'.1 hc'.2
      rw [← heq, show c' - 1 = (c - 1) + (c' - c) by omega, pow_add] at e2
      have h0 : (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) *
          (algebraMap ℤ_[l] O u ^ (c' - c) - 1) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.1 h0 with h | h
      · exact ((χ c).isUnit.mul (hφu.pow _)).ne_zero h
      · rw [hε] at h
        exact mul_ne_zero ε.ne_zero (pow_ne_zero _ hl0) h
    rcases le_total c c' with hle | hle
    · exact key c c' hc hc' heq hle
    · exact (key c' c hc' hc heq.symm hle).symm
  · have hterm : ∀ c ∈ Finset.Ioc 1 t, ∃ ε : Oˣ,
        (χ 1 : O) - χ c = ε * (l : O) ^ (s + padicValNat l (c - 1)) := by
      intro c hc
      rw [Finset.mem_Ioc] at hc
      obtain ⟨ε, hε⟩ := hD (c - 1) (by omega)
      refine ⟨χ c * ε, ?_⟩
      rw [← hrel c (by omega) hc.2, Units.val_mul, mul_assoc, ← hε]
      ring
    choose! ε hε using hterm
    have hprod : ∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - χ c) =
        ((∏ c ∈ Finset.Ioc 1 t, ε c : Oˣ) : O) *
          (l : O) ^ (∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1))) := by
      rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Units.coe_prod]
    have hsum : ∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1)) =
        ∑ k ∈ Finset.Ioo 0 t, (s + padicValNat l k) := by
      refine Finset.sum_nbij' (fun c => c - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
        simp only [Finset.mem_Ioc, Finset.mem_Ioo] at ha ⊢ <;> omega
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    have he : e ≠ 0 := by
      rintro rfl
      have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal O)
      have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
        rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.subset_span rfl
      rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
      exact hl (by rw [hη, pow_zero, mul_one]; exact η.isUnit)
    unfold _root_.Formalism.BasicNotions.lenUnit
    rw [hprod, hsum, hη, mul_pow, ← pow_mul, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, length_quotient_span_unit_mul_pow_eq hϖ, length_quotient_span_unit_mul_pow_eq hϖ,
      ENat.toNat_natCast, ENat.toNat_natCast, Nat.cast_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 he)]
    push_cast
    rfl

end GlobalTheory.CharValueLength
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotientStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injOn_charValues_and_length_quotient : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  first | exact @GlobalTheory.CharValueLength.injOn_and_lenUnit | exact GlobalTheory.CharValueLength.injOn_and_lenUnit | (intros; apply GlobalTheory.CharValueLength.injOn_and_lenUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.RootFactor

theorem aeval_sq {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) : aeval D q * aeval D q = q.eval r • aeval D q := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  obtain ⟨s, hs⟩ : ∃ s : K[X], q = s * (X - C r) + C (q.eval r) :=
    ⟨q /ₘ (X - C r), by
      have hmd := Polynomial.modByMonic_add_div q (X - C r)
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hmd
      rw [mul_comm, add_comm]
      exact hmd.symm⟩
  conv_lhs => arg 1; rw [hs]
  rw [map_add (f := _), map_mul, aeval_C, add_mul, Matrix.mul_assoc, hCH, Matrix.mul_zero, zero_add,
    Algebra.smul_def]

theorem aeval_rank {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) (hq : q.eval r ≠ 0) : (aeval D q).rank = 1 := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  have hDP : D * aeval D q = r • aeval D q := by
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mul,
      sub_eq_zero, Matrix.smul_mul, Matrix.one_mul] at hCH
    exact hCH
  have hchar : LinearMap.charpoly (Matrix.toLinAlgEquiv' D) = (X - C r) * q := by
    rw [← h]; exact Matrix.charpoly_toLin' D
  have hmult : (LinearMap.charpoly (Matrix.toLinAlgEquiv' D)).rootMultiplicity r = 1 := by
    rw [hchar, Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_X_sub_C_self,
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hq)]
    rw [← h]; exact (Matrix.charpoly_monic D).ne_zero
  have hle : LinearMap.range (aeval D q).mulVecLin ≤
      Module.End.eigenspace (Matrix.toLinAlgEquiv' D) r := by
    rintro _ ⟨v, rfl⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLinAlgEquiv'_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hDP, Matrix.smul_mulVec]
  have hEig : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' D) r := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar]
    simp [Polynomial.IsRoot]
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hPv : Matrix.mulVec (aeval D q) v = q.eval r • v := by
    rw [← Matrix.toLinAlgEquiv'_apply, ← Polynomial.aeval_algHom_apply]
    exact Module.End.aeval_apply_of_hasEigenvector hv
  show Module.finrank K (LinearMap.range (aeval D q).mulVecLin) = 1
  apply le_antisymm
  · exact (Submodule.finrank_mono hle).trans (hmult ▸ LinearMap.finrank_eigenspace_le _ r)
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have hmem : Matrix.mulVec (aeval D q) v ∈ LinearMap.range (aeval D q).mulVecLin := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot, hPv] at hmem
    exact smul_ne_zero hq hv.2 hmem

private theorem aeval_list_prod_X_sub_C_mul_comm {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K)
    (l : List ℕ) :
    b * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have key : b * (a * D * b - ρ c • (a * b)) = (D - ρ c • 1) * b := by
      simp only [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hba, Matrix.one_mul,
        Matrix.sub_mul, Matrix.smul_mul]
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul, ← Matrix.mul_assoc,
      key, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    congr 2
    simp [Algebra.algebraMap_eq_smul_one]

theorem prod_eq {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K)
    (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K) (l : List ℕ) :
    (a * b) * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      a * aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  rw [Matrix.mul_assoc, aeval_list_prod_X_sub_C_mul_comm a b hba D ρ l, ← Matrix.mul_assoc]

private theorem prod_Ioc_one_eq_list_range'_prod {M : Type} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Ioc 1 t, f c = ((List.range' 2 (t - 1)).map f).prod := by
  rw [Finset.prod_eq_multiset_prod]
  rfl

theorem field_case {K : Type} [Field K] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) K) (ρ : ℕ → K) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  obtain ⟨a, b, hba, hab, hM⟩ := GlobalTheory.BlockCharpoly.blockPol_eq_charpoly e he rfl
  have hX : e * X₀ * e = X₀ := by rw [h1, h2]
  have hX' : a * (b * X₀ * a) * b = X₀ := by
    conv_rhs => rw [← hX, ← hab]
    simp only [Matrix.mul_assoc]
  have hcp : (b * X₀ * a).charpoly =
      (X - C (ρ 1)) * ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod := by
    rw [← hM, hX, ← hP, Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ t), Finset.prod_cons,
      prod_Ioc_one_eq_list_range'_prod]
  have hev : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) =
      ∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c) := by
    rw [prod_Ioc_one_eq_list_range'_prod, Polynomial.eval_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp
  have hne : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) ≠ 0 := by
    rw [hev, Finset.prod_ne_zero_iff]
    intro c hc hzero
    rw [Finset.mem_Ioc] at hc
    have := hρ (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega)
      (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega) (sub_eq_zero.mp hzero)
    omega
  have heE : e * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
    obtain ⟨k, hk⟩ : ∃ k, t - 1 = k + 1 := ⟨t - 2, by omega⟩
    rw [hk, List.range'_succ, List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Matrix.mul_sub,
      Matrix.mul_smul, h1, he]
  have hE : ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      a * aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod * b := by
    rw [← heE, ← prod_eq a b hba (b * X₀ * a) ρ, hab]
    congr 2
    apply List.map_congr_left
    intro c _
    rw [hX']
  have hsq := aeval_sq (b * X₀ * a) (ρ 1) _ hcp
  have hrk := aeval_rank (b * X₀ * a) (ρ 1) _ hcp hne
  rw [hE, ← hev]
  generalize aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod = R at hsq hrk
  constructor
  · apply le_antisymm
    · exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hrk.le
    · have hR : R = b * (a * R * b) * a := by
        simp only [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rw [Matrix.mul_assoc, hba, Matrix.mul_one]
      calc 1 = R.rank := hrk.symm
        _ = (b * (a * R * b) * a).rank := by rw [← hR]
        _ ≤ (b * (a * R * b)).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (a * R * b).rank := Matrix.rank_mul_le_right _ _
  · calc a * R * b * (a * R * b) = a * (R * R) * b := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
      _ = _ := by rw [hsq, Matrix.mul_smul, Matrix.smul_mul]

theorem blockPol_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

private theorem map_list_prod' {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (l : List ℕ) :
    ((l.map fun c => X₀ - ρ c • e).prod).map f = (l.map fun c => X₀.map f - f (ρ c) • e.map f).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    ext i j
    simp

private theorem map_smul_eq_smul_map {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (s : O) (M : Matrix (Fin n) (Fin n) O) : (s • M).map f = f s • M.map f := by
  ext i j
  simp

theorem rank_one_and_sq {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O)
    (ρ : ℕ → O) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  obtain ⟨hr, hsq⟩ := field_case (K := FractionRing O) n t (e.map (toFr O)) (X₀.map (toFr O))
    (fun c => toFr O (ρ c)) ht (by rw [← Matrix.map_mul, he]) (by rw [← Matrix.map_mul, h1])
    (by rw [← Matrix.map_mul, h2]) (fun x hx y hy hxy => hρ hx hy (hinj hxy))
    (by rw [← blockPol_map, ← hP, Polynomial.map_prod]; simp)
  refine ⟨by rw [map_list_prod']; exact hr, ?_⟩
  have hmap : (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) =
      ((∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) •
        ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) := by
    rw [Matrix.map_mul, map_smul_eq_smul_map, map_list_prod', hsq, map_prod]
    simp [map_sub]
  ext i j
  exact hinj (congrFun (congrFun hmap i) j)

end GlobalTheory.RootFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomainStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain : ∀ {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → e * e = e → e * X₀ = X₀ → X₀ * e = X₀ → Set.InjOn ρ (Finset.Icc 1 t : Set ℕ) → ∏ c ∈ Finset.Icc 1 t, (Polynomial.X - Polynomial.C (ρ c)) = blockPol e X₀ → ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧ ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  first | exact @GlobalTheory.RootFactor.rank_one_and_sq | exact GlobalTheory.RootFactor.rank_one_and_sq | (intros; apply GlobalTheory.RootFactor.rank_one_and_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtale
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LimBasis

variable {l : ℕ} [hl : Fact l.Prime]

theorem sep (z : WCb l) (h : ∀ n, (l : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

def Cg {ι κ : Type} (n : ℕ) (M : Matrix ι κ (WCb l)) : Prop := ∃ Y : Matrix ι κ (WCb l), M = ((l : WCb l) ^ n) • Y

section Cg

variable {ι κ μ : Type} {n : ℕ}

theorem cg_of {M : Matrix ι κ (WCb l)} (h : ∀ i j, (l : WCb l) ^ n ∣ M i j) : Cg n M :=
  ⟨Matrix.of fun i j => Classical.choose (h i j), by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Classical.choose_spec (h i j)⟩

theorem Cg.dvd {M : Matrix ι κ (WCb l)} (h : Cg n M) (i : ι) (j : κ) : (l : WCb l) ^ n ∣ M i j := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y i j, by simp⟩

theorem Cg.add {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M + M') := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y + Y', (smul_add _ _ _).symm⟩

theorem Cg.neg {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (-M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨-Y, (smul_neg _ _).symm⟩

theorem Cg.sub {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M - M') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem Cg.mul_left [Fintype κ] {M : Matrix κ μ (WCb l)} (P : Matrix ι κ (WCb l)) (h : Cg n M) : Cg n (P * M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨P * Y, Matrix.mul_smul _ _ _⟩

theorem Cg.mul_right [Fintype κ] {M : Matrix ι κ (WCb l)} (P : Matrix κ μ (WCb l)) (h : Cg n M) : Cg n (M * P) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y * P, Matrix.smul_mul _ _ _⟩

theorem Cg.map (f : WCb l →+* WCb l) {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (M.map f) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y.map f, Matrix.ext fun i j => by simp⟩

theorem Cg.eq_zero {M : Matrix ι κ (WCb l)} (h : ∀ n, Cg n M) : M = 0 := by
  refine Matrix.ext fun i j => ?_
  exact sep _ fun n => (h n).dvd i j

end Cg

variable {K : FinExt l} (bk : BK K)

def InOE {ι κ : Type} (M : Matrix ι κ (WCb l)) : Prop := ∀ i j, M i j ∈ bk.OE

variable {bk}

theorem InOE.mul {ι κ μ : Type} [Fintype κ] {M : Matrix ι κ (WCb l)} {M' : Matrix κ μ (WCb l)} (h : InOE bk M)
    (h' : InOE bk M') : InOE bk (M * M') := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h i k) (h' k j)

theorem InOE.smul {ι κ : Type} {c : WCb l} (hc : c ∈ bk.OE) {M : Matrix ι κ (WCb l)} (h : InOE bk M) :
    InOE bk (c • M) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (h i j)

variable (bk)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem inOE_evW {ι κ : Type} (M : Matrix ι κ bk.S) : InOE bk (M.map bk.evW) := fun i j => evW_mem bk (M i j)

theorem mem_of_approx {x : WCb l} (h : ∀ n, ∃ w ∈ bk.OE, (l : WCb l) ^ n ∣ x - w) : x ∈ bk.OE := by
  intro n
  obtain ⟨w, hw, c, hc⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hw n
  exact ⟨m, s, y + bk.evW X ^ m * c, by linear_combination bk.evW X ^ m * hc + hy⟩

theorem inOE_of_approx {ι κ : Type} {A : Matrix ι κ (WCb l)}
    (h : ∀ n, ∃ M : Matrix ι κ (WCb l), InOE bk M ∧ Cg n (A - M)) : InOE bk A := fun i j =>
  mem_of_approx bk fun n => by
    obtain ⟨M, hM, hc⟩ := h n
    exact ⟨M i j, hM i j, by simpa [Matrix.sub_apply] using hc.dvd i j⟩

theorem E_not_dvd : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨s, hs⟩
  have h : PowerSeries.coeff bk.Ep.natDegree (bk.Ep : (Wq l bk.a)⟦X⟧) =
      PowerSeries.coeff bk.Ep.natDegree ((l : bk.S) * s) :=
    congrArg (PowerSeries.coeff bk.Ep.natDegree) hs
  rw [Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 : (1 : Wq l bk.a) = (PowerSeries.coeff bk.Ep.natDegree s) * (l : Wq l bk.a) := by
    rw [h, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  have h3 := congrArg (fun w : Wq l bk.a => w.coeff 0) h2
  simp only [WittVector.one_coeff_zero, WittVector.mul_charP_coeff_zero] at h3
  exact one_ne_zero h3

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  intro l _ K bk τ _ d N ρ tw F T0 hT0 hR
  obtain ⟨-, -, hunit, -, -, hfix, hfrob⟩ := GlobalTheory.OEDvr.main l K bk
  obtain ⟨e, he, heE⟩ := hunit bk.E (E_not_dvd bk)
  have key : ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)),
      InOE bk R ∧ InOE bk R' ∧ Cg n (zW (tw.Pi n) * (F n).T - T0 * R) ∧
      Cg n (T0 - zW (tw.Pi n) * (F n).T * R') := fun n => by
    obtain ⟨R, R', h1, h2, h3, h4⟩ := hR n
    refine ⟨R, R', h1, h2, cg_of h3, ?_⟩
    have e1 : T0 - zW (tw.Pi n) * (F n).T * R' =
        -(T0 * (R * R' - 1)) - (zW (tw.Pi n) * (F n).T - T0 * R) * R' := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    rw [e1]
    exact ((cg_of h4).mul_left T0).neg.sub ((cg_of h3).mul_right R')
  have hdet : IsUnit T0.det := (Matrix.isUnit_iff_isUnit_det T0).1 hT0
  refine ⟨fun g hg => ?_, ?_⟩
  · let σ : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hσz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map σ = zW M := fun M =>
      Matrix.ext fun i j => (galW l (g : GQ l)).commutes (M i j)
    change zW (ρ g).val * T0.map σ = T0
    refine sub_eq_zero.1 (Cg.eq_zero fun n => ?_)
    obtain ⟨R, R', -, hR', -, h2⟩ := key n
    have hR'σ : R'.map σ = R' := Matrix.ext fun i j => hfix g hg _ (hR' i j)
    have hT' : zW (tw.ρ' n g).val * (F n).T.map σ = (F n).T := (F n).fix g hg
    have hequi : Cg n (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) := by
      have e2 : zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val =
          -zW (tw.Pi n * (tw.ρ' n g).val - (ρ g).val * tw.Pi n) := by
        simp only [zW, Matrix.map_sub _ (map_sub (algebraMap ℤ_[l] (WCb l))), Matrix.map_mul, neg_sub]
      rw [e2]
      refine (cg_of fun i j => ?_).neg
      have := map_dvd (algebraMap ℤ_[l] (WCb l)) ((tw.onto n).equi g i j)
      rwa [map_pow, map_natCast] at this
    have h3 : Cg n (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') := by
      have := h2.map σ
      rwa [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz, hR'σ] at this
    have e3 : zW (ρ g).val * T0.map σ - T0 = zW (ρ g).val * (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') +
        (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) * (F n).T.map σ * R' -
        (T0 - zW (tw.Pi n) * (zW (tw.ρ' n g).val * (F n).T.map σ) * R') := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    rw [e3, hT']
    exact ((h3.mul_left _).add ((hequi.mul_right _).mul_right _)).sub h2
  · let f : WCb l →+* WCb l := (frobW l).toRingHom
    change ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧
      T0.map f = T0 * A0 ∧ A0 * A0' = 1
    have hfz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map f = zW M := fun M =>
      Matrix.ext fun i j => (frobW l).commutes (M i j)
    have hfOE : ∀ {m m' : Type} {M : Matrix m m' (WCb l)}, InOE bk M → InOE bk (M.map f) :=
      fun h i j => hfrob _ (h i j)
    have hTf : IsUnit (T0.map f) := hT0.map f.mapMatrix
    have hdetf : IsUnit (T0.map f).det := (Matrix.isUnit_iff_isUnit_det _).1 hTf
    have heN : bk.evW bk.E ^ N * e ^ N = 1 := by rw [← mul_pow, heE, one_pow]
    have hφ : ∀ n, (F n).T.map f = (F n).T * (e ^ N • (F n).A.map bk.evW) := fun n => by
      have h := (F n).φ
      rw [Matrix.mul_smul, ← h, smul_smul, mul_comm (e ^ N), heN, one_smul]
      rfl
    have hφ' : ∀ n, (F n).T = (F n).T.map f * (e ^ N • (F n).A'.map bk.evW) := fun n => by
      have hA : (F n).A.map bk.evW * (F n).A'.map bk.evW =
          (bk.evW bk.E ^ (2 * N)) • (1 : Matrix (Fin (tw.d' n)) (Fin (tw.d' n)) (WCb l)) := by
        rw [← Matrix.map_mul, (F n).A_mul]
        refine Matrix.ext fun i j => ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have hs : e ^ N * (e ^ N * bk.evW bk.E ^ (2 * N)) = 1 := by
        linear_combination (bk.evW bk.E ^ N * e ^ N + 1) * heN
      rw [hφ n, Matrix.mul_assoc]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, Matrix.mul_one]
      rw [hs, one_smul]
    refine ⟨T0⁻¹ * T0.map f, (T0.map f)⁻¹ * T0, ?_, ?_, ?_, ?_⟩
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R * (e ^ N • (F n).A.map bk.evW) * R'.map f,
        (hR.mul ((inOE_evW bk _).smul (pow_mem he N))).mul (hfOE hR'), ?_⟩
      have i4 : T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f) =
          (T0 - zW (tw.Pi n) * (F n).T * R').map f +
            (zW (tw.Pi n) * (F n).T - T0 * R) * (e ^ N • (F n).A.map bk.evW) * R'.map f := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz, hφ n]
        simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
      have e4 : T0⁻¹ * T0.map f - R * (e ^ N • (F n).A.map bk.evW) * R'.map f =
          T0⁻¹ * (T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f)) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
      rw [e4, i4]
      exact ((h2.map f).add ((h1.mul_right _).mul_right _)).mul_left _
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R.map f * (e ^ N • (F n).A'.map bk.evW) * R',
        ((hfOE hR).mul ((inOE_evW bk _).smul (pow_mem he N))).mul hR', ?_⟩
      have e6 : zW (tw.Pi n) * ((F n).T.map f * ((e ^ N • (F n).A'.map bk.evW) * R')) =
          zW (tw.Pi n) * ((F n).T * R') := by
        rw [← Matrix.mul_assoc ((F n).T.map f), ← hφ' n]
      have i5 : T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R') =
          (T0 - zW (tw.Pi n) * (F n).T * R') +
            (zW (tw.Pi n) * (F n).T - T0 * R).map f * (e ^ N • (F n).A'.map bk.evW) * R' := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz]
        simp only [Matrix.sub_mul, Matrix.mul_assoc, e6]; abel
      have e5 : (T0.map f)⁻¹ * T0 - R.map f * (e ^ N • (F n).A'.map bk.evW) * R' =
          (T0.map f)⁻¹ * (T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R')) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdetf]
      rw [e5, i5]
      exact (h2.add (((h1.map f).mul_right _).mul_right _)).mul_left _
    · exact (Matrix.mul_nonsing_inv_cancel_left T0 _ hdet).symm
    · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdetf, Matrix.nonsing_inv_mul _ hdet]

end GlobalTheory.LimBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_breuilKisin_basis_invariant_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  first | exact @GlobalTheory.LimBasis.main | exact GlobalTheory.LimBasis.main | (intros; apply GlobalTheory.LimBasis.main; all_goals assumption)
end
end
