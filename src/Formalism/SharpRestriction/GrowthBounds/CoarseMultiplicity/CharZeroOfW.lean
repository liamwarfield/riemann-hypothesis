module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ExpFactIoExp
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FactAbs
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem fact_abs {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (c : ℕ) :
    ∃ (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → ℚ),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ (∀ v ∈ ν.support, odd v) ∧ PadicGe p (q ν) 0) ∧
      ∀ μ : σ →₀ ℕ, ∃ h : ℚ, PadicGe p h c ∧
        (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) *
            (∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) =
          (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) * (1 + h) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, hop⟩ := h2 σ t' ρ' hlt
  obtain ⟨T, q, hT, hq⟩ := hop true c
  let E : (σ → ℕ) → (σ →₀ ℕ) := fun j => Finsupp.equivFunOnFinite.symm j
  have hE : Function.Injective E := Finsupp.equivFunOnFinite.symm.injective
  have hEa : ∀ j v, E j v = j v := fun j v => rfl
  refine ⟨(T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E, fun ν => q ν, ?_, ?_⟩
  · intro ν hν
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hν
    obtain ⟨hjT, hj0⟩ := Finset.mem_filter.1 hj
    refine ⟨?_, ?_, ?_⟩
    · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (hT j hjT).1
    · intro v hv
      by_contra hno
      exact (Finsupp.mem_support_iff.1 hv) (hj0 v hno)
    · exact (hT j hjT).2
  · intro μ
    set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
    set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
    set A : ℚ := ∏ k, (((ρ' k + p ^ (t' k + 1) * e' k).factorial : ℕ) : ℚ) with hA
    set B : ℚ := ∏ k, ((ρ' k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (t' k + 1)).factorial : ℚ) ^ (e' k) with hB
    set g : ℚ := ∑ j ∈ T, q j * ∏ k, ((e' k).choose (j k) : ℚ) with hg
    have hU0 : U ≠ 0 := (hunit e').1
    have hUv : padicValRat p U = 0 := (hunit e').2
    have hAB : A = B * U := by
      rw [hA, hB, hU, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [h1 (t' k) (ρ' k) (e' k) (hlt k)]
      ring
    have hB0 : B ≠ 0 := by
      rw [hB]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      have a1 : ((ρ' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a2 : ((e' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a3 : ((p ^ (t' k + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      exact mul_ne_zero (mul_ne_zero a1 a2) (pow_ne_zero _ a3)
    have hq' : PadicGe p (U⁻¹ - g) c := by
      have := hq e'
      simp only [if_true] at this
      have e : A / B = U := by rw [hAB]; field_simp
      rw [← hA, ← hB, e] at this
      exact this
    have hgs : (∑ ν ∈ (T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E,
        q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) = g := by
      rw [Finset.sum_image fun a _ b _ h => hE h, hg, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ∀ v, ¬ odd v → j v = 0
      · rw [if_pos hj, Finsupp.prod_fintype _ _ (fun _ => Nat.choose_zero_right _)]
        push_cast
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hk : odd k
        · simp only [he', if_pos hk, hEa]
        · simp only [he', if_neg hk, hEa, hj k hk, Nat.choose_zero_right]
      · rw [if_neg hj]
        push_neg at hj
        obtain ⟨v, hv, hjv⟩ := hj
        have : (∏ k, ((e' k).choose (j k) : ℚ)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
          simp only [he', if_neg hv]
          rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hjv)]
          simp
        rw [this, mul_zero]
    refine ⟨(-U) * (U⁻¹ - g), ?_, ?_⟩
    · have hU' : PadicGe p (-U) 0 := padicGe_neg (Or.inr (by rw [hUv]; simp))
      have := padicGe_mul hU' hq'
      simpa using this
    · rw [hgs]
      set M : ℚ := ∏ v, (if odd v then (1 : ℚ) else ((μ v).factorial : ℚ)) with hM
      have l1 : (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) = A * M := by
        rw [hA, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      have l2 : (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) = B * M := by
        rw [hB, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      rw [l1, l2, hAB]
      field_simp
      ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees MvPolynomial

theorem rat_int {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [CharZero K] [Algebra O K] {p : ℕ} (hp : p.Prime)
    (hpO : ¬ IsUnit (p : O)) (x : ℚ) (c : ℕ) (hx : PadicGe p x c) :
    ∃ y : O, (x : K) = (p : K) ^ c * algebraMap O K y := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  rcases hx with hx | hv
  · exact absurd hx hx0
  haveI : Fact p.Prime := ⟨hp⟩
  have hv' : (c : ℤ) ≤ padicValRat p x := by exact_mod_cast hv
  simp only [padicValRat] at hv'
  have hden : ¬ p ∣ x.den := by
    intro hd
    have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      have h1 : p ∣ x.num.natAbs := Int.ofNat_dvd_left.mp hn
      have h2 := Nat.dvd_gcd h1 hd
      rw [x.reduced.gcd_eq_one] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have h0 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h1 : 1 ≤ multiplicity p x.den := one_le_padicValNat_of_dvd x.den_nz hd
    rw [h0] at hv'
    omega
  have hpv0 : multiplicity p x.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  rw [hpv0] at hv'
  have hdvd : (p : ℤ) ^ c ∣ x.num := by
    have := (padicValInt_dvd_iff (p := p) c x.num).mpr (Or.inr (by omega))
    exact_mod_cast this
  obtain ⟨n, hn⟩ := hdvd
  have hcop : Nat.Coprime p x.den := (Nat.Prime.coprime_iff_not_dvd hp).mpr hden
  have hb := Nat.gcd_eq_gcd_ab p x.den
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (p : O) * (Nat.gcdA p x.den : O) + (x.den : O) * (Nat.gcdB p x.den : O) = 1 := by
    have := congrArg (Int.cast : ℤ → O) hb
    push_cast at this
    exact this.symm
  have hdu : IsUnit (x.den : O) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hb' with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) hpO
    · exact isUnit_of_mul_isUnit_left h
  have hinv : algebraMap O K (↑hdu.unit⁻¹ : O) * (x.den : K) = 1 := by
    rw [← map_natCast (algebraMap O K), ← map_mul, IsUnit.val_inv_mul, map_one]
  have hainv : algebraMap O K (↑hdu.unit⁻¹ : O) = (x.den : K)⁻¹ := eq_inv_of_mul_eq_one_left hinv
  refine ⟨(n : O) * ↑hdu.unit⁻¹, ?_⟩
  rw [map_mul, map_intCast, hainv, Rat.cast_def, hn]
  push_cast
  ring

def Rblk (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  open Classical in
  ∏ x ∈ Finset.univ \ (Finset.univ.image (symVar C0 CE1 CE2 X j)), (baseExp C0 CE1 CE2 X j b x).factorial

theorem expFact_ioExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) :
    expFact (ioExp C0 CE1 CE2 X j b μ) = Rblk C0 CE1 CE2 X j b *
      ∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
        symLev X.p C0 CE1 CE2 X j v * μ v).factorial := by
  classical
  have hinj := symVar_inj C0 CE1 CE2 X j
  have hsumv : ∀ x, (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) x =
      ∑ v ∈ μ.support, if symVar C0 CE1 CE2 X j v = x then symLev X.p C0 CE1 CE2 X j v * μ v else 0 := by
    intro x
    rw [Finsupp.sum_apply]
    exact Finset.sum_congr rfl fun v _ => Finsupp.single_apply
  have hout : ∀ x ∉ Finset.univ.image (symVar C0 CE1 CE2 X j),
      ioExp C0 CE1 CE2 X j b μ x = baseExp C0 CE1 CE2 X j b x := by
    intro x hx
    rw [ioExp, Finsupp.add_apply, hsumv, Finset.sum_eq_zero, add_zero]
    intro v _
    rw [if_neg]
    intro h
    exact hx (Finset.mem_image.2 ⟨v, Finset.mem_univ _, h⟩)
  have hin : ∀ v, ioExp C0 CE1 CE2 X j b μ (symVar C0 CE1 CE2 X j v) =
      baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) + symLev X.p C0 CE1 CE2 X j v * μ v := by
    intro v
    rw [ioExp, Finsupp.add_apply, hsumv]
    congr 1
    rw [Finset.sum_eq_single v]
    · rw [if_pos rfl]
    · intro v' _ hne
      rw [if_neg]
      exact fun h => hne (hinj h)
    · intro hv
      have h0 : μ v = 0 := by simpa using hv
      rw [if_pos rfl, h0, mul_zero]
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image (symVar C0 CE1 CE2 X j)))]
  rw [Finset.prod_image (fun a _ c _ h => hinj h)]
  congr 1
  · unfold Rblk
    exact Finset.prod_congr rfl fun x hx => by rw [hout x (Finset.mem_sdiff.1 hx).2]
  · exact Finset.prod_congr rfl fun v _ => by rw [hin v]

theorem baseExp_odd (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (i0 : Fin (segS X.TT j)) (β0 : Bool) (c0 : Fin (X.m + 1)) :
    baseExp C0 CE1 CE2 X j b ((topOdd X j i0, β0), c0) = (if β0 then b.rz i0 c0 else b.ry i0 c0) +
      (if (i0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma ∧ c0 = 0 then (X.seg C0 CE1 CE2 j).P X.p i0 *
        (if β0 then coarseA X.p (X.seg C0 CE1 CE2 j) b i0 - b.w i0 else b.sg i0) else 0) := by
  classical
  have hinj := topOdd_inj X j
  have hite : ∀ (Q : Prop) [Decidable Q] (f : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ) (y),
      (if Q then f else 0) y = if Q then f y else 0 := by
    intro Q _ f y
    split_ifs <;> rfl
  have hne : ∀ (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)), i ≠ i0 →
      ((topOdd X j i, β), c) ≠ ((topOdd X j i0, β0), c0) := by
    intro i β c hi h
    exact hi (hinj (congrArg (fun y => y.1.1) h))
  rw [baseExp, Finsupp.add_apply]
  congr 1
  · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i0]
    · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c0]
      · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
        cases β0 <;> simp
      · intro c _ hc
        rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg, if_neg]
        · rfl
        · intro h
          exact hc (congrArg (fun y => y.2) h)
        · intro h
          exact hc (congrArg (fun y => y.2) h)
      · intro h
        exact absurd (Finset.mem_univ c0) h
    · intro i _ hi
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne i true c hi),
        if_neg (hne i false c hi)]
      rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h
  · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i0]
    · rw [hite]
      by_cases h1 : (i0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma
      · by_cases hc : c0 = 0
        · subst hc
          rw [if_pos h1, if_pos ⟨h1, rfl⟩, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
          cases β0 <;> simp
        · rw [if_pos h1, if_neg (fun h => hc h.2), Finsupp.add_apply, Finsupp.single_apply,
            Finsupp.single_apply, if_neg, if_neg]
          · rfl
          · intro h
            exact hc (congrArg (fun y => y.2) h).symm
          · intro h
            exact hc (congrArg (fun y => y.2) h).symm
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    · intro i _ hi
      rw [hite]
      split_ifs
      · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne i true 0 hi),
          if_neg (hne i false 0 hi)]
        rfl
      · rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h

theorem baseExp_end (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (β0 : Bool) (c0 : Fin (X.m + 1)) : baseExp C0 CE1 CE2 X j b ((topEnd X j, β0), c0) = 0 := by
  classical
  have hite : ∀ (Q : Prop) [Decidable Q] (f : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ) (y),
      (if Q then f else 0) y = if Q then f y else 0 := by
    intro Q _ f y
    split_ifs <;> rfl
  simp [baseExp, Finsupp.finsetSum_apply, Finsupp.single_apply, topOdd_ne_end, hite]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees MvPolynomial

theorem p_not_unit {O : Type} [CommRing O] {p : ℕ} {w : O} (hw : Irreducible w) (hpw : w ^ 2 = (p : O)) :
    ¬ IsUnit (p : O) := by
  rw [← hpw]
  intro h
  exact hw.not_isUnit (isUnit_of_mul_isUnit_left (by rwa [pow_two] at h))

theorem charZero_of_w {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime) {w : O} (hw : Irreducible w)
    (hpw : w ^ 2 = (p : O)) : CharZero O := by
  have hp0 : (p : O) ≠ 0 := by rw [← hpw]; exact pow_ne_zero _ hw.ne_zero
  have hpu := p_not_unit hw hpw
  obtain ⟨c, hc⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O c with h | h
  · exfalso
    have hc0 : (c : O) = 0 := CharP.cast_eq_zero O c
    by_cases hcp : c = p
    · exact hp0 (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h hp).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact hpu (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero O

def KapAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O),
    Irreducible w → w ^ 2 = (X.p : O) → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ κ : O, κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        ∀ μ, HomExp C0 CE1 CE2 X j b μ →
          zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) * (Rblk C0 CE1 CE2 X j b : KK O) *
            (∏ v : BV C0 CE1 CE2 X j, ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial : KK O) *
              ((symLev X.p C0 CE1 CE2 X j v).factorial : KK O) ^ (μ v)) =
          algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O)

theorem lev_pow (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    ∃ t, (X.seg C0 CE1 CE2 j).P X.p i = X.p ^ (t + 1) := by
  obtain ⟨s, ⟨-, -, -, h4⟩, h5⟩ := get_spec X.TT j i
  have hlt : (segDists X.TT j).get i < segG X.TT j := h5 ▸ h4
  refine ⟨segG X.TT j - (segDists X.TT j).get i - 1, ?_⟩
  show X.p ^ (segG X.TT j - (segDists X.TT j).get i) = _
  congr 1
  omega

theorem oddVar_data (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (v : BV C0 CE1 CE2 X j)
    (hv : IsOddVar C0 CE1 CE2 X j v) :
    (∃ t, symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1)) ∧
      baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · have h : (a : ℕ) < 2 * segS X.TT j := hv
    simp only [symLev, symVar, dif_pos h]
    refine ⟨lev_pow C0 CE1 CE2 X j _, ?_⟩
    rw [baseExp_odd]
    simp only [Fin.succ_ne_zero, and_false, if_false, add_zero]
    split_ifs
    · exact (hb.1.1 _ _).1
    · exact (hb.1.1 _ _).2
  · have h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := hv
    simp only [symLev, symVar, dif_pos h]
    refine ⟨lev_pow C0 CE1 CE2 X j _, ?_⟩
    rw [baseExp_odd]
    have hz : ¬ ((uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩ : ℕ) < (X.seg C0 CE1 CE2 j).sigma) := by
      show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma)
      omega
    simp only [hz, false_and, if_false, add_zero]
    split_ifs
    · exact (hb.1.1 _ _).1
    · exact (hb.1.1 _ _).2

theorem endVar_data (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (v : BV C0 CE1 CE2 X j) (hv : ¬ IsOddVar C0 CE1 CE2 X j v) :
    symLev X.p C0 CE1 CE2 X j v = 1 ∧ baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) = 0 := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · have h : ¬ (a : ℕ) < 2 * segS X.TT j := hv
    simp only [symLev, symVar, dif_neg h]
    exact ⟨trivial, baseExp_end C0 CE1 CE2 X j b _ _⟩
  · have h : ¬ (l : ℕ) < (X.seg C0 CE1 CE2 j).t := hv
    simp only [symLev, symVar, dif_neg h]
    exact ⟨trivial, baseExp_end C0 CE1 CE2 X j b _ _⟩

theorem factAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hK : KapAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : FactAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ _ w hw h2 hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  have hpO := p_not_unit hw h2
  have hO : CharZero O := charZero_of_w hp hw h2
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨κ, hκ0, hκv, hκ⟩ := hK X O w hw h2 hD1 hH hc j b hb
  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  obtain ⟨T, q, hT, hfa⟩ := fact_abs h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) X.c
  have hq : ∀ ν, ∃ y : O, ν ∈ T → ((q ν : ℚ) : KK O) = algebraMap O (KK O) y := by
    intro ν
    by_cases hν : ν ∈ T
    · obtain ⟨y, hy⟩ := rat_int (O := O) (K := KK O) hp hpO (q ν) 0 (by simpa using (hT ν hν).2.2)
      exact ⟨y, fun _ => by rw [hy, pow_zero, one_mul]⟩
    · exact ⟨0, fun h => absurd h hν⟩
  choose qO hqO using hq
  refine ⟨κ, T, qO, hκ0, hκv, fun ν hν => ⟨(hT ν hν).1, (hT ν hν).2.1⟩, ?_⟩
  intro μ hμ
  obtain ⟨h, hh, heq⟩ := hfa μ
  obtain ⟨y, hy⟩ := rat_int (O := O) (K := KK O) hp hpO h X.c hh
  refine ⟨w ^ X.c * y, ?_⟩
  have hg : algebraMap O (KK O) (gEv T qO μ) =
      ((∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ) : ℚ) : KK O) := by
    unfold gEv
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [map_mul, ← hqO ν hν, map_natCast, Rat.cast_mul, Rat.cast_natCast]
  have heqK := congrArg (fun x : ℚ => (x : KK O)) heq
  simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Rat.cast_pow] at heqK
  have hsplit : (∏ x : BV C0 CE1 CE2 X j,
      ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j x)).factorial : KK O) * ((μ x).factorial : KK O) *
        ((symLev X.p C0 CE1 CE2 X j x).factorial : KK O) ^ (μ x)) =
      (∏ v : BV C0 CE1 CE2 X j, ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial : KK O) *
        ((symLev X.p C0 CE1 CE2 X j v).factorial : KK O) ^ (μ v)) * ∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hmu : (expFact μ : KK O) = ∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O) := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    push_cast
    rfl
  have hW : (algebraMap O (KK O) (w ^ X.c)) ^ 2 = (X.p : KK O) ^ X.c := by
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, h2, map_pow, map_natCast]
  have hk := hκ μ hμ
  rw [expFact_ioExp, hg, hmu, map_add (f := _), map_one, map_mul, map_mul, Nat.cast_mul, Nat.cast_prod]
  rw [hsplit] at heqK
  linear_combination (zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) *
      (Rblk C0 CE1 CE2 X j b : KK O)) * heqK +
    ((∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O)) * (1 + (h : KK O))) * hk +
    (algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
      (∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O))) * hy -
    (algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
      (∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O)) * algebraMap O (KK O) y) * hW

end Formalism.MainNotions.ColumnSystems.Pf
