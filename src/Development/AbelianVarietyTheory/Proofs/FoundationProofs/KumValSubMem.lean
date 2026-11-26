module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RecipConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqTrue
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDiscreteInertiaKummerCoboundaryBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDiscreteInertiaKummerCoboundaryBound
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.HTTrace

theorem apply_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G ℚ Ω)
    {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod ℚ Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ

theorem cycMod_eq_one (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (hm : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) (s : G ℚ Ω) (hsζ : s ζ = ζ) : cycMod ℚ Ω l m s = 1 := by
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ m) := ⟨hlm⟩
  have h1 := apply_pow Ω l m s hζ.pow_eq_one
  rw [hsζ] at h1
  have hv1 : ((cycMod ℚ Ω l m s : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val = 1 := by
    have := hζ.pow_inj (i := 1) (j := ((cycMod ℚ Ω l m s : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val) hlm (ZMod.val_lt _)
      (by rw [pow_one]; exact h1)
    exact this.symm
  ext
  rw [Units.val_one]
  apply ZMod.val_injective
  rw [hv1, ZMod.val_one]

theorem exists_gen (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (m : ℕ) (hm : 1 ≤ m) (ζ ζ' : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m))
    (hζ' : ζ' ^ (l ^ m) = ζ) :
    ∃ s ∈ Ine (F := ℚ) A, s ζ' = ζ * ζ' := by
  obtain ⟨v, hv, hlv⟩ := hA
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hv (l : 𝓞 ℚ)).2 hlv
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) hl1
  have hlt : 1 + l ^ m < l ^ (2 * m) := by
    rw [two_mul, pow_add]; nlinarith
  have hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (2 * m))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h
    have h2 : l ∣ l ^ m := dvd_pow_self l (by omega)
    have h3 : l ∣ 1 := (Nat.dvd_add_left h2).mp h
    have := Nat.le_of_dvd one_pos h3
    omega
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hAl (2 * m) hu.unit
  have hsu' : ((cycMod ℚ Ω l (2 * m) s : (ZMod (l ^ (2 * m)))ˣ) : ZMod (l ^ (2 * m)))
      = ((1 + l ^ m : ℕ) : ZMod (l ^ (2 * m))) := by
    have := congrArg Units.val hsu
    simpa using this
  have hpow2 : ζ' ^ (l ^ (2 * m)) = 1 := by
    rw [two_mul, pow_add, pow_mul, hζ', hζ.pow_eq_one]
  refine ⟨s, hs, ?_⟩
  rw [apply_pow Ω l (2 * m) s hpow2, hsu', ZMod.val_natCast, Nat.mod_eq_of_lt hlt, pow_add, pow_one, hζ', mul_comm]

theorem isPrimitiveRoot_root {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (ζ ζ' : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hζ' : ζ' ^ (l ^ m) = ζ) : IsPrimitiveRoot ζ' (l ^ (2 * m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [IsPrimitiveRoot.iff_orderOf, show 2 * (n + 1) = (n + 1 + n) + 1 by ring]
  apply orderOf_eq_prime_pow
  · rw [pow_add, pow_mul, hζ']
    exact hζ.pow_ne_one_of_pos_of_lt (pow_pos (Fact.out : l.Prime).pos n).ne'
      (Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (by omega))
  · rw [show (n + 1 + n) + 1 = (n + 1) + (n + 1) by ring, pow_add l (n + 1) (n + 1), pow_mul, hζ', hζ.pow_eq_one]

theorem geom_sum_root {Ω : Type} [Field Ω] (N : ℕ) (u : Ω) (hu : u ^ N = 1) :
    ∃ e : ℕ, ∑ j ∈ Finset.range N, u ^ j = (N : Ω) * e := by
  by_cases h : u = 1
  · exact ⟨1, by simp [h]⟩
  · refine ⟨0, ?_⟩
    have h1 := geom_sum_mul u N
    rw [hu, sub_self] at h1
    simpa using (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)

theorem trace_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (N : ℕ) (ζ ζ' : Ω) (hζ : ζ ^ N = 1)
    (hζ'A : ζ' ∈ A) (γ : G ℚ Ω) (h1 : γ ζ = ζ) (h2 : γ ζ' = ζ * ζ') (Q : Polynomial Ω)
    (hQ : ∀ d, Q.coeff d ∈ A ∧ γ (Q.coeff d) = Q.coeff d) :
    ∃ v ∈ A, ∑ j ∈ Finset.range N, (γ ^ j) (Q.eval ζ') = (N : Ω) * v := by
  have hfix : ∀ a : Ω, γ a = a → ∀ j : ℕ, (γ ^ j) a = a := by
    intro a ha j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
  have hj : ∀ j : ℕ, (γ ^ j) ζ' = ζ ^ j * ζ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h2, map_mul, hfix ζ h1, ih]; ring
  choose e he using fun d : ℕ => geom_sum_root N (ζ ^ d) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])
  refine ⟨∑ d ∈ Finset.range (Q.natDegree + 1), Q.coeff d * ζ' ^ d * e d,
    sum_mem fun d _ => mul_mem (mul_mem (hQ d).1 (pow_mem hζ'A d)) (natCast_mem A _), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.eval_eq_sum_range, map_sum, map_mul, map_pow, hj, hfix _ (hQ _).2]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have : ∀ j : ℕ, Q.coeff d * (ζ ^ j * ζ') ^ d = Q.coeff d * ζ' ^ d * (ζ ^ d) ^ j := fun j => by ring
  simp only [this]
  rw [← Finset.mul_sum, he d]; ring

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m k : ℕ), k ≤ m → ∀ (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ → ∀ o x : Ω, o ∈ A → x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s o = o) →
  (∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ t : ZMod (l ^ m), s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l k ((t.val : Ω) * o) (s x - x)) →
  GlobalTheory.Glue.CgA A l k ((l : Ω) ^ c * o) 0 := by
  intro l _ hl2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ A hA m k hkm ζ ζ' hζ hζ' o x ho hx hofix hyp
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  rcases k with _ | k
  · exact ⟨(l : Ω) ^ 1 * o, mul_mem (pow_mem hlA 1) ho, by simp⟩
  have hm : 1 ≤ m := by omega
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ m) := ⟨hlm⟩
  have hprim := isPrimitiveRoot_root l m hm ζ ζ' hζ hζ'
  have hζ'A : ζ' ∈ A := by
    rw [← A.valuation_le_one_iff]
    have h1 := congrArg A.valuation hprim.pow_eq_one
    rw [map_pow, map_one] at h1
    exact (pow_le_one_iff (pow_pos (Fact.out : l.Prime).pos _).ne').1 h1.le
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ MulAction.stabilizer (G ℚ Ω) ζ'
  have hHmem : ∀ s : G ℚ Ω, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ s ζ' = ζ' := fun s => Iff.rfl
  have hHζ : ∀ s : G ℚ Ω, s ζ' = ζ' → s ζ = ζ := fun s hs => by rw [← hζ', map_pow, hs]
  have hHc : ∀ s : G ℚ Ω, s ζ' = ζ' → cycMod ℚ Ω l m s = 1 := fun s hs =>
    cycMod_eq_one l Ω m hm ζ hζ s (hHζ s hs)
  obtain ⟨y, hyA, hyfix, e, heA, he⟩ := GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A hA H (inf_le_left.trans (Ine_le_Dec A)) k x hx (by
    intro h hh
    obtain ⟨hh1, hh2⟩ := (hHmem h).1 hh
    obtain ⟨z, hz, hze⟩ := hyp h hh1 (hHc h hh2) 0 (by simpa using hh2)
    refine ⟨-z, neg_mem hz, ?_⟩
    simp only [ZMod.val_zero, Nat.cast_zero, zero_mul] at hze
    linear_combination -hze)
  obtain ⟨γ, hγI, hγ⟩ := exists_gen l Ω A hA m hm ζ ζ' hζ hζ'
  have hγζ : γ ζ = ζ := by
    conv_lhs => rw [← hζ']
    rw [map_pow, hγ, mul_pow, hζ.pow_eq_one, one_mul, hζ']
  have hγc := cycMod_eq_one l Ω m hm ζ hζ γ hγζ
  obtain ⟨z, hzA, hz⟩ := hyp γ hγI hγc 1 (by rw [ZMod.val_one, pow_one]; exact hγ)
  rw [ZMod.val_one, Nat.cast_one, one_mul] at hz
  have hγD := Ine_le_Dec A hγI
  set w : Ω := γ e - e + l * z with hw
  have hwA : w ∈ A :=
    add_mem (sub_mem ((apply_mem_iff_of_mem_Dec hγD e).2 heA) heA) (mul_mem hlA hzA)
  have hweq : (l : Ω) ^ k * w = o - (γ y - y) := by
    have h1 := congrArg γ he
    rw [map_sub, map_mul, map_pow, map_natCast] at h1
    rw [hw]
    linear_combination -hz - h1 + he
  have hwfix : ∀ s ∈ Ine (F := ℚ) A, s ζ' = ζ' → s w = w := by
    intro s hs hsζ
    have h1 : γ⁻¹ * s * γ⁻¹⁻¹ ∈ H := by
      refine (hHmem _).2 ⟨conj_mem_Ine ((Dec (F := ℚ) A).inv_mem hγD) hs, ?_⟩
      rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγ, map_mul, hHζ s hsζ, hsζ, ← hγ]
      exact γ.symm_apply_apply ζ'
    have h2 : s (γ y) = γ y := by
      have h3 := congrArg γ (hyfix _ h1)
      rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply] at h3
      exact h3
    have h4 := congrArg s hweq
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, h2, hyfix s ((hHmem s).2 ⟨hs, hsζ⟩),
      hofix s hs (hHc s hsζ), ← hweq] at h4
    exact mul_left_cancel₀ (pow_ne_zero k hl0) h4
  obtain ⟨Q, hQ, hQw⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA (2 * m) ζ' hprim w hwA hwfix
  obtain ⟨v, hvA, hv⟩ := trace_mem A (l ^ m) ζ ζ' hζ.pow_eq_one hζ'A γ hγζ hγ Q fun d => ⟨(hQ d).1, (hQ d).2 γ hγI⟩
  rw [hQw] at hv
  have hfix : ∀ a : Ω, γ a = a → ∀ j : ℕ, (γ ^ j) a = a := by
    intro a ha j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
  have hj : ∀ j : ℕ, (γ ^ j) ζ' = ζ ^ j * ζ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hγ, map_mul, hfix ζ hγζ, ih]; ring
  have htop : (γ ^ (l ^ m)) y = y :=
    hyfix _ ((hHmem _).2 ⟨pow_mem hγI _, by rw [hj, hζ.pow_eq_one, one_mul]⟩)
  have hsum : ∑ j ∈ Finset.range (l ^ m), (γ ^ j) ((l : Ω) ^ k * w) = ((l ^ m : ℕ) : Ω) * o := by
    have h5 : ∀ j : ℕ, (γ ^ j) ((l : Ω) ^ k * w) = o - ((γ ^ (j + 1)) y - (γ ^ j) y) := fun j => by
      rw [hweq, map_sub, map_sub, hfix o (hofix γ hγI hγc), pow_succ, AlgEquiv.mul_apply]
    simp only [h5]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => (γ ^ j) y), htop]
    simp
  simp only [map_mul, map_pow, map_natCast] at hsum
  rw [← Finset.mul_sum, hv] at hsum
  have hN : ((l ^ m : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ho' : o = (l : Ω) ^ k * v := mul_left_cancel₀ hN (by linear_combination -hsum)
  exact ⟨v, hvA, by rw [ho']; ring⟩

end GlobalTheory.HTTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDiscreteInertiaKummerCoboundaryBoundStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m k : ℕ), k ≤ m → ∀ (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ → ∀ o x : Ω, o ∈ A → x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s o = o) →
  (∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ t : ZMod (l ^ m), s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l k ((t.val : Ω) * o) (s x - x)) →
  GlobalTheory.Glue.CgA A l k ((l : Ω) ^ c * o) 0 := by
  first | exact @GlobalTheory.HTTrace.main | exact GlobalTheory.HTTrace.main | (intros; apply GlobalTheory.HTTrace.main <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

noncomputable section

namespace GlobalTheory.LambdaValuationPowers.HTCoUniq

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (π : K) : AddSubgroup K where
  carrier := {z | ‖z‖ ≤ ‖π‖}
  zero_mem' := by simp
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' := fun ha => by simpa using ha

theorem mem_ball {π z : K} : z ∈ ball π ↔ ‖z‖ ≤ ‖π‖ := Iff.rfl

theorem mul_mem_ball {π a z : K} (ha : ‖a‖ ≤ 1) (hz : z ∈ ball π) : a * z ∈ ball π := by
  rw [mem_ball, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hz

theorem ball_pow_mono {p : K} (hp : ‖p‖ < 1) {i k : ℕ} (h : i ≤ k) {z : K} (hz : z ∈ ball (p ^ k)) : z ∈ ball (p ^ i) := by
  refine (mem_ball.1 hz).trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hp.le h

theorem mem_ball_of_mul {p : K} (hp0 : p ≠ 0) {a k : ℕ} (h : a ≤ k) {u z : K} (hu : ‖p ^ a‖ ≤ ‖u‖)
    (hz : u * z ∈ ball (p ^ k)) : z ∈ ball (p ^ (k - a)) := by
  rw [mem_ball] at hz ⊢
  have h1 : 0 < ‖p ^ a‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  have e : p ^ k = p ^ a * p ^ (k - a) := by rw [← pow_add, Nat.add_sub_cancel' h]
  rw [e, norm_mul, norm_mul] at hz
  exact le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans hz) h1

omit [IsUltrametricDist K] in
theorem exists_pow_le {p : K} (hp : ‖p‖ < 1) {u : K} (hu : u ≠ 0) : ∃ a : ℕ, ‖p ^ a‖ ≤ ‖u‖ := by
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hu) hp
  exact ⟨a, by rw [norm_pow]; exact ha.le⟩

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ K]

theorem smul_mem_ball (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) (g : Γ) {π z : K} (hz : z ∈ ball π) : g • z ∈ ball π := by
  rw [mem_ball, hn]; exact hz

theorem inv_mul (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) {lam : Γ → K} {π d x : K} (hd : ‖d‖ ≤ 1) {h t : Γ}
    (hfix : h • lam t = lam t) (hadd : lam (h * t) - lam h - lam t ∈ ball π)
    (h1 : d * lam h - (h • x - x) ∈ ball π) (h2 : d * lam t - (t • x - x) ∈ ball π)
    (h3 : d * lam (h * t) - ((h * t) • x - x) ∈ ball π) : lam t * (h • d - d) ∈ ball π := by
  have e : lam t * (h • d - d) = h • (d * lam t - (t • x - x)) - (d * lam (h * t) - ((h * t) • x - x)) +
      (d * lam h - (h • x - x)) + d * (lam (h * t) - lam h - lam t) := by
    simp only [smul_sub, smul_mul', hfix, mul_smul]; ring
  rw [e]
  exact add_mem (add_mem (sub_mem (smul_mem_ball hn h h2) h3) h1) (mul_mem_ball hd hadd)

theorem pow_sub_mem {lam : Γ → K} {π : K} (hadd : ∀ s t, lam (s * t) - lam s - lam t ∈ ball π) (s : Γ) (n : ℕ) :
    lam (s ^ n) - n * lam s ∈ ball π := by
  induction n with
  | zero => simpa using neg_mem (hadd 1 1)
  | succ n ih =>
    have e : lam (s ^ (n + 1)) - ((n + 1 : ℕ) : K) * lam s =
        (lam (s ^ n * s) - lam (s ^ n) - lam s) + (lam (s ^ n) - n * lam s) := by
      rw [pow_succ]; push_cast; ring
    rw [e]; exact add_mem (hadd _ _) ih

theorem transfer (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) (H : Subgroup Γ) [Fintype (Γ ⧸ H)] {lam : Γ → K} {π d y : K}
    (hd : ‖d‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hl : ∀ s, ‖lam s‖ ≤ 1) (hfix : ∀ g s : Γ, g • lam s = lam s)
    (hadd : ∀ s t, lam (s * t) - lam s - lam t ∈ ball π)
    (h1 : ∀ h ∈ H, d * lam h - (h • y - y) ∈ ball π) (h2 : ∀ h ∈ H, h • d - d ∈ ball π) :
    ∃ X : K, ‖X‖ ≤ 1 ∧ ∀ s : Γ, (∑ q : Γ ⧸ H, q.out • d) * lam s - (s • X - X) ∈ ball π := by
  refine ⟨∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d), ?_, fun s => ?_⟩
  · have : (∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d)) ∈ ball (1 : K) :=
      sum_mem fun q _ => sub_mem (smul_mem_ball hn _ (by simpa [mem_ball] using hy))
        (mul_mem_ball (hl _) (smul_mem_ball hn _ (by simpa [mem_ball] using hd)))
    simpa [mem_ball] using this
  · rw [← Equiv.sum_comp (MulAction.toPerm s) (fun q : Γ ⧸ H => q.out • d)]
    conv => enter [2, 2, 2]; rw [← Equiv.sum_comp (MulAction.toPerm s)]
    rw [Finset.smul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine sum_mem fun q _ => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (s * q.out)
    have hq : (MulAction.toPerm s q : Γ ⧸ H).out = s * q.out * h := by
      rw [← hh, MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul]
    rw [hq]
    set r := q.out
    have e : (s * r * h) • d * lam s - (s • (r • y - lam r * r • d) - ((s * r * h) • y - lam (s * r * h) * (s * r * h) • d)) =
        - ((s * r) • (d * lam h - ((h : Γ) • y - y))) - (lam r + lam h) * (s * r) • ((h : Γ) • d - d) -
          (s * r * h) • d * (lam (s * r * h) - lam (s * r) - lam h) - (s * r * h) • d * (lam (s * r) - lam s - lam r) := by
      simp only [smul_sub, smul_mul', hfix, mul_smul]; ring
    rw [e]
    have hd' : ‖(s * r * h) • d‖ ≤ 1 := by rw [hn]; exact hd
    refine sub_mem (sub_mem (sub_mem (neg_mem (smul_mem_ball hn _ (h1 h h.2))) (mul_mem_ball ?_ (smul_mem_ball hn _ (h2 h h.2))))
      (mul_mem_ball hd' (hadd _ _))) (mul_mem_ball hd' (hadd _ _))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hl _) (hl _))

theorem core [CharZero K] {R : Type} [CommRing R] [Algebra R K] (O : Subalgebra R K) [Finite (O →ₐ[R] K)]
    (hO : ∀ a ∈ O, ‖a‖ ≤ 1) (hφ : ∀ (φ : O →ₐ[R] K) a, ‖φ a‖ ≤ 1) {p : K} (hp0 : p ≠ 0) (hp : ‖p‖ < 1) (c : ℕ) :
    ∃ c₁ : ℕ, ∀ (Γ : Type) [Group Γ] [MulSemiringAction Γ K] (_ : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖)
      (_ : ∀ (g : Γ) (a : R), g • algebraMap R K a = algebraMap R K a) (lam : Γ → K) (m k : ℕ) (_ : k ≤ m)
      (_ : ∀ s, ‖lam s‖ ≤ 1) (_ : ∀ g s : Γ, g • lam s = lam s)
      (_ : ∀ s t, lam (s * t) - lam s - lam t ∈ ball (p ^ m)) (s₀ : Γ) (_ : ‖lam s₀‖ = 1)
      (_ : ∀ k' ≤ m, ∀ T X : K, ‖T‖ ≤ 1 → ‖X‖ ≤ 1 → (∀ s : Γ, T * lam s - (s • X - X) ∈ ball (p ^ k')) →
        p ^ c * T ∈ ball (p ^ k')) (d y : K) (_ : ‖d‖ ≤ 1) (_ : ‖y‖ ≤ 1)
      (_ : ∀ h : Γ, (∀ a ∈ O, h • a = a) → d * lam h - (h • y - y) ∈ ball (p ^ k)), d ∈ ball (p ^ (k - c₁)) := by
  classical
  haveI := Fintype.ofFinite (O →ₐ[R] K)
  have hsep : ∀ φ : O →ₐ[R] K, ∃ a : O, φ ≠ O.val → (a : K) - φ a ≠ 0 := by
    intro φ
    by_cases h : φ = O.val
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
      exact ⟨a, fun _ => sub_ne_zero.2 (Ne.symm ha)⟩
  choose α hα using hsep
  set S : Finset (O →ₐ[R] K) := Finset.univ.erase O.val with hS
  have hD : (∏ φ ∈ S, ((α φ : K) - φ (α φ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun φ h => hα φ (Finset.ne_of_mem_erase h)
  obtain ⟨b, hb⟩ := exists_pow_le hp hD
  have hN : (((Nat.card (O →ₐ[R] K)).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  obtain ⟨a, ha⟩ := exists_pow_le hp hN
  refine ⟨a + c + b + 1, ?_⟩
  intro Γ _ _ hn hR lam m k hkm hl hfix hadd s₀ hs₀ U d y hd hy hyp
  by_cases hk : k ≤ a + c + b + 1
  · rw [Nat.sub_eq_zero_of_le hk, mem_ball]; simpa using hd
  let H : Subgroup Γ :=
    { carrier := {h | ∀ a ∈ O, h • a = a}
      one_mem' := fun a _ => one_smul _ _
      mul_mem' := fun {g h} hg hh a ha => by rw [mul_smul, hh a ha, hg a ha]
      inv_mem' := fun {g} hg a ha => by rw [inv_smul_eq_iff, hg a ha] }
  let e : Γ → (O →ₐ[R] K) := fun g =>
    { toRingHom := (MulSemiringAction.toRingHom Γ K g).comp (O.val : O →+* K)
      commutes' := fun r => hR g r }
  have he : ∀ g (a : O), e g a = g • (a : K) := fun _ _ => rfl
  have hinj : Function.Injective fun q : Γ ⧸ H => e q.out := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq]
    intro a ha
    rw [mul_smul, inv_smul_eq_iff]
    exact (DFunLike.congr_fun hq ⟨a, ha⟩).symm
  haveI : Finite (Γ ⧸ H) := Finite.of_injective _ hinj
  haveI := Fintype.ofFinite (Γ ⧸ H)
  have hidx : H.index ≤ Nat.card (O →ₐ[R] K) := Nat.card_le_card_of_injective _ hinj
  have ht : s₀ ^ (Nat.card (O →ₐ[R] K)).factorial ∈ H :=
    Subgroup.pow_mem_of_index_ne_zero_of_dvd (Nat.card_pos (α := Γ ⧸ H)).ne' s₀
      fun n h0 hn => Nat.dvd_factorial h0 (hn.trans hidx)
  set t := s₀ ^ (Nat.card (O →ₐ[R] K)).factorial
  have hlt : ‖p ^ a‖ ≤ ‖lam t‖ := by
    by_contra hlt
    push Not at hlt
    have h1 := pow_sub_mem hadd s₀ (Nat.card (O →ₐ[R] K)).factorial
    have h2 : ‖p ^ m‖ < ‖p ^ a‖ := by
      rw [norm_pow, norm_pow]
      exact pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.2 hp0) hp (by omega)
    have h3 := IsUltrametricDist.norm_add_le_max (lam t) (-(lam t - ((Nat.card (O →ₐ[R] K)).factorial : ℕ) * lam s₀))
    rw [norm_neg, neg_sub, add_sub_cancel, norm_mul, hs₀, mul_one] at h3
    exact absurd (ha.trans h3) (not_le.2 (max_lt hlt (lt_of_le_of_lt h1 h2)))
  have hinv : ∀ h ∈ H, h • d - d ∈ ball (p ^ (k - a)) := fun h hh =>
    mem_ball_of_mul hp0 (by omega) hlt (inv_mul hn hd (hfix _ _) (ball_pow_mono hp hkm (hadd _ _))
      (hyp h hh) (hyp t ht) (hyp _ (H.mul_mem hh ht)))
  have hT : ∀ β ∈ O, p ^ c * ∑ q : Γ ⧸ H, q.out • (β * d) ∈ ball (p ^ (k - a)) := by
    intro β hβ
    have hβd : ‖β * d‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hd
    have hβy : ‖β * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hy
    obtain ⟨X, hX, hXs⟩ := transfer hn H (π := p ^ (k - a)) hβd hβy hl hfix
      (fun s t => ball_pow_mono hp (by omega) (hadd s t))
      (fun h hh => by
        have := mul_mem_ball (hO β hβ) (ball_pow_mono hp (Nat.sub_le k a) (hyp h hh))
        rw [smul_mul', hh β hβ]
        convert this using 1; ring)
      (fun h hh => by
        have := mul_mem_ball (hO β hβ) (hinv h hh)
        rw [smul_mul', hh β hβ]
        convert this using 1; ring)
    refine U _ (by omega) _ X ?_ hX hXs
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => by rw [hn]; exact hβd
  have hsep : ∀ S' : Finset (O →ₐ[R] K), ∀ β ∈ O,
      p ^ c * ∑ q : Γ ⧸ H, (∏ φ ∈ S', (q.out • (α φ : K) - φ (α φ))) * q.out • (β * d) ∈ ball (p ^ (k - a)) := by
    intro S'
    induction S' using Finset.induction_on with
    | empty => simpa using hT
    | insert φ S' hφS ih =>
      intro β hβ
      have h1 := sub_mem (ih (α φ * β) (O.mul_mem (α φ).2 hβ)) (mul_mem_ball (hφ φ (α φ)) (ih β hβ))
      convert h1 using 1
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_insert hφS]
      simp only [smul_mul']
      ring
  have h1 := hsep S 1 O.one_mem
  have hout : ((1 : Γ) : Γ ⧸ H).out ∈ H := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (1 : Γ)
    rw [hh, one_mul]; exact h.2
  rw [Finset.sum_eq_single ((1 : Γ) : Γ ⧸ H) (fun q _ hq => ?_) (by simp)] at h1
  · have h2 : (p ^ c * ∏ φ ∈ S, ((α φ : K) - φ (α φ))) * d ∈ ball (p ^ (k - a)) := by
      rw [Finset.prod_congr rfl (fun φ _ => by rw [hout _ (α φ).2])] at h1
      rw [mem_ball] at h1 ⊢
      simpa only [norm_mul, hn, one_mul, mul_assoc] using h1
    have h3 := mem_ball_of_mul hp0 (a := c + b) (by omega)
      (by rw [pow_add, norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)) h2
    exact ball_pow_mono hp (by omega) h3
  · have hne : e q.out ≠ O.val := by
      intro h
      apply hq
      apply hinj
      show e q.out = e _
      rw [h]
      ext a
      exact (hout _ a.2).symm
    rw [Finset.prod_eq_zero (i := e q.out) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) (by rw [he, sub_self]), zero_mul]

end Abstract

open ReciprocityTheory.Neutral.Cmp

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral {a : Qbar l} (hi : IsIntegral ℤ_[l] a) : ‖a‖ ≤ 1 := by
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}


omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in
theorem cgA_iff (hj : Compat l A j) (n : ℕ) (x y : Ω) :
    GlobalTheory.Glue.CgA A l n x y ↔ j x - j y ∈ ball ((l : Qbar l) ^ n) := by
  have h0 : ((l : Qbar l) ^ n) ≠ 0 := pow_ne_zero _ natCast_ne_zero
  constructor
  · rintro ⟨z, hz, e⟩
    rw [← map_sub, e, map_mul, map_pow, map_natCast, mul_comm]
    exact mul_mem_ball ((hj z).1 hz) (mem_ball.2 le_rfl)
  · intro h
    have h1 : ((l : Ω) ^ n) ≠ 0 := by
      intro h'
      apply h0
      simpa using congrArg j h'
    refine ⟨(x - y) / (l : Ω) ^ n, (hj _).2 ?_, by field_simp⟩
    rw [map_div₀, map_sub, map_pow, map_natCast, norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)

theorem exists_approx (hj : Compat l A j) (n : ℕ) {T : Qbar l} (hT : ‖T‖ ≤ 1) :
    ∃ o ∈ A, T - j o ∈ ball ((l : Qbar l) ^ n) := by
  obtain ⟨o, ho⟩ := Metric.denseRange_iff.1 (denseRange ℚ j) T _
    (norm_pos_iff.2 (pow_ne_zero n (natCast_ne_zero (l := l))))
  rw [dist_eq_norm] at ho
  refine ⟨o, (hj o).2 ?_, ho.le⟩
  have h1 : T - j o ∈ ball ((l : Qbar l) ^ 0) := ball_pow_mono norm_natCast_lt_one (Nat.zero_le n) ho.le
  have h2 : T ∈ ball ((l : Qbar l) ^ 0) := by simpa [mem_ball] using hT
  simpa [mem_ball] using sub_mem h2 h1

omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in
theorem valuation_lt_one (hj : Compat l A j) : A.valuation (l : Ω) < 1 := by
  rw [hj.valuation_lt_one_iff, map_natCast]; exact norm_natCast_lt_one

theorem overL (hj : Compat l A j) : OverL l A := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have h := lies_over_ratPrime A (valuation_lt_one hj)
  refine ⟨ratPrime l, fun x => by simpa using h x, (h (l : 𝓞 ℚ)).1 ?_⟩
  simpa using valuation_lt_one hj

theorem exists_norm_lamv_eq_one (hl2 : l ≠ 2) (hA : A.valuation (l : Ω) < 1) (m : ℕ) :
    ∃ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 ∧ ‖lamv l m s‖ = 1 := by
  have hl := (Fact.out : l.Prime)
  have hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by simpa using h))
    · exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (dvd_pow_self l hm.ne')).mp h))
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA (m + 1) hu.unit
  have h1 : PadicInt.toZModPow (m + 1) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
    simpa [cycMod] using congrArg Units.val hsu
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - ((1 + l ^ m : ℕ) : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow (m + 1) : ℤ_[l] →+* ZMod (l ^ (m + 1))) := by
    rw [RingHom.mem_ker, map_sub, h1, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨b, hb⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * (1 + l * b) := by
    push_cast at hb
    linear_combination hb
  have hm : cycMod ℚ Ω l m s = 1 := by
    ext
    show PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1
    rw [h3, map_add (f := _), map_one, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
  refine ⟨s, hs, hm, ?_⟩
  obtain ⟨a, ha, ha'⟩ := exists_lamv_eq hm
  have h4 : a = 1 + l * b :=
    mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero)) (add_left_cancel (ha.symm.trans h3))
  rw [ha', norm_algebraMap_padicInt, h4]
  have h5 : ‖(l : ℤ_[l]) * b‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one b))
      (PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h5.ne'), norm_one, max_eq_left h5.le]

theorem kummer_sub_lamv {m : ℕ} {ζ' : Ω} (hζ : IsPrimitiveRoot ζ' (l ^ (m + m))) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1)
    {t : ℕ} (ht : s ζ' = (ζ' ^ l ^ m) ^ t * ζ') : (t : Qbar l) - lamv l m s ∈ ball ((l : Qbar l) ^ m) := by
  have hl := (Fact.out : l.Prime)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have h1 : s ζ' = ζ' ^ (PadicInt.toZModPow (m + m) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ' hζ.pow_eq_one
  rw [ht, ← pow_mul, ← pow_succ, pow_eq_pow_mod _ hζ.pow_eq_one] at h1
  have : NeZero (l ^ (m + m)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  replace h1 := congrArg (Nat.cast : ℕ → ZMod (l ^ (m + m)))
    (hζ.pow_inj (Nat.mod_lt _ (pow_pos hl.pos _)) (ZMod.val_lt _) h1)
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val] at h1
  obtain ⟨a, ha, ha'⟩ := exists_lamv_eq hs
  have h2 : ((l ^ m * t + 1 : ℕ) : ℤ_[l]) - ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow (m + m) : ℤ_[l] →+* ZMod (l ^ (m + m))) := by
    rw [RingHom.mem_ker, map_sub, ← h1, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨b, hb⟩ := h2
  have h4 : (t : ℤ_[l]) - a = b * (l : ℤ_[l]) ^ m := by
    apply mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero : (l : ℤ_[l]) ≠ 0))
    rw [ha] at hb
    push_cast at hb
    linear_combination hb
  have h5 := congrArg (algebraMap ℤ_[l] (Qbar l)) h4
  rw [RingHom.map_sub, map_natCast, map_mul, map_pow, map_natCast] at h5
  rw [ha', h5]
  exact mul_mem_ball (by rw [norm_algebraMap_padicInt]; exact PadicInt.norm_le_one b) (mem_ball.2 le_rfl)

def grp (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (m : ℕ) : Subgroup (GK ℚ j) :=
  (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker).comap (res j)

theorem exists_grp (hj : Compat l A j) {m : ℕ} {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (hm : cycMod ℚ Ω l m s = 1) :
    ∃ σ : grp A j m, res j σ.1 = s := by
  obtain ⟨σ, rfl⟩ := exists_res_eq hj (Ine_le_Dec A hs)
  exact ⟨⟨σ, ⟨hs, hm⟩⟩, rfl⟩

theorem smul_algebraMap (σ : GK ℚ j) (a : ℤ_[l]) : σ (algebraMap ℤ_[l] (Qbar l) a) = algebraMap ℤ_[l] (Qbar l) a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  exact σ.commutes ⟨_, (Kloc ℚ j).algebraMap_mem _⟩

theorem lamv_add_mem {m : ℕ} {s t : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) (ht : cycMod ℚ Ω l m t = 1) :
    lamv l m (s * t) - lamv l m s - lamv l m t ∈ ball ((l : Qbar l) ^ m) := by
  have e : lamv l m (s * t) - lamv l m s - lamv l m t = lamv l m s * (lamv l m t * (l : Qbar l) ^ m) := by
    rw [lamv_mul]; ring
  rw [e]
  exact mul_mem_ball (norm_lamv_le_one hs) (mul_mem_ball (norm_lamv_le_one ht) (mem_ball.2 le_rfl))

theorem smul_lamv {m : ℕ} (σ : GK ℚ j) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : σ (lamv l m s) = lamv l m s := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, smul_algebraMap]

theorem uniq_true (hl2 : l ≠ 2) : ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (j : Ω →+* Qbar l), Compat l A j → ∀ m k : ℕ, k ≤ m → ∀ T X : Qbar l, ‖T‖ ≤ 1 → ‖X‖ ≤ 1 →
    (∀ σ : grp A j m, T * lamv l m (res j σ.1) - (σ • X - X) ∈ ball ((l : Qbar l) ^ k)) →
    (l : Qbar l) ^ c * T ∈ ball ((l : Qbar l) ^ k) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound l hl2
  refine ⟨c + 1, ?_⟩
  intro Ω _ _ _ A j hj m k hkm T X hT hX hyp
  have hl := (Fact.out : l.Prime)
  have hp1 := norm_natCast_lt_one (l := l)
  have hpc : ‖(l : Qbar l) ^ c‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le
  rcases k with _ | n
  · have : T ∈ ball ((l : Qbar l) ^ 0) := by simpa [mem_ball] using hT
    exact mul_mem_ball (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le) this
  have hn : ∀ (g : grp A j m) (x : Qbar l), ‖g • x‖ = ‖x‖ := fun g x => norm_map_GK j g.1 x
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m
  obtain ⟨t, rfl⟩ := exists_grp hj hs₀ hm₀
  have hinv : ∀ h : grp A j m, h • T - T ∈ ball ((l : Qbar l) ^ (n + 1)) := by
    intro h
    have := inv_mul hn (lam := fun σ : grp A j m => lamv l m (res j σ.1)) hT (h := h) (t := t) (smul_lamv h.1 hm₀)
      (by simpa using ball_pow_mono hp1 hkm (lamv_add_mem h.2.2 hm₀)) (hyp _) (hyp _) (hyp _)
    rwa [mem_ball, norm_mul, hu₀, one_mul] at this
  obtain ⟨o, ho, hTo⟩ := exists_approx hj (n + 1) hT
  obtain ⟨x, hx, hXx⟩ := exists_approx hj (n + 1) hX
  obtain ⟨y, hy, hyfix, hoy⟩ := GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A (overL hj) (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker)
    (fun h hh => Ine_le_Dec A hh.1) n o ho (fun h hh => by
      obtain ⟨σ, rfl⟩ := exists_grp hj hh.1 hh.2
      rw [cgA_iff hj, res_spec]
      have := add_mem (sub_mem (hinv σ) (smul_mem_ball hn σ hTo)) hTo
      convert this using 1
      rw [smul_sub]
      show σ.1 (j o) - j o = σ.1 T - T - (σ.1 T - σ.1 (j o)) + (T - j o)
      ring)
  rw [cgA_iff hj] at hoy
  have hTy : T - j y ∈ ball ((l : Qbar l) ^ n) := by
    simpa using add_mem (ball_pow_mono hp1 (Nat.le_succ n) hTo) hoy
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l ^ (m + m) : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.ne_zero)⟩
  obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (m + m))
  have hζ : IsPrimitiveRoot (ζ' ^ l ^ m) (l ^ m) := hζ'.pow (pow_pos hl.pos _) (pow_add l m m)
  have key := hc Ω A (overL hj) m n (by omega) _ ζ' hζ rfl y x hy hx (fun s hs hm => hyfix s ⟨hs, hm⟩)
    (fun s hs hm τ hτ => by
      have h1 := kummer_sub_lamv hζ' hm hτ
      obtain ⟨σ, rfl⟩ := exists_grp hj hs hm
      rw [cgA_iff hj, map_mul, map_natCast, map_sub, res_spec]
      have h2 := ball_pow_mono hp1 (Nat.le_succ n) hXx
      have := sub_mem (add_mem (sub_mem (add_mem (ball_pow_mono hp1 (Nat.le_succ n) (hyp σ))
        (mul_mem_ball hT (ball_pow_mono hp1 (by omega : n ≤ m) h1)))
        (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one (Qbar l) τ.val) hTy)) (smul_mem_ball hn σ h2)) h2
      convert this using 1
      rw [smul_sub]
      show _ = T * _ - (σ.1 X - X) + _ - _ + (σ.1 X - σ.1 (j x)) - _
      ring)
  rw [cgA_iff hj, map_zero, sub_zero, map_mul, map_pow, map_natCast] at key
  have h3 := add_mem key (mul_mem_ball hpc hTy)
  rw [mem_ball] at h3 ⊢
  have e : (l : Qbar l) ^ (c + 1) * T = l * ((l : Qbar l) ^ c * j y + (l : Qbar l) ^ c * (T - j y)) := by ring
  rw [e, pow_succ' _ n, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)

end GlobalTheory.LambdaValuationPowers.HTCoUniq
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

noncomputable section

namespace GlobalTheory.LambdaValuationPowers.LocGlue

open GlobalTheory.LambdaValuationPowers.HTCoUniq ReciprocityTheory.Neutral.Cmp

theorem uniq_fix : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∃ c₂ : ℕ, ∀ (m : ℕ) (D : Qbar l) (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω),
    (∀ i, ‖o i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) →
    (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m (D * GlobalTheory.LambdaValuationPowers.lamv l m s) (∑ i, o i * (j (s (w i)) - j (w i)))) →
    Cg (m - c₂) D 0 := by
  intro l _ hl2 Ω _ _ _ A c j _ hj
  have hj' : Compat l A j := hj
  have hp1 := norm_natCast_lt_one (l := l)
  obtain ⟨c', hc'⟩ := uniq_true hl2
  obtain ⟨c₁, hc₁⟩ := core (K := Qbar l) c.O (fun a ha => norm_le_one_of_mem ha)
    (fun φ a => norm_le_one_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map φ))
    natCast_ne_zero hp1 c'
  refine ⟨c₁, ?_⟩
  intro m D q o w how hyp
  have hx : ‖∑ i, o i * j (w i)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (how i).1 (norm_nonneg _) (how i).2.2
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj') m
  have hd : ‖D‖ ≤ 1 := by
    have h1 : (∑ i, o i * (j (s₀ (w i)) - j (w i))) ∈ ball ((l : Qbar l) ^ 0) := by
      refine sum_mem fun i _ => mul_mem_ball (how i).1 (sub_mem ?_ ?_)
      · simpa [mem_ball] using (hj _).1 ((apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs₀) _).2 ((hj _).2 (how i).2.2))
      · simpa [mem_ball] using (how i).2.2
    have h2 := add_mem (ball_pow_mono hp1 (Nat.zero_le m) (mem_ball.2 (hyp s₀ hs₀ hm₀))) h1
    simpa [mem_ball, hu₀] using h2
  obtain ⟨t, rfl⟩ := exists_grp hj' hs₀ hm₀
  have key := hc₁ (grp A j m) (fun g x => norm_map_GK j g.1 x) (fun g a => smul_algebraMap g.1 a)
    (fun σ => lamv l m (res j σ.1)) m m le_rfl (fun σ => norm_lamv_le_one σ.2.2)
    (fun g σ => smul_lamv g.1 σ.2.2) (fun s t => by simpa using lamv_add_mem s.2.2 t.2.2) t hu₀
    (fun k hk T X hT hX hh => hc' Ω A j hj' m k hk T X hT hX hh) D _ hd hx fun σ hσ => ?_
  · simpa [Cg, mem_ball] using key
  have hine : ∀ x : Qbar l, ‖x‖ ≤ 1 → ‖σ.1 x - x‖ < 1 := by
    intro x hx1
    obtain ⟨a, ha, hxa⟩ := exists_approx hj' 1 hx1
    have h1 : ‖x - j a‖ < 1 := lt_of_le_of_lt (mem_ball.1 hxa) (by simpa using hp1)
    have h2 : ‖j (res j σ.1 a - a)‖ < 1 :=
      (hj'.valuation_lt_one_iff _).1 (σ.2.1.2 a ((A.valuation_le_one_iff a).2 ha))
    have e : σ.1 x - x = σ.1 (x - j a) + (j (res j σ.1 a - a) + -(x - j a)) := by
      rw [map_sub, map_sub, res_spec]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (by rwa [norm_map_GK]) ?_)
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 (by rwa [norm_neg]))
  have hfix : ∀ i, σ.1 (o i) = o i := fun i => (how i).2.1 (σ.1.restrictScalars ℚ_[l]) hσ hine
  have e : σ • (∑ i, o i * j (w i)) - ∑ i, o i * j (w i) = ∑ i, o i * (j (res j σ.1 (w i)) - j (w i)) := by
    show σ.1 _ - _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hfix, res_spec]; ring
  rw [e]
  exact hyp _ σ.2.1 σ.2.2

theorem exists_kumVal {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {m : ℕ} {ζ u v : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hu : u ≠ 0) (hv : v ^ (l ^ m) = u) {s : G ℚ Ω} (hs : s u = u) :
    ∃ k : ZMod (l ^ m), s v = ζ ^ k.val * v := by
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have h1 : (s v / v) ^ (l ^ m) = 1 := by rw [div_pow, ← map_pow, hv, hs, div_self hu]
  obtain ⟨k, hk, e⟩ := hζ.eq_pow_of_pow_eq_one h1
  exact ⟨(k : ZMod (l ^ m)), by rw [ZMod.val_cast_of_lt hk, e]; field_simp⟩

theorem kumVal_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {m c₀ : ℕ} (hc : c₀ ≤ m) {ζ u : Ω}
    (hζ : IsPrimitiveRoot (ζ ^ l ^ c₀) (l ^ (m - c₀))) (hu : u ≠ 0) {s : G ℚ Ω} (hs : s ζ = ζ) {k : ZMod (l ^ m)}
    {k' : ZMod (l ^ (m - c₀))} (hk : GlobalTheory.Col.KumVal m ζ u s k) (hk' : GlobalTheory.Col.KumVal (m - c₀) (ζ ^ l ^ c₀) u s k') :
    (k'.val : Qbar l) - k.val ∈ ball ((l : Qbar l) ^ (m - c₀)) := by
  obtain ⟨v, hv, hsv⟩ := hk
  have h1 : GlobalTheory.Col.KumVal (m - c₀) (ζ ^ l ^ c₀) u s ((k.val : ℕ) : ZMod (l ^ (m - c₀))) := by
    refine ⟨v ^ l ^ c₀, by rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hc, hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm k.val]
  have h2 := GlobalTheory.Col.kumVal_unique hζ (by rw [map_pow, hs]) hu hk' h1
  have h3 : (k.val : Qbar l) = k'.val + ((k.val / l ^ (m - c₀) : ℕ) : Qbar l) * (l : Qbar l) ^ (m - c₀) := by
    rw [h2, ZMod.val_natCast]
    exact_mod_cast congrArg (Nat.cast : ℕ → Qbar l) (Nat.mod_add_div' k.val (l ^ (m - c₀))).symm
  rw [h3, sub_add_cancel_left]
  exact neg_mem (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one _ _) (mem_ball.2 le_rfl))

theorem htv_coeff : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (cf : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∀ (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ), c₀ ≤ m →
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x, Z m (s * t) x = Z m s x + (ν s : Qbar l) * Z m t (x * (cycMod ℚ Ω l m s)⁻¹)) →
  ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A cf m c₀ Z ζ P o →
  ∀ y : (ZMod (l ^ m))ˣ, ∃ x : ι → Ω, (∀ i, x i ∈ A) ∧ ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
    Cg (m - c₀) ((l : Qbar l) ^ c * Z m s y)
      ((l : Qbar l) ^ c * htv j ζ P o (y : ZMod (l ^ m)).val * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o i * (j (s (x i)) - j (x i))) := by
  intro l _ hl2
  obtain ⟨c, hc⟩ := GlobalTheory.RecConj.recip_conj l hl2
  refine ⟨c, ?_⟩
  intro Ω _ _ _ A cf j hA hj ν Z m c₀ hm hν hZ ζ ι _ P o hP y
  have hj' : Compat l A j := hj
  have hp1 := norm_natCast_lt_one (l := l)
  have hpc : ‖(l : Qbar l) ^ c‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  obtain ⟨hζ, hco, -, hP0, hζ0, -, hu, ho, hK⟩ := hP
  obtain ⟨⟨τ, hτ⟩, hτy⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A (valuation_lt_one hj') m y⁻¹
  have hτy' : cycMod ℚ Ω l m τ = y⁻¹ := hτy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ', hζ'⟩ := IsAlgClosed.exists_pow_nat_eq ζ hpos
  choose x hxA hgA hx using fun i => hc Ω A hA m ζ ζ' hζ hζ' (P i) (hco i) (hu i).1 (hu i).2.2 (hP0 i) τ y hτ hτy'
  refine ⟨x, hxA, fun s hs hs1 => ?_⟩
  have hs' : τ * s * τ⁻¹ ∈ Ine (F := ℚ) A := mul_mem (mul_mem hτ hs) (inv_mem hτ)
  have hs1' : cycMod ℚ Ω l m (τ * s * τ⁻¹) = 1 := by rw [map_mul, map_mul, hs1, map_inv, mul_one, mul_inv_cancel]
  have hfix : ∀ {g : G ℚ Ω}, cycMod ℚ Ω l m g = 1 → g ζ = ζ := fun hg => by
    haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
      haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
      inferInstance
    exact GlobalTheory.Col.fix_of_cycMod le_rfl hg hζ.pow_eq_one
  have hconj : Z m (τ * s * τ⁻¹) 1 = Z m s y := by
    have h1 := hZ τ (Ine_le_Dec A hτ) s (Ine_le_Dec A hs) 1
    have h2 := hZ _ (Ine_le_Dec A hs') τ (Ine_le_Dec A hτ) 1
    rw [hν τ hτ, hτy', inv_inv, one_mul, Units.val_one, one_mul] at h1
    rw [hν _ hs', hs1', inv_one, one_mul, Units.val_one, one_mul, inv_mul_cancel_right, h1, add_comm] at h2
    exact (add_right_cancel h2).symm
  obtain ⟨k', hk', hZk⟩ := hK _ hs' hs1' (by rw [map_pow, hfix hs1'])
  rw [hconj] at hZk
  have hPfix : ∀ i, (τ * s * τ⁻¹) ((P i).eval ζ) = (P i).eval ζ := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, hfix hs1']
    by_cases h : (P i).coeff n = 0
    · rw [h, map_zero]
    · rw [(hco i _ (Polynomial.coeff_mem_coeffs h)).2 _ hs']
  have hk : ∀ i, ∃ k : ZMod (l ^ m), GlobalTheory.Col.KumVal m ζ ((P i).eval ζ) (τ * s * τ⁻¹) k := by
    intro i
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((P i).eval ζ) hpos
    obtain ⟨k, hk⟩ := exists_kumVal hζ (hP0 i) hv (hPfix i)
    exact ⟨k, v, hv, hk⟩
  choose k hk using hk
  obtain ⟨t, ht⟩ := exists_kumVal hζ (hζ.ne_zero hpos.ne') hζ' (hfix hs1)
  have hlam : (t.val : Qbar l) - lamv l m s ∈ ball ((l : Qbar l) ^ m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact sub_mem (by simpa [mem_ball] using IsUltrametricDist.norm_natCast_le_one (Qbar l) t.val)
        (by simpa [mem_ball] using norm_lamv_le_one hs1)
    · have hprim : IsPrimitiveRoot ζ' (l ^ (m + m)) := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        have h1 : ¬ ζ' ^ l ^ (n + 1 + n) = 1 := by
          rw [pow_add l (n + 1) n, pow_mul, hζ']
          exact hζ.pow_ne_one_of_pos_of_lt (pow_pos (Fact.out : l.Prime).pos n).ne'
            (Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n))
        have h2 : ζ' ^ l ^ (n + 1 + n + 1) = 1 := by
          rw [add_assoc (n + 1), pow_add l (n + 1) (n + 1), pow_mul, hζ', hζ.pow_eq_one]
        have h3 := orderOf_eq_prime_pow h1 h2
        rw [show n + 1 + (n + 1) = n + 1 + n + 1 from rfl, ← h3]
        exact IsPrimitiveRoot.orderOf ζ'
      exact kummer_sub_lamv hprim hs1 (by rw [hζ']; exact ht)
  have hterm : ∀ i, (l : Qbar l) ^ c * (o i * ((k' i).val : Qbar l)) -
      ((l : Qbar l) ^ c * (o i * j (ζ ^ (y : ZMod (l ^ m)).val * (Polynomial.derivative (P i)).eval (ζ ^ (y : ZMod (l ^ m)).val) /
        (P i).eval (ζ ^ (y : ZMod (l ^ m)).val))) * lamv l m s + o i * (j (s (x i)) - j (x i))) ∈
      ball ((l : Qbar l) ^ (m - c₀)) := by
    intro i
    have h1 := kumVal_sub_mem hm hζ0 (hP0 i) (hfix hs1') (hk i) (hk' i)
    have h2 := (cgA_iff hj' _ _ _).1 (hx i s hs hs1 _ t (hk i) ht)
    have h3 := (hj _).1 (hgA i)
    generalize ζ ^ (y : ZMod (l ^ m)).val * (Polynomial.derivative (P i)).eval (ζ ^ (y : ZMod (l ^ m)).val) /
        (P i).eval (ζ ^ (y : ZMod (l ^ m)).val) = g at h2 h3 ⊢
    simp only [map_mul, map_add (f := _), map_sub, map_pow, map_natCast] at h2
    have h4 := mul_mem_ball (ho i) (add_mem (add_mem (mul_mem_ball hpc h1) (ball_pow_mono hp1 (Nat.sub_le m c₀) h2))
      (mul_mem_ball hpc (mul_mem_ball h3 (ball_pow_mono hp1 (Nat.sub_le m c₀) hlam))))
    convert h4 using 1
    ring
  have h5 := add_mem (mul_mem_ball hpc (mem_ball.2 hZk)) (sum_mem fun i (_ : i ∈ Finset.univ) => hterm i)
  refine mem_ball.1 ?_
  convert h5 using 1
  rw [htv, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem localGlue : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∃ c₁ : ℕ, ∀ (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ), c₀ + c₁ ≤ m →
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x, Z m (s * t) x = Z m s x + (ν s : Qbar l) * Z m t (x * (cycMod ℚ Ω l m s)⁻¹)) →
  ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (h : (ZMod (l ^ m))ˣ → Qbar l),
    HTPresNuOfPolys A c m c₀ Z ζ P o → (∀ y, GlobalTheory.LambdaValuationPowers.HTCoL A c j Z m c₀ y (h y)) →
    ∀ y : (ZMod (l ^ m))ˣ, Cg (m - c₀ - c₁) (htv j ζ P o (y : ZMod (l ^ m)).val) (h y) := by
  intro l _ hl Ω _ _ _ A c j hA hj
  obtain ⟨cA, hcA⟩ := htv_coeff l hl
  obtain ⟨c₂, hc₂⟩ := uniq_fix l hl Ω A c j hA hj
  refine ⟨cA + c₂, ?_⟩
  intro ν Z m c₀ hm hν hZ ζ ι _ P o h hP hh y
  obtain ⟨x, hxA, hx⟩ := hcA Ω A c j hA hj ν Z m c₀ (by omega) hν hZ ζ ι P o hP y
  obtain ⟨q, o', w', ho', hw'⟩ := hh y
  have hl0 : (l : Qbar l) ≠ 0 := GlobalTheory.LambdaValuationPowers.natCast_ne_zero
  have hl1 : ‖(l : Qbar l)‖ < 1 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one
  have hlpos : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 hl0
  set H := htv j ζ P o (y : ZMod (l ^ m)).val with hH
  let e := Fintype.equivFin ι
  let n := Fintype.card ι
  let o'' : Fin (q + n) → Qbar l :=
    Fin.append (fun i => (l : Qbar l) ^ cA * o' i) (fun i => -((l : Qbar l) ^ c₀ * o (e.symm i)))
  let w'' : Fin (q + n) → Ω := Fin.append w' (fun i => x (e.symm i))
  have hsum : ∀ s : G ℚ Ω, ∑ i, o'' i * (j (s (w'' i)) - j (w'' i)) =
      (l : Qbar l) ^ cA * ∑ i, o' i * (j (s (w' i)) - j (w' i)) -
        (l : Qbar l) ^ c₀ * ∑ i, o i * (j (s (x i)) - j (x i)) := by
    intro s
    rw [Fin.sum_univ_add]
    simp only [o'', w'', Fin.append_left, Fin.append_right]
    rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [← e.symm.sum_comp (fun i => -((l : Qbar l) ^ c₀ * (o i * (j (s (x i)) - j (x i)))))]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hoi : ∀ i, o i ∈ c.O := hP.2.2.1
  have hB : ∀ i, ‖o'' i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (o'' i) ∧ ‖j (w'' i)‖ ≤ 1 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [o'', w'', Fin.append_left]
      obtain ⟨h1, h2, h3⟩ := ho' i
      refine ⟨?_, fun σ hσ hσ' => ?_, h3⟩
      · rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _) h1
      · rw [map_mul, map_pow, map_natCast, h2 σ hσ hσ']
    · simp only [o'', w'', Fin.append_right]
      refine ⟨?_, fun σ hσ _ => ?_, (hj _).1 (hxA _)⟩
      · rw [norm_neg, norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hoi _))
      · rw [map_neg, map_mul, map_pow, map_natCast, hσ _ (hoi _)]
  have key := hc₂ m ((l : Qbar l) ^ (cA + c₀) * (H - h y)) (q + n) o'' w'' hB (by
    intro s hs hs1
    rw [hsum s]
    have h1 := hx s hs hs1
    have h2 := hw' s hs hs1
    unfold Cg at h1 h2 ⊢
    have e1 : (l : Qbar l) ^ (cA + c₀) * (H - h y) * GlobalTheory.LambdaValuationPowers.lamv l m s -
        ((l : Qbar l) ^ cA * ∑ i, o' i * (j (s (w' i)) - j (w' i)) -
          (l : Qbar l) ^ c₀ * ∑ i, o i * (j (s (x i)) - j (x i))) =
        (-(l : Qbar l) ^ c₀) * ((l : Qbar l) ^ cA * Z m s y -
          ((l : Qbar l) ^ cA * H * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o i * (j (s (x i)) - j (x i)))) +
        (l : Qbar l) ^ cA * ((l : Qbar l) ^ c₀ * Z m s y -
          ((l : Qbar l) ^ c₀ * h y * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o' i * (j (s (w' i)) - j (w' i)))) := by
      ring
    rw [e1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_neg, norm_pow, norm_pow]
      calc ‖(l : Qbar l)‖ ^ c₀ * ‖_‖ ≤ ‖(l : Qbar l)‖ ^ c₀ * ‖(l : Qbar l)‖ ^ (m - c₀) :=
            mul_le_mul_of_nonneg_left (by simpa [norm_pow] using h1) (by positivity)
        _ = ‖(l : Qbar l)‖ ^ m := by rw [← pow_add]; congr 1; omega
    · rw [norm_mul, norm_pow, norm_pow]
      calc ‖(l : Qbar l)‖ ^ cA * ‖_‖ ≤ 1 * ‖(l : Qbar l)‖ ^ m :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hl1.le) (by simpa [norm_pow] using h2) (norm_nonneg _) zero_le_one
        _ = ‖(l : Qbar l)‖ ^ m := one_mul _)
  unfold Cg at key ⊢
  rw [sub_zero, norm_mul, norm_pow, norm_pow] at key
  rw [norm_pow]
  have e2 : ‖(l : Qbar l)‖ ^ (m - c₂) = ‖(l : Qbar l)‖ ^ (cA + c₀) * ‖(l : Qbar l)‖ ^ (m - c₀ - (cA + c₂)) := by
    rw [← pow_add]; congr 1; omega
  rw [e2] at key
  exact le_of_mul_le_mul_left key (pow_pos hlpos _)

end GlobalTheory.LambdaValuationPowers.LocGlue
