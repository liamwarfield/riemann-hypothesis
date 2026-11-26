module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteField
open GlobalTheory.Cong

namespace GlobalTheory

theorem exists_matrix_no_invariant_subspace :
    ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ,
      ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro κ _ _ a ha
  obtain ⟨p, hp⟩ := CharP.exists κ
  haveI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩
  haveI : NeZero a := ⟨by omega⟩
  let L := FiniteField.Extension κ p a
  let b : Module.Basis (Fin a) κ L :=
    Module.finBasisOfFinrankEq κ L (FiniteField.finrank_extension κ p a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Lˣ)
  let β : L := (g : L)
  refine ⟨LinearMap.toMatrix b b (Algebra.lmul κ L β), fun W hW => ?_⟩

  let e := b.equivFun
  have key : ∀ x : L, (LinearMap.toMatrix b b (Algebra.lmul κ L β)).mulVec (e x) = e (β * x) := by
    intro x
    simpa [e, Module.Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul κ L β) x

  have stepβ : ∀ x : L, e x ∈ W → e (β * x) ∈ W := fun x hx => key x ▸ hW _ hx
  have stepPow : ∀ n : ℕ, ∀ x : L, e x ∈ W → e (β ^ n * x) ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := stepβ _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have stepAll : ∀ y x : L, e x ∈ W → e (y * x) ∈ W := by
    intro y x hx
    by_cases hy : y = 0
    · subst hy; simpa using W.zero_mem
    · obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 y hy))
      have : β ^ n = y := by
        have := congrArg (fun u : Lˣ => (u : L)) hn
        simpa [β] using this
      rw [← this]; exact stepPow n x hx
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hx0 : e.symm v ≠ 0 := by
      intro h0; apply hv0; simpa using congrArg e h0
    have hxW : e (e.symm v) ∈ W := by simpa using hvW
    rw [eq_top_iff]
    intro u _
    have := stepAll (e.symm u * (e.symm v)⁻¹) (e.symm v) hxW
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteFieldStatement
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_no_invariant_subspace_finite_field : ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ, ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  first | exact @GlobalTheory.exists_matrix_no_invariant_subspace | exact GlobalTheory.exists_matrix_no_invariant_subspace | (intros; apply GlobalTheory.exists_matrix_no_invariant_subspace; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongruenceKernelTraceCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongruenceKernelTraceCharacter
open GlobalTheory.Cong

namespace GlobalTheory.CongChar

variable {R : Type} [CommRing R] [IsDomain R] {a : ℕ} {c : R}

theorem exists_eq_one_add_smul
    (g : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker) :
    ∃ x : Matrix (Fin a) (Fin a) R, (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x := by
  have hg := g.2
  rw [MonoidHom.mem_ker] at hg
  have h : ∀ i j, (g.1 : Matrix (Fin a) (Fin a) R) i j - (1 : Matrix (Fin a) (Fin a) R) i j
      ∈ Ideal.span {c} := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun M : GL (Fin a) (R ⧸ Ideal.span {c}) => M.1 i j) hg
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  choose x hx using fun i j => Ideal.mem_span_singleton'.1 (h i j)
  refine ⟨Matrix.of x, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination (-1 : R) * hx i j

theorem smul_injective (hc : c ≠ 0) {x y : Matrix (Fin a) (Fin a) R}
    (h : (1 : Matrix (Fin a) (Fin a) R) + c • x = 1 + c • y) : x = y := by
  have h' : c • x = c • y := add_left_cancel h
  ext i j
  have := congrArg (fun M => M i j) h'
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

variable {A : Type} [AddCommGroup A]

theorem one_add_smul_mul (x y : Matrix (Fin a) (Fin a) R) :
    ((1 : Matrix (Fin a) (Fin a) R) + c • x) * (1 + c • y) = 1 + c • (x + y + c • (x * y)) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  abel

noncomputable def congChar (hc : c ≠ 0) (φ : R →+ A) (hφ : ∀ x, φ (c * x) = 0)
    (B : Matrix (Fin a) (Fin a) R) :
    (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →*
      Multiplicative A :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (φ (B * Classical.choose (exists_eq_one_add_smul g)).trace))
    (by
      intro g h
      have hg := Classical.choose_spec (exists_eq_one_add_smul g)
      have hh := Classical.choose_spec (exists_eq_one_add_smul h)
      have hgh := Classical.choose_spec (exists_eq_one_add_smul (g * h))
      set x := Classical.choose (exists_eq_one_add_smul g)
      set y := Classical.choose (exists_eq_one_add_smul h)
      set z := Classical.choose (exists_eq_one_add_smul (g * h))
      have hz : z = x + y + c • (x * y) := by
        apply smul_injective hc
        rw [← hgh, ← one_add_smul_mul, ← hg, ← hh]
        rfl
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
      rw [← ofAdd_add, hz]
      congr 1
      rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, map_add (f := _), map_add (f := _),
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hφ, add_zero])

theorem congChar_apply (hc : c ≠ 0) (φ : R →+ A) (hφ : ∀ x, φ (c * x) = 0)
    (B : Matrix (Fin a) (Fin a) R) (g) (x : Matrix (Fin a) (Fin a) R)
    (hx : (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x) :
    congChar hc φ hφ B g = Multiplicative.ofAdd (φ (B * x).trace) := by
  have hs := Classical.choose_spec (exists_eq_one_add_smul g)
  have : Classical.choose (exists_eq_one_add_smul g) = x := smul_injective hc (hs.symm.trans hx)
  simp only [congChar, MonoidHom.mk'_apply, this]

end GlobalTheory.CongChar

namespace GlobalTheory

theorem congChar_exists : ∀ (R A : Type) [CommRing R] [IsDomain R] [AddCommGroup A] (a : ℕ) (c : R), c ≠ 0 → ∀ (φ : R →+ A), (∀ x, φ (c * x) = 0) → ∀ B : Matrix (Fin a) (Fin a) R, ∃ lam : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →* Multiplicative A, ∀ g (x : Matrix (Fin a) (Fin a) R), (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x → lam g = Multiplicative.ofAdd (φ (B * x).trace) := by
  intro R A _ _ _ a c hc φ hφ B
  exact ⟨CongChar.congChar hc φ hφ B, fun g x hx => CongChar.congChar_apply hc φ hφ B g x hx⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongruenceKernelTraceCharacterStatement
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceKernel_trace_character : ∀ (R A : Type) [CommRing R] [IsDomain R] [AddCommGroup A] (a : ℕ) (c : R), c ≠ 0 → ∀ (φ : R →+ A), (∀ x, φ (c * x) = 0) → ∀ B : Matrix (Fin a) (Fin a) R, ∃ lam : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →* Multiplicative A, ∀ g (x : Matrix (Fin a) (Fin a) R), (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x → lam g = Multiplicative.ofAdd (φ (B * x).trace) := by
  first | exact @GlobalTheory.congChar_exists | exact GlobalTheory.congChar_exists | (intros; apply GlobalTheory.congChar_exists; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddHomZmodPrimePowOneOfNotIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddHomZmodPrimePowOneOfNotIsUnit
open GlobalTheory.Cong

namespace GlobalTheory

theorem natCast_dvd_of_pow_dvd_of_not_isUnit (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    (l : ℕ) (hl : l.Prime) (hu : ¬ IsUnit (l : R)) :
    ∀ (m k : ℕ), (l : R) ^ m ∣ (k : R) → l ^ m ∣ k := by
  intro m
  induction m with
  | zero => intro k _; simp
  | succ m ih =>
    intro k hk
    have h1 : (l : R) ∣ (k : R) := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans hk
    have h2 : l ∣ k := by
      by_contra hnd
      have hcop : Nat.Coprime l k := (Nat.Prime.coprime_iff_not_dvd hl).2 hnd
      have hg := Nat.gcd_eq_gcd_ab l k
      rw [hcop] at hg
      apply hu
      obtain ⟨c, hc⟩ := h1
      refine isUnit_of_dvd_one ⟨(Nat.gcdA l k : R) + (Nat.gcdB l k : R) * c, ?_⟩
      have := congrArg (fun z : ℤ => (z : R)) hg
      simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
      rw [this, hc]; ring
    obtain ⟨k', rfl⟩ := h2
    have hl0 : (l : R) ≠ 0 := by exact_mod_cast hl.ne_zero
    have hk' : (l : R) ^ m ∣ (k' : R) := by
      obtain ⟨c, hc⟩ := hk
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hl0
      rw [Nat.cast_mul] at hc
      rw [hc]; ring
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left l (ih k' hk')

theorem exists_addHom_zmod_pow_one_of_not_isUnit :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l m : ℕ), l.Prime → ¬ IsUnit (l : R) →
      ∃ φ : R →+ ZMod (l ^ m), φ 1 = 1 ∧ ∀ x, φ ((l : R) ^ m * x) = 0 := by
  intro R _ _ _ l m hl hu
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set I : Ideal R := Ideal.span {(l : R) ^ m} with hI
  have hlI : (((l ^ m : ℕ) : ℤ) : R ⧸ I) = 0 := by
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem,
      hI, Nat.cast_pow]
    exact Ideal.subset_span rfl
  let f : ZMod (l ^ m) →+ R ⧸ I := ZMod.lift (l ^ m) ⟨Int.castAddHom (R ⧸ I), by
    simpa using hlI⟩
  have hf_nat : ∀ k : ℕ, f (k : ZMod (l ^ m)) = (k : R ⧸ I) := by
    intro k
    have := ZMod.lift_coe (l ^ m) ⟨Int.castAddHom (R ⧸ I), by simpa using hlI⟩ (k : ℤ)
    simpa using this
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← ZMod.natCast_zmod_val x, hf_nat, ← map_natCast (Ideal.Quotient.mk I),
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at hx
    have hd := natCast_dvd_of_pow_dvd_of_not_isUnit R l hl hu m _ hx
    have hlt := ZMod.val_lt x
    have h0 : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    rw [← ZMod.natCast_zmod_val x, h0, Nat.cast_zero]
  obtain ⟨Λ, hΛ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    f hinj (ZMod.toAddCircle (N := l ^ m))
  have hΛ' : ∀ z, Λ (f z) = ZMod.toAddCircle z := fun z => DFunLike.congr_fun hΛ z
  have htor : ∀ q : R ⧸ I, ∃ k : ZMod (l ^ m), ZMod.toAddCircle k = Λ q := by
    intro q
    have h0 : (l ^ m) • Λ q = 0 := by
      rw [← map_nsmul]
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I), ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2, map_zero]
      rw [hI, Ideal.mem_span_singleton, Nat.cast_pow]
      exact dvd_mul_right _ _
    obtain ⟨k, -, hk⟩ := (AddCircle.nsmul_eq_zero_iff (pow_pos hl.pos _)).1 h0
    refine ⟨k, ?_⟩
    rw [ZMod.toAddCircle_natCast, ← hk, mul_one]
  choose a ha using htor
  let A : R ⧸ I →+ ZMod (l ^ m) := AddMonoidHom.mk' a (by
    intro x y
    apply ZMod.toAddCircle_injective
    rw [map_add (f := _), ha, ha, ha, map_add (f := _)])
  refine ⟨A.comp (Ideal.Quotient.mk I).toAddMonoidHom, ?_, ?_⟩
  · show a (Ideal.Quotient.mk I 1) = 1
    apply ZMod.toAddCircle_injective
    rw [ha, map_one]
    have := hΛ' 1
    rw [show (1 : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) by simp, hf_nat] at this
    simpa using this
  · intro x
    show a (Ideal.Quotient.mk I ((l : R) ^ m * x)) = 0
    have hmem : (l : R) ^ m * x ∈ I := by
      rw [hI]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem]
    apply ZMod.toAddCircle_injective
    rw [ha, map_zero, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddHomZmodPrimePowOneOfNotIsUnitStatement
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHom_zmod_prime_pow_one_of_not_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l m : ℕ), l.Prime → ¬ IsUnit (l : R) → ∃ φ : R →+ ZMod (l ^ m), φ 1 = 1 ∧ ∀ x, φ ((l : R) ^ m * x) = 0 := by
  first | exact @GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit | exact GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit | (intros; apply GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFree
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFree
open GlobalTheory.Cong

namespace GlobalTheory.CongTorsion

open Finset

variable {R : Type} [CommRing R] {a : ℕ}

lemma one_add_smul_pow (t : R) (z : Matrix (Fin a) (Fin a) R) (n : ℕ) :
    (1 + t • z) ^ n = 1 + t • ∑ m ∈ range n, t ^ m • ((n.choose (m + 1)) • z ^ (m + 1)) := by
  rw [add_comm, (Commute.one_right (t • z)).add_pow, sum_range_succ', add_comm]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  congr 1
  rw [smul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [← nsmul_eq_mul', smul_pow, smul_smul, ← pow_succ', smul_comm]

lemma dvd_entries_of_pow_eq_one [IsDomain R] [IsLocalRing R] [CharZero R] {l p : ℕ} (hl : l.Prime)
    (hlu : ¬ IsUnit (l : R)) (hp : p.Prime) {t : R} (ht : (l : R) ^ 2 ∣ t) (ht0 : t ≠ 0)
    {z : Matrix (Fin a) (Fin a) R} (hz : (1 + t • z) ^ p = 1) (i j : Fin a) : (l : R) ∣ z i j := by
  have h := one_add_smul_pow t z p
  rw [hz] at h
  have hS : t • ∑ m ∈ range p, t ^ m • ((p.choose (m + 1)) • z ^ (m + 1)) = 0 := by
    have := congrArg (fun A => A - 1) h
    simpa using this.symm
  rw [smul_eq_zero] at hS
  have hS := hS.resolve_left ht0
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [sum_range_succ'] at hS
  have he := congrFun (congrFun hS i) j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    pow_zero, one_smul, zero_add, Nat.choose_one_right, pow_one, Matrix.zero_apply] at he
  simp only [nsmul_eq_mul] at he
  have hdiv : (l : R) ^ 2 ∣ ((q + 1 : ℕ) : R) * z i j := by
    have : ((q + 1 : ℕ) : R) * z i j = -(∑ m ∈ range q, t ^ (m + 1) *
        (((q + 1).choose (m + 1 + 1) : R) * (z ^ (m + 1 + 1)) i j)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact he
    rw [this, dvd_neg]
    exact dvd_sum fun m _ => dvd_mul_of_dvd_left (ht.trans (dvd_pow_self t (Nat.succ_ne_zero m))) _
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  by_cases hpl : q + 1 = l
  · rw [hpl, pow_two] at hdiv
    exact (mul_dvd_mul_iff_left hl0).mp hdiv
  · have hcop : Nat.Coprime (q + 1) l := (Nat.coprime_primes hp hl).mpr hpl
    have hc : IsCoprime ((q + 1 : ℕ) : R) (l : R) := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom R)
      simpa using this
    obtain ⟨u, v, huv⟩ := hc
    have hpu : IsUnit ((q + 1 : ℕ) : R) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one huv with h1 | h1
      · exact isUnit_of_mul_isUnit_right h1
      · exact absurd (isUnit_of_mul_isUnit_right h1) hlu
    exact (dvd_pow_self (l : R) two_ne_zero).trans ((hpu.dvd_mul_left).mp hdiv)

lemma pow_dvd_entries_of_pow_eq_one [IsDomain R] [IsLocalRing R] [CharZero R] {l p : ℕ}
    (hl : l.Prime) (hlu : ¬ IsUnit (l : R)) (hp : p.Prime) (N : ℕ) :
    ∀ (t : R) (z : Matrix (Fin a) (Fin a) R), (l : R) ^ 2 ∣ t → t ≠ 0 → (1 + t • z) ^ p = 1 →
      ∀ i j, (l : R) ^ N ∣ z i j := by
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  induction N with
  | zero => intro t z _ _ _ i j; simp
  | succ N ih =>
    intro t z ht ht0 hz i j
    have hd := dvd_entries_of_pow_eq_one hl hlu hp ht ht0 hz
    choose w hw using hd
    have hzz : z = (l : R) • Matrix.of w := by ext i j; simp [hw i j]
    have htz : t • z = (t * l) • Matrix.of w := by rw [hzz, smul_smul]
    have h' := ih (t * l) (Matrix.of w) (dvd_mul_of_dvd_left ht _) (mul_ne_zero ht0 hl0)
      (by rw [← htz]; exact hz) i j
    rw [hw i j, pow_succ']
    exact mul_dvd_mul_left _ (by simpa using h')

lemma eq_zero_of_forall_pow_dvd [IsDomain R] [IsDiscreteValuationRing R] {c b : R}
    (hc : ¬ IsUnit c) (h : ∀ N, c ^ N ∣ b) : b = 0 := by
  by_contra hb
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hc hb
  exact hn (h _)

end GlobalTheory.CongTorsion

namespace GlobalTheory


open GlobalTheory.CongTorsion in
theorem principalCongruence_torsionFree :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (l m a : ℕ),
      l.Prime → ¬ IsUnit (l : R) → 2 ≤ m → ∀ (x : Matrix (Fin a) (Fin a) R) (n : ℕ), 0 < n →
        (1 + ((l : R) ^ m) • x) ^ n = 1 → x = 0 := by
  intro R _ _ _ _ l m a hl hlu hm x n hn hx
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hc0 : (l : R) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hc2 : (l : R) ^ 2 ∣ (l : R) ^ m := pow_dvd_pow _ hm
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      rw [pow_one, add_eq_left, smul_eq_zero] at hx
      exact hx.resolve_left hc0
    · set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      have hklt : k < n := by
        rw [hk]; exact lt_mul_left hkpos hp.one_lt
      have he := one_add_smul_pow ((l : R) ^ m) x p
      rw [hk, pow_mul, he] at hx
      have hx' := ih k hklt _ hkpos hx
      rw [hx', smul_zero, add_zero] at he
      ext i j
      exact eq_zero_of_forall_pow_dvd hlu
        (fun N => pow_dvd_entries_of_pow_eq_one hl hlu hp N _ x hc2 hc0 he i j)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFreeStatement
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_prime_pow_torsionFree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (l m a : ℕ), l.Prime → ¬ IsUnit (l : R) → 2 ≤ m → ∀ (x : Matrix (Fin a) (Fin a) R) (n : ℕ), 0 < n → (1 + ((l : R) ^ m) • x) ^ n = 1 → x = 0 := by
  first | exact @GlobalTheory.principalCongruence_torsionFree | exact GlobalTheory.principalCongruence_torsionFree | (intros; apply GlobalTheory.principalCongruence_torsionFree; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroup
namespace GlobalTheory.LocFinSemisimple

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem exists_isAtom_le : ∀ (n : ℕ) (Y : Subrepresentation ρ),
    FiniteDimensional ℂ Y.toSubmodule → Module.finrank ℂ Y.toSubmodule = n → Y ≠ ⊥ →
      ∃ T : Subrepresentation ρ, IsAtom T ∧ T ≤ Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY hn hne
    by_cases hA : IsAtom Y
    · exact ⟨Y, hA, le_rfl⟩
    · have : ∃ Z, Z < Y ∧ Z ≠ ⊥ := by
        by_contra hc
        push_neg at hc
        exact hA ⟨hne, hc⟩
      obtain ⟨Z, hZY, hZ⟩ := this
      have hlt : Z.toSubmodule < Y.toSubmodule :=
        lt_of_le_of_ne hZY.le fun h => hZY.ne (Subrepresentation.toSubmodule_injective h)
      have hZf : FiniteDimensional ℂ Z.toSubmodule := Submodule.finiteDimensional_of_le hlt.le
      have hr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT, hTZ⟩ := ih _ (hn ▸ hr) Z hZf rfl hZ
      exact ⟨T, hT, hTZ.trans hZY.le⟩

def ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U) : Subrepresentation ρ :=
  ⟨U, fun k _ hu => hU k _ hu⟩

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

theorem isSemisimple_ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U)
    (hfd : FiniteDimensional ℂ U)
    (hc : ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) :
    (ofInvariant U hU).toRepresentation.IsSemisimpleRepresentation := by
  haveI : FiniteDimensional ℂ (ofInvariant U hU).toSubmodule := hfd
  refine GlobalTheory.isSemisimpleRepresentation_of_continuous_coeff _ fun l v => ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := U) l
  have h : ∀ k, l ((ofInvariant U hU).toRepresentation k v) = g (ρ k v) := fun k => by
    rw [← hg]; rfl
  simp only [h]
  exact hc g v v.2

theorem le_iSup_atoms
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef
  have hNX : N ≤ X.toSubmodule := iSup₂_le fun S hS => hS.2
  have hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N := by
    intro k
    have : N ≤ N.comap (ρ k) := iSup₂_le fun S hS x hx =>
      (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun x hx => this hx
  intro x hxX
  obtain ⟨U, hxU, hfd, hU, hc⟩ := H x
  let R := ofInvariant U hU
  haveI : ComplementedLattice (Subrepresentation R.toRepresentation) :=
    isSemisimple_ofInvariant U hU hfd hc
  let W : Subrepresentation R.toRepresentation :=
    ⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩
  obtain ⟨W', hW'⟩ := exists_isCompl W
  have hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
  let Xc : Submodule ℂ U := X.toSubmodule.comap U.subtype
  let Y : Subrepresentation ρ := ⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by
    rintro k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1,
      X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩
  have hY : Y = ⊥ := by
    by_contra hne
    haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le
      (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)
    obtain ⟨T, hT, hTY⟩ := exists_isAtom_le _ Y this rfl hne
    have hTX : T ≤ X := by
      intro t ht
      obtain ⟨u, ⟨_, hu2⟩, rfl⟩ := hTY ht
      exact hu2
    have hTN : T.toSubmodule ≤ N :=
      le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨u, ⟨hu1, _⟩, rfl⟩ := hTY ht
    have hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule := ⟨hTN ht, hu1⟩
    rw [hdis] at hu
    have hu0 : ((u : R.toSubmodule) : V) = 0 :=
      congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)
    exact ht0 hu0
  have hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', hww⟩ := Submodule.mem_sup.1 hx'
  have hsum : (w : V) + (w' : V) = x := congrArg Subtype.val hww
  have hw'X : w' ∈ Xc := by
    have h1 : (w : V) ∈ X.toSubmodule := hNX hw
    have h2 : (w' : V) = x - w := by
      rw [← hsum]; abel
    show (w' : V) ∈ X.toSubmodule
    rw [h2]
    exact X.toSubmodule.sub_mem hxX h1
  have hw'0 : (w' : V) ∈ Y.toSubmodule := ⟨w', ⟨hw', hw'X⟩, rfl⟩
  rw [hY] at hw'0
  have : (w' : V) = 0 := (Submodule.mem_bot ℂ).1 hw'0
  have hxw : x = w := by
    rw [← hsum, ‹(w' : V) = 0›, add_zero]
  rw [hxw]
  exact hw

theorem semisimple_of_locallyFinite : ∀ (K V : Type) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) →
    ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S →
      FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ,
        X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  intro K V _ _ _ _ _ _ ρ H
  have hle := le_iSup_atoms H
  refine ⟨?_, ?_, fun X => le_antisymm (hle X) (iSup₂_le fun S hS => hS.2)⟩
  · rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
      ← sSup_simples_eq_top_iff_isSemisimpleModule]
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
    set s := sSup {m : Submodule (MonoidAlgebra ℂ K) ρ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ K) m} with hs
    have hZ : (e.symm s).toSubmodule = ⊤ := by
      refine eq_top_iff.2 ((hle ⊤).trans (iSup₂_le fun S hS => ?_))
      have : S ≤ e.symm s := e.le_symm_apply.2
        (le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff S).2 hS.1)))
      exact this
    have h1 : e.symm s = ⊤ := Subrepresentation.toSubmodule_injective hZ
    rw [← e.apply_symm_apply s, h1, e.map_top]
  · intro S hS
    have hS0 : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    obtain ⟨U, hvU, hfd, hU, -⟩ := H v
    rcases hS.le_iff.1 (inf_le_left : S ⊓ ofInvariant U hU ≤ S) with h | h
    · have hm : v ∈ (S ⊓ ofInvariant U hU).toSubmodule := ⟨hv, hvU⟩
      rw [h] at hm
      exact absurd ((Submodule.mem_bot ℂ).1 hm) hv0
    · have hSU : S.toSubmodule ≤ U := by
        rw [← h]; exact fun x hx => hx.2
      exact Submodule.finiteDimensional_of_le hSU

end GlobalTheory.LocFinSemisimple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroupStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup : ∀ (K V : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) → ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  first | exact @GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | exact GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | (intros; apply GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralUnitPairingOfIrreducibleReductionA
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralUnitPairingOfIrreducibleReductionA
open GlobalTheory.Cong

namespace GlobalTheory.Cong.UnitPairing

open IsLocalRing

variable {R k : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k]
  [Algebra R k] [IsFractionRing R k] {a : ℕ}

noncomputable def intLattice (W : Submodule k (Fin a → k)) : Submodule R (Fin a → R) :=
  (W.restrictScalars R).comap ((Algebra.linearMap R k).compLeft (Fin a))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R k] in
lemma mem_intLattice {W : Submodule k (Fin a → k)} {x : Fin a → R} :
    x ∈ intLattice (R := R) W ↔ (fun i => algebraMap R k (x i)) ∈ W := Iff.rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma mem_intLattice_of_smul {W : Submodule k (Fin a → k)} {r : R} (hr : r ≠ 0)
    {x : Fin a → R} (h : r • x ∈ intLattice (R := R) W) : x ∈ intLattice (R := R) W := by
  rw [mem_intLattice] at *
  have h' : algebraMap R k r • (fun i => algebraMap R k (x i)) ∈ W := by
    convert h using 1
    ext i
    simp [Algebra.smul_def]
  exact (W.smul_mem_iff ((map_ne_zero_iff _ (IsFractionRing.injective R k)).mpr hr)).mp h'

omit [IsDiscreteValuationRing R] in
lemma exists_integral_multiple (y : Fin a → k) :
    ∃ d : R, d ≠ 0 ∧ ∃ x : Fin a → R,
      (fun i => algebraMap R k (x i)) = algebraMap R k d • y := by
  classical
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ y
  choose x hx using fun i => h i (Finset.mem_univ i)
  refine ⟨b, nonZeroDivisors.ne_zero hb, x, ?_⟩
  ext i
  rw [hx i]
  simp [Algebra.smul_def]

noncomputable def redLattice (L : Submodule R (Fin a → R)) :
    Submodule (ResidueField R) (Fin a → ResidueField R) where
  carrier := {v | ∃ x ∈ L, (fun i => residue R (x i)) = v}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, L.add_mem hx hy, by ext i; simp⟩
  zero_mem' := ⟨0, L.zero_mem, by ext i; simp⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨r • x, L.smul_mem r hx, by ext i; simp⟩

omit [IsFractionRing R k] in
lemma exists_eq_smul_of_residue_eq_zero {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})
    {x : Fin a → R} (h : (fun i => residue R (x i)) = 0) : ∃ z : Fin a → R, x = ϖ • z := by
  have : ∀ i, ϖ ∣ x i := fun i => by
    have h1 : residue R (x i) = 0 := congrFun h i
    rw [residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton] at h1
    exact h1
  choose z hz using this
  exact ⟨z, funext fun i => by simp [hz i]⟩

theorem main (B : Matrix (Fin a) (Fin a) R)
    (hB : ∀ W : Submodule (ResidueField R) (Fin a → ResidueField R),
      (∀ v ∈ W, (B.map (residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) :
    ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧
      (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  classical
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hϖ0 : ϖ ≠ 0 := hϖirr.ne_zero
  have hϖm : ϖ ∈ maximalIdeal R := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hϖres : residue R ϖ = 0 := (residue_eq_zero_iff ϖ).mpr hϖm
  have hinj := IsFractionRing.injective R k
  set L := intLattice (R := R) W with hLdef
  haveI : NoZeroSMulDivisors R ((Fin a → R) ⧸ L) := by
    refine ⟨fun {r q} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero L).mpr (mem_intLattice_of_smul hr h)
  haveI : Module.Free R ((Fin a → R) ⧸ L) := Module.free_of_finite_type_torsion_free'
  have hmemL : ∀ {y : Fin a → k}, y ∈ W → ∀ {d : R} {x : Fin a → R},
      (fun i => algebraMap R k (x i)) = algebraMap R k d • y → x ∈ L := by
    intro y hy d x hx
    show (fun i => algebraMap R k (x i)) ∈ W
    rw [hx]
    exact W.smul_mem _ hy

  have hA : redLattice L ≠ ⊥ := by
    intro hbot
    have hle : L ≤ maximalIdeal R • L := by
      intro x hx
      have h0 : (fun i => residue R (x i)) = 0 := by
        have hm : (fun i => residue R (x i)) ∈ redLattice L := ⟨x, hx, rfl⟩
        rw [hbot] at hm
        exact (Submodule.mem_bot _).mp hm
      obtain ⟨z, rfl⟩ := exists_eq_smul_of_residue_eq_zero hϖ h0
      exact Submodule.smul_mem_smul hϖm (mem_intLattice_of_smul hϖ0 hx)
    have hL : L = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) L
      (IsNoetherian.noetherian L) hle (maximalIdeal_le_jacobson _)
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL := hmemL hyW hx
    rw [hL, Submodule.mem_bot] at hxL
    subst hxL
    have h2 : algebraMap R k d • y = 0 := by
      rw [← hx]
      ext i
      simp
    rcases smul_eq_zero.mp h2 with h | h
    · exact hd (hinj (by simpa using h))
    · exact hy0 h

  have hT : redLattice L ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Submodule R ((Fin a → R) ⧸ L)) ≤ maximalIdeal R • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
      have hm : (fun i => residue R (x i)) ∈ redLattice L := htop ▸ Submodule.mem_top
      obtain ⟨l, hl, hlx⟩ := hm
      have h0 : (fun i => residue R ((x - l) i)) = 0 := by
        ext i
        have := congrFun hlx i
        simp only [Pi.sub_apply, map_sub, Pi.zero_apply] at this ⊢
        rw [this, sub_self]
      obtain ⟨z, hz⟩ := exists_eq_smul_of_residue_eq_zero hϖ h0
      have hq : Submodule.Quotient.mk (p := L) x = ϖ • Submodule.Quotient.mk z := by
        rw [← Submodule.Quotient.mk_smul, ← hz, Submodule.Quotient.eq, sub_sub_cancel]
        exact hl
      rw [hq]
      exact Submodule.smul_mem_smul hϖm Submodule.mem_top
    have htopQ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
      Module.Finite.fg_top hle (maximalIdeal_le_jacobson _)
    apply hWt
    rw [eq_top_iff]
    intro y _
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL : x ∈ L := by
      have h1 : Submodule.Quotient.mk (p := L) x ∈ (⊤ : Submodule R ((Fin a → R) ⧸ L)) :=
        Submodule.mem_top
      rw [htopQ] at h1
      exact (Submodule.Quotient.mk_eq_zero L).mp ((Submodule.mem_bot _).mp h1)
    have hdy : algebraMap R k d • y ∈ W := by
      rw [← hx]
      exact hxL
    exact (W.smul_mem_iff ((map_ne_zero_iff _ hinj).mpr hd)).mp hdy

  have hnot : ∃ v ∈ redLattice L, (B.map (residue R)).mulVec v ∉ redLattice L := by
    by_contra hcon
    push_neg at hcon
    rcases hB _ hcon with h | h
    · exact hA h
    · exact hT h
  obtain ⟨_, ⟨w, hwL, rfl⟩, hBw⟩ := hnot
  have hres : (B.map (residue R)).mulVec (fun i => residue R (w i)) =
      fun i => residue R (B.mulVec w i) := by
    ext i
    exact (RingHom.map_mulVec (residue R) B w i).symm
  rw [hres] at hBw
  have hnotsmul : ∀ z : Fin a → R,
      Submodule.Quotient.mk (p := L) (B.mulVec w) ≠ ϖ • Submodule.Quotient.mk z := by
    intro z hz
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hz
    apply hBw
    refine ⟨B.mulVec w - ϖ • z, hz, ?_⟩
    ext i
    simp [hϖres]
  let b := Module.Free.chooseBasis R ((Fin a → R) ⧸ L)
  have hj : ∃ j, b.repr (Submodule.Quotient.mk (B.mulVec w)) j ∉ maximalIdeal R := by
    by_contra hcon
    push_neg at hcon
    have hdv : ∀ j, ϖ ∣ b.repr (Submodule.Quotient.mk (B.mulVec w)) j := fun j => by
      have := hcon j
      rwa [hϖ, Ideal.mem_span_singleton] at this
    choose c hc using hdv
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective L
      (b.repr.symm (Finsupp.equivFunOnFinite.symm c))
    apply hnotsmul z
    apply b.repr.injective
    ext j
    rw [hc j, hz, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, smul_eq_mul]
    simp
  obtain ⟨j, hjm⟩ := hj
  let φ : (Fin a → R) →ₗ[R] R := (b.coord j).comp L.mkQ
  have hφ : ∀ x, φ x = b.repr (Submodule.Quotient.mk x) j := fun x => by
    simp [φ, Module.Basis.coord_apply]
  let f : Fin a → R := fun i => φ (fun j' => if i = j' then 1 else 0)
  have hf : ∀ x, f ⬝ᵥ x = φ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f, smul_eq_mul, mul_comm]
  refine ⟨w, f, hwL, ?_, ?_⟩
  · intro y hy
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL := hmemL hy hx
    have hφx : φ x = 0 := by
      rw [hφ, (Submodule.Quotient.mk_eq_zero L).mpr hxL, map_zero, Finsupp.zero_apply]
    have e1 : (fun i => algebraMap R k (f i)) ⬝ᵥ (fun i => algebraMap R k (x i)) =
        algebraMap R k (f ⬝ᵥ x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [dotProduct, map_sum, map_mul]
    rw [hx, dotProduct_smul, smul_eq_mul, hf, hφx, map_zero] at e1
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h ((map_ne_zero_iff _ hinj).mpr hd)
    · exact h
  · rw [hf, hφ]
    by_contra hu
    exact hjm ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))

end GlobalTheory.Cong.UnitPairing

namespace GlobalTheory.Cong

theorem exists_integral_unit_pairing_of_irreducible_reduction : ∀ (R k : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k] (a : ℕ) (B : Matrix (Fin a) (Fin a) R), (∀ W : Submodule (IsLocalRing.ResidueField R) (Fin a → IsLocalRing.ResidueField R), (∀ v ∈ W, (B.map (IsLocalRing.residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ W : Submodule k (Fin a → k), W ≠ ⊥ → W ≠ ⊤ → ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧ (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  intro R k _ _ _ _ _ _ a B hB W hW0 hWt
  exact UnitPairing.main B hB W hW0 hWt

end GlobalTheory.Cong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralUnitPairingOfIrreducibleReductionAStatement
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unit_pairing_of_irreducible_residue : ∀ (R k : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k] (a : ℕ) (B : Matrix (Fin a) (Fin a) R), (∀ W : Submodule (IsLocalRing.ResidueField R) (Fin a → IsLocalRing.ResidueField R), (∀ v ∈ W, (B.map (IsLocalRing.residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ W : Submodule k (Fin a → k), W ≠ ⊥ → W ≠ ⊤ → ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧ (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  first | exact @GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction | exact GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction | (intros; apply GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction; all_goals assumption)
end
end
