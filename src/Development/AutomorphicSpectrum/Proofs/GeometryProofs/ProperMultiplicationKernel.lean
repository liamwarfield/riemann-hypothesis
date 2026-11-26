module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultiplicativeDerivationRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnit
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteAlgebraUnit

theorem exists_isUnit_mem_of_forall_point :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  intro k _ _ R _ _ _ U hU
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Infinite k := IsAlgClosed.instInfinite

  have hpt : ∀ m : Ideal R, m.IsMaximal → ∃ x : R →ₐ[k] k, ∀ r ∈ m, x r = 0 := by
    intro m hm
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite k (R ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
        (Ideal.Quotient.mkₐ_surjective k m)
    let e : k ≃ₐ[k] (R ⧸ m) :=
      AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(e.symm : (R ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
    have h0 : Ideal.Quotient.mkₐ k m r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    change e.symm (Ideal.Quotient.mkₐ k m r) = 0
    rw [h0, map_zero]

  let f : Ideal R → Submodule k U := fun m => (m.restrictScalars k).comap U.subtype
  have hfin : (f '' {m : Ideal R | m.IsMaximal}).Finite :=
    (IsArtinianRing.setOfPred_isMaximal_finite R).image f
  let s : Finset (Submodule k U) := hfin.toFinset
  have htop : (⊤ : Submodule k U) ∉ s := by
    intro h
    obtain ⟨m, hm, hfm⟩ := (Set.Finite.mem_toFinset hfin).mp h
    obtain ⟨x, hx⟩ := hpt m hm
    obtain ⟨t, htU, ht⟩ := hU x
    have : (⟨t, htU⟩ : U) ∈ f m := by rw [hfm]; trivial
    exact ht (hx t this)
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (s := s) htop
  obtain ⟨w, hw⟩ : ∃ w : U, w ∉ ⋃ p ∈ s, (p : Set U) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  refine ⟨w, w.2, ?_⟩
  by_contra hnu
  obtain ⟨m, hm, hwm⟩ := exists_max_ideal_of_mem_nonunits (show (w : R) ∈ nonunits R from hnu)
  apply hw
  simp only [Set.mem_iUnion]
  exact ⟨f m, (Set.Finite.mem_toFinset hfin).mpr ⟨m, hm, rfl⟩, hwm⟩

end GlobalTheory.CompanionTheory.FiniteAlgebraUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnitStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subspace_contains_unit : ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  first | exact @GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | exact GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | (intros; apply GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElement
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElement
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfFrob

theorem exists_algHom_ne_zero_of_not_isNilpotent
    {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A]
    [Module.Finite k A] {f : A} (hf : ¬ IsNilpotent f) :
    ∃ x : A →ₐ[k] k, x f ≠ 0 := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at hf
  push_neg at hf
  obtain ⟨P, hP, hfP⟩ := hf
  haveI : P.IsPrime := hP
  haveI : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  have hbij : Function.Bijective (algebraMap k (A ⧸ P)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hbij
  refine ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  intro h
  apply hfP
  have h' : e.symm (Ideal.Quotient.mk P f) = 0 := h
  have h2 : Ideal.Quotient.mk P f = 0 := by
    simpa using h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem exists_pow_eq_zero_of_isNilpotent
    {A : Type} [CommRing A] {p : ℕ} (hp : 2 ≤ p) {S : Set A}
    (hS : ∀ f ∈ S, f ^ p ∈ S) {f : A} (hfS : f ∈ S) (hf0 : f ≠ 0) (hf : IsNilpotent f) :
    ∃ g ∈ S, g ≠ 0 ∧ g ^ p = 0 := by
  classical
  obtain ⟨n, hn⟩ := hf
  have hex : ∃ m : ℕ, f ^ (p ^ m) = 0 :=
    ⟨n, pow_eq_zero_of_le (Nat.lt_pow_self (by omega)).le hn⟩
  have hspec := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp at hspec
    exact hf0 hspec
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem : ∀ j : ℕ, f ^ (p ^ j) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hfS
    | succ j ih =>
      have := hS _ ih
      rwa [← pow_mul, ← pow_succ] at this
  refine ⟨f ^ (p ^ m), hmem m, Nat.find_min hex (m := m) (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ]
  rw [hm] at hspec
  exact hspec

theorem exists_frobenius_fixed_or_killed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  intro k _ _ p _ _ A _ _ _ V hV hVp
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f₀, hf₀V, hf₀⟩ := (Submodule.ne_bot_iff V).mp hV
  have key : ∀ n : ℕ, ∀ f ∈ V, f ≠ 0 →
      Module.finrank k (LinearMap.range (LinearMap.mulLeft k f)) = n →
      ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hfV hf0 hn
      by_cases hnil : IsNilpotent f
      · obtain ⟨g, hg, hg0, hgp⟩ := exists_pow_eq_zero_of_isNilpotent (S := (V : Set A)) hp
          (fun a ha => hVp a ha) hfV hf0 hnil
        exact ⟨g, hg, hg0, Or.inl hgp⟩
      obtain ⟨x, hx⟩ := exists_algHom_ne_zero_of_not_isNilpotent (k := k) hnil
      set c : k := (x f)⁻¹ with hc
      set f' : A := c • f with hf'
      have hf'V : f' ∈ V := V.smul_mem c hfV
      have hxf' : x f' = 1 := by
        simp [hf', hc, hx]
      have hf'0 : f' ≠ 0 := by
        intro h
        rw [h] at hxf'
        simp at hxf'
      set g : A := f' ^ p - f' with hg
      have hgV : g ∈ V := V.sub_mem (hVp _ hf'V) hf'V
      by_cases hg0 : g = 0
      · exact ⟨f', hf'V, hf'0, Or.inr (sub_eq_zero.mp hg0)⟩
      have hxg : x g = 0 := by
        simp [hg, hxf']
      obtain ⟨q, hq⟩ : ∃ q : A, g = f * q := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
        refine ⟨c • (f' ^ r - 1), ?_⟩
        calc g = f' * (f' ^ r - 1) := by rw [hg, hr]; ring
          _ = f * (c • (f' ^ r - 1)) := by rw [mul_smul_comm, hf', smul_mul_assoc]
      have hlt : LinearMap.range (LinearMap.mulLeft k g) <
          LinearMap.range (LinearMap.mulLeft k f) := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact ⟨q * a, by simp [hq, mul_assoc]⟩
        · intro heq
          have hmem : f ∈ LinearMap.range (LinearMap.mulLeft k g) := by
            rw [heq]
            exact ⟨1, by simp⟩
          obtain ⟨a, ha⟩ := hmem
          apply hx
          have : g * a = f := by simpa using ha
          rw [← this, map_mul, hxg, zero_mul]
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      exact ih _ (hn ▸ hrank) g hgV hg0 rfl
  exact key _ f₀ hf₀V hf₀ rfl

end GlobalTheory.CompanionTheory.HopfFrob
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElementStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_stable_subspace_element : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  first | exact @GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | exact GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | (intros; apply GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfPrim

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem comul_pow_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (i : ℕ) :
    Coalgebra.comul (R := k) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) • ((f ^ l) ⊗ₜ[k] (f ^ (i - l))) := by
  have h1 : Coalgebra.comul (R := k) (f ^ i) = (f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) ^ i := by
    rw [← hf, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
  rw [h1, add_pow]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

noncomputable def convPow (y : A →ₗ[k] k) : ℕ → (A →ₗ[k] k)
  | 0 => Coalgebra.counit
  | m + 1 => LinearMap.mul' k k ∘ₗ TensorProduct.map y (convPow y m) ∘ₗ Coalgebra.comul

theorem convPow_succ_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (m i : ℕ) :
    convPow y (m + 1) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) := by
  simp only [convPow, LinearMap.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comul_pow_of_primitive f hf i, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]

theorem convPow_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f)
    (hy1 : y 1 = 0) (hyf : y f = 1) (m : ℕ) :
    (∀ i < m, convPow y m (f ^ i) = 0) ∧ convPow y m (f ^ m) = (m.factorial : k) := by
  induction m with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    simp [convPow]
  | succ m ih =>
    have hterm : ∀ i ≤ m + 1, ∀ l ∈ Finset.range (i + 1), l ≠ 1 →
        (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) = 0 := by
      intro i hi l hl hl1
      rcases Nat.lt_or_ge l 2 with h | h
      · have : l = 0 := by omega
        subst this
        simp [hy1]
      · have hlt : i - l < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [convPow_succ_pow y f hf m i]
      refine Finset.sum_eq_zero (fun l hl => ?_)
      by_cases hl1 : l = 1
      · subst hl1
        have hlt : i - 1 < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
      · exact hterm i hi.le l hl hl1
    · rw [convPow_succ_pow y f hf m (m + 1),
        Finset.sum_eq_single 1 (fun l hl hl1 => hterm (m + 1) le_rfl l hl hl1)
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      rw [pow_one, hyf, Nat.add_sub_cancel, ih.2, Nat.choose_one_right, Nat.factorial_succ]
      push_cast
      ring

theorem counit_eq_zero_of_primitive [Nontrivial A] (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    Coalgebra.counit (R := k) f = 0 := by
  have key := congrArg (fun t => TensorProduct.lid k A (LinearMap.rTensor A Coalgebra.counit t)) hf
  simp only [Coalgebra.rTensor_counit_comul, map_add (f := _), LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, Bialgebra.counit_one, one_smul] at key
  have h2 : Coalgebra.counit (R := k) f • (1 : A) = 0 := by
    have := congrArg (· - f) key
    simpa using this.symm
  rw [Algebra.smul_def, mul_one] at h2
  exact (algebraMap k A).injective (h2.trans (map_zero _).symm)

theorem exists_form_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (hf0 : f ≠ 0) :
    ∃ y : A →ₗ[k] k, y 1 = 0 ∧ y f = 1 := by
  have : Nontrivial A := nontrivial_of_ne f 0 hf0
  have hε := counit_eq_zero_of_primitive f hf
  let p : Submodule k A := k ∙ (1 : A)
  have hfp : Submodule.Quotient.mk (p := p) f ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    apply hf0
    rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hε
    rw [hε, zero_smul]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ p), φ (Submodule.Quotient.mk f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hfp ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  refine ⟨(φ (Submodule.Quotient.mk f))⁻¹ • (φ ∘ₗ p.mkQ), ?_, ?_⟩
  · have h1 : Submodule.Quotient.mk (p := p) (1 : A) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr (Submodule.mem_span_singleton_self 1)
    simp [h1]
  · simp [inv_mul_cancel₀ hφ]

theorem powers_indep_of_primitive :
    ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  intro k _ p _ _ A _ _ _ _ f hf hf0 c hsum
  obtain ⟨y, hy1, hyf⟩ := exists_form_of_primitive f hf hf0
  have key : ∀ m < p, (∀ i, m < i → i < p → c i = 0) → c m = 0 := by
    intro m hm hgt
    have h := congrArg (convPow y m) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [Finset.sum_eq_single m] at h
    · rw [(convPow_pow y f hf hy1 hyf m).2] at h
      have hfact : (m.factorial : k) ≠ 0 := by
        rw [ne_eq, CharP.cast_eq_zero_iff k p, Nat.Prime.dvd_factorial (Fact.out)]
        omega
      exact (mul_eq_zero.mp h).resolve_right hfact
    · intro i hi hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · rw [(convPow_pow y f hf hy1 hyf m).1 i h', mul_zero]
      · rw [hgt i h' (Finset.mem_range.mp hi), zero_mul]
    · intro h'
      exact absurd (Finset.mem_range.mpr hm) h'
  have hall : ∀ n, ∀ i < p, p - 1 - i < n → c i = 0 := by
    intro n
    induction n with
    | zero => intro i _ h; omega
    | succ n ih =>
      intro i hi hn
      exact key i hi (fun j hij hj => ih j hj (by omega))
  intro i hi
  exact hall p i hi (by omega)

end GlobalTheory.CompanionTheory.HopfPrim
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndepStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_element_powers_indep : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | exact GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | (intros; apply GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairing
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HopfCount
open Coalgebra GlobalTheory WithConv

section dual
variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
  [Module.Finite k A]

theorem mul_apply_prim {g : A} (hg : comul (R := k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g)
    (w w' : CartierDual k A) : (w * w') g = w g * w' 1 + w 1 * w' g := by
  rw [CartierDual.mul_apply, hg]
  simp

noncomputable def dualDer (f : A) (hf : comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    Derivation k (CartierDual k A) (CartierDual k A) :=
  Derivation.mk' (CartierDual.transpose (LinearMap.mulLeft k f)) (by
    intro a b
    refine CartierDual.ext_apply fun c => ?_
    have h : ∀ t : A ⊗[k] A, CartierDual.pair k A A (a ⊗ₜ b) ((f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) * t) =
        CartierDual.pair k A A ((CartierDual.transpose (LinearMap.mulLeft k f) a) ⊗ₜ b) t +
        CartierDual.pair k A A (a ⊗ₜ (CartierDual.transpose (LinearMap.mulLeft k f) b)) t := by
      intro t
      induction t with
      | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]; ring
      | tmul c d => simp [add_mul]
    have h2 := h (comul (R := k) c)
    rw [← hf, ← Bialgebra.comul_mul] at h2
    change (a * b) (f * c) = (a * CartierDual.transpose (LinearMap.mulLeft k f) b +
      b * CartierDual.transpose (LinearMap.mulLeft k f) a) c
    rw [mul_comm b, CartierDual.mul_apply a b (f * c), h2, ← CartierDual.mul_apply, ← CartierDual.mul_apply]
    simp [add_comm])

theorem dualDer_apply (f : A) (hf) (w : CartierDual k A) (a : A) :
    dualDer (k := k) f hf w a = w (f * a) := rfl

theorem dualDer_iter (f : A) (hf) (n : ℕ) (w : CartierDual k A) (a : A) :
    ((⇑(dualDer (k := k) f hf))^[n] w) a = w (f ^ n * a) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', dualDer_apply, ih, pow_succ, mul_assoc, mul_comm f a,
      ← mul_assoc, mul_assoc, mul_comm a f]

theorem point_eval (x : CartierDual k A →ₐ[k] k) :
    ∃ g : A, IsUnit g ∧ ∀ w : CartierDual k A, x w = w g := by
  let X : CartierDual k (CartierDual k A) := toConv x.toLinearMap
  let g : A := (CartierDual.bidual k A).symm X
  have hg : ∀ w : CartierDual k A, x w = w g := fun w => by
    rw [CartierDual.apply_bidual_symm]; rfl
  refine ⟨g, ?_, hg⟩
  have h1 : comul (R := k) g = g ⊗ₜ[k] g := by
    refine CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_
    rw [← CartierDual.mul_apply, CartierDual.pair_tmul_tmul, ← hg, ← hg, ← hg, map_mul]
  have h2 : counit (R := k) g = 1 := by
    rw [← CartierDual.one_apply, ← hg, map_one]
  have h3 := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) g
  rw [h1, h2] at h3
  simp at h3
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h3)

theorem exists_dual_ne {a : A} (h : a ≠ 0) : ∃ w : CartierDual k A, w a ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (CartierDual.eq_of_forall_apply (R := k) fun w => by simp [hc w])

end dual

theorem key (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (f : A) (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (h0 : f ≠ 0)
    (hc : f ^ p = 0 ∨ f ^ p = f) :
    Module.finrank k A = p * Module.finrank k (A ⧸ Ideal.span {f}) ∧
    ∀ g ∈ Ideal.span {f}, Coalgebra.comul (R := k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g →
      ∃ a : k, g = a • f := by
  classical
  have hp2 : 2 ≤ p := hp.out.two_le
  let D := dualDer (k := k) f hf
  let ε := Bialgebra.counitAlgHom k (CartierDual k A)
  have hεD : ∀ z : CartierDual k A, ε (D z) = z f := fun z => by
    show (D z) 1 = z f
    rw [dualDer_apply, mul_one]
  have hG : Module.finrank k (CartierDual k A) =
        p * Module.finrank k (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)) ∧
      ∃ z : CartierDual k A, ε (D z) ≠ 0 ∧ ∀ u : CartierDual k A →ₗ[k] k,
        (∀ a b : CartierDual k A, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : CartierDual k A, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
    rcases hc with hc | hc
    · have hD : ∀ a, (⇑D)^[p] a = 0 := fun a => CartierDual.ext_apply fun c => by
        rw [dualDer_iter, hc]; simp
      have hnz : f ^ (p - 1) ≠ 0 := by
        intro hz
        have := GlobalTheory.T.primitive_element_powers_indep k p A f hf h0 (fun i => if i = p - 1 then 1 else 0) (by
          rw [Finset.sum_eq_single (p - 1)]
          · simp [hz]
          · intro b _ hb; simp [hb]
          · intro h; simp at h; omega) (p - 1) (by omega)
        simp at this
      obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.subspace_contains_unit k (CartierDual k A)
        (LinearMap.range (((D : CartierDual k A →ₗ[k] CartierDual k A)) ^ (p - 1))) (by
        intro x
        obtain ⟨g, hgu, hg⟩ := point_eval x
        obtain ⟨w, hw⟩ := exists_dual_ne (k := k) (hgu.mul_left_eq_zero.not.2 hnz)
        refine ⟨_, ⟨w, rfl⟩, ?_⟩
        rw [hg, Module.End.pow_apply]
        exact (dualDer_iter f hf (p - 1) w g).symm ▸ hw)
      obtain ⟨t, rfl⟩ := hw
      exact GlobalTheory.T.nilpotent_derivation_rank k p _ D ε hD t (by simpa [Module.End.pow_apply] using hwu)
    · have hD : ∀ a, (⇑D)^[p] a = D a := fun a => CartierDual.ext_apply fun c => by
        rw [dualDer_iter, hc]; rfl
      let u0 : A := ∑ i ∈ Finset.Ico 1 p, f ^ i
      have hu1 : f * u0 = u0 := by
        have h := geom_sum_Ico_mul f (show 1 ≤ p by omega)
        rw [hc, pow_one, sub_self] at h
        have h' : u0 * (f - 1) = 0 := h
        linear_combination h'
      have hu0 : u0 ≠ 0 := by
        intro hz
        have := GlobalTheory.T.primitive_element_powers_indep k p A f hf h0 (fun i => if i = 0 then 0 else 1) (by
          rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
          simp only [if_true, zero_smul, zero_add]
          rw [← hz]
          refine Finset.sum_congr rfl fun i hi => ?_
          have : i ≠ 0 := by have := (Finset.mem_Ico.1 hi).1; omega
          simp [this]) 1 (by omega)
        simp at this
      obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.subspace_contains_unit k (CartierDual k A)
        (LinearMap.ker ((D : CartierDual k A →ₗ[k] CartierDual k A) - LinearMap.id)) (by
        intro x
        obtain ⟨g, hgu, hg⟩ := point_eval x
        obtain ⟨w, hw⟩ := exists_dual_ne (k := k) (hgu.mul_left_eq_zero.not.2 hu0)
        refine ⟨CartierDual.transpose (LinearMap.mulLeft k u0) w, ?_, ?_⟩
        · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
          refine CartierDual.ext_apply fun c => ?_
          show w (u0 * (f * c)) = w (u0 * c)
          rw [← mul_assoc, mul_comm u0, hu1]
        · rw [hg]; exact hw)
      have hw' : D w = w := by
        simpa [sub_eq_zero] using hw
      exact GlobalTheory.T.multiplicative_derivation_rank k p _ D ε hD w hwu hw'
  obtain ⟨hdim, z, hz, hu⟩ := hG
  refine ⟨?_, ?_⟩
  · let Ik : Submodule k A := (Ideal.span {f}).restrictScalars k
    have h1 : Module.finrank k (CartierDual k A) = Module.finrank k A := by
      rw [LinearEquiv.finrank_eq (CartierDual.toDual k A)]
      exact Subspace.dual_finrank_eq
    have h2 : Module.finrank k (A ⧸ Ideal.span {f}) = Module.finrank k (A ⧸ Ik) :=
      (LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f}))).symm
    have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq Ik
    have h4 := Submodule.finrank_quotient_add_finrank Ik
    have h5 : (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)).map
        (CartierDual.toDual k A).toLinearMap = Ik.dualAnnihilator := by
      ext φ
      rw [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      constructor
      · rintro ⟨w, hw, rfl⟩ x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
        have hw0 : D w = 0 := LinearMap.mem_ker.1 hw
        have : (D w) a = 0 := by rw [hw0]; rfl
        rw [dualDer_apply] at this
        rw [mul_comm]; exact this
      · intro h
        refine ⟨(CartierDual.toDual k A).symm φ, ?_, by simp⟩
        refine LinearMap.mem_ker.2 (CartierDual.ext_apply fun c => ?_)
        exact h _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
    have h6 : Module.finrank k (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)) =
        Module.finrank k Ik.dualAnnihilator := by
      rw [← h5]
      exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (CartierDual.toDual k A).injective _)
    rw [← h1, hdim, h6, h2]
    congr 1
    omega
  · intro g hgI hg
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hgI
    have hzf : z f ≠ 0 := by rwa [hεD] at hz
    let a : k := z (b * f) / z f
    refine ⟨a, ?_⟩
    let u : CartierDual k A →ₗ[k] k :=
      CartierDual.evalAt k A (b * f) - a • CartierDual.evalAt k A f
    have hua : ∀ w : CartierDual k A, u w = w (b * f) - a * w f := fun w => rfl
    have hu0 := hu u (fun w w' => by
      rw [hua, hua, hua, mul_apply_prim hg, mul_apply_prim hf]
      show _ = (w (b * f) - a * w f) * w' 1 + w 1 * (w' (b * f) - a * w' f)
      ring) (fun w hw => by
      have h1 : ∀ c, w (f * c) = 0 := fun c => by
        have : (D w) c = 0 := by rw [hw]; rfl
        rwa [dualDer_apply] at this
      have h2 : w f = 0 := by simpa using h1 1
      have h3 : w (b * f) = 0 := by rw [mul_comm]; exact h1 b
      rw [hua, h2, h3]; simp) (by
      rw [hua]
      simp only [a]
      field_simp
      ring)
    refine CartierDual.eq_of_forall_apply (R := k) fun w => ?_
    have := congr($hu0 w)
    rw [hua] at this
    simp only [LinearMap.zero_apply, sub_eq_zero] at this
    rw [this, map_smul]
    rfl

end GlobalTheory.CompanionTheory.Ar.HopfCount

namespace GlobalTheory.CompanionTheory.Ar.HopfCount
open Coalgebra

section
variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem antipode_prim {f : A} (hf : comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    HopfAlgebra.antipode k f = -f := by
  have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) f
  have h0 : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hf
  rw [hf] at h
  simp [h0] at h
  exact eq_neg_of_add_eq_zero_left h

theorem isHopfIdeal_span {f : A}
    (hf' : comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    (Ideal.span {f}).IsHopfIdeal k := by
  have h0 : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hf'
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have := Bialgebra.counit_mul (R := k) a f
    simp [h0]
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hz : Ideal.Quotient.mkₐ k (Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)
    have : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span {f}))
        (Ideal.Quotient.mkₐ k (Ideal.span {f}))) (comul (R := k) (a * f)) = 0 := by
      rw [Bialgebra.comul_mul, map_mul, hf', map_add (f := _)]
      simp [hz]
    exact this
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : HopfAlgebra.antipode k (a * f) = HopfAlgebra.antipode k a * (- f) := by
      rw [← antipode_prim (k := k) hf']
      exact map_mul (HopfAlgebra.antipodeAlgHom k A) a f
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self f))

theorem isCocomm_quot (I : Ideal A) [I.IsHopfIdeal k] [Coalgebra.IsCocomm k A] :
    Coalgebra.IsCocomm k (A ⧸ I) := by
  refine ⟨LinearMap.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := A)) a)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
  rw [Bialgebra.Quotient.comul_mk]
  conv_rhs => rw [← h]
  generalize comul (R := k) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a b => simp
end

theorem stepP (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (IH : ∀ (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B],
      Module.finrank k B < Module.finrank k A →
      ∀ (P : Submodule k B) (W : Submodule k (B →ₗ[k] k)),
      (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] f) →
      (∀ v ∈ W, ∀ f g : B, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
      (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
      p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k B)
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)) (hP0 : P ≠ ⊥)
    (hP : ∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f)
    (hW : ∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g)
    (hPW : ∀ v ∈ W, ∀ f ∈ P, v f = 0) :
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  classical
  have hp2 : 2 ≤ p := hp.out.two_le

  let Q : Submodule k A := GlobalTheory.primitiveElems k A ⊓ ⨅ v ∈ W, LinearMap.ker v
  have memQ : ∀ g, g ∈ Q ↔ (comul (R := k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g) ∧ ∀ v ∈ W, v g = 0 := by
    intro g
    simp [Q, Submodule.mem_iInf, GlobalTheory.mem_primitiveElems, GlobalTheory.IsPrimitiveElem]
  have hPQ : P ≤ Q := fun f hf => (memQ f).2 ⟨hP f hf, fun v hv => hPW v hv f hf⟩
  have hQ0 : Q ≠ ⊥ := fun h => hP0 (le_bot_iff.1 (h ▸ hPQ))
  have hNT : Nontrivial A := by
    obtain ⟨x, -, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    exact ⟨x, 0, hx⟩
  have hfrob : ∀ f ∈ Q, f ^ p ∈ Q := by
    intro f hf
    obtain ⟨h1, h2⟩ := (memQ f).1 hf
    have hcf : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) h1
    refine (memQ _).2 ⟨?_, fun v hv => ?_⟩
    · have : CharP (A ⊗[k] A) p :=
        charP_of_injective_algebraMap (algebraMap k (A ⊗[k] A)).injective p
      have : comul (R := k) (f ^ p) = (comul (R := k) f) ^ p :=
        map_pow (Bialgebra.comulAlgHom k A) f p
      rw [this, h1, add_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
        one_pow]
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [pow_succ, hW v hv, h2 v hv, hcf]
      simp
  obtain ⟨f, hfQ, hf0, hfc⟩ := GlobalTheory.T.frobenius_stable_subspace_element k p A Q hQ0 hfrob
  obtain ⟨hfp, hfW⟩ := (memQ f).1 hfQ
  obtain ⟨hdim, hker⟩ := key k p A f hfp hf0 hfc
  have : (Ideal.span {f}).IsHopfIdeal k := isHopfIdeal_span hfp
  have : Coalgebra.IsCocomm k (A ⧸ Ideal.span {f}) := isCocomm_quot _
  have hcf : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hfp
  let π := Ideal.Quotient.mkₐ k (Ideal.span {f})
  let dm : ((A ⧸ Ideal.span {f}) →ₗ[k] k) →ₗ[k] (A →ₗ[k] k) := π.toLinearMap.dualMap
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k _
  have hdm : Function.Injective dm := LinearMap.dualMap_injective_of_surjective hπ
  let PB : Submodule k (A ⧸ Ideal.span {f}) := Q.map π.toLinearMap
  let WB : Submodule k ((A ⧸ Ideal.span {f}) →ₗ[k] k) := W.comap dm
  have hWmap : WB.map dm = W := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun v hv => ?_
    have hvI : ∀ x ∈ (Ideal.span {f}).restrictScalars k, v x = 0 := by
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [hW v hv, hfW v hv, hcf]; simp
    let u : (A ⧸ Ideal.span {f}) →ₗ[k] k := ((Ideal.span {f}).restrictScalars k).liftQ v
      (fun x hx => hvI x hx)
    have hu : dm u = v := LinearMap.ext fun a => rfl
    exact ⟨u, by show dm u ∈ W; rwa [hu], hu⟩
  have hfW' : Module.finrank k WB = Module.finrank k W := by
    rw [← hWmap]; exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective dm hdm WB)
  let q : Q →ₗ[k] (A ⧸ Ideal.span {f}) := π.toLinearMap.domRestrict Q
  have hker' : LinearMap.ker q = Submodule.span k {(⟨f, hfQ⟩ : Q)} := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro h
      have hxI : x ∈ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.1 h
      obtain ⟨a, rfl⟩ := hker x hxI ((memQ x).1 hx).1
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      have : x = a • f := (congrArg Subtype.val ha).symm
      subst this
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Submodule.smul_of_tower_mem _ a (Ideal.mem_span_singleton_self f))
  have hfQ' : Module.finrank k PB + 1 = Module.finrank k Q := by
    have h := LinearMap.finrank_range_add_finrank_ker q
    rw [hker', finrank_span_singleton (by simpa [Subtype.ext_iff] using hf0),
      LinearMap.range_domRestrict] at h
    exact h
  have hpos : 0 < Module.finrank k A := Module.finrank_pos
  have hlt : Module.finrank k (A ⧸ Ideal.span {f}) < Module.finrank k A := by
    rw [hdim] at hpos ⊢
    have : 0 < Module.finrank k (A ⧸ Ideal.span {f}) := Nat.pos_of_mul_pos_left hpos
    nlinarith
  have key2 := IH (A ⧸ Ideal.span {f}) hlt PB WB ?_ ?_ ?_
  · have hle : Module.finrank k P ≤ Module.finrank k Q := Submodule.finrank_mono hPQ
    rw [hfW'] at key2
    have h3 : p ^ (Module.finrank k Q + Module.finrank k W) ∣ Module.finrank k A := by
      rw [hdim, ← hfQ', show Module.finrank k PB + 1 + Module.finrank k W =
        (Module.finrank k PB + Module.finrank k W) + 1 by ring, pow_succ, mul_comm]
      exact Nat.mul_dvd_mul_left p key2
    exact (pow_dvd_pow p (by omega)).trans h3
  · rintro _ ⟨g, hg, rfl⟩
    have h := ((memQ g).1 hg).1
    show comul (R := k) (Ideal.Quotient.mk (Ideal.span {f}) g) = _
    rw [Bialgebra.Quotient.comul_mk, h]
    simp [π]
  · intro u hu x y
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨b, rfl⟩ := hπ y
    exact hW (dm u) hu a b
  · rintro u hu _ ⟨g, hg, rfl⟩
    exact ((memQ g).1 hg).2 (dm u) hu

theorem norm_index_count_bound (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A],
      Module.finrank k A = n →
      ∀ (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
      (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
      (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
      (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
      p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hn P W hP hW hPW
  have IH : ∀ (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B],
      Module.finrank k B < Module.finrank k A →
      ∀ (P : Submodule k B) (W : Submodule k (B →ₗ[k] k)),
      (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] f) →
      (∀ v ∈ W, ∀ f g : B, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
      (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
      p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k B := by
    intro B _ _ _ _ hB
    exact ih _ (hn ▸ hB) B rfl
  by_cases hP0 : P = ⊥
  · by_cases hW0 : W = ⊥
    · simp [hP0, hW0]
    ·
      let e : (A →ₗ[k] k) ≃ₗ[k] GlobalTheory.CartierDual k A := (GlobalTheory.CartierDual.toDual k A).symm
      have hd : Module.finrank k (GlobalTheory.CartierDual k A) = Module.finrank k A := by
        rw [LinearEquiv.finrank_eq (GlobalTheory.CartierDual.toDual k A)]
        exact Subspace.dual_finrank_eq
      let P' : Submodule k (GlobalTheory.CartierDual k A) := W.map e.toLinearMap
      have hfin : Module.finrank k P' = Module.finrank k W :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective e.toLinearMap e.injective W)).symm
      have hP'0 : P' ≠ ⊥ := by
        intro h
        exact hW0 (Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective
          (h.trans (Submodule.map_bot _).symm))
      have := stepP k p (GlobalTheory.CartierDual k A) (fun B _ _ _ _ hB => IH B (hd ▸ hB)) P' ⊥ hP'0 ?_
        (by simp) (by simp)
      · rw [hP0]
        simpa [hfin, hd, add_comm] using this
      · rintro _ ⟨v, hv, rfl⟩
        rw [GlobalTheory.CartierDual.comul_eq_iff]
        intro a b
        have := hW v hv a b
        have he : ∀ a, (e v).ofConv a = v a := fun _ => rfl
        simpa [GlobalTheory.CartierDual.one_apply, he] using this.symm
  · exact stepP k p A IH P W hP0 hP hW hPW

theorem primitive_tangent_dvd_finrank :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A :=
  fun k _ _ p _ _ A _ _ _ _ P W hP hW hPW => norm_index_count_bound k p _ A rfl P W hP hW hPW

end GlobalTheory.CompanionTheory.Ar.HopfCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairingStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_derivation_pairing : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | exact GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.KerBd

variable {k : Type} [Field k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Wd (B : Germ.FB k d O) (a : O) : Submodule k (Fin d → k) where
  carrier := {u | (rho B a).mulVec u = 0 ∧ ∀ z : Fin d → k, (rho B (star a)).mulVec z = 0 →
      z ⬝ᵥ (bil (B.ad a) 1 1).transpose.mulVec u = 0}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by simp [Matrix.mulVec_add, hu1, hv1], fun z hz => ?_⟩
    simp [Matrix.mulVec_add, dotProduct_add, hu2 z hz, hv2 z hz]
  zero_mem' := ⟨by simp, fun z _ => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    refine ⟨by simp [Matrix.mulVec_smul, hu1], fun z hz => ?_⟩
    simp [Matrix.mulVec_smul, dotProduct_smul, hu2 z hz]

theorem Wd_le (B : Germ.FB k d O) (a : O) : Wd B a ≤ LinearMap.ker (Matrix.toLin' (rho B a)) :=
  fun u hu => by simpa [Matrix.toLin'_apply] using hu.1

theorem finrank_ker_transpose (M : Matrix (Fin d) (Fin d) k) :
    Module.finrank k (LinearMap.ker (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M.transpose)
  have h3 : Module.finrank k (LinearMap.range (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.range (Matrix.toLin' M)) := by
    have := Matrix.rank_transpose M
    rw [Matrix.rank, Matrix.rank] at this
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
    convert this using 2
  omega

theorem finrank_ker_rhoH_le (B : Germ.FB k d O) (a : O) :
    Module.finrank k (LinearMap.ker (rhoH B a)) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)))) + Module.finrank k (Wd B a) := by
  set K := LinearMap.ker (rhoH B a)
  let f : K →ₗ[k] (Fin d → k) := (LinearMap.fst k (Fin d → k) (Fin d → k)).comp K.subtype
  have hrange : LinearMap.range f ≤ Wd B a := by
    rintro _ ⟨y, rfl⟩
    have hy : rhoH B a y = 0 := y.2
    rw [rhoH_apply, Prod.mk_eq_zero] at hy
    refine ⟨hy.1, fun z hz => ?_⟩
    have h2 : (bil (B.ad a) 1 1).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).1 =
        (rho B (star a)).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).2 := (sub_eq_zero.1 hy.2).symm
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.fst_apply]
    rw [h2, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hz, zero_dotProduct]
  let g : LinearMap.ker f →ₗ[k] (Fin d → k) :=
    (LinearMap.snd k (Fin d → k) (Fin d → k)).comp (K.subtype.comp (LinearMap.ker f).subtype)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have h2 : ((y : K) : (Fin d → k) × (Fin d → k)).2 = 0 := hy
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
  have hgr : LinearMap.range g ≤ LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose) := by
    rintro _ ⟨y, rfl⟩
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have hy : rhoH B a (y : K) = 0 := (y : K).2
    rw [rhoH_apply, Prod.mk_eq_zero, h1] at hy
    simpa [g, Matrix.toLin'_apply] using hy.2
  have e1 := LinearMap.finrank_range_add_finrank_ker f
  have e2 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (Wd B a) := Submodule.finrank_mono hrange
  have e3 : Module.finrank k (LinearMap.ker f) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose)) := by
    rw [← LinearMap.finrank_range_of_inj hg]; exact Submodule.finrank_mono hgr
  rw [finrank_ker_transpose] at e3
  omega

end GlobalTheory.CompanionTheory.Ar.Flat.KerBd

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.KerBd in
theorem lemF_ker_order_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  intro E _ _ _ H _ hbar k _ _ p _ _ t hprop hK d g a A _ _ _ i hpb
  obtain ⟨A', _, _, _, _, hrk, D, T, hD, hT, hder, hprim, horth⟩ :=
    GlobalTheory.T.proper_group_germ_finite_subscheme E H hbar k p t hprop hK d g a A i hpb
  let W0 : Submodule k (LinearMap.ker (Matrix.toLin' (rho g.B a))) :=
    (Wd g.B a).comap (LinearMap.ker (Matrix.toLin' (rho g.B a))).subtype
  have hW0 : Module.finrank k W0 = Module.finrank k (Wd g.B a) :=
    (Submodule.comapSubtypeEquivOfLe (Wd_le g.B a)).finrank_eq
  have hc := GlobalTheory.T.primitive_derivation_pairing k p A' (LinearMap.range T) (W0.map D)
    (by rintro _ ⟨z, rfl⟩; exact hprim z)
    (by rintro _ ⟨u, -, rfl⟩; exact hder u)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨z, rfl⟩
      have hz : (rho g.B (star a)).mulVec (z : Fin d → k) = 0 := by
        have := z.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      exact horth u z ((hu : (u : Fin d → k) ∈ Wd g.B a).2 z hz))
  rw [LinearMap.finrank_range_of_inj hT, ← (Submodule.equivMapOfInjective D hD W0).finrank_eq, hW0, hrk] at hc
  exact (pow_dvd_pow p (finrank_ker_rhoH_le g.B a)).trans hc

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_multiplication_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd | exact GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd <;> assumption)
end
