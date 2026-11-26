module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSumIntegralBasis
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem isClosed_int_add_mul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (M : ℕ) (hM : 0 < M) (hcl : IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c}) :
    IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} := by
  have key : {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} =
      ⋃ r : Fin M, (fun x => x - ((r : ℕ) : A)) ⁻¹' {a : A | ∃ c ∈ O, a = (M : A) * c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨z, c, hc, rfl⟩
      have hMz : (0 : ℤ) < M := by exact_mod_cast hM
      have h0 : 0 ≤ z % (M : ℤ) := Int.emod_nonneg z hMz.ne'
      have h1 : z % (M : ℤ) < M := Int.emod_lt_of_pos z hMz
      have hdiv := congrArg (fun t : ℤ => (t : A)) (Int.emod_add_mul_ediv z M)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hdiv
      refine ⟨⟨(z % M).toNat, by omega⟩, ((z / M : ℤ) : A) + c, add_mem (intCast_mem O _) hc, ?_⟩
      have hr : (((z % M).toNat : ℕ) : A) = ((z % M : ℤ) : A) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      simp only [hr]
      linear_combination -hdiv
    · rintro ⟨r, c, hc, hx⟩
      refine ⟨((r : ℕ) : ℤ), c, hc, ?_⟩
      rw [Int.cast_natCast]
      linear_combination hx
  rw [key]
  exact isClosed_iUnion_of_finite fun r => hcl.preimage (continuous_id.sub continuous_const)

theorem exists_sum_of_approx {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (hO : IsCompact (O : Set A))
    (hcl : ∀ M : ℕ, 0 < M → IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c})
    (hz : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c ∈ O, a = (M : A) * c) → a = 0)
    {β : Type} [Fintype β] (w : β → A) (a : A)
    (ha : ∀ M : ℕ, 0 < M → ∃ (z : β → ℤ) (c : A), c ∈ O ∧ a = ∑ i, (z i : A) * w i + (M : A) * c) :
    ∃ r : β → A, (∀ i, ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r i = (z : A) + (M : A) * c) ∧
      a = ∑ i, r i * w i := by
  classical
  have hSc : ∀ M : ℕ, 0 < M →
      IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} :=
    fun M hM => isClosed_int_add_mul O M hM (hcl M hM)
  have hL : Continuous fun r : β → A => a - ∑ i, r i * w i :=
    continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  let t : ℕ → Set (β → A) := fun m =>
    (⋂ i, (fun r : β → A => r i) ⁻¹'
      {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + ((m + 1 : ℕ) : A) * c}) ∩
    (fun r : β → A => a - ∑ i, r i * w i) ⁻¹' {x : A | ∃ c ∈ O, x = ((m + 1 : ℕ) : A) * c}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (isClosed_iInter fun i => (hSc (m + 1) m.succ_pos).preimage (continuous_apply i)).inter
      ((hcl (m + 1) m.succ_pos).preimage hL)
  have hs : IsCompact (Set.univ.pi fun _ : β => (O : Set A)) := isCompact_univ_pi fun _ => hO
  have hne : ∀ u : Finset ℕ, ((Set.univ.pi fun _ : β => (O : Set A)) ∩ ⋂ m ∈ u, t m).Nonempty := by
    intro u
    have hNpos : 0 < ∏ m ∈ u, (m + 1) := Finset.prod_pos fun m _ => m.succ_pos
    obtain ⟨z, c, hc, hac⟩ := ha _ hNpos
    refine ⟨fun i => (z i : A), fun i _ => intCast_mem O (z i), ?_⟩
    simp only [Set.mem_iInter]
    intro m hm
    obtain ⟨k, hk⟩ : (m + 1) ∣ ∏ m ∈ u, (m + 1) := Finset.dvd_prod_of_mem _ hm
    rw [hk] at hac
    simp only [t, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun i => ⟨z i, 0, zero_mem O, by ring⟩, (k : A) * c, mul_mem (natCast_mem O k) hc, ?_⟩
    push_cast at hac ⊢
    linear_combination hac
  obtain ⟨r, -, hr⟩ := hs.inter_iInter_nonempty t htc hne
  simp only [t, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hr
  have hpred : ∀ M : ℕ, 0 < M → ∃ m : ℕ, M = m + 1 := fun M hM => ⟨M - 1, by omega⟩
  refine ⟨r, fun i M hM => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := hpred M hM
    exact (hr m).1 i
  · have h0 : a - ∑ i, r i * w i = 0 := hz _ fun M hM => by
      obtain ⟨m, rfl⟩ := hpred M hM
      exact (hr m).2
    exact sub_eq_zero.mp h0

private def intAdeles (F : Type) [Field F] [NumberField F] :
    Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' ha v := neg_mem (ha v)

theorem exists_sum_integralBasis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ r : β → FiniteAdeleRing (𝓞 F) F, (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) ∧ a = ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) := by
  intro F _ _ β _ ω a ha
  obtain ⟨hcomp, hclM, hzero, -, -, -⟩ := GlobalTheory.T.integralFiniteAdele_compact_closed_multiples F
  have hexp : ∀ x : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) =
      ∑ i, ((ω.repr x i : ℤ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω i : 𝓞 F) : F) := by
    intro x
    conv_lhs => rw [← ω.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine exists_sum_of_approx (intAdeles F) hcomp hclM hzero _ a ?_
  intro M hM
  obtain ⟨x, c, hc, hac⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F M hM).2 a ha
  refine ⟨fun i => ω.repr x i, c, hc, ?_⟩
  rw [hac, hexp, nsmul_eq_mul]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordDivisible
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CoordDiv

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {c | ∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' := fun {a b} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' := fun {a b} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' := fun {a} ha v => neg_mem (ha v)

theorem algebraMap_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ intAdeles F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, RingOfIntegers.coe_eq_algebraMap]
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_of_mem (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAdeles F) :
    ∃ a : 𝓞 F, (a : F) = k := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => by
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact ⟨a, ha⟩

theorem dvd_of_eq (x : 𝓞 F) (N : ℕ) (hN : 0 < N) (e : FiniteAdeleRing (𝓞 F) F)
    (he : e ∈ intAdeles F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) = (N : FiniteAdeleRing (𝓞 F) F) * e) :
    ∃ a : 𝓞 F, x = (N : 𝓞 F) * a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((x : F) / N) = e := by
    rw [div_eq_mul_inv, map_mul, h, mul_comm, ← mul_assoc,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, inv_mul_cancel₀ hN',
      map_one, one_mul]
  obtain ⟨a, ha⟩ := exists_of_mem F _ (hk ▸ he)
  have hx : (x : F) = N * (a : F) := by
    rw [ha]
    field_simp
  exact ⟨a, by exact_mod_cast hx⟩

theorem int_dvd (z : ℤ) (N : ℕ) (a : 𝓞 F) (h : (z : 𝓞 F) = (N : 𝓞 F) * a) : (N : ℤ) ∣ z := by

  have h2 := congrArg (Algebra.norm ℤ) h
  rw [map_mul, ← eq_intCast (algebraMap ℤ (𝓞 F)) z,
    show (N : 𝓞 F) = algebraMap ℤ (𝓞 F) (N : ℤ) by simp, Algebra.norm_algebraMap,
    Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').mp ⟨_, h2⟩

theorem coord_divisible : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (r : β → FiniteAdeleRing (𝓞 F) F) (N : ℕ), 0 < N → (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) → (∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v, (e : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) = (N : FiniteAdeleRing (𝓞 F) F) * e) → ∀ i, ∃ s : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ s = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c) ∧ r i = (N : FiniteAdeleRing (𝓞 F) F) * s := by
  intro F _ _ β _ ω r N hN hr hsum i
  obtain ⟨e, he, hsum⟩ := hsum
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have := (isUnit_iff_ne_zero.mpr hN').map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
    rwa [map_natCast] at this
  have hω : ∀ j, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω j : 𝓞 F) : F) ∈ intAdeles F :=
    fun j => algebraMap_mem F (ω j)
  have hint : ∀ z : ℤ, (z : FiniteAdeleRing (𝓞 F) F) ∈ intAdeles F := fun z => intCast_mem _ z

  choose z c hc hrc using fun j => hr j N hN
  have hc' : ∀ j, c j ∈ intAdeles F := hc

  have hL : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∑ j, z j • ω j : 𝓞 F)) : F) =
      ∑ j, (z j : FiniteAdeleRing (𝓞 F) F) * algebraMap F _ ((ω j : 𝓞 F) : F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap]
  obtain ⟨a, ha⟩ := dvd_of_eq F (∑ j, z j • ω j) N hN
    (e - ∑ j, c j * algebraMap F _ ((ω j : 𝓞 F) : F))
    (sub_mem he (sum_mem fun j _ => mul_mem (hc' j) (hω j))) (by
      rw [hL, mul_sub, Finset.mul_sum, ← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrc j]
      ring)

  have hm : ∀ j, z j = N * ω.repr a j := by
    intro j
    have h1 := congrArg (fun y => ω.repr y j) ha
    have h2 : (N : 𝓞 F) * a = (N : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    simp only [ω.repr_sum_self, h2, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1
    simpa using h1
  have key : ∀ j, r j = N * ((ω.repr a j : FiniteAdeleRing (𝓞 F) F) + c j) := by
    intro j
    rw [hrc j, hm j]
    push_cast
    ring
  refine ⟨(ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i, ?_, key i⟩
  intro M hM

  obtain ⟨z', c', hc'', hr'⟩ := hr i (M * N) (Nat.mul_pos hM hN)
  have hs : (ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i - M * c' ∈ intAdeles F :=
    sub_mem (add_mem (hint _) (hc' i)) (mul_mem (natCast_mem _ M) hc'')
  obtain ⟨a', ha'⟩ := dvd_of_eq F (z' : 𝓞 F) N hN _ hs (by
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((z' : 𝓞 F)) : F) =
        (z' : FiniteAdeleRing (𝓞 F) F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]
    have e2 : (z' : FiniteAdeleRing (𝓞 F) F) = r i - ((M * N : ℕ) : FiniteAdeleRing (𝓞 F) F) * c' := by
      rw [hr']
      ring
    rw [e1, e2, key i]
    push_cast
    ring)
  obtain ⟨t, ht⟩ := int_dvd F z' N a' ha'
  refine ⟨t, c', hc'', hu.mul_left_cancel ?_⟩
  rw [← key i, hr', ht]
  push_cast
  ring

end GlobalTheory.CoordDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasis
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.AdeleFree

section Abstract

variable {A : Type} [CommRing A]

def intClosure (O : Subring A) : Subring A where
  carrier := {r | ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r = (z : A) + (M : A) * c}
  mul_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    refine ⟨z * z', z * c' + c * z' + M * (c * c'), ?_, by push_cast; ring⟩
    exact add_mem (add_mem (mul_mem (intCast_mem _ _) hc') (mul_mem hc (intCast_mem _ _)))
      (mul_mem (natCast_mem _ _) (mul_mem hc hc'))
  one_mem' := fun M _ => ⟨1, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    exact ⟨z + z', c + c', add_mem hc hc', by push_cast; ring⟩
  zero_mem' := fun M _ => ⟨0, 0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    exact ⟨-z, -c, neg_mem hc, by push_cast; ring⟩

theorem intClosure_le (O : Subring A) {a : A} (ha : a ∈ intClosure O) : a ∈ O := by
  obtain ⟨z, c, hc, rfl⟩ := ha 1 one_pos
  exact add_mem (intCast_mem _ _) (by simpa using hc)

def ratSpan (Z : Subring A) : Subring A where
  carrier := {a | ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ Z}
  mul_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a * b) = (M * a) * (N * b) := by push_cast; ring
    rw [this]; exact mul_mem ha hb
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a + b) = N * (M * a) + M * (N * b) := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) ha) (mul_mem (natCast_mem _ _) hb)
  zero_mem' := ⟨1, one_pos, by simp⟩
  neg_mem' := by
    rintro a ⟨M, hM, ha⟩
    exact ⟨M, hM, by rw [mul_neg]; exact neg_mem ha⟩

theorem mem_ratSpan {Z : Subring A} {a : A} (ha : a ∈ Z) : a ∈ ratSpan Z :=
  ⟨1, one_pos, by simpa using ha⟩

theorem den_mul (φ : ℚ →+* A) (q : ℚ) : (q.den : A) * φ q = (q.num : A) := by
  rw [← map_natCast φ q.den, ← map_mul, Rat.den_mul_eq_num, map_intCast]

theorem rat_mem (φ : ℚ →+* A) (Z : Subring A) (q : ℚ) : φ q ∈ ratSpan Z :=
  ⟨q.den, q.den_pos, by rw [den_mul]; exact intCast_mem _ _⟩

theorem inv_mul (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) : φ (N : ℚ)⁻¹ * (N : A) = 1 := by
  rw [← map_natCast φ N, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]

theorem cancel (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) {a b : A} (h : (N : A) * a = N * b) :
    a = b :=
  calc a = (φ (N : ℚ)⁻¹ * N) * a := by rw [inv_mul φ hN, one_mul]
    _ = φ (N : ℚ)⁻¹ * (N * a) := mul_assoc _ _ _
    _ = φ (N : ℚ)⁻¹ * (N * b) := by rw [h]
    _ = b := by rw [← mul_assoc, inv_mul φ hN, one_mul]

theorem mem_of_mul (φ : ℚ →+* A) (O : Subring A)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    {N : ℕ} (hN : 0 < N) {c : A} (hc : c ∈ O) (h : (N : A) * c ∈ intClosure O) :
    c ∈ intClosure O := by
  intro M hM
  obtain ⟨z, d, hd, hzd⟩ := h (N * M) (Nat.mul_pos hN hM)
  have hz : (z : A) = N * (c - M * d) := by rw [mul_sub, hzd]; push_cast; ring
  obtain ⟨y, rfl⟩ := hint z N hN (c - M * d) (sub_mem hc (mul_mem (natCast_mem _ _) hd)) hz
  refine ⟨y, d, hd, cancel φ hN ?_⟩
  rw [hzd]; push_cast; ring

theorem exists_basis (φ : ℚ →+* A) (O : Subring A) [IsReduced A] {β : Type} [Fintype β]
    (w : β → A) (hw : ∀ i, w i ∈ O)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    (h0 : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c, c ∈ O ∧ a = (M : A) * c) → a = 0)
    (hden : ∀ a : A, ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ O)
    (hspan : ∀ a ∈ O, ∃ r : β → A, (∀ i, r i ∈ intClosure O) ∧ a = ∑ i, r i * w i)
    (hdiv : ∀ (r : β → A) (N : ℕ), 0 < N → (∀ i, r i ∈ intClosure O) →
      (∃ e, e ∈ O ∧ ∑ i, r i * w i = (N : A) * e) →
        ∀ i, ∃ s, s ∈ intClosure O ∧ r i = (N : A) * s) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R A)
      (b : Module.Basis β R A), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = w i) ∧
        ∀ a : A, a ∈ O ↔ ∀ i, b.repr a i ∈ R₀ := by
  classical

  set Z := intClosure O with hZdef
  set R := ratSpan Z with hRdef
  have hZO : ∀ x ∈ Z, x ∈ O := fun x hx => intClosure_le O hx
  have hZR : ∀ x ∈ Z, x ∈ R := fun x hx => mem_ratSpan hx
  let φR : ℚ →+* R := φ.codRestrict R (rat_mem φ Z)
  let _ : Algebra ℚ R := φR.toAlgebra
  let _ : Algebra R A := (Subring.subtype R).toAlgebra
  have hsmul : ∀ (c : R) (x : A), c • x = (c : A) * x := fun _ _ => rfl
  let R₀ : Subring R := Z.comap (Subring.subtype R)
  have hmemR : ∀ c : R, ∃ M : ℕ, 0 < M ∧ (M : A) * c ∈ Z := fun c => c.2

  have hli : LinearIndependent R w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    choose M hM hMc using fun j => hmemR (c j)
    set K := ∏ j, M j with hKdef
    have hK : 0 < K := Finset.prod_pos fun j _ => hM j
    have hr : ∀ j, (K : A) * c j ∈ Z := by
      intro j
      have hsplit : (K : A) * c j = ((∏ k ∈ Finset.univ.erase j, M k : ℕ) : A) * ((M j : A) * c j) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      rw [hsplit]
      exact mul_mem (natCast_mem _ _) (hMc j)
    have hc' : ∑ j, (c j : A) * w j = 0 := by simpa only [hsmul] using hc
    have hsum : ∑ j, ((K : A) * c j) * w j = 0 := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, hc', mul_zero]
    have hzero : (K : A) * c i = 0 := by
      apply h0
      intro N hN
      obtain ⟨s, hs, hrs⟩ := hdiv (fun j => (K : A) * c j) N hN hr
        ⟨0, zero_mem _, by rw [hsum, mul_zero]⟩ i
      exact ⟨s, hZO s hs, hrs⟩
    exact Subtype.ext (cancel φ hK (by rw [hzero]; simp))

  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    rintro a -
    obtain ⟨M, hM, hMa⟩ := hden a
    obtain ⟨r, hr, hra⟩ := hspan _ hMa
    have hmem : ∀ i, φ (M : ℚ)⁻¹ * r i ∈ R := fun i =>
      ⟨M, hM, by rw [← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]; exact hr i⟩
    have ha : a = ∑ i, (⟨φ (M : ℚ)⁻¹ * r i, hmem i⟩ : R) • w i := by
      simp only [hsmul]
      apply cancel φ hM
      rw [hra, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b : Module.Basis β R A := Module.Basis.mk hli hsp
  have hb : ∀ i, b i = w i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨R, inferInstance, inferInstance, R₀, inferInstance, b, ?_, ?_, hb, ?_⟩
  ·
    refine ⟨?_, ?_⟩
    · intro q hq
      have hq' : φ q ∈ Z := hq
      obtain ⟨z, c, hc, hzc⟩ := hq' q.den q.den_pos
      have h1 : ((q.num - q.den * z : ℤ) : A) = (q.den : A) * ((q.den : A) * c) := by
        push_cast
        rw [← den_mul φ q, hzc]
        ring
      have h2 := hint _ q.den q.den_pos _ (mul_mem (natCast_mem _ _) hc) h1
      have h3 : (q.den : ℤ) ∣ q.num := by
        have h4 := dvd_add h2 (dvd_mul_right (q.den : ℤ) z)
        simpa using h4
      have h5 : q.den = 1 :=
        Nat.eq_one_of_dvd_coprimes q.reduced.symm dvd_rfl (Int.natCast_dvd.mp h3)
      exact ⟨q.num, ((Rat.den_eq_one_iff q).mp h5).symm⟩
    · intro M hM r
      obtain ⟨K, hK, hKr⟩ := hmemR r
      obtain ⟨z, c, hc, hzc⟩ := hKr (K * M) (Nat.mul_pos hK hM)
      have hcZ : c ∈ Z := by
        apply mem_of_mul φ O hint (Nat.mul_pos hK hM) hc
        have hkm : ((K * M : ℕ) : A) * c = (K : A) * r - z := by rw [hzc]; ring
        rw [hkm]
        exact sub_mem hKr (intCast_mem _ _)
      refine ⟨(z : ℚ) / K, ⟨c, hZR c hcZ⟩, hcZ, ?_⟩
      apply Subtype.ext
      have hk : (K : A) * φ ((z : ℚ) / K) = z := by
        rw [← map_natCast φ K, ← map_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hK.ne'),
          map_intCast]
      change (r : A) = φ ((z : ℚ) / K) + (M : A) * c
      apply cancel φ hK
      rw [hzc, mul_add, hk]
      push_cast
      ring
  · exact isReduced_of_injective (Subring.subtype R) Subtype.val_injective
  · intro a
    have hrep : a = ∑ i, (b.repr a i : A) * w i := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [hsmul, hb]
    constructor
    · intro ha i
      obtain ⟨r, hr, hra⟩ := hspan a ha
      let c : β → R := fun j => ⟨r j, hZR _ (hr j)⟩
      have hdiff : ∑ j, (b.repr a j - c j) • b j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
        rw [sub_eq_zero]
        simp only [hsmul, hb]
        exact hra
      have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ hdiff i
      rw [sub_eq_zero.1 h]
      exact hr i
    · intro h
      rw [hrep]
      exact Subring.sum_mem _ fun i _ => mul_mem (hZO _ (h i)) (hw i)

end Abstract

theorem finiteAdele_free : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  intro F _ _ β _ ω
  classical
  obtain ⟨-, -, hz0, -, hden, hred⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  have : IsReduced (FiniteAdeleRing (𝓞 F) F) := hred
  let O : Subring (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.CoordDiv.intAdeles F
  have hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O,
      (z : FiniteAdeleRing (𝓞 F) F) = N * e → (N : ℤ) ∣ z := by
    intro z N hN e he h
    obtain ⟨a, ha⟩ := GlobalTheory.CoordDiv.dvd_of_eq F (z : 𝓞 F) N hN e he (by simpa using h)
    exact GlobalTheory.CoordDiv.int_dvd F z N a ha
  obtain ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, hmem⟩ :=
    exists_basis ((algebraMap F (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap ℚ F)) O
      (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F))
      (fun i => GlobalTheory.CoordDiv.algebraMap_mem F (ω i)) hint (fun a ha => hz0 a ha) (fun a => hden a)
      (fun a ha => GlobalTheory.ClassFin.exists_sum_integralBasis F β ω a ha)
      (fun r N hN hr he => GlobalTheory.CoordDiv.coord_divisible F β ω r N hN hr he)
  exact ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, fun a => hmem a⟩

end GlobalTheory.AdeleFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasisStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_pair_reduced_basis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  first | exact @GlobalTheory.AdeleFree.finiteAdele_free | exact GlobalTheory.AdeleFree.finiteAdele_free | (intros; apply GlobalTheory.AdeleFree.finiteAdele_free <;> assumption)
end
