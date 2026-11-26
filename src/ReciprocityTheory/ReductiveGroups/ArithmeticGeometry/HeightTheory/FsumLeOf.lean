module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SubstitutionVanishesOfRelation

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumLeOf
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem fsum_le_of {α : Type*} (s : Set α) (f g : α → ℤ) (hf : {x | x ∈ s ∧ f x ≠ 0}.Finite)
    (hg : {x | x ∈ s ∧ g x ≠ 0}.Finite) (r : ℝ) (hle : ∀ x ∈ s, (f x : ℝ) ≤ r * g x) :
    ((∑ᶠ x ∈ s, f x : ℤ) : ℝ) ≤ r * ((∑ᶠ x ∈ s, g x : ℤ) : ℝ) := by
  classical
  set u : Finset α := (hf.union hg).toFinset with hu
  have hus : ∀ x ∈ u, x ∈ s := by
    intro x hx
    simp only [hu, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with h | h
    · exact h.1
    · exact h.1
  have ef : ∑ᶠ x ∈ s, f x = ∑ x ∈ u, f x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  have eg : ∑ᶠ x ∈ s, g x = ∑ x ∈ u, g x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  rw [ef, eg, Int.cast_sum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => hle x (hus x hx)

theorem wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem pow_mem_ne (hd : d.AxH 𝒜) {G : WT} {ta : ∀ c, A c} (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (n : ℕ) : ∀ c, (ta ^ (n + 1)) c ∈ 𝒜 c ((n + 1) • G) ∧ (ta ^ (n + 1)) c ≠ 0 := by
  intro c
  haveI := hd.graded c
  induction n with
  | zero => simpa using hta c
  | succ n ih =>
    rw [pow_succ, Pi.mul_apply, succ_nsmul G (n + 1)]
    exact ⟨SetLike.mul_mem_graded ih.1 (hta c).1, hd.mul_ne_zero c ih.1 (hta c).1 ih.2 (hta c).2⟩

private lemma finsum_mem_const_mul {α : Type*} (s : Set α) (f : α → ℤ) (k : ℤ) (hk : k ≠ 0) :
    ∑ᶠ x ∈ s, k * f x = k * ∑ᶠ x ∈ s, f x := by
  classical
  have hs : s ∩ Function.support (fun x => k * f x) = s ∩ Function.support f := by
    ext x
    simp [hk]
  by_cases hf : (s ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq (fun x => k * f x) (t := hf.toFinset) (by
        ext x
        simp [hk]
        try tauto),
      finsum_mem_eq_sum_of_inter_support_eq f (t := hf.toFinset) (by
        ext x
        simp
        try tauto),
      Finset.mul_sum]
  · rw [finsum_mem_eq_zero_of_infinite hf, finsum_mem_eq_zero_of_infinite (by rwa [hs]), mul_zero]

private lemma nP_pow_succ_eq_succ_mul (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (n : ℕ) : d.nP h c ((n + 1) • G) ((ta ^ (n + 1)) c) p = ((n : ℤ) + 1) * d.nP h c G (ta c) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (ta ^ (n + 1 + 1)) c = (ta ^ (n + 1)) c * ta c := by rw [pow_succ, Pi.mul_apply]
    rw [e, succ_nsmul G (n + 1), d.nP_mul hd h c (d.pow_mem_ne hd hta n c).1 (hta c).1
      (d.pow_mem_ne hd hta n c).2 (hta c).2 hp, ih]
    push_cast
    ring

theorem aG_pow (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (n : ℕ) :
    d.aG h ((n + 1) • G) (ta ^ (n + 1)) = (n + 1) * d.aG h G ta := by
  unfold aG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← finsum_mem_const_mul _ (fun p => d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)) ((n : ℤ) + 1) (by positivity)]
  refine finsum_mem_congr rfl fun p hp => ?_
  rw [nP_pow_succ_eq_succ_mul d hd h hta c hp n, mul_assoc]

theorem aG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hord : ∀ c v, d.admitted c v → 0 ≤ d.ord c v G (ta c)) : 0 ≤ d.aG h G ta := by
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  refine finsum_nonneg fun p => finsum_nonneg fun hp => ?_
  exact mul_nonneg (d.nP_nonneg hd h c hp G (ta c) (hord c)) (by positivity)

private lemma ratio_zero_left {F0 V0 : Type*} [Field F0] [AddCommGroup V0] [Module F0 V0] {g : V0}
    (hg : g ≠ 0) : ratio (Ω := F0) (0 : V0) g = 0 := by
  unfold ratio
  split_ifs with h0
  · rcases smul_eq_zero.1 h0.choose_spec.symm with h1 | h1
    · exact h1
    · exact absurd h1 hg
  · rfl

theorem thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, he, -, hy⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := hy 1
  have key := hp c
  simp only [Pi.one_apply, mul_one] at key
  rw [Finset.sum_eq_zero] at key
  · exact hq c key
  · intro k _
    rw [hcon, ratio_zero_left (he c).2, map_zero, mul_zero]

theorem aG_sb (hd : d.AxH 𝒜) (h : d.S1) :
    d.aG h d.wL (fun c => d.w (d.jc c) c) =
      d.del + ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.Ep h c p * (d.dg (d.gen p) : ℤ) := by
  unfold aG del
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨F, -, -, -, h4, -⟩ := d.componentForm_properties hd h c
  have hf := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hE := d.Ep_ne hd h c _ (hd.w_mem _ c) (hd.w_base c)
  rw [← h4, ← finsum_mem_add_distrib']
  · exact finsum_mem_congr rfl fun p hp => by rw [d.nP_split hd h c hp]; ring
  · exact hf.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩
  · exact hE.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩

theorem aG_wx (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) :
    d.aG h d.wL (d.wx x) = d.aG h d.wL (fun c => d.w (d.jc c) c) :=
  (d.norm_factorization hd h).2.1 _ _ _ (fun c => ⟨d.wx_mem hd x c, hx c⟩) (fun c => ⟨hd.w_mem _ c, hd.w_base c⟩)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorStructure
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffPsiBNeZero
namespace ReciprocityTheory.ChartRestriction.G.T0.MHF

open MvPolynomial ReciprocityTheory.MultiplicativeHeights

variable {K : Type*} [Field K] {B n : ℕ}

def bw (b : Fin B) (s : Fin B × Fin n →₀ ℕ) : ℕ := ∑ j, s (b, j)

theorem bw_add (b : Fin B) (s t : Fin B × Fin n →₀ ℕ) : bw b (s + t) = bw b s + bw b t := by
  simp [bw, Finset.sum_add_distrib]

theorem bw_single (b : Fin B) (v : Fin B × Fin n) (e : ℕ) :
    bw b (Finsupp.single v e) = if v.1 = b then e else 0 := by
  obtain ⟨i, j⟩ := v
  by_cases h : i = b
  · subst h; simp [bw, Finsupp.single_apply]
  · simp [bw, h]

noncomputable def psiB (b : Fin B) :
    MvPolynomial (Fin B × Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin B × Fin n) K) :=
  aeval fun v => if v.1 = b then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiB_X (b : Fin B) (v : Fin B × Fin n) :
    psiB (K := K) b (X v) = Polynomial.C (X v) * Polynomial.X ^ (if v.1 = b then 1 else 0) := by
  simp only [psiB, aeval_X]; split_ifs <;> simp

theorem psiB_monomial (b : Fin B) (s : Fin B × Fin n →₀ ℕ) (a : K) :
    psiB b (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ bw b s := by
  induction s using Finsupp.induction generalizing a
  · simp [psiB, bw, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  · rename_i v e f _ _ ih
    rw [monomial_single_add, map_mul, map_pow, ih, psiB_X, bw_add, bw_single]
    split_ifs <;> simp only [map_mul, map_pow, mul_pow, ← pow_mul, pow_add, mul_one,
      pow_zero, zero_add] <;> ring

theorem psiB_eq_of_hom (b : Fin B) (δ : ℕ) (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ∀ s ∈ f.support, bw b s = δ) : psiB b f = Polynomial.C f * Polynomial.X ^ δ := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs => by rw [psiB_monomial, hf s hs]

theorem coeff_psiB_ne_zero (b : Fin B) (f : MvPolynomial (Fin B × Fin n) K)
    (s : Fin B × Fin n →₀ ℕ) (hs : s ∈ f.support) : (psiB b f).coeff (bw b s) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (AddMonoidAlgebra.coeff · s) h0
  conv at h1 => lhs; rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h1
  simp only [psiB_monomial, Polynomial.coeff_C_mul_X_pow, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
  rw [Finset.sum_eq_single s] at h1
  · simp at h1; exact (mem_support_iff.1 hs) h1
  · intro s' _ hne
    split_ifs <;> simp [coeff_monomial, hne]
  · intro h; exact absurd hs h

theorem ntd_pow {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).natTrailingDegree = m * p.natTrailingDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]

theorem isMH_of_pow (hB : 0 < B) (F0 : MvPolynomial (Fin B × Fin n) K) (κ : K) (m δ : ℕ)
    (hm : 1 ≤ m) (hκ : κ ≠ 0) (hF0 : F0 ≠ 0)
    (h : IsMultiHomogeneous (fun _ => δ) (C κ * F0 ^ m)) :
    ∃ d0, m * d0 = δ ∧ IsMultiHomogeneous (fun _ => d0) F0 := by
  classical
  have key : ∀ b : Fin B, ∃ k, m * k = δ ∧ ∀ s ∈ F0.support, bw b s = k := by
    intro b
    have h1 := psiB_eq_of_hom b δ _ (fun s hs => h s hs b)
    rw [map_mul, map_pow, show psiB b (C κ) = Polynomial.C (C κ) by
      simp [psiB, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply], map_mul] at h1
    have hCk : (Polynomial.C (C κ) : Polynomial (MvPolynomial (Fin B × Fin n) K)) ≠ 0 := by
      simp [hκ]
    have h2 : psiB b F0 ^ m = Polynomial.C (F0 ^ m) * Polynomial.X ^ δ := by
      apply mul_left_cancel₀ hCk
      rw [h1, map_pow]; ring
    obtain ⟨s0, hs0⟩ : F0.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.2 fun h0 => hF0 (support_eq_empty.1 h0)
    have hP : psiB b F0 ≠ 0 := fun h0 => coeff_psiB_ne_zero b F0 s0 hs0 (by rw [h0]; simp)
    have hFm : F0 ^ m ≠ 0 := pow_ne_zero _ hF0
    have hdeg := congrArg Polynomial.natDegree h2
    have htr := congrArg Polynomial.natTrailingDegree h2
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C_mul_X_pow _ _ hFm] at hdeg
    rw [ntd_pow _ hP, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hFm] at htr
    have heq : (psiB b F0).natDegree = (psiB b F0).natTrailingDegree :=
      Nat.eq_of_mul_eq_mul_left hm (hdeg.trans htr.symm)
    refine ⟨(psiB b F0).natDegree, hdeg, fun s hs => ?_⟩
    have hc := coeff_psiB_ne_zero b F0 s hs
    have h3 := Polynomial.le_natDegree_of_ne_zero hc
    have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
    omega
  obtain ⟨k0, hk0, -⟩ := key ⟨0, hB⟩
  refine ⟨k0, hk0, fun s hs b => ?_⟩
  obtain ⟨k, hk, hks⟩ := key b
  rw [show (∑ j, s (b, j)) = bw b s from rfl, hks s hs]
  exact Nat.eq_of_mul_eq_mul_left hm (hk.trans hk0.symm)

end ReciprocityTheory.ChartRestriction.G.T0.MHF
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem irreducible_factor_structure (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (κ : K)
      (a m deF : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ m * deF ≤ d.delc c ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d.delc c) ∧
      bilinearSubstitution (F c) = MvPolynomial.C κ * MvPolynomial.X (Sum.inr 0) ^ a * F1 ^ m ∧
      d.linearSubstitution c (bilinearSubstitution (F c)) = 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := by

  obtain ⟨F0, κ0, m0, hκ0, hm0, hirr0, hFeq, hker⟩ := d.fZ_eq_const_mul_irreducible_pow hd h c (F c) (hF c) hpos
  obtain ⟨F', hF', -, hmh', -⟩ := d.componentForm_properties hd h c
  have hFF : F c = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) ((hF c).trans hF'.symm)
  have hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := hFF ▸ hmh'
  have hmh1 : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (MvPolynomial.C κ0 * F0 ^ m0) := by
    rw [← hFeq]; exact hmh
  obtain ⟨d0, hd0, hmh0⟩ :=
    MHF.isMH_of_pow (Nat.succ_pos _) F0 κ0 m0 (d.delc c) hm0 hκ0 hirr0.ne_zero hmh1
  obtain ⟨a0, F1, deF, hG0, hirr1, hxh, hdeF, hU⟩ := d.substitution_split_irreducible hd c F0 hirr0 d0 hmh0 hker
  have hg : bilinearSubstitution (F c) = MvPolynomial.C κ0 * bilinearSubstitution F0 ^ m0 := by
    rw [hFeq]; simp only [bilinearSubstitution, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  refine ⟨F1, κ0, a0 * m0, m0, deF, hκ0, hm0, ?_, hirr1, hxh, ?_, ?_, ?_, hmh⟩
  · calc m0 * deF ≤ m0 * d0 := Nat.mul_le_mul_left _ hdeF
      _ = d.delc c := hd0
  · intro s hs
    refine (hU s hs).trans (Nat.mul_le_mul_left _ ?_)
    calc d0 ≤ m0 * d0 := Nat.le_mul_of_pos_left _ hm0
      _ = d.delc c := hd0
  · rw [hg, hG0, mul_pow, pow_mul]; ring
  · rw [hg, map_mul, map_pow, d.substitution_vanishes_of_relation hd c F0 ((hker F0).2 dvd_rfl), zero_pow (by omega), mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
