module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem hom_two {n : ℕ} {A : Type} [CommRing A] (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
  classical
  have hd : ∀ d ∈ P.support, d 0 + d 1 = n := fun d hd => by
    have h := hP (MvPolynomial.mem_support_iff.1 hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [Fin.sum_univ_two] using h
  refine ⟨fun i => ∑ d ∈ P.support with d 1 = i, P.coeff d, fun S _ _ s t => ?_⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n + 1)) (g := fun d => d 1)
      (fun d h => by have := hd d h; simp only [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d h => ?_
  rw [Finset.mem_filter] at h
  have h0 : d 0 = n - i := by have := hd d h.1; have := h.2; omega
  simp [Fin.prod_univ_two, h0, h.2, mul_assoc]

private theorem lam_two {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E)
    (S : Type) [CommRing S] [Algebra A S] (s t : S) :
    D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (D.lam i x) * s ^ (n - i) * t ^ i := by
  obtain ⟨h1, h2⟩ := d_poly D ![1, x]
  obtain ⟨c, hc⟩ := hom_two _ h1
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
    intro S _ _ s t
    rw [← hc, ← h2]
    simp [Fin.sum_univ_two]
  have hl : ∀ j ∈ Finset.range (n + 1), D.lam j x = c j := by
    intro j hj
    have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * c i) * X ^ (n - i) := by
      rw [Det.chi, sub_eq_add_neg, ← neg_tmul, key]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
        map_one]
      ring
    rw [Det.lam, hchi, finsetSum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl, ← mul_assoc, ← mul_pow]; simp
    · intro i hi hij
      have : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro h; exact absurd hj h
  rw [key]
  exact Finset.sum_congr rfl fun i hi => by rw [hl i hi]

theorem UpperTheory.V.CA.d_chi :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), D.lam 0 x = 1 ∧ D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) ∧ D.D A[X] (1 + X ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), C (D.lam i x) * X ^ i ∧ D.lam n x = D.val x ∧ (D.chi x).Monic ∧ (D.chi x).natDegree ≤ n ∧ ∀ (a : A) (i : ℕ), i ≤ n → D.lam i (a • x) = a ^ i * D.lam i x := by
  intro n A E _ _ _ D x
  have h0 : D.lam 0 x = 1 := by
    have h := lam_two D x A 1 0
    rw [zero_tmul, add_zero, ← Algebra.TensorProduct.one_def, map_one, Finset.sum_range_succ'] at h
    simpa using h.symm
  have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) := by
    conv_lhs => rw [Det.chi, sub_eq_add_neg, ← neg_tmul, lam_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
      map_one]
    ring
  have h1 : ∀ y : E, D.D A[X] (1 + X ⊗ₜ y) = ∑ i ∈ Finset.range (n + 1), C (D.lam i y) * X ^ i := by
    intro y
    rw [Algebra.TensorProduct.one_def, lam_two]
    simp
  have hdeg : (D.chi x).natDegree ≤ n := by
    rw [hchi]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  refine ⟨h0, hchi, h1 x, ?_, ?_, hdeg, ?_⟩
  · have h := lam_two D x A 0 1
    rw [zero_tmul, zero_add, Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
      have : n - i ≠ 0 := by rw [Finset.mem_range] at hi; omega
      simp [this])] at h
    change _ = D.D A (1 ⊗ₜ x)
    rw [h]; simp
  · refine monic_of_natDegree_le_of_coeff_eq_one n hdeg ?_
    simpa [Det.lam] using h0
  · intro a j hj
    have h := h1 (a • x)
    rw [← smul_tmul, Algebra.TensorProduct.one_def, lam_two] at h
    have h' : ∑ i ∈ Finset.range (n + 1), C (a ^ i * D.lam i x) * X ^ i =
        ∑ i ∈ Finset.range (n + 1), C (D.lam i (a • x)) * X ^ i := by
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow,
        smul_eq_C_mul]
      ring
    have h2 := congrArg (fun p => p.coeff j) h'
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hj,
      if_true] at h2
    exact h2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem chiS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y) = (D.chiS S y).map (f : S →+* T) := by
  have h := D.nat (Polynomial S) (Polynomial T) (Polynomial.mapAlgHom f) (Polynomial.X ⊗ₜ 1 -
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y)
  refine Eq.trans ?_ h
  unfold Det.chiS
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y with
    | tmul s x => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem F_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    Polynomial.aeval (Algebra.TensorProduct.map f (AlgHom.id A E) y)
      (D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y)) =
      Algebra.TensorProduct.map f (AlgHom.id A E) (Polynomial.aeval y (D.chiS S y)) := by
  rw [chiS_map]
  generalize D.chiS S y = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), hp, hq]
  | monomial k a =>
    simp [Polynomial.aeval_monomial, Algebra.TensorProduct.algebraMap_apply]

private theorem expand {ι : Type} (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S)
    (N : Set E) (w : MvPolynomial ι A ⊗[A] E)
    (h : ∀ α, TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) ∈ N) :
    Algebra.TensorProduct.map f (AlgHom.id A E) w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  classical
  have hw : ∃ s : Finset (ι →₀ ℕ), ∀ t, s ⊆ t → w = ∑ α ∈ t, (MvPolynomial.monomial α (1 : A)) ⊗ₜ[A]
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) := by
    clear h
    induction w with
    | add a b ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s ∪ s', fun t ht => ?_⟩
      simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib]
      rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
    | tmul p z =>
      refine ⟨p.support, fun t ht => ?_⟩
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, MvPolynomial.lcoeff_apply, ← smul_tmul,
        ← sum_tmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      congr 1
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_subset ht fun α _ hα => ?_
      rw [MvPolynomial.notMem_support_iff.1 hα, map_zero]
  obtain ⟨s, hs⟩ := hw
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs s le_rfl, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [Algebra.TensorProduct.map_tmul, ← mul_one (f _), ← smul_eq_mul, ← smul_tmul']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h α, rfl⟩)

private theorem part1 (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    Polynomial.aeval y (D.chiS S y) ∈
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  obtain ⟨k, s, x, rfl⟩ := TensorProduct.exists_sum_tmul_eq y
  have : ∑ j, s j ⊗ₜ[A] x j =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen (A := A) x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum]
  rw [this, F_map]
  exact expand S _ _ _ fun α => TwoSidedIdeal.subset_span ⟨k, x, α, rfl⟩

private theorem rT_mem (P S : Type) [CommRing P] [Algebra A P] [CommRing S] [Algebra A S] (g : P →ₗ[A] S)
    (N : Set E) (w : P ⊗[A] E) (h : w ∈ Submodule.span P ((fun z : E => (1 : P) ⊗ₜ[A] z) '' N)) :
    g.rTensor E w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  suffices H : ∀ p : P, g.rTensor E (p • w) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) by
    simpa using H 1
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    intro p
    rw [smul_tmul', LinearMap.rTensor_tmul, ← mul_one (g _), ← smul_eq_mul, ← smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz, rfl⟩)
  | zero => intro p; simp
  | add x y _ _ hx hy => intro p; rw [smul_add, map_add (f := _)]; exact add_mem (hx p) (hy p)
  | smul a x _ hx => intro p; rw [smul_smul]; exact hx _

private theorem chElt_bc (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → S ⊗[A] E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt x α = ((MvPolynomial.lcoeff S α).restrictScalars A).rTensor E
      (Polynomial.aeval (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x))
        (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x)))) := by
  unfold Det.chElt
  generalize Det.gen (A := S) x = y
  have h1 : (D.baseChange S).chiS (MvPolynomial (Fin k) S) y =
      D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y) := by
    unfold Det.chiS
    rw [(d_bc D S).1]
    congr 1
    rw [map_sub]
    congr 1
    · rw [Algebra.TensorProduct.one_def, Det.cancel_tmul]; simp
    · induction y with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        induction y with
        | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
        | tmul b z => simp [Det.cancel_tmul]
  rw [h1, Polynomial.aeval_algHom_apply]
  generalize Polynomial.aeval y (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y)) = w
  induction w with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s y =>
    induction y with
    | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
    | tmul b z =>
      rw [Det.cancel_tmul, mul_comm]
      simp [smul_tmul', MvPolynomial.coeff_C_mul, mul_comm b]

private theorem chElt_one (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt (fun i => (1 : S) ⊗ₜ[A] x i) α = (1 : S) ⊗ₜ[A] D.chElt x α := by
  rw [chElt_bc]
  have : Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen fun i => (1 : S) ⊗ₜ[A] x i) =
      Algebra.TensorProduct.map (MvPolynomial.mapAlgHom (Algebra.ofId A S)) (AlgHom.id A E)
        (Det.gen (A := A) x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum, Det.cancel_tmul]
  rw [this, F_map]
  unfold Det.chElt
  generalize Polynomial.aeval (Det.gen (A := A) x) (D.chiS (MvPolynomial (Fin k) A) (Det.gen x)) = w
  induction w with
  | add a b ha hb => simp only [map_add (f := _), tmul_add, ha, hb]
  | tmul s y =>
    simp [MvPolynomial.coeff_map, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem span_mul (S : Type) [CommRing S] [Algebra A S] (I : TwoSidedIdeal E) (w : S ⊗[A] E)
    (h : w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E))) (u : S ⊗[A] E) :
    u * w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) ∧
    w * u ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    induction u with
    | add a b ha hb => rw [add_mul, mul_add]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
    | tmul s e =>
      have key : ∀ t ∈ I, s ⊗ₜ[A] t ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
        intro t ht
        rw [← mul_one s, ← smul_eq_mul, ← smul_tmul']
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht, rfl⟩)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact ⟨key _ (I.mul_mem_left _ _ hz), key _ (I.mul_mem_right _ _ hz)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, mul_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    rw [mul_smul_comm, smul_mul_assoc]
    exact ⟨Submodule.smul_mem _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩

private theorem part2 (S : Type) [CommRing S] [Algebra A S] :
    ((D.baseChange S).CH : Set (S ⊗[A] E)) =
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  ext w
  simp only [SetLike.mem_coe]
  constructor
  · intro h
    unfold Det.CH at h
    induction h using TwoSidedIdeal.span_induction with
    | mem x hx =>
      obtain ⟨k, x, α, rfl⟩ := hx
      rw [chElt_bc]
      exact rT_mem _ _ _ _ _ (part1 D _ _)
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | left_absorb a x _ hx => exact (span_mul S _ _ hx a).1
    | right_absorb b x _ hx => exact (span_mul S _ _ hx b).2
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      change z ∈ TwoSidedIdeal.span _ at hz
      induction hz using TwoSidedIdeal.span_induction with
      | mem x hx =>
        obtain ⟨k, x, α, rfl⟩ := hx
        exact TwoSidedIdeal.subset_span ⟨k, _, α, (chElt_one D S x α).symm⟩
      | zero => simp
      | add x y _ _ hx hy => simp only [tmul_add]; exact add_mem hx hy
      | neg x _ hx => simp only [tmul_neg]; exact neg_mem hx
      | left_absorb a x _ hx =>
        have := TwoSidedIdeal.mul_mem_left _ ((1 : S) ⊗ₜ[A] a) _ hx
        simpa using this
      | right_absorb b x _ hx =>
        have := TwoSidedIdeal.mul_mem_right _ _ ((1 : S) ⊗ₜ[A] b) hx
        simpa using this
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx

end

theorem UpperTheory.V.CA.d_chS :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S], (∀ y : S ⊗[A] E, Polynomial.aeval y (D.chiS S y) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E))) ∧ ((D.baseChange S).CH : Set (S ⊗[A] E)) = Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) ∧ (D.IsCH → (D.baseChange S).IsCH ∧ ∀ x : E, Polynomial.aeval x (D.chi x) = 0) := by
  intro n A E _ _ _ D S _ _
  refine ⟨part1 D S, part2 D S, fun h => ?_⟩
  have hb : ∀ (T : Type) [CommRing T] [Algebra A T],
      Submodule.span T ((fun z : E => (1 : T) ⊗ₜ[A] z) '' (D.CH : Set E)) = ⊥ := by
    intro T _ _
    rw [Submodule.span_eq_bot]
    rintro _ ⟨z, hz, rfl⟩
    rw [show D.CH = ⊥ from h] at hz
    have : z = 0 := by simpa using hz
    simp [this]
  refine ⟨?_, fun x => ?_⟩
  · refine eq_bot_iff.2 fun w hw => ?_
    have : w ∈ ((D.baseChange S).CH : Set (S ⊗[A] E)) := hw
    rw [part2, hb] at this
    simpa using this
  · have h1 := part1 D A (1 ⊗ₜ x)
    rw [hb, Submodule.mem_bot] at h1
    have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
    rw [h2] at h1
    have h3 := congrArg (Algebra.TensorProduct.lid A E) h1
    rw [← Polynomial.aeval_algHom_apply] at h3
    simpa using h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cm_of_regular (A : Type) [CommRing A] [IsRegularLocalRing A] : ReciprocityTheory.CA.IsCM A := by
  obtain ⟨xs, hspan, hlen, hreg⟩ :=
    PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal A
  refine ⟨inferInstance, xs.length, hlen.symm, xs, rfl, fun r hr => ?_, hreg⟩
  rw [← hspan]
  exact Ideal.subset_span hr

theorem UpperTheory.V.CA.cl_cm :
    (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (d : ℕ), IsCM (MvPowerSeries (Fin d) O) ∧ ringKrullDim (MvPowerSeries (Fin d) O) = (d + 1 : ℕ)) ∧ ∀ (k : Type) [Field k] (d : ℕ), IsCM (MvPowerSeries (Fin d) k) ∧ ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  refine ⟨fun O _ _ _ _ d => ⟨?_, ?_⟩, fun k _ d => ⟨?_, ?_⟩⟩
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) O) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    push_cast
    rfl
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) k) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GammaOneGammaZeroHomogeneousCocyclesFinite
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem module_finite_z1_padicInt (l : ℕ) [Fact l.Prime] {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ ψ : G →* kˣ) (hΦ : PhiCond (Γ := G) l)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G)) : Finite (Z1 χ ψ) := by
  classical
  letI := ZMod.algebra k l
  haveI : Module.Finite (ZMod l) k := Module.Finite.of_finite
  let N : Subgroup G := χ.ker ⊓ ψ.ker
  have hNo : IsOpen (N : Set G) := by
    show IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G)
    rw [Subgroup.coe_inf]
    exact hχ.inter hψ
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  haveI := hΦ N hNo
  let b := Module.finBasis (ZMod l) k
  have mem : ∀ a ∈ Z1 χ ψ, IsLocallyConstant a ∧
      ∀ g h : G, a (g * h) = (χ g : k) * a h + a g * (ψ h : k) := fun a ha => ha
  have hadd : ∀ a ∈ Z1 χ ψ, ∀ x y : N, a ((x : G) * (y : G)) = a x + a y := by
    intro a ha x y
    have hx : χ (x : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).1
    have hy : ψ (y : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2
    rw [(mem a ha).2, hx, hy]
    simp [add_comm]
  let φ : ∀ a ∈ Z1 χ ψ, Fin (Module.finrank (ZMod l) k) → (N →* Multiplicative (ZMod l)) :=
    fun a ha i => MonoidHom.mk' (fun x => Multiplicative.ofAdd (b.repr (a x) i)) (by
      intro x y
      simp [hadd a ha x y, ofAdd_add])
  have hφo : ∀ a (ha : a ∈ Z1 χ ψ) i, IsOpen ((φ a ha i).ker : Set N) := by
    intro a ha i
    have hlc : IsLocallyConstant (fun x : N => b.repr (a x) i) :=
      ((mem a ha).1.comp_continuous continuous_subtype_val).comp (fun y => b.repr y i)
    have e : ((φ a ha i).ker : Set N) = {x | (fun x : N => b.repr (a x) i) x = 0} := by
      ext x
      simp [φ, MonoidHom.mem_ker]
    rw [e]
    exact hlc.isOpen_fiber 0
  let F : Z1 χ ψ → (G ⧸ N → k) ×
      (Fin (Module.finrank (ZMod l) k) → {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}) :=
    fun a => (fun q => (a : G → k) q.out, fun i => ⟨φ a a.2 i, hφo a a.2 i⟩)
  refine Finite.of_injective F ?_
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hN' : ∀ x : N, a x = a' x := by
    intro x
    apply b.repr.injective
    ext i
    exact congrArg (fun f => Multiplicative.toAdd ((f i).1 x)) h2
  apply Subtype.ext
  funext g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  have e1 : a (QuotientGroup.mk g : G ⧸ N).out = a' (QuotientGroup.mk g : G ⧸ N).out := congrFun h1 _
  have hg : g = (QuotientGroup.mk g : G ⧸ N).out * ((n⁻¹ : N) : G) := by
    rw [hn]; simp [mul_assoc]
  show a g = a' g
  rw [hg, (mem a ha).2, (mem a' ha').2, hN' n⁻¹, e1]

theorem UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars :
    ∀ (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ h, MultFree χ h := by
  intro l _ n k G _ _ _ _ _ _ _ _ χ hΦ hopen hinj
  refine ⟨∑ i, ∑ j, Module.finrank k (Z1 (χ i) (χ j)), hopen, hinj, fun i j _ => ?_⟩
  haveI := module_finite_z1_padicInt l (χ i) (χ j) hΦ (hopen i) (hopen j)
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank k (Z1 (χ i) (χ j)) ≤ ∑ j', Module.finrank k (Z1 (χ i) (χ j')) :=
        Finset.single_le_sum (f := fun j' => Module.finrank k (Z1 (χ i) (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Module.finrank k (Z1 (χ i') (χ j')) :=
        Finset.single_le_sum (f := fun i' => ∑ j', Module.finrank k (Z1 (χ i') (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevelOfCongruence
private theorem UpperTheory.Reformulated.B.LevelOfCongruence.level {C R T : Type} [CommRing C] [CommRing R] [CommRing T]
    (a : C →+* R) (f : C →+* T) (M : Ideal R) (K : Ideal T)
    (hd : ∀ r : R, ∃ c, r - a c ∈ M) (hk : ∀ c, a c ∈ M → f c ∈ K) :
    ∃ g : R →+* T ⧸ K, ∀ r c, r - a c ∈ M → g r = Ideal.Quotient.mk K (f c) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk M).comp a) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hd r
    exact ⟨c, (Ideal.Quotient.eq.2 hc).symm⟩
  have hker : RingHom.ker ((Ideal.Quotient.mk M).comp a) ≤
      RingHom.ker ((Ideal.Quotient.mk K).comp f) := by
    intro c hc
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
    exact hk c hc
  refine ⟨(RingHom.liftOfSurjective _ hs ⟨_, hker⟩).comp (Ideal.Quotient.mk M), ?_⟩
  intro r c hc
  rw [RingHom.comp_apply, Ideal.Quotient.eq.2 hc]
  exact RingHom.liftOfSurjective_comp_apply _ hs ⟨_, hker⟩ c

theorem UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex :
    ∀ {C R : Type} [inst : CommRing C] [inst_1 : CommRing R] [inst_2 : Algebra C R] [inst_3 : IsLocalRing R] {x : Ideal C},
      UpperTheory.V.CA.IsCplAt x R →
        ∀ {T : Type} [inst_4 : CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T),
          x ≤ Ideal.comap f J →
            ∃ (F : R →+* T), F.comp (Algebra.algebraMap C R) = f ∧ IsLocalRing.maximalIdeal R ≤ Ideal.comap F J := by
  intro C R _ _ _ _ x h T _ J _ f hx
  have hk : ∀ (n : ℕ) (c : C), algebraMap C R c ∈ IsLocalRing.maximalIdeal R ^ n → f c ∈ J ^ n := by
    intro n c hc
    have h1 : c ∈ x ^ n := by
      rw [← h.comap_pow n]
      exact hc
    exact Ideal.le_comap_pow f n (Ideal.pow_right_mono hx n h1)
  choose g hg using fun n : ℕ => UpperTheory.Reformulated.B.LevelOfCongruence.level (algebraMap C R) f
    (IsLocalRing.maximalIdeal R ^ n) (J ^ n) (h.dense n) (hk n)
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (g n) = g m := by
    intro m n hle
    ext r
    obtain ⟨c, hc⟩ := h.dense n r
    rw [RingHom.comp_apply, hg n r c hc, hg m r c (Ideal.pow_le_pow_right hle hc)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J g hc, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' J
    intro n c
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom]
    exact hg n _ c (by simp)
  · intro r hr
    have h0 := IsAdicComplete.mk_liftRingHom J g hc 1 r
    rw [hg 1 r 0 (by simpa using hr), map_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      pow_one] at h0
    exact h0
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cu_uniq {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (F G : R →+* T)
    (e : F.comp (algebraMap C R) = G.comp (algebraMap C R))
    (hF : maximalIdeal R ≤ J.comap F) (hG : maximalIdeal R ≤ J.comap G) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n r
  obtain ⟨c, hc⟩ := h.dense n r
  have h1 : F (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow F n (Ideal.pow_right_mono hF n hc)
  have h2 : G (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow G n (Ideal.pow_right_mono hG n hc)
  have h3 : F (algebraMap C R c) = G (algebraMap C R c) := RingHom.congr_fun e c
  rw [Ideal.Quotient.eq]
  have := sub_mem h1 h2
  rw [map_sub, map_sub, h3] at this
  simpa using this

private theorem cu_ex {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T)
    (hf : x ≤ J.comap f) :
    ∃ F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F :=
  _root_.UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex h J f hf

private theorem cu_le {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x ≤ (maximalIdeal R).comap (algebraMap C R) := by
  have := h.comap_pow 1
  rw [pow_one, pow_one] at this
  exact this.ge

private theorem cu_map {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x.map (algebraMap C R) = maximalIdeal R := by
  haveI := h.noeth
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cu_le h)) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) fun r hr => ?_
  obtain ⟨c, hc⟩ := h.dense 2 r
  have h1 : algebraMap C R c ∈ maximalIdeal R := by
    have := sub_mem hr (Ideal.pow_le_self two_ne_zero hc)
    simpa using this
  have h2 : c ∈ x := by
    have := h.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← this]; exact h1
  have h3 : r = algebraMap C R c + (r - algebraMap C R c) := by ring
  rw [h3]
  refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h2) ?_
  rw [smul_eq_mul, ← pow_two]
  exact hc

private theorem cu_equiv {C R S : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R]
    [CommRing S] [Algebra C S] [IsLocalRing S] {x : Ideal C}
    (h : IsCplAt x R) (h' : IsCplAt x S) : Nonempty (R ≃ₐ[C] S) := by
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨F, hF1, hF2⟩ := cu_ex h (maximalIdeal S) (algebraMap C S) (cu_le h')
  obtain ⟨G, hG1, hG2⟩ := cu_ex h' (maximalIdeal R) (algebraMap C R) (cu_le h)
  have e1 : G.comp F = RingHom.id R :=
    cu_uniq h (maximalIdeal R) _ _ (by rw [RingHom.comp_assoc, hF1, hG1, RingHom.id_comp])
      (fun r hr => hG2 (hF2 hr)) (fun r hr => hr)
  have e2 : F.comp G = RingHom.id S :=
    cu_uniq h' (maximalIdeal S) _ _ (by rw [RingHom.comp_assoc, hG1, hF1, RingHom.id_comp])
      (fun r hr => hF2 (hG2 hr)) (fun r hr => hr)
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G e2 e1) fun c => RingHom.congr_fun hF1 c⟩

theorem UpperTheory.V.CA.cpl_uniq :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ (T : Type) [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T), x ≤ J.comap f → ∃! F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F) ∧ Nonempty (R ≃ₐ[C] Cpl x) ∧ x.map (algebraMap C R) = maximalIdeal R := by
  intro C R _ _ _ _ _ x _ h
  refine ⟨fun T _ J _ f hf => ?_, ?_, cu_map h⟩
  · obtain ⟨F, hF⟩ := cu_ex h J f hf
    exact ⟨F, hF, fun G hG => cu_uniq h J G F (hG.1.trans hF.1.symm) hG.2 hF.2⟩
  · obtain ⟨_, h'⟩ := cpl_is C x
    exact cu_equiv h h'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CoCoprod
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem co_coprod_pres (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ W : WPres O Unit R, ∀ s, W.z s ∈ maximalIdeal R := by
  obtain ⟨n, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (maximalIdeal R))
  have hm : ∀ s, z s ∈ maximalIdeal R := fun s => hz ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI : IsCO O (MvPowerSeries (Fin n) O) := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R (Fin n) (Algebra.ofId _ _) z hm
  refine ⟨⟨Fin n, fun _ => (), F, ?_, ?_⟩, fun s => ?_⟩
  · refine co_surj O _ R _ (le_trans ?_ le_sup_left)
    rw [← hz, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [← hF s]
    refine Ideal.mem_map_of_mem _ fun hu => ?_
    simpa using MvPowerSeries.isUnit_constantCoeff _ hu
  · intro g hg j
    have : wcomp O (fun _ : Fin n => ()) j g = g := by
      ext a
      rw [coeff_wcomp, if_pos (Subsingleton.elim _ _)]
    rwa [this]
  · show F (MvPowerSeries.X s) ∈ _
    rw [hF]
    exact hm s

theorem UpperTheory.V.CA.co_coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (T : Type) [Finite T] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra O (B t)] [∀ t, IsCO O (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : ∀ t, B t →ₐ[O] R), ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ t, B t →ₐ[O] R'), ∃! g : R →ₐ[O] R', ∀ t, g.comp (j t) = f t := by
  intro O _ _ _ _ T _ B _ _ _
  haveI := Fintype.ofFinite T
  choose WB hWB using fun t => co_coprod_pres O (B t)
  obtain ⟨R, i1, i2, i3, i, _, _, h, -⟩ := UpperTheory.V.Alg.coprod O Unit T B WB hWB
  exact ⟨R, i1, i2, i3, i, h⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairMap
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem UpperTheory.V.CA.pair_map :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R) (f : R →ₐ[O] R'), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ _ _ _ _ n r R R' _ _ _ _ _ _ p f
  have hl : ∀ i y, (p.D.map (f : R →+* R')).lam i (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = f (p.D.lam i y) :=
    fun i y => ((d_gmap p.D).2.2.1 (f : R →+* R') y).2 i
  have h1 : ∀ g : F.G₀, MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single g 1 := fun g => by rw [MonoidAlgebra.mapRingHom_single, map_one]
  refine ⟨{ D := p.D.map (f : R →+* R'), ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i),
            cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, rfl, fun _ _ => rfl⟩
  · intro i
    have := adic_map f (p.cont i)
    simpa only [← hl, h1] using this
  · rw [(d_gmap p.D).2.1, ← p.red]
    congr 1
    ext x
    exact res_map f x
  · intro v i
    refine ⟨adic_map f (p.psi v i).cont, fun g => (res_map f _).trans ((p.psi v i).red g), fun g => ?_⟩
    change f (p.ψ v i g : R) = _
    rw [(p.psi v i).mu g, f.commutes]
  · intro i g
    have hs : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      rw [star_single, star_single, MonoidAlgebra.mapRingHom_single]
      congr 1
      have he : F.eps O R' g = Units.map ((f : R →+* R') : R →* R') (F.eps O R g) :=
        Units.ext (f.commutes _).symm
      rw [he, ← map_zpow]
      rfl
    rw [hs, hl, p.P, ← hl, h1]
  · intro v g h
    have ho : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      rw [map_mul, h1, GFrame.oEl, GFrame.oEl, map_list_prod, List.map_ofFn]
      congr 3
      funext i
      simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    have := p.Ord v g h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
  · intro u g hg h
    have ho : (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1) : MonoidAlgebra R' F.G₀) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      rw [map_mul, map_sub, h1, h1, map_one]
    have := p.I u g hg h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FChars
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private noncomputable def piB {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] : MonoidAlgebra B G →ₐ[B] (Fin n → B) :=
  MonoidAlgebra.lift B (Fin n → B) G
    { toFun := fun g i => algebraMap k B (χ i g)
      map_one' := by ext i; simp
      map_mul' := fun g h => by ext i; simp }

private theorem piB_single {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (g : G) (b : B) (i : Fin n) :
    piB χ B (MonoidAlgebra.single g b) i = b * algebraMap k B (χ i g) := by
  simp [piB]

private theorem piB_map {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (y : MonoidAlgebra k G) (i : Fin n) :
    piB χ B (MonoidAlgebra.mapRingHom G (algebraMap k B) y) i = algebraMap k B (piB χ k y i) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  | single g r => rw [MonoidAlgebra.mapRingHom_single, piB_single, piB_single]; simp

private theorem D_eq {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (x : MonoidAlgebra B G) :
    (GDet.ofChars χ).D B x = ∏ i, piB χ B x i := by
  change (GDet.repAlg (GDet.diagRep χ) B x).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [Pi.zero_def]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.diagonal_add]; rfl
  | single g r =>
    ext i j
    by_cases h : i = j
    · subst h; simp [GDet.repAlg, GDet.diagRep, piB_single]
    · simp [GDet.repAlg, GDet.diagRep, Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.V.CA.f_chars :
    ∀ {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ), Function.Injective χ → ∃ π : MonoidAlgebra k G →ₐ[k] (Fin n → k), Function.Surjective π ∧ (∀ g i, π (MonoidAlgebra.single g 1) i = χ i g) ∧ (∀ y, (GDet.ofChars χ).Kills y ↔ π y = 0) ∧ ∀ y, (GDet.ofChars χ).chi y = ∏ i, (X - C (π y i)) := by
  intro n k G _ _ χ hχ
  have hs : ∀ g i, piB χ k (MonoidAlgebra.single g 1) i = χ i g := fun g i => by simp [piB_single]
  have hsurj : Function.Surjective (piB χ k) := by
    have hinj : Function.Injective fun i => (Units.coeHom k).comp (χ i) := fun i j h =>
      hχ (MonoidHom.ext fun g => Units.ext (DFunLike.congr_fun h g))
    have hli : LinearIndependent k fun i (g : G) => (χ i g : k) :=
      (linearIndependent_monoidHom G k).comp _ hinj
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range (piB χ k).toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, funext (hs g)⟩
    exact LinearMap.range_eq_top.1 this
  refine ⟨piB χ k, hsurj, hs, fun y => ⟨fun h => ?_, fun h B _ _ z => ?_⟩, fun y => ?_⟩
  · ext i
    by_contra hi
    obtain ⟨z, hz⟩ := hsurj fun _ => -(piB χ k y i)⁻¹
    have := h k z
    rw [D_eq, Finset.prod_eq_zero (Finset.mem_univ i)] at this
    · exact zero_ne_one this
    · rw [map_add (f := _), map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, hz]
      have hi' : piB χ k y i ≠ 0 := hi
      simp [hi']
  · rw [D_eq]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_add (f := _), map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, h]
    simp
  · unfold GDet.chi
    rw [D_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub, Pi.sub_apply, piB_single]
    have := piB_map χ k[X] y i
    rw [Polynomial.algebraMap_eq] at this
    rw [this]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UniversalDeformationRingLocalCharacters
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* Rˣ) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => (ψ g : R)
  map_one' := by ext a b; simp
  map_mul' g h := by ext a b; simp [Matrix.mul_apply]

private noncomputable def ofMat {G R : Type} [Group G] [CommRing R] (ρ : G →* Matrix Unit Unit R) : G →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ρ g () ()
      map_one' := by simp
      map_mul' := fun g h => by simp [Matrix.mul_apply] }

private theorem lc_of_open {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : k) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  have h2 : (x - 1) ^ l ^ m = 0 := by rw [sub_pow_char_pow, h]; simp
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero) |>.1 h2)

private theorem psib_th {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v) :
    ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) = residue O (r.th v i g) := by
  obtain ⟨m, hm⟩ := (CommGroup.primaryComponent.isPGroup (G := TopologicalAbelianization (F.Gv v)) (p := l))
    ⟨QuotientGroup.mk' _ (g : F.Gv v), g.2⟩
  have h1 : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure ((g : F.Gv v) ^ l ^ m)) = 1 := by
    rw [map_pow]; exact congrArg Subtype.val hm
  have h2 : (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
  have h4 : r.psib v i g ^ l ^ m = 1 := by rw [← map_pow]; exact h3 h2
  have h5 : r.th v i g ^ l ^ m = 1 := by rw [← map_pow]; exact r.th_comm v i _ h2
  rw [eq_one_of_pow l ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) m
      (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]),
    eq_one_of_pow l (residue O (r.th v i g)) m
      (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h5, Units.val_one, map_one])]

theorem UpperTheory.V.CA.universalDeformationRing_localCharacters :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n), PhiCond (F.Gv v) l → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (ψ : F.Gv v →* Rˣ), r.IsPsi v i ψ ∧ ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (ψ' : F.Gv v →* R'ˣ), r.IsPsi v i ψ' → ∃! f : R →ₐ[O] R', pushCh (f : R →+* R') ψ = ψ' := by
  intro l _ F O _ _ _ _ _ _ _ n r v i hΦ
  have hlc : IsLocallyConstant (r.psib v i) := lc_of_open _ (r.psib_open v i)
  have hlc' : IsLocallyConstant (toMat (r.psib v i)) :=
    hlc.comp fun x => (Matrix.of fun _ _ => (x : ResidueField O) : Matrix Unit Unit (ResidueField O))
  obtain ⟨R₀, _, _, _, u, hu⟩ := univ_lift l O (F.Gv v) Unit (toMat (r.psib v i)) hΦ hlc'
  let P : Cond O (toMat (r.psib v i)) := fun R _ _ _ s =>
    ∀ g : F.mu v, s.hom g () () = algebraMap O R (r.th v i g)
  have hP : P.IsClosed := fun R _ _ _ s => by
    refine ⟨Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)),
      fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h g => ?_⟩⟩
    · have : Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)) ≤
          RingHom.ker f := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        show f _ = 0
        rw [map_sub, AlgHom.commutes, sub_eq_zero]
        exact h g
      exact this hx
    · have := h _ (Ideal.subset_span ⟨g, rfl⟩)
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  haveI := (co_res O).1
  have hres : ∀ x : ResidueField O, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  let r₁ : Lift O (toMat (r.psib v i)) (ResidueField O) :=
    { hom := toMat (r.psib v i)
      cont := fun a b N => hlc.comp fun x => Ideal.Quotient.mk _ (x : ResidueField O)
      red := fun g a b => hres _ }
  obtain ⟨R, _, _, _, p, -, hR⟩ := univ_cond O (F.Gv v) Unit _ R₀ u _ P hu hP
    ⟨ResidueField O, inferInstance, inferInstance, inferInstance, r₁, trivial, fun g => psib_th r v i g⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat (u.map p).hom,
    ⟨(u.map p).cont () (), fun g => (u.map p).red g () (), ((hR R).1 (AlgHom.id O R)).2⟩, fun R' _ _ _ ψ' h' => ?_⟩
  let s : Lift O (toMat (r.psib v i)) R' :=
    { hom := toMat ψ'
      cont := fun a b => h'.cont
      red := fun g a b => h'.red g }
  obtain ⟨f, hf, huniq⟩ := (hR R').2 s ⟨trivial, h'.mu⟩
  refine ⟨f, ?_, fun f' hf' => huniq f' ?_⟩
  · ext g
    exact congrArg (fun t : Lift O (toMat (r.psib v i)) R' => t.hom g () ()) hf
  · ext g a b
    exact congrArg (fun t : F.Gv v →* R'ˣ => ((t g : R'ˣ) : R')) hf'
end
