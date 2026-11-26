module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegLtTwoCorrectionSimple
open Polynomial

namespace GlobalTheory.PicDiv

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory.PicDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapNormMemSpan
open Polynomial

namespace GlobalTheory.PicDiv.SquarefreeFibre

theorem algebraMap_norm_mem_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (g : S) :
    algebraMap R S (Algebra.norm R g) ∈ Ideal.span {g} := by
  set p := LinearMap.charpoly (Algebra.lmul R S g) with hp
  have h1 : aeval g p = 0 := by
    have h2 := congrArg (fun φ : Module.End R S => φ 1) (LinearMap.aeval_self_charpoly (Algebra.lmul R S g))
    rw [← hp, Polynomial.aeval_algHom_apply (Algebra.lmul R S) g p] at h2
    simpa using h2
  have h3 : algebraMap R S (p.coeff 0) = -(g * aeval g p.divX) := by
    have h4 := X_mul_divX_add p
    rw [← h4] at h1
    simp only [map_add (f := _), map_mul, aeval_X, aeval_C] at h1
    linear_combination h1
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, ← hp, h3]
  exact Ideal.mul_mem_left _ _ ((Ideal.span {g}).neg_mem
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)))

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ hred g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := hred
  set u := algebraMap k[X] A with hu
  set N := Algebra.norm k[X] g with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hinj : Function.Injective u := FaithfulSMul.algebraMap_injective k[X] A
  have huC : ∀ c : k, u (C c) = algebraMap k A c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] A c, Polynomial.algebraMap_eq]

  have hCnot : ∀ (P : Ideal A), P.IsPrime → ∀ c : k, c ≠ 0 → u (C c) ∉ P := by
    intro P hP c hc hmem
    rw [huC] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map (algebraMap k A)))

  have hgnot : ∀ (P : Ideal A), P.IsPrime → ∀ α : k, N.eval α ≠ 0 → u (X - C α) ∈ P → g ∉ P := by
    intro P hP α hα hX hgP
    have hNP : u N ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr hgP (algebraMap_norm_mem_span g)
    have hdec := modByMonic_add_div N (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdec
    have h5 : C (N.eval α) = N - (X - C α) * (N /ₘ (X - C α)) := eq_sub_of_add_eq hdec
    have : u (C (N.eval α)) = u N - u (X - C α) * u (N /ₘ (X - C α)) := by
      rw [h5, map_sub, map_mul]
    exact hCnot P hP _ hα (this ▸ P.sub_mem hNP (P.mul_mem_right _ hX))

  have hδN : δ * N ≠ 0 := mul_ne_zero hδ0 hN
  have hfin : {a : k | (δ * N).eval a = 0}.Finite :=
    ((δ * N).roots.toFinset.finite_toSet).subset (fun a ha => by
      simp only [Set.mem_setOf_eq] at ha
      simp [Polynomial.mem_roots hδN, ha])
  have hinf : {a : k | (δ * N).eval a ≠ 0}.Infinite := by
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  obtain ⟨F, hFS, hFcard⟩ := hinf.exists_subset_card_eq s
  have hF : ∀ a ∈ F, δ.eval a ≠ 0 ∧ N.eval a ≠ 0 := by
    intro a ha
    have := hFS ha
    simp only [Set.mem_setOf_eq, eval_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set q : k[X] := ∏ a ∈ F, (X - C a) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqdeg : q.natDegree = s := by
    rw [hq, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [hFcard]

  have hone : ∀ (P : Ideal A), P.IsPrime → u q ∈ P → ∃ a ∈ F, u (X - C a) ∈ P := by
    intro P hP hqP
    rw [hq, map_prod] at hqP
    exact Ideal.IsPrime.prod_mem_iff.mp hqP
  have huniq : ∀ (P : Ideal A), P.IsPrime → ∀ a b : k, u (X - C a) ∈ P → u (X - C b) ∈ P → a = b := by
    intro P hP a b ha hb
    by_contra hab
    have : u (C (b - a)) = u (X - C a) - u (X - C b) := by
      rw [← map_sub]; congr 1; simp [C_sub]
    exact hCnot P hP (b - a) (sub_ne_zero.mpr (Ne.symm hab)) (this ▸ P.sub_mem ha hb)
  have hnotsq : ∀ (P : Ideal A), P.IsMaximal → u q ∉ P ^ 2 := by
    intro P hPm hq2
    have hP : P.IsPrime := hPm.isPrime
    obtain ⟨a, haF, haP⟩ := hone P hP (Ideal.pow_le_self two_ne_zero hq2)
    have hsplit : q = (∏ b ∈ F.erase a, (X - C b)) * (X - C a) := by
      rw [hq, mul_comm, Finset.mul_prod_erase F (fun b => X - C b) haF]
    rw [hsplit, map_mul] at hq2
    rcases Ideal.IsPrime.mul_mem_pow P hq2 with hrest | hX2
    · rw [map_prod] at hrest
      obtain ⟨b, hbF, hbP⟩ := Ideal.IsPrime.prod_mem_iff.mp hrest
      exact (Finset.ne_of_mem_erase hbF) (huniq P hP b a hbP haP)
    · exact hδ a (hF a haF).1 P hPm hX2

  set I : Ideal A := Ideal.span {u q} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hqm.ne_zero (hinj (h.trans (map_zero u).symm))
  have hsq : Squarefree I := by
    intro J hJ
    by_contra hJu
    have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.mpr h)
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
    have hle : I ≤ P ^ 2 := (Ideal.le_of_dvd hJ).trans (by rw [pow_two]; exact Ideal.mul_mono hJP hJP)
    exact hnotsq P hPm (hle (Ideal.mem_span_singleton_self _))
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hmem : ∀ P ∈ M, P.IsMaximal ∧ g ∉ P := by
    intro P hPM
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPM)
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hPM
    refine ⟨hPp.isMaximal hPne, ?_⟩
    have hqP : u q ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPM)
      (Ideal.mem_span_singleton_self _)
    obtain ⟨a, haF, haP⟩ := hone P hPp hqP
    exact hgnot P hPp a (hF a haF).2 haP
  let e := M.toFinset.equivFin
  refine ⟨q, M.toFinset.card, fun i => (e.symm i : Ideal A), hqm, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).1
  · intro i j h; exact e.symm.injective (Subtype.ext h)
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).2
  · rw [Fintype.prod_equiv e.symm (fun i => (e.symm i : Ideal A)) (fun x => (x : Ideal A)) (fun _ => rfl),
      Finset.prod_coe_sort M.toFinset (fun x => x), Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      hnodup.dedup, Multiset.map_id', hM, ← hI]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm

end GlobalTheory.PicDiv.SquarefreeFibre
end

open Polynomial

noncomputable section

namespace GlobalTheory.PicDiv.LinSys

section Bounded

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] [Algebra k[X] A]
  [IsScalarTower k k[X] A]

theorem repr_smul_const {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (c : k) (f : A) (i : Fin n) :
    b.repr (c • f) i = C c * b.repr f i := by
  rw [← algebraMap_smul k[X] c f, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Polynomial.algebraMap_eq]

def boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) : Submodule k A where
  carrier := {f | f ∈ D ∧ ∀ i, (b.repr f i).natDegree ≤ d}
  zero_mem' := ⟨D.zero_mem, fun i => by simp⟩
  add_mem' := fun {f g} hf hg => ⟨D.add_mem hf.1 hg.1, fun i => by
    rw [map_add (f := _), Finsupp.add_apply]
    exact (natDegree_add_le _ _).trans (max_le (hf.2 i) (hg.2 i))⟩
  smul_mem' := fun c f hf => ⟨by rw [Algebra.smul_def]; exact D.mul_mem_left _ hf.1, fun i => by
    rw [repr_smul_const]
    exact (natDegree_C_mul_le _ _).trans (hf.2 i)⟩

def coeffMap {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    boundedIn b D d →ₗ[k] (Fin n → Fin (d + 1) → k) where
  toFun f i j := (b.repr (f : A) i).coeff j
  map_add' f g := by ext i j; simp [coeff_add]
  map_smul' c f := by ext i j; simp [repr_smul_const, coeff_C_mul]

theorem coeffMap_injective {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    Function.Injective (coeffMap b D d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h0 : ∀ i, b.repr (f : A) i = 0 := by
    intro i
    ext j
    by_cases hj : j ≤ d
    · have := congrFun (congrFun hf i) ⟨j, Nat.lt_succ_of_le hj⟩
      simpa [coeffMap] using this
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (f.2.2 i) (not_le.1 hj))]; simp
  have : (f : A) = 0 := by
    rw [← b.sum_repr (f : A)]; simp [h0]
  exact Subtype.ext this

instance finiteDimensional_boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A)
    (d : ℕ) : FiniteDimensional k (boundedIn b D d) :=
  Module.Finite.of_injective (coeffMap b D d) (coeffMap_injective b D d)

end Bounded

theorem isCoprime_of_not_le {A : Type} [CommRing A] {M D : Ideal A} (hM : M.IsMaximal)
    (h : ¬ D ≤ M) : IsCoprime M D := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h'
  exact h (le_sup_right.trans (hM.eq_of_le h' le_sup_left).ge)

end GlobalTheory.PicDiv.LinSys


open GlobalTheory.PicDiv.LinSys in
theorem GlobalTheory.PicDiv.linear_system_setup : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  intro k A _ _ _ _ _ _ _ _ _ hred N P₀ hN hP
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set n := Module.finrank k[X] A
  let b : Module.Basis (Fin n) k[X] A := Module.finBasis k[X] A
  obtain ⟨c, lam, hdeg1, hdeg2⟩ := GlobalTheory.NormDegree.natDegree_norm_of_coord_degree k A n b
  obtain ⟨p, hp2, hpP, hpP2⟩ := GlobalTheory.PicDiv.exists_deg_lt_two_correction_simple k A n b P₀ (∑ i, (C (lam i) * X ^ 2) • b i) hP
  set f₁ : A := ∑ i, (C (lam i) * X ^ 2 + p i) • b i with hf₁def
  have hf₁eq : (∑ i, (C (lam i) * X ^ 2) • b i) + ∑ i, p i • b i = f₁ := by
    rw [hf₁def, ← Finset.sum_add_distrib]; simp [add_smul]
  rw [hf₁eq] at hpP hpP2
  obtain ⟨hf₁0, hf₁deg⟩ := hdeg2 2 p hp2
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  have hDP : ¬ D ≤ P₀ := by
    intro h
    apply hpP2
    have : Ideal.span {f₁} ≤ P₀ ^ 2 := by rw [hD, sq]; exact Ideal.mul_mono_right h
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  have hf₁D : f₁ ∈ D := by
    have : Ideal.span {f₁} ≤ D := hD ▸ Ideal.mul_le_right
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  set s := n * 2 + c with hs
  obtain ⟨q, r, Q, hqm, hqdeg, hQmax, hQinj, hf₁Q, hqQ⟩ := GlobalTheory.PicDiv.SquarefreeFibre.main k A hred f₁ s hf₁0
  set d := 2 + (M + 1) * s with hd
  have hspan : ∀ m : ℕ, Ideal.span {f₁ * algebraMap k[X] A (q ^ m)} = P₀ * D * ∏ i, Q i ^ m := by
    intro m
    rw [← Ideal.span_singleton_mul_span_singleton, hD, map_pow, ← Ideal.span_singleton_pow, hqQ,
      Finset.prod_pow]
  have hrepr₁ : ∀ i, b.repr f₁ i = C (lam i) * X ^ 2 + p i := by
    intro i; rw [hf₁def, b.repr_sum_self]
  have hdeg₁ : ∀ i, (b.repr f₁ i).natDegree ≤ 2 := by
    intro i
    rw [hrepr₁]
    exact (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _)
      (natDegree_le_iff_degree_le.2 (le_of_lt (hp2 i))))
  set f₀ : A := f₁ * algebraMap k[X] A (q ^ (M + 1)) with hf₀def
  have hf₀smul : f₀ = q ^ (M + 1) • f₁ := by rw [hf₀def, Algebra.smul_def, mul_comm]
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀smul]; exact smul_ne_zero (pow_ne_zero _ hqm.ne_zero) hf₁0
  have hf₀V : f₀ ∈ boundedIn b D d := by
    refine ⟨D.mul_mem_right _ hf₁D, fun i => ?_⟩
    rw [hf₀smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine (natDegree_mul_le).trans ?_
    rw [hqm.natDegree_pow, hqdeg]
    have := hdeg₁ i
    omega
  have hnorm₁ : Algebra.norm k[X] f₁ ≠ 0 := Algebra.norm_ne_zero_iff.2 hf₁0
  have hf₀deg : (Algebra.norm k[X] f₀).natDegree = n * d + c := by
    rw [hf₀def, map_mul, Algebra.norm_algebraMap_of_basis b, Fintype.card_fin,
      natDegree_mul hnorm₁ (pow_ne_zero _ (pow_ne_zero _ hqm.ne_zero)), hf₁deg,
      natDegree_pow, hqm.natDegree_pow, hqdeg, hd, hs]
    ring
  refine ⟨r, boundedIn b D d, D, Q, f₀, ⟨inferInstance, fun v hv => hv.1, hQmax, hQinj,
    fun i h => hf₁Q i (h ▸ hpP), fun i h => hf₁Q i (h hf₁D), hDP, hf₀V, hf₀0, hspan (M + 1),
    ?_⟩, ?_⟩
  · intro u
    have hcop : IsCoprime (P₀ * ∏ i, Q i ^ M) D :=
      (isCoprime_of_not_le hP hDP).mul_left
        (IsCoprime.prod_left fun i _ => (isCoprime_of_not_le (hQmax i) (fun h => hf₁Q i (h hf₁D))).pow_left)
    have h1 : (1 : A) ∈ (P₀ * ∏ i, Q i ^ M) ⊔ D := by
      rw [Ideal.isCoprime_iff_sup_eq.1 hcop]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    have hqd : (Algebra.norm k[X] f₁).natDegree + (q ^ M).natDegree ≤ d + 1 := by
      rw [hqm.natDegree_pow, hqdeg, hf₁deg, hd, hs]; nlinarith
    obtain ⟨p', hp'd, hp'⟩ := GlobalTheory.exists_lowDegree_coords_mod k A n b f₁ (q ^ M) d hf₁0 (pow_ne_zero _ hqm.ne_zero)
      hqd (u * y)
    rw [hspan M] at hp'
    have hP0 : P₀ * D * ∏ i, Q i ^ M ≤ D := Ideal.mul_le_left.trans Ideal.mul_le_right
    have hPI : P₀ * D * ∏ i, Q i ^ M ≤ P₀ * ∏ i, Q i ^ M := Ideal.mul_mono_left Ideal.mul_le_left
    refine ⟨∑ i, p' i • b i, ⟨?_, fun i => ?_⟩, ?_⟩
    · have : ∑ i, p' i • b i = u * y - (u * y - ∑ i, p' i • b i) := by ring
      rw [this]; exact D.sub_mem (D.mul_mem_left _ hy) (hP0 hp')
    · rw [b.repr_sum_self]; exact hp'd i
    · have : u - ∑ i, p' i • b i = u * x + (u * y - ∑ i, p' i • b i) := by
        linear_combination (-u) * hxy
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (hPI hp')
  · intro f hf hf0
    rw [finrank_quotient_span_eq_natDegree_norm b hf0, finrank_quotient_span_eq_natDegree_norm b hf₀0,
      hf₀deg]
    have := hdeg1 d (fun i => b.repr f i) hf.2
    rwa [b.sum_repr] at this
