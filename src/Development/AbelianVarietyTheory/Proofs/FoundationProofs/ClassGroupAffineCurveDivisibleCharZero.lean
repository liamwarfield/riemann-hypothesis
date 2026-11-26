module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialiseGenericSolutionAlmostAllPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedFibresAlmostAll
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedFibresAlmostAll
open Polynomial

attribute [local instance] FractionRing.liftAlgebra

namespace GlobalTheory

theorem reduced_fibres_almost_all (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    [Module.Finite k[X] A] [Module.Free k[X] A] :
    ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal →
      algebraMap k[X] A (X - C α) ∉ Q ^ 2 := by
  haveI : Module.IsTorsionFree k[X] A := inferInstance
  haveI : FaithfulSMul k[X] A := inferInstance
  haveI : Algebra.IsSeparable (FractionRing k[X]) (FractionRing A) := inferInstance
  have hD := differentIdeal_ne_bot (A := k[X]) (B := A)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hc := Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨δ, hδ0, fun α hα Q hQ hmem => hα ?_⟩
  set p : Ideal k[X] := Ideal.span {X - C α} with hpdef
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)
  have hp0 : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero α
  have hP : Q ^ 2 ∣ p.map (algebraMap k[X] A) := by
    rw [Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact hmem
  have hdiv := pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP
  rw [show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le] at hdiv
  have hδQ : δ ∈ Q.comap (algebraMap k[X] A) := hdiv hδ
  have hXQ : X - C α ∈ Q.comap (algebraMap k[X] A) :=
    Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)
  have hle : p ≤ Q.comap (algebraMap k[X] A) := by
    rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]; exact hXQ
  have heq : p = Q.comap (algebraMap k[X] A) :=
    hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle
  rw [← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot] at hδQ
  exact hδQ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedFibresAlmostAllStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_sub_C_not_mem_sq_maximal : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2 := by
  first | exact @GlobalTheory.reduced_fibres_almost_all | exact GlobalTheory.reduced_fibres_almost_all | (intros; apply GlobalTheory.reduced_fibres_almost_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve
open Polynomial

namespace GlobalTheory.SquarefreeFibre

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

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ _ g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.exists_nonzero_sub_C_not_mem_sq_maximal k A
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

end GlobalTheory.SquarefreeFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurveStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squarefree_poly_distinct_zeros_on_curve : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  first | exact @GlobalTheory.SquarefreeFibre.main | exact GlobalTheory.SquarefreeFibre.main | (intros; apply GlobalTheory.SquarefreeFibre.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero
open Polynomial

namespace GlobalTheory

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((GlobalTheory.T.dedekind_finiteType_ideal_codimension k A).2.1 P₀ hP).2
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

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZeroStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degree_lt_two_correction_simple_zero : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A), P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧ w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  first | exact @GlobalTheory.exists_deg_lt_two_correction_simple | exact GlobalTheory.exists_deg_lt_two_correction_simple | (intros; apply GlobalTheory.exists_deg_lt_two_correction_simple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization
open Polynomial

noncomputable section

namespace GlobalTheory.LinSys

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

end GlobalTheory.LinSys

open GlobalTheory.LinSys in
theorem GlobalTheory.linear_system_setup : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  intro k A _ _ _ _ _ _ _ _ _ _ N P₀ hN hP
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set n := Module.finrank k[X] A
  let b : Module.Basis (Fin n) k[X] A := Module.finBasis k[X] A
  obtain ⟨c, lam, hdeg1, hdeg2⟩ := GlobalTheory.T.norm_degree_bound_polynomial_combination k A n b
  obtain ⟨p, hp2, hpP, hpP2⟩ := GlobalTheory.T.exists_degree_lt_two_correction_simple_zero k A n b P₀ (∑ i, (C (lam i) * X ^ 2) • b i) hP
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
  obtain ⟨q, r, Q, hqm, hqdeg, hQmax, hQinj, hf₁Q, hqQ⟩ := GlobalTheory.T.exists_squarefree_poly_distinct_zeros_on_curve k A f₁ s hf₁0
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
    obtain ⟨p', hp'd, hp'⟩ := GlobalTheory.T.exists_lowDegree_coords_mod_mul k A n b f₁ (q ^ M) d hf₁0 (pow_ne_zero _ hqm.ne_zero)
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
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorizationStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_system_maximalDegree_factorization : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  first | exact @GlobalTheory.linear_system_setup | exact GlobalTheory.linear_system_setup | (intros; apply GlobalTheory.linear_system_setup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DegreeCountMaximalIdealGeneratesProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DegreeCountMaximalIdealGeneratesProduct
open Polynomial

namespace GlobalTheory

theorem degree_count_generates : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  intro k A _ _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg
  obtain ⟨_hfin, hmax, hmul, hle⟩ := GlobalTheory.T.dedekind_finiteType_ideal_codimension k A
  have hPne : P ≠ ⊥ := by
    intro h; apply hf; rw [h] at hfP; simpa using hfP
  have hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥ := by
    intro M hM h
    subst h
    exact hPne (hM.eq_of_le hP.ne_top bot_le).symm
  have hDne : D ≠ ⊥ := by
    intro h; exact hDP (h ▸ bot_le)
  have hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥ := by
    intro s g hg
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro i _; rw [Ideal.zero_eq_bot]; exact hg i
  have hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥ := by
    intro M n hM
    rw [← Ideal.zero_eq_bot] at hM ⊢
    exact pow_ne_zero n hM
  have hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥ := by
    intro M M' hM hM'
    rw [← Ideal.zero_eq_bot] at hM hM' ⊢
    exact mul_ne_zero hM hM'
  have htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0 := by
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n := by
    intro M n hM
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, htop]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]
  have hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) →
      Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]
  have hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) →
      Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I := by
    intro R hR
    rw [hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]
    simp only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥ :=
    fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))
  have h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) =
      1 + Module.finrank k (A ⧸ D) + N * Fintype.card I := by
    rw [hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ),
      hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]
  have hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M' := by
    intro M M' hM hM' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 := hM.eq_of_le h le_sup_left
    have h2 := hM'.eq_of_le h le_sup_right
    exact hne (h1.trans h2.symm)
  have hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D := by
    intro M hM hDM
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)
  have hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f} := fun M hM =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)
  have hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow
    · intro i _; exact hdvd _ (hfQ' i)
  have hPD : P * D ∣ Ideal.span {f} := (hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)
  have hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N) :=
    IsCoprime.mul_left
      (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right)
      (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)
  have hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f} := hPDX.mul_dvd hPD hX
  apply hle _ _ _ (Ideal.le_of_dvd hJ)
  · rw [hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1,
      hPowProd Q' hQ']
    rw [h0] at hdeg; exact hdeg
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DegreeCountMaximalIdealGeneratesProductStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_count_maximalIdeal_generates_product : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  first | exact @GlobalTheory.degree_count_generates | exact GlobalTheory.degree_count_generates | (intros; apply GlobalTheory.degree_count_generates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowers
open Polynomial

namespace GlobalTheory

theorem classGroup_mk0_mul_mul_pow_eq_one_of_span_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (N : ℕ) (P D C : Ideal A) (f : A) (hP : P ∈ nonZeroDivisors (Ideal A))
    (hD : D ∈ nonZeroDivisors (Ideal A)) (hC : C ∈ nonZeroDivisors (Ideal A))
    (h : Ideal.span {f} = P * D * C ^ N) :
    ClassGroup.mk0 ⟨P, hP⟩ * ClassGroup.mk0 ⟨D, hD⟩ * ClassGroup.mk0 ⟨C, hC⟩ ^ N = 1 := by
  rw [← map_pow, ← map_mul, ← map_mul]
  have hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A) :=
    mul_mem (mul_mem hP hD) (pow_mem hC N)
  have e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩ :=
    Subtype.ext (by simp)
  rw [e, ClassGroup.mk0_eq_one_iff, ← h]
  exact ⟨⟨f, rfl⟩⟩

theorem prod_maximal_mem_nonZeroDivisors {A : Type} [CommRing A] [IsDedekindDomain A]
    {I : Type} [Fintype I] (Q : I → Ideal A) (hQ : ∀ i, (Q i).IsMaximal)
    (P₀ : Ideal A) (hP₀ : P₀.IsMaximal) (h₀ : P₀ ≠ ⊥) :
    (∏ i, Q i) ∈ nonZeroDivisors (Ideal A) := by
  refine prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_
  intro hi
  have hb : (⊥ : Ideal A).IsMaximal := by
    have := hQ i
    rwa [hi] at this
  exact h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm

theorem exists_class_group_mk0_eq_mul_pow :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal →
      ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal →
        a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A,
          ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  intro k A _ _ _ _ _ _ _ _ _ _ N hN P₀ hP₀ h₀
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨r, V, D, Q, f₀, hset, hdeg⟩ := GlobalTheory.T.exists_linear_system_maximalDegree_factorization k A N P₀ (by omega) hP₀
  have hform := GlobalTheory.T.exists_formal_deformation_powerSeries_solution k A N (Fin r) V D P₀ Q f₀ hN hP₀ hset
  obtain ⟨a, ha, hall⟩ := GlobalTheory.T.specialise_generic_solution_almost_all_points k A (PowerSeries k) N (Fin r) V D hN hform
  obtain ⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩ := hset
  refine ⟨a, ha, fun P hP haP h => ?_⟩
  obtain ⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩ := hall P hP haP
  have hspan := GlobalTheory.T.degree_count_maximalIdeal_generates_product k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP
    hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)
  have hP₀ne : P₀ ≠ ⊥ := nonZeroDivisors.ne_zero h₀
  have hD : D ∈ nonZeroDivisors (Ideal A) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hD0
    apply hDP
    rw [hD0]
    exact bot_le
  have hC := prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne
  have hC' := prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne
  rw [Finset.prod_pow] at hspan hspan₀
  have e := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan
  have e₀ := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀
  refine ⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩
  generalize ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢
  generalize ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢
  generalize ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀
  generalize ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢
  generalize ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢
  have e' : p * c' ^ N = p₀ * c ^ N := by
    apply mul_right_cancel (b := d)
    rw [mul_right_comm p, mul_right_comm p₀, e, e₀]
  rw [div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowersStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_class_group_powers : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  first | exact @GlobalTheory.exists_class_group_mk0_eq_mul_pow | exact GlobalTheory.exists_class_group_mk0_eq_mul_pow | (intros; apply GlobalTheory.exists_class_group_mk0_eq_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne
open Polynomial

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_integral_norm_natDegree_mod_eq_one :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
      [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 1 ≤ N →
      ∃ f : FunctionField.ringOfIntegers k K, f ≠ 0 ∧ (Algebra.norm k[X] f).natDegree % N = 1 % N := by
  intro k K _ _ _ _ _ _ _ _ N hN
  set O := FunctionField.ringOfIntegers k K
  have hC1 : _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) := by
    unfold _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle
    intro n d f hf hd hdn
    obtain ⟨x, hx, h⟩ := _root_.GlobalTheory.tsenLang_ratFunc k n 1 d (fun _ => f) (fun _ => hf) hd (by simpa using hdn)
    exact ⟨x, hx, h 0⟩
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) K hC1
    RatFunc.X RatFunc.X_ne_zero
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.Free k[X] O := Module.free_of_finite_type_torsion_free'
  haveI := IsIntegralClosure.isLocalization k[X] (RatFunc k) K O
  have hnorm : ∀ a : O, algebraMap k[X] (RatFunc k) (Algebra.norm k[X] a) =
      Algebra.norm (RatFunc k) (algebraMap O K a) := fun a =>
    (Algebra.norm_localization k[X] (nonZeroDivisors k[X]) (Rₘ := RatFunc k) (Sₘ := K) a).symm
  obtain ⟨⟨a, s⟩, hxa⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid O (nonZeroDivisors k[X])) x
  obtain ⟨b, hb, hbs⟩ := s.2
  simp only at hxa
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set r := Module.finrank k[X] O
  have hs : Algebra.norm k[X] (s : O) = b ^ r := by rw [← hbs]; exact Algebra.norm_algebraMap b
  have ha : Algebra.norm k[X] a = X * b ^ r := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [hnorm, ← hxa, map_mul, hx, ← hnorm, hs, map_mul, RatFunc.algebraMap_X]
  have hexp : r + r * (N - 1) = r * N := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hf : Algebra.norm k[X] (a * (s : O) ^ (N - 1)) = X * b ^ (r * N) := by
    rw [map_mul, map_pow, ha, hs, mul_assoc, ← pow_mul, ← pow_add, hexp]
  refine ⟨a * (s : O) ^ (N - 1), ?_, ?_⟩
  · intro h
    have h0 := hf
    rw [h, Algebra.norm_zero] at h0
    exact mul_ne_zero X_ne_zero (pow_ne_zero _ hb0) h0.symm
  · rw [hf, natDegree_mul X_ne_zero (pow_ne_zero _ hb0), natDegree_X, natDegree_pow,
      show r * N * b.natDegree = r * b.natDegree * N by ring, Nat.add_mul_mod_self_right]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsMod
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsMod
open Polynomial

namespace GlobalTheory

theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.T.dedekind_finiteType_ideal_codimension k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsModStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  first | exact @GlobalTheory.classGroup_nthPower_of_codim_one_mod | exact GlobalTheory.classGroup_nthPower_of_codim_one_mod | (intros; apply GlobalTheory.classGroup_nthPower_of_codim_one_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero
open Polynomial

namespace GlobalTheory

theorem classGroup_ringOfIntegers_divisible : GlobalTheory.NeedB.ClDiv := by
  intro k K _ _ _ _ _ _ _ _ N hN c
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    exact ⟨c, (pow_one c).symm⟩
  set A := FunctionField.ringOfIntegers k K
  have : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  have : Module.Free k[X] A := IsIntegralClosure.module_free k[X] (RatFunc k) K _
  have : Module.Finite k[X] A := IsIntegralClosure.finite k[X] (RatFunc k) K _
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  letI : Algebra k A := ((algebraMap k[X] A).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.exists_integral_norm_natDegree_mod_eq_one k K N hN
  have hdim : Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
    rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hf0]
    exact hf
  exact GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod k A N hN (GlobalTheory.T.function_field_class_group_powers k A N h) ⟨f, hf0, hdim⟩ c

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZeroStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_affineCurve_divisible_charZero : GlobalTheory.NeedB.ClDiv := by
  first | exact @GlobalTheory.classGroup_ringOfIntegers_divisible | exact GlobalTheory.classGroup_ringOfIntegers_divisible | (intros; apply GlobalTheory.classGroup_ringOfIntegers_divisible <;> assumption)
end
