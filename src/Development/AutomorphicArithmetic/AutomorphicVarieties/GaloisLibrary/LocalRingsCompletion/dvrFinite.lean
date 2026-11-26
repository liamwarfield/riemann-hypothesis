module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_smul_top_iff_repr {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun a c ha hc => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · rw [map_add (f := _), Finsupp.add_apply]
      exact I.add_mem ha hc
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

private theorem prec_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I M := ⟨fun f hf => by
  let b := Module.Free.chooseBasis R M
  have key : ∀ i, ∃ L : R, ∀ k, b.repr (f k) i - L ∈ I ^ k := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i)
      (fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at h
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using h i)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using key
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
  intro i
  have : b.repr (b.equivFun.symm L) i = L i := by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, this]
  exact hL i n⟩

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.abelian₂.dvr_finite :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      IsAdicComplete (maximalIdeal O) O ∧ Finite (ResidueField O) ∧ (l : O) ∈ maximalIdeal O ∧
        Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) := by
  intro l hl O _ _ _ _ _ _
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    exact mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero (pow_ne_zero _ hl0) hx
  have : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hfree : Module.Free ℤ_[l] O := Module.free_of_finite_type_torsion_free'
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hlm : (l : O) ∈ maximalIdeal O := by
    have h : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have := map_nonunit (algebraMap ℤ_[l] O) _ h
    rwa [map_natCast] at this
  have hres : Finite (ResidueField O) := by
    have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  refine ⟨?_, hres, hlm, hinj, hfree, hloc⟩
  have hP : IsPrecomplete (maximalIdeal O) O := by
    have h1 : IsPrecomplete ((maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) O :=
      IsPrecomplete.map_algebraMap_iff.2 (prec_free _)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {(l : O)}) (by simpa using hl0) hϖ
    refine prec_cofinal ((Ideal.span_singleton_le_iff_mem _).2 hlm) (e := e) ?_ h1
    rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

theorem UpperTheory.V.abelian₂.nakayama :
    ∀ (R : Type) [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M] [Module R M] [IsHausdorff I M],
      (∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
        Submodule.span R (Set.range s) = ⊤) ∧
      (Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) → Module.Finite R M) := by
  intro R _ I _ M _ _ _
  have part1 : ∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
      Submodule.span R (Set.range s) = ⊤ := by
    intro r s hs
    have hsurj : Function.Surjective (Fintype.linearCombination R s) := by
      haveI := isPrecomplete_pi I r
      apply surjective_of_mkQ_comp_surjective (I := I)
      intro q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hm : m ∈ Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) := by
        rw [hs]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
      rw [← Fintype.range_linearCombination, LinearMap.mem_range] at ha
      obtain ⟨c, rfl⟩ := ha
      refine ⟨c, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using Submodule.neg_mem _ hb
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hsurj
  refine ⟨part1, ?_⟩
  intro hfin
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  choose t ht using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (s i)
  have hsup : Submodule.span R (Set.range t) ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.map_span, ← Set.range_comp]
    have hcomp : (I • (⊤ : Submodule R M)).mkQ ∘ t = s := funext fun i => ht i
    rw [hcomp, hs, Submodule.comap_top]
  have htop := part1 r t hsup
  exact ⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t, htop⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem UpperTheory.V.abelian₂.dvr_intClosure :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K],
      IsDiscreteValuationRing (integralClosure ℤ_[l] K) ∧ Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) ∧
        IsFractionRing (integralClosure ℤ_[l] K) K := by
  intro l hl K _ _ _ _ _
  let φ : K →ₐ[ℚ_[l]] PadicAlgCl l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hint := UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis φ
  have hunit : ∀ a : integralClosure ℤ_[l] K, ‖φ a‖ = 1 → IsUnit a := by
    intro a ha
    have h0 : (a : K) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have hi : IsIntegral ℤ_[l] (a : K)⁻¹ := by
      rw [hint, map_inv₀, norm_inv, ha, inv_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : integralClosure ℤ_[l] K) (Subtype.ext (mul_inv_cancel₀ h0))
  have hloc : IsLocalRing (integralClosure ℤ_[l] K) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    have ha : ‖φ a‖ ≤ 1 := (hint _).1 a.2
    rcases ha.eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · refine Or.inr (hunit _ (le_antisymm ((hint _).1 (1 - a).2) ?_))
      by_contra hlt
      push Not at hlt
      have h1 : φ ((1 - a : integralClosure ℤ_[l] K) : K) + φ a = 1 := by simp
      have h2 := (PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt hlt h)
      simp only [h1] at h2
      simp at h2
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    have h := congrArg (fun x : integralClosure ℤ_[l] K => (x : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  exact ⟨((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded,
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K),
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] K⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.adicComplete
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.MemMaxPow
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_max_iff {O : Type} [CommRing O] [IsLocalRing O] (f : O⟦X⟧) :
    f ∈ maximalIdeal O⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

private theorem C_mem_pow {O : Type} [CommRing O] [IsLocalRing O] (k : ℕ) (a : O)
    (ha : a ∈ maximalIdeal O ^ k) : (C a : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ ^ k := by
  have h1 : Ideal.map (C : O →+* O⟦X⟧) (maximalIdeal O) ≤ maximalIdeal O⟦X⟧ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff]
    simpa using hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* O⟦X⟧) ha
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

theorem UpperTheory.V.abelian₂.mem_max_pow :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (f : O⟦X⟧) (n : ℕ),
      f ∈ maximalIdeal O⟦X⟧ ^ n ↔ ∀ i, coeff i f ∈ maximalIdeal O ^ (n - i) := by
  intro O _ _ f n
  constructor
  · intro hf
    induction n generalizing f with
    | zero => intro i; simp
    | succ n ih =>
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb i
        rw [PowerSeries.coeff_mul]
        refine Ideal.sum_mem _ ?_
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h1 := ih a ha p.1
        have h2 : coeff p.2 b ∈ maximalIdeal O ^ (1 - p.2) := by
          rcases Nat.eq_zero_or_pos p.2 with h | h
          · rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply]
            simpa using (mem_max_iff b).1 hb
          · rw [Nat.sub_eq_zero_of_le h]
            simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · intro x y hx hy i
        rw [map_add (f := _)]
        exact Ideal.add_mem _ (hx i) (hy i)
  · intro h
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [PowerSeries.eq_X_mul_shift_add_const f]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ']
        refine Ideal.mul_mem_mul ?_ ?_
        · exact (mem_max_iff X).2 (by simp)
        · apply ih
          intro i
          rw [PowerSeries.coeff_mk]
          have := h (i + 1)
          simpa using this
      · apply C_mem_pow
        have := h 0
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
end

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.adicComplete :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O],
      IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := by
  intro O _ _ _
  have key : ∀ (x y : O⟦X⟧) (n : ℕ),
      x ≡ y [SMOD (maximalIdeal O⟦X⟧) ^ n • (⊤ : Submodule O⟦X⟧ O⟦X⟧)] ↔
        ∀ i, coeff i x - coeff i y ∈ maximalIdeal O ^ (n - i) := by
    intro x y n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow]
    simp only [map_sub]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    ext i
    apply eq_of_sub_mem_pow (maximalIdeal O)
    intro n
    have h := (key x 0 (n + i)).1 (hx (n + i)) i
    simpa using h
  · intro f hf
    have hc : ∀ i, ∃ L : O, ∀ n, coeff i (f (n + i)) - L ∈ maximalIdeal O ^ n := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal O) (M := O)
        (fun m => coeff i (f (m + i))) (by
          intro m n hmn
          have h := (key _ _ (m + i)).1 (hf (Nat.add_le_add_right hmn i)) i
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
          simpa using h)
      refine ⟨L, fun n => ?_⟩
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
      exact h
    choose L hL using hc
    refine ⟨PowerSeries.mk L, fun n => ?_⟩
    rw [key]
    intro i
    rw [coeff_mk]
    rcases le_or_gt i n with hin | hin
    · have h := hL i (n - i)
      rwa [Nat.sub_add_cancel hin] at h
    · rw [Nat.sub_eq_zero_of_le hin.le, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.SnakeLen
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem len_mid {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (h : N →ₗ[R] P)
    (e : Function.Exact f h) :
    Module.length R N = Module.length R (LinearMap.range f) + Module.length R (LinearMap.range h) := by
  refine Module.length_eq_add_of_exact (LinearMap.range f).subtype h.rangeRestrict
    (Submodule.injective_subtype _) h.surjective_rangeRestrict ?_
  intro n
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero]
  change h n = 0 ↔ _
  rw [e n]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨⟨f m, m, rfl⟩, rfl⟩
  · rintro ⟨⟨_, m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩

private def tmap {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : R) (f : M →ₗ[R] N) :
    Submodule.torsionBy R M g →ₗ[R] Submodule.torsionBy R N g :=
  f.restrict fun x hx => by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero]

private theorem ex_tors {R : Type} (M : Type) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (Submodule.torsionBy R M g).subtype (g • (LinearMap.id : M →ₗ[R] M)) := by
  intro x
  constructor
  · intro hx
    refine ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, rfl⟩
    simpa using hx
  · rintro ⟨⟨y, hy⟩, rfl⟩
    simpa using (Submodule.mem_torsionBy_iff _ _).1 hy

private theorem ex_quot {R : Type} (M : Type) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (g • (LinearMap.id : M →ₗ[R] M)) (g • (⊤ : Submodule R M)).mkQ := by
  intro x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact ⟨b, by simp⟩
  · rintro ⟨b, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, Submodule.mem_top, by simp⟩

theorem UpperTheory.V.abelian₂.snake_len :
    ∀ (R : Type) [CommRing R] (g : R) (A B D : Type) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D] [Module R D]
      (i : A →ₗ[R] B) (j : B →ₗ[R] D), Function.Injective i → Function.Surjective j → Function.Exact i j →
      invLen g A + invLen g D + coinvLen g B = invLen g B + coinvLen g A + coinvLen g D ∧
        invLen g B ≤ invLen g A + invLen g D ∧ coinvLen g B ≤ coinvLen g A + coinvLen g D ∧
        invLen g A ≤ invLen g B ∧ coinvLen g D ≤ coinvLen g B ∧
        coinvLen g A ≤ invLen g D + coinvLen g B ∧ invLen g D ≤ invLen g B + coinvLen g A := by
  intro R _ g A B D _ _ _ _ _ _ i j hi hj hij
  have h₁ : i ∘ₗ (g • LinearMap.id : A →ₗ[R] A) = (g • LinearMap.id : B →ₗ[R] B) ∘ₗ i := by
    ext a
    simp
  have h₂ : j ∘ₗ (g • LinearMap.id : B →ₗ[R] B) = (g • LinearMap.id : D →ₗ[R] D) ∘ₗ j := by
    ext b
    simp
  let G : QuotSMulTop g A →ₗ[R] QuotSMulTop g B := Submodule.mapQ _ _ i (by
    intro a ha
    rw [Submodule.mem_comap]
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  let H : QuotSMulTop g B →ₗ[R] QuotSMulTop g D := Submodule.mapQ _ _ j (by
    intro a ha
    rw [Submodule.mem_comap]
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hG : G ∘ₗ (g • ⊤ : Submodule R A).mkQ = (g • ⊤ : Submodule R B).mkQ ∘ₗ i := by
    ext a
    rfl
  have hδr := SnakeLemma.exact_δ'_right (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂ (Submodule.torsionBy R B g).subtype (ex_tors B g)
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    hj hi (tmap g j) (by ext x; rfl) (Submodule.injective_subtype _)
  have hδl := SnakeLemma.exact_δ'_left (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    (g • ⊤ : Submodule R B).mkQ (ex_quot B g) hj hi G hG (Submodule.mkQ_surjective _)
  have e1 : Function.Exact (tmap g i) (tmap g j) := by
    intro x
    constructor
    · intro hx
      have hx' : j x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨a, ha⟩ := (hij x.1).1 hx'
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      rw [Submodule.mem_torsionBy_iff]
      apply hi
      rw [map_smul, ha, map_zero]
      exact (Submodule.mem_torsionBy_iff _ _).1 x.2
    · rintro ⟨a, rfl⟩
      exact Subtype.ext (hij.apply_apply_eq_zero a.1)
  have i1 : Function.Injective (tmap g i) := fun x y hxy =>
    Subtype.ext (hi (congrArg Subtype.val hxy))
  have e4 : Function.Exact G H := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    constructor
    · intro hy
      change Submodule.Quotient.mk (j b) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨d, -, hd⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      obtain ⟨b', rfl⟩ := hj d
      obtain ⟨a, ha⟩ := (hij (b - g • b')).1 (by rw [map_sub, map_smul, hd, sub_self])
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (i a) = Submodule.Quotient.mk b
      rw [ha, Submodule.Quotient.eq, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    · rintro ⟨x, hx⟩
      rw [← hx]
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
      change Submodule.Quotient.mk (j (i a)) = 0
      rw [hij.apply_apply_eq_zero, Submodule.Quotient.mk_zero]
  have s4 : Function.Surjective H := by
    intro y
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨b, rfl⟩ := hj d
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have L1 := len_mid (tmap g i) (tmap g j) e1
  have L2 := len_mid _ _ hδr
  have L3 := len_mid _ _ hδl
  have L4 := len_mid G H e4
  have r1 : Module.length R (LinearMap.range (tmap g i)) =
      Module.length R (Submodule.torsionBy R A g) :=
    (LinearEquiv.ofInjective _ i1).length_eq.symm
  have r4 : Module.length R (LinearMap.range H) = Module.length R (QuotSMulTop g D) := by
    rw [LinearMap.range_eq_top.2 s4, Module.length_top]
  have arith : ∀ p x y z q : ℕ∞,
      p + (x + y) + (z + q) = p + x + (y + z) + q ∧ p + x ≤ p + (x + y) ∧
        z + q ≤ y + z + q ∧ p ≤ p + x ∧ q ≤ z + q ∧ y + z ≤ x + y + (z + q) ∧
        x + y ≤ p + x + (y + z) := by
    intro p x y z q
    exact ⟨by ring, le_iff_exists_add.2 ⟨y, by ring⟩, le_iff_exists_add.2 ⟨y, by ring⟩,
      le_iff_exists_add.2 ⟨x, by ring⟩, le_iff_exists_add.2 ⟨z, by ring⟩,
      le_iff_exists_add.2 ⟨x + q, by ring⟩, le_iff_exists_add.2 ⟨p + z, by ring⟩⟩
  unfold invLen coinvLen
  rw [L1, L2, L3, L4, r1, r4]
  exact arith _ _ _ _ _
end
