module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnVanishingOnSubalgebraKilledSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnVanishingOnSubalgebraKilledSq
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) →
      ∀ x ∈ C, (e * e) • D x = 0 := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD hB x hx
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → S), (∀ i, f i ∈ C) →
      D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hD.alg 0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hD.add _ (hf j) _ (Subalgebra.sum_mem _ (fun i _ => hf i)), ih]
  have key : ∀ y ∈ C, e • D y = ∑ j, tr (b j * y) • D (a j) := by
    intro y hy
    have heC : e ∈ C := h.le h.e_mem
    have h1 : D (e * y) = e • D y := by
      rw [hD.mul e heC y hy, hB e h.e_mem, smul_zero, add_zero]
    rw [← h1, ← h.left y hy, hsum _ _ (fun j => C.mul_mem (h.a_mem j)
      (h.le (h.tr_mem _ (C.mul_mem (h.b_mem j) hy))))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have ht : tr (b j * y) ∈ B := h.tr_mem _ (C.mul_mem (h.b_mem j) hy)
    rw [hD.mul _ (h.a_mem j) _ (h.le ht), hB _ ht, smul_zero, zero_add]
  have L : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) := by
    simp_rw [key _ (C.mul_mem hx (h.a_mem _)), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    have hr := h.right (b j * x) (C.mul_mem (h.b_mem j) hx)
    calc ∑ i, b i * tr (b j * (x * a i)) = ∑ i, b i * tr (a i * (b j * x)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show b j * (x * a i) = a i * (b j * x) by ring]
      _ = e * (b j * x) := hr
      _ = e * x * b j := by ring
  have R : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) + (e * e) • D x := by
    simp_rw [hD.mul x hx _ (h.a_mem _), smul_add, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1; ring
    · congr 1
      rw [show e * e = e * ∑ i, a i * b i by rw [h.sum], Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  have := R.symm.trans L
  simpa using this

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnVanishingOnSubalgebraKilledSqStatement
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) → ∀ x ∈ C, (e * e) • D x = 0 := by
  first | exact @GlobalTheory.AlmostEt.derOn_killed_sq | exact GlobalTheory.AlmostEt.derOn_killed_sq | (intros; apply GlobalTheory.AlmostEt.derOn_killed_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_mem_span_of_trData : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C,
      (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  intro A S M _ _ _ _ _ B C tr n a b e ht D hD x hx
  set N : Submodule S M := Submodule.span S (D '' (B : Set S))
  have hD' : IsDerOn C (fun s => N.mkQ (D s)) :=
    { add := fun u hu v hv => by simp only [hD.add u hu v hv, map_add (f := _)]
      mul := fun u hu v hv => by simp only [hD.mul u hu v hv, map_add (f := _), map_smul]
      alg := fun r => by simp only [hD.alg r, map_zero] }
  have hB : ∀ β ∈ B, N.mkQ (D β) = 0 := fun β hβ => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨β, hβ, rfl⟩
  have h := GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq A S (M ⧸ N) B C tr n a b e ht (fun s => N.mkQ (D s)) hD' hB x hx
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact h

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValuesStatement
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostDualTrace_derivation_mem_span_values : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C, (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  first | exact @GlobalTheory.AlmostEt.derOn_mem_span_of_trData | exact GlobalTheory.AlmostEt.derOn_mem_span_of_trData | (intros; apply GlobalTheory.AlmostEt.derOn_mem_span_of_trData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CthFacMultipliable
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.CthMult

end GlobalTheory.Sieg.CthMult

theorem _root_.GlobalTheory.Sieg.cthFac_multipliable : ∀ (c : ℕ) (q t : ℂ), ‖q‖ < 1 → t ≠ 0 →
    Multipliable (fun m : ℕ => _root_.GlobalTheory.Sieg.cthFac c q t (m + 1)) := by
  intro c q t hq _
  set g : ℂ → ℂ := fun u => (1 - u * t) ^ c ^ 2 * (1 - u * t⁻¹) ^ c ^ 2 /
    ((1 - u * t ^ c) * (1 - u * (t ^ c)⁻¹)) with hg
  have hgd : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    simp
  have hg0 : g 0 = 1 := by simp [hg]
  have hbig : (fun m : ℕ => g (q ^ (m + 1)) - 1) =O[Filter.atTop] (fun m : ℕ => q ^ (m + 1)) := by
    have h := hgd.isBigO_sub
    rw [hg0] at h
    simp only [sub_zero] at h
    have ht : Filter.Tendsto (fun m : ℕ => q ^ (m + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    exact h.comp_tendsto ht
  have hsum : Summable (fun m : ℕ => ‖g (q ^ (m + 1)) - 1‖) := by
    refine summable_of_isBigO_nat (g := fun m : ℕ => ‖q‖ ^ (m + 1)) ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
    · simpa [norm_pow] using hbig.norm_left.norm_right
  have hmul := multipliable_one_add_of_summable hsum
  simpa [hg, _root_.GlobalTheory.Sieg.cthFac] using hmul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelation
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (x y : ℂ) : ∏ j ∈ Finset.range m, (x - ζ ^ j * y) = x ^ m - y ^ m := by
  have hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (Finset.range m) := fun i hi j hj h =>
    hζ.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have himage :
      (Finset.range m).image (fun j : ℕ => ζ ^ j) = Polynomial.nthRootsFinset m (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Polynomial.mem_nthRootsFinset hm, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [hζ.pow_sub_pow_eq_prod_sub_mul x y hm, ← himage, Finset.prod_image hinj]

theorem _root_.GlobalTheory.Sieg.ee_nat_div_eq_pow (m j : ℕ) :
    _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m) = Complex.exp (2 * Real.pi * Complex.I / m) ^ j := by
  rw [_root_.GlobalTheory.Sieg.ee, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow {c m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hm : 0 < m) (hc : Nat.Coprime c m) (q t : ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) n =
      _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) n := by
  have key : ∀ {ξ : ℂ}, IsPrimitiveRoot ξ m → ∀ (u : ℂ) (g : ℕ → ℂ), (∀ j, g j = ξ ^ j * u) →
      ∏ j ∈ Finset.range m, (1 - q ^ n * g j) = 1 - (q ^ m) ^ n * u ^ m := by
    intro ξ hξ u g hg
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hξ hm 1 (q ^ n * u)
    rw [one_pow] at h
    calc ∏ j ∈ Finset.range m, (1 - q ^ n * g j)
          = ∏ j ∈ Finset.range m, (1 - ξ ^ j * (q ^ n * u)) :=
          Finset.prod_congr rfl fun j _ => by rw [hg]; ring
      _ = _ := by rw [h]; ring
  unfold _root_.GlobalTheory.Sieg.cthFac
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
    Finset.prod_pow, key hζ t _ (fun j => by ring),
    key hζ.inv t⁻¹ _ (fun j => by rw [mul_inv, inv_pow]; ring),
    key (hζ.pow_of_coprime c hc) (t ^ c) _
      (fun j => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring),
    key (hζ.pow_of_coprime c hc).inv (t ^ c)⁻¹ _
      (fun j => by rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm c j, mul_inv]; ring)]
  ring

theorem _root_.GlobalTheory.Sieg.prod_cth_mul_ee : ∀ (c m : ℕ) (q t : ℂ), 1 < c →
    Nat.Coprime c 6 → 0 < m → Nat.Coprime c m →
    ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) →
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cth c q (t * _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m)) =
      _root_.GlobalTheory.Sieg.cth c (q ^ m) (t ^ m) := by
  intro c m q t _ _ hm hc hq _ ht _
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  simp only [_root_.GlobalTheory.Sieg.ee_nat_div_eq_pow]
  rw [← hζdef]
  have hA : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t
    simp only [zero_pow hm.ne', zero_sub] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hB : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t
    rw [one_pow] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hC : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)
    rw [one_pow, ← pow_mul, mul_comm c m, pow_mul] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring
  have hD : ∏ j ∈ Finset.range m, ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) (n + 1) =
      ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) (n + 1) := by
    rw [← Multipliable.tprod_finsetProd fun j _ =>
      _root_.GlobalTheory.Sieg.cthFac_multipliable c q _ hq (mul_ne_zero ht (pow_ne_zero _ hζ0))]
    exact tprod_congr fun n => _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow hζ hm hc q t (n + 1)
  unfold _root_.GlobalTheory.Sieg.cth
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow,
    Finset.prod_const, Finset.card_range, hB, hC, hD]
  rw [hA]

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelationStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_distribution_relation : ∀ (c m : ℕ) (q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) → ∏ j ∈ Finset.range m, cth c q (t * ee ((j : ℂ) / m)) = cth c (q ^ m) (t ^ m) := by
  first | exact @GlobalTheory.Sieg.prod_cth_mul_ee | exact GlobalTheory.Sieg.prod_cth_mul_ee | (intros; apply GlobalTheory.Sieg.prod_cth_mul_ee <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjectiveCokerOfIsLocallyConstantFinrankRange
open TensorProduct Module Function Filter Topology

namespace GlobalTheory

open Semicont

section FiniteModule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_away_equiv_of_eventually_finrank_fiber_eq [IsReduced R] [Module.Finite R M]
    (p : PrimeSpectrum R)
    (h : ∀ᶠ q : PrimeSpectrum R in 𝓝 p,
      finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    ∃ f ∉ p.asIdeal, Nonempty
      ((Fin (finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) →
        Localization.Away f) ≃ₗ[Localization.Away f] LocalizedModule.Away f M) := by
  obtain ⟨φ, hφ⟩ := exists_baseChange_surjective (R := R) (M := M) p.asIdeal.ResidueField
  have h1 := h.and ((isOpen_setOf_baseChange_surjective φ).mem_nhds hφ)
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 h1
  have hker : ∀ x, φ x = 0 → f • x = 0 := by
    intro x hx
    ext j
    refine IsReduced.eq_zero _ (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
    by_cases hfJ : f ∈ J
    · exact J.mul_mem_right _ hfJ
    obtain ⟨h2, h3⟩ := hf (show (⟨J, hJ⟩ : PrimeSpectrum R) ∈ _ from hfJ)
    have hinj : Injective (φ.baseChange J.ResidueField) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((finrank_baseChange_fin _ _).trans h2.symm)).2 h3
    have h4 : (1 : J.ResidueField) ⊗ₜ[R] x = 0 := hinj (by simp [hx])
    have h5 :=
      congrFun (congrArg (TensorProduct.piScalarRight R J.ResidueField J.ResidueField _) h4) j
    refine J.mul_mem_left _ ?_
    rw [← Ideal.algebraMap_residueField_eq_zero]
    simpa [Algebra.smul_def] using h5
  let A := Localization.Away f
  have hsurj : Surjective (φ.baseChange A) := by
    rw [baseChange_surjective_iff]
    have : Subsingleton (LocalizedModule.Away f (M ⧸ LinearMap.range φ)) := by
      rw [LocalizedModule.subsingleton_iff_disjoint, Set.disjoint_left]
      intro q hq
      have h3 : Surjective (φ.baseChange q.asIdeal.ResidueField) := (hf hq).2
      rwa [baseChange_surjective_iff, ← not_nontrivial_iff_subsingleton,
        ← Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h3
    exact (LocalizedModule.equivTensorProduct (Submonoid.powers f) _).symm.toEquiv.subsingleton
  have hinj : Injective (φ.baseChange A) := by
    have : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
    rw [← LinearMap.ker_eq_bot, ← baseChange_ker, Submodule.baseChange_eq_span, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hu : IsUnit (algebraMap R A f) := IsLocalization.Away.algebraMap_isUnit f
    refine (hu.smul_eq_zero).1 ?_
    rw [algebraMap_smul, ← map_smul, hker x hx, map_zero]
  exact ⟨f, hpf, ⟨(TensorProduct.piScalarRight R A A _).symm ≪≫ₗ
    LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩ ≪≫ₗ
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm⟩⟩

theorem finitePresentation_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.FinitePresentation R M := by
  refine Module.FinitePresentation.of_localizationSpan
    {f | Module.FinitePresentation (Localization.Away f) (LocalizedModule.Away f M)} ?_
    fun g => g.2
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_away_equiv_of_eventually_finrank_fiber_eq (M := M)
    ⟨m, hm.isPrime⟩ (h.eventually_eq _)
  exact hf (hle (Ideal.subset_span (Module.FinitePresentation.of_equiv e)))

theorem projective_of_finite_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Projective R M :=
  have := finitePresentation_of_isLocallyConstant_finrank_fiber h
  projective_of_isLocallyConstant_finrank_fiber h

theorem finrank_tensorProduct_eq_finrank_fiber (k : Type*) [Field k] [Algebra R k]
    (p : PrimeSpectrum R) (hp : p.asIdeal = RingHom.ker (algebraMap R k)) :
    finrank k (k ⊗[R] M) = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  letI : Algebra p.asIdeal.ResidueField k :=
    (Ideal.ResidueField.lift p.asIdeal (algebraMap R k) hp.le (fun x hx => by
      refine IsUnit.mk0 _ fun h0 => hx ?_
      rw [hp]
      exact h0)).toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (Ideal.ResidueField.lift_algebraMap ..).symm
  rw [← (AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField k k M).finrank_eq,
    Module.finrank_baseChange]

end FiniteModule

section Map

variable {R : Type*} [CommRing R] {E F : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

theorem finrank_baseChange_coker_add_finrank_range [Module.Finite R F]
    (k : Type*) [Field k] [Algebra R k] (φ : E →ₗ[R] F) :
    finrank k (k ⊗[R] (F ⧸ LinearMap.range φ)) + finrank k (LinearMap.range (φ.baseChange k)) =
      finrank k (k ⊗[R] F) := by
  rw [(baseChangeQuotEquiv k _).finrank_eq, baseChange_range]
  exact Submodule.finrank_quotient_add_finrank _

theorem projective_coker_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    Module.Projective R (F ⧸ LinearMap.range φ) := by
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    ((IsLocallyConstant.iff_eventually_eq _).2 fun p => ?_)
  filter_upwards [h.eventually_eq p, (Semicont.isLocallyConstant_finrank_fiber F).eventually_eq p]
    with q h1 h2
  have h3 := finrank_baseChange_coker_add_finrank_range p.asIdeal.ResidueField φ
  have h4 := finrank_baseChange_coker_add_finrank_range q.asIdeal.ResidueField φ
  omega

theorem exists_comp_comp_eq_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    ∃ s : F →ₗ[R] E, φ ∘ₗ s ∘ₗ φ = φ :=
  have := projective_coker_of_isLocallyConstant_finrank_range φ h
  exists_comp_comp_eq_of_projective φ

theorem exists_retraction_ker_of_generalizedInverse (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) :
    ∃ r : E →ₗ[R] LinearMap.ker φ, r ∘ₗ (LinearMap.ker φ).subtype = LinearMap.id := by
  have hs' : ∀ x, φ (s (φ x)) = φ x := LinearMap.congr_fun hs
  refine ⟨(LinearMap.id - s ∘ₗ φ).codRestrict _ fun x => by simp [hs'], ?_⟩
  ext x
  simp

theorem lTensor_subtype_injective_of_retraction (P : Submodule R E) (r : E →ₗ[R] P)
    (hr : r ∘ₗ P.subtype = LinearMap.id) (N : Type*) [AddCommGroup N] [Module R N] :
    Injective (P.subtype.lTensor N) :=
  LeftInverse.injective (g := r.lTensor N) fun x => by
    rw [← LinearMap.lTensor_comp_apply, hr, LinearMap.lTensor_id, LinearMap.id_apply]

theorem baseChange_ker_of_comp_comp_eq (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) (S : Type*) [CommRing S] [Algebra R S] :
    (LinearMap.ker φ).baseChange S = LinearMap.ker (φ.baseChange S) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]
  · intro hz
    obtain ⟨y, hy⟩ := (tensorKer_bijective_of_comp_comp_eq S S φ s hs).2 ⟨z, hz⟩
    exact ⟨y, (LinearMap.tensorKer_coe S S φ y).symm.trans (congrArg Subtype.val hy)⟩

universe u v

end Map

universe u v w

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
noncomputable section

namespace GlobalTheory.AlmostEt

variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

def trTwist (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x : S) : M :=
  ∑ i, a i • D (tr (b i * x))

def trTwistDefect (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x u : S) : M :=
  trTwist tr a b D (x * u) - x • trTwist tr a b D u

def trExtDer (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) (D : S → M) (y : S) : M :=
  e • ∑ j, b j • trTwistDefect tr a b D y (a j)

variable {B C : Subalgebra A S} {tr : S → S} {n : ℕ} {a b : Fin n → S} {e : S} {D : S → M}

theorem trTwist_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : trTwist tr a b D (x + y) = trTwist tr a b D x + trTwist tr a b D y := by
  unfold trTwist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := C.mul_mem (h.b_mem i) hx
  have h2 := C.mul_mem (h.b_mem i) hy
  rw [mul_add, h.tr_add _ h1 _ h2, hD.add _ (h.tr_mem _ h1) _ (h.tr_mem _ h2), smul_add]

theorem trTwist_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β x : S} (hβ : β ∈ B)
    (hx : x ∈ C) : trTwist tr a b D (β * x) = β • trTwist tr a b D x + (e * x) • D β := by
  unfold trTwist
  have key : ∀ i, a i • D (tr (b i * (β * x))) =
      β • (a i • D (tr (b i * x))) + (a i * tr (b i * x)) • D β := by
    intro i
    have h1 := C.mul_mem (h.b_mem i) hx
    have hm : b i * (β * x) = β * (b i * x) := by ring
    rw [hm, h.tr_mul _ hβ _ h1, hD.mul _ hβ _ (h.tr_mem _ h1), smul_add, mul_smul, smul_comm (a i) β]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, h.left x hx]

theorem trTwist_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    trTwist tr a b D (0 : S) = 0 := by
  have := trTwist_add h hD C.zero_mem C.zero_mem
  rw [add_zero] at this
  simpa using this

theorem defect_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x u v : S} (hx : x ∈ C)
    (hu : u ∈ C) (hv : v ∈ C) :
    trTwistDefect tr a b D x (u + v) = trTwistDefect tr a b D x u + trTwistDefect tr a b D x v := by
  unfold trTwistDefect
  rw [mul_add, trTwist_add h hD (C.mul_mem hx hu) (C.mul_mem hx hv), trTwist_add h hD hu hv, smul_add]
  abel

theorem defect_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C) :
    trTwistDefect tr a b D x 0 = 0 := by
  unfold trTwistDefect
  rw [mul_zero, trTwist_zero h hD, smul_zero, sub_zero]

theorem defect_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x β u : S} (hx : x ∈ C)
    (hβ : β ∈ B) (hu : u ∈ C) :
    trTwistDefect tr a b D x (β * u) = β • trTwistDefect tr a b D x u := by
  unfold trTwistDefect
  have hm : x * (β * u) = β * (x * u) := by ring
  rw [hm, trTwist_smul h hD hβ (C.mul_mem hx hu), trTwist_smul h hD hβ hu, smul_add, smul_sub,
    smul_smul x (e * u), smul_comm x β]
  have : x * (e * u) = e * (x * u) := by ring
  rw [this]
  abel

theorem defect_sum (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C)
    (c : Fin n → S) (hc : ∀ i, c i ∈ B) :
    trTwistDefect tr a b D x (∑ i, c i * a i) = ∑ i, c i • trTwistDefect tr a b D x (a i) := by
  have : ∀ s : Finset (Fin n), trTwistDefect tr a b D x (∑ i ∈ s, c i * a i) =
      ∑ i ∈ s, c i • trTwistDefect tr a b D x (a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using defect_zero h hD hx
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        defect_add h hD hx (C.mul_mem (h.le (hc j)) (h.a_mem j))
          (C.sum_mem fun i _ => C.mul_mem (h.le (hc i)) (h.a_mem i)),
        defect_smul h hD hx (hc j) (h.a_mem j), ih]
  exact this Finset.univ

theorem defect_mul (x y u : S) :
    trTwistDefect tr a b D (x * y) u =
      trTwistDefect tr a b D x (y * u) + x • trTwistDefect tr a b D y u := by
  unfold trTwistDefect
  rw [smul_sub, mul_assoc, mul_smul]
  abel

theorem trExtDer_swap (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : y • trExtDer tr a b e D x =
      e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) := by

  have step1 : ∀ j, e • (b j • trTwistDefect tr a b D x (y * a j)) =
      ∑ i, (tr (b i * (y * a j)) * b j) • trTwistDefect tr a b D x (a i) := by
    intro j
    have hya := C.mul_mem hy (h.a_mem j)
    have hl : e * (y * a j) = ∑ i, tr (b i * (y * a j)) * a i := by
      rw [← h.left _ hya]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [smul_comm, ← defect_smul h hD hx h.e_mem hya, hl,
      defect_sum h hD hx _ fun i => h.tr_mem _ (C.mul_mem (h.b_mem i) hya), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm (b j)]
  rw [Finset.smul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hr : ∀ i, ∑ j, tr (b i * (y * a j)) * b j = y • (e • b i) := by
    intro i
    have := h.right _ (C.mul_mem (h.b_mem i) hy)
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm y e, mul_assoc, mul_comm y (b i), ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; congr 2; ring
  simp_rw [hr]
  unfold trExtDer
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_smul, smul_eq_mul, mul_assoc]

theorem trExtDer_isDerOn (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    IsDerOn C (trExtDer tr a b e D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    unfold trExtDer
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold trTwistDefect
    rw [← smul_add, add_mul, trTwist_add h hD (C.mul_mem hx (h.a_mem j)) (C.mul_mem hy (h.a_mem j)),
      add_smul]
    congr 1
    abel
  · intro x hx y hy
    have e1 : trExtDer tr a b e D (x * y) =
        e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) + x • trExtDer tr a b e D y := by
      unfold trExtDer
      simp_rw [defect_mul, smul_add, Finset.sum_add_distrib, smul_add]
      congr 1
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm (b j) x, smul_comm e x]
    rw [e1, ← trExtDer_swap h hD hx hy, add_comm]
  · intro c
    unfold trExtDer
    have hc : algebraMap A S c ∈ B := B.algebraMap_mem c
    have : ∀ j, b j • trTwistDefect tr a b D (algebraMap A S c) (a j) =
        (b j * (e * a j)) • D (algebraMap A S c) := by
      intro j
      unfold trTwistDefect
      rw [trTwist_smul h hD hc (h.a_mem j), add_sub_cancel_left, smul_smul]
    simp [this, hD.alg c]

theorem trExtDer_apply_of_mem (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β : S} (hβ : β ∈ B) :
    trExtDer tr a b e D β = (e ^ 3) • D β := by
  unfold trExtDer
  have : ∀ j, b j • trTwistDefect tr a b D β (a j) = (b j * (e * a j)) • D β := by
    intro j
    unfold trTwistDefect
    rw [trTwist_smul h hD hβ (h.a_mem j), add_sub_cancel_left, smul_smul]
  simp_rw [this, ← Finset.sum_smul, smul_smul]
  have hs : ∑ j, b j * (e * a j) = e * e := by
    rw [← h.sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; congr 1; ring

theorem exists_derOn_ext : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D →
      ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD
  exact ⟨trExtDer tr a b e D, trExtDer_isDerOn h hD, fun β hβ => trExtDer_apply_of_mem h hD hβ⟩

end GlobalTheory.AlmostEt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefectStatement
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationOn_extension_cube_defect : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D → ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  first | exact @GlobalTheory.AlmostEt.exists_derOn_ext | exact GlobalTheory.AlmostEt.exists_derOn_ext | (intros; apply GlobalTheory.AlmostEt.exists_derOn_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitary
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma petersson_smul_of_mem {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f g : CuspForm Γ k) {h : SL(2, ℤ)}
    (hh : h ∈ Γ) (τ : ℍ) : petersson k ⇑f ⇑g (h • τ) = petersson k ⇑f ⇑g τ := by
  have hf : (⇑f ∣[k] h) = ⇑f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ ⟨h, hh, rfl⟩
  have hg : (⇑g ∣[k] h) = ⇑g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn g _ ⟨h, hh, rfl⟩
  rw [← petersson_slash_SL, hf, hg]

def cosetShift (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h₁ : ∀ γ ∈ Γ, σ * γ * σ⁻¹ ∈ Γ) (h₂ : ∀ γ ∈ Γ, σ⁻¹ * γ * σ ∈ Γ) :
    SL(2, ℤ) ⧸ Γ ≃ SL(2, ℤ) ⧸ Γ where
  toFun := Quotient.map' (· * σ⁻¹) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₁ _ hab
  invFun := Quotient.map' (· * σ) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₂ _ hab
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

theorem pet_dia_dia : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) =
        GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  intro N l k d σ _ _ hσ f g
  have h₁ : ∀ γ ∈ lev N l, σ * γ * σ⁻¹ ∈ lev N l := fun γ hγ => GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l d σ γ hσ hγ
  have hσ' : IsDia N l (σ 0 0) σ⁻¹ := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl, hσ.1]
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h₂ : ∀ γ ∈ lev N l, σ⁻¹ * γ * σ ∈ lev N l := fun γ hγ => by
    simpa using GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l _ σ⁻¹ γ hσ' hγ
  set e := cosetShift (lev N l) σ h₁ h₂
  unfold pet
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun γ => ?_
  congr 1
  funext z
  have he : e γ = QuotientGroup.mk (γ.out * σ⁻¹) := by
    conv_lhs => rw [← QuotientGroup.out_eq' γ]
    rfl
  have hx : (QuotientGroup.mk (e γ).out : SL(2, ℤ) ⧸ lev N l) = QuotientGroup.mk (γ.out * σ⁻¹) := by
    rw [QuotientGroup.out_eq', he]
  have hmem := QuotientGroup.eq.mp hx.symm
  have hinv : (e γ).out⁻¹ = ((γ.out * σ⁻¹)⁻¹ * (e γ).out)⁻¹ * (σ * γ.out⁻¹) := by group
  rw [hinv, mul_smul, petersson_smul_of_mem f g (inv_mem hmem), dia, dia, petersson_slash_SL,
    mul_smul]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitaryStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  first | exact @GlobalTheory.Hk.pet_dia_dia | exact GlobalTheory.Hk.pet_dia_dia | (intros; apply GlobalTheory.Hk.pet_dia_dia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMul
noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_inv_qParam_pow_mul {M a : ℕ} (ha : a < M) {g : ℍ → ℂ}
    (hg : g =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    Tendsto (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹ * g τ) atImInfty (𝓝 0) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_le a).trans_lt ha
  have haM : (a : ℝ) < M := by exact_mod_cast ha
  have h1 : (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (2 * Real.pi * τ.im * a / M) := by
    refine Asymptotics.IsBigO.of_norm_le fun τ => le_of_eq ?_
    rw [norm_inv, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, ← Real.exp_neg, coe_im]
    congr 1; ring
  refine (h1.mul hg).trans_tendsto ?_
  have hr : -2 * Real.pi * (1 - a / M) < 0 := by
    have : (a : ℝ) / M < 1 := (div_lt_one hM).2 haM
    have := Real.pi_pos
    nlinarith
  have h2 : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  refine (Real.tendsto_exp_atBot.comp (h2.const_mul_atTop_of_neg hr)).congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_add]; congr 1; ring

theorem sum_mul_co_eq {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} {w : Fin r → ℤ}
    {F : Fin r → ℍ → ℂ} (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (l : Fin r) {a : ℕ} (ha : a < M) (c : Fin r → ℂ)
    (hc : ∀ i, (leadM M s w F).mulVec c i = co M (w l) (F l) (s i) a) (x : SL(2, ℤ)) {n : ℕ} (hn : n < M) :
    ∑ j, c j * co M (w j) (F j) x n = if n = a then co M (w l) (F l) x a else 0 := by
  have H := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  rw [← sub_eq_zero]
  refine GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero M Γ r s
    (fun x n => ∑ j, c j * co M (w j) (F j) x n - if n = a then co M (w l) (F l) x a else 0)
    hM hs ?_ ?_ ?_ ?_ x n hn
  · intro x n
    simp only [fun j => (H j).1, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · split_ifs with h
      · rw [h]
      · simp
  · intro γ hγ x n
    simp only [fun j => (H j).2.1 γ hγ]
  · intro x n
    simp only [fun j => (H j).2.2 (hF j).1, mul_neg, Finset.sum_neg_distrib]
    split_ifs <;> ring
  · intro i
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range M) a, if_pos (Finset.mem_range.2 ha),
      ← hc i, Finset.sum_comm, sub_eq_zero]
    simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, mul_comm]

theorem exists_tendsto_evM_mul (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (leadM M s w F).det ≠ 0) :
    ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ,
      Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧
        Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  set c : Fin r → ℕ → Fin r → ℂ := fun l a =>
    (leadM M s w F)⁻¹.mulVec fun i => co M (w l) (F l) (s i) a with hcdef
  have hc : ∀ l a i, (leadM M s w F).mulVec (c l a) i = co M (w l) (F l) (s i) a := by
    intro l a i
    simp only [hcdef]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  set t : ℍ → ℂ := fun τ => Function.Periodic.qParam (M : ℝ) (τ : ℂ) with ht
  have ht0 : ∀ τ, t τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  refine ⟨fun τ => Matrix.of fun j l => ∑ a ∈ Finset.range M, c l a j * (t τ ^ a)⁻¹, ?_, ?_⟩
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun l => ?_
    have hlim : Tendsto (fun τ : ℍ => leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j *
        ((t τ ^ a)⁻¹ * ((F j ∣[w j] s i) τ -
          ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n))) atImInfty
        (𝓝 (leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j * 0)) := by
      refine tendsto_const_nhds.add (tendsto_finsetSum _ fun a ha => tendsto_finsetSum _ fun j _ => ?_)
      exact (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha)
        (GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 (s i))).const_mul _
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.mul_apply, evM, leadM, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    have key : ∑ j, c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n =
        co M (w l) (F l) (s i) a * t τ ^ a := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ n ∈ Finset.range M, ∑ j, c l a j * (co M (w j) (F j) (s i) n * t τ ^ n) =
          if n = a then co M (w l) (F l) (s i) a * t τ ^ a else 0 := by
        intro n hn
        simp only [← mul_assoc, ← Finset.sum_mul]
        rw [sum_mul_co_eq hM hΓ hs hF l ha' (c l a) (hc l a) (s i) (Finset.mem_range.1 hn)]
        split_ifs with h
        · rw [h]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range M) a, if_pos ha]
    have hta : t τ ^ a ≠ 0 := pow_ne_zero _ (ht0 τ)
    have e : co M (w l) (F l) (s i) a =
        ∑ j, (t τ ^ a)⁻¹ * (c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n) := by
      rw [← Finset.mul_sum, key]; field_simp
    rw [e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun l => ?_
    have hΔ : ModularForm.discriminant =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      simpa [CuspForm.coe_discriminant] using
        CuspFormClass.exp_decay_atImInfty CuspForm.discriminant one_pos one_mem_strictPeriods_SL
    have hlim : Tendsto (fun τ : ℍ => ∑ a ∈ Finset.range M, c l a j *
        ((t τ ^ a)⁻¹ * ModularForm.discriminant τ)) atImInfty (𝓝 (∑ a ∈ Finset.range M, c l a j * 0)) :=
      tendsto_finsetSum _ fun a ha =>
        (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha) hΔ).const_mul _
    simp only [mul_zero, Finset.sum_const_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMulStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det ≠ 0 → ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ, Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧ Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.exists_tendsto_evM_mul | exact GlobalTheory.OddFrame.exists_tendsto_evM_mul | (intros; apply GlobalTheory.OddFrame.exists_tendsto_evM_mul <;> assumption)
end
end
