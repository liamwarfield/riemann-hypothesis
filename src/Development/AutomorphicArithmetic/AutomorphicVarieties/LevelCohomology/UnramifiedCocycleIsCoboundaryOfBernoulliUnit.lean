module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.V.ML UpperTheory.V.Bern

namespace UpperTheory.V.X

def prodX {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n)) :
    DirichletCharacter R (f * 2 ^ n) :=
  DirichletCharacter.changeLevel (dvd_mul_right f (2 ^ n)) φ * DirichletCharacter.changeLevel (dvd_mul_left (2 ^ n) f) ξ

structure XData (l d : ℕ) {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n)) : Prop where
  d_pos : 0 < d
  four : 4 ∣ l ^ d - 1
  f_odd : Odd f
  prim : φ.IsPrimitive
  ord : orderOf φ ∣ l ^ d - 1
  prim2 : ξ.IsPrimitive
  big : f * 4 ^ (l ^ d - 1).factorization 2 ≤ 2 ^ n
  odd : φ (-1) * ξ (-1) = -1

def LemmaX : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d f n : ℕ) (φ : DirichletCharacter (PadicAlgCl l) f) (ξ : DirichletCharacter (PadicAlgCl l) (2 ^ n)),
    XData l d φ ξ → ‖genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → PadicAlgCl l)‖ = 1

section

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def redChar {O k : Type} [CommRing O] [Field k] (red : O →+* k) {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) : G ℚ Ω →* kˣ :=
  (Units.map red.toMonoidHom).comp (Chr.dirG ℚ Ω χ)

variable {Ω}

def UnrEv (l : ℕ) {k : Type} [Field k] (γ : G ℚ Ω →* kˣ) (c : G ℚ Ω → k) : Prop :=
  ∀ A : ValuationSubring Ω, ∃ H : Subgroup (G ℚ Ω), ¬ l ∣ H.relIndex (Ine (F := ℚ) A ⊓ γ.ker) ∧
    ∀ g ∈ H, g ∈ Ine (F := ℚ) A → γ g = 1 → c g = 0

end

def UnramifiedCocycleIsCoboundaryOfBernoulliUnit : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (c : HV.Coef l) (k : Type) [Field k] [CharP k l]
    (red : c.O →+* k) (N : ℕ) [NeZero N] (χ : DirichletCharacter c.O N), χ ≠ 1 → ¬ l ∣ orderOf χ →
    (∃ g : G ℚ Ω, (redChar Ω red χ g : k) ≠ red (chiO (k := ℚ) (Ω := Ω) l c.O g : c.O)) →
    ‖genB 1 (χ⁻¹.ringHomComp c.O.val.toRingHom : ZMod N → PadicAlgCl l)‖ = 1 →
    ∀ z : G ℚ Ω → k, IsCoc (redChar Ω red χ) z → UnrEv l (redChar Ω red χ) z → ∃ m : k, ∀ g, z g = (redChar Ω red χ g : k) * m - m

def CorX : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (k : Type) [Field k] [CharP k l]
    (red : c.O →+* k) (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ →
    ∀ γ : G ℚ Ω →* kˣ, (γ = redChar Ω red (prodX φ ξ) ∨ γ = (redChar Ω red (prodX φ ξ))⁻¹) →
    ∀ z : G ℚ Ω → k, IsCoc γ z → UnrEv l γ z → ∃ m : k, ∀ g, z g = (γ g : k) * m - m

end UpperTheory.V.X

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
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

theorem UpperTheory.V.X.So.coefOf :
    ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E], ∃ c : HV.Coef l, ∀ x : PadicAlgCl l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  intro l _ K _
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (int_iff_norm K.val y).1 hy⟩
  · rintro ⟨hx, hn⟩
    exact ⟨⟨x, hx⟩, (int_iff_norm K.val ⟨x, hx⟩).2 hn, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCardLen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem card_simple (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [h : IsSimpleModule O M] : Nat.card M = Nat.card (ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  obtain rfl : I = maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  exact Nat.card_congr e.toEquiv

private theorem card_of_finiteLength (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M]
    [Module O M] (h : IsFiniteLength O M) :
    ∃ k : ℕ, Module.length O M = k ∧ Nat.card M = Nat.card (ResidueField O) ^ k := by
  induction h with
  | of_subsingleton =>
    refine ⟨0, Module.length_eq_zero, ?_⟩
    rw [pow_zero]
    exact Nat.card_of_subsingleton 0
  | @of_simple_quotient M _ _ N _ hS ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      norm_cast
    · have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField O) := card_simple O (M ⧸ N)
      have hsplit := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
      change Nat.card M = Nat.card (M ⧸ N) * Nat.card N at hsplit
      rw [hsplit, hq, hc, pow_succ, mul_comm]

theorem UpperTheory.V.X.So.cardLen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], 1 < Nat.card (ResidueField O) ∧ ∀ (N : Type) [AddCommGroup N] [Module O N], (Module.length O N ≠ ⊤ ↔ Finite N) ∧ (Finite N → Nat.card N = Nat.card (ResidueField O) ^ (Module.length O N).toNat) := by
  intro l _ O _ _ _ _ _
  have : CharZero O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l O).1
  have hres : Finite (ResidueField O) := (UpperTheory.V.abelian₂.dvr_finite l O).2.1
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  refine ⟨h1, fun N _ _ => ?_⟩
  have hfl : Finite N → IsFiniteLength O N := fun _ =>
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  refine ⟨⟨fun h => ?_, fun h => Module.length_ne_top_iff.2 (hfl h)⟩, fun h => ?_⟩
  · obtain ⟨k, -, hk⟩ := card_of_finiteLength O N (Module.length_ne_top_iff.1 h)
    exact Nat.finite_of_card_ne_zero (hk ▸ pow_ne_zero k (by omega))
  · obtain ⟨k, hk1, hk⟩ := card_of_finiteLength O N (hfl h)
    rw [hk, hk1, ENat.toNat_coe]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem finite_quot {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (b : O) (hb : b ≠ 0) : Finite (O ⧸ Ideal.span {b}) := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hb)
  haveI : IsArtinianRing (O ⧸ Ideal.span {b}) :=
    isArtinian_of_tower O (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  exact IsLocalRing.finite_quotient_iff.mpr
    (IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _)

theorem UpperTheory.V.X.So.levFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → Finite M ∧ (∃ r : ℕ, 0 < r ∧ ∀ m : M, (l ^ r) • m = 0) ∧ ∀ d : O, d ≠ 0 → Nat.card {m : M // d • m = 0} ≤ Nat.card (O ⧸ Ideal.span {d}) := by
  intro l _ O _ _ _ _ _ a ha M _ _ hne
  obtain ⟨e⟩ := hne
  haveI : CharZero O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l O).1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfin
  haveI hQa : Finite (O ⧸ Ideal.span {a}) := finite_quot a ha
  haveI : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hkill : ∀ c : O, c ∈ Ideal.span {a} → ∀ z : O ⧸ Ideal.span {a}, c • z = 0 := by
    intro c hc z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hc
  have hgen : ∀ m : M, ∃ y : O, y • e.symm (Ideal.Quotient.mk _ 1) = m := by
    intro m
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e m)
    refine ⟨y, e.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply, ← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, mul_one]
  refine ⟨inferInstance, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (IsLocalRing.finite_quotient_iff (R := O)).mp hQa
    refine ⟨n + 1, Nat.succ_pos n, fun m => ?_⟩
    have hmem : (l : O) ^ (n + 1) ∈ Ideal.span {a} :=
      hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hlm (n + 1)))
    apply e.injective
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact hkill _ hmem _
  · intro d hd
    haveI : Finite (O ⧸ Ideal.span {d}) := finite_quot d hd
    let φ : M →ₗ[O] M := LinearMap.lsmul O M d
    have hker : Nat.card {m : M // d • m = 0} = Nat.card (LinearMap.ker φ) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun m => by simp [φ]))
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φ).toAddSubgroup
    have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range φ).toAddSubgroup
    change Nat.card M = Nat.card (M ⧸ LinearMap.ker φ) * Nat.card (LinearMap.ker φ) at h1
    change Nat.card M = Nat.card (M ⧸ LinearMap.range φ) * Nat.card (LinearMap.range φ) at h2
    rw [Nat.card_congr φ.quotKerEquivRange.toEquiv] at h1
    have hpos : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
    have heq : Nat.card (LinearMap.ker φ) = Nat.card (M ⧸ LinearMap.range φ) := by
      have h3 := h1.symm.trans h2
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h3, mul_comm])
    rw [hker, heq]
    let x0 : M := e.symm (Ideal.Quotient.mk _ 1)
    let f : O →ₗ[O] M ⧸ LinearMap.range φ :=
      (LinearMap.range φ).mkQ ∘ₗ LinearMap.toSpanSingleton O M x0
    have hle : Ideal.span {d} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x0, rfl⟩
    apply Nat.card_le_card_of_surjective ((Ideal.span {d}).liftQ f hle)
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, rfl⟩ := hgen m
    exact ⟨Submodule.Quotient.mk y, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoScal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private def subEq {R R' X : Type} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [Module R' X]
    (Z : Submodule R X) (Z' : Submodule R' X) (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') : Z ≃+ Z' where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem quotEq {R R' X : Type} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [Module R' X]
    (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃+ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨QuotientAddGroup.congr (B.comap Z.subtype).toAddSubgroup (B'.comap Z'.subtype).toAddSubgroup (subEq Z Z' hZ) ?_⟩
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hB _).1 hy
  · intro hx
    exact ⟨⟨x.1, (hZ _).2 x.2⟩, (hB _).2 hx, rfl⟩

theorem UpperTheory.V.X.So.scal :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R' Γ M), (∀ g m, ρ g m = ρ' g m) → Nonempty (H0 ρ ≃+ H0 ρ') ∧ Nonempty (H1 ρ ≃+ H1 ρ') ∧ Nonempty (H2 ρ ≃+ H2 ρ') := by
  intro R R' _ _ Γ _ _ M _ _ _ _ _ ρ ρ' h
  have hd : ∀ c, d1 ρ c = d1 ρ' c := by
    intro c
    funext p
    obtain ⟨g, k⟩ := p
    rw [d1_apply, d1_apply, h]
  refine ⟨⟨subEq _ _ fun x => ?_⟩, quotEq _ _ _ _ (fun x => ?_) (fun x => ?_),
    quotEq _ _ _ _ (fun x => ?_) (fun x => ?_)⟩
  · simp only [mem_riemannRochSpace_iff_regularAt_everywhere, h]
  · simp only [mem_Z1_iff_cocycle, h]
  · simp only [mem_coboundaries1, h]
  · simp only [mem_cocycles2, h]
  · simp only [separated_dvr_second_cohomology_mem, hd]
end
