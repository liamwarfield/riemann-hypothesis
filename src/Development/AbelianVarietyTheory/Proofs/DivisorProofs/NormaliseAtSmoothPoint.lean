module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplexStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueC
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueC
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing KaehlerDifferential

theorem linearIndependent_one_tmul_D {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    {J : Type} (f : J → A) (hf : ∀ j, f j ∈ maximalIdeal A)
    (h : LinearIndependent (ResidueField A) (fun j =>
      ((maximalIdeal A).toCotangent ⟨f j, hf j⟩ : CotangentSpace A))) :
    LinearIndependent (ResidueField A) (fun j => (1 : ResidueField A) ⊗ₜ[A] D k A (f j)) := by
  have hs : Function.Surjective (algebraMap A (ResidueField A)) := residue_surjective
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) hs).mpr
    inferInstance
  have hker : maximalIdeal A = RingHom.ker (algebraMap A (ResidueField A)) := ker_residue.symm
  let c := Ideal.Cotangent.equivOfEq _ _ hker
  let e : CotangentSpace A →ₗ[A] ResidueField A ⊗[A] Ω[A⁄k] :=
    kerCotangentToTensor k A (ResidueField A) ∘ₗ c.toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) := hinj.comp c.injective
  have := h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)
  have key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j =>
      ((maximalIdeal A).toCotangent ⟨f j, hf j⟩ : CotangentSpace A)) =
      fun j => (1 : ResidueField A) ⊗ₜ[A] D k A (f j) := by
    funext j
    simp only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e,
      LinearMap.comp_apply, LinearEquiv.coe_coe, c]
    rw [Ideal.Cotangent.equivOfEq_toCotangent, kerCotangentToTensor_toCotangent]
    rfl
  rw [key] at this
  exact this

theorem span_one_tmul_D {k A : Type} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) {r : ℕ} (τ : Fin r → A)
    (hspan : maximalIdeal A = Ideal.span (Set.range τ)) :
    Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (τ i)) = ⊤ := by
  set S := Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (τ i))
  have hτ0 : ∀ i, residue A (τ i) = 0 := fun i =>
    (residue_eq_zero_iff _).2 (hspan ▸ Ideal.subset_span ⟨i, rfl⟩)

  have h1 : ∀ a : A, (1 : ResidueField A) ⊗ₜ[A] D k A a ∈ S := by
    intro a
    obtain ⟨c, hc⟩ := hres (residue A a)
    have hm : a - algebraMap k A c ∈ Ideal.span (Set.range τ) := by
      rw [← hspan, ← residue_eq_zero_iff, map_sub, ← hc]
      rw [IsScalarTower.algebraMap_apply k A (ResidueField A)]
      exact sub_self _
    obtain ⟨β, hβ⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hm
    have hD : D k A a = ∑ i, (β i • D k A (τ i) + τ i • D k A (β i)) := by
      have : D k A a = D k A (a - algebraMap k A c) := by
        rw [map_sub, Derivation.map_algebraMap, sub_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, ← hβ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Derivation.leibniz, add_comm]
    rw [hD, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (ResidueField A) (τ i), ← algebraMap_smul (ResidueField A) (β i)]
    change _ + residue A (τ i) • _ ∈ S
    rw [hτ0, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h2 : ∀ ω : Ω[A⁄k], (1 : ResidueField A) ⊗ₜ[A] ω ∈ S := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h1 a
    | zero => rw [TensorProduct.tmul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (ResidueField A) a]
      exact S.smul_mem _ hx
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul c ω =>
    have : c ⊗ₜ[A] ω = c • ((1 : ResidueField A) ⊗ₜ[A] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact S.smul_mem _ (h2 ω)
  | add x y hx hy => exact S.add_mem hx hy

end GlobalTheory.EtaleCoordLocal

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing KaehlerDifferential

theorem exists_coords (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] [Algebra.EssFiniteType k A] [Algebra.FormallySmooth k A]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) :
    ∃ (r : ℕ) (τ : Fin r → A), maximalIdeal A = Ideal.span (Set.range τ) ∧
      ∃ b : Module.Basis (Fin r) A Ω[A⁄k], ∀ i, b i = D k A (τ i) := by
  classical
  haveI : Algebra.FormallySmooth k (ResidueField A) :=
    Algebra.FormallySmooth.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField A)) ⟨(algebraMap k _).injective, hres⟩)
  let b0 := Module.finBasis (ResidueField A) (CotangentSpace A)
  choose τ' hτ' using fun i => Ideal.toCotangent_surjective (maximalIdeal A) (b0 i)
  have hspan : maximalIdeal A = Ideal.span (Set.range fun i => (τ' i : A)) := by
    have h1 : Submodule.span (ResidueField A) ((maximalIdeal A).toCotangent '' Set.range τ') = ⊤ := by
      rw [← Set.range_comp, show (maximalIdeal A).toCotangent ∘ τ' = ⇑b0 from funext hτ', b0.span_eq]
    rw [CotangentSpace.span_image_eq_top_iff] at h1
    have h2 := congrArg (Submodule.map (maximalIdeal A).subtype) h1
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
    exact h2.symm
  refine ⟨_, fun i => (τ' i : A), hspan, ?_⟩
  have hli := linearIndependent_one_tmul_D (k := k) (fun i => (τ' i : A)) (fun i => (τ' i).2)
    (by
      have : (fun i => (maximalIdeal A).toCotangent ⟨(τ' i : A), (τ' i).2⟩) = ⇑b0 := funext hτ'
      rw [this]
      exact b0.linearIndependent)
  have hsp := span_one_tmul_D hres (fun i => (τ' i : A)) hspan
  haveI : Module.FinitePresentation A Ω[A⁄k] := Module.finitePresentation_of_finite A _
  exact Module.exists_basis_of_basis_baseChange (R := A) (fun i => D k A (τ' i : A)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal A).subtype
      Subtype.val_injective)

theorem formallyEtale_eval₂Hom_of_basis (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    [Algebra.FormallySmooth k A] {r : ℕ} (τ : Fin r → A) (b : Module.Basis (Fin r) A Ω[A⁄k])
    (hb : ∀ i, b i = D k A (τ i)) : (MvPolynomial.eval₂Hom (algebraMap k A) τ).FormallyEtale := by
  letI := (MvPolynomial.eval₂Hom (algebraMap k A) τ).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (MvPolynomial.eval₂Hom_C _ τ c).symm
  have hX (i : Fin r) : algebraMap (MvPolynomial (Fin r) k) A (MvPolynomial.X i) = τ i :=
    MvPolynomial.eval₂Hom_X' _ τ i
  have he : mapBaseChange k (MvPolynomial (Fin r) k) A =
      (((mvPolynomialBasis k (Fin r)).baseChange A).equiv b (Equiv.refl _)).toLinearMap := by
    refine ((mvPolynomialBasis k (Fin r)).baseChange A).ext fun i => ?_
    rw [EtaleCoordJacobian.mapBaseChange_basis, hX, ← hb]
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange k (MvPolynomial (Fin r) k) A) := by
    rw [he]; exact LinearEquiv.bijective _
  have h1 : Subsingleton Ω[A⁄MvPolynomial (Fin r) k] := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨x, rfl⟩ := map_surjective k (MvPolynomial (Fin r) k) A y
    exact (exact_mapBaseChange_map k (MvPolynomial (Fin r) k) A x).2 (hbij.2 x)
  have h2 : Subsingleton (Algebra.H1Cotangent (MvPolynomial (Fin r) k) A) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    have h3 : Algebra.H1Cotangent.δ k (MvPolynomial (Fin r) k) A y = 0 := by
      apply hbij.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange k (MvPolynomial (Fin r) k) A _).2 ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ k (MvPolynomial (Fin r) k) A y).1 h3
    rw [Subsingleton.elim x 0, map_zero]
  exact (⟨h1, h2⟩ : Algebra.FormallyEtale (MvPolynomial (Fin r) k) A)

end GlobalTheory.EtaleCoordLocal

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing

theorem exists_etaleCoords : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ')
    (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B),
      (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  intro κ' _ _ B hB hres hsm
  letI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ').codRestrict B hB.const_mem
  letI : Algebra ℂ B := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ B := hB.essFiniteType
  haveI : Algebra.FormallySmooth ℂ B := hsm
  haveI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℂ B
  have hres' : Function.Surjective (algebraMap ℂ (ResidueField B)) := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := hres x x.2
    refine ⟨a, ?_⟩
    have hn : ¬ IsUnit (x - c0 a) := (nonUnit_iff (R := B) (x - c0 a)).1 ha
    have hm : x - c0 a ∈ maximalIdeal B := (mem_maximalIdeal _).2 hn
    rw [IsScalarTower.algebraMap_apply ℂ B (ResidueField B)]
    have := (residue_eq_zero_iff _).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨r, τ, hspan, b, hb⟩ := exists_coords ℂ B hres'
  refine ⟨r, τ, hspan, formallyEtale_eval₂Hom_of_basis ℂ B τ b hb, ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have hmax : maximalIdeal B = ⊥ := by
      rw [hspan, Set.range_eq_empty, Ideal.span_empty]
    have hB0 : ∀ x : B, ∃ a : ℂ, x = c0 a := by
      intro x
      obtain ⟨a, ha⟩ := hres x x.2
      have hn : ¬ IsUnit (x - c0 a) := (nonUnit_iff (R := B) (x - c0 a)).1 ha
      have hm : x - c0 a ∈ maximalIdeal B := (mem_maximalIdeal _).2 hn
      rw [hmax, Ideal.mem_bot, sub_eq_zero] at hm
      exact ⟨a, hm⟩
    have halg : Algebra.IsAlgebraic ℂ κ' := by
      refine ⟨fun f => ?_⟩
      obtain ⟨p, hp, q, hq, hq0, e⟩ := hB.frac f
      obtain ⟨a, ha⟩ := hB0 ⟨p, hp⟩
      obtain ⟨d, hd⟩ := hB0 ⟨q, hq⟩
      have ha' : p = algebraMap ℂ κ' a := congrArg Subtype.val ha
      have hd' : q = algebraMap ℂ κ' d := congrArg Subtype.val hd
      have hf : f = algebraMap ℂ κ' (a / d) := by
        rw [map_div₀, ← ha', ← hd', eq_div_iff hq0, e]
      rw [hf]
      exact isAlgebraic_algebraMap _
    have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
    exact (algebraicIndependent_empty_type : AlgebraicIndependent ℂ fun i : Fin 0 => (τ i : κ')).isTranscendenceBasis_of_trdeg_le_of_finite
      (by rw [trdeg_eq_zero]; exact zero_le)
  · exact trBasis_of_isFreeGen_dForm (algebraMap ℂ κ') B hB r τ hr
      (TopForm.isFreeGen_dForm τ b hb)

end GlobalTheory.EtaleCoordLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueCStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B), (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  first | exact @GlobalTheory.EtaleCoordLocal.exists_etaleCoords | exact GlobalTheory.EtaleCoordLocal.exists_etaleCoords | (intros; apply GlobalTheory.EtaleCoordLocal.exists_etaleCoords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothFiniteTypeSubalgebraInRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothFiniteTypeSubalgebraInRing
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem Place.exists_smooth_subalgebra : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (S : Finset κ'),
    (∀ x ∈ S, x ∈ F.ring) → ∃ A : Subalgebra ℂ κ', Algebra.Smooth ℂ A ∧
      A.toSubring ≤ F.ring.toSubring ∧ (∀ x ∈ S, x ∈ A) ∧
      ∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
  intro κ' _ _ F S hS
  classical
  let R := F.ring
  letI : Algebra ℂ R := F.const.toAlgebra
  haveI : IsScalarTower ℂ R κ' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := F.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  let R' : Subalgebra ℂ κ' :=
    { F.ring.toSubring with algebraMap_mem' := F.const_mem }
  let T : Set κ' := ((σ.image (fun x : R => (x : κ')) ∪ S : Finset κ') : Set κ')
  let A₀ : Subalgebra ℂ κ' := Algebra.adjoin ℂ T
  have hT : T ⊆ R' := by
    intro x hx
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hx
    rcases hx with ⟨y, -, rfl⟩ | hx
    · exact y.2
    · exact hS x hx
  have hA₀R : A₀ ≤ R' := Algebra.adjoin_le hT

  have memA₀ : ∀ x : R, x ∈ Algebra.adjoin ℂ (σ : Set R) → (x : κ') ∈ A₀ := by
    intro x hx
    have h1 : (IsScalarTower.toAlgHom ℂ R κ') x ∈
        (Algebra.adjoin ℂ (σ : Set R)).map (IsScalarTower.toAlgHom ℂ R κ') := ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe]
    exact Or.inl ⟨y, hy, rfl⟩
  have hfg : Algebra.FiniteType ℂ A₀ :=
    (Subalgebra.fg_iff_finiteType A₀).mp (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FinitePresentation ℂ A₀ := Algebra.FinitePresentation.of_finiteType.mp hfg
  let ι : A₀ →+* R := (A₀.val.toRingHom).codRestrict R (fun x => hA₀R x.2)
  letI : Algebra A₀ R := ι.toAlgebra
  haveI : IsScalarTower ℂ A₀ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let q : Ideal A₀ := (IsLocalRing.maximalIdeal R).comap ι
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization q.primeCompl R := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      by_contra h; exact ht ((IsLocalRing.mem_maximalIdeal _).2 h)
    · intro r
      obtain ⟨t, htA, ht, h⟩ := hσ r
      refine ⟨⟨⟨_, memA₀ _ h⟩, ⟨⟨_, memA₀ _ htA⟩, fun hq => ?_⟩⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · intro x y e
      refine ⟨1, ?_⟩
      have : (x : κ') = y := congrArg (fun z : R => (z : κ')) e
      simp [Subtype.ext this]
  haveI : Algebra.FormallySmooth ℂ R := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ R
  haveI : Algebra.IsSmoothAt ℂ q := by
    have e := (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars ℂ
    exact Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨g, hgq, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℂ q
  have hgu : IsUnit (ι g) := by
    by_contra h; exact hgq ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hg0 : (g : κ') ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have := congrArg (fun x : R => (x : κ')) hu
    simp [ι, h0] at this
  have hgu' : IsUnit (A₀.val g) := (isUnit_iff_ne_zero).2 hg0
  let φ : Localization.Away g →ₐ[ℂ] κ' := IsLocalization.Away.liftAlgHom g hgu'

  have hφ : ∀ a : A₀, φ (algebraMap A₀ (Localization.Away g) a) = a := by
    intro a; simp [φ]
  have hginv : (g : κ')⁻¹ ∈ F.ring := by
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have h1 : (g : κ') * (u : κ') = 1 := by
      have := congrArg (fun x : R => (x : κ')) hu; simpa [ι] using this
    rw [inv_eq_of_mul_eq_one_right h1]; exact u.2
  have hpow : ∀ s ∈ Submonoid.powers g, (s : κ') ≠ 0 ∧ (s : κ')⁻¹ ∈ F.ring := by
    rintro s ⟨n, rfl⟩
    refine ⟨by simpa using pow_ne_zero n hg0, ?_⟩
    simpa [inv_pow] using pow_mem hginv n
  have hrep : ∀ x : Localization.Away g, ∃ a : A₀, ∃ s ∈ Submonoid.powers g,
      φ x * (s : κ') = a := by
    intro x
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨a, s, hs, ?_⟩
    have := congrArg φ e
    rw [map_mul, hφ, hφ] at this
    exact this
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    have h1 := congrArg φ e
    rw [map_mul, hφ, hφ, hx, zero_mul] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units (Localization.Away g) (⟨s, hs⟩ : Submonoid.powers g)).mul_left_eq_zero.1 e
  let A : Subalgebra ℂ κ' := φ.range
  haveI : Algebra.Smooth ℂ A := Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φ hinj)
  have hA₀A : ∀ a ∈ A₀, a ∈ A := fun a ha => ⟨algebraMap A₀ _ ⟨a, ha⟩, hφ ⟨a, ha⟩⟩
  refine ⟨A, inferInstance, ?_, fun x hx => hA₀A x (Algebra.subset_adjoin ?_), ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, s, hs, e⟩ := hrep x
    obtain ⟨hs0, hsi⟩ := hpow s hs
    have : φ x = a * (s : κ')⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    show φ x ∈ F.ring
    rw [this]; exact F.ring.mul_mem _ _ (hA₀R a.2) hsi
  · simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe]; exact Or.inr hx
  · intro f
    have hfrac : ∃ a ∈ F.ring, ∃ b ∈ F.ring, b ≠ 0 ∧ f * b = a := by
      obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := F.ring) f
      have hb0 : (b : κ') ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
      refine ⟨a, a.2, b, b.2, hb0, ?_⟩
      rw [← e]
      exact div_mul_cancel₀ _ hb0
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hfrac
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    have unit_ne : ∀ t : R, IsUnit t → (t : κ') ≠ 0 := by
      intro t ht h0
      obtain ⟨u, hu⟩ := ht.exists_right_inv
      have := congrArg (fun x : R => (x : κ')) hu
      simp [h0] at this
    refine ⟨r1 * t1 * t2, hA₀A _ ?_, r2 * t2 * t1, hA₀A _ ?_, ?_, ?_⟩
    · simpa using A₀.mul_mem (memA₀ _ h1) (memA₀ _ ht2A)
    · simpa using A₀.mul_mem (memA₀ _ h2) (memA₀ _ ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothFiniteTypeSubalgebraInRingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_finiteType_subalgebra_in_ring : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (S : Finset κ'),
    (∀ x ∈ S, x ∈ F.ring) → ∃ A : Subalgebra ℂ κ', Algebra.Smooth ℂ A ∧
      A.toSubring ≤ F.ring.toSubring ∧ (∀ x ∈ S, x ∈ A) ∧
      ∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
  first | exact @GlobalTheory.FieldPair.Place.exists_smooth_subalgebra | exact GlobalTheory.FieldPair.Place.exists_smooth_subalgebra | (intros; apply GlobalTheory.FieldPair.Place.exists_smooth_subalgebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_locRing_closedPoint_centre : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro κ' _ _ F A hsm hAF hfrac
    haveI : IsFractionRing A κ' := IsFractionRing.of_field A κ' fun z => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac z
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [← e, hb0]⟩
    let ι : A →+* F.ring := (algebraMap A κ').codRestrict F.ring (fun x => hAF x.2)
    let q : Ideal A := (IsLocalRing.maximalIdeal F.ring).comap ι
    have hq : q ≠ ⊤ := by
      intro h
      have h1 : (1 : A) ∈ q := h ▸ Submodule.mem_top
      exact (IsLocalRing.mem_maximalIdeal _).1 (show ι 1 ∈ _ from h1) (by simp)
    obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q hq
    have hinv : ∀ s ∈ n.primeCompl, ((s : A) : κ')⁻¹ ∈ F.ring := by
      intro s hs
      have hs' : ι s ∉ IsLocalRing.maximalIdeal F.ring := fun h => hs (hqn h)
      have hu : IsUnit (ι s) := by
        by_contra h
        exact hs' ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have e : ((s : A) : κ') * (u : κ') = 1 := congrArg Subtype.val hu
      rw [← eq_inv_of_mul_eq_one_right e]
      exact u.2
    have hle : n.primeCompl ≤ nonZeroDivisors A := n.primeCompl_le_nonZeroDivisors
    let B0 : Subalgebra A κ' := Localization.subalgebra.ofField κ' n.primeCompl hle
    haveI : IsLocalization.AtPrime B0 n := Localization.subalgebra.isLocalization_ofField κ' _ hle
    have hAB : A.toSubring ≤ B0.toSubring := fun x hx => B0.algebraMap_mem (⟨x, hx⟩ : A)
    have hc : ∀ a, algebraMap ℂ κ' a ∈ B0.toSubring := fun a => hAB (A.algebraMap_mem a)
    letI : Algebra ℂ B0 := ((algebraMap A B0).comp (algebraMap ℂ A)).toAlgebra
    haveI : IsScalarTower ℂ A B0 := IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := A) (A := B0) rfl
    have hloc : IsLocalRing B0 := IsLocalization.AtPrime.isLocalRing B0 n
    refine ⟨B0.toSubring, ⟨hc, hloc, ?_, ?_⟩, ?_, hAB, ?_, ?_⟩
    · show (algebraMap ℂ B0).EssFiniteType
      refine RingHom.EssFiniteType.comp ?_ ?_
      · exact RingHom.essFiniteType_algebraMap.2 inferInstance
      · exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization B0 n.primeCompl)
    · intro f
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
      exact ⟨a, hAB ha, b, hAB hb, hb0, e⟩
    · intro r hr
      let r' : B0 := ⟨r, hr⟩
      letI : Field (A ⧸ n) := Ideal.Quotient.field n
      haveI : Module.Finite ℂ (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ n)
      have hsurj : Function.Surjective (algebraMap ℂ (A ⧸ n)) :=
        IsAlgClosed.algebraMap_bijective_of_isIntegral.2
      let e := IsLocalization.AtPrime.equivQuotMaximalIdeal n B0
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ r'))
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk n x)
      refine ⟨a, ?_⟩
      let z : B0 := algebraMap A B0 (algebraMap ℂ A a)
      have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0) z = Ideal.Quotient.mk _ r' := by
        rw [← e.apply_symm_apply (Ideal.Quotient.mk _ r'), ← hx, ← ha]
        exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk n B0 (algebraMap ℂ A a)).symm
      have hm : r' - z ∈ IsLocalRing.maximalIdeal B0 := Ideal.Quotient.eq.1 hz.symm
      have hnu := (nonUnit_iff (R := B0.toSubring) (r' - z)).2 ((IsLocalRing.mem_maximalIdeal _).1 hm)
      exact hnu
    · rintro x ⟨a, s, hs, rfl⟩
      exact F.ring.toSubring.mul_mem (hAF a.2) (hinv s hs)
    · show (algebraMap ℂ B0).FormallySmooth
      haveI : Algebra.FormallyEtale A B0 := Algebra.FormallyEtale.of_isLocalization n.primeCompl
      haveI : Algebra.FormallySmooth ℂ B0 := Algebra.FormallySmooth.comp ℂ A B0
      exact RingHom.formallySmooth_algebraMap.2 inferInstance

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointLocalRing_closedPoint_centre_of_place : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  first | exact @GlobalTheory.FieldPair.exists_locRing_closedPoint_centre | exact GlobalTheory.FieldPair.exists_locRing_closedPoint_centre | (intros; apply GlobalTheory.FieldPair.exists_locRing_closedPoint_centre <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothNormalise

theorem inv_mem_of_isField {κ' : Type} [Field κ'] {O : Subring κ'} (hF : IsField O) {f : κ'}
    (hf : f ∈ O) (h0 : f ≠ 0) : f⁻¹ ∈ O := by
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel (a := (⟨f, hf⟩ : O)) (fun e => h0 (congrArg Subtype.val e))
  have : f * (y : κ') = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right this]; exact y.2

theorem const_of_isField {κ' : Type} [Field κ'] [Algebra ℂ κ'] {O : Subring κ'}
    (hO : IsLocModel (algebraMap ℂ κ') O) (hR : RatRes (algebraMap ℂ κ') O) (hF : IsField O) :
    ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α := by
  have hc : ∀ f ∈ O, ∃ α : ℂ, f = algebraMap ℂ κ' α := by
    intro f hf
    obtain ⟨α, hα, h⟩ := hR f hf
    refine ⟨α, ?_⟩
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · by_contra hne
      exact h (inv_mem_of_isField hF hα (sub_ne_zero.2 hne))
  intro x
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hO.frac x
  obtain ⟨α, rfl⟩ := hc a ha
  obtain ⟨β, rfl⟩ := hc b hb
  refine ⟨α / β, ?_⟩
  rw [map_div₀, eq_div_iff hb0, e]

theorem top_model_of_const {κ' : Type} [Field κ'] [Algebra ℂ κ']
    (hc : ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α) :
    ∃ (hB : IsLocModel (algebraMap ℂ κ') ⊤), RatRes (algebraMap ℂ κ') ⊤ ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal (⊤ : Subring κ') = Ideal.span (Set.range (Fin.elim0 : Fin 0 → (⊤ : Subring κ')))) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')) := by
  have hsurj : Function.Surjective ((algebraMap ℂ κ').codRestrict (⊤ : Subring κ') (fun _ => trivial)) :=
    fun x => by obtain ⟨α, hα⟩ := hc x; exact ⟨α, Subtype.ext hα.symm⟩
  let hB : IsLocModel (algebraMap ℂ κ') ⊤ :=
    { const_mem := fun _ => trivial
      isLocalRing := (Subring.topEquiv (R := κ')).symm.isLocalRing
      essFiniteType := (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
      frac := fun f => ⟨f, trivial, 1, trivial, one_ne_zero, mul_one f⟩ }
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro r _
    obtain ⟨α, hα⟩ := hc r
    exact ⟨α, by rw [hα, sub_self]; exact nonUnit_zero _⟩
  · letI := hB.isLocalRing
    have hfield : IsField (⊤ : Subring κ') := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
      have ha' : (a : κ') ≠ 0 := fun e => ha (Subtype.ext e)
      exact ⟨⟨(a : κ')⁻¹, trivial⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.1 hfield
  · have hb : Function.Bijective (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))) := by
      refine ⟨fun P Q e => ?_, fun x => ?_⟩
      · rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eq_C_of_isEmpty Q] at e ⊢
        simp only [MvPolynomial.eval₂Hom_C] at e
        exact congrArg _ (((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem).injective e)
      · obtain ⟨α, hα⟩ := hsurj x
        exact ⟨MvPolynomial.C α, by simpa using hα⟩
    letI := (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).toAlgebra
    exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hb)
  · have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_empty_type, ⟨fun x => ?_⟩⟩
    obtain ⟨α, rfl⟩ := hc x
    exact isAlgebraic_algebraMap (algebraMap ℂ (Algebra.adjoin ℂ (Set.range (fun i : Fin 0 => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')))) α)

theorem inv_not_mem {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ'))
    {B : Subring κ'} (hBF : B ≤ F.ring.toSubring) {f : κ'} (hf : f ≠ 0) (hp : 0 < F.ord f) :
    f⁻¹ ∉ B := by
  intro h
  have := (F.ord_nonneg_iff (inv_ne_zero hf)).2 (hBF h)
  rw [F.ord_inv] at this
  omega

theorem nonUnit_sub {κ' : Type} [Field κ'] {B : Subring κ'} [IsLocalRing B] {x y : κ'}
    (hx : NonUnit B x) (hy : NonUnit B y) : NonUnit B (x - y) := by
  have hx' := (nonUnit_iff (R := B) ⟨x, hx.1⟩).1 hx
  have hy' := (nonUnit_iff (R := B) ⟨y, hy.1⟩).1 hy
  have h := (nonUnit_iff (R := B) (⟨x, hx.1⟩ - ⟨y, hy.1⟩)).2
  exact h ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.sub_mem _
    ((IsLocalRing.mem_maximalIdeal _).2 hx') ((IsLocalRing.mem_maximalIdeal _).2 hy')))

theorem normalise_at_smooth_point : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (O : Subring κ') (l : ℕ) (a : Fin l → κ'),
  IsLocModel (algebraMap ℂ κ') O → RatRes (algebraMap ℂ κ') O → a ≠ 0 →
  ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B) (r : ℕ) (τ : Fin r → B),
    RatRes (algebraMap ℂ κ') B ∧ Dominates (RingHom.id κ') B O ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) ∧ ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ B := by
  classical
  intro κ' _ _ O l a hO hR ha
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
  by_cases hF : IsField O
  · have hc := const_of_isField hO hR hF
    obtain ⟨hB, h1, h2, h3, h4⟩ := top_model_of_const hc
    refine ⟨⊤, hB, 0, Fin.elim0, h1, fun f hf => ⟨trivial, fun hn => ?_⟩, h2, h3, h4, j, hj,
      fun _ => trivial⟩
    refine ⟨trivial, Or.inl ?_⟩
    by_contra h0
    rcases hn.2 with h | h
    · exact h0 h
    · exact h (inv_mem_of_isField hF hf h0)
  · obtain ⟨F, hFO, hpos⟩ := GlobalTheory.T.exists_place_dominating_local_domain_complex O hO hF
    obtain ⟨j₀, hj₀, hdiv⟩ : ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ F.ring := by
      obtain ⟨j₀, hj₀s, hmin⟩ := (Finset.univ.filter (fun i => a i ≠ 0)).exists_min_image
        (fun i => F.ord (a i)) ⟨j, by simpa using hj⟩
      have hj₀ : a j₀ ≠ 0 := (Finset.mem_filter.1 hj₀s).2
      refine ⟨j₀, hj₀, fun i => ?_⟩
      by_cases hi : a i = 0
      · rw [hi, zero_div]; exact zero_mem _
      · have hne : a i / a j₀ ≠ 0 := div_ne_zero hi hj₀
        rw [← F.ord_nonneg_iff hne, div_eq_mul_inv, F.ord_mul hi (inv_ne_zero hj₀), F.ord_inv]
        have := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        omega
    letI : Algebra ℂ O := ((algebraMap ℂ κ').codRestrict O hO.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
    obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ O).1 inferInstance
    let S : Finset κ' := σ.image (fun x : O => (x : κ')) ∪ Finset.univ.image (fun i => a i / a j₀)
    have hS : ∀ x ∈ S, x ∈ F.ring := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
        exact hFO _ y.2
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdiv i
    obtain ⟨A, hAs, hAF, hSA, hAfrac⟩ := GlobalTheory.T.exists_smooth_finiteType_subalgebra_in_ring F S hS
    obtain ⟨B, hB, hRB, hAB, hBF, hsm⟩ := GlobalTheory.T.exists_pointLocalRing_closedPoint_centre_of_place F A hAs hAF hAfrac
    obtain ⟨r, τ, hm, het, htr⟩ := GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex B hB hRB hsm
    have hSB : ∀ x ∈ S, x ∈ B := fun x hx => hAB (hSA x hx)
    letI := hB.isLocalRing
    letI := hO.isLocalRing

    have hadj : ∀ t : O, t ∈ Algebra.adjoin ℂ (σ : Set O) → (t : κ') ∈ B := by
      intro t ht
      induction ht using Algebra.adjoin_induction with
      | mem x hx => exact hSB _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      | algebraMap α => exact hB.const_mem α
      | add x y _ _ hx hy => exact B.add_mem hx hy
      | mul x y _ _ hx hy => exact B.mul_mem hx hy

    have hnon : ∀ f ∈ B, NonUnit O f → NonUnit B f := by
      intro f hfB hn
      refine ⟨hfB, ?_⟩
      by_cases h0 : f = 0
      · exact Or.inl h0
      · refine Or.inr (inv_not_mem F hBF h0 (hpos ⟨f, hn.1⟩ ?_ h0))
        exact (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := O) ⟨f, hn.1⟩).1 hn)

    have hunit : ∀ t : O, IsUnit t → (t : κ') ∈ B → (t : κ')⁻¹ ∈ B := by
      intro t ht htB
      by_contra hinv
      have htn : NonUnit B (t : κ') := ⟨htB, Or.inr hinv⟩
      obtain ⟨α, hα⟩ := hR t t.2
      have hαB : algebraMap ℂ κ' α ∈ B := hB.const_mem α
      have hu : NonUnit B ((t : κ') - algebraMap ℂ κ' α) := hnon _ (B.sub_mem htB hαB) hα
      have hc : NonUnit B (algebraMap ℂ κ' α) := by
        simpa using nonUnit_sub htn hu
      by_cases hα0 : α = 0
      · subst hα0
        simp only [map_zero, sub_zero] at hα
        exact (nonUnit_iff (R := O) t).1 hα ht
      · rcases hc.2 with h | h
        · exact hα0 ((map_eq_zero_iff _ (algebraMap ℂ κ').injective).1 h)
        · exact h (by rw [← map_inv₀]; exact hB.const_mem _)
    refine ⟨B, hB, r, τ, hRB, fun f hf => ?_, hm, het, htr, j₀, hj₀,
      fun i => hSB _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
    obtain ⟨t, htA, htu, hft⟩ := hσ ⟨f, hf⟩
    have htB := hadj t htA
    have hfB : f ∈ B := by
      have h1 := hadj _ hft
      have h2 := hunit t htu htB
      have ht0 : (t : κ') ≠ 0 := fun e => htu.ne_zero (Subtype.ext e)
      have : f = (f * (t : κ')) * (t : κ')⁻¹ := by field_simp
      rw [this]
      exact B.mul_mem h1 h2
    exact ⟨hfB, hnon f hfB⟩

end GlobalTheory.SmoothNormalise
