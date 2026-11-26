module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponent
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem GeomInt.baseChange {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    (K' : Type) [Field K'] [Algebra K K'] : GeomInt K' (K' ⊗[K] R) := by
  haveI := h.1
  refine ⟨inferInstance, fun L _ _ => ?_⟩
  letI : Algebra K L := ((algebraMap K' L).comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := h.2 L
  exact (Algebra.TensorProduct.cancelBaseChange K K' L L R).toMulEquiv.isDomain _

theorem GeomInt.away {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    {r : R} (hr : r ≠ 0) : GeomInt K (Localization.Away r) := by
  haveI := h.1
  haveI : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  refine ⟨Algebra.Smooth.comp K R _, fun L _ _ => ?_⟩
  haveI := h.2 L
  letI : Algebra (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    (Algebra.TensorProduct.map (AlgHom.id L L)
      (IsScalarTower.toAlgHom K R (Localization.Away r))).toAlgebra
  haveI : IsScalarTower L (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right K L (Submonoid.powers r)
    (Localization.Away r) (by ext; simp [RingHom.algebraMap_toAlgebra])
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (hM := ?_) (S := L ⊗[K] Localization.Away r)
    (M := (Submonoid.powers r).map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
  rw [Submonoid.map_powers]
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  exact fun h0 => hr (hinj (by rw [h0, map_zero]))

theorem geomInt_baseChange_and_away :
    ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R],
      GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) :=
  fun _ K' _ _ _ _ _ _ h => ⟨h.baseChange K', fun _ hr => h.away hr⟩

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geom_integral_base_change_and_localization : ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R], GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) := by
  first | exact @GlobalTheory.KeyFam.geomInt_baseChange_and_away | exact GlobalTheory.KeyFam.geomInt_baseChange_and_away | (intros; apply GlobalTheory.KeyFam.geomInt_baseChange_and_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_point_over_of_idempotent {F A B : Type} [Field F] [IsAlgClosed F] [CommRing A]
    [CommRing B] [Algebra F A] [Algebra F B] [IsNoetherianRing A] (f : A →ₐ[F] B)
    (hfin : f.toRingHom.Finite) (hflat : f.toRingHom.Flat) (P : B →ₐ[F] F) (Q : A →ₐ[F] F)
    (h : ∀ e : A, IsIdempotentElem e → P (f e) = Q e) (E : B) (hE : IsIdempotentElem E)
    (hP : P E = 1) : ∃ Q' : B →ₐ[F] F, Q' E = 1 ∧ ∀ a, Q' (f a) = Q a := by
  algebraize [f.toRingHom]
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hcl : IsClopen (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨E, hE, rfl⟩
  have him : IsClopen (PrimeSpectrum.comap (algebraMap A B) ''
      (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B))) :=
    ⟨PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (Algebra.IsIntegral.isIntegral) _ hcl.1,
      PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ hcl.2⟩
  obtain ⟨ε, hε, hεe⟩ := PrimeSpectrum.isClopen_iff.1 him
  have h1 : PrimeSpectrum.comap (algebraMap A B) ⟨RingHom.ker P, RingHom.ker_isPrime P⟩ ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    rw [← hεe]
    refine ⟨_, ?_, rfl⟩
    change ¬ (P E = 0)
    rw [hP]; exact one_ne_zero
  have h2 : (⟨RingHom.ker Q, RingHom.ker_isPrime Q⟩ : PrimeSpectrum A) ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    change ¬ (Q ε = 0)
    rw [← h ε hε]
    exact h1
  rw [← hεe] at h2
  obtain ⟨𝔮, h𝔮E, h𝔮⟩ := h2
  have hker : ∀ a : A, Q a = 0 → f a ∈ 𝔮.asIdeal := by
    intro a ha
    have : a ∈ (PrimeSpectrum.comap (algebraMap A B) 𝔮).asIdeal := by
      rw [h𝔮]; exact ha
    exact this
  have hcomp : ∀ a : A, Ideal.Quotient.mk 𝔮.asIdeal (f a) =
      algebraMap F (B ⧸ 𝔮.asIdeal) (Q a) := by
    intro a
    have := hker (a - algebraMap F A (Q a)) (by simp)
    rw [map_sub, AlgHom.commutes] at this
    exact Ideal.Quotient.eq.2 this
  have hint : (algebraMap F (B ⧸ 𝔮.asIdeal)).IsIntegral := by
    apply RingHom.IsIntegral.tower_top Q.toRingHom
    have : (algebraMap F (B ⧸ 𝔮.asIdeal)).comp Q.toRingHom =
        (Ideal.Quotient.mk 𝔮.asIdeal).comp f.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hfin.to_isIntegral
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  haveI : Algebra.IsIntegral F (B ⧸ 𝔮.asIdeal) := ⟨hint⟩
  have hbij : Function.Bijective (Algebra.ofId F (B ⧸ 𝔮.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := (AlgEquiv.ofBijective _ hbij).symm
  refine ⟨φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal), ?_, fun a => ?_⟩
  · rcases IsIdempotentElem.iff_eq_zero_or_one.1
      (hE.map (φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal))) with h0 | h0
    · exfalso
      apply h𝔮E
      have : Ideal.Quotient.mk 𝔮.asIdeal E = 0 := φ.injective (by rw [map_zero]; exact h0)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    · exact h0
  · change φ (Ideal.Quotient.mk 𝔮.asIdeal (f a)) = _
    rw [hcomp, AlgEquiv.commutes]; rfl

theorem exists_algHom_baseChange_away {k₀ k B L : Type} [Field k₀] [Field k] [Algebra k₀ k]
    [CommRing B] [Algebra k₀ B] [CommRing L] [Algebra k₀ L] [Algebra k L] [IsScalarTower k₀ k L]
    (e : B) (G : B →ₐ[k₀] L) (hG : G e = 1) :
    ∃ s : k ⊗[k₀] Localization.Away e →ₐ[k] L,
      ∀ b, s (1 ⊗ₜ algebraMap B (Localization.Away e) b) = G b := by
  have hu : ∀ y : Submonoid.powers e, IsUnit (G y) := by
    rintro ⟨_, n, rfl⟩
    simp [hG]
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId k L)
    (IsLocalization.liftAlgHom (S := Localization.Away e) hu) (fun _ _ => Commute.all _ _),
    fun b => ?_⟩
  simp

theorem exists_finset_integral_of_finiteType {K T L : Type} [Field K] [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] [CommRing L] [Algebra K L] (g : T →ₐ[K] L)
    (hg : ∀ x, IsIntegral K (g x)) :
    ∃ s : Set L, s.Finite ∧ (∀ y ∈ s, IsIntegral K y) ∧
      ∀ U : Subalgebra K L, s ⊆ U → ∀ x, g x ∈ U := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := K) (A := T)
  refine ⟨g '' t, t.finite_toSet.image _, ?_, fun U hU x => ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact hg x
  · have : Algebra.adjoin K (t : Set T) ≤ U.comap g :=
      Algebra.adjoin_le fun y hy => hU ⟨y, hy, rfl⟩
    rw [ht] at this
    exact this Algebra.mem_top

theorem finite_flat_tensor_map (K F R R₁ : Type) [CommRing K] [CommRing F] [Algebra K F]
    [CommRing R] [Algebra K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁]
    [Module.Finite R R₁] [Module.Flat R R₁] :
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Finite ∧
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Flat := by
  constructor
  · exact RingHom.Finite.tensorProductMap (f := AlgHom.id K F) (RingHom.Finite.id F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.finite_algebraMap.2 inferInstance)
  · exact RingHom.Flat.tensorProductMap (f := AlgHom.id F F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.Flat.id F)
      (RingHom.flat_algebraMap_iff.2 inferInstance)

theorem exists_geomInt_piece_of_finite_etale : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  intro K _ _ _ R R₁ _ _ _ _ _ _ _ K₁ _ _ _ σ₁ p q ⟨hfin, het, hff⟩ hidem
  haveI : Algebra.Smooth K R₁ := Algebra.Smooth.comp K R R₁
  obtain ⟨k₀, e, hk₀, he, hpe, hgi⟩ := GlobalTheory.T.exists_finite_ext_geom_integral_localization K R₁ p
  haveI : IsNoetherianRing (ℂ ⊗[K] R) := Algebra.FiniteType.isNoetherianRing ℂ _
  let f : ℂ ⊗[K] R →ₐ[ℂ] ℂ ⊗[K] R₁ :=
    Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (IsScalarTower.toAlgHom K R R₁)
  obtain ⟨hf1, hf2⟩ : f.toRingHom.Finite ∧ f.toRingHom.Flat := finite_flat_tensor_map K ℂ R R₁
  let emb : k₀ ⊗[K] R₁ →ₐ[K] ℂ ⊗[K] R₁ := Algebra.TensorProduct.map k₀.val (AlgHom.id K R₁)
  let P : ℂ ⊗[K] R₁ →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _)
  have hPemb : ∀ x, P (emb x) = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, emb]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hPf : ∀ x, P (f x) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ)
      (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, f]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨Q', hQE, hQ⟩ := exists_point_over_of_idempotent f hf1 hf2 P
    (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _))
    (fun x hx => (hPf x).trans (hidem x hx)) (emb e) (he.map emb) ((hPemb e).trans hpe)
  let q' : R₁ →ₐ[K] ℂ := (Q'.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hq' : ∀ r, q' (algebraMap R R₁ r) = σ₁ (q r) := by
    intro r
    have := hQ (1 ⊗ₜ r)
    simpa [f, q'] using this
  have hq'int : ∀ x, IsIntegral K (q' x) := by
    intro x
    letI : Algebra K₁ ℂ := σ₁.toRingHom.toAlgebra
    haveI : IsScalarTower K K₁ ℂ := IsScalarTower.of_algebraMap_eq fun a => (σ₁.commutes a).symm
    have h1 : IsIntegral K₁ (q' x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).map_of_comp_eq q.toRingHom q'.toRingHom
        (RingHom.ext fun r => (hq' r).symm)
    exact isIntegral_trans _ h1
  obtain ⟨s₁, hs₁, hs₁i, hs₁U⟩ := exists_finset_integral_of_finiteType q' hq'int
  obtain ⟨s₂, hs₂, hs₂i, hs₂U⟩ := exists_finset_integral_of_finiteType σ₁
    (fun x => (Algebra.IsIntegral.isIntegral (R := K) x).map σ₁)
  let k : IntermediateField k₀ ℂ := IntermediateField.adjoin k₀ (s₁ ∪ s₂)
  haveI : Finite ↥(s₁ ∪ s₂) := (hs₁.union hs₂).to_subtype
  haveI : FiniteDimensional k₀ k := IntermediateField.finiteDimensional_adjoin (by
    rintro x (hx | hx)
    · exact (hs₁i x hx).tower_top
    · exact (hs₂i x hx).tower_top)
  haveI : NumberField k₀ := NumberField.of_module_finite K k₀
  haveI : NumberField k := NumberField.of_module_finite k₀ k
  have hm₁ : ∀ x, q' x ∈ k := hs₁U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inl hy))
  have hm₂ : ∀ x, σ₁ x ∈ k := hs₂U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inr hy))
  let qk : R₁ →ₐ[K] k :=
    { toRingHom := q'.toRingHom.codRestrict k hm₁
      commutes' := fun a => Subtype.ext (q'.commutes a) }
  let G : k₀ ⊗[K] R₁ →ₐ[k₀] ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ ℂ) p (fun _ _ => Commute.all _ _)
  let G₀ : k₀ ⊗[K] R₁ →ₐ[k₀] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ k) qk (fun _ _ => Commute.all _ _)
  have hG : ∀ x, G x = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hG₀ : ∀ x, (G₀ x : ℂ) = Q' (emb x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : emb (a ⊗ₜ b) = (a : ℂ) • ((1 : ℂ) ⊗ₜ[K] b) := by
        simp [emb, TensorProduct.smul_tmul']
      rw [this, map_smul, smul_eq_mul]
      rfl
    | add a b ha hb => simp only [map_add (f := _), ← ha, ← hb]; rfl
  obtain ⟨s, hs⟩ := exists_algHom_baseChange_away (k := k) e G ((hG e).trans hpe)
  obtain ⟨s₀, hs₀⟩ := exists_algHom_baseChange_away (k := k) e G₀
    (Subtype.ext ((hG₀ e).trans hQE))
  refine ⟨k, inferInstance, inferInstance, k ⊗[k₀] Localization.Away e, inferInstance,
    inferInstance,
    (Algebra.TensorProduct.includeRight (R := k₀) (A := k)).toRingHom.comp
      ((algebraMap (k₀ ⊗[K] R₁) (Localization.Away e)).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := k₀)).toRingHom),
    s.toRingHom, s₀, σ₁.toRingHom.codRestrict k hm₂, (geomInt_baseChange_and_away k₀ k _ hgi).1, ?_, ?_⟩
  · ext x
    refine (hs (1 ⊗ₜ x)).trans ?_
    simp [G]
  · refine RingHom.ext fun x => ?_
    refine (hs₀ (1 ⊗ₜ algebraMap R R₁ x)).trans (Subtype.ext ?_)
    rw [hG₀]
    exact Eq.trans (by simp [emb, q']) (hq' x)

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geom_integral_of_etale_faithfully_flat_cover : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  first | exact @GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale | exact GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale | (intros; apply GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.PolFamPf
open GlobalTheory.ZM.SiegPull GlobalTheory.CoordToExt

theorem exists_polPB (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), PolPB P' P f φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem polPB_cancel {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {P' : Out.PolAV S'} {P'' : Out.PolAV S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : P'.A.left ⟶ P.A.left} {χ : P''.A.left ⟶ P.A.left}
    (h : PolPB P' P f φ) (n : PolPB P'' P (g ≫ f) χ) : ∃ ψ, PolPB P'' P' g ψ := by
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ g) ≫ f := n.1.1.w.trans (Category.assoc _ _ _).symm
  have e : h.1.1.lift χ _ w ≫ φ = χ := h.1.1.lift_fst _ _ _
  refine ⟨h.1.1.lift χ _ w, h.1.cancel (n.1.congr rfl e.symm) (h.1.1.lift_snd _ _ _), n.2.1.trans h.2.1.symm, ?_⟩
  have k := GlobalTheory.ZM.SiegPull.lbIso_pull_comp h.2.2 (h.1.1.lift χ _ w)
  rw [e] at k
  exact LBIso.trans P''.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull P'.isLB _) n.2.2 k.symm

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a : Sp k ⟶ X)
    (u : Y ⟶ X) (φ : Fin 2 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) :
    LBIso (LB.LinComb L φ ![1, -1]) (L.pull u) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := PUnit) (fun _ => a) (fun _ => 1)
  refine ((refines_self _ _).div (refines_self φ _)).exists_gen hL (fun U _ f => ?_) _
    (DVR.pullGen_isGen _ _ _ e he p)
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fintype.prod_unique, h₀, h₁]
  simp

theorem exists_translate (hL : Out.Laws) {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) {R : Type} [CommRing R] (f : Sp R ⟶ S) (Q : Out.PolAV (Sp R)) (φ : Q.A.left ⟶ c.A.left)
    (hQ : SqOf Q c f φ) (hT : TorsConst Q.A 2) (x : Sp ℂ ⟶ Sp R) (P : Out.PolAV (Sp ℂ)) (χ : P.A.left ⟶ c.A.left)
    (hP : SqOf P c (x ≫ f) χ) :
    ∃ (Q' : Out.PolAV (Sp R)) (φ' : Q'.A.left ⟶ c.A.left) (ψ : P.A.left ⟶ Q'.A.left),
      SqOf Q' c f φ' ∧ PolPB P Q' x ψ := by
  obtain ⟨P₁, π, hπ⟩ := exists_polPB hL.polBaseChange x Q
  have h₁ := (sqOf_calculus h k o ζ S (Sp R) (Sp ℂ) s c f).1 x Q P₁ φ π hQ hπ
  obtain ⟨e, he, -, hl⟩ := (sqOf_calculus h k o ζ S (Sp ℂ) (Sp ℂ) s c (x ≫ f)).2.1 P₁ P _ _ h₁ hP
  obtain ⟨t₁, ht₁, hi⟩ := GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle hL ℂ P₁ P e he hl
  obtain ⟨t, ht, hy⟩ := hT ℂ _ (pushHom hπ.1 _ t₁) (by rw [← map_pow, ht₁, map_one])
  obtain ⟨Q', e', he', hg', hl', hi'⟩ := GlobalTheory.T.exists_rigidTranslate_principalPolarisation_order_two hL R Q t ht
  have hy' : t₁.left ≫ π = x ≫ t.left := by
    refine (congrArg (fun q => q.left) hy).trans ?_
    refine congrArg (· ≫ t.left) ?_
    exact (Category.comp_id _).symm.trans ((Over.w (toUnit (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x)))).trans
      (Category.id_comp _))
  have : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have gp₀ : IsGrpPullback P.A Q.A x (e.hom.left ≫ π) :=
    ((isGrpPullback_of_iso e).comp hπ.1).congr (Category.id_comp _) rfl
  have gp : IsGrpPullback P.A Q'.A x ((e.hom.left ≫ π) ≫ e'.inv.left) :=
    (gp₀.comp (isGrpPullback_of_iso e'.symm)).congr (Category.comp_id _) rfl
  have ee : ((e.hom.left ≫ π) ≫ e'.inv.left) ≫ e'.hom.left = e.hom.left ≫ π := by
    rw [Category.assoc, ← Over.comp_left, e'.inv_hom_id, Over.id_left, Category.comp_id]
  refine ⟨Q', _, (e.hom.left ≫ π) ≫ e'.inv.left,
    (sqOf_calculus h k o ζ S (Sp R) (Sp R) s c f).2.2 Q Q' φ e' he' hg' hl' hQ, gp,
    hP.2.1.trans (hg'.trans hQ.2.1).symm, ?_⟩
  have k₁ := LBIso.trans P.isLB (LB.isLB_pull P₁.isLB _) (LB.isLB_pull Q.isLB _) hi
    (GlobalTheory.ZM.SiegPull.lbIso_pull_comp hπ.2.2 (e.hom ≫ ((toUnit P₁.A ≫ t₁) * 𝟙 P₁.A)).left)
  have k₂ := LBIso.chartPull (Geo.Tor.chartPullPull Q'.L _ ((e.hom.left ≫ π) ≫ e'.inv.left) rfl)
    (chartPullSame Q.L _ _ _ ((e.hom.left ≫ π) ≫ e'.inv.left) fun _ => rfl) hi'
  have k₃ := lbIso_drop Q.isLB P.A.hom (x ≫ t.left) ((e.hom ≫ ((toUnit P₁.A ≫ t₁) * 𝟙 P₁.A)).left ≫ π)
    (fun i => ((e.hom.left ≫ π) ≫ e'.inv.left) ≫
      (![(e'.hom ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A)).left, (toUnit Q'.A ≫ t).left] : Fin 2 → _) i) ?_ ?_
  · exact LBIso.trans P.isLB (LB.isLB_pull Q.isLB _) (LB.isLB_pull Q'.isLB _) k₁
      (LBIso.trans (LB.isLB_pull Q'.isLB _) (DVR.linComb_isLB _ Q.isLB _ _) (LB.isLB_pull Q.isLB _) k₂ k₃).symm
  · show _ ≫ (e'.hom.left ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A).left) = (e.hom.left ≫ _) ≫ π
    rw [← Category.assoc, ee, Category.assoc, Category.assoc]
    refine congrArg (e.hom.left ≫ ·) ?_
    let ρ : Over.mk (P₁.A.hom ≫ x) ⟶ Q.A := Over.homMk π hπ.1.1.w
    refine Eq.trans ?_ (hπ.1.2 P₁.A (toUnit P₁.A ≫ t₁) (𝟙 _) (ρ ≫ toUnit _ ≫ t) (ρ ≫ 𝟙 _) ?_
      ((Category.comp_id _).trans (Category.id_comp _).symm))
    · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (toUnit _ ≫ t) (𝟙 _))
    · show π ≫ Q.A.hom ≫ t.left = (P₁.A.hom ≫ t₁.left) ≫ π
      rw [Category.assoc, hy', ← Category.assoc, hπ.1.1.w, Category.assoc]
  · show _ ≫ Q'.A.hom ≫ t.left = P.A.hom ≫ x ≫ t.left
    rw [← Category.assoc, gp.1.w, Category.assoc]

theorem exists_lift_point {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁]
    [Module.FaithfullyFlat R R₁] (p : R →+* ℂ) : ∃ p₁ : R₁ →+* ℂ, p₁.comp (algebraMap R R₁) = p := by
  letI := p.toAlgebra
  haveI : Nontrivial (ℂ ⊗[R] R₁) := Module.FaithfullyFlat.rTensor_nontrivial R R₁ ℂ
  obtain ⟨a⟩ := exists_algHom_of_finiteType_of_isAlgClosed ℂ (ℂ ⊗[R] R₁) ℂ
  refine ⟨a.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun r => ?_⟩
  show a (Algebra.TensorProduct.includeRight (algebraMap R R₁ r)) = p r
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R ℂ (ℂ ⊗[R] R₁), AlgHom.commutes]
  rfl

theorem exists_affine {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Sp K) (hs : IsQProjOver s)
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (p : Sp K₁ ⟶ X) (q : Sp K₂ ⟶ X) :
    ∃ (R : Type) (_ : CommRing R) (i : Sp R ⟶ X) (a : K →+* R) (p' : R →+* K₁) (q' : R →+* K₂),
      IsOpenImmersion i ∧ i ≫ s = spMap a ∧ spMap p' ≫ i = p ∧ spMap q' ≫ i = q := by
  obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver K X s hs (Set.range p ∪ Set.range q) ⊤
    ((Set.finite_range _).union (Set.finite_range _)) (fun _ _ => trivial)
  have hr : Set.range hV.fromSpec = V := hV.range_fromSpec
  refine ⟨Γ(X, V), inferInstance, hV.fromSpec, (Spec.preimage (hV.fromSpec ≫ s)).hom,
    (Spec.preimage (IsOpenImmersion.lift hV.fromSpec p (hr ▸ Set.subset_union_left.trans hF))).hom,
    (Spec.preimage (IsOpenImmersion.lift hV.fromSpec q (hr ▸ Set.subset_union_right.trans hF))).hom,
    inferInstance, (Spec.map_preimage _).symm, ?_, ?_⟩
  · exact (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)
  · exact (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.KeyFam.PolFamPf


open GlobalTheory.KeyFam.PolFamPf in
theorem GlobalTheory.KeyFam.polFam : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → PolFam := by
  intro hL hL2 hU hA P hg
  obtain ⟨k, K, _, _, ζ, σ, hk, ho, hζ, ⟨F⟩⟩ := GlobalTheory.T.exists_siegelFamily_over_numberField hL hL2 hU P.g hg
  obtain ⟨τ, lev, hper⟩ := exists_perLev hU P P.g k rfl
  obtain ⟨p, χ, hp, hP, hlev⟩ := exists_point_of_perLev hL P.g k K ζ σ F hg hk ho hζ P τ lev hper
  obtain ⟨K₁, _, _, j₁, σ₁, y, q, χy, τ', hσ, hq, hy, hyq, hpt⟩ :=
    GlobalTheory.T.exists_numberField_point_siegelFamily_knownValue hL hU P.g k K ζ σ F hg hk ho hζ inferInstance
  have hq' : (spMap σ₁ ≫ q) ≫ F.s = spMap σ := by rw [Category.assoc, hq, ← spMap_comp, hσ]
  have hc := GlobalTheory.T.siegelFamily_standard_level_points_same_component hL hL2 hU hA P.g k K ζ σ F hg hk ho hζ τ τ' p _ hp hq' ⟨P, lev, χ, hper, hP, hlev⟩ hpt
  obtain ⟨R, _, i, a, p', q', hi, ha, rfl, rfl⟩ := exists_affine F.s F.qproj p q
  letI := σ.toAlgebra
  letI := j₁.toAlgebra
  letI := a.toAlgebra
  have hp' : p'.comp a = σ := spMap_inj (by rw [spMap_comp, ← ha, ← hp, Category.assoc])
  have hq'' : q'.comp a = j₁ := spMap_inj (by rw [spMap_comp, ← ha, ← hq, Category.assoc])
  let pA : R →ₐ[K] ℂ := { p' with commutes' := fun r => DFunLike.congr_fun hp' r }
  let qA : R →ₐ[K] K₁ := { q' with commutes' := fun r => DFunLike.congr_fun hq'' r }
  let σA : K₁ →ₐ[K] ℂ := { σ₁ with commutes' := fun r => DFunLike.congr_fun hσ r }
  have hsm : Smooth F.s := by
    have := F.smooth
    exact SmoothOfRelativeDimension.smooth (P.g * (P.g + 1) / 2) F.s
  have hid := GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent K F.X F.s R i pA (σA.comp qA) hsm hi ha (by
    have e : spMap (σA.comp qA).toRingHom ≫ i = spMap σ₁ ≫ spMap q' ≫ i := by
      rw [← Category.assoc, ← spMap_comp]; rfl
    rw [e]; exact hc)
  haveI : Algebra.Smooth K R := by
    have : Smooth (spMap a) := ha ▸ inferInstance
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  letI : Algebra ℚ R := (a.comp (algebraMap ℚ K)).toAlgebra
  have hu : IsUnit ζ := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at hζ
    exact Complex.exp_ne_zero _ hζ.symm
  obtain ⟨R₁, _, _, Q, φ, ⟨c₁, c₂, c₃⟩, hQ, hT⟩ := GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale hL P.g k K ζ R F.X F.s F.univ i (by omega) hu F.princ
  obtain ⟨p₁, hp₁⟩ := exists_lift_point (R₁ := R₁) p'
  obtain ⟨Q', φ', ψ, hQ', hψ⟩ := exists_translate hL F.univ _ Q φ hQ hT (spMap p₁) P χ (by
    rw [← Category.assoc, ← spMap_comp, hp₁]; exact hP)
  letI : Algebra K R₁ := ((algebraMap R R₁).comp a).toAlgebra
  haveI : IsScalarTower K R R₁ := IsScalarTower.of_algebraMap_eq' rfl
  let p₁A : R₁ →ₐ[K] ℂ :=
    { p₁ with commutes' := fun r => (DFunLike.congr_fun hp₁ (a r)).trans (DFunLike.congr_fun hp' r) }
  have hpp : p₁A.comp (IsScalarTower.toAlgHom K R R₁) = pA := AlgHom.ext fun r => DFunLike.congr_fun hp₁ r
  obtain ⟨k', _, _, S, _, _, j, s, s₀, ii, hS, hs, hs₀⟩ :=
    GlobalTheory.T.geom_integral_of_etale_faithfully_flat_cover K R R₁ K₁ σA p₁A qA ⟨c₁, c₂, c₃⟩ (by rw [hpp]; exact hid)
  obtain ⟨Q'', π, hπ⟩ := exists_polPB hL.polBaseChange (spMap j) Q'
  obtain ⟨ψ', hψ'⟩ := polPB_cancel (g := spMap s) hπ (by
    rw [← spMap_comp, hs]; exact hψ)
  refine ⟨k', inferInstance, inferInstance, S, inferInstance, inferInstance, Q'', s, s₀, ψ', hS, hψ',
    fun P₀ φ₀ h₀ => ?_⟩
  have a₁ := (sqOf_calculus _ k K ζ F.X _ _ F.s F.univ _).1 _ _ _ _ _
    ((sqOf_calculus _ k K ζ F.X _ _ F.s F.univ _).1 _ _ _ _ _ hQ' hπ) h₀
  obtain ⟨y', hy'⟩ := keyIn_baseChange hL.polBaseChange K₁ k' y ii
  have hk' : Known k' y' := by
    obtain ⟨t₀, ht₀⟩ := hy
    exact ⟨ii t₀, fun e x hx => ht₀ (e.comp ii) x (keyPB_trans _ _ _ y y' x ii e hy' hx)⟩
  obtain ⟨β, -, w, hβg, -, hβ, hw, -⟩ := hy'
  have a₂ := (sqOf_calculus _ k K ζ F.X _ _ F.s F.univ _).1 _ _ _ _ _ hyq (⟨hβ, hβg, w, hw⟩ : PolPB y'.P y.P _ β)
  have e : spMap s₀.toRingHom ≫ spMap j ≫ spMap (algebraMap R R₁) ≫ i = spMap ii ≫ spMap q' ≫ i := by
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, hs₀,
      spMap_comp, Category.assoc]
  rw [e] at a₁
  obtain ⟨ε, hε, -, hl⟩ := (sqOf_calculus _ k K ζ F.X _ (Sp k') F.s F.univ _).2.1 _ _ _ _ a₂ a₁
  exact GlobalTheory.T.potentiallyKnown_of_same_lambdaBundle hL hU k' y' P₀ ε hε hl hk'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_family_of_theta_uniformization : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → PolFam := by
  first | exact @GlobalTheory.KeyFam.polFam | exact GlobalTheory.KeyFam.polFam | (intros; apply GlobalTheory.KeyFam.polFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDatumConnectedFamilyOfPolarizedArithmeticFami
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFrames
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KeyFam

theorem GeomInt.mvPolynomial {k S : Type} [Field k] [CommRing S] [Algebra k S] (σ : Type) [Finite σ]
    (h : GeomInt k S) : GeomInt k (MvPolynomial σ S) := by
  have h₀ := h.1
  have h₁ : Algebra.Smooth S (MvPolynomial σ S) := ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.Smooth.comp k S _, fun K _ _ => ?_⟩
  have := h.2 K
  let e₁ : K ⊗[k] MvPolynomial σ S ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ((MvPolynomial.algebraTensorAlgEquiv k S).symm.restrictScalars k)
  let e₂ : (K ⊗[k] S) ⊗[k] MvPolynomial σ k ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.assoc k k k K S (MvPolynomial σ k)
  let e₃ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k (K ⊗[k] S)
  exact ((e₁.trans e₂.symm).toMulEquiv.trans e₃.toMulEquiv).isDomain _

theorem exists_univ_scalars {k S : Type} [Field k] [CommRing S] [Algebra k S] (h : GeomInt k S) (s : S →+* ℂ)
    (s₀ : S →ₐ[k] k) (n : ℕ) (a : ℂˣ) (N : Matrix (Fin n) (Fin n) ℂ) (hN : IsUnit N.det) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k)
      (b : S'ˣ) (M : Matrix (Fin n) (Fin n) S'), GeomInt k S' ∧ s'.comp j.toRingHom = s ∧ s₀'.comp j = s₀ ∧
      IsUnit M.det ∧ s' b = a ∧ ∀ i l, s' (M i l) = N i l := by
  let T := MvPolynomial (Option (Fin n × Fin n)) S
  let M₀ : Matrix (Fin n) (Fin n) T := fun i l => MvPolynomial.X (some (i, l))
  let r : T := MvPolynomial.X none * M₀.det
  have key : ∀ {L : Type} [CommRing L] (f : S →+* L) (c : L) (B : Matrix (Fin n) (Fin n) L),
      ∃ F : T →+* L, (∀ z, F (MvPolynomial.C z) = f z) ∧ F (MvPolynomial.X none) = c ∧
        (∀ i l, F (M₀ i l) = B i l) ∧ F r = c * B.det := by
    intro L _ f c B
    let F : T →+* L := MvPolynomial.eval₂Hom f (fun o => o.elim c fun p => B p.1 p.2)
    have h₁ : F (MvPolynomial.X none) = c := MvPolynomial.eval₂Hom_X' _ _ _
    have h₂ : ∀ i l, F (M₀ i l) = B i l := fun i l => MvPolynomial.eval₂Hom_X' _ _ _
    refine ⟨F, fun z => MvPolynomial.eval₂Hom_C _ _ _, h₁, h₂, ?_⟩
    rw [map_mul, h₁, RingHom.map_det]
    congr 2
    ext i l
    exact h₂ i l
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄⟩ := key s a N
  obtain ⟨G, hG₁, -, -, hG₄⟩ := key s₀.toRingHom 1 1
  have uF : IsUnit (F r) := hF₄ ▸ a.isUnit.mul hN
  have uG : IsUnit (G r) := by rw [hG₄]; simp
  have hr : r ≠ 0 := fun e => uG.ne_zero (by rw [e, map_zero])
  let S' := Localization.Away r
  have ur : IsUnit (algebraMap T S' r) := IsLocalization.Away.algebraMap_isUnit r
  rw [map_mul, IsUnit.mul_iff] at ur
  obtain ⟨⟨b, hb⟩, uM⟩ := ur
  let j : S →ₐ[k] S' := (IsScalarTower.toAlgHom k T S').comp (IsScalarTower.toAlgHom k S T)
  have hj : ∀ z, j z = algebraMap T S' (MvPolynomial.C z) := fun _ => rfl
  let g₀ : S' →+* k := IsLocalization.Away.lift r uG
  have hg : ∀ z, g₀ (j z) = s₀ z := fun z => by
    rw [hj, IsLocalization.Away.lift_eq, hG₁]; rfl
  refine ⟨S', inferInstance, inferInstance, j, IsLocalization.Away.lift r uF,
    { g₀ with commutes' := fun c => ?_ }, b, (algebraMap T S').mapMatrix M₀,
    (GlobalTheory.KeyFam.geomInt_baseChange_and_away k k T (h.mvPolynomial _)).2 r hr, RingHom.ext fun z => ?_, AlgHom.ext hg, ?_, ?_, fun i l => ?_⟩
  · change g₀ _ = _
    rw [← j.commutes, hg, s₀.commutes]
  · change IsLocalization.Away.lift r uF (j z) = _
    rw [hj, IsLocalization.Away.lift_eq, hF₁]
  · rwa [← RingHom.map_det]
  · rw [hb, IsLocalization.Away.lift_eq, hF₂]
  · change IsLocalization.Away.lift r uF (algebraMap T S' (M₀ i l)) = _
    rw [IsLocalization.Away.lift_eq, hF₃]

theorem exists_polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := h
  exact ⟨φ, hp, hg, w, hw⟩

theorem exists_univ_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  intro hL k S _ _ _ y x s φ s₀ hS hφ
  obtain ⟨Q, hg, rig', hr', th', hth', v', hv'⟩ := x
  dsimp only at φ hφ
  obtain ⟨rig, hr, th, hth, v, hv, H⟩ := KeyTf.exists_keyPB_on S ℂ s y Q φ hg hφ.2.1 hφ.1 hφ.2.2
  obtain ⟨a, t, ht, hat, Hid⟩ := (KeyOnPol.main hL ℂ).2 ⟨Q, hg, rig, hr, th, hth, v, hv⟩ rig' hr' th' hth' v' hv'
  choose N hN using fun i => (hv.2 _ (hv'.1 i)).exists
  have := Q.isAb.comm
  have uN : IsUnit (Matrix.det (N : Matrix _ _ ℂ)) :=
    ((LieComb.lieComb_algebra ℂ Q.A Q.g v hv.1).2.2.2.2 N v' hv hN).1 hv'
  obtain ⟨S', _, _, j, s', s₀', b, M, hS', hs, hs₀, uM, hb, hM⟩ := exists_univ_scalars hS s s₀ Q.g a N uN
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y j.toRingHom
  have H₂ := KeyCancel.keyPB_cancel _ _ _ y y₁ _ _ s' H₁ (hs ▸ H)
  obtain ⟨ψ, hψ⟩ := exists_polPB_of_keyPB H₁
  have e : Q.g = y₁.P.g := KeyGalDesc.g_eq H₂
  have := y₁.P.isAb.comm
  let M' : Matrix (Fin y₁.P.g) (Fin y₁.P.g) S' := Matrix.reindex (finCongr e) (finCongr e) M
  have uM' : IsUnit M'.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := LieComb.lieComb_algebra S' y₁.P.A y₁.P.g y₁.v y₁.basis.1
  choose v₁ hv₁ using fun i => (ex (M' i)).exists
  obtain ⟨t₁, ht₁, -, hle⟩ := exists_sec_div y₁.P.A.hom b.inv_mul y₁.th
  refine ⟨S', _, _, j, ⟨y₁.P, y₁.g_pos, y₁.rig, y₁.rig_gen, t₁,
    fun p => (y₁.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁, (bas M' v₁ y₁.basis hv₁).2 uM'⟩, s', s₀', ψ, hS', ?_, hψ, hs₀⟩
  rw [← RingHom.id_comp s']
  refine keyPB_trans _ _ _ _ _ _ _ _ ?_ Hid
  refine KeyPBScale.keyPB_scale S' ℂ s' y₁.P y₁.g_pos y₁.rig y₁.rig_gen y₁.th y₁.th_ne y₁.v y₁.basis t₁ _ v₁ _ b M' Q e
    hg rig hr th hth v hv t ht v' hv' ht₁ hv₁ (hb ▸ hat) (fun i => ?_) H₂
  convert hN i using 2 with l
  exact hM i l

end GlobalTheory.KeyFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaKeyFamily_universal_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  first | exact @GlobalTheory.KeyFam.exists_univ_frames | exact GlobalTheory.KeyFam.exists_univ_frames | (intros; apply GlobalTheory.KeyFam.exists_univ_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDatumConnectedFamilyOfPolarizedArithmeticFami
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.Frames

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp (f : R →+* R') (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem polPB_comp {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h' : ∃ φ', PolPB P'' P' (spMap f') φ')
    (h : ∃ φ, PolPB P' P (spMap f) φ) : ∃ ψ, PolPB P'' P (spMap g) ψ := by
  obtain ⟨φ', hc', hg', w', hw'⟩ := h'
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  obtain ⟨w'', T⟩ := exists_comp P'.isLB w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') P.isLB P''.isLB
  exact ⟨φ' ≫ φ, (hc'.comp hc).congr (spMap_comp f f').symm rfl, hg'.trans hg, w'',
    (isGen_iff w'').2 (T.pgen_comp P'.isLB ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem polPB_cancel {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h : ∃ φ, PolPB P' P (spMap f) φ)
    (h'' : ∃ ψ, PolPB P'' P (spMap g) ψ) : ∃ φ', PolPB P'' P' (spMap f') φ' := by
  obtain ⟨φ'', hc'', hg'', w'', hw''⟩ := h''
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  have hsp := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : P''.A.left ⟶ P'.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ P'.A.hom = P''.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (P''.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' g g'' P'.isLB P''.isLB
  exact ⟨φ', hc.cancel (hc''.congr hsp rfl) hw0, hg''.trans hg.symm, w',
    (isGen_iff w').2 (T.pgen_cancel P.isLB g g'')⟩

theorem polPB_exists (hB : Out.PolBaseChangeSt) (P : Out.PolAV (Sp R)) (f : R →+* R') :
    ∃ (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), PolPB P' P (spMap f) φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB _ _ (spMap f) P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem polPB_of_keyPB {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} (h : KeyPB x' x f) :
    ∃ φ, PolPB x'.P x.P (spMap f) φ :=
  let ⟨φ, _, w, hg, _, hc, hw, _⟩ := h
  ⟨φ, hc, hg, w, hw⟩

theorem exists_points (K K' R : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [CommRing R] [Algebra K R] (s : R →+* ℂ) (s₀ : R →ₐ[K] K) :
    ∃ (i : R →+* K' ⊗[K] R) (s' : K' ⊗[K] R →+* ℂ) (s₀' : K' ⊗[K] R →ₐ[K'] K'),
      s'.comp i = s ∧ s₀'.toRingHom.comp i = (algebraMap K K').comp s₀.toRingHom := by
  letI : Algebra K ℂ := (s.comp (algebraMap K R)).toAlgebra
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let e : K' →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let sA : R →ₐ[K] ℂ := { s with commutes' := fun _ => rfl }
  refine ⟨Algebra.TensorProduct.includeRight.toRingHom,
    (Algebra.TensorProduct.lift e sA fun _ _ => Commute.all _ _).toRingHom,
    Algebra.TensorProduct.lift (AlgHom.id K' K') ((Algebra.ofId K K').comp s₀) fun _ _ => Commute.all _ _,
    RingHom.ext fun r => ?_, RingHom.ext fun r => ?_⟩
  · simp [sA]
  · simp

end GlobalTheory.KeyFam.Frames

namespace GlobalTheory.KeyFam
open Frames

theorem connFam_of_polFam : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  intro hL hL2 hF x
  obtain ⟨K, _, _, R, _, _, Q, s, s₀, φ, hG, hP, hK⟩ := hF x.P x.g_pos
  obtain ⟨P₀, φ₀, hP₀⟩ := polPB_exists hL.polBaseChange Q s₀.toRingHom
  obtain ⟨K', _, _, j, hKn⟩ := hK P₀ φ₀ hP₀
  letI : Algebra K K' := j.toAlgebra
  obtain ⟨i, s', s₀', hs', hs₀'⟩ := exists_points K K' R s s₀
  obtain ⟨Q', ψ, hQ'⟩ := polPB_exists hL.polBaseChange Q i
  have hG' : GeomInt K' (K' ⊗[K] R) := (GlobalTheory.T.geom_integral_base_change_and_localization K K' R hG).1
  haveI := hG'.1
  haveI : IsNoetherianRing (K' ⊗[K] R) := Algebra.FiniteType.isNoetherianRing K' _
  obtain ⟨r, hr, hr₀, y, χ, hy⟩ := GlobalTheory.T.exists_keyData_near_two_primes hL hL2 (K' ⊗[K] R) Q' ⟨RingHom.ker s', RingHom.ker_isPrime _⟩
    ⟨RingHom.ker s₀'.toRingHom, RingHom.ker_isPrime _⟩ (by rw [hQ'.2.1, ← hP.2.1]; exact x.g_pos)
  have hu : IsUnit (s' r) := isUnit_iff_ne_zero.2 hr
  have hu₀ : IsUnit (s₀'.toRingHom r) := isUnit_iff_ne_zero.2 hr₀
  have hS : GeomInt K' (Localization.Away r) :=
    (GlobalTheory.T.geom_integral_base_change_and_localization K' K' _ hG').2 r fun h => hr (h ▸ Ideal.zero_mem _)
  let t : Localization.Away r →+* ℂ := IsLocalization.Away.lift r hu
  have ht : t.comp (algebraMap _ _) = s' := IsLocalization.Away.lift_comp r hu
  let u : Localization.Away r →+* K' := IsLocalization.Away.lift r hu₀
  have hu' : u.comp (algebraMap _ _) = s₀'.toRingHom := IsLocalization.Away.lift_comp r hu₀
  let t₀ : Localization.Away r →ₐ[K'] K' :=
    { u with
      commutes' := fun a => by
        rw [IsScalarTower.algebraMap_apply K' (K' ⊗[K] R) (Localization.Away r)]
        exact (RingHom.congr_fun hu' _).trans (s₀'.commutes a) }
  have hyQ := polPB_comp rfl ⟨χ, hy⟩ ⟨ψ, hQ'⟩
  obtain ⟨φ₁, hφ₁⟩ := polPB_cancel (f' := t) (by rw [← RingHom.comp_assoc, ht, hs']) hyQ ⟨φ, hP⟩
  obtain ⟨S', _, _, j', y', v, v₀, ψ', hS', hx, hy', hv₀⟩ := GlobalTheory.T.exists_thetaKeyFamily_universal_frames hL K' _ y x t φ₁ t₀ hS hφ₁
  obtain ⟨y₀, hy₀⟩ := exists_keyPB_ring y' v₀.toRingHom
  have e₁ : v₀.toRingHom.comp j'.toRingHom = u := congrArg AlgHom.toRingHom hv₀
  have h₁ := polPB_comp e₁ (polPB_of_keyPB hy₀) ⟨ψ', hy'⟩
  have h₂ := polPB_comp (g := ((RingHom.id K').comp j).comp s₀.toRingHom)
    (by rw [← RingHom.comp_assoc, hu', hs₀']; rfl) h₁ hyQ
  obtain ⟨φ₂, hφ₂⟩ := polPB_cancel rfl ⟨φ₀, hP₀⟩ h₂
  obtain ⟨c, hc⟩ := hKn K' (RingHom.id K') y₀ φ₂ hφ₂
  exact ⟨K', _, ‹_›, S', _, _, y', v, v₀, c, hS'.1, hS'.2, hx, fun e x₀ h =>
    hc e x₀ (KeyCancel.keyPB_cancel _ _ _ y' y₀ x₀ _ _ hy₀ h)⟩

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDatumConnectedFamilyOfPolarizedArithmeticFamiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatumConnectedFamily_of_polarizedArithmeticFamily : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  first | exact @GlobalTheory.KeyFam.connFam_of_polFam | exact GlobalTheory.KeyFam.connFam_of_polFam | (intros; apply GlobalTheory.KeyFam.connFam_of_polFam <;> assumption)
end
end

namespace GlobalTheory.KeyFam

theorem connFam_holds : GlobalTheory.KeyKa.ConnFam :=
  GlobalTheory.T.keyDatumConnectedFamily_of_polarizedArithmeticFamily GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (GlobalTheory.T.polarized_family_of_theta_uniformization GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.thetaUnifAV_closed
      GlobalTheory.torusAlgebraic_holds)

end GlobalTheory.KeyFam
