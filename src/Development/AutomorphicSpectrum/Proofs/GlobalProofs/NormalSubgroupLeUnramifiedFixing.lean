module

public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
public import GroundTheory.AutomorphicForms.TraceFormulaConvolution

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]


omit [NumberField F] [Algebra F Ω] [Field F] in
theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h1 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hz]
  exact z.2

noncomputable def intToVal (A : ValuationSubring Ω) (M : IntermediateField F Ω) : 𝓞 M →+* A :=
  ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun z =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ M Ω))

noncomputable def cutPrime (A : ValuationSubring Ω) (M : IntermediateField F Ω) : Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal A).comap (intToVal A M)

instance (A : ValuationSubring Ω) (M : IntermediateField F Ω) : (cutPrime A M).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_cutPrime_iff (A : ValuationSubring Ω) (M : IntermediateField F Ω) (z : 𝓞 M) :
    z ∈ cutPrime A M ↔ A.valuation ((z : M) : Ω) < 1 := by
  rw [cutPrime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem cutPrime_liesOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (M : IntermediateField F Ω) : (cutPrime A M).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, mem_cutPrime_iff, ← hA x]
  rfl

theorem inertia_apply_eq [IsGalois F Ω] {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Inertia (F := F) A) {x : Ω} (hx : x ∈ maxUnramifiedOutside F Ω S) :
    σ x = x := by
  classical
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  set E : IntermediateField F Ω := IntermediateField.normalClosure F (IntermediateField.adjoin F ({x} : Set Ω)) Ω with hE
  haveI : FiniteDimensional F E := normalClosure.is_finiteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Normal F E := normalClosure.normal F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω E.val
  haveI : IsGalois F E := ⟨⟩
  have hxE : x ∈ E := IntermediateField.le_normalClosure (IntermediateField.adjoin F ({x} : Set Ω)) (IntermediateField.mem_adjoin_simple_self F x)
  have hEM : E ≤ maxUnramifiedOutside F Ω S := by
    rw [hE, IntermediateField.normalClosure_le_iff_of_normal]
    exact IntermediateField.adjoin_simple_le_iff.2 hx
  have hEun : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEM
  haveI hPl : (cutPrime A E).LiesOver v.asIdeal := cutPrime_liesOver hA E
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI : Algebra.FiniteType (𝓞 F) (𝓞 E) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 F) (𝓞 E)
  haveI : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing (G := Gal(E/F)) (A := 𝓞 F) (B := 𝓞 E) (K := F) (L := E)
  have he : (cutPrime A E).ramificationIdx (𝓞 F) = 1 :=
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hEun v hv) hPl
  have hcard : Nat.card ((cutPrime A E).inertia Gal(E/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal (cutPrime A E),
      Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(E/F)) v.asIdeal (cutPrime A E), he]
  set σ' : Gal(E/F) := σ.restrictNormal E with hσ'
  have hmem : σ' ∈ (cutPrime A E).inertia Gal(E/F) := by
    intro z
    show σ' • z - z ∈ cutPrime A E
    rw [mem_cutPrime_iff]
    obtain ⟨-, hσ2⟩ := hσ
    have hy : ((z : E) : Ω) ∈ A :=
      mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ E Ω))
    have hc : (((σ' • z - z : 𝓞 E) : E) : Ω) = σ ((z : E) : Ω) - ((z : E) : Ω) := by
      have h1 := AlgEquiv.restrictNormal_commutes σ E (z : E)
      simp only [IntermediateField.algebraMap_apply] at h1
      rw [← h1, hσ']
      rfl
    rw [hc]
    exact hσ2 _ (A.valuation_le_one ⟨_, hy⟩)
  have hσ'1 : σ' = 1 := by
    haveI hsub : Subsingleton ((cutPrime A E).inertia Gal(E/F)) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have := Subsingleton.elim (⟨σ', hmem⟩ : (cutPrime A E).inertia Gal(E/F)) ⟨1, Subgroup.one_mem _⟩
    exact congrArg Subtype.val this
  have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨x, hxE⟩
  rw [← hσ', hσ'1] at h1
  exact h1.symm

theorem NS_le_fixingSubgroup : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by
  intro F Ω _ _ _ _ _ S
  haveI : IsGalois F Ω := ⟨⟩
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : (maxUnramifiedOutside F Ω S).fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois _).2 hM
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A) ⊆
      ((maxUnramifiedOutside F Ω S).fixingSubgroup : Set (G F Ω)) := by
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    show σ ∈ (maxUnramifiedOutside F Ω S).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact inertia_apply_eq hv hA hσA hx
  show (Subgroup.normalClosure _).topologicalClosure ≤ _
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub)
    (InfiniteGalois.fixingSubgroup_isClosed _)

end GlobalTheory.CompanionTheory.GlobalFiniteness
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_subgroup_le_unramified_fixing : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside (F := F) (Ω := Ω) S).fixingSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | exact GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open scoped Pointwise IntermediateField

namespace GlobalTheory.CompanionTheory.Glob.InertiaLift

section

variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]


omit [NumberField F] [NumberField K] in
theorem restrictScalars_smul (h : Ω ≃ₐ[K] Ω) (A : ValuationSubring Ω) :
    (h.restrictScalars F) • A = h • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl


omit [NumberField K] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] in
theorem mem_inertia_of_integers [IsAlgClosure F Ω] {A : ValuationSubring Ω} {σ : Ω ≃ₐ[F] Ω}
    (hd : σ • A = A) (hb : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) :
    σ ∈ Inertia (F := F) A := by
  refine ⟨hd, fun x hx => ?_⟩
  have hD : σ ∈ Dec (F := F) A := hd
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    refine not_lt.mp fun h => ?_
    have := (valuation_apply_lt_one_iff hD s).1 h
    rw [hs1] at this
    exact lt_irrefl _ this
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s * σ s * (σ x - x) = s * (σ t - t) + t * (s - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s * σ s * (σ x - x)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, hs1, one_mul]
      exact hb t ht
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation t * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) :=
            mul_le_mul_left hvt _
        _ < 1 := by rw [one_mul]; exact hb s hs
  rwa [Valuation.map_mul, Valuation.map_mul, hs1, hσs, one_mul, one_mul] at hv

noncomputable def actInt (g : Ω ≃ₐ[F] Ω) : IntCl K Ω ≃+* IntCl K Ω where
  toFun b := ⟨g b, ((isIntegral_int_of_isIntegral (F := K) b.2).map
    (g.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨(g⁻¹ : Ω ≃ₐ[F] Ω) b, ((isIntegral_int_of_isIntegral (F := K) b.2).map
    ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (by
    show (g⁻¹ * g) (b : Ω) = b
    simp)
  right_inv b := Subtype.ext (mul_inv_apply (σ := g) (b : Ω))
  map_mul' a b := Subtype.ext (map_mul g (a : Ω) b)
  map_add' a b := Subtype.ext (map_add g (a : Ω) b)

theorem exists_residue_correction [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    (w : HeightOneSpectrum (𝓞 K))
    (hA : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal)
    {σ₁ : Ω ≃ₐ[F] Ω} (hd : σ₁ ∈ Dec (F := F) A)
    (hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1) :
    ∃ h : Ω ≃ₐ[K] Ω, h • A = A ∧ ∀ b : IntCl K Ω, A.valuation (h (b : Ω) - σ₁ b) < 1 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : IsGalois K Ω := {}
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set P := primeBelow (F := K) A with hPdef
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : P.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 K) P
    (by rw [show Ideal.under (𝓞 K) P = w.asIdeal from under_primeBelow hA]
        exact w.isMaximal)
  let e : IntCl K Ω ≃+* IntCl K Ω := actInt σ₁
  have hP : P = P.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (valuation_apply_lt_one_iff ((Dec (F := F) A).inv_mem hd) _).symm
  let φr : (IntCl K Ω ⧸ P) ≃+* (IntCl K Ω ⧸ P) := Ideal.quotientEquiv P P e hP
  let φ : (IntCl K Ω ⧸ P) ≃ₐ[𝓞 K ⧸ w.asIdeal] (IntCl K Ω ⧸ P) := AlgEquiv.ofRingEquiv (f := φr) (by
    intro r
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective r
    show φr (Ideal.Quotient.mk P (algebraMap (𝓞 K) (IntCl K Ω) z)) =
      Ideal.Quotient.mk P (algebraMap (𝓞 K) (IntCl K Ω) z)
    rw [Ideal.quotientEquiv_mk]
    refine Ideal.Quotient.eq.2 ?_
    exact hz z)
  obtain ⟨⟨h, hhP⟩, hh⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) w.asIdeal P φ
  have hhP' : h • P = P := hhP
  refine ⟨h, ?_, fun b => ?_⟩
  · refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (h • A) ↔ b' ∈ P
    rw [primeBelow_smul, hhP']
  · have h1 : Ideal.Quotient.mk P (h • b) = Ideal.Quotient.mk P (e b) :=
      DFunLike.congr_fun hh (Ideal.Quotient.mk P b)
    exact Ideal.Quotient.eq.1 h1

theorem exists_inertia_lift [IsAlgClosure F Ω] [IsAlgClosure K Ω] [Normal F K]
    (w : HeightOneSpectrum (𝓞 K)) {τ : K ≃ₐ[F] K} (hτ : τ ∈ w.asIdeal.inertia (K ≃ₐ[F] K)) :
    ∃ (A : ValuationSubring Ω) (σ : Ω ≃ₐ[F] Ω),
      (∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal) ∧
      σ ∈ Inertia (F := F) A ∧ ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : IsGalois K Ω := {}
  have : IsGalois F Ω := {}
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let σ₀ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have hσ₀ : ∀ x : K, σ₀ (algebraMap K Ω x) = algebraMap K Ω (τ x) := fun x =>
    AlgEquiv.liftNormal_commutes τ Ω x
  have hτ' : ∀ z : 𝓞 K, τ • z - z ∈ w.asIdeal := fun z => AddSubgroup.mem_inertia.1 hτ z
  have hτi : ∀ z : 𝓞 K, τ⁻¹ • z - z ∈ w.asIdeal := fun z =>
    AddSubgroup.mem_inertia.1 (Subgroup.inv_mem _ hτ) z
  have hσ₀i : ∀ x : K, (σ₀⁻¹ : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω ((τ⁻¹ : K ≃ₐ[F] K) x) := by
    intro x
    have h1 : algebraMap K Ω x = σ₀ (algebraMap K Ω ((τ⁻¹ : K ≃ₐ[F] K) x)) := by
      rw [hσ₀]
      congr 1
      show x = (τ * τ⁻¹) x
      simp
    rw [h1]
    show (σ₀⁻¹ * σ₀) _ = _
    simp
  have hA' : ∀ x : 𝓞 K, (σ₀ • A).valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    rw [smul_valuation_lt_one_iff, hσ₀i]
    have := hA (τ⁻¹ • x)
    refine (Iff.trans (by exact this) ?_)
    constructor
    · intro h
      have := w.asIdeal.sub_mem h (hτi x)
      simpa using this
    · intro h
      have := w.asIdeal.add_mem (hτi x) h
      simpa using this
  obtain ⟨h, hh⟩ := exists_smul_eq_of_over hA' hA
  let σ₁ : Ω ≃ₐ[F] Ω := h.restrictScalars F * σ₀
  have hσ₁ : ∀ x : K, σ₁ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
    intro x
    show (h.restrictScalars F) (σ₀ (algebraMap K Ω x)) = _
    rw [hσ₀]
    exact h.commutes _
  have hd : σ₁ ∈ Dec (F := F) A := by
    show σ₁ • A = A
    rw [mul_smul, restrictScalars_smul, hh]
  have hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1 := by
    intro z
    rw [hσ₁, ← map_sub]
    exact (hA (τ • z - z)).2 (hτ' z)
  obtain ⟨g, hgA, hg⟩ := exists_residue_correction (F := F) w hA hd hz
  let g' : Ω ≃ₐ[F] Ω := g.restrictScalars F
  have hgD : g' ∈ Dec (F := F) A := by
    show g' • A = A
    rw [restrictScalars_smul, hgA]
  refine ⟨A, g'⁻¹ * σ₁, hA, ?_, fun x => ?_⟩
  · refine mem_inertia_of_integers ((Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hgD) hd) ?_
    intro b hb
    have e : (g'⁻¹ * σ₁) b - b = (g'⁻¹ : Ω ≃ₐ[F] Ω) (σ₁ b - g' b) := by
      rw [map_sub]
      have : (g'⁻¹ : Ω ≃ₐ[F] Ω) (g' b) = b := by
        show (g'⁻¹ * g') b = b
        simp
      rw [this]
      rfl
    rw [e, valuation_apply_lt_one_iff ((Dec (F := F) A).inv_mem hgD), Valuation.map_sub_swap]
    exact hg ⟨b, hb.tower_top⟩
  · show (g'⁻¹ : Ω ≃ₐ[F] Ω) (σ₁ (algebraMap K Ω x)) = _
    rw [hσ₁]
    have : g' (algebraMap K Ω (τ x)) = algebraMap K Ω (τ x) := g.commutes _
    conv_lhs => rw [← this]
    show (g'⁻¹ * g') _ = _
    simp

end

theorem fixingSubgroup_le_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  intro F Ω _ _ _ _ _ S
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : IsGalois F Ω := {}
  have key : IntermediateField.fixedField (NS Ω S) ≤ maxUnramifiedOutside F Ω S := by
    intro x hx
    obtain ⟨M, hxM⟩ := exists_finiteGalois_mem (K := F) x
    have hE : F⟮x⟯ ≤ M.toIntermediateField := IntermediateField.adjoin_simple_le_iff.2 hxM
    have : FiniteDimensional F F⟮x⟯ := finiteDimensional_of_le hE
    have hEK : F⟮x⟯ ≤ IntermediateField.fixedField (NS Ω S) :=
      IntermediateField.adjoin_simple_le_iff.2 hx
    refine le_maxUnramifiedOutside S (E := F⟮x⟯) (fun v hv => ?_)
      (IntermediateField.mem_adjoin_simple_self F x)
    rw [isUnramifiedIn_iff_inertia hE v]
    intro Q hQ hQv τ hτ y hy
    have : NumberField M.toIntermediateField := NumberField.of_module_finite F _
    have : IsAlgClosure M.toIntermediateField Ω :=
      ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) _⟩
    let w : HeightOneSpectrum (𝓞 M.toIntermediateField) :=
      ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    obtain ⟨A, σ, hA, hσ, hres⟩ := exists_inertia_lift (Ω := Ω) w hτ
    have hAv : IsPlaceOver A v := by
      intro a
      have h1 := hA (algebraMap (𝓞 F) (𝓞 M.toIntermediateField) a)
      refine Iff.trans (by exact h1) ?_
      exact (Ideal.mem_of_liesOver Q v.asIdeal a).symm
    have hNS : σ ∈ NS Ω S := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hσ⟩
    have hfix : σ y = y :=
      (IntermediateField.mem_fixedField_iff (NS Ω S) y).1 (hEK hy) σ hNS
    apply Subtype.ext
    have := hres ⟨y, hE hy⟩
    exact (this.symm.trans hfix)
  have hc := InfiniteGalois.fixingSubgroup_fixedField (⟨NS Ω S, isClosed_NS Ω S⟩ : ClosedSubgroup (Ω ≃ₐ[F] Ω))
  have := IntermediateField.fixingSubgroup_antitone key
  rw [show (IntermediateField.fixedField (NS Ω S)).fixingSubgroup = NS Ω S from hc] at this
  exact this

end GlobalTheory.CompanionTheory.Glob.InertiaLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomologyStatement
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_unramified_outside_cohomology : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | exact GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | (intros; apply GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearUnimodularHaar
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.HaarGL

theorem exists_haar_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro F _ _ _ _ O ϖ nrm q hLF n
  obtain ⟨hKo, hKc, hlc, _hsc, ht2, -, -⟩ := GlobalTheory.T.generalLinear_integral_compact_open hLF n
  haveI := hlc
  haveI := ht2
  haveI : BorelSpace (GL (Fin n) F) := GlobalTheory.CompanionTheory.QL.instBorelGL n
  refine ⟨?_, fun μ hμ => ?_⟩
  · let μ₀ : Measure (GL (Fin n) F) := Measure.haar
    have hpos : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ 0 :=
      hKo.measure_ne_zero μ₀ ⟨1, (GLint O n).one_mem⟩
    have hfin : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ ⊤ := hKc.measure_lt_top.ne
    refine ⟨(μ₀ (GLint O n : Set (GL (Fin n) F)))⁻¹ • μ₀, inferInstance, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · haveI := hμ
    exact ⟨GroundTheory.Automorphic.Measures.isMulRightInvariant_GL F n μ,
      ⟨GroundTheory.Automorphic.Measures.inv_eq_self_GL F n μ⟩⟩

end GlobalTheory.CompanionTheory.QL.HaarGL
end
