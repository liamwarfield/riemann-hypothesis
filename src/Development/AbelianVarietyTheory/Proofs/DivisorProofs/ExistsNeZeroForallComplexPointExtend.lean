module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
open TensorProduct

namespace GlobalTheory

theorem exists_basicOpen_subset_of_isConstructible_of_bot_mem {B : Type*} [CommRing B] [IsDomain B]
    {s : Set (PrimeSpectrum B)} (hs : Topology.IsConstructible s)
    (h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ s) :
    ∃ q : B, q ≠ 0 ∧ ∀ p : PrimeSpectrum B, q ∉ p.asIdeal → p ∈ s := by
  revert h0
  induction s, hs using Topology.IsConstructible.induction_of_isTopologicalBasis
      _ (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)) with
  | isCompact_basis i => exact PrimeSpectrum.isCompact_basicOpen _
  | sdiff i t ht =>
    intro h0
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_exists, not_not] at h0

    refine ⟨i, fun hi => h0.1 (by simp [hi]), fun p hp => ?_⟩
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_exists, not_not]
    refine ⟨hp, fun j hj => ?_⟩
    have hj0 : j = 0 := by simpa using h0.2 j hj
    simp [hj0]
  | union s hs t ht Hs Ht =>
    rintro (h0 | h0)
    · obtain ⟨q, hq, hsub⟩ := Hs h0
      exact ⟨q, hq, fun p hp => Or.inl (hsub p hp)⟩
    · obtain ⟨q, hq, hsub⟩ := Ht h0
      exact ⟨q, hq, fun p hp => Or.inr (hsub p hp)⟩

theorem exists_ringHom_extend_of_ker_mem_range_comap {B A L : Type*} [CommRing B] [CommRing A]
    [Algebra B A] [Algebra.FiniteType B A] [Field L] [IsAlgClosed L] (φ : B →+* L)
    (h : (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    ∃ ψ : A →+* L, ψ.comp (algebraMap B A) = φ := by
  obtain ⟨P, hP⟩ := h
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPp : RingHom.ker φ = P.asIdeal.comap (algebraMap B A) := by
    have := congrArg PrimeSpectrum.asIdeal hP
    simpa using this.symm

  let σ : (RingHom.ker φ).ResidueField →+* L :=
    Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl (fun x hx => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact isUnit_iff_ne_zero.mpr fun h0 => hx (RingHom.mem_ker.mpr h0))

  let g : (RingHom.ker φ).ResidueField →ₐ[B] P.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ (RingHom.ker φ) P.asIdeal (Algebra.ofId B A) hPp
  let F : (RingHom.ker φ).ResidueField ⊗[B] A →ₐ[B] P.asIdeal.ResidueField :=
    Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B A _) (fun _ _ => Commute.all _ _)
  have : Nontrivial ((RingHom.ker φ).ResidueField ⊗[B] A) := F.toRingHom.domain_nontrivial
  obtain ⟨χ, hχ⟩ := exists_ringHom_extend_of_finiteType (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A) L σ
  refine ⟨χ.comp (Algebra.TensorProduct.includeRight (R := B)
    (A := (RingHom.ker φ).ResidueField) (B := A)).toRingHom, RingHom.ext fun b => ?_⟩
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply B (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A), hχ]
  exact Ideal.ResidueField.lift_algebraMap _ _ _ _ _

theorem exists_ne_zero_forall_complexPoint_extend :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A]
    [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  intro B A _ _ _ _ _ _ _ hinj
  have hfp : (algebraMap B A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)

  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨q, hq, hsub⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem
    (PrimeSpectrum.isConstructible_range_comap hfp) hgen
  exact ⟨q, hq, fun φ hφ =>
    exists_ringHom_extend_of_ker_mem_range_comap φ (hsub _ fun hk => hφ (RingHom.mem_ker.mp hk))⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ker_bC_eq_range_alC_and_ker_alC_eq_range_bC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (h : ℕ) (D : Datum ε h Γ), LinearMap.ker (bC C D) = LinearMap.range (alC C D) ∧ LinearMap.ker (alC C D) = LinearMap.range (bC C D) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ h D
  obtain ⟨hdom, -, hker, hsurj, hnu, hxi, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  have hFG : D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    (GlobalTheory.DetInv.datum_scalar_intertwine p C v O hv ε hε Γ h D).2.1
  have hGF : D.G * D.F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := D.G_mul_F
  set f : Ainf p O →+* C := (algebraMap O C).comp (WittVector.fontaineTheta O p) with hf
  have hinj := hv.hom_inj
  have hfnu : f (nu ε) ≠ 0 := by
    intro h0
    apply hnu
    apply hinj
    simpa [hf] using h0
  have hxiker : WittVector.fontaineTheta O p (xi ε) = 0 := by
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    exact this
  have hfmu : f (mu ε) = 0 := by
    rw [← xi_mul_nu, map_mul]
    simp [hf, hxiker]
  have hnzd : xi ε ∈ nonZeroDivisors (Ainf p O) := mem_nonZeroDivisors_of_ne_zero hxi
  have hfrac : ∀ c : C, ∃ s t : Ainf p O, f s ≠ 0 ∧ c * f s = f t := by
    intro c
    by_cases hc : v c ≤ 1
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one hc
      obtain ⟨t, rfl⟩ := hsurj a
      refine ⟨1, t, by simp, ?_⟩
      simp [hf, ha]
    · have hc0 : c ≠ 0 := by
        intro h0; apply hc; simp [h0]
      have hle : v c⁻¹ ≤ 1 := by
        rw [map_inv₀]
        push_neg at hc
        exact inv_le_one_of_one_le₀ hc.le
      obtain ⟨a, ha⟩ := hv.exists_of_le_one hle
      obtain ⟨s, rfl⟩ := hsurj a
      refine ⟨s, 1, ?_, ?_⟩
      · simp [hf, ha, hc0]
      · simp [hf, ha, hc0]
  have hdiv : ∃ s : Ainf p O, f s ≠ 0 ∧ ∀ r : Ainf p O, f r = 0 → xi ε ∣ s * r := by
    refine ⟨1, by simp, fun r hr => ?_⟩
    have h1 : WittVector.fontaineTheta O p r = 0 := by
      apply hinj; simpa [hf] using hr
    have h2 : r ∈ RingHom.ker (WittVector.fontaineTheta O p) := h1
    rw [hker, Ideal.mem_span_singleton] at h2
    simpa using h2
  have hmuxi : mu ε = xi ε * nu ε := (xi_mul_nu ε).symm

  have hcomp : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = mu ε • 1 →
      ∀ z : Fin h → C, X.map f *ᵥ (Y.map f *ᵥ z) = 0 := by
    intro X Y hXY z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hXY]
    have : (mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))).map f = 0 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply, hfmu]
    rw [this, Matrix.zero_mulVec]
  have hb : ∀ z, bC C D z = D.G.map f *ᵥ z := fun z => by
    simp [bC, redC, Matrix.toLin'_apply, hf]
  have ha : ∀ z, alC C D z = D.F.map f *ᵥ z := fun z => by
    simp [alC, redC, Matrix.toLin'_apply, hf]
  constructor
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, hb] at hx
      obtain ⟨y, hy⟩ := GlobalTheory.DetInv.ker_map_subset_im_map (Ainf p O) C f (xi ε) (nu ε) h D.G D.F
        hnzd hfnu hfrac hdiv (by rw [hFG, hmuxi]) x hx
      exact ⟨y, by rw [ha, hy]⟩
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, hb, ha]
      exact hcomp D.G D.F hGF y
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, ha] at hx
      obtain ⟨y, hy⟩ := GlobalTheory.DetInv.ker_map_subset_im_map (Ainf p O) C f (xi ε) (nu ε) h D.F D.G
        hnzd hfnu hfrac hdiv (by rw [hGF, hmuxi]) x hx
      exact ⟨y, by rw [hb, hy]⟩
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, hb, ha]
      exact hcomp D.F D.G hFG y

end GlobalTheory.DetInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R] →ₐ[R] TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R] :=
  { semiDiag (semiHom_mp F φ) with
    commutes' := fun r ↦ by
      change semiDiag (semiHom_mp F φ) (algebraMap R _ r) = algebraMap R _ r
      ext
      · rw [fst_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl', (semiHom_mp F φ).map_algebraMap]
      · rw [snd_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl'] }

theorem fst_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).fst = mp F φ c.fst := fst_semiDiag _ c

theorem snd_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).snd = p1 F φ c.snd := snd_semiDiag _ c

def omExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
  map φ := CommAlgCat.ofHom (extMap F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans (mp_id F T _)) ((snd_extMap F _ c).trans (oneFormsMapOfFunctorMorphism_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).fst
      rw [fst_extMap, fst_extMap])))
    ((snd_extMap F _ c).trans ((oneFormsMapOfFunctorMorphism_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).snd
      rw [snd_extMap, snd_extMap]))))

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem isLocalization_of_data {T T' : C} (l : T ⟶ T') (b : F.obj T) (h1 : IsUnit (mp F l b))
    (h2 : ∀ y : F.obj T', ∃ (n : ℕ) (x : F.obj T), y * mp F l b ^ n = mp F l x)
    (h3 : ∀ x : F.obj T, mp F l x = 0 → ∃ n : ℕ, b ^ n * x = 0) :
    letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
    IsLocalization.Away b (F.obj T') := by
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  refine ⟨?_, fun z ↦ ?_, fun {x y} e ↦ ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (mp F l (b ^ n))
    rw [map_pow]; exact h1.pow n
  · obtain ⟨n, x, e⟩ := h2 z
    refine ⟨(x, ⟨b ^ n, n, rfl⟩), ?_⟩
    change z * mp F l (b ^ n) = mp F l x
    rw [map_pow]; exact e
  · obtain ⟨n, hn⟩ := h3 (x - y) (by rw [map_sub]; exact sub_eq_zero.2 e)
    exact ⟨⟨b ^ n, n, rfl⟩, sub_eq_zero.1 (by rw [← mul_sub]; exact hn)⟩

theorem isUnit_mp_omExt_iff {T S : C} (u : T ⟶ S) (c : (omExt F).obj T) :
    IsUnit (mp (omExt F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMap F u c)))

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
    (y : TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R]) (a₀ : F.obj T) (η₀ : Ω[F.obj T⁄R]) (k₁ k₂ : ℕ)
    (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀) (hη : mp F l (c.fst ^ k₂) • y.snd = p1 F l η₀) :
    y * extMap F l c ^ (k₁ + k₂ + 1) = extMap F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMap, fst_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMap, fst_extMap, snd_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      oneFormsMapOfFunctorMorphism_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omExt (H : Desc.HasLoc F) : Desc.HasLoc (omExt F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ ω, p1 F l ω = KaehlerDifferential.map R R (F.obj T) (F.obj T') ω :=
    SemiHom.oneFormMap_eq_kaehlerDifferential_map _ fun _ ↦ rfl
  have hs : ∀ (a : F.obj T) (η : Ω[F.obj T'⁄R]), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omExt_iff F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omExt_iff F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (KaehlerDifferential.map R R (F.obj T) (F.obj T')) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_key F l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMap F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : KaehlerDifferential.map R R (F.obj T) (F.obj T') x.snd = 0 :=
      (hp _).symm.trans ((snd_extMap F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := KaehlerDifferential.map R R (F.obj T) (F.obj T')) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem span_inl_eq_top {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omExt F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) Ω[F.obj S⁄R])) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem glue_one_forms : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], [Quiver.IsThin C'] → ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : AffOp X') (s : ∀ t, (T ⟶ G.obj t) → Ω[(OAff s').obj (G.obj t)⁄R']), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 (OAff s') (G.map a) (s t u)) → ∃ ω : Ω[(OAff s').obj T⁄R'], ∀ t u, p1 (OAff s') u ω = s t u) := by
  intro R' _ X' s' C' _ _ G hcov hdir T s hs
  have unit : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) G (hasLoc_omExt (OAff s') (hasLoc_OAff s'))
    (fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unit u _ hu)⟩)
    (fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unit u _ hu)⟩)
    T (fun t u ↦ TrivSqZeroExt.inr (s t u)) (fun t t' u a ↦ by
      apply TrivSqZeroExt.ext
      · exact (TrivSqZeroExt.fst_inr _ _).trans (((fst_extMap (OAff s') (G.map a) _).trans
          (by rw [TrivSqZeroExt.fst_inr, map_zero])).symm)
      · exact ((TrivSqZeroExt.snd_inr _ _).trans (hs t t' u a)).trans
          ((snd_extMap (OAff s') (G.map a) _).trans (by rw [TrivSqZeroExt.snd_inr])).symm)
  exact ⟨x.snd, fun t u ↦ (snd_extMap (OAff s') u x).symm.trans
    ((congrArg TrivSqZeroExt.snd (hx t u)).trans (TrivSqZeroExt.snd_inr _ _))⟩

end GlobalTheory.CechDR.FormExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
namespace GlobalTheory.FinTypeIntCatenary

open ReciprocityTheory.CA

theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔓 𝔑 : Ideal S) [𝔓.IsPrime] [𝔑.IsPrime]
    (hle : 𝔓 ≤ 𝔑) (h : IsCM (Localization.AtPrime 𝔑)) : IsCM (Localization.AtPrime 𝔓) := by
  have hdisj : Disjoint (𝔑.primeCompl : Set S) (𝔓 : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let q : Ideal (Localization.AtPrime 𝔑) := 𝔓.map (algebraMap S (Localization.AtPrime 𝔑))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔓 inferInstance hdisj
  have h2 := h.localization_atPrime q
  have hc : q.comap (algebraMap S (Localization.AtPrime 𝔑)) = 𝔓 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔑.primeCompl _ inferInstance hdisj
  haveI : IsLocalization 𝔓.primeCompl (Localization.AtPrime q) := by
    have h0 : IsLocalization (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl
        (Localization.AtPrime q) :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (M := 𝔑.primeCompl) q
    have hsub : (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl = 𝔓.primeCompl :=
      Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hc]
    rw [hsub] at h0
    exact h0
  exact h2.of_ringEquiv (IsLocalization.algEquiv 𝔓.primeCompl (Localization.AtPrime q) (Localization.AtPrime 𝔓)).toRingEquiv

theorem height_comap_mk {S : Type*} [CommRing S] (Q : Ideal S) [Q.IsPrime] (J : Ideal (S ⧸ Q))
    [J.IsPrime] (h : IsCM (Localization.AtPrime (J.comap (Ideal.Quotient.mk Q)))) :
    (J.comap (Ideal.Quotient.mk Q)).height = Q.height + J.height := by
  have hle : Q ≤ J.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, J.zero_mem]
  have := height_eq_add_of_isCM_localization (J.comap (Ideal.Quotient.mk Q)) Q h hle
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this

theorem height_le_of_equidim {S : Type*} [CommRing S] (d : ℕ)
    (hS : ∀ (𝔑 : Ideal S) [𝔑.IsMaximal], IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = d)
    (Q : Ideal S) [Q.IsPrime] (P M : Ideal (S ⧸ Q)) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim ((S ⧸ Q) ⧸ P) := by
  haveI hMt : (M.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨hCM1, hd1⟩ := hS (M.comap (Ideal.Quotient.mk Q))
  have e1 := height_comap_mk Q M hCM1
  obtain ⟨M', hM', hPM'⟩ := Ideal.exists_le_maximal (P.comap (Ideal.Quotient.mk Q))
    (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨hCM2, hd2⟩ := hS M'
  have e2 := height_eq_add_of_isCM_localization M' (P.comap (Ideal.Quotient.mk Q)) hCM2 hPM'
  have e3 := height_comap_mk Q P (isCM_atPrime_of_le _ M' hPM' hCM2)
  have hQM : Q ≤ M.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M.zero_mem]
  have hQP : Q ≤ P.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, P.zero_mem]
  have hQle : Q.height ≤ d := hd1 ▸ Ideal.height_mono hQM
  have hQt : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
  have key : M.height = P.height +
      (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height := by
    have hsum : Q.height + M.height = Q.height + (P.height +
        (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height) := by
      rw [← e1, hd1, ← hd2, e2, e3, add_assoc]
    exact WithTop.add_left_cancel hQt hsum
  haveI : (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPM')
  have hb : ((M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height : WithBot ℕ∞) ≤
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) := Ideal.height_le_ringKrullDim_of_isPrime
  have hdim : ringKrullDim ((S ⧸ Q) ⧸ (P.comap (Ideal.Quotient.mk Q)).map (Ideal.Quotient.mk Q)) =
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQP)
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hdim
  rw [key, hdim]
  push_cast
  exact add_le_add le_rfl hb

theorem isMaximal_comap_C_int (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ)).IsMaximal := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) ℤ ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization_int (p : Ideal ℤ) [p.IsMaximal] :
    IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 := by
  have hp : p ≠ ⊥ := by
    intro h
    have : (⊥ : Ideal ℤ).IsMaximal := h ▸ inferInstance
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr this)
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp _
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
  refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, hd⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
  refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization (N : ℕ) (p : Ideal ℤ) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) ℤ) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) ℤ)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) ℤ) ∈ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_under W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap ℤ (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem isCM_and_height_of_isMaximal (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = ((N + 1 : ℕ) : ℕ∞) := by
  haveI := isMaximal_comap_C_int N 𝔑
  obtain ⟨hCM, hdim⟩ := isCM_localization_int (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

theorem height_maximal_le (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (P M : Ideal A) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ A›
  haveI : (RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)).IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) ℤ →+* A)) hf
  haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h := height_le_of_equidim (N + 1) (isCM_and_height_of_isMaximal N) _ (P.comap e) (M.comap e)
  rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
  have hdim : ringKrullDim ((MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ⧸
      P.comap e) = ringKrullDim (A ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective _ e.surjective P).symm)
  rwa [hdim] at h

end GlobalTheory.FinTypeIntCatenary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

open NumberField

section Mod

variable {O T V : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V]

def eigSub (μ : O →+* Module.End T V) (τ : O →+* T) : Submodule T V where
  carrier := {v | ∀ c, μ c v = τ c • v}
  add_mem' {u v} hu hv c := by simp only [Set.mem_setOf_eq, map_add (f := _), hu c, hv c, smul_add]
  zero_mem' c := by simp
  smul_mem' r v hv c := by simp only [Set.mem_setOf_eq, map_smul, hv c, smul_comm r]

theorem mem_eigSub {μ : O →+* Module.End T V} {τ : O →+* T} {v : V} :
    v ∈ eigSub μ τ ↔ ∀ c, μ c v = τ c • v := Iff.rfl

def LieMod (μ : O →+* Module.End T V) (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) : Prop :=
  ∀ v, μ ω v = ρ • v → ∃ w : Fin a → V, (∀ i, w i ∈ eigSub μ (τ i)) ∧ v = ∑ i, w i

end Mod

def matAct {O B T : Type} [CommRing O] [CommRing B] [CommRing T] {n : ℕ} (M : O →+* Matrix (Fin n) (Fin n) B)
    (f : B →+* T) : O →+* Module.End T (Fin n → T) :=
  (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)).toRingEquiv.toRingHom.comp (f.mapMatrix.comp M)

theorem matAct_apply {O B T : Type} [CommRing O] [CommRing B] [CommRing T] {n : ℕ}
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) (c : O) (v : Fin n → T) :
    matAct M f c v = ((M c).map f).mulVec v := rfl

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def lieMat (b : Base D R) {B : Type} [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B)
    (c : Fin D.a → 𝓞 D.F) : Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun i => M (c i) - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t i (c i)))).prod *
    (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ)))

def lieIdeal (b : Base D R) {B : Type} [CommRing B] (βB : R →+* B) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) : Ideal B :=
  Ideal.span {x | ∃ (c : Fin D.a → 𝓞 D.F) (i j : Fin n), lieMat b βB M c i j = x}

def LieHerMat (b : Base D R) {B : Type} [CommRing B] {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B)
    {T : Type} [CommRing T] (f : B →+* T) (β : R →+* T) : Prop :=
  ∀ (T' : Type) [CommRing T'] (g : T →+* T'),
    LieMod (matAct M (g.comp f)) D.ω (g (β b.ρ)) (fun i => (g.comp β).comp (b.t i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (h : T' →+* k) (i : Fin D.a),
      Module.finrank k (eigSub (matAct M (h.comp (g.comp f))) ((h.comp (g.comp β)).comp (b.t i))) = D.m

end GlobalTheory.UPel.HT.LieLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopy
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopy
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.TwResExt

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem twRes_ext : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧
    (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
    IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧
    ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  intro q _ i
  obtain ⟨hKI, hInj, hGE, hQI, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  refine ⟨⟨hGE, resAug _, hQI, fun _ _ => rfl⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf q ((res _ (tw q i)).X t)).2
  intro T e ⟨_, ε, hε, he⟩
  have hext := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) (tw q i) T (res _ (tw q i)) ε
  refine ⟨?_, fun u u' huu => ?_⟩
  · obtain ⟨m, hm⟩ := hext.1 (resAug _)
    refine ⟨m, fun U ζ => ?_⟩
    rw [← he U ζ, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
    rfl
  · refine hext.2 u u' ?_
    have htw := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2
    obtain ⟨hres, hrel, huniq⟩ := htw
    let ψ : (T ⟶ res _ (tw q i)) → (tw q i ⟶ (res _ (tw q i)).X 0) := fun v => sglι (tw q i) ≫ (ε ≫ v).f 0
    have key : ∀ v : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (ψ v) (twGen i ζ) = Sec.map (v.f 0) (e U ζ) := by
      intro v U ζ
      rw [← he U ζ]
      rfl
    have hnat : ∀ v : T ⟶ res _ (tw q i), ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
        Sec.res g (Sec.map (ψ v) (twGen i ζ)) = Sec.map (ψ v) (twGen i (ζ.map g.appTop.hom)) := by
      intro v V U g ζ
      rw [← hres V U g ζ]
      exact (congrArg (fun f => f.hom (twGen i ζ)) ((ψ v).hom.naturality g.op)).symm
    have hrl : ∀ v : T ⟶ res _ (tw q i), ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ),
        ξ.1 = ζ.1 ^ (a : ZMod q).val →
        Sec.map (ψ v) (twGen i ξ) = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • Sec.map (ψ v) (twGen i ζ) := by
      intro v U ζ ξ a h
      rw [hrel U ζ ξ a h]
      exact map_nsmul _ _ _
    obtain ⟨φ, -, hφ⟩ := huniq ((res _ (tw q i)).X 0) (fun U ζ => Sec.map (ψ u) (twGen i ζ)) (hnat u) (hrl u)
    have h1 := hφ (ψ u) fun U ζ => rfl
    have h2 := hφ (ψ u') fun U ζ => by rw [key, key, huu]
    have h12 : ψ u = ψ u' := h2.symm ▸ h1 ▸ rfl
    apply HomologicalComplex.from_single_hom_ext
    exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)) _ _).1 h12

end GlobalTheory.EtC.TwResExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  first | (exact @GlobalTheory.EtC.TwResExt.twRes_ext) | (exact GlobalTheory.EtC.TwResExt.twRes_ext) | (intros; apply GlobalTheory.EtC.TwResExt.twRes_ext  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulP
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)


open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo (n : ℕ) (x : G.A (n + 1))
    (t : G.A n ⊗[R] G.A n)
    (h : _root_.GlobalTheory.PDiv.cobOne R _ x = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) t)
    (h1 : G.resOne n x = 0) :
    G.transl n x = x ⊗ₜ 1 := by
  set f := G.mulP n
  set ρ := G.resOne n
  have hcomul : comul x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x +
      TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
        (f : G.A n →ₗ[R] G.A (n + 1)) t := by
    have := h
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo at this
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at this
    rw [← this]; abel
  have hε : counit x = (0 : R) := by
    have := CoalgHomClass.counit_comp_apply ρ x
    rw [h1, map_zero] at this
    exact this.symm
  have hρf : (ρ : G.A (n + 1) →ₗ[R] G.A 1) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1))
        = Algebra.linearMap R _ ∘ₗ counit := by
    ext a
    exact _root_.GlobalTheory.PDivGroup.resOne_mulP G n a
  have hεf : (counit : _ →ₗ[R] R) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1)) = counit := by
    ext a
    exact CoalgHomClass.counit_comp_apply f a
  have hzero : TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
      (counit : _ →ₗ[R] R) t = 0 := by
    have := congrArg (LinearMap.lTensor _ (counit : _ →ₗ[R] R)) hcomul
    rw [Coalgebra.lTensor_counit_comul, map_add (f := _), map_add (f := _), LinearMap.lTensor_tmul,
      LinearMap.lTensor_tmul, hε, counit_one, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map,
      hεf, tmul_zero, add_zero] at this
    simpa using this
  rw [_root_.GlobalTheory.PDivGroup.transl_apply, hcomul, map_add (f := _), map_add (f := _), LinearMap.lTensor_tmul,
    LinearMap.lTensor_tmul, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map, hρf,
    ← LinearMap.lTensor_comp_map, LinearMap.comp_apply, hzero, map_zero, add_zero]
  have h1' : G.resOne n x = 0 := h1
  simp [h1']

end PDivGroup


open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
theorem _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP :
    ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
      (c : G.cocycles) (B : G.funs),
        G.cob B = _root_.GlobalTheory.PDivGroup.cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G c B hB hB1
  have hcobf : ∀ {m m' : ℕ} (f : G.A m →ₐc[R] G.A m') (a),
      _root_.GlobalTheory.PDiv.cobOne R _ (f a)
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.cobOne R _ a) := by
    intro m m' f a
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply, map_sub,
      TensorProduct.map_tmul]
    rw [← CoalgHomClass.map_comp_comul_apply f a]
    simp
  have hpull : ∀ {m m' m'' : ℕ} (f : G.A m' →ₐc[R] G.A m'')
      (g : G.A m →ₐc[R] G.A m') (z),
      _root_.GlobalTheory.PDiv.pullbackTwo (f.comp g) z
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.pullbackTwo g z) := by
    intro m m' m'' f g z
    unfold _root_.GlobalTheory.PDiv.pullbackTwo
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  have hlevel : ∀ n, _root_.GlobalTheory.PDiv.cobOne R _ (B.1 (n + 1))
      = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    have h := congrArg (fun z => z.1 (n + 1)) hB
    unfold _root_.GlobalTheory.PDivGroup.cob _root_.GlobalTheory.PDivGroup.cocyclesMap at h
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at h
    rw [h, _root_.GlobalTheory.PDivGroup.natCast_smul_id_app, ← _root_.GlobalTheory.PDivGroup.mulP_comp_res, hpull]
    congr 1
    exact (c.2 n).2
  have hres1 : ∀ n, G.resOne n (B.1 (n + 1)) = 0 := by
    intro n
    rw [_root_.GlobalTheory.PDivGroup.resOne_funs, hB1]
  have hex : ∀ n, ∃ e, G.mulP n e = B.1 (n + 1) := fun n =>
    _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq G n _
      (_root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo G n _ _ (hlevel n) (hres1 n))
  choose e he using hex
  have hcompat : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply _root_.GlobalTheory.PDivGroup.Test.mulP_injective G n
    rw [_root_.GlobalTheory.PDivGroup.mulP_res, ← _root_.GlobalTheory.PDivGroup.res_mulP, he, he]
    exact B.2 (n + 1)
  refine ⟨⟨e, hcompat⟩, ?_⟩
  apply Subtype.ext
  funext n
  apply _root_.GlobalTheory.PDivGroup.pullbackTwo_mulP_injective G n
  rw [← hlevel, ← he, hcobf]
  rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulPStatement
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R) (c : G.cocycles) (B : G.funs), G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 → c ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | exact GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | (intros; apply GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.OpenImmDim

theorem topologicalKrullDim_eq_of_isOpenImmersion : ∀ (F : Type) [Field F] (X V : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ]
    [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  intro F _ X V _ p ℓ _ _ _
  have hne : ((ℓ.opensRange : X.Opens) : Set X).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, by rw [Scheme.Hom.coe_opensRange]; exact ⟨v, rfl⟩⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F p ℓ.opensRange hne]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding ℓ.isOpenEmbedding.isEmbedding
    (by rw [Scheme.Hom.coe_opensRange])).symm

end GlobalTheory.OpenImmDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme : ∀ (F : Type) [Field F] (X V : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ] [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  first | exact @GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | exact GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | (intros; apply GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cup_natural_in_pairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ]
  simp only [cpush, cpost_mk]
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 _ _ _ ?_).symm
  intro N w h U x
  have hm := fun {L L' : Cx R} (φ : L ⟶ L') {d : ℤ} (c : Cochain ((chains R).obj E) L d) p s hs U x =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := d)).2.2.2.2 φ c p s hs U x
  change ev (γ.1.comp (Cochain.ofHom u) (add_zero k)) N w h U x = _
  rw [hm, hγ N w h U x]
  refine (map_sum ((u.f w).hom.app (op U)).hom _ _).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  change Sec.map (u.f w) _ = _ • ν.mul U _ _ w _ (ev (α.1.comp (Cochain.ofHom f) (add_zero n)) _ _ _ U _) (ev (β.1.comp (Cochain.ofHom g) (add_zero m)) _ _ _ U _)
  rw [hm, hm, Units.smul_def, Units.smul_def, ← hc]
  exact map_zsmul ((u.f w).hom.app (op U)).hom _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  first | (exact @GlobalTheory.cup_natural_in_pairing) | (exact GlobalTheory.cup_natural_in_pairing) | (intros; apply GlobalTheory.cup_natural_in_pairing  <;> assumption)
end
end
