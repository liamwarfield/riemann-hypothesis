module

public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConjStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitReduction

open IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueEmb (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ResidueField (integralClosure ℤ_[p] K) →+* GlobalTheory.ZJ.kb p :=
  haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
  ResidueField.map (integralClosureToPadicAlgClIntegers K)

noncomputable def intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') :
    integralClosure ℤ_[p] K →+* integralClosure ℤ_[p] K' :=
  ((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure

instance isLocalHom_intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') : IsLocalHom (intIncl h) :=
  isLocalHom_of_injective_integralClosure _ (mapIntegralClosure_padicInt_injective (IntermediateField.inclusion h))

theorem exists_subset_range (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (s : Set (GlobalTheory.ZJ.kb p)) (hs : s.Finite) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : K ≤ K') (_ : FiniteDimensional ℚ_[p] K'),
      s ⊆ Set.range (residueEmb K') := by
  choose l hl using residue_surjective (R := GlobalTheory.ZJ.OO p)
  let t : Set (PadicAlgCl p) := (fun x => (l x : PadicAlgCl p)) '' s
  haveI : Finite t := (hs.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] t) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K ⊔ IntermediateField.adjoin ℚ_[p] t, le_sup_left, inferInstance, fun x hx => ?_⟩
  have hm : (l x : PadicAlgCl p) ∈ K ⊔ IntermediateField.adjoin ℚ_[p] t :=
    (le_sup_right : IntermediateField.adjoin ℚ_[p] t ≤ _) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
  refine ⟨residue _ ⟨⟨_, hm⟩, (mem_integralClosure_padicInt_iff _ _).2
    ((mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (l x).2)⟩, ?_⟩
  exact hl x

theorem residueEmb_comp {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K'] (h : K ≤ K') :
    (residueEmb K').comp (ResidueField.map (intIncl h)) = residueEmb K :=
  RingHom.ext fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    exact congrArg (residue (GlobalTheory.ZJ.OO p)) (Subtype.ext rfl)

theorem algebraMap_comp_intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') :
    (IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K) =
      (algebraMap (integralClosure ℤ_[p] K') K').comp (intIncl h) :=
  RingHom.ext fun _ => rfl

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_iso_of_square {R R₁ R₂ T : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing T]
    {a : R →+* R₁} {b : R₁ →+* T} {c : R →+* R₂} {d : R₂ →+* T} (e : b.comp a = d.comp c)
    (G : Over (Sp R)) [GrpObj G] :
    ∃ i : (Over.pullback (spMap b)).obj ((Over.pullback (spMap a)).obj G) ≅
      (Over.pullback (spMap d)).obj ((Over.pullback (spMap c)).obj G), IsMonHom i.hom := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_comp, e, ← spMap_comp]) rfl)
    ((isGrpPullback_pullback ((Over.pullback (spMap c)).obj G) (spMap d)).comp (isGrpPullback_pullback G _))
  exact ⟨i, hi⟩

theorem exists_finite_torusExtension_specialFibre {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [IsAlgClosed Ω]
    (σ : ResidueField R →+* Ω) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
      (β : ResidueField R' →+* Ω), β.comp (ResidueField.map f) = σ → s ⊆ Set.range β →
      ∃ E : SplitExt (Sp (ResidueField R')),
        E.IsGt ((Over.pullback (spMap (residue R'))).obj ((Over.pullback (spMap f)).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  obtain ⟨T⟩ := h₀.fibres _ (spMap σ)
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ _ T
  refine ⟨s, hs, fun R' _ _ f _ β hβ hr => ?_⟩
  obtain ⟨T'⟩ := H _ (ResidueField.map f) β hβ hr
  obtain ⟨i, hi⟩ := exists_iso_of_square (ResidueField.map_comp_residue f) G
  haveI := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T'⟩

theorem exists_isGrpPullback_of_square {R R₁ R₂ T K : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing T]
    [CommRing K] {a : R →+* R₁} {b : R₁ →+* T} {c : R →+* R₂} {d : R₂ →+* T} (e : b.comp a = d.comp c)
    {u : K →+* R₁} {v : K →+* T} (e' : b.comp u = v) (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A]
    {φ : pullback G.hom (spMap a) ⟶ A.left} (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ : pullback ((Over.pullback (spMap c)).obj G).hom (spMap d) ⟶ A.left,
      IsGrpPullback ((Over.pullback (spMap d)).obj ((Over.pullback (spMap c)).obj G)) A (spMap v) ψ := by
  obtain ⟨i, hi⟩ := exists_iso_of_square e.symm G
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_comp, e']) rfl⟩

end GlobalTheory.SplitReduction

namespace GlobalTheory


open SplitReduction in
theorem exists_semiAbelian_model_split_specialFibre : GlobalTheory.Published.SemistableReductionSt → ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K') (_ : IsLocalRing (integralClosure ℤ_[p] K')), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ E : SplitExt (Sp (IsLocalRing.ResidueField (integralClosure ℤ_[p] K'))), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue (integralClosure ℤ_[p] K')))).obj G)) ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro H p _ K _ P
  obtain ⟨K₁, h₁, f₁, G, gG, hG, φ, hφ⟩ := H p K P
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := p)
  obtain ⟨s, hs, T⟩ := exists_finite_torusExtension_specialFibre (residueEmb K₁) G hG
  obtain ⟨K', h, f', hr⟩ := exists_subset_range K₁ s hs
  exact ⟨K', h₁.trans h, inferInstance, f', (Over.pullback (spMap (intIncl h))).obj G, inferInstance,
    IsSemiAbelian.pullback _ G hG, T _ (intIncl h) (residueEmb K') (residueEmb_comp h) hr,
    exists_isGrpPullback_of_square (algebraMap_comp_intIncl h) (RingHom.ext fun _ => rfl) G P.A hφ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem natCast_self_residueField_padicAlgCl_eq_zero (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  have : (((p : ℕ) : OO p) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [this, PadicAlgCl.valuation_p]
  have h1 : (1 : NNReal) < p := by exact_mod_cast hp.out.one_lt
  rw [div_lt_one (lt_trans zero_lt_one h1)]
  exact h1

theorem ker_isMaximal_of_forall_pow_eq_one {A k : Type*} [CommRing A] [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) (φ : A →+* k) :
    (RingHom.ker φ).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨by simp, fun J a hJ ha haJ => ?_⟩
  obtain ⟨n, hn, h⟩ := hk (φ a) ha
  have h1 : 1 - a ^ n ∈ J := hJ (by simp [RingHom.mem_ker, h])
  have h2 : a ^ n ∈ J := J.pow_mem_of_mem haJ n hn
  simpa using J.add_mem h1 h2

theorem isClosed_image_point_of_forall_pow_eq_one {k : Type} [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) {X : Scheme.{0}} [JacobsonSpace X]
    (x : Sp k ⟶ X) (s : Sp k) : IsClosed ({x s} : Set X) := by
  obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing x
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hs : Spec.map φ s ∈ closedPoints (Spec Γ(X, V)) := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr ?_
    have := (s : PrimeSpectrum k).isPrime
    have e : (s : PrimeSpectrum k).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have : (Spec.map φ s : PrimeSpectrum Γ(X, V)).asIdeal = RingHom.ker φ.hom := by
      change Ideal.comap φ.hom (s : PrimeSpectrum k).asIdeal = _
      rw [e]; rfl
    rw [this]
    exact ker_isMaximal_of_forall_pow_eq_one hk φ.hom
  rw [← h] at hs
  rw [Scheme.Hom.comp_apply]
  exact hs

theorem exists_residueField_factor_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}}
    (x : Sp k ⟶ X) (s : Sp k) (z : X) (hz : x s = z) :
    ∃ r : X.residueField z ⟶ CommRingCat.of k, Spec.map r ≫ X.fromSpecResidueField z = x := by
  obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst hz
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x⟩

theorem exists_integral_point_lifting_residue_point :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens),
      (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime],
        (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧
        (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  intro X _ π _ _ U hU p hp
  obtain ⟨hJ, hfin, -⟩ := jacobson_closedPoints_tools_int X π
  obtain ⟨-, hord, hgal⟩ := GlobalTheory.T.kb_isAlgClosed_and_conj' p
  have hcl : ∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X) :=
    fun x s => isClosed_image_point_of_forall_pow_eq_one hord x s
  refine ⟨fun x => ?_, hcl⟩
  let s : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hlift : ∃ (q : ℕ) (_ : Fact q.Prime) (y : Sp (OO q) ⟶ X),
      y (IsLocalRing.closedPoint (OO q)) = x s ∧ Set.range (gPt q ≫ y) ⊆ U := by
    obtain ⟨q, hq, hqz⟩ := exists_prime_residueField_eq_zero π (hcl x s)
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨K, hK, y, hy, hyU, -⟩ := exists_padic_point_scheme π (hcl x s) hqz U hU
    have hmem (a : PadicAlgCl q) : a ∈ OO q ↔ ‖a‖ ≤ 1 := by
      rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
      rfl
    let j : integralClosure ℤ_[q] K →+* OO q :=
      (K.val.toRingHom.comp (integralClosure ℤ_[q] K).val.toRingHom).codRestrict (OO q)
        fun a => (hmem _).mpr ((mem_integralClosure_padicInt_iff K _).mp a.2)
    haveI : IsLocalHom j := by
      refine ⟨fun a ha => ?_⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : ((a : K) : PadicAlgCl q) * (b : PadicAlgCl q) = 1 :=
        congrArg (fun z : OO q => (z : PadicAlgCl q)) hb
      have ha0 : (a : K) ≠ 0 := by
        intro h
        rw [h] at hb'
        simp at hb'
      have hinv : (a : K)⁻¹ ∈ integralClosure ℤ_[q] K := by
        rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
          ← eq_inv_of_mul_eq_one_right hb']
        exact (hmem _).mp b.2
      exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
    refine ⟨q, inferInstance, spMap j ≫ y, ?_, ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
      exact IsLocalRing.comap_closedPoint j
    · rintro _ ⟨t, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      have key : spMap j ((gPt q) t) = genericPoint (Sp (integralClosure ℤ_[q] K)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        apply le_antisymm _ bot_le
        intro a ha
        have ha' : ((a : K) : PadicAlgCl q) ∈ (t : PrimeSpectrum (PadicAlgCl q)).asIdeal := ha
        haveI := (t : PrimeSpectrum (PadicAlgCl q)).isPrime
        rw [Ideal.eq_bot_of_prime (t : PrimeSpectrum (PadicAlgCl q)).asIdeal,
          Ideal.mem_bot] at ha'
        exact Subtype.ext (Subtype.ext ha')
      rw [Scheme.Hom.comp_apply, key]
      exact hyU
  obtain ⟨q, hq, y, hy, hyU⟩ := hlift
  have hfz := hfin _ (hcl x s)
  obtain ⟨r', hr'⟩ := exists_residueField_factor_of_apply_eq x s _ rfl
  have hy' : (rPt q ≫ y) (IsLocalRing.closedPoint (kb q)) = x s := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO q))
  obtain ⟨r, hr⟩ := exists_residueField_factor_of_apply_eq (rPt q ≫ y) _ _ hy'
  obtain rfl : p = q := by
    have h1 : ((p : ℕ) : X.residueField (x s)) = 0 := by
      apply r'.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero p
    have h2 : ((q : ℕ) : X.residueField (x s)) = 0 := by
      apply r.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero q
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hp.out).mpr h1
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hq.out).mpr h2
    exact CharP.eq (X.residueField (x s)) ‹CharP _ p› ‹CharP _ q›
  obtain ⟨σ, hσ⟩ := hgal (X.residueField (x s)) r.hom r'.hom
  refine ⟨spMap σ.toRingHom ≫ y, ?_, ?_⟩
  · let τ : kb p →+* kb p := IsLocalRing.ResidueField.map (σ : OO p →+* OO p)
    have e1 : rPt p ≫ spMap σ.toRingHom = spMap τ ≫ rPt p := by
      refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
      rfl
    have e2 : r ≫ CommRingCat.ofHom τ = r' := by
      ext a
      obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (r.hom a)
      change τ (r.hom a) = r'.hom a
      rw [← hσ a c hc, ← hc]
      rfl
    rw [← Category.assoc, e1, Category.assoc]
    refine (congrArg (spMap τ ≫ ·) hr.symm).trans (Eq.trans ?_ hr')
    rw [← e2, Spec.map_comp, Category.assoc]
  · rintro _ ⟨t, rfl⟩
    apply hyU
    refine ⟨t, ?_⟩
    simp only [Scheme.Hom.comp_apply]
    congr 1
    have := (t : PrimeSpectrum (PadicAlgCl p)).isPrime
    have e : (t : PrimeSpectrum (PadicAlgCl p)).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    apply PrimeSpectrum.ext
    ext a
    change (a : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal ↔
      ((σ a : OO p) : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal
    rw [e]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_classical_point_lifting_residue_point : ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens), (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime], (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧ (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  first | exact @GlobalTheory.exists_integral_point_lifting_residue_point | exact GlobalTheory.exists_integral_point_lifting_residue_point | (intros; apply GlobalTheory.exists_integral_point_lifting_residue_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTestMatch
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ZH

theorem exists_test_match : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) → (0 < S.delta y₀ ∧ AddSubgroup.closure {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} = l.yy.ker) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∀ h ∈ l.yy.ker, ∀ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ h ∈ l.yy.ker, ∃ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt 0) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀) → ∃ τ : S.Test p y₀, l.Match τ := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l h1 h2 h3 h4 h5
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hmax : IsGreatest (Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (S.delta y₀) := by
    obtain ⟨x, hx⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖)
    refine ⟨⟨x, hx⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove z
  let τ : S.Test p y₀ :=
    { X := u.D.toPre.X
      q := l.q
      pos := l.pos
      yy := l.yy
      yy_onto := l.yy_onto
      isoFree := l.isoFree
      wt := l.wt
      wt_eq := l.wt_eq
      δ := S.delta y₀
      δ_max := hmax
      δ_pos := h2.1
      supp := h2.2
      tx := h1
      le := h3
      eq := h4
      unit0 := h5 }
  exact ⟨τ, AddEquiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl⟩
end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormDividingWeightSumEqOfModelPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory

theorem norm_val_FF_eq_of_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) := by
  intro o Ω _ _ _ _ S M U₀ hO h0 h1 _ z p _ y y₀ τ hC hA
  have hT : S.TT M z = S.perp τ.yy.ker := by
    rw [ThetaSys.TT, (h0 z p y y₀ τ hC hA).2]
  obtain ⟨hmem, -, hpp, -⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  rw [hT]
  intro c k α hdiv hα hc
  have hcw : c = τ.wt α := AddMonoidHom.ext fun t => hc t.1 t.2 t.2
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [hA]
    exact hC.norm_val_le_one ((M.O z).algebraMap_mem a)
  have hk : M.val (gPt p ≫ y) (S.FF _ c k) = y₀ ⟨_, hmem _ c k⟩ := (hA ⟨_, hmem _ c k⟩).symm
  refine le_antisymm ?_ ?_
  · rw [hk]
    exact (h1 p y₀ τ hint _ c k (hmem _ c k) τ.isoFree).1 le_rfl
      (τ.isoFree.1.trans (hpp _).le) α hα hc
  · subst hcw
    obtain ⟨k₁, hk₁, he⟩ := τ.eq α hα
    rw [← he, hA]
    let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w := fun w' => by
      have : (gPt p ≫ y) w' ∈ Set.range (gPt p ≫ y) := ⟨w', rfl⟩
      rw [RatModel.range_eq_singleton _ w] at this
      rw [this]
    have hU : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
    have hq := hdiv.2 k₁
    have hmul := RatModel.val_mul hw
      (RatModel.O_le_of_specializes (RatModel.gPt_specializes hC.1 w) hq)
      (RatModel.ringOn_le_O hU (hO.le (hmem _ (τ.wt α) k)))
    rw [div_mul_cancel₀ _ hdiv.1] at hmul
    change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k₁)‖ ≤ _
    rw [hmul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hC.norm_val_le_one hq)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocus
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread.ClosedFac

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

def str {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) : CommRingCat.of R ⟶ Γ(H, U) :=
  CommRingCat.ofHom (GlobalTheory.SectionsCommRing.structureHom q U)

theorem fromSpec_comp {H : Scheme.{0}} (q : H ⟶ Sp R) {U : H.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (str q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl

theorem str_res {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) (a : R) :
    str q U a = H.presheaf.map (homOfLE le_top).op (str q ⊤ a) :=
  (GlobalTheory.SectionsCommRing.map_structureHom q le_top a).symm

theorem appTop_str {H T : Scheme.{0}} (q : H ⟶ Sp R) {R' : Type} [CommRing R'] (g : R →+* R') (x : T ⟶ H)
    (t : T ⟶ Sp R') (w : x ≫ q = t ≫ spMap g) (a : R) : x.appTop (str q ⊤ a) = str t ⊤ (g a) := by
  have e {Y : Scheme.{0}} {S : Type} [CommRing S] (p : Y ⟶ Sp S) :
      str p ⊤ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop :=
    congrArg ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ·) (Scheme.Hom.appLE_eq_app (f := p) (U := ⊤))
  have : str q ⊤ ≫ x.appTop = CommRingCat.ofHom g ≫ str t ⊤ := by
    rw [e, e, Category.assoc, ← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg (fun φ => φ.hom a) this

theorem eq_zero_of_app_eq_zero {H : Scheme.{0}} {U : H.Opens} (hU : IsAffineOpen U) {B : CommRingCat.{0}}
    (f : Γ(H, U) ⟶ B) (s : Γ(H, U)) (hs : (Spec.map f ≫ hU.fromSpec).app U s = 0) : f s = 0 := by
  have hz : ⊤ ≤ (Spec.map f ≫ hU.fromSpec) ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(H, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(H, U)).presheaf.map_id _
  have h2 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map f).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [h1, ← Scheme.ΓSpecIso_inv_naturality] at h2
  have h3 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz s = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hs, map_zero]
  rw [h2, CommRingCat.comp_apply] at h3
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective).1 h3

theorem exists_mul_eq_zero [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Z H : Scheme.{0}} (i : Z ⟶ H) (q : H ⟶ Sp R) [IsLocallyNoetherian H]
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) (U : H.affineOpens) :
    ∃ a : R, a ≠ 0 ∧ ∀ s ∈ i.ker.ideal U, str q U.1 a * s = 0 := by
  classical
  let M : Submonoid Γ(H, U.1) := (nonZeroDivisors R).map (str q U.1).hom
  let B := Localization M
  let φ : R →+* B := (algebraMap Γ(H, U.1) B).comp (str q U.1).hom
  have hφ (y : nonZeroDivisors R) : IsUnit (φ y) := IsLocalization.map_units B (⟨_, y, y.2, rfl⟩ : M)
  let ψ : K →+* B := IsLocalization.lift (M := nonZeroDivisors R) hφ
  obtain ⟨y, hy⟩ := h B (spMap (algebraMap Γ(H, U.1) B) ≫ U.2.fromSpec) (spMap ψ) (by
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact (IsLocalization.lift_comp (M := nonZeroDivisors R) hφ).symm)
  have key (s : Γ(H, U.1)) (hs : s ∈ i.ker.ideal U) : ∃ a : R, a ≠ 0 ∧ str q U.1 a * s = 0 := by
    have h1 := (y ≫ i).ideal_ker_le U (y.le_ker_comp i U hs)
    rw [hy] at h1
    have h2 : algebraMap Γ(H, U.1) B s = 0 :=
      eq_zero_of_app_eq_zero U.2 (CommRingCat.ofHom (algebraMap Γ(H, U.1) B)) s h1
    obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff M B s).1 h2
    exact ⟨a, nonZeroDivisors.ne_zero ha, hm⟩
  have := IsLocallyNoetherian.component_noetherian U
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (i.ker.ideal U)
  have hS' (s : S) : s.1 ∈ i.ker.ideal U := hS ▸ Ideal.subset_span s.2
  choose a ha ha' using fun s : S => key s (hS' s)
  refine ⟨∏ s, a s, Finset.prod_ne_zero_iff.2 fun s _ => ha s, fun s hs => ?_⟩
  rw [← hS] at hs
  refine Submodule.span_induction (fun s hs => ?_) (mul_zero _) (fun u v _ _ hu hv => ?_)
    (fun c u _ hu => ?_) hs
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨s, hs⟩ : S)), map_mul, mul_assoc, ha' ⟨s, hs⟩, mul_zero]
  · rw [mul_add, hu, hv, add_zero]
  · rw [smul_eq_mul, mul_left_comm, hu, mul_zero]

theorem exists_lift (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R) (hi : IsClosedImmersion i)
    (hq : LocallyOfFiniteType q) (hq' : QuasiCompact q)
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  classical
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace H := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨S, hS, hSU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : H.Opens))).1
    isCompact_univ
  have : Fintype S := hS.fintype
  choose a ha ha' using exists_mul_eq_zero i q h
  refine ⟨∏ U : S, a U, Finset.prod_ne_zero_iff.2 fun U _ => ha U, fun R' _ g hg T x t w => ?_⟩
  set s := str q ⊤ (∏ U : S, a U) with hs
  have hx : IsUnit (x.appTop s) := by
    rw [hs, appTop_str q g x t w]
    exact hg.map _
  have hle : i.ker ≤ (H.basicOpen s).ι.ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) ?_ fun U u hu => ?_
    · rw [hSU, iSup_subtype]
    · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
      have h0 : str q U.1.1 (∏ U : S, a U) * u = 0 := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ U), map_mul, mul_assoc, ha' _ u hu, mul_zero]
      have h1 : IsUnit ((H.basicOpen s).ι.app U.1.1 (str q U.1.1 (∏ U : S, a U))) := by
        rw [str_res, ← hs, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        refine IsUnit.map _ ?_
        refine (H.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z _ => ?_
        refine (Scheme.mem_basicOpen _ _ z _).1 ?_
        rw [← Scheme.preimage_basicOpen]
        exact z.2
      exact h1.mul_right_eq_zero.1 (by rw [← map_mul, h0, map_zero])
  have hr : Set.range x ⊆ Set.range (H.basicOpen s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ x ⁻¹ᵁ H.basicOpen s
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hx]
    trivial
  refine ⟨IsOpenImmersion.lift _ x hr ≫ IsClosedImmersion.lift i _ hle, ?_⟩
  rw [Category.assoc, IsClosedImmersion.lift_fac, IsOpenImmersion.lift_fac]

end GlobalTheory.GenSpread.ClosedFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_immersion_generic_unit_locus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R), IsClosedImmersion i → LocallyOfFiniteType q → QuasiCompact q → (∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) → ∃ y : Sp B ⟶ Z, y ≫ i = x) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  first | exact @GlobalTheory.GenSpread.ClosedFac.exists_lift | exact GlobalTheory.GenSpread.ClosedFac.exists_lift | (intros; apply GlobalTheory.GenSpread.ClosedFac.exists_lift <;> assumption)
end
end
