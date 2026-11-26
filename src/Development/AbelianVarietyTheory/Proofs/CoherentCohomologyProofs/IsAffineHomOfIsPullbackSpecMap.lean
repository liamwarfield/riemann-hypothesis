module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoToInterAppPushforwardInclusion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Base

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

def baseRingHom (p : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_res (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by
  rw [← ConcreteCategory.comp_apply, baseRingHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl

theorem baseRingHom_top (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
  rw [baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_app (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) :
    baseRingHom p U ≫ g.app U = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) := by
  rw [baseRingHom, baseRingHom, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

theorem app_baseRingHom (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) (r : R) :
    g.app U (baseRingHom p U r) = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) r := by
  rw [← baseRingHom_comp_app]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_SpecMap {L : CommRingCat.{u}} (q : Y ⟶ Spec L) (ι : R ⟶ L)
    (V : Y.Opens) : baseRingHom (q ≫ Spec.map ι) V = ι ≫ baseRingHom q V := by
  rw [baseRingHom, baseRingHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  exact congrArg _ (Scheme.Hom.appLE_comp_appLE q (Spec.map ι) ⊤ ⊤ V le_top le_top).symm

end Base

section Localization

variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))

include H

omit S in
theorem baseRingHom_algebraMap (V : Y.Opens) (r : R) :
    baseRingHom q V (algebraMap R L r) = baseRingHom (g ≫ p) V r := by
  rw [H.w, baseRingHom_comp_SpecMap]; rfl


theorem isLocalization_app {V : X.Opens} (hV : IsAffineOpen V) :
    @IsLocalization Γ(X, V) _ (S.map (baseRingHom p V).hom) Γ(Y, g ⁻¹ᵁ V) _
      (g.app V).hom.toAlgebra := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have po' : IsPushout (baseRingHom p V) (CommRingCat.ofHom (algebraMap R L)) (g.app V)
      (baseRingHom q (g ⁻¹ᵁ V)) := by
    refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (g.app V).hom.toAlgebra
  let := (baseRingHom p V).hom.toAlgebra
  let := (baseRingHom q (g ⁻¹ᵁ V)).hom.toAlgebra
  let := (baseRingHom (g ≫ p) (g ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower R Γ(X, V) Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom g p V r).symm
  have : IsScalarTower R L Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap H _ r).symm
  exact (Algebra.isLocalization_iff_isPushout S L).mpr
    (CommRingCat.isPushout_iff_isPushout.mp po')

end Localization

end GlobalTheory.QCoh.Qcqs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

section Index

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]

variable [IsDomain R] [IsDiscreteValuationRing R]

end Index

section Points

variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]

theorem det_algHom_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : (Matrix.of fun i j => P j (e i)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hc₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hli := (linearIndependent_algHom_toLinearMap R S L).comp P hP
  rw [Fintype.linearIndependent_iff] at hli
  refine hc (funext (hli c (e.ext fun i => ?_)))
  have := congrFun hc₀ i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this


omit [IsDomain L] in
theorem algHom_matrix_mul_leftMulMatrix (e : Basis ι R S) (P : ι → (S →ₐ[R] L)) (x : S) :
    (Matrix.of fun j i => P j (e i)) * (Algebra.leftMulMatrix e x).map (algebraMap R L) =
      Matrix.diagonal (fun j => P j x) * Matrix.of fun j i => P j (e i) := by
  ext j k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.diagonal_mul, Matrix.of_apply, ← map_mul, ← e.sum_repr (x * e k), map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Matrix.of_apply, mul_comm]

theorem map_charpoly_leftMulMatrix_eq_prod_algHom (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    (Algebra.leftMulMatrix e x).charpoly.map (algebraMap R L) = ∏ j, (X - C (P j x)) := by
  set Q : Matrix ι ι L := Matrix.of fun j i => P j (e i) with hQ
  have hQ₀ : Q.det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact det_algHom_basis_ne_zero e hP
  have h := algHom_matrix_mul_leftMulMatrix e P x
  rw [← hQ] at h
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal]
  set A := (Algebra.leftMulMatrix e x).map (algebraMap R L)
  set D := Matrix.diagonal fun j => P j x
  have h₁ : (C : L →+* L[X]).mapMatrix Q * A.charmatrix =
      D.charmatrix * (C : L →+* L[X]).mapMatrix Q := by
    simp only [Matrix.charmatrix, mul_sub, sub_mul, ← map_mul, h]
    congr 1
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm
  have h₂ := congrArg Matrix.det h₁
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, mul_comm] at h₂
  exact mul_right_cancel₀ (C_ne_zero.mpr hQ₀) h₂

theorem algebraMap_trace_eq_sum_algHom_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  have h := map_charpoly_leftMulMatrix_eq_prod_algHom e hP x
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal] at h
  rw [Algebra.trace_eq_matrix_trace e, ← Matrix.trace_diagonal,
    Matrix.trace_eq_neg_charpoly_nextCoeff (Matrix.diagonal _), ← h,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, AddMonoidHom.map_trace]

theorem map_traceMatrix_eq_mul_transpose_of_basis {κ : Type*} (e : Basis ι R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : κ → S) :
    (Algebra.traceMatrix R v).map (algebraMap R L) =
      (Matrix.of fun i j => P j (v i)) * (Matrix.of fun i j => P j (v i)).transpose := by
  ext i k
  simp [algebraMap_trace_eq_sum_algHom_of_basis e hP, Matrix.mul_apply]

theorem algebraMap_discr_eq_det_sq_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_traceMatrix_eq_mul_transpose_of_basis e hP, Matrix.det_mul, Matrix.det_transpose, pow_two]

theorem algebraMap_discr_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : algebraMap R L (Algebra.discr R e) ≠ 0 := by
  rw [algebraMap_discr_eq_det_sq_of_basis e hP]
  exact pow_ne_zero _ (det_algHom_basis_ne_zero e hP)

variable [Module.Free R S] [Module.Finite R S]



omit [DecidableEq ι] in
theorem algebraMap_trace_eq_sum_algHom_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_trace_eq_sum_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x

end Points

section Count

theorem etale_of_isReduced_of_perfectField (K S : Type*) [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Module.Finite K S] [IsReduced S] : Algebra.Etale K S := by
  have : IsArtinianRing S := .of_finite K S
  have (I : MaximalSpectrum S) : Algebra.FormallyEtale K (S ⧸ I.asIdeal) := by
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyEtale.of_isSeparable K (S ⧸ I.asIdeal)
  exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars K).symm,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]

theorem natCard_algHom_eq_finrank_of_etale_baseChange [Module.Free R S] [Module.Finite R S]
    [IsSepClosed L] [Algebra.FormallyEtale L (L ⊗[R] S)] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have := (algebraMap R L).domain_nontrivial
  have : IsArtinianRing (L ⊗[R] S) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[R] S))
  rw [Nat.card_congr (AlgHom.liftEquiv R L S L),
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[R] S)),
    ← Module.finrank_baseChange (R := L) (S := R) (M' := S),
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[R] S)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_algHom_eq_finrank_of_isReduced_baseChange [Module.Free R S] [Module.Finite R S]
    [IsAlgClosed L] [IsReduced (L ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have := etale_of_isReduced_of_perfectField L (L ⊗[R] S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L

end Count

section Etale

variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]


variable (S) in
theorem natCard_algHom_eq_finrank_of_etale : Nat.card (S →ₐ[K] L) = finrank K S :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  natCard_algHom_eq_finrank_of_etale_baseChange K S L


variable {K L} {ι : Type*} [Fintype ι]

end Etale

section Reduced

variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]

end Reduced

section Both

variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]

end Both

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfSheafPullback
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

noncomputable section

namespace GlobalTheory
namespace AffineVanishing

section Restriction

variable {X Y : TopCat.{u}} {j : Y ⟶ X} (hj : IsOpenEmbedding j)

lemma shortExact_map_sheafPullback {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) [(hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    (S.map (hj.sheafPullback AddCommGrpCat.{u})).ShortExact := by
  have h₁ : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} j) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map j) AddCommGrpCat.{u} _ _
  have h₂ : PreservesFiniteLimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (hj.sheafPullbackIso _)
  have h₃ : PreservesFiniteColimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteColimits_of_natIso (hj.sheafPullbackIso _)
  exact hS.map_of_exact _

lemma subsingleton_of_sheafPullback (V : Opens Y) (n : ℕ) (F : X.Sheaf AddCommGrpCat.{u})
    (h : Subsingleton (Sheaf.H'.{u} ((hj.sheafPullback AddCommGrpCat.{u}).obj F) (n + 1) V)) :
    Subsingleton (Sheaf.H'.{u} F (n + 1) (hj.functor.obj V)) := by
  haveI : (hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  induction n generalizing F with
  | zero =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    exact SheafLES.subsingleton₁_one_of_sections_surjective.{u} hS _
      (SheafLES.sections_surjective_of_subsingleton.{u} (shortExact_map_sheafPullback hj hS) V h)
      (Flasque.subsingleton_H'_of_isFlasque _ 0 _)
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    have hI : (Flasque.injectiveShortComplex F).X₂.IsFlasque := inferInstance
    have hI' : ((hj.sheafPullback AddCommGrpCat.{u}).obj
        (Flasque.injectiveShortComplex F).X₂).IsFlasque := ⟨fun _ ↦ hI.epi _⟩
    exact SheafLES.subsingleton₁.{u} hS (n + 1) _
      (ih _ (SheafLES.subsingleton₃.{u} (shortExact_map_sheafPullback hj hS) (n + 1) V
        (Flasque.subsingleton_H'_of_isFlasque _ (hF := hI') n V) h))
      (Flasque.subsingleton_H'_of_isFlasque _ (n + 1) _)

end Restriction

variable {X Y : Scheme.{u}}

lemma subsingleton_of_restrict (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules) (V : Y.Opens)
    (n : ℕ) (h : Subsingleton (cohOn (F.restrict j) V (n + 1))) :
    Subsingleton (cohOn F (j ''ᵁ V) (n + 1)) :=
  subsingleton_of_sheafPullback j.isOpenEmbedding V n ((toAbSheaf X).obj F) h

abbrev interModule (F : X.Modules) (W : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)

abbrev toInterModule (F : X.Modules) (W : X.Opens) : F ⟶ interModule F W :=
  (Scheme.Modules.restrictAdjunction W.ι).unit.app F

lemma map_toInterModule_eq_zero (F : X.Modules) (W V : X.Opens) (n : ℕ) (α : cohOn F V n)
    (h : SheafLES.map.{u} ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj F)) n V
      (cohOn.toH' F V n α) = 0) :
    cohOn.map ℤ (toInterModule F W) V n α = 0 :=
  haveI : IsIso ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj (interModule F W))) :=
    Kempf.isIso_toInter_app_pushforward (A := AddCommGrpCat.{u}) W.ι.base W (fun y ↦ y.2)
      ((toAbSheaf W.toScheme).obj (F.restrict W.ι))
  Kempf.map_eq_zero_of_map_toInter_eq_zero.{u} ((toAbSheaf X).map (toInterModule F W)) h

lemma mono_lift_toInterModule (F : X.Modules) {ι : Type u} [Finite ι] (W : ι → X.Opens)
    (hW : ⊤ ≤ iSup W) : Mono (Pi.lift fun i ↦ toInterModule F (W i)) := by
  refine ⟨fun {Z} a b hab ↦ ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover F (fun i ↦ (W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ U))
    (fun i ↦ (W i).ι.image_preimage_le U) (fun x hx ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hW (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨i, ⟨x, hi⟩, hx, rfl⟩
  · have h : a ≫ toInterModule F (W i) = b ≫ toInterModule F (W i) := by
      simpa using hab =≫ Pi.π _ i
    exact congr(($h).app U s)

lemma subsingleton_top [IsAffine X] (n : ℕ)
    (ih : ∀ q, 0 < q → q < n + 1 → ∀ (G : X.Modules) [G.IsQuasicoherent] (U : X.Opens),
      IsAffineOpen U → Subsingleton (cohOn G U q))
    (F : X.Modules) [F.IsQuasicoherent] : Subsingleton (cohOn F ⊤ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun α ↦ ?_
  obtain ⟨𝔘, h𝔘, hfin, hsup, h0⟩ := Kempf.exists_finite_cover_map_toInter_eq_zero.{u}
    (X := X) (𝔅 := X.affineOpens) X.isBasis_affineOpens
    (fun B hB B' hB' ↦ IsAffineOpen.inf hB hB') ((toAbSheaf X).obj F) ⊤
    (isAffineOpen_top X).isCompact (Nat.le_add_left 1 n)
    (fun q hq hqn B hB ↦ ih q hq hqn F B hB) (cohOn.toH' F ⊤ (n + 1) α)
  haveI : Finite 𝔘 := hfin
  haveI (W : 𝔘) : IsAffine W.1 := h𝔘 W.2
  let φ : F ⟶ ∏ᶜ (fun W : 𝔘 ↦ interModule F W.1) := Pi.lift fun W ↦ toInterModule F W.1
  haveI : Mono φ := mono_lift_toInterModule F (fun W : 𝔘 ↦ W.1) (by
    rw [← sSup_eq_iSup', hsup])
  have hα : cohOn.map ℤ φ ⊤ (n + 1) α = 0 := by
    apply (cohOn.piEquiv ℤ ⊤ (n + 1) _).injective
    ext W
    simp only [cohOn.piEquiv_apply, cohOn.map_map, map_zero, φ, Pi.lift_comp_π]
    exact map_toInterModule_eq_zero F W.1 ⊤ (n + 1) α (h0 W.1 W.2)
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_cokernel φ }
  have hT := SheafLES.shortExact_map_toAbSheaf hS
  have hinj : Function.Injective (SheafLES.map.{u} ((toAbSheaf X).map φ) (n + 1) ⊤) := by
    cases n with
    | zero =>
      exact SheafLES.map_f_one_injective_of_sections_surjective.{u} hT ⊤
        (QCoh.surjective_cokernel_π_app φ (isAffineOpen_top X))
    | succ n =>
      refine SheafLES.map_f_injective_of_surjective.{u} hT (n + 1) ⊤ fun y ↦ ⟨0, ?_⟩
      exact @Subsingleton.elim _ (ih (n + 1) n.succ_pos (by omega) (cokernel φ) ⊤
        (isAffineOpen_top X)) _ _
  exact (cohOn.toH' F ⊤ (n + 1)).injective (hinj (hα.trans (by
    rw [map_zero]; exact (map_zero _).symm)))

end AffineVanishing

open AffineVanishing

theorem cohOn.subsingleton_of_isAffineOpen {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (hn : 0 < n) : Subsingleton (cohOn F U n) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    haveI : IsAffine U := hU
    have h := subsingleton_of_restrict U.ι F ⊤ n
      (subsingleton_top n (fun q hq hqn G _ V hV ↦ ih q hqn G hV hq) (F.restrict U.ι))
    rwa [Scheme.Opens.ι_image_top] at h

theorem coh.subsingleton_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 0 < n) : Subsingleton (coh F n) :=
  cohOn.subsingleton_of_isAffineOpen F (isAffineOpen_top X) hn

instance coh.subsingleton_succ_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) : Subsingleton (coh F (n + 1)) :=
  coh.subsingleton_of_isAffine F n.succ_pos

end GlobalTheory
end
end
