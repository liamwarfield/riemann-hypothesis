module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbeddingHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartLocalAmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartSmooth
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PolynomialRingOverGlobalSections
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLift
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelectionCompatibility

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackGraphChart
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SumCoordinatePartialDerivatives
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def renameSumInl (k : Type u) [Field k] (M n : ℕ) :
    MvPolynomial (ULift.{u} (Fin M)) k →+* MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k :=
  (MvPolynomial.rename
      (fun a : ULift.{u} (Fin M) =>
        (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n)))).toRingHom

theorem renameSumInl_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    renameSumInl k M n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [renameSumInl]

theorem renameSumInl_X (k : Type u) [Field k] (M n : ℕ) (a : Fin M) :
    renameSumInl k M n (MvPolynomial.X (ULift.up a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) := by
  simp [renameSumInl]

private theorem pderiv_inr_X_inl (k : Type u) [Field k] (M n : ℕ) (i : Fin n) (a : Fin M) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) = 0 := by
  classical
  simp [MvPolynomial.pderiv_X]

theorem pderiv_inr_renameSumInl (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (renameSumInl k M n p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i c
    simp [renameSumInl_C]
  · rename_i q r hq hr
    simp [hq, hr]
  · rename_i q a hq
    obtain ⟨a⟩ := a
    rw [map_mul, renameSumInl_X, MvPolynomial.pderiv_mul, hq, pderiv_inr_X_inl]
    simp

private theorem projLeft_appTop_affineSpaceIndexedByToSpec_appTop (k : Type u) [Field k] (M n : ℕ)
    (y : Γ(Spec (CommRingCat.of k), ⊤)) :
    (projLeft k M n).appTop ((affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y) =
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
  have h2 : ((projLeft k M n) ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y
      = (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
    rw [projLeft_comp_affineSpaceIndexedByToSpec]
  exact h2

private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n)) (MvPolynomial.C c) := by
  rw [mvPolynomialEquivGlobalSections_C, mvPolynomialEquivGlobalSections_C, projLeft_appTop_affineSpaceIndexedByToSpec_appTop]

private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (M n : ℕ)
    (a : ULift.{u} (Fin M)) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n))) := by
  obtain ⟨a⟩ := a
  simp

theorem mvPolynomialEquivGlobalSections_symm_projLeft_appTop (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        ((projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) p)) =
      renameSumInl k M n p := by
  have key :
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          ((((projLeft k M n).appTop).hom).comp
            ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).toRingHom))
        = renameSumInl k M n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)))
          = renameSumInl k M n (MvPolynomial.C c)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_C, RingEquiv.symm_apply_apply, renameSumInl_C]
    · intro a
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)))
          = renameSumInl k M n (MvPolynomial.X a)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_X, RingEquiv.symm_apply_apply]
      simp [renameSumInl]
  exact RingHom.congr_fun key p

theorem mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) :
    ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp (mvPolynomialToSumCoordinateRing k M n) =
      MvPolynomial.eval₂Hom
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) := by
  apply MvPolynomial.ringHom_ext
  · intro t
    have h := mvPolynomialEquivGlobalSections_symm_projLeft_appTop k M n
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm t)
    simp only [RingEquiv.apply_symm_apply] at h
    simpa using h
  · intro i
    simp

theorem mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p) =
      MvPolynomial.eval₂
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) p :=
  RingHom.congr_fun (mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing k M n) p

private theorem pderiv_inr_eval₂_X_inr (k : Type u) [Field k] (M n : ℕ)
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) (i : Fin n)
    (hf : ∀ t, MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) (f t) = 0)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.eval₂ f
          (fun j : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) p) =
      MvPolynomial.eval₂ f
        (fun j : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)))
        (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i t
    rw [MvPolynomial.eval₂_C, MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero]
    exact hf t
  · rename_i q r hq hr
    simp [MvPolynomial.eval₂_add, hq, hr]
  · rename_i q j hq
    have hX : MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) =
        MvPolynomial.eval₂ f
          (fun l : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr l) : ULift.{u} (Fin M ⊕ Fin n)))
          (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
      by_cases h : i = j
      · subst h
        simp
      · simp [MvPolynomial.pderiv_X, h]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.eval₂_add, hq, hX]

theorem pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p)) =
      (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv i p)) := by
  rw [mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing]
  refine pderiv_inr_eval₂_X_inr k M n
    ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom)) i ?_ p
  intro t
  rw [RingHom.comp_apply]
  exact pderiv_inr_renameSumInl k M n i _

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffinePullbackPresentation
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffineLiftRelativeDimension
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLiftRelativeDimension
universe u

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

namespace StandardSmoothLift

section

variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)

theorem liftedSubmersivePresentation_dimension :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by
  have hu : Nat.card Unit = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
  have h1 : Nat.card (Unit ⊕ ι) = Nat.card ι + 1 := by
    rw [Nat.card_sum, hu]
    omega
  have h2 : Nat.card (Unit ⊕ σ) = Nat.card σ + 1 := by
    rw [Nat.card_sum, hu]
    omega
  show Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ
  rw [h1, h2]
  omega

end

end StandardSmoothLift

section

variable (S R B : Type u) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]

theorem exists_lift_of_isStandardSmoothOfRelativeDimension (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      Algebra.IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b' : B', e (1 ⊗ₜ[S] b') = f b' := by
  have hinst : Algebra.IsStandardSmoothOfRelativeDimension r R B := ‹_›
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ := hinst.out
  have : Finite ι := hι
  have : Finite σ := hσ
  refine ⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance,
    StandardSmoothLift.liftedAlgebraHom hsurj P, ?_,
    StandardSmoothLift.liftedAlgebraHom_surjective hsurj P,
    StandardSmoothLift.baseChangeEquiv hsurj P,
    StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩
  exact ⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance,
    StandardSmoothLift.liftedSubmersivePresentation hsurj P,
    (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P).trans hdim⟩⟩

end

end FunctorialResolution.EmbeddedResolution
end

universe u

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace SmoothChartRelativeDimension

private def tensorProductLiftRingHom {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) : (R ⊗[S] C) →+* T :=
  letI : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  letI : Algebra R T := a.toAlgebra
  haveI : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom S R T)
      ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T)).toRingHom

private theorem tensorProductLiftRingHom_tmul {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) (x : R) (y : C) :
    tensorProductLiftRingHom a b hab (x ⊗ₜ[S] y) = a x * b y := by
  let _ : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  let _ : Algebra R T := a.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.productMap_apply_tmul (IsScalarTower.toAlgHom S R T)
    ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T) x y

theorem exists_affineOpen_isStandardSmoothOfRelativeDimension {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V),
      RingHom.IsStandardSmoothOfRelativeDimension r
        (CommRingCat.Hom.hom ((V.ι ≫ h).appTop)) := by
  obtain ⟨U, hU, V, hV, hyV, e, hss⟩ := ‹AlgebraicGeometry.SmoothOfRelativeDimension r h›.1 y
  have hmemU : h.base y ∈ U := e hyV
  obtain ⟨f₀, hf₀le, hf₀mem⟩ :=
    (isAffineOpen_top X).exists_basicOpen_le (⟨h.base y, hmemU⟩ : ↥U) (by trivial)
  set g : Γ(X, U) :=
    (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) f₀ with hgdef
  set s : Γ(Y, V) := (ConcreteCategory.hom (h.appLE U V e)) g with hsdef
  have hsg : s = (CommRingCat.Hom.hom (h.appLE U V e)) g := rfl
  have hbg : X.basicOpen g = U ⊓ X.basicOpen f₀ :=
    Scheme.basicOpen_res X f₀ (homOfLE (le_top : U ≤ ⊤)).op
  have hbgf : X.basicOpen g = X.basicOpen f₀ := hbg.trans (inf_eq_right.mpr hf₀le)
  have hbs : Y.basicOpen s = V ⊓ h ⁻¹ᵁ X.basicOpen g :=
    Scheme.basicOpen_appLE h V U e g
  have hyW : y ∈ Y.basicOpen s := by
    rw [hbs]
    refine ⟨hyV, ?_⟩
    show h.base y ∈ X.basicOpen g
    rw [hbgf]
    exact hf₀mem
  have hWaff : IsAffineOpen (Y.basicOpen s) := hV.basicOpen s
  have hle₂ : Y.basicOpen s ≤ h ⁻¹ᵁ X.basicOpen g := by
    rw [hbs]; exact inf_le_right
  have hle₃ : Y.basicOpen s ≤ h ⁻¹ᵁ (⊤ : X.Opens) := by
    intro z hz; trivial
  have hbgU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hWV : Y.basicOpen s ≤ V := Y.basicOpen_le s
  have hmm : Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
      = Submonoid.powers s := by
    ext x
    constructor
    · rintro ⟨y', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow, hsg]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨g ^ n, ⟨n, rfl⟩, by rw [map_pow, hsg]⟩
  have hlocX : IsLocalization (Submonoid.powers g) (Γ(X, X.basicOpen g) : Type u) :=
    hU.isLocalization_basicOpen g
  have hlocY : IsLocalization
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g))
      (Γ(Y, Y.basicOpen s) : Type u) := by
    rw [hmm]
    exact hV.isLocalization_basicOpen s
  have hloc := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves r
    (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
    (Γ(X, X.basicOpen g) : Type u) (Γ(Y, Y.basicOpen s) : Type u) hss
  have hle_sub : Submonoid.powers g ≤ Submonoid.comap (CommRingCat.Hom.hom (h.appLE U V e))
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hloc2 : RingHom.IsStandardSmoothOfRelativeDimension r
      (IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub) := hloc
  have arrow : h.appLE U V e ≫ Y.presheaf.map (homOfLE hWV).op
      = X.presheaf.map (homOfLE hbgU).op ≫ h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have key : IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub
      = CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom arrow
  have hP : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)) := by
    rw [← key]
    exact hloc2
  let _ : Algebra (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u) :=
    (CommRingCat.Hom.hom
      (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op)).toAlgebra
  have : IsLocalization.Away f₀ (Γ(X, X.basicOpen g) : Type u) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen f₀
      (homOfLE (le_top : X.basicOpen g ≤ ⊤)) hbgf
  have hsrc :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway r).1
  have hcomp0 : RingHom.IsStandardSmoothOfRelativeDimension r
      ((CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)).comp
        (algebraMap (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u))) :=
    hsrc _ f₀ _ hP
  have hmap : X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op ≫
      h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ = h.appLE ⊤ (Y.basicOpen s) hle₃ :=
    Scheme.Hom.map_appLE h hle₂ (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op
  have hcomp : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE ⊤ (Y.basicOpen s) hle₃)) := by
    rw [← hmap, CommRingCat.hom_comp]
    exact hcomp0
  have hA : ((Y.basicOpen s).ι ''ᵁ ⊤) ≤ (⊤ : Y.Opens) := le_top
  have hBeq : ((Y.basicOpen s).ι ''ᵁ ⊤) = Y.basicOpen s := by simp
  have hB : Y.basicOpen s ≤ ((Y.basicOpen s).ι ''ᵁ ⊤) := le_of_eq hBeq.symm
  have hclean : h.appTop ≫ (Y.presheaf.map (homOfLE hA).op ≫ Y.presheaf.map (homOfLE hB).op)
      = h.appLE (⊤ : X.Opens) (Y.basicOpen s) hle₃ := by
    rw [← Functor.map_comp]
    rfl
  have hiso : ((Y.basicOpen s).ι ≫ h).appTop ≫ (Y.basicOpen s).topIso.hom
      = h.appLE ⊤ (Y.basicOpen s) hle₃ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
    exact hclean
  have hgoal : ((Y.basicOpen s).ι ≫ h).appTop
      = h.appLE ⊤ (Y.basicOpen s) hle₃ ≫ (Y.basicOpen s).topIso.inv :=
    (Iso.eq_comp_inv _).mpr hiso
  refine ⟨Y.basicOpen s, hyW, hWaff, ?_⟩
  rw [hgoal]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := r)).1 _
    (Y.basicOpen s).topIso.symm.commRingCatIsoToRingEquiv hcomp

theorem exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension {S R B : CommRingCat.{u}}
    (ι : S ⟶ R) (hι : Function.Surjective ⇑(CommRingCat.Hom.hom ι)) (φ : R ⟶ B) (r : ℕ)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom φ)) :
    ∃ (B' : CommRingCat.{u}) (σ : S ⟶ B') (ψ : B' ⟶ B),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        Function.Surjective ⇑(CommRingCat.Hom.hom ψ) ∧
        CategoryTheory.IsPushout ι σ φ ψ := by
  let _ : Algebra (S : Type u) (R : Type u) := (CommRingCat.Hom.hom ι).toAlgebra
  let _ : Algebra (R : Type u) (B : Type u) := (CommRingCat.Hom.hom φ).toAlgebra
  let _ : Algebra (S : Type u) (B : Type u) :=
    ((CommRingCat.Hom.hom φ).comp (CommRingCat.Hom.hom ι)).toAlgebra
  have : IsScalarTower (S : Type u) (R : Type u) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension r (R : Type u) (B : Type u) := hφ
  obtain ⟨C, hCring, hCalg, f, hss, hfs, e, he⟩ :=
    FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension (S : Type u) (R : Type u)
      (B : Type u) r hι
  have : Algebra.IsStandardSmoothOfRelativeDimension r (S : Type u) C := hss
  have hcond : ι ≫ φ = CommRingCat.ofHom (algebraMap (S : Type u) C) ≫
      CommRingCat.ofHom f.toRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
    exact (f.commutes s).symm
  have hcc : ∀ (c : CategoryTheory.Limits.PushoutCocone ι
        (CommRingCat.ofHom (algebraMap (S : Type u) C))) (s : (S : Type u)),
      (CommRingCat.Hom.hom c.inl) (algebraMap (S : Type u) (R : Type u) s)
        = (CommRingCat.Hom.hom c.inr) (algebraMap (S : Type u) C s) := fun c s =>
    congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) c.condition
  have facR : ∀ c : CategoryTheory.Limits.PushoutCocone ι
      (CommRingCat.ofHom (algebraMap (S : Type u) C)),
      CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom) = c.inr := by
    intro c
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    show tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)
        (e.symm (f z)) = (CommRingCat.Hom.hom c.inr) z
    rw [show e.symm (f z) = (1 : (R : Type u)) ⊗ₜ[(S : Type u)] z from
      e.symm_apply_eq.mpr (he z).symm, tensorProductLiftRingHom_tmul, map_one, one_mul]
  refine ⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap (S : Type u) C),
    CommRingCat.ofHom f.toRingHom, ?_, ?_, ?_⟩
  · exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap r).mpr hss
  · exact hfs
  · refine CategoryTheory.IsPushout.of_isColimit' ⟨hcond⟩
      (CategoryTheory.Limits.PushoutCocone.IsColimit.mk hcond
        (fun c => CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) ?_ facR ?_)
    · intro c
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      obtain ⟨s, rfl⟩ := hι x
      have key : ι ≫ (φ ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) = ι ≫ c.inl := by
        rw [← Category.assoc, hcond, Category.assoc, facR c, ← c.condition]
      exact congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) key
    · intro c m h₁ h₂
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨z, rfl⟩ := hfs b
      exact congrArg (fun t : CommRingCat.of C ⟶ c.pt => (CommRingCat.Hom.hom t) z)
        (h₂.trans (facR c).symm)

end SmoothChartRelativeDimension

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace PresentedSmoothChart

theorem smooth_specMap_comp_isoSpec_inv {A : Scheme.{u}} [AlgebraicGeometry.IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B')
    (hσ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom σ)) :
    AlgebraicGeometry.Smooth (Spec.map σ ≫ A.isoSpec.inv) := by
  have hs : RingHom.Smooth (CommRingCat.Hom.hom σ) := by
    let := (CommRingCat.Hom.hom σ).toAlgebra
    have : Algebra.IsStandardSmooth ↥Γ(A, ⊤) ↥B' := hσ
    exact ⟨inferInstance, inferInstance⟩
  have h1 : AlgebraicGeometry.Smooth (Spec.map σ) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr hs
  have h2 : AlgebraicGeometry.Smooth A.isoSpec.inv := inferInstance
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) _ _ h1 h2

theorem exists_affineOpen_isPullback_specMap {A X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine A] [AlgebraicGeometry.IsAffine X]
    (i : X ⟶ A) [AlgebraicGeometry.IsClosedImmersion i] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V) (B' : CommRingCat.{u})
      (σ : Γ(A, ⊤) ⟶ B') (j : (V : Scheme.{u}) ⟶ Spec B'),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        AlgebraicGeometry.IsClosedImmersion j ∧
        CategoryTheory.IsPullback j (V.ι ≫ h) (Spec.map σ ≫ A.isoSpec.inv) i := by
  obtain ⟨V, hyV, hV, hsm⟩ :=
    SmoothChartRelativeDimension.exists_affineOpen_isStandardSmoothOfRelativeDimension r h y
  have : AlgebraicGeometry.IsAffine (V : Scheme.{u}) := hV
  obtain ⟨B', σ, ψ, hσ, hψ, hpo⟩ :=
    SmoothChartRelativeDimension.exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension
      (Scheme.Hom.appTop i)
      (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2
      (Scheme.Hom.appTop (V.ι ≫ h)) r hsm
  have S1 : CategoryTheory.IsPullback (Spec.map ψ)
      (Spec.map (Scheme.Hom.appTop (V.ι ≫ h))) (Spec.map σ)
      (Spec.map (Scheme.Hom.appTop i)) := hpo.op.map Scheme.Spec
  have L : CategoryTheory.IsPullback (V : Scheme.{u}).isoSpec.hom (V.ι ≫ h)
      (Spec.map (Scheme.Hom.appTop (V.ι ≫ h))) X.isoSpec.hom :=
    CategoryTheory.IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality (V.ι ≫ h)⟩
  have C1 := L.paste_horiz S1
  rw [Scheme.isoSpec_hom_naturality i] at C1
  refine ⟨V, hyV, hV, B', σ, (V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ, hσ, ?_, ?_⟩
  · have := AlgebraicGeometry.IsClosedImmersion.spec_of_surjective ψ hψ
    infer_instance
  · have t : CategoryTheory.IsPullback (𝟙 (Spec B')) (Spec.map σ ≫ A.isoSpec.inv)
        (Spec.map σ) A.isoSpec.hom :=
      CategoryTheory.IsPullback.of_horiz_isIso ⟨by simp⟩
    have p : ((V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ) ≫ (Spec.map σ ≫ A.isoSpec.inv)
        = (V.ι ≫ h) ≫ i := by
      rw [← Category.assoc, C1.w]
      simp
    have s : CategoryTheory.IsPullback
        (((V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ) ≫ 𝟙 (Spec B')) (V.ι ≫ h)
        (Spec.map σ) (i ≫ A.isoSpec.hom) := by
      rw [Category.comp_id]
      exact C1
    exact CategoryTheory.IsPullback.of_right s p t

end PresentedSmoothChart

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem jacobianDetSection_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n q : ℕ)
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (s : Fin q → Fin n) :
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      mvPolynomialToSumCoordinateRing k M n
        (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j))) := by
  have key : ∀ i j : Fin q,
      jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s i j =
        (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm
          (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv (s i) (lift j))) := by
    intro i j
    have h0 : polynomialOfSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) j
        = (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n (lift j)) := rfl
    rw [jacobianMatrixOfSections_apply, h0]
    exact pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing k M n (s i) (lift j)
  have hmat : jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      ((((mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          (mvPolynomialToSumCoordinateRing k M n)).mapMatrix)
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact key i j
  show mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s).det = _
  rw [hmat, ← RingHom.map_det]
  simp

theorem appTop_specToAffineSpaceExtendCoords_jacobianDetSection (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n q : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j)
    (s : Fin q → Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s) =
      (Scheme.ΓSpecIso B').inv
        (Matrix.det (Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ σ.hom b ((MvPolynomial.pderiv (s i)) (rel j)))) := by
  have hmap : ∀ i j : Fin q,
      (MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e)))
          (MvPolynomial.pderiv (s i) (lift j)) = MvPolynomial.pderiv (s i) (rel j) := by
    intro i j
    rw [← MvPolynomial.pderiv_map, hlift j]
  have hM1 : ((MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e))).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)))
      = Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j) := by
    refine Matrix.ext fun i j => ?_
    simpa [RingHom.mapMatrix_apply] using hmap i j
  have hM2 : ((MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j)))
      = Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom σ) b (MvPolynomial.pderiv (s i) (rel j)) := by
    refine Matrix.ext fun i j => ?_
    simp [RingHom.mapMatrix_apply]
  rw [jacobianDetSection_mvPolynomialToSumCoordinateRing k M n q lift s,
    specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b he]
  congr 1
  rw [RingHom.map_det, hM1]
  show (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b)
      (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j))) = _
  rw [RingHom.map_det, hM2]

theorem smoothPullbackHasGraphChart : SmoothPullbackHasGraphChart.{u} := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ _ M ρ _ hρ r h _ _ y
  have : IsAffine X := isAffine_of_isAffineHom (f := i)
  obtain ⟨V, hyV, hVaff, B', τ, jV, hτ, hjV, hpb⟩ :=
    PresentedSmoothChart.exists_affineOpen_isPullback_specMap i r h y
  have := hjV
  let _ : Algebra Γ(A, ⊤) B' := (CommRingCat.Hom.hom τ).toAlgebra
  have halg : (algebraMap Γ(A, ⊤) B') = CommRingCat.Hom.hom τ := rfl
  obtain ⟨⟨ι, κ, hκ, hι, P, hPdim⟩⟩ := hτ
  have := hι
  have := hκ
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  have hA : Algebra.IsStandardSmooth Γ(A, ⊤) B' := ⟨⟨ι, κ, hκ, hι, ⟨P⟩⟩⟩
  have hss : RingHom.IsStandardSmooth (CommRingCat.Hom.hom τ) := hA
  have hgsmooth : Smooth (specHomOfGlobalSections A τ) :=
    PresentedSmoothChart.smooth_specMap_comp_isoSpec_inv τ hss
  have := hgsmooth
  obtain ⟨n, ev, hn⟩ : ∃ (n : ℕ) (_ : ι ≃ Fin n), Nat.card ι = n :=
    ⟨_, Finite.equivFin ι, rfl⟩
  obtain ⟨q, er, hq⟩ : ∃ (q : ℕ) (_ : κ ≃ Fin q), Nat.card κ = q :=
    ⟨_, Finite.equivFin κ, rfl⟩
  have hdim' : Nat.card ι - Nat.card κ = r := hPdim
  have hle : Nat.card κ ≤ Nat.card ι := Nat.card_le_card_of_injective P.map P.map_inj
  have hnq : n = q + r := by omega
  obtain ⟨b, hb⟩ : ∃ b : Fin n → B', b = fun t => P.val (ev.symm t) := ⟨_, rfl⟩
  obtain ⟨rel, hrel_def⟩ : ∃ rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤),
      rel = fun j => MvPolynomial.rename ⇑ev (P.relation (er.symm j)) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : Fin q → Fin n, s = fun j => ev (P.map (er.symm j)) := ⟨_, rfl⟩
  have hsinj : Function.Injective s := by
    intro a₁ a₂ hab
    simp only [hs_def] at hab
    exact er.symm.injective (P.map_inj (ev.injective hab))
  have hbev : (b ∘ ⇑ev) = P.val := by
    funext x
    simp [hb]
  have hvb : (P.val ∘ ⇑ev.symm) = b := by
    funext t
    simp [hb]
  have heval : ∀ p : MvPolynomial ι Γ(A, ⊤),
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b (MvPolynomial.rename ⇑ev p) =
        MvPolynomial.aeval P.val p := by
    intro p
    rw [MvPolynomial.eval₂_rename, hbev, MvPolynomial.aeval_def, halg]
  have hE : ∀ x : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.aeval P.val (MvPolynomial.rename ⇑ev.symm x) =
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b x := by
    intro x
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_rename, hvb, halg]
  have hkerP : ∀ x : MvPolynomial ι Γ(A, ⊤),
      MvPolynomial.aeval P.val x = 0 ↔ x ∈ Ideal.span (Set.range P.relation) := by
    intro x
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    simp [RingHom.mem_ker]
  have hrel0 : ∀ j : κ, MvPolynomial.aeval P.val (P.relation j) = 0 := fun j =>
    (hkerP _).mpr (Ideal.subset_span ⟨j, rfl⟩)
  have hsub : Ideal.map (MvPolynomial.rename ⇑ev) (Ideal.span (Set.range P.relation))
      ≤ Ideal.span (Set.range rel) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro z ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span ⟨er j, by simp [hrel_def]⟩
  have hker : RingHom.ker (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom τ) b) =
      Ideal.span (Set.range rel) := by
    apply le_antisymm
    · intro x hx
      have hx' : MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b x = 0 := by
        simpa [RingHom.mem_ker] using hx
      have h1 : MvPolynomial.rename ⇑ev.symm x ∈ Ideal.span (Set.range P.relation) :=
        (hkerP _).mp (by rw [hE x]; exact hx')
      have h2 := hsub (Ideal.mem_map_of_mem _ h1)
      rw [MvPolynomial.rename_rename, Equiv.self_comp_symm] at h2
      simpa using h2
    · rw [Ideal.span_le]
      rintro z ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hrel_def]
      rw [heval]
      exact hrel0 _
  have hjacEntry : ∀ i₀ j₀ : Fin q,
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b (MvPolynomial.pderiv (s i₀) (rel j₀)) =
        MvPolynomial.aeval P.val (P.jacobiMatrix (er.symm i₀) (er.symm j₀)) := by
    intro i₀ j₀
    simp only [hs_def, hrel_def]
    rw [MvPolynomial.pderiv_rename (f := ⇑ev) ev.injective, heval, P.jacobiMatrix_apply]
  have hj := P.jacobian_eq_jacobiMatrix_det
  have hdet : (Matrix.of fun i₀ j₀ : Fin q =>
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
          (MvPolynomial.pderiv (s i₀) (rel j₀))).det = P.jacobian := by
    have h1 : (Matrix.of fun i₀ j₀ : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
            (MvPolynomial.pderiv (s i₀) (rel j₀)))
        = (P.jacobiMatrix.map ⇑(MvPolynomial.aeval P.val).toRingHom).submatrix
            ⇑er.symm ⇑er.symm := by
      refine Matrix.ext fun i₀ j₀ => ?_
      simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact hjacEntry i₀ j₀
    rw [h1, Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa [Algebra.Generators.algebraMap_apply] using hj.symm
  have hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b p = x := by
    intro x
    refine ⟨MvPolynomial.rename ⇑ev (P.σ x), ?_⟩
    rw [heval]
    exact P.aeval_val_σ x
  choose lift hliftmap using fun j : Fin q => exists_mvPolynomial_map_appTop_eq k A M ρ n q rel j
  have hΔ : IsUnit ((specToAffineSpaceExtendCoords k A pA M ρ τ n b).appTop
      (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s)) := by
    rw [appTop_specToAffineSpaceExtendCoords_jacobianDetSection k A pA M ρ τ n q b hρ rel lift hliftmap s]
    have h2 : IsUnit ((Matrix.of fun i₀ j₀ : Fin q =>
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
          ((MvPolynomial.pderiv (s i₀)) (rel j₀))).det) := by
      rw [hdet]
      exact P.jacobian_isUnit
    exact h2.map ((Scheme.ΓSpecIso B').inv).hom
  have hpA'Sm : Smooth (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  have hpA'ft : LocallyOfFiniteType (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  have hpA'qc : QuasiCompact (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  refine ⟨V, hyV, hVaff, Spec B', specHomOfGlobalSections A τ ≫ pA, inferInstance, hpA'Sm,
    hpA'ft, hpA'qc, specHomOfGlobalSections A τ, hgsmooth, rfl, jV, hjV, hpb, n, q, hnq,
    specToAffineSpaceExtendCoords k A pA M ρ τ n b, ?_, ?_, (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)),
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s, ?_, ?_, ?_⟩
  · exact isClosedImmersion_specToAffineSpaceExtendCoords k A pA M ρ τ n b hρ hgen
  · exact specToAffineSpaceExtendCoords_comp_projLeft k A pA M ρ τ n b hρ
  · exact ker_specToAffineSpaceExtendCoords_appTop k A pA M ρ τ n b hρ q rel hker lift hliftmap
  · exact preimage_basicOpen_specToAffineSpaceExtendCoords k A pA M ρ τ n b _ hΔ
  · exact smooth_graphMorphismToAffineSpace_basicOpen k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s hsinj

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    SmoothPullbackHasLocalAmbientEmbedding.{u} :=
  smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart hsm smoothPullbackHasGraphChart

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithOpenImmersions_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithOpenImmersions ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithEtaleCovers_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithEtaleCovers ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithFieldBaseChange (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithFieldBaseChange_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithFieldBaseChange A hAlg hw) nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithFieldBaseChange ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k V pV)
      (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y pY) := by
  have key := isPullbackBlowupSequence_presentedSelection_of_smooth (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw)
    (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
    k Y V pY pV u r hu
  rw [← toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex,
    EmbeddedResolutionRule.toAffineResolutionRule_apply, EmbeddedResolutionRule.toAffineResolutionRule_apply]
  exact key

end FunctorialResolution.EmbeddedResolution
