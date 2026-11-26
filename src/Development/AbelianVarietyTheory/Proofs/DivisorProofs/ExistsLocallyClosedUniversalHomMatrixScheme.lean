module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZeroSectionValueInPowerFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinati
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem topS_hom_ext {Rg : Type} [CommRing Rg] {Y : Over (Sp Rg)} (u v : Y ⟶ topS Rg) : u = v := by
  have hm : Mono (topS Rg).hom := by
    change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w u, Over.w v]

instance isIso_snd_left {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) :
    IsIso (snd (topS Rg) A).left := by
  have : IsIso (snd (topS Rg) A) := by
    refine ⟨⟨lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A), ?_, ?_⟩⟩
    · refine CartesianMonoidalCategory.hom_ext _ _ (topS_hom_ext _ _) ?_
      simp
    · simp
  exact (Over.forget _).map_isIso (snd (topS Rg) A)

theorem fA_flat_isProjBy_universallyClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  intro Rg _ A _ L hA hL hamp
  have hsq : IsPullback (snd (topS Rg) A).left (fA A) A.hom (𝟙 (Sp Rg)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w (snd (topS Rg) A)⟩
  obtain ⟨hproj, hsm, hpr, -⟩ :=
    GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp Rg) A L hA hL hamp Rg (𝟙 _) _ _ (fA A) hsq
  exact ⟨inferInstance, hproj, inferInstance⟩

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  first | (exact @GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (exact GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (intros; apply GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixPoint

theorem exists_affine_hom (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg)
    (x : Fin n → Γ(T, ⊤)) :
    ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  let φ : MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom) x
  have key : ∀ p, (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv p) = φ p := by
    intro p
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop]
    simp
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · apply ext_of_isAffine
    refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of Rg)) _ _).1 ?_
    ext r
    have n2 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n2, key]
    simp [φ]
  · intro i
    unfold coord
    rw [key]
    simp [φ]

end GlobalTheory.HomFixPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineSpace_morphism_of_coordinates : ∀ (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg) (x : Fin n → Γ(T, ⊤)), ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  first | (exact @GlobalTheory.HomFixPoint.exists_affine_hom) | (exact GlobalTheory.HomFixPoint.exists_affine_hom) | (intros; apply GlobalTheory.HomFixPoint.exists_affine_hom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubscheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem factors_quot_iff {P : Type} [CommRing P] (I : Ideal P) (T : Scheme.{0}) (g : T ⟶ Sp P) :
    (∃ w : T ⟶ Sp (P ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ x hx
    have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of (P ⧸ I))).inv (Ideal.Quotient.mk I x) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of P ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ g.appTop
    let ψ : CommRingCat.of (P ⧸ I) ⟶ Γ(T, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom (fun x hx => h x hx))
    refine ⟨T.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have e : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ = φ := by ext x; rfl
    rw [Category.assoc, ← Spec.map_comp, e]
    simp only [φ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

def normEq {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (j : Fin mB) : MvPolynomial (Fin (mA * mB)) Rg :=
  MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (β j)) -
    ∑ i, MvPolynomial.X (finProdFinEquiv (i, j)) *
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (α i))

theorem appTop_affπ {Rg : Type} [CommRing Rg] {N : ℕ} (a : Γ(Sp Rg, ⊤)) :
    (affπ Rg N).appTop a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv
      (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom a)) := by
  conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of Rg)).hom_inv_id_apply a]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl

theorem normal_iff {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔
      ∀ j, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (normEq α β j)) = 0 := by
  refine forall_congr' fun j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [normEq, map_sub, map_sub, sub_eq_zero, map_sum, map_sum]
  simp only [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affπ, matOf, coord]

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem normal_closed : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ mA mB α β
  let I : Ideal (MvPolynomial (Fin (mA * mB)) Rg) := Ideal.span (Set.range (normEq α β))
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ I), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, fun T g => ?_⟩
  rw [factors_quot_iff, normal_iff]
  let φ : MvPolynomial (Fin (mA * mB)) Rg →+* Γ(T, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv.hom
  change (∀ j, φ (normEq α β j) = 0) ↔ ∀ x ∈ I, φ x = 0
  constructor
  · intro h x hx
    have hle : I ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    exact hle hx
  · intro h j
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubschemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearNormalisation_closed_subscheme : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.HomFixUniv.normal_closed) | (exact GlobalTheory.HomFixUniv.normal_closed) | (intros; apply GlobalTheory.HomFixUniv.normal_closed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem hom_to_topS_eq {Rg : Type} [CommRing Rg] {Z : Over (Sp Rg)} (f g : Z ⟶ topS Rg) : f = g := by
  haveI : IsIso (topS Rg).hom := by
    show IsIso ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id, ← Scheme.topIso_hom]
    infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w f, Over.w g]

def θOver {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A ⟶ topS Rg ⊗ A :=
  lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)

theorem θOver_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θOver A) := by
  refine ⟨⟨snd (topS Rg) A, ?_, ?_⟩⟩
  · rw [θOver, lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, θOver, lift_fst, Category.id_comp]
      exact hom_to_topS_eq _ _
    · rw [Category.assoc, θOver, lift_snd, Category.comp_id, Category.id_comp]

theorem θ_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θ A) := by
  haveI := θOver_isIso A
  have : θ A = (Over.forget _).map (θOver A) := rfl
  rw [this]
  exact (Over.forget _).map_isIso (θOver A)

theorem θ_fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ fA A = A.hom :=
  Over.w (θOver A)

theorem θ_pullback (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left)
    (p : X' ⟶ T) (t : T ⟶ Sp Rg) :
    (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
      GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  haveI := θ_isIso A
  refine ⟨fun h => ?_, θ_fA A, inferInstance⟩
  refine IsPullback.of_iso h (Iso.refl _) (asIso (θ A)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact (θ_fA A).symm
  · simp

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left) (p : X' ⟶ T) (t : T ⟶ Sp Rg), (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧ GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  first | (exact @GlobalTheory.HomFixUniv.θ_pullback) | (exact GlobalTheory.HomFixUniv.θ_pullback) | (intros; apply GlobalTheory.HomFixUniv.θ_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixOpen

variable {A₀ X T : Scheme.{0}} {N : LB A₀} {mA mB : ℕ}

theorem isUnit_comb_chart (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (z : X) {q q' : N.ι} (hq : φ z ∈ N.U q) (hq' : φ z ∈ N.U q') (j : Fin mB) :
    IsUnit (comb a φ p c z q j) ↔ IsUnit (comb a φ p c z q' j) := by
  have e : comb a φ p c z q j = (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    simp only [comb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_compat (a i) φ z hq hq', mul_left_comm]
  rw [e, Units.isUnit_units_mul]

theorem comb_comp {Y : Scheme.{0}} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (h : Y ⟶ X) (y : Y) (q : N.ι) (hq : φ (h y) ∈ N.U q) (j : Fin mB) :
    comb a (h ≫ φ) (h ≫ p) c y q j = (h.stalkMap y).hom (comb a φ p c (h y) q j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp h p y ⊤ trivial, gs_comp h φ y (N.U q) hq]

theorem gs_top {Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : X) (c : Γ(Z, ⊤)) :
    gs f z ⊤ (g.appTop.hom c) = gs (f ≫ g) z ⊤ c :=
  gs_pull f g z ⊤ trivial c

theorem gs_sum' {Y : Scheme.{0}} (f : X ⟶ Y) (z : X) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (b : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, b i) = ∑ i, gs f z U (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f z U h, map_sum]

def good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Set X :=
  {z | ∃ q, φ z ∈ N.U q ∧ ∃ j, IsUnit (comb a φ p c z q j)}

def combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) : Γ(X, φ ⁻¹ᵁ N.U q) :=
  ∑ i, (X.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom (c i j)) * (φ.app (N.U q)).hom ((a i).f q)

theorem gs_combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) (z : X) (hz : φ z ∈ N.U q) : gs (𝟙 X) z _ (combFn a φ p c q j) = comb a φ p c z q j := by
  have hz' : (𝟙 X) z ∈ φ ⁻¹ᵁ N.U q := hz
  rw [combFn, gs_sum' (𝟙 X) z _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hz', gs_res _ z le_top hz', gs_top, gs_pull (𝟙 X) φ z (N.U q) hz, Category.id_comp,
    Category.id_comp]

theorem isOpen_good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) :
    IsOpen (good a φ p c) := by
  have e : good a φ p c = ⋃ q, ⋃ j, (X.basicOpen (combFn a φ p c q j) : Set X) := by
    ext z
    simp only [good, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, j, hu⟩
      refine ⟨q, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq] at hu
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).1 hu
    · rintro ⟨q, j, hz⟩
      have hq : φ z ∈ N.U q := X.basicOpen_le _ hz
      refine ⟨q, hq, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq]
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).2 hz
  rw [e]
  exact isOpen_iUnion fun q => isOpen_iUnion fun j => (X.basicOpen _).isOpen

end GlobalTheory.HomFixOpen

namespace GlobalTheory.HomFixOpen

theorem main : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  intro Rg _ A₀ f _ N mA mB a hN
  let π₁ := pullback.fst f (affπ Rg (mA * mB))
  let π₂ := pullback.snd f (affπ Rg (mA * mB))
  let G := good a π₁ π₂ (matOf (𝟙 (Sp (MvPolynomial (Fin (mA * mB)) Rg))))
  have hG : IsOpen G := isOpen_good _ _ _ _
  have hC : IsClosed (π₂ '' Gᶜ) := π₂.isClosedMap _ hG.isClosed_compl
  refine ⟨⟨(π₂ '' Gᶜ)ᶜ, hC.isOpen_compl⟩, fun T X' g φ p hP => ?_⟩
  have w : φ ≫ f = (p ≫ g) ≫ affπ Rg (mA * mB) := by rw [Category.assoc]; exact hP.w
  let h := pullback.lift φ (p ≫ g) w
  have h1 : h ≫ π₁ = φ := pullback.lift_fst _ _ _
  have h2 : h ≫ π₂ = p ≫ g := pullback.lift_snd _ _ _
  have hπ₁ : ∀ z, π₁ (h z) = φ z := fun z => by rw [← Scheme.Hom.comp_apply, h1]
  have key : ∀ z q j, φ z ∈ N.U q → comb a φ p (matOf g) z q j =
      (h.stalkMap z).hom (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j) := by
    intro z q j hq
    rw [← comb_comp a π₁ π₂ _ h z q (by rw [hπ₁]; exact hq) j]
    simp only [comb, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [h2, matOf, matOf, coord, coord, gs_top, gs_top, Category.comp_id]
  have unitIff : ∀ z q j, φ z ∈ N.U q → (IsUnit (comb a φ p (matOf g) z q j) ↔
      IsUnit (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j)) := by
    intro z q j hq; rw [key z q j hq]; exact isUnit_map_iff _ _
  have stepA : Generates a φ p (matOf g) ↔ ∀ z, h z ∈ G := by
    constructor
    · intro hg z
      obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hN (φ z)
      obtain ⟨j, hj⟩ := hg z q hq
      exact ⟨q, by rw [hπ₁]; exact hq, j, (unitIff z q j hq).1 hj⟩
    · intro hg z q hq
      obtain ⟨q', hq', j, hj⟩ := hg z
      exact ⟨j, (unitIff z q j hq).2 ((isUnit_comb_chart a π₁ π₂ _ (h z) hq' (by rw [hπ₁]; exact hq) j).1 hj)⟩
  rw [stepA]
  have hP' : IsPullback h p π₂ g := IsPullback.of_right (by rw [h1]; exact hP) h2 (IsPullback.of_hasPullback _ _)
  constructor
  · intro hg τ
    show g τ ∈ (π₂ '' Gᶜ)ᶜ
    rintro ⟨w', hw, he⟩
    obtain ⟨y, hy1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π₂) (g := g) w' τ he
    apply hw
    have e : h (hP'.isoPullback.inv y) = w' := by
      rw [← Scheme.Hom.comp_apply, hP'.isoPullback_inv_fst, hy1]
    rw [← e]; exact hg _
  · intro hg z
    by_contra hz
    exact hg (p z) ⟨h z, hz, by rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]⟩

end GlobalTheory.HomFixOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_generatingCombinationMatrixLocus : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  first | (exact @GlobalTheory.HomFixOpen.main) | (exact GlobalTheory.HomFixOpen.main) | (intros; apply GlobalTheory.HomFixOpen.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImmersedClosedOpenIntersection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImmersedClosedOpenIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixMat.exists_immersed_locus : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  intro Y _ Z₁ Z₂ ι₁ ι₂ U h₁ h₂
  let p : pullback ι₁ ι₂ ⟶ Y := pullback.fst ι₁ ι₂ ≫ ι₁
  let V : (pullback ι₁ ι₂).Opens := p ⁻¹ᵁ U
  let j : V.toScheme ⟶ Y := V.ι ≫ p
  have hj : IsImmersion j := IsImmersion.comp _ _
  have hW : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian j
  have hN : TopologicalSpace.NoetherianSpace V.toScheme :=
    (IsPreimmersion.isEmbedding j).isInducing.noetherianSpace
  refine ⟨V.toScheme, j, hj, quasiCompact_of_noetherianSpace_source j, hW, ?_⟩
  intro T g
  constructor
  · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, hU⟩
    let f : T ⟶ pullback ι₁ ι₂ := pullback.lift w₁ w₂ (hw₁.trans hw₂.symm)
    have hf : f ≫ p = g := by
      simp only [f, p]; rw [← Category.assoc, pullback.lift_fst]; exact hw₁
    have hr : Set.range f ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      show p (f τ) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact hU τ
    refine ⟨IsOpenImmersion.lift V.ι f hr, ?_⟩
    simp only [j, ← Category.assoc, IsOpenImmersion.lift_fac, hf]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨w ≫ V.ι ≫ pullback.fst ι₁ ι₂, by simp [j, p]⟩,
      ⟨w ≫ V.ι ≫ pullback.snd ι₁ ι₂, by simp [j, p, pullback.condition]⟩, ?_⟩
    intro τ
    have : V.ι (w τ) ∈ V := by
      have h := Scheme.Opens.range_ι V
      exact (Set.ext_iff.mp h (V.ι (w τ))).mp ⟨_, rfl⟩
    exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImmersedClosedOpenIntersectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_immersed_closed_open_intersection : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  first | (exact @GlobalTheory.HomFixMat.exists_immersed_locus) | (exact GlobalTheory.HomFixMat.exists_immersed_locus) | (intros; apply GlobalTheory.HomFixMat.exists_immersed_locus  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixMatCond

theorem eq_θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Y : Scheme.{0}} (φ : Y ⟶ A.left)
    (ψ : Y ⟶ (topS Rg ⊗ A).left) (h : ψ ≫ (snd (topS Rg) A).left = φ) : ψ = φ ≫ θ A := by
  let Y0 : Over (Sp Rg) := Over.mk (φ ≫ A.hom)
  have w1 : ψ ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [← h, Category.assoc, Over.w (snd (topS Rg) A)]
  have w2 : (φ ≫ θ A) ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [Category.assoc, ← Over.w (snd (topS Rg) A), ← Category.assoc (θ A), θ_snd, Category.id_comp]
  let u : Y0 ⟶ topS Rg ⊗ A := Over.homMk ψ w1
  let v : Y0 ⟶ topS Rg ⊗ A := Over.homMk (φ ≫ θ A) w2
  have : u = v := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      haveI : Mono (topS Rg).hom := by dsimp [topS, overRes]; infer_instance
      rw [← cancel_mono (topS Rg).hom]
      simp only [Over.comp_left, Category.assoc, Over.w]
      try exact w1.trans w2.symm
    · ext
      simp only [Over.comp_left, u, v, Over.homMk_left, Category.assoc, θ_snd, Category.comp_id, h]
  exact congrArg CommaMorphism.left this

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ}
    (a : Fin n → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (t z) ∈ U)
    (f : Γ(X, U)) : gs (t ≫ g) z U f = (t.stalkMap z).hom (gs g (t z) U f) := by
  rw [← gs_pull t g z U h, gs_stalkMap t z _ h, gs_pull (𝟙 _) g (t z) U h, Category.id_comp]

theorem gs_appTop' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (a : Γ(X, ⊤)) :
    gs (𝟙 Y) y ⊤ (f.appTop.hom a) = gs f y ⊤ a :=
  (gs_pull (𝟙 _) f y ⊤ trivial a).trans (by rw [Category.id_comp])

theorem mem_wchart_one {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (j : Fin 1 → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : Fin 1 => m) j ↔ m y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem mem_wchart_unit {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (q : L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : PUnit => m) (fun _ => q) ↔ m y ∈ L.U q :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem app_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) :
    g (f x) = h x := by
  rw [← e]; rfl

theorem mem_wchart_comp {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (g : Y ⟶ X) (j : Fin 1 → L.ι) (z : Z)
    (h : f z ∈ LB.wchart L (fun _ : Fin 1 => g) j) : (𝟙 Z) z ∈ LB.wchart L (fun _ : Fin 1 => f ≫ g) j :=
  (mem_wchart_one L (f ≫ g) j ((𝟙 Z) z)).2 ((mem_wchart_one L g j (f z)).1 h)

end GlobalTheory.HomFixMatCond

namespace GlobalTheory.HomFixMatCond

theorem mat_cond : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM hcov hvA hvB hT hMat
  obtain ⟨hpA, hpB, hΦ, -⟩ := hT
  obtain ⟨ψA, ψB, α, hA, hB, -, hnorm, hmat⟩ := hMat
  obtain rfl := eq_θ A φA' ψA hA
  obtain rfl := eq_θ B φB' ψB hB
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A'.left) (z : Z) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι))
      (_ : r z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (j : Fin mB),
      gs (r ≫ Φ'.left ≫ φB' ≫ θ B) z ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs r z _ (α.s p).val * ∑ i, gs (r ≫ A'.hom) z ⊤ (c i j) *
          gs (r ≫ φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) := by
    intro Z r z p hz j
    have e := congrArg (gs r z _) (hmat j p)
    erw [gs_appLE _ _ _ _ r z hz, gs_mul r z _ hz, gs_sum' r z _ hz] at e
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul r z _ hz]
      erw [gs_appLE _ _ _ _ r z hz, gs_appLE _ _ _ _ r z hz]
      all_goals rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z q hq
    have hz : (Φ'.left ≫ φB' ≫ θ B) z ∈ ⨆ j, nonzeroLocus (bB j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    unfold nonzeroLocus at hj
    obtain ⟨kk, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hkU := (topS Rg ⊗ B).left.basicOpen_le _ hk
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hkU, mem_wchart_comp _ _ _ _ _ hq⟩
    have e := key (𝟙 _) z (kk, q) hzU j
    simp only [Category.id_comp] at e
    refine ⟨j, ?_⟩
    have hu : IsUnit (gs (Φ'.left ≫ φB' ≫ θ B) z _ ((bB j).f kk)) := by
      rw [gs_eq _ _ _ hkU]
      have : z ∈ A'.left.basicOpen (((Φ'.left ≫ φB' ≫ θ B).app _).hom ((bB j).f kk)) := by
        rw [← Scheme.preimage_basicOpen]; exact hk
      exact (Scheme.mem_basicOpen _ _ _ _).1 this
    rw [e] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro z q kk hq hk j j'
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hk, mem_wchart_comp _ _ _ _ _ hq⟩
    have e1 := key (𝟙 _) z (kk, q) hzU j
    have e2 := key (𝟙 _) z (kk, q) hzU j'
    simp only [Category.id_comp] at e1 e2
    have hc : ∀ j, comb bA (φA' ≫ θ A) A'.hom c z q j = ∑ i, gs A'.hom z ⊤ (c i j) *
        gs (φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U q) ((bA i).f q) := fun _ => rfl
    rw [hc, hc, e1, e2]
    ring
  · intro j
    apply fn_ext
    intro x _
    obtain ⟨qA, hqA⟩ := exists_chart hL (eSec A (t x))
    obtain ⟨qB, hqB⟩ := exists_chart hM (eSec B (t x))
    have F2 : zeroPt A' ≫ φA' = t ≫ eSec A := GlobalTheory.PolBaseChange.eSec_comm hpA
    have F3 : zeroPt A' ≫ Φ'.left ≫ φB' = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
        show η[A'].left ≫ Φ'.left = η[B'].left
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, h0]; exact GlobalTheory.PolBaseChange.eSec_comm hpB
    have F1 : zeroPt A' ≫ A'.hom = 𝟙 _ := Over.w η[A']
    have GA : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by rw [reassoc_of% F2]
    have GB : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by rw [reassoc_of% F3]
    let p : (Fin 1 → M.ι) × (Fin 1 → L.ι) := (fun _ => qB, fun _ => qA)
    have hx0 : zeroPt A' x ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := by
      refine ⟨(mem_wchart_one _ _ _ _).2 ?_, (mem_wchart_one _ _ _ _).2 ?_⟩
      · rw [app_of_comp (f := zeroPt A') (g := (Φ'.left ≫ φB' ≫ θ B) ≫ (snd (topS Rg) B).left)
          (h := t ≫ eSec B) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F3)]
        exact hqB
      · rw [app_of_comp (f := zeroPt A') (g := (φA' ≫ θ A) ≫ (snd (topS Rg) A).left)
          (h := t ≫ eSec A) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F2)]
        exact hqA
    have hmemA : (eSec A ≫ θ A) (t x) ∈ (LPow A L (k : ℤ) (topS Rg)).U p.2 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec A ≫ θ A) (g := (snd (topS Rg) A).left) (h := eSec A)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqA
    have hmemB : (eSec B ≫ θ B) (t x) ∈ (LPow B M (k : ℤ) (topS Rg)).U p.1 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec B ≫ θ B) (g := (snd (topS Rg) B).left) (h := eSec B)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqB
    have hWA : t x ∈ (L.pull (eSec A)).U (fun _ => p.2 0) := (mem_wchart_unit _ _ _ _).2 hqA
    have hWB : t x ∈ (M.pull (eSec B)).U (fun _ => p.1 0) := (mem_wchart_unit _ _ _ _).2 hqB
    have hIA : ∀ i, gs (t ≫ eSec A ≫ θ A) x ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) =
        gs t x ⊤ (αA i) * gs t x _ (eA.s (fun _ => qA)).val ^ k := by
      intro i
      rw [gs_comp_stalk _ _ _ _ hmemA, hvA i (t x) p.2 hmemA, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eA.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWA, ← gs_stalkMap t x _ hWA]
    have hIB : gs (t ≫ eSec B ≫ θ B) x ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs t x ⊤ (βB j) * gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      rw [gs_comp_stalk _ _ _ _ hmemB, hvB j (t x) p.1 hmemB, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eB.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWB, ← gs_stalkMap t x _ hWB]
    have hxW : (𝟙 (Sp R)) x ∈ (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p ⊓
        t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
        t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := ⟨⟨hx0, hWA⟩, hWB⟩
    have hN : gs (zeroPt A') x _ (α.s p).val * gs t x _ (eA.s (fun _ => qA)).val ^ k =
        gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      have e := congrArg (gs (𝟙 (Sp R)) x _) (hnorm p)
      rw [gs_mul _ _ _ hxW, gs_pow' _ _ _ hxW, gs_pow' _ _ _ hxW] at e
      erw [gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW] at e
      simp only [Category.id_comp] at e
      exact e
    have eK := key (zeroPt A') x p hx0 j
    rw [GA, GB, F1, hIB] at eK
    simp only [hIA] at eK
    have heb : IsUnit (gs t x _ (eB.s (fun _ => qB)).val) := by
      rw [gs_unit t x _ hWB]; exact Units.isUnit _
    rw [gs_appTop', gs_sum' (𝟙 (Sp R)) x ⊤ trivial]
    simp only [gs_mul (𝟙 (Sp R)) x ⊤ trivial, gs_appTop']
    apply (heb.pow k).mul_left_inj.1
    rw [eK, ← hN, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.HomFixMatCond
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testHom_matrix_generates_normalised : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  first | (exact @GlobalTheory.HomFixMatCond.mat_cond) | (exact GlobalTheory.HomFixMatCond.mat_cond) | (intros; apply GlobalTheory.HomFixMatCond.mat_cond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixUniv

variable {mA mB : ℕ}

theorem comb_comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) (z : X₂)
    (q : N.ι) (hq : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ : gs p₂ z ⊤ (h.appTop (c i j)) = gs (r ≫ p) z ⊤ (c i j) := by
    rw [← e]; exact gs_pull p₂ h z ⊤ trivial (c i j)
  rw [e₁, gs_comp r p z ⊤ trivial, gs_comp r φ z _ hq]

theorem Generates.comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hg : Generates a φ p c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂)
    (e : p₂ ≫ h = r ≫ p) : Generates a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) := by
  intro z q hq
  obtain ⟨j, hj⟩ := hg (r z) q hq
  exact ⟨j, by rw [comb_comp a φ p c r h p₂ e z q hq j]; exact hj.map _⟩

theorem Proport.comp {A₀ B₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {H : LB B₀} {a : Fin mA → LB.Sec N}
    {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hp : Proport a b φ p Ψ c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) :
    Proport a b (r ≫ φ) p₂ (r ≫ Ψ) (fun i j => h.appTop (c i j)) := by
  intro z q k hq hk j j'
  rw [comb_comp a φ p c r h p₂ e z q hq, comb_comp a φ p c r h p₂ e z q hq, gs_comp r Ψ z _ hk,
    gs_comp r Ψ z _ hk, ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem matOf_comp {Rg : Type} [CommRing Rg] {X X' : Scheme.{0}} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) : matOf (h ≫ g) = fun i j => h.appTop (matOf g i j) := by
  funext i j; exact coord_comp h g _

theorem relift {S T' T : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over T} [GrpObj G₁] {G' : Over T'} [GrpObj G']
    {t₁ : T ⟶ S} {u : T' ⟶ T} {φ₁ : G₁.left ⟶ G.left} {φ' : G'.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G t₁ φ₁)
    (h' : IsGrpPullback G' G (u ≫ t₁) φ') : ∃ ψ : G'.left ⟶ G₁.left, IsGrpPullback G' G₁ u ψ ∧ ψ ≫ φ₁ = φ' := by
  refine ⟨h₁.1.lift φ' (G'.hom ≫ u) (by rw [h'.1.w, Category.assoc]), ?_, h₁.1.lift_fst _ _ _⟩
  exact h₁.cancel (by rw [h₁.1.lift_fst]; exact h') (h₁.1.lift_snd _ _ _)

theorem exists_universal_matrix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH
  obtain ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ := hH
  obtain ⟨hfl, hpj, huc⟩ := GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed Rg A L hAb hL hamp
  haveI := huc
  have hEmb := GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hBb hM hk hva hbB
  have hcov : (⨆ j, nonzeroLocus (bB j)) = ⊤ := hEmb.1
  have hNA : (LPow A L (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hL _ _
  have hNB : (LPow B M (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hM _ _
  choose αA hαA using fun i => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg A L k eA (bA i) hL heA
  choose βB hβB using fun j => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg B M k eB (bB j) hM heB
  obtain ⟨U, hU⟩ := GlobalTheory.T.isOpen_generatingCombinationMatrixLocus Rg _ (fA A) _ mA mB bA hNA
  obtain ⟨ZF, ιF, hιF, hF⟩ := GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections Rg _ _ (fA A) (fA B) _ _ mA mB bA bB hfl hpj hNA
  obtain ⟨ZN, ιN, hιN, hNm⟩ := GlobalTheory.T.linearNormalisation_closed_subscheme Rg mA mB αA βB
  haveI : IsNoetherian (Sp (MvPolynomial (Fin (mA * mB)) Rg)) := isNoetherian_Spec.2 inferInstance
  obtain ⟨W, j₁, hj₁, hj₁q, hWn, hW⟩ := GlobalTheory.T.exists_immersed_closed_open_intersection _ ZF ZN ιF ιN U hιF hιN
  have cond : ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ (topS Rg ⊗ A).left)
      (p : X' ⟶ T), (∃ w, w ≫ j₁ = g) → IsPullback φ p (fA A) (g ≫ affπ Rg (mA * mB)) →
      Generates bA φ p (matOf g) ∧ FormsOK bA (fA B) bB φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ∧
        Normal (g ≫ affπ Rg (mA * mB)) (matOf g) αA βB := by
    intro T X' g φ p hg hP
    obtain ⟨h1, h2, h3⟩ := (hW T g).2 hg
    exact ⟨(hU T X' g φ p hP).2 h3, (hF T X' g φ p hP).2 h1, (hNm T g).2 h2⟩
  have datum : ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (∃ w, w ≫ j₁ = g) →
      ∃ (AT : Over T) (_ : GrpObj AT) (BT : Over T) (_ : GrpObj BT) (φA : AT.left ⟶ A.left) (φB : BT.left ⟶ B.left)
        (Φ : AT ⟶ BT), IsGrpPullback AT A (g ≫ affπ Rg (mA * mB)) φA ∧
        IsGrpPullback BT B (g ≫ affπ Rg (mA * mB)) φB ∧ IsMonHom Φ ∧ Generates bA (φA ≫ θ A) AT.hom (matOf g) ∧
        Proport bA bB (φA ≫ θ A) AT.hom (Φ.left ≫ φB ≫ θ B) (matOf g) := by
    intro T g hg
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj B) := Functor.grpObjObj
    have pA := isGrpPullback_pullback A (g ≫ affπ Rg (mA * mB))
    have pB := isGrpPullback_pullback B (g ≫ affπ Rg (mA * mB))
    have hP := (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A T _ _ _ (g ≫ affπ Rg (mA * mB))).1 pA.1
    obtain ⟨c1, c2, c3⟩ := cond T _ g _ _ hg hP
    obtain ⟨Ψ, hΨ, hpr⟩ := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ T (fA A) (fA B) _ _ mA mB bA bB _ _ _ (matOf g) hEmb hNB hNA hP.w
      c1).1 c2
    obtain ⟨Φ, hΦ, hΦΨ⟩ := GlobalTheory.T.grpHom_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB T _ _ _ _ _ Ψ (matOf g)
      ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ hαA hβB pA pB hΨ c1 hpr c3
    exact ⟨_, inferInstance, _, inferInstance, _, _, Φ, pA, pB, hΦ, c1, by rw [hΦΨ]; exact hpr⟩
  have θf : ∀ C : Over (Sp Rg), θ C ≫ fA C = C.hom := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.1
  have θi : ∀ C : Over (Sp Rg), IsIso (θ C) := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.2
  obtain ⟨A₁, iA₁, B₁, iB₁, φA₁, φB₁, Φ₁, pA₁, pB₁, hΦ₁, hg₁, hp₁⟩ := datum W j₁ ⟨𝟙 _, Category.id_comp _⟩
  haveI := hWn
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic Rg A B L M eA eB W (j₁ ≫ affπ Rg (mA * mB)) A₁ B₁ φA₁ φB₁ Φ₁ hAb hBb hL hM heA heB
    hamp pA₁ pB₁ hΦ₁
  have compare : ∀ (T : Scheme.{0}) (u : T ⟶ W) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φA' →
      IsGrpPullback B' B ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φB' →
      Generates bA (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) →
      Proport bA bB (φA' ≫ θ A) A'.hom (Φ'.left ≫ φB' ≫ θ B) (matOf (u ≫ j₁)) →
      ∃ (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left), IsGrpPullback A' A₁ u ψA ∧ IsGrpPullback B' B₁ u ψB ∧
        ψA ≫ φA₁ = φA' ∧ ψB ≫ φB₁ = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ₁.left := by
    intro T u A' B' _ _ φA' φB' Φ' hA' hB' hgen hprop
    rw [Category.assoc] at hA' hB'
    obtain ⟨ψA, hψA, eA'⟩ := relift pA₁ hA'
    obtain ⟨ψB, hψB, eB'⟩ := relift pB₁ hB'
    refine ⟨ψA, ψB, hψA, hψB, eA', eB', ?_⟩
    apply pB₁.1.hom_ext
    · rw [Category.assoc, eB', Category.assoc, ← cancel_mono (θ B), Category.assoc, Category.assoc, Category.assoc]
      have hp := hp₁.comp ψA u A'.hom hψA.1.w.symm
      rw [← matOf_comp, ← Category.assoc ψA φA₁, eA'] at hp
      refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ _ T (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) _ _ hEmb hNB hNA hgen
        hprop hp ?_
      simp only [Category.assoc, θf]
      rw [hB'.1.w, pB₁.1.w, reassoc_of% (Over.w Φ'), reassoc_of% (Over.w Φ₁), reassoc_of% hψA.1.w]
    · rw [Category.assoc, hψB.1.w, reassoc_of% (Over.w Φ'), Category.assoc, Over.w Φ₁, hψA.1.w]
  obtain ⟨AH, iAH, BH, iBH, φAH, φBH, ΦH, pAH, pBH, hΦH, hgH, hpH⟩ := datum Z (i ≫ j₁) ⟨i, rfl⟩
  obtain ⟨ψA, ψB, hψA, hψB, eψA, eψB, eΦ⟩ := compare Z i AH BH φAH φBH ΦH pAH pBH hgH hpH
  have hlb : LBIso (L.pull φAH) ((M.pull φBH).pull ΦH.left) := by
    have := (hZ Z i AH BH ψA ψB ΦH hψA hψB eΦ).2 ⟨𝟙 _, Category.id_comp _⟩
    rwa [eψA, eψB] at this
  refine ⟨(i ≫ j₁).image, (i ≫ j₁).imageι, Z, (i ≫ j₁).toImage, AH, iAH, BH, iBH, φAH, φBH, ΦH, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.toImage_imageι_assoc]
    exact ⟨pAH, pBH, hΦH, hlb⟩
  · intro R _ t A' B' _ _ φA' φB' Φ' c hT hMat
    obtain ⟨g, hgt, hgc⟩ := GlobalTheory.T.exists_affineSpace_morphism_of_coordinates Rg (Sp R) (mA * mB) t
      (fun n => c (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2)
    have hgm : matOf g = c := by funext a b; simp [matOf, hgc]
    obtain ⟨hgen, hprop, hnorm⟩ := GlobalTheory.T.testHom_matrix_generates_normalised Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c hL hM
      hcov hαA hβB hT hMat
    rw [← hgm] at hgen hprop
    rw [← hgm, ← hgt] at hnorm
    have hP : IsPullback (φA' ≫ θ A) A'.hom (fA A) (g ≫ affπ Rg (mA * mB)) := by
      rw [hgt]; exact (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A _ _ _ _ t).1 hT.1.1
    have hbase : (Φ'.left ≫ φB' ≫ θ B) ≫ fA B = A'.hom ≫ g ≫ affπ Rg (mA * mB) := by
      rw [hgt, Category.assoc, Category.assoc, θf, hT.2.1.1.w, reassoc_of% (Over.w Φ')]
    have hforms := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ _ (fA A) (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (g ≫ affπ Rg _) (matOf g)
      hEmb hNB hNA hP.w hgen).2 ⟨_, hbase, hprop⟩
    obtain ⟨w₁, hw₁⟩ := (hW _ g).1 ⟨(hF _ _ g _ _ hP).1 hforms, (hNm _ g).1 hnorm, (hU _ _ g _ _ hP).1 hgen⟩
    have hA' : IsGrpPullback A' A ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φA' := by rw [hw₁, hgt]; exact hT.1
    have hB' : IsGrpPullback B' B ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φB' := by rw [hw₁, hgt]; exact hT.2.1
    obtain ⟨ψA', ψB', hψA', hψB', eψA', eψB', eΦ'⟩ := compare _ w₁ A' B' φA' φB' Φ' hA' hB'
      (by rw [hw₁]; exact hgen) (by rw [hw₁]; exact hprop)
    have hlb' := hT.2.2.2
    rw [← eψA', ← eψB'] at hlb'
    obtain ⟨w₂, hw₂⟩ := (hZ _ w₁ A' B' ψA' ψB' Φ' hψA' hψB' eΦ').1 hlb'
    refine ⟨w₂, ?_, ?_⟩
    · rw [Scheme.Hom.toImage_imageι_assoc, ← Category.assoc, ← Category.assoc, hw₂, hw₁, hgt]
    · rw [Scheme.Hom.toImage_imageι, ← Category.assoc, hw₂, hw₁, hgm]
  · intro R _ h A' B' _ _ φA' φB' Φ' hT hD
    obtain ⟨ψA', ψB', qA, qB, eA', eB', eΦ'⟩ := hD
    simp only [Scheme.Hom.toImage_imageι_assoc, Scheme.Hom.toImage_imageι] at hT ⊢
    have e₀ : A'.hom ≫ h = ψA' ≫ AH.hom := qA.1.w.symm
    have keyA : ψA' ≫ φAH ≫ θ A = φA' ≫ θ A := by rw [← eA', Category.assoc]
    have keyB : ψA' ≫ ΦH.left ≫ φBH ≫ θ B = Φ'.left ≫ φB' ≫ θ B := by
      rw [← eB']; simp only [Category.assoc]; rw [reassoc_of% eΦ']
    have hgen := hgH.comp ψA' h A'.hom e₀
    rw [keyA, ← matOf_comp] at hgen
    have hpr := hpH.comp ψA' h A'.hom e₀
    rw [keyA, keyB, ← matOf_comp] at hpr
    have hnorm : Normal ((h ≫ i ≫ j₁) ≫ affπ Rg (mA * mB)) (matOf (h ≫ i ≫ j₁)) αA βB :=
      (hNm _ _).2 ((hW _ _).2 ⟨h ≫ i, Category.assoc _ _ _⟩).2.1
    simp only [Category.assoc] at hT hnorm hgen hpr ⊢
    exact GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB R _ A' B' φA' φB' Φ' _ hL hM heA heB hcov hαA hβB hT
      hgen hpr hnorm

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  first | (exact @GlobalTheory.HomFixUniv.exists_universal_matrix) | (exact GlobalTheory.HomFixUniv.exists_universal_matrix) | (intros; apply GlobalTheory.HomFixUniv.exists_universal_matrix  <;> assumption)
end
