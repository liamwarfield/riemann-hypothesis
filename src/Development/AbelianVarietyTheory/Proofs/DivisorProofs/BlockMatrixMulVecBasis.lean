module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentRepresentationSmoothGroupScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.LeviHC

section Alg

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def FinMod (K : Submodule ℂ M) (A : Subalgebra ℂ (Module.End ℂ M)) (v : M) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ A, y = K.mkQ (a v)})

def MonicFactorFinite : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (p q : ℂ → Module.End ℂ N),
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    ∀ v : N, FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range fun u => p u * q u), y = a v}) →
      FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range p), y = a v})

def MonicFactorFiniteMod : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K ∧ q u x ∈ K) →
    (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
    ∀ v ∈ M', FinMod K (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v

theorem coeff_mem_span {d : ℕ} {a : ℕ → M} {p : ℂ → M} (hp : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i)
    {i : ℕ} (hi : i < d + 1) : a i ∈ Submodule.span ℂ (Set.range p) := by
  set W := Submodule.span ℂ (Set.range p)
  have hdual : ∀ f : Module.Dual ℂ (M ⧸ W), f (W.mkQ (a i)) = 0 := by
    intro f
    let P : Polynomial ℂ :=
      ∑ j ∈ Finset.range (d + 1), Polynomial.C (f (W.mkQ (a j))) * Polynomial.X ^ j
    have hP : P = 0 := by
      apply Polynomial.funext
      intro u
      have h0 : W.mkQ (p u) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span ⟨u, rfl⟩)
      have h1 : f (W.mkQ (p u)) = ∑ j ∈ Finset.range (d + 1), u ^ j * f (W.mkQ (a j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hp u, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, smul_eq_mul]
      rw [h0, map_zero] at h1
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff i) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_ite_eq] at hc
    simpa [Finset.mem_range.2 hi] using hc
  have hq : W.mkQ (a i) = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ _).1 hdual
  exact (Submodule.Quotient.mk_eq_zero W).1 hq

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}



variable (σ J) in
def IsLineOf {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z)


variable {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}

theorem IsLineOf.skew (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 := by
  apply GlobalTheory.LineDerSum.skew_of_exp_unitary
  intro t
  obtain ⟨y, -, hy⟩ := hγ t
  rw [← hy, GlobalTheory.Orb.archMat_eq_archEquiv J h τ y]
  exact (archEquiv J h τ y).2

theorem IsLineOf.isRealLine (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, hγ.skew h, hγ⟩

private theorem conjTranspose_map_eq_of_isHermND (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← h.2.2.2 τ, hJ.1 i j]

private theorem isUnit_det_map_of_det_ne_zero {K : Type} [Field K] {m : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (hM : M.det ≠ 0) (τ : K →+* ℂ) : IsUnit (M.map τ).det := by
  have hd : (M.map τ).det = τ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 hM

theorem conjTranspose_map (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := conjTranspose_map_eq_of_isHermND h hJ τ

omit [NumberField F] [NumberField E] in
theorem isUnit_det_map (hJ : IsHermND σ J) (τ : E →+* ℂ) : IsUnit (J.map τ).det := isUnit_det_map_of_det_ne_zero hJ.2 τ

variable {n₁ : ℕ}




end GlobalTheory.LeviHC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalk
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalk
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef

theorem evAt_eq_comp {R : Type} [CommRing R] {X : Scheme.{0}} (b : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) :
    CommRingCat.ofHom (evAt b h) = b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := rfl

theorem evAt_spMap_comp (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evAt (spMap φ ≫ b) h' f = φ (evAt b h f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE (spMap φ) b U ⊤ ⊤ h le_rfl
  have e3 : (spMap φ).appLE ⊤ ⊤ le_rfl = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (spMap φ ≫ b).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    rw [← e2, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_comp (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)) :
    evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE b g V U ⊤ e h
  have e4 : (b ≫ g).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      g.appLE V U e ≫ b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_res (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)) :
    evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f := by
  have e2 := Scheme.Hom.map_appLE b h' (homOfLE e).op
  have e4 : X.presheaf.map (homOfLE e).op ≫ b.appLE U' ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem top_le_iff_closedPoint_mem (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X)
    (U : X.Opens) : ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U := by
  refine ⟨fun h => h (Set.mem_univ _), fun hb q _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum R)).map b.continuous).mem_open U.2 hb

theorem eq_of_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (he : evAt b h = evAt b' h') : b = b' := by
  have k0 : b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b'.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← evAt_eq_comp, ← evAt_eq_comp, he]
  have k : b.appLE U ⊤ h = b'.appLE U ⊤ h' := (cancel_mono _).1 k0
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec b hU (isAffineOpen_top (Sp R)) h
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec b' hU (isAffineOpen_top (Sp R)) h'
  rw [k] at e1
  have e3 := e1.symm.trans e2
  rw [IsAffineOpen.fromSpec_top] at e3
  exact (cancel_epi _).1 e3

theorem exists_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens) (hU : IsAffineOpen U)
    (φ : Γ(X, U) →+* R) : ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, h, ?_⟩
  have e1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) hU.fromSpec U ⊤ ⊤ hfs le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : CommRingCat.ofHom (evAt (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) h) =
      CommRingCat.ofHom φ := by
    rw [evAt_eq_comp, ← e2, e1, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc _
  exact congrArg CommRingCat.Hom.hom e4

theorem evAt_fromSpecStalk' (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R)
    (U : X.Opens) (hp : p ∈ U) :
    ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U,
      ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f =
        φ (X.presheaf.germ U p hp f) := by
  have h0 : ⊤ ≤ X.fromSpecStalk p ⁻¹ᵁ U := fun q _ =>
    ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum _)).map (X.fromSpecStalk p).continuous).mem_open U.2
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hp)
  refine ⟨fun q _ => h0 (Set.mem_univ _), fun s => ?_⟩
  have e1 : (X.fromSpecStalk p).appLE U ⊤ h0 = X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (Category.comp_id _))
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) (X.fromSpecStalk p) U ⊤ ⊤ h0 le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p).appLE U ⊤ (fun q _ => h0 (Set.mem_univ _)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = X.presheaf.germ U p hp ≫ CommRingCat.ofHom φ := by
    rw [← e2, e1, e3, Category.assoc, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact congrArg (_ ≫ ·) ((Scheme.ΓSpecIso (X.presheaf.stalk p)).inv_hom_id_assoc _)
  exact congrArg (fun ψ => ψ.hom s) e4

theorem evAt_calculus : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)), evAt (spMap φ ≫ b) h' f = φ (evAt b h f)) ∧ (∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)), evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f)) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)), evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f) ∧ (∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U : X.Opens), ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b h = evAt b' h' → b = b') ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ φ : Γ(X, U) →+* R, ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R) (U : X.Opens) (hp : p ∈ U), ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U, ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f = φ (X.presheaf.germ U p hp f)) :=
  ⟨evAt_spMap_comp, evAt_comp, evAt_res, top_le_iff_closedPoint_mem, eq_of_evAt_eq, exists_evAt_eq,
    evAt_fromSpecStalk'⟩

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)), evAt (spMap φ ≫ b) h' f = φ (evAt b h f)) ∧ (∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)), evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f)) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)), evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f) ∧ (∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U : X.Opens), ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b h = evAt b' h' → b = b') ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ φ : Γ(X, U) →+* R, ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R) (U : X.Opens) (hp : p ∈ U), ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U, ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f = φ (X.presheaf.germ U p hp f)) := by
  first | exact @GlobalTheory.Nef.evAt_calculus | exact GlobalTheory.Nef.evAt_calculus | (intros; apply GlobalTheory.Nef.evAt_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.PsiNontriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels WithZero
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_trace_not_int (v : HeightOneSpectrum (𝓞 F)) :
    ∃ z : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1) ∧
      Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
  classical
  set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC
  set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN
  have hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := by simpa using v.ne_bot
  set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI
  have hI0 : I ≠ 0 := inv_ne_zero (pow_ne_zero _ hP)
  have hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0 := by
    intro w
    rw [hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]
    split_ifs with hw
    · subst hw; rw [FractionalIdeal.count_self]; ring
    · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]; ring
  have hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1 := by
    intro z hz w hw
    have := (GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w
    rwa [hcount w, if_neg hw, neg_zero, exp_zero] at this
  by_contra H
  push_neg at H
  have hle : I ≤ C := by
    intro x hx
    rw [hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hxa : x * algebraMap (𝓞 F) F a ∈ I := by
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a hx
    exact H _ (hint _ hxa)
  have := FractionalIdeal.count_mono F v hI0 hle
  rw [hcount v, if_pos rfl] at this
  omega

theorem psiV_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  obtain ⟨z, hz, hzt⟩ := exists_trace_not_int (F := F) v
  have hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1 := fun t => by
    rw [← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]
  set zv : Fv F v := algebraMap F (Fv F v) z with hzv
  set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα
  have hαint : α ∈ intAf F := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv := rfl
      rw [this, sub_self]
      exact zero_mem _
    · rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z := rfl
      rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
      exact hz w hw
  have htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k := by
    intro a
    have hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1)) := by
      rw [mul_one]
      exact Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact ⟨k, by rw [← hk]; simp⟩
  have h0 := GlobalTheory.LatVacArith.psi_int hψ 1 htr α hαint
  rw [map_one, mul_one] at h0
  have hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv := by
    refine Prod.ext (add_zero (0 : Ainf F)).symm ?_
    show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv
    rw [hα, sub_add_cancel]
  have hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1 := by
    rw [hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]
  rw [GlobalTheory.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff] at hval
  obtain ⟨n, hn⟩ := hval
  apply hzt
  refine ⟨n, ?_⟩
  have hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  rw [eq_intCast]
  exact_mod_cast hc.symm

end GlobalTheory.PsiNontriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  first | exact @GlobalTheory.PsiNontriv.psiV_ne_one | exact GlobalTheory.PsiNontriv.psiV_ne_one | (intros; apply GlobalTheory.PsiNontriv.psiV_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm.HaarSplit

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem splitE_apply (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl

theorem continuous_splitE : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
    refine continuous_pi fun v => ?_
    rcases v.isReal_or_isComplex with hv | hv
    · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
      exact ((continuous_apply _).comp continuous_fst).congr fun y =>
        (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
    · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
      exact ((continuous_apply _).comp continuous_snd).congr fun y =>
        (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  exact continuous_pi fun i => (hc.comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have he : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
          (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
      funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
    rw [he]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact (continuous_pi fun i => hc.comp
    (continuous_fst.comp (continuous_apply i))).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]

theorem continuous_comp_splitE [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    Continuous fun p => Φ (splitE F κ p) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_splitE]
    exact (f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x x' _ _ hx hx' => exact hx.add hx'
  | smul a x _ hx => exact hx.const_smul a

theorem splitE_add_finE (z : κ → mixedEmbedding.mixedSpace F) (y u : κ → FiniteAdeleRing (𝓞 F) F) :
    splitE F κ (z, y + u) = splitE F κ (z, y) + GlobalTheory.WeilAdm.finE F u :=
  funext fun i => Prod.ext (add_zero _).symm rfl

theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  exact Measure.pi.isAddHaarMeasure _

end GlobalTheory.WeilAdm.HaarSplit

namespace GlobalTheory.WeilAdm.HaarSplit

open GlobalTheory.WeilAdm.HaarSplit

theorem haar_pure_slice_bounds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ g hg U hU
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em

  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]

  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : κ → FiniteAdeleRing (𝓞 F) F)
  set S : Set (κ → FiniteAdeleRing (𝓞 F) F) := (U : Set _) ∩ K with hS
  have hSm : MeasurableSet S := hU.measurableSet.inter hKc.isClosed.measurableSet
  have hc0 : ν S ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_right _ interior_subset)))
    exact (hU.inter isOpen_interior).measure_pos ν ⟨0, U.zero_mem, mem_interior_iff_mem_nhds.2 hK0⟩
  have hcT : ν S ≠ ⊤ := ne_top_of_le_ne_top hKc.measure_lt_top.ne (measure_mono Set.inter_subset_right)
  refine ⟨(volume.prod ν).map (splitE F κ), hμH, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ν S, hC, hc0, hcT, ?_, ?_⟩
  · intro f
    rw [hint]
    have e1 : ∀ p, ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (f.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable, mul_comm]
  · intro Φ hΦ hinv y
    rw [hint]
    have hHm : Measurable fun p => ‖Φ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Φ hΦ).measurable.enorm.pow_const 2
    rw [lintegral_prod _ hHm.aemeasurable, ← lintegral_const_mul' _ _ hcT]
    refine lintegral_mono fun z => ?_
    set T : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun y' => y' + -y) ⁻¹' S with hT
    have hTm : MeasurableSet T := hSm.preimage (continuous_id.add continuous_const).measurable
    have hνT : ν T = ν S := measure_preimage_add_right ν (-y) S
    calc ν S * ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2
        = ∫⁻ y', T.indicator (fun _ => ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2) y' ∂ν := by
          rw [lintegral_indicator_const hTm, hνT, mul_comm]
      _ ≤ ∫⁻ y', ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y' => (Set.indicator_le (g := fun y' => ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2) (fun a ha => le_of_eq ?_)) y'
          have hu : a + -y ∈ U := ha.1
          have ha' : a = y + (a + -y) := by abel
          show ‖Φ (splitE F κ (z, y))‖ₑ ^ 2 = ‖Φ (splitE F κ (z, a))‖ₑ ^ 2
          rw [ha', splitE_add_finE, hinv _ _ hu]

end GlobalTheory.WeilAdm.HaarSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlicesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_adelicVectors_bounds_pureTensors_slices : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | exact GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | (intros; apply GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotMatch

def complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) : {s : Fin a' → Fin d // StrictMono s} :=
  ⟨Finset.orderEmbOfFin (Finset.univ.image s.1)ᶜ (by
      rw [Finset.card_compl, Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]; omega), (Finset.orderEmbOfFin _ _).strictMono⟩

theorem range_complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    Set.range (complSub h s).1 = (Set.range s.1)ᶜ := by
  simp only [complSub, Finset.range_orderEmbOfFin, Finset.coe_compl, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem complSub_complSub {a a' d : ℕ} (h : a + a' = d) (h' : a' + a = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    complSub h' (complSub h s) = s := by
  apply Subtype.ext
  apply (StrictMono.range_inj (complSub h' (complSub h s)).2 s.2).1
  rw [range_complSub, range_complSub, compl_compl]

def complTup (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) (T : Tup D a d n) : Tup D a' d n :=
  fun τ k => complSub h (T τ k)

theorem complTup_bijective (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) :
    Function.Bijective (complTup D (n := n) h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨complTup D (a := a') (a' := a) (by omega), fun T => ?_, fun T => ?_⟩ <;>
    funext τ k <;> simp only [complTup, complSub_complSub]

theorem exists_signed_perm {α β : Type} [Fintype α] [Fintype β] (c : α → β) (hc : Function.Bijective c) (ε : α → ℤˣ) :
    ∃ (M : α → β → ℤ) (M' : β → α → ℤ), (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
      ∀ T (f : β → ℂ), ∑ T', (M T T' : ℂ) * f T' = ((ε T : ℤ) : ℂ) * f (c T) := by
  classical
  refine ⟨fun T T' => if T' = c T then (ε T : ℤ) else 0, fun T' T => if T' = c T then (ε T : ℤ) else 0, fun T₁ T₂ => ?_,
    fun T f => ?_⟩
  · obtain ⟨T, rfl⟩ := hc.2 T₁
    rw [Finset.sum_eq_single T]
    · by_cases h : c T = T₂
      · subst h; simp [← Units.val_mul]
      · simp [h, Ne.symm h]
    · intro b _ hb
      have : c T ≠ c b := fun e => hb (hc.1 e).symm
      simp [this]
    · simp
  · rw [Finset.sum_eq_single (c T)]
    · simp
    · intro b _ hb; simp [hb]
    · simp

end GlobalTheory.BotMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

private theorem hasFrame_of_isBaseChange_local : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (j : W →ₗ[R] Glob1 F), (∀ T : C, ∃ e : W →ₗ[R] Ω[F.obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange (F.obj T) e) → HasFrame F := by
  intro R _ C _ F W _ _ _ _ j h
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin' R W
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property v (LinearMap.id) hv
  have hw : ∀ x : W, x = ∑ i, σ x i • v (Pi.single i 1) := by
    intro x
    have := LinearMap.congr_fun hσ x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    conv_lhs => rw [← this]
    conv_lhs => rw [show σ x = ∑ i, σ x i • Pi.single i (1 : R) from by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  choose e he hb using h
  let l : Fin n → W →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ σ
  let δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
    fun i T ↦ (hb T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l i)
  have hδ : ∀ i T (x : W), δ i T (e T x) = algebraMap R (F.obj T) (σ x i) := by
    intro i T x
    exact (hb T).lift_eq _ x
  refine ⟨n, ⟨⟨fun i ↦ j (v (Pi.single i 1)), δ, ?_, ?_⟩⟩⟩
  · intro i T T' φ ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      have h1 : p1 F φ (e T x) = e T' x := by
        rw [he T x, he T' x]; exact ((j x).2 φ).symm
      rw [h1, hδ, hδ]
      exact ((mp F φ).commutes _).symm
    · intro s ω hω
      rw [oneFormsMapOfFunctorMorphism_smul, LinearMap.map_smul, LinearMap.map_smul, hω, smul_eq_mul, smul_eq_mul, map_mul]
    · intro a b ha hb'
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb', map_add (f := _)]
  · intro T ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      simp_rw [hδ, ← he T, algebraMap_smul]
      conv_lhs => rw [hw x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp_rw [map_smul]
    · intro s ω hω
      conv_lhs => rw [hω]
      simp_rw [LinearMap.map_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
    · intro a b ha hb'
      conv_lhs => rw [ha, hb']
      simp_rw [map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem hasFrame_of_smooth_grpObj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    Smooth A.hom → HasFrame (OAff A.hom) := by
  intro R _ A _ hs
  obtain ⟨W, i1, i2, hfin, hproj, ⟨t⟩⟩ := GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hs
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_global_oneForms_isBaseChange_tangentRep R A W t
  exact hasFrame_of_isBaseChange_local R _ (OAff A.hom) W j hj

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGlobalOneFormFrame_of_smooth_groupScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], Smooth A.hom → HasFrame (OAff A.hom) := by
  first | exact @GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj | exact GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj | (intros; apply GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem smoothOfRelativeDimension_sq {R : Type} [CommRing R] {A : Over (Sp R)} {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom A.hom).flip hg
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g g _ _

theorem basic_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ CohomZeroIsConstants (OAff A.hom) ∧
      IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  intro R _ A _ g hA hg
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  refine ⟨GlobalTheory.T.hasGlobalOneFormFrame_of_smooth_groupScheme R A hs, ?_, AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, smoothOfRelativeDimension_sq hg⟩
  have hsq : IsPullback (𝟙 A.left) A.hom A.hom (spMap (algebraMap R R)) := by
    rw [Algebra.algebraMap_self, spMap_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA R A.left A.hom (𝟙 _) hsq

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_oneFormFrame_and_square : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ CohomZeroIsConstants (OAff A.hom) ∧ IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  first | exact @GlobalTheory.AbCoh.basic_of_isAbelianScheme | exact GlobalTheory.AbCoh.basic_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.basic_of_isAbelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatVac

theorem heis_at_local_identity : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (co.rho ψ γ) f (χ • f) →
    ∀ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r → ∀ x₀, r x₀ ≠ 0 →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f χ hγ hA r hr x₀ hx₀ ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : r x = r x₀ := hr.1 x₀ z hzat
  have hrx1 : r (x + (co.e γ).1) = r x := hr.1 x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun (hA r hr) x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : r x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  simp only [Pi.smul_apply, smul_eq_mul] at this
  apply mul_right_cancel₀ hr0
  rw [← this]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

end GlobalTheory.LatVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergEigen_latticePointAtPlace_localIdentity : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (co.rho ψ γ) f (χ • f) →
    ∀ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r → ∀ x₀, r x₀ ≠ 0 →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  first | exact @GlobalTheory.LatVac.heis_at_local_identity | exact GlobalTheory.LatVac.heis_at_local_identity | (intros; apply GlobalTheory.LatVac.heis_at_local_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticTransfer
open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.ArchUniq

open GlobalTheory.RealWeil

theorem pairingCoords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland

theorem symplMatrix : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm

end GlobalTheory.ArchUniq

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

end GlobalTheory.ArchUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRows
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

theorem carries_of_rows_top : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro hC hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hOk hW hEx hHk hPG hPos
  have hS : SchurAll R.toRealDat := schurAll_of_cuspRapidDecay hC R.toRealDat
  have hB := GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces hC R F hL hOk hW hEx hPG
  have hIx := GlobalTheory.T.nonempty_finite_type_index_of_rows_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hOk hB (hPos false)
  exact GlobalTheory.T.rowEigensystem_carried_by_finite_type R F hL hOk hW hEx hS (GlobalTheory.T.exists_partner_combination_good_inert_lift hH R F hL hW hEx hS) hHk hPG hIx

end GlobalTheory.Hk3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRowsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  first | exact @GlobalTheory.Hk3.carries_of_rows_top | exact GlobalTheory.Hk3.carries_of_rows_top | (intros; apply GlobalTheory.Hk3.carries_of_rows_top <;> assumption)
end
end
