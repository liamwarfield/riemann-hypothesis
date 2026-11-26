module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellation
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem spec_localInjective_cancel_left (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
    (φ : R →+* R') [IsLocalHom φ] (hφ : Function.Injective φ) (Y : Scheme.{0}) (a a' : Sp R ⟶ Y)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  obtain ⟨hcomp, -, -, hloc, hext, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint φ
  have hy : a (IsLocalRing.closedPoint R) = a' (IsLocalRing.closedPoint R) := by
    have := congrArg (fun f : Sp R' ⟶ Y => f (IsLocalRing.closedPoint R')) h
    exact (congrArg a hc).symm.trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
      (this.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg a' hc))))
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := a (IsLocalRing.closedPoint R))
    (U := ⊤) trivial
  have h1 : ⊤ ≤ a ⁻¹ᵁ U := (hloc R Y a U).2 hyU
  have h2 : ⊤ ≤ a' ⁻¹ᵁ U := (hloc R Y a' U).2 (hy ▸ hyU)
  have h1' : ⊤ ≤ (spMap φ ≫ a) ⁻¹ᵁ U := (hloc R' Y _ U).2 (((Scheme.Hom.comp_apply _ _ _).trans (congrArg a hc)) ▸ hyU)
  have h2' : ⊤ ≤ (spMap φ ≫ a') ⁻¹ᵁ U := h ▸ h1'
  have key : ∀ (b b' : Sp R' ⟶ Y) (_ : b = b') (hb : ⊤ ≤ b ⁻¹ᵁ U) (hb' : ⊤ ≤ b' ⁻¹ᵁ U),
      evAt b hb = evAt b' hb' := by
    rintro b _ rfl _ _; rfl
  refine hext R Y a a' U hU h1 h2 (RingHom.ext fun f => hφ ?_)
  rw [← hcomp R R' Y φ a U h1 h1' f, ← hcomp R R' Y φ a' U h2 h2' f, key _ _ h h1' h2']

theorem spec_injective_cancel_left_of_separated (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Injective φ)
    (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y) (hp : a ≫ p = a' ≫ p)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  let d : Sp R ⟶ pullback p p := pullback.lift a a' hp
  have e1 : a = d ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
  have e2 : a' = d ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
  let i : pullback d (pullback.diagonal p) ⟶ Sp R := pullback.fst _ _
  have hfac : spMap φ ≫ d = (spMap φ ≫ a) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, ← e2, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  let g : Sp R' ⟶ pullback d (pullback.diagonal p) := pullback.lift (spMap φ) (spMap φ ≫ a) hfac
  have hg : g ≫ i = spMap φ := pullback.lift_fst _ _ _
  have key : (spMap φ).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality]; simp
  have h2 : Function.Injective (spMap φ).appTop := by
    rw [key]
    exact ((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.injective.comp hφ).comp
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
  have hinj : Function.Injective i.appTop := by
    rw [← hg, Scheme.Hom.comp_appTop] at h2
    exact Function.Injective.of_comp h2
  have : IsIso i := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  have hd : d = inv i ≫ pullback.snd _ _ ≫ pullback.diagonal p := by
    rw [← pullback.condition]; simp [i]
  rw [e1, e2, hd]; simp

theorem spMap_injective_cancel : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') :=
  ⟨fun R R' _ _ _ _ φ _ hφ Y a a' h => spec_localInjective_cancel_left R R' φ hφ Y a a' h,
    fun R R' _ _ φ hφ S Y p _ a a' hp h => spec_injective_cancel_left_of_separated R R' φ hφ S Y p a a' hp h⟩

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_injectiveRingMap_cancellation : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') := by
  first | exact @GlobalTheory.Nef.spMap_injective_cancel | exact GlobalTheory.Nef.spMap_injective_cancel | (intros; apply GlobalTheory.Nef.spMap_injective_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueConstantLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueConstantLocalRing
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem comp_grpMul {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (x : T' ⟶ T) (f g : T ⟶ G) :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, Subsingleton.elim (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  have : (η[G] : 𝟙_ (Over S) ⟶ G) ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [comp_grpMul, Category.comp_id, h1, _root_.one_mul]
  exact congrArg (·.left) this

theorem triv_isPath {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (c : R) (b : Sp R ⟶ S) :
    IsPath G c b (triv G b) := by
  refine { base := triv_over G b, zero := ?_, scale := ?_ }
  · rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.constantCoeff (R := R))) = 𝟙 _ := by
      ext x; simp
    rw [this, Spec.map_id, Category.id_comp]
  · rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.rescale c)) = CommRingCat.ofHom (PowerSeries.C (R := R)) := by
      ext x n; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs with h <;> simp [h]
    rw [this, Category.assoc, Category.assoc, unitSec_comp_sqr]

theorem eq_unitSec_of_sqr_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (z : Sp R ⟶ G.left)
    (hz : z ≫ sqr G = z) : z = (z ≫ G.hom) ≫ unitSec G := by
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h : z' * z' = z' := by
    have e := comp_grpMul z' (𝟙 G) (𝟙 G)
    rw [Category.comp_id] at e
    rw [← e]
    ext
    exact hz
  have h1 : z' = 1 := by simpa using h
  have h2 := congrArg (·.left) h1
  rw [Hom.one_def] at h2
  refine h2.trans ?_
  rw [Over.comp_left]
  congr 1

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem triv_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  intro S G _ R _
  refine ⟨fun c b => triv_isPath G c b, fun z hz => eq_unitSec_of_sqr_eq G z hz, ?_⟩
  intro _ hq c hc b ξ hξ
  exact GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees S G R hq c 1 one_pos hc b ξ (triv G b) hξ (triv_isPath G c b)
    (fun _ _ _ _ j hj hj' => absurd hj' (by omega))

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueConstantLocalRingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSquaringPath_unique_constant_localRing : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  first | exact @GlobalTheory.Nef.triv_unique | exact GlobalTheory.Nef.triv_unique | (intros; apply GlobalTheory.Nef.triv_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalingCompatibleExpansionAtInfinity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalingCompatibleExpansionAtInfinity
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def polyScale (c : F) : F[X] →ₐ[F] F[X] := Polynomial.aeval (Polynomial.C c * Polynomial.X)

theorem polyScale_polyScale (c d : F) (p : F[X]) :
    polyScale d (polyScale c p) = polyScale (c * d) p := by
  have : (polyScale d).comp (polyScale c) = polyScale (c * d) := by
    apply Polynomial.algHom_ext
    simp only [polyScale, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, Polynomial.C_mul]
    ring
  exact congrArg (fun φ : F[X] →ₐ[F] F[X] => φ p) this

theorem polyScale_one (p : F[X]) : polyScale (1 : F) p = p := by
  show Polynomial.aeval (Polynomial.C (1 : F) * Polynomial.X) p = p
  rw [map_one, one_mul, Polynomial.aeval_X_left_apply]

theorem polyScale_injective {c : F} (hc : c ≠ 0) : Function.Injective (polyScale c) := by
  intro p q h
  have := congrArg (polyScale c⁻¹) h
  rwa [polyScale_polyScale, polyScale_polyScale, mul_inv_cancel₀ hc, polyScale_one, polyScale_one] at this

theorem rescale_injective {c : F} (hc : c ≠ 0) : Function.Injective (PowerSeries.rescale c) := by
  intro p q h
  have := congrArg (PowerSeries.rescale c⁻¹) h
  rwa [PowerSeries.rescale_rescale, PowerSeries.rescale_rescale, mul_inv_cancel₀ hc,
    PowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply] at this

theorem transcendental_X : Transcendental F (RatFunc.X : RatFunc F) := by
  rw [transcendental_iff_injective]
  intro p q h
  have e : ∀ r : F[X], Polynomial.aeval (RatFunc.X : RatFunc F) r = algebraMap F[X] (RatFunc F) r := by
    intro r
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [e, e] at h
  exact IsFractionRing.injective F[X] (RatFunc F) h

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def ratScale (c : F) (hc : c ≠ 0) : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (algebraMap F[X] (RatFunc F)).comp (polyScale c).toRingHom)
    ((IsFractionRing.injective F[X] (RatFunc F)).comp (polyScale_injective hc))

noncomputable def lsScale (c : F) (hc : c ≠ 0) : LaurentSeries F →+* LaurentSeries F :=
  IsFractionRing.lift (g := (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c))
    ((IsFractionRing.injective (PowerSeries F) (LaurentSeries F)).comp (rescale_injective hc))

noncomputable def ratInv : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹).toRingHom)
    (fun x y h => (transcendental_iff_injective.1 fun h => transcendental_X (IsAlgebraic.inv_iff.1 h)) h)

theorem lsScale_comp (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c) :=
  IsLocalization.lift_comp _

theorem ratScale_alg (c : F) (hc : c ≠ 0) (p : F[X]) :
    ratScale c hc (algebraMap F[X] (RatFunc F) p) = algebraMap F[X] (RatFunc F) (polyScale c p) :=
  IsLocalization.lift_eq _ _

theorem ratInv_alg (p : F[X]) :
    ratInv (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p :=
  IsLocalization.lift_eq _ _

theorem ext_rat {A : Type} [CommRing A] {f g : RatFunc F →+* A}
    (hC : ∀ a, f (RatFunc.C a) = g (RatFunc.C a)) (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors F[X])
  apply Polynomial.ringHom_ext
  · intro a; simpa [RatFunc.algebraMap_C] using hC a
  · simpa [RatFunc.algebraMap_X] using hX

theorem ratScale_C (c : F) (hc : c ≠ 0) (a : F) : ratScale c hc (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratScale_alg]; simp [polyScale]

theorem ratScale_X (c : F) (hc : c ≠ 0) :
    ratScale c hc RatFunc.X = RatFunc.C c * RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratScale_alg]; simp [polyScale, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

theorem ratInv_C (a : F) : ratInv (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratInv_alg]; simp

theorem ratInv_X : ratInv (RatFunc.X : RatFunc F) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, ratInv_alg]; simp

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

theorem alg_C (a : F) : algebraMap (RatFunc F) (LaurentSeries F) (RatFunc.C a) =
    algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.C a) := by
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem alg_X : algebraMap (RatFunc F) (LaurentSeries F) RatFunc.X =
    algebraMap (PowerSeries F) (LaurentSeries F) PowerSeries.X := by
  simp [RatFunc.coe_X]

theorem rescale_C' (c a : F) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  rcases n with _ | n <;> simp

theorem lsScale_rat (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (RatFunc F) (LaurentSeries F)) =
      (algebraMap (RatFunc F) (LaurentSeries F)).comp (ratScale c hc) := by
  have hl : ∀ p, lsScale c hc (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.rescale c p) :=
    fun p => RingHom.congr_fun (lsScale_comp c hc) p
  apply ext_rat
  · intro a
    simp only [RingHom.comp_apply, ratScale_C, alg_C, hl, rescale_C']
  · simp only [RingHom.comp_apply, ratScale_X, map_mul, alg_C, alg_X, hl, PowerSeries.rescale_X,
      rescale_C']

theorem ratInv_ratScale (c : F) (hc : c ≠ 0) :
    ratInv.comp (ratScale c hc) = (ratScale c⁻¹ (inv_ne_zero hc)).comp ratInv := by
  apply ext_rat
  · intro a; simp only [RingHom.comp_apply, ratScale_C, ratInv_C]
  · simp only [RingHom.comp_apply, ratScale_X, ratInv_X, map_mul, ratInv_C, map_inv₀, mul_inv,
      inv_inv]

theorem scaling_expansion_infinity :
    ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  intro F _ _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h2' : (2 : F)⁻¹ ≠ 0 := inv_ne_zero h2
  refine ⟨ratScale 2 h2, (algebraMap (RatFunc F) (LaurentSeries F)).comp ratInv, lsScale 2 h2,
    lsScale 2⁻¹ h2', lsScale_comp 2 h2, lsScale_rat 2 h2, lsScale_comp 2⁻¹ h2', ?_, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, lsScale_rat, RingHom.comp_assoc, RingHom.comp_assoc,
      ratInv_ratScale 2 h2]
  · ext a; simp only [RingHom.comp_apply, ratInv_C, alg_C]
  · ext a; simp only [RingHom.comp_apply, alg_C]

end GlobalTheory.Nef.InfScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalingCompatibleExpansionAtInfinityStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity : ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  first | exact @GlobalTheory.Nef.InfScale.scaling_expansion_infinity | exact GlobalTheory.Nef.InfScale.scaling_expansion_infinity | (intros; apply GlobalTheory.Nef.InfScale.scaling_expansion_infinity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isProper_of_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H],
    IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  intro Ω _ _ H _ hP ξ hξ hrat
  obtain ⟨β, hβ⟩ := hrat
  obtain ⟨σ, j, r₂, rh, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity Ω
  have comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by rw [← Spec.map_comp]; rfl
  have compA : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
      {Z : Scheme.{0}} (h : Sp A ⟶ Z), spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by
    intros; rw [← Category.assoc, comp]
  have canc := (GlobalTheory.T.spec_injectiveRingMap_cancellation).1
  have cancS := (GlobalTheory.T.spec_injectiveRingMap_cancellation).2
  haveI := hP
  haveI : IsSeparated H.hom := inferInstance
  have sqr_hom : sqr H ≫ H.hom = H.hom := Over.w (𝟙 H * 𝟙 H)
  have hi : Function.Injective (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) :=
    IsFractionRing.injective _ _
  have ha : Function.Injective (algebraMap (RatFunc Ω) (LaurentSeries Ω)) := RingHom.injective _
  have hj : Function.Injective j := RingHom.injective _

  have hσ : spMap σ ≫ β = β ≫ sqr H := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [compA, ← h2, ← comp, Category.assoc, hβ, compA, h1, ← compA, hξ.scale, ← Category.assoc,
      ← Category.assoc, hβ]

  have hβb : β ≫ H.hom = spMap RatFunc.C := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, Category.comp_id, comp, comp, h6]
  have hsq : (spMap j ≫ β) ≫ H.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries Ω) (LaurentSeries Ω))) ≫ spMap PowerSeries.C := by
    rw [Category.assoc, hβb, comp, h5]; exact (comp _ _).symm
  have hE : ValuativeCriterion.Existence H.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed H.hom) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) H.hom).1
  let V : ValuativeCommSq H.hom :=
    { R := PowerSeries Ω
      K := LaurentSeries Ω
      i₁ := spMap j ≫ β
      i₂ := spMap PowerSeries.C
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l⟩⟩ := hE V
  have hζ1 : spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ l.l = spMap j ≫ β := l.fac_left
  have hζ2 : l.l ≫ H.hom = spMap PowerSeries.C := l.fac_right
  have hrC : (PowerSeries.rescale (2⁻¹ : Ω)).comp PowerSeries.C = PowerSeries.C := by
    refine RingHom.ext fun x => PowerSeries.ext fun n => ?_
    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with hn
    · subst hn; rw [pow_zero, _root_.one_mul]
    · rw [MulZeroClass.mul_zero]
  have hcc : (PowerSeries.constantCoeff (R := Ω)).comp (PowerSeries.rescale (2⁻¹ : Ω)) =
      PowerSeries.constantCoeff (R := Ω) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      _root_.one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hcC : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, PowerSeries.constantCoeff_C]; rfl

  have hζs : spMap (PowerSeries.rescale (2⁻¹ : Ω)) ≫ l.l = l.l ≫ sqr H := by
    refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hζ2, comp, hrC, sqr_hom, hζ2]
    · rw [compA, ← h3, ← comp, Category.assoc, hζ1, compA, h4, ← compA, hσ, ← Category.assoc,
        ← Category.assoc, hζ1]

  have hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((2⁻¹ : Ω) ^ n - 2) := by
    intro n hn
    rw [isUnit_iff_ne_zero, sub_ne_zero, inv_pow]
    intro h
    have h0 : (2 : Ω) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have e : (2 : Ω) ^ (n + 1) = 1 := by
      calc (2 : Ω) ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
        _ = 2 ^ n * (2 ^ n)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ h0
    have e' : (2 : ℕ) ^ (n + 1) = 1 := by exact_mod_cast e
    have : 1 < (2 : ℕ) ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hz := (GlobalTheory.T.formalSquaringPath_unique_constant_localRing (Sp Ω) H Ω).2.1 (spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l)
    (by rw [Category.assoc, ← hζs, compA, hcc])
  have hzero : spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l = 𝟙 (Sp Ω) ≫ unitSec H := by
    rw [hz, Category.assoc (spMap _) l.l H.hom, hζ2, comp, hcC, show spMap (RingHom.id Ω) = 𝟙 (Sp Ω) from Spec.map_id _]
  have hζt : l.l = triv H (𝟙 (Sp Ω)) :=
    (GlobalTheory.T.formalSquaringPath_unique_constant_localRing (Sp Ω) H Ω).2.2 inferInstance (2⁻¹) hunit (𝟙 _) l.l
      ⟨by rw [Category.comp_id]; exact hζ2, hzero, hζs⟩

  have hβu : β = spMap RatFunc.C ≫ unitSec H := by
    refine canc _ _ j hj _ _ _ ?_
    rw [← hζ1, hζt, triv, Category.id_comp, compA, ← h5, ← compA]
  refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
  · rw [hξ.base, triv_over]
  · rw [← hβ, hβu, compA, h6, triv, Category.id_comp, compA]

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H], IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isProper_of_charZero | exact GlobalTheory.Nef.ratRigid_of_isProper_of_charZero | (intros; apply GlobalTheory.Nef.ratRigid_of_isProper_of_charZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusRationalSquaringPathsRigidCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeEqZeroOfSqDvd
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

namespace RatDilation

theorem coe_comp_C_mul_X {F : Type} [Field F] (a : F) (f : F[X]) :
    ((f.comp (C a * X) : F[X]) : PowerSeries F) = PowerSeries.rescale a (f : PowerSeries F) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
    split_ifs with h <;> simp [h, mul_comm]

theorem natDegree_comp_two {F : Type} [Field F] [CharZero F] (f : F[X]) :
    (f.comp (C (2:F) * X)).natDegree = f.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X _ two_ne_zero, mul_one]

theorem natDegree_eq_zero_of_sq_dvd {F : Type} [Field F] [CharZero F] (f g : F[X]) (hf : f ≠ 0)
    (hc : IsCoprime f g) (h : f.comp (C (2:F) * X) * g ^ 2 = g.comp (C (2:F) * X) * f ^ 2) :
    f.natDegree = 0 := by
  have hd : f ^ 2 ∣ f.comp (C (2:F) * X) := by
    have : f ^ 2 ∣ f.comp (C (2:F) * X) * g ^ 2 := h ▸ dvd_mul_left _ _
    exact (hc.pow).dvd_of_dvd_mul_right this
  have hne : f.comp (C (2:F) * X) ≠ 0 := by
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · exact hf h0
    · have := congrArg natDegree h0
      rw [natDegree_C_mul_X _ two_ne_zero, natDegree_C] at this
      exact one_ne_zero this
  have := natDegree_le_of_dvd hd hne
  rw [natDegree_comp_two, natDegree_pow] at this
  omega

end RatDilation


open RatDilation in
theorem rat_dilation_eq_one (F : Type) [Field F] [CharZero F] (φ : PowerSeries F) (hr : IsRat φ)
    (h0 : PowerSeries.constantCoeff φ = 1) (h2 : PowerSeries.rescale 2 φ = φ ^ 2) : φ = 1 := by
  classical
  obtain ⟨p₀, q₀, hq₀, hpq₀⟩ := hr
  set g := GCDMonoid.gcd p₀ q₀ with hg
  have hg0 : g ≠ 0 := fun h => hq₀ ((gcd_eq_zero_iff _ _).1 h).2
  set p := p₀ / g
  set q := q₀ / g
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd hq₀
  have hp₀ : p₀ = g * p := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm
  have hq₀' : q₀ = g * q := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm
  have hq : q ≠ 0 := by rintro h; rw [h, mul_zero] at hq₀'; exact hq₀ hq₀'
  have hgc : ((g : F[X]) : PowerSeries F) ≠ 0 := by
    rwa [Ne, Polynomial.coe_eq_zero_iff]
  have hpq : (q : PowerSeries F) * φ = (p : PowerSeries F) := by
    rw [hp₀, hq₀', Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc] at hpq₀
    exact mul_left_cancel₀ hgc hpq₀
  have hφ0 : φ ≠ 0 := by
    rintro rfl; simp at h0
  have hp : p ≠ 0 := by
    rintro h
    rw [h, Polynomial.coe_zero] at hpq
    rcases mul_eq_zero.1 hpq with h' | h'
    · exact hq ((Polynomial.coe_eq_zero_iff).1 h')
    · exact hφ0 h'
  have key : p.comp (C (2:F) * X) * q ^ 2 = q.comp (C (2:F) * X) * p ^ 2 := by
    apply Polynomial.coe_inj.1
    have e := congrArg (PowerSeries.rescale (2:F)) hpq
    rw [map_mul, h2, ← RatDilation.coe_comp_C_mul_X, ← RatDilation.coe_comp_C_mul_X] at e
    simp only [Polynomial.coe_mul, Polynomial.coe_pow]
    rw [← e, ← hpq]; ring
  have dq := RatDilation.natDegree_eq_zero_of_sq_dvd q p hq hcop.symm key.symm
  have dp := RatDilation.natDegree_eq_zero_of_sq_dvd p q hp hcop key
  rw [eq_C_of_natDegree_eq_zero dq, eq_C_of_natDegree_eq_zero dp] at hpq
  rw [Polynomial.coe_C, Polynomial.coe_C] at hpq
  have hc := congrArg PowerSeries.constantCoeff hpq
  simp only [map_mul, h0, mul_one, PowerSeries.constantCoeff_C] at hc
  rw [← hc] at hpq
  have ha : (PowerSeries.C (q.coeff 0) : PowerSeries F) ≠ 0 := by
    intro h
    have h0 : PowerSeries.C (q.coeff 0) = PowerSeries.C 0 := by simpa using h
    have h' : q.coeff 0 = 0 := PowerSeries.C_injective h0
    apply hq; rw [eq_C_of_natDegree_eq_zero dq, h', C_0]
  exact mul_left_cancel₀ ha (hpq.trans (mul_one _).symm)

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusRationalSquaringPathsRigidCharZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

namespace SplitTorusRigid

theorem gamma_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (y : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom ((spMap f).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]; rfl

theorem unitSec_chi {S : Scheme.{0}} (X : Type) [AddCommGroup X] (a : X) :
    (unitSec (splitTorus S X)).appTop.hom (Rosenlicht.chi X a) = 1 := by
  have h := SplitTorus.val_one (T := 𝟙_ (Over S)) (S := S) (X := X) a
  rw [SplitTorus.val_eq] at h
  have e : (1 : 𝟙_ (Over S) ⟶ splitTorus S X) = η[splitTorus S X] := by
    rw [Hom.one_def]; simp
  rw [e] at h
  exact h

theorem sqr_chi {S : Scheme.{0}} (X : Type) [AddCommGroup X] (a : X) :
    (sqr (splitTorus S X)).appTop.hom (Rosenlicht.chi X a) = Rosenlicht.chi X a * Rosenlicht.chi X a := by
  have h := SplitTorus.val_mul (𝟙 (splitTorus S X)) (𝟙 _) a
  rw [SplitTorus.val_eq, SplitTorus.val_id] at h
  exact h

end SplitTorusRigid


open SplitTorusRigid in
theorem splitTorus_ratRigid : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Type) [AddCommGroup X],
    RatRigid (splitTorus (Sp Ω) X) (𝟙 (Sp Ω)) := by
  intro Ω _ _ X _ ξ hξ hr
  obtain ⟨β, hβ⟩ := hr
  let φ : X → PowerSeries Ω := fun a =>
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω))).hom.hom (ξ.appTop.hom (Rosenlicht.chi X a))
  have key : ∀ a, φ a = 1 := by
    intro a
    apply rat_dilation_eq_one Ω (φ a)
    · have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries Ω))).hom.hom
        (g.appTop.hom (Rosenlicht.chi X a))) hβ
      rw [appTop_comp_apply, appTop_comp_apply, gamma_spMap, gamma_spMap] at h
      exact (isRat_iff_exists_ratFunc Ω (φ a)).2 ⟨_, h⟩
    · have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
        (g.appTop.hom (Rosenlicht.chi X a))) hξ.zero
      rw [appTop_comp_apply, appTop_comp_apply, gamma_spMap, unitSec_chi, map_one, map_one] at h
      exact h
    · have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω))).hom.hom
        (g.appTop.hom (Rosenlicht.chi X a))) hξ.scale
      rw [appTop_comp_apply, appTop_comp_apply, gamma_spMap, sqr_chi, map_mul, map_mul] at h
      rw [h, sq]
  have hx : ∀ a, ξ.appTop.hom (Rosenlicht.chi X a) = 1 := fun a =>
    (cr_iso_bij (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω)))).1 (by rw [map_one]; exact key a)
  have ht : ∀ a, (triv (splitTorus (Sp Ω) X) (𝟙 (Sp Ω))).appTop.hom (Rosenlicht.chi X a) = 1 := by
    intro a
    simp only [triv, appTop_comp_apply, unitSec_chi, map_one]
  have e := SplitTorus.hom_ext
    (g := (Over.homMk ξ hξ.base : Over.mk (spMap (PowerSeries.C (R := Ω)) ≫ 𝟙 (Sp Ω)) ⟶ splitTorus (Sp Ω) X))
    (g' := Over.homMk (triv (splitTorus (Sp Ω) X) (𝟙 (Sp Ω))) (triv_over _ _))
    (fun a => by rw [SplitTorus.val_eq, SplitTorus.val_eq]; exact (hx a).trans (ht a).symm)
  exact congrArg (·.left) e

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusRationalSquaringPathsRigidCharZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Type) [AddCommGroup X], RatRigid (splitTorus (Sp Ω) X) (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.splitTorus_ratRigid | exact GlobalTheory.Nef.splitTorus_ratRigid | (intros; apply GlobalTheory.Nef.splitTorus_ratRigid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtension
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.TorExt

theorem algebraMap_comp_C (Ω : Type) [Field Ω] :
    (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp RatFunc.C =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp PowerSeries.C := by
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply]
  rw [← RatFunc.algebraMap_C]
  have := RatFunc.coe_coe (Polynomial.C c)
  simp only [Polynomial.coe_C] at this
  exact this.symm

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    unitSec G ≫ f.left = unitSec H := by
  rw [unitSec, unitSec, sec, sec, ← Over.comp_left, IsMonHom.one_hom]

theorem isLocalHom_field {K L : Type} [Field K] [Field L] (φ : K →+* L) : IsLocalHom φ :=
  ⟨fun x hx => by
    by_cases h : x = 0
    · subst h; simp at hx
    · exact IsUnit.mk0 x h⟩

theorem exists_lift {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) {Z : Scheme.{0}}
    (z : Z ⟶ Sp Ω) (f : Z ⟶ G.left) (hf : f ≫ G.hom = z) (hq : letI := E.grpB; f ≫ E.q.left = z ≫ unitSec E.B) :
    letI := E.addCommGroup
    ∃ g : Z ⟶ (splitTorus (Sp Ω) E.X).left, g ≫ E.i.left = f ∧ g ≫ (splitTorus (Sp Ω) E.X).hom = z := by
  letI := E.addCommGroup
  letI := E.grpB
  let f' : Over.mk z ⟶ G := Over.homMk f hf
  have h : f' ≫ E.q = toUnit _ ≫ η := by
    ext
    simp [f', hq, unitSec, sec]
  refine ⟨(E.isKernel.lift f' (toUnit _) h).left, ?_, ?_⟩
  · rw [← Over.comp_left, E.isKernel.lift_fst]
    rfl
  · exact Over.w (E.isKernel.lift f' (toUnit _) h)

theorem mono_i {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) :
    letI := E.addCommGroup
    Mono E.i.left := by
  letI := E.addCommGroup
  letI := E.grpB
  have : Mono E.i := ⟨fun a b hab => E.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  exact Over.mono_left_of_mono _

end GlobalTheory.Nef.TorExt

namespace GlobalTheory.Nef


open TorExt in
theorem ratRigid_of_torusExtension : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (G : Over (Sp Ω)) [GrpObj G],
    Nonempty (TorusExtension G) → RatRigid G (𝟙 (Sp Ω)) := by
  intro Ω _ _ G _ ⟨E⟩ ξ hξ ⟨β, hβ⟩
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI := mono_i E
  haveI := isLocalHom_field (algebraMap (RatFunc Ω) (LaurentSeries Ω))
  obtain ⟨-, bc2⟩ := GlobalTheory.T.formalSquaringPaths_baseChange_and_hom
  obtain ⟨epi1, -⟩ := GlobalTheory.T.spec_injectiveRingMap_cancellation
  set T := splitTorus (Sp Ω) E.X
  set a := algebraMap (RatFunc Ω) (LaurentSeries Ω)
  set ι₀ := algebraMap (PowerSeries Ω) (LaurentSeries Ω)
  have ha : Function.Injective a := a.injective
  have hC : spMap a ≫ spMap RatFunc.C = spMap ι₀ ≫ spMap (PowerSeries.C (R := Ω)) := by
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, algebraMap_comp_C]
  have hq : ξ ≫ E.q.left = spMap (PowerSeries.C (R := Ω)) ≫ unitSec E.B := by
    have := GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero Ω E.B inferInstance (ξ ≫ E.q.left) ((bc2 _ G E.B E.q Ω 2 (𝟙 _) ξ).1 hξ)
      ⟨β ≫ E.q.left, by rw [← Category.assoc, hβ, Category.assoc]⟩
    rw [this, triv, Category.id_comp]
  have hbase : ξ ≫ G.hom = spMap (PowerSeries.C (R := Ω)) := by
    rw [hξ.base, Category.comp_id]
  obtain ⟨ζ, hζ, hζT⟩ := exists_lift E _ ξ hbase hq
  have hβG : β ≫ G.hom = spMap (RatFunc.C (K := Ω)) :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hbase, hC])
  have hβq : β ≫ E.q.left = spMap (RatFunc.C (K := Ω)) ≫ unitSec E.B :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hq, reassoc_of% hC])
  obtain ⟨βT, hβT, -⟩ := exists_lift E _ β hβG hβq
  have hTunit : unitSec T ≫ E.i.left = unitSec G := unitSec_comp E.i
  have hpath : IsPath T 2 (𝟙 _) ζ := by
    refine ⟨by rw [hζT, Category.comp_id], ?_, ?_⟩
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.zero, Category.assoc, hTunit]
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.scale, Category.assoc,
        (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.2, reassoc_of% hζ]
  have hrat : IsRatPath ζ :=
    ⟨βT, by rw [← cancel_mono E.i.left, Category.assoc, hβT, hβ, Category.assoc, hζ]⟩
  have h := GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero Ω E.X ζ hpath hrat
  rw [← hζ, h, (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.1]

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtensionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_torusExtension : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (G : Over (Sp Ω)) [GrpObj G], Nonempty (TorusExtension G) → RatRigid G (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.ratRigid_of_torusExtension | exact GlobalTheory.Nef.ratRigid_of_torusExtension | (intros; apply GlobalTheory.Nef.ratRigid_of_torusExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

theorem GlobalTheory.Nef.RatRigidField.spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

namespace GlobalTheory.Nef

theorem isRatPath_map {F Ω : Type} [Field F] [Field Ω] (φ : F →+* Ω) {Y : Scheme.{0}}
    (ξ : Sp (PowerSeries F) ⟶ Y) (h : IsRatPath ξ) : IsRatPath (spMap (PowerSeries.map φ) ≫ ξ) := by
  obtain ⟨β, hβ⟩ := h
  have hinjP : Function.Injective
      ((algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ)) :=
    (IsFractionRing.injective (PowerSeries Ω) (LaurentSeries Ω)).comp
      (PowerSeries.map_injective φ φ.injective)
  have hinjR : Function.Injective
      ((algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ)) :=
    (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)).comp
      (Polynomial.map_injective φ φ.injective)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LaurentSeries F →+* LaurentSeries Ω, ψ.comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ) :=
    by
    refine ⟨IsFractionRing.lift hinjP, ?_⟩
    ext1 x
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  obtain ⟨ρ, hρ0⟩ : ∃ ρ : RatFunc F →+* RatFunc Ω, ρ.comp (algebraMap (Polynomial F) (RatFunc F)) =
      (algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ) :=
    by
    refine ⟨IsFractionRing.lift hinjR, RingHom.ext fun x => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  have hpol : ((algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ).comp (algebraMap (Polynomial F) (RatFunc F)) =
      (ψ.comp (algebraMap (RatFunc F) (LaurentSeries F))).comp (algebraMap (Polynomial F) (RatFunc F)) := by
    refine RingHom.ext fun p => ?_
    have h1 : ρ (algebraMap (Polynomial F) (RatFunc F) p) =
        algebraMap (Polynomial Ω) (RatFunc Ω) (p.map φ) := by
      have := congrArg (fun f => f p) hρ0
      simpa using this
    have h2 : ψ (algebraMap (PowerSeries F) (LaurentSeries F) (p : PowerSeries F)) =
        algebraMap (PowerSeries Ω) (LaurentSeries Ω) (PowerSeries.map φ (p : PowerSeries F)) :=
      congrArg (fun f => f (p : PowerSeries F)) hψ
    have h3 : PowerSeries.map φ (p : PowerSeries F) = ((p.map φ : Polynomial Ω) : PowerSeries Ω) := by
      ext n; simp [Polynomial.coeff_map]
    have hc : ∀ (K : Type) [Field K] (q : Polynomial K),
        algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) q) =
          algebraMap (PowerSeries K) (LaurentSeries K) (q : PowerSeries K) :=
      fun K _ q => (RatFunc.coe_coe q).symm
    simp only [RingHom.comp_apply]
    rw [h1, hc, hc, h2, h3]
  have hρ : (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ =
      ψ.comp (algebraMap (RatFunc F) (LaurentSeries F)) :=
    IsLocalization.ringHom_ext (M := nonZeroDivisors (Polynomial F)) (S := RatFunc F) hpol
  refine ⟨spMap ρ ≫ β, ?_⟩
  have e1 : spMap (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ≫ spMap ρ =
      spMap ψ ≫ spMap (algebraMap (RatFunc F) (LaurentSeries F)) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hρ]
  have e2 : spMap ψ ≫ spMap (algebraMap (PowerSeries F) (LaurentSeries F)) =
      spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ spMap (PowerSeries.map φ) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hψ]
  rw [← Category.assoc, e1, Category.assoc, hβ, ← Category.assoc, e2, Category.assoc]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem ratRigid_of_field_map (S : Scheme.{0}) (G : Over S) [GrpObj G] (F Ω : Type) [Field F] [Field Ω]
    (φ : F →+* Ω) (b : Sp F ⟶ S) (h : RatRigid G (spMap φ ≫ b)) : RatRigid G b := by
  intro ξ hξ hr
  have hp := ((GlobalTheory.T.formalSquaringPaths_baseChange_and_hom).1 S G F Ω φ 2 1 b ξ hξ).1
  rw [PowerSeries.rescale_one, RingHom.id_comp, map_ofNat] at hp
  have e := h _ hp (isRatPath_map φ ξ hr)
  have hC : (PowerSeries.map φ).comp (PowerSeries.C (R := F)) = (PowerSeries.C (R := Ω)).comp φ := by
    ext1 x; simp
  have ht : spMap (PowerSeries.map φ) ≫ triv G b = triv G (spMap φ ≫ b) := by
    simp only [triv]
    rw [← Category.assoc, ← RatRigidField.spMap_comp, hC, RatRigidField.spMap_comp]
    simp only [Category.assoc]
  exact (GlobalTheory.T.spec_injectiveRingMap_cancellation).1 _ _ (PowerSeries.map φ) (PowerSeries.map_injective φ φ.injective) _ _ _
    (e.trans ht.symm)

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMapStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (F Ω : Type) [Field F] [Field Ω] (φ : F →+* Ω) (b : Sp F ⟶ S), RatRigid G (spMap φ ≫ b) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_field_map | exact GlobalTheory.Nef.ratRigid_of_field_map | (intros; apply GlobalTheory.Nef.ratRigid_of_field_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelian
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G →
    ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  intro S G _ hG F _ _ b
  let Ω := AlgebraicClosure F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hE : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G)) :=
    hG.fibres Ω (spMap (algebraMap F Ω) ≫ b)
  have h1 := GlobalTheory.T.rationalSquaringPathsRigid_of_torusExtension Ω ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G) hE
  have h2 := GlobalTheory.T.rationalSquaringPathsRigid_of_fibre S G Ω (spMap (algebraMap F Ω) ≫ b) h1
  exact GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map S G F Ω (algebraMap F Ω) b h2

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelianStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isSemiAbelian | exact GlobalTheory.Nef.ratRigid_of_isSemiAbelian | (intros; apply GlobalTheory.Nef.ratRigid_of_isSemiAbelian <;> assumption)
end
