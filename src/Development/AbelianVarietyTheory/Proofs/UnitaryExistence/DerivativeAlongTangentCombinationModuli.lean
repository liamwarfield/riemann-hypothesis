module

public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
noncomputable section

namespace GlobalTheory.TanDeriv

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.TanMod

def evAt {R : Type} [CommRing R] {Y : Scheme.{0}} (W : Sp R ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U)
    (f : Γ(Y, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((W.appLE U ⊤ h).hom f)

theorem evAt_congr {R : Type} [CommRing R] {Y : Scheme.{0}} {W W' : Sp R ⟶ Y} (e : W = W') (U : Y.Opens)
    (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ W' ⁻¹ᵁ U) (f : Γ(Y, U)) : evAt W U h f = evAt W' U h' f := by
  subst e; rfl

theorem evAt_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ W) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evAt (spMap φ ≫ W) U h' f = φ (evAt W U h f) := by
  have h1 : (spMap φ ≫ W).appLE U ⊤ h' = W.appLE U ⊤ h ≫ (spMap φ).appTop := by
    have : (spMap φ).appTop = (spMap φ).appLE ⊤ ⊤ le_top := (Scheme.Hom.app_eq_appLE (spMap φ))
    rw [this]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) W U ⊤ ⊤ h le_top).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h3 := congrArg (fun ψ => ψ.hom ((W.appLE U ⊤ h).hom f)) h2
  unfold evAt
  rw [h1]
  exact h3

theorem top_le_of_comp {R A : Type} [CommRing R] [CommRing A] (p : R →+* A)
    (hs : Function.Surjective p) (hn : ∀ x, p x = 0 → x * x = 0) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U) : ⊤ ≤ W ⁻¹ᵁ U := by
  intro x _
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap p) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have h3 : a * a ∈ (show PrimeSpectrum R from x).asIdeal := by
      rw [hn a ha]; exact Ideal.zero_mem _
    exact ((show PrimeSpectrum R from x).isPrime.mem_or_mem h3).elim id id
  obtain ⟨y, hy⟩ := hx
  have h4 : (show Sp A from y) ∈ (spMap p ≫ W) ⁻¹ᵁ U := h trivial
  have h5 : spMap p (show Sp A from y) = x := hy
  rw [← h5]
  exact h4

theorem comp_top_le {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U :=
  fun y _ => h (show spMap p y ∈ (⊤ : (Sp R).Opens) from trivial)

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]

theorem snd_evAt_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hu0 : smT x0 0 u = 1) (hv0 : smT x0 0 v = 1)
    (U : G.left.Opens) (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ U)
    (hv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from v.left) ⁻¹ᵁ U)
    (huv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (u * v).left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt (R := DualNumber S) (u * v).left U huv f).snd =
      (evAt (R := DualNumber S) u.left U hu f).snd + (evAt (R := DualNumber S) v.left U hv f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change smT x0 0 u * _ = _
    rw [hu0, _root_.one_mul]
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = v.left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ U := by
    refine top_le_of_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ U ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  rw [← evAt_congr f1 U (comp_top_le _ _ U hP) hu, ← evAt_congr f2 U (comp_top_le _ _ U hP) hv,
    ← evAt_congr f3 U (comp_top_le _ _ U hP) huv, evAt_comp _ _ U hP, evAt_comp _ _ U hP, evAt_comp _ _ U hP]
  simp

variable [IsCommMonObj G]

theorem tan_top_le (U : G.left.Opens)
    (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U) (m : TanSp x0 G) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from m.pt.left) ⁻¹ᵁ U := by
  refine top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ U ?_
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]
  · exact (unit_of_smT_zero x0 _ m.tan).symm ▸ h1

def derivAt (U : G.left.Opens) (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : TanSp x0 G →ₗ[S] S where
  toFun m := (evAt (R := DualNumber S) m.pt.left U (tan_top_le U h1 m) f).snd
  map_add' m n := snd_evAt_mul m.pt n.pt m.tan n.tan U _ _ _ f
  map_smul' a m := by
    have := evAt_comp (epsMul a) (show Sp (DualNumber S) ⟶ G.left from m.pt.left) U (tan_top_le U h1 m)
      (tan_top_le U h1 (a • m)) f
    refine (congrArg TrivSqZeroExt.snd this).trans ?_
    simp [epsMul]

theorem derivAt_sum {m : ℕ} (b : Fin m → TanSp x0 G) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ G.left)
    (hw : w = (∑ i, a i • b i).pt.left) (U : G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (hv : ∀ i, ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (b i).pt.left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (R := DualNumber S) (b i).pt.left U (hv i) f).snd := by
  subst hw
  have h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U :=
    (unit_of_smT_zero x0 _ (∑ i, a i • b i).tan) ▸ comp_top_le _ _ U h
  have key := map_sum (derivAt U h1 f) (fun i => a i • b i) Finset.univ
  simp only [map_smul, smul_eq_mul] at key
  exact key

theorem derivative_tangent_combination_universal_group_eval {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hv0 : ∀ i, IsTanAt x (v i)) (hw : IsCombAt x v a w)
    (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (v i) U (hv i) f).snd := by
  let b : Fin m → TanSp x Xo.univ.t.G := fun i =>
    TanSp.mk (Over.homMk (v i) (hv0 i).1) (smT_zero_of x _ (hv0 i).2)
  refine derivAt_sum b a w ?_ U h hv f
  obtain ⟨u, hu, rfl⟩ := hw
  have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
  subst hub
  rw [List.prod_ofFn, ← TanSp.pt_sum]

end SlopeTestRemainingChoices

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem deriv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  intro E _ _ _ H Dw l Xo S _ x m v a w hv0 hw U h hv f
  exact derivative_tangent_combination_universal_group_eval Xo x v a w hv0 hw U h hv f

end GlobalTheory.TanDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuliStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_tangent_combination_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  first | exact @GlobalTheory.TanDeriv.deriv_comb | exact GlobalTheory.TanDeriv.deriv_comb | (intros; apply GlobalTheory.TanDeriv.deriv_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormCurve

theorem exists_eq_div {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) (z : R) :
    ∃ x y : B, z = algebraMap B R x / algebraMap B R y := by
  obtain ⟨x, r, c, hc, hr, e⟩ := (RingHom.surjective_localRingHom_iff (⊥ : Ideal R)).mp
    (h ⊥ inferInstance) z
  rw [Ideal.mem_bot] at hc hr
  refine ⟨x, r, ?_⟩
  rw [eq_div_iff hr]
  apply mul_left_cancel₀ hc
  rw [← e]
  ring

theorem isIntegrallyClosed_integralClosure {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) : IsIntegrallyClosed (integralClosure B R) := by
  haveI : IsFractionRing (integralClosure B R) R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, e⟩
  exact (isIntegrallyClosed_iff R).mpr fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

theorem finite_integralClosure (k : Type) {B R : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B R) ∧ ∀ [Algebra k R] [IsScalarTower k B R],
      ringKrullDim (B ⧸ RingHom.ker (algebraMap B R)) ≤ 1 → Algebra.trdeg k R ≤ 1 := by
  let A := B ⧸ RingHom.ker (algebraMap B R)
  haveI : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _
  letI : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra
  haveI : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (RingHom.kerLift_injective _)
  haveI : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, by
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩
  constructor
  · haveI := NormFin.finite_integralClosure_of_perfectField k A R R
    haveI : Module.Finite B (integralClosure A R) := Module.Finite.trans A _
    have h' : Module.Finite B ((integralClosure A R).restrictScalars B) := this
    rwa [integralClosure_restrictScalars_of_isIntegral] at h'
  · intro _ _ hd
    haveI : IsScalarTower k A R := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k B R, IsScalarTower.algebraMap_apply k B A,
        ← IsScalarTower.algebraMap_apply B A R]
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
    haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k A).injective
    haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := R), trdeg_eq_zero (R := A) (A := R), add_zero, hs2]
    rw [hs1] at hd
    exact_mod_cast hd

theorem dimensionLEOne_of_injective {k A R : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (g : A →ₐ[k] R)
    (hg : Function.Injective g) (h : Algebra.trdeg k R ≤ 1) : Ring.DimensionLEOne A := by
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  have h1 := (trdeg_le_of_injective g hg).trans h
  rw [hs2] at h1
  have h2 : s ≤ 1 := by exact_mod_cast h1
  have h3 : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hs1]
    exact_mod_cast h2
  exact ⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩

section Scheme

variable {k : Type} [Field k] {X Z : Scheme.{0}}

noncomputable def constHom (s : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top).hom

theorem finiteType_constHom (s : X ⟶ Sp k) [LocallyOfFiniteType s] {U : X.Opens}
    (hU : IsAffineOpen U) : (constHom s U).FiniteType := by
  have h : (s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      le_top
  exact h.comp (.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

theorem appLE_comp_constHom (s : X ⟶ Sp k) (f : Z ⟶ X) (U : X.Opens) (V : Z.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.comp (constHom s U) = constHom (f ≫ s) V := by
  rw [constHom, constHom, ← Scheme.Hom.appLE_comp_appLE f s ⊤ U V le_top e]
  rfl

theorem isField_sections [IsIntegral Z] [Subsingleton Z] (V : Z.Opens) [hV : Nonempty V] :
    IsField Γ(Z, V) := by
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => IsUnit.exists_right_inv ?_⟩
  refine Z.toRingedSpace.isUnit_of_isUnit_germ V a fun x hx => ?_
  have h : Z.basicOpen a ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff a).mp h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h
  rw [Subsingleton.elim y x] at hy
  exact (Z.mem_basicOpen a x hx).mp hy

theorem isAffineOpen_of_subsingleton [IsAffine Z] [Subsingleton Z] (V : Z.Opens)
    [hV : Nonempty V] : IsAffineOpen V := by
  obtain ⟨y, hy⟩ := hV
  have : V = ⊤ := eq_top_iff.mpr fun x _ => Subsingleton.elim y x ▸ hy
  rw [this]
  exact isAffineOpen_top Z

variable [IsIntegral Z] [Subsingleton Z] [IsAffine Z] (f : Z ⟶ X) [SurjectiveOnStalks f]

theorem surjectiveOnStalks_appLE {U : X.Opens} (hU : IsAffineOpen U) (V : Z.Opens) [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.SurjectiveOnStalks :=
  HasRingHomProperty.appLE @SurjectiveOnStalks f inferInstance ⟨U, hU⟩
    ⟨V, isAffineOpen_of_subsingleton V⟩ e

variable [QuasiCompact f] [QuasiSeparated f]

theorem isFinite_fromNormalization [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s] :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    by_cases hne : Nonempty (f ⁻¹ᵁ U)
    · letI := (isField_sections (f ⁻¹ᵁ U)).toField
      letI := (constHom s U).toAlgebra
      haveI : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU
      refine (finite_integralClosure k ?_).1
      have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
      rwa [← Scheme.Hom.app_eq_appLE] at this
    · have : f ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      have : Subsingleton Γ(Z, f ⁻¹ᵁ U) := by rw [this]; infer_instance
      infer_instance
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr h)

theorem isIntegrallyClosed_stalk (y : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization y)) isOpen_univ
  have hy : y ∈ f.fromNormalization ⁻¹ᵁ U := hyU
  have hne : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    refine ⟨⟨z, ?_⟩⟩
    rw [← f.toNormalization_fromNormalization]
    exact hz
  letI := (f.app U).hom.toAlgebra
  have h1 : IsIntegrallyClosed (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    letI := (isField_sections (f ⁻¹ᵁ U)).toField
    refine isIntegrallyClosed_integralClosure ?_
    have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have h2 : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have hV := hU.preimage f.fromNormalization
  haveI : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
  letI := f.normalization.presheaf.algebra_section_stalk (⟨y, hy⟩ : f.fromNormalization ⁻¹ᵁ U)
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization (R := Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) _
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

theorem isDedekindDomain_sections [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hd : letI := (constHom (f ≫ s) ⊤).toAlgebra; Algebra.trdeg k Γ(Z, ⊤) ≤ 1)
    (U : f.normalization.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] :
    IsDedekindDomain Γ(f.normalization, U) := by
  haveI := isFinite_fromNormalization f s
  letI := (constHom (f ≫ s) ⊤).toAlgebra
  letI := (constHom (f.fromNormalization ≫ s) U).toAlgebra
  haveI : Algebra.FiniteType k Γ(f.normalization, U) := finiteType_constHom _ hU
  have e : ⊤ ≤ f.toNormalization ⁻¹ᵁ U := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
    exact fun x _ => Subsingleton.elim z x ▸ hz
  have hc := appLE_comp_constHom (f.fromNormalization ≫ s) f.toNormalization U ⊤ e
  rw [f.toNormalization_fromNormalization_assoc] at hc
  let g : Γ(f.normalization, U) →ₐ[k] Γ(Z, ⊤) :=
    { (f.toNormalization.appLE U ⊤ e).hom with commutes' := fun a => congr($hc a) }
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have h : f.normalization.basicOpen a ≠ ⊥ := fun h => h0 ((basicOpen_eq_bot_iff a).mp h)
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.normalization.basicOpen a).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h)
    have h1 : z ∈ Z.basicOpen (f.toNormalization.appLE U ⊤ e a) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨trivial, hz⟩
    have ha' : f.toNormalization.appLE U ⊤ e a = 0 := ha
    rw [ha', Scheme.basicOpen_zero] at h1
    exact h1
  exact { Algebra.FiniteType.isNoetherianRing k _, dimensionLEOne_of_injective g hg hd,
    isIntegrallyClosed_sections_of_stalks (isIntegrallyClosed_stalk f) hU with }

end Scheme

end GlobalTheory.NormCurve
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_eigen_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  intro E _ _ _ H l c S _ _ N _ _ ρ m
  classical
  have hσ₀ : Function.Injective (fun τ : E →+* ℂ => embK c τ) := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective
      (RingHom.ext fun a => by
        have h1 := embK_coe c τ a
        have h2 := embK_coe c τ' a
        have h3 : embK c τ a = embK c τ' a := RingHom.congr_fun h a
        exact h1.symm.trans ((congrArg _ h3).trans h2))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => (algebraMap c.F S).comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) (algebraMap c.F S) (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map (algebraMap c.F S))
  have hI := EigenSplit.isInternal_eigenSub hσ ρ
  let A := fun τ : E →+* ℂ => EigenSplit.eigenSub ρ ((algebraMap c.F S).comp (embK c τ))
  have hsum : ∀ x : DirectSum _ (fun τ => A τ), DirectSum.coeAddMonoidHom A x = ∑ τ, (x τ : N) :=
    fun x => by
      conv_lhs => rw [← DirectSum.sum_univ_of x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, DirectSum.coeAddMonoidHom_of]
  obtain ⟨x, hx⟩ := hI.2 m
  refine ⟨fun τ => x τ, ⟨fun τ a => EigenSplit.mem_eigenSub.1 (x τ).2 a, (hsum x).symm.trans hx⟩, ?_⟩
  rintro f ⟨hf, hm⟩
  let y : DirectSum _ (fun τ => A τ) :=
    DFinsupp.equivFunOnFintype.symm fun τ => ⟨f τ, EigenSplit.mem_eigenSub.2 (hf τ)⟩
  have hy : y = x := hI.1 (((hsum y).trans hm).trans hx.symm)
  funext τ
  rw [← hy]
  rfl

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  first | exact @GlobalTheory.Frames.existsUnique_eigen_sum | exact GlobalTheory.Frames.existsUnique_eigen_sum | (intros; apply GlobalTheory.Frames.existsUnique_eigen_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PerFrLact
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerGam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma perFr_lact (X : Data E r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hm : ∀ t : X.Ψ, mat (lact γ x) t = (γ : Matrix (Fin r) (Fin r) E).map t.1 * mat x t := fun _ => rfl
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  unfold perFr
  simp only [hm, GlobalTheory.PerMove.emb_mulVec]
  split_ifs
  · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _),
      Matrix.mul_one]
  · rfl
  · rw [GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl

omit [IsCMField E] in
lemma exists_equiv (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) :
    ∃ f : Λ ≃ₗ[𝓞 E] Λ, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), (hγ _).1 a.2⟩
            invFun := fun a => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E),
              (hγ _).2 (by rw [hri]; exact a.2)⟩
            map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun a => Subtype.ext (hli _)
            right_inv := fun a => Subtype.ext (hri _) }, fun _ => rfl⟩

end GlobalTheory.PerGam

namespace GlobalTheory

theorem per_gam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ γ ∈ (M.X k).Γ, ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La, ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) ∧ ∀ x ∈ (M.X k).dom, ∀ a, Pf (lact γ x) (gam a) = Pf x a := by
  intro E _ _ _ H Dw l Xo c σ g e F r M _ hB _ k Pf hP γ hγ
  obtain ⟨⟨hU, hS⟩, hM, hA⟩ := (hB.gam k γ).1 hγ
  obtain ⟨f, hf⟩ := PerGam.exists_equiv _ γ hS
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (f.trans (M.φ k).symm)
  have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    rw [← hf]
    simp [gam]
  have key : ∀ (n : ℕ) (a b : (F.Di k).La),
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + n • (M.φ k b : Fin r → E) → gam a = a + n • b := by
    intro n a b h
    apply (M.φ k).injective
    apply Subtype.ext
    rw [hg, h, map_add (f := _), map_nsmul]
    rfl
  refine ⟨gam, ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩, fun x _ a => ?_⟩
  · have h1 := hB.ef k (gam a) (gam b)
    rw [hg, hg, hU, ← hB.ef k a b] at h1
    exact_mod_cast h1
  · obtain ⟨b, hb⟩ := hM a ha
    exact ⟨b, key _ a b hb⟩
  · obtain ⟨b, hb⟩ := hA a
    exact ⟨b, key _ a b hb⟩
  · funext j
    rw [hP, hP, hg, PerGam.perFr_lact _ γ hU]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := by simp [cc]
theorem cc_mul' (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]
theorem cc_neg' (x : E) : cc (-x) = -cc x := by simp [cc]
theorem cc_zero' : cc (0 : E) = 0 := by simp [cc]
theorem cc_cc' (x : E) : cc (cc x) = x := by simp [cc]
theorem cc_sum' {ι : Type} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]

theorem herm_add_l (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_add_r (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp [herm, cc_add', mul_add, Finset.sum_add_distrib]

theorem herm_comb_l (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (y : Fin r → E) : herm G (∑ a, c a • e a) y = ∑ a, c a * herm G (e a) y := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_comb_r (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (x : Fin r → E) : herm G x (∑ a, c a • e a) = ∑ a, cc (c a) * herm G x (e a) := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cc_sum', cc_mul', Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_swap (X : Data E r) (x y : Fin r → E) : herm X.Gm x y = cc (herm X.Gm y x) := by
  simp only [herm, cc_sum', cc_mul', cc_cc', X.Gm_herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem herm_nondeg (X : Data E r) (w : Fin r → E) (h : ∀ v, herm X.Gm v w = 0) : w = 0 := by
  have h1 : X.Gm *ᵥ (fun b => cc (w b)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    simpa [herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det h1
  funext b
  have h3 : cc (w b) = 0 := congrFun h2 b
  rw [← cc_cc' (w b), h3, cc_zero']
  rfl

theorem zMatE_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (v : Fin r → E) :
    FJ.zMatE X e β *ᵥ v = v + ∑ a, (∑ b, β a b * herm X.Gm v (e b)) • e a := by
  funext k
  simp only [FJ.zMatE, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => ?_
  ring

theorem zMatE_zero (X : Data E r) (e : Fin ρ → Fin r → E) : FJ.zMatE X e 0 = 1 := by
  ext k l
  simp [FJ.zMatE, Matrix.one_apply]

theorem zMatE_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X cu.e (β + β') = FJ.zMatE X cu.e β * FJ.zMatE X cu.e β' := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec]
  simp only [zMatE_mulVec, herm_add_l, herm_comb_l, cu.iso, mul_zero, Finset.sum_const_zero,
    add_zero, Matrix.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
  abel

theorem zMatE_unitary (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) (u v : Fin r → E) :
    herm X.Gm (FJ.zMatE X cu.e β *ᵥ u) (FJ.zMatE X cu.e β *ᵥ v) = herm X.Gm u v := by
  simp only [zMatE_mulVec, herm_add_l, herm_add_r, herm_comb_l, herm_comb_r, cu.iso, mul_zero,
    Finset.sum_const_zero, add_zero, cc_sum', cc_mul', hβ _ _, ← herm_swap, Finset.sum_mul]
  rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  ring

theorem zMatE_injective (X : Data E r) (cu : FJ.CuspFD X ρ) :
    Function.Injective (FJ.zMatE X cu.e) := by
  intro β β' h
  have h1 : ∀ v a, ∑ b, β a b * herm X.Gm v (cu.e b) = ∑ b, β' a b * herm X.Gm v (cu.e b) := by
    intro v a
    have h2 := congrArg (· *ᵥ v) h
    simp only [zMatE_mulVec, add_right_inj] at h2
    exact Fintype.linearIndependent_iffₛ.1 cu.ind _ _ h2 a
  ext a b
  have h3 : ∑ b, cc (β a b - β' a b) • cu.e b = 0 := by
    refine herm_nondeg X _ fun v => ?_
    simp only [herm_comb_r, cc_cc', sub_mul, Finset.sum_sub_distrib, h1 v a, sub_self]
  have h4 : cc (β a b - β' a b) = 0 := Fintype.linearIndependent_iff.1 cu.ind _ h3 b
  rw [← sub_eq_zero, ← cc_cc' (β a b - β' a b), h4, cc_zero']

def zGamSub (X : Data E r) (cu : FJ.CuspFD X ρ) : AddSubgroup (Matrix (Fin ρ) (Fin ρ) E) where
  carrier := FJ.zGam X cu
  zero_mem' := ⟨fun a b => by simp [cc_zero'], 1, X.Γ.one_mem, by simp [zMatE_zero]⟩
  add_mem' := by
    rintro β β' ⟨h, γ, hγ, e⟩ ⟨h', γ', hγ', e'⟩
    refine ⟨fun a b => ?_, γ * γ', X.Γ.mul_mem hγ hγ', ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, cc_add', h, h']; ring
    · rw [zMatE_add, ← e, ← e', Units.val_mul]
  neg_mem' := by
    rintro β ⟨h, γ, hγ, e⟩
    refine ⟨fun a b => ?_, γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    · rw [Matrix.neg_apply, Matrix.neg_apply, cc_neg', h]
    · refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [e, ← zMatE_add, add_neg_cancel, zMatE_zero]

end GlobalTheory.CuspCentre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpMulThetaCharAutomorphy
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaAH

variable {g : ℕ}

private lemma intCast_dotProduct' (k m : Fin g → ℤ) :
    ((k ⬝ᵥ m : ℤ) : ℂ) = (fun i => (k i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) := by
  simp [dotProduct]

theorem _root_.GlobalTheory.ThetaAH.thetaChar_add_period {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (a b w : Fin g → ℂ)
    (m n : Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b (w + ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))) =
      Complex.exp (Real.pi * Complex.I * (2 * (a ⬝ᵥ fun i => (m i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ b)
        - ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ w))) *
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  rw [← (Equiv.subRight n).tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  set N : Fin g → ℂ := fun i => (n i : ℂ)
  set M : Fin g → ℂ := fun i => (m i : ℂ)
  set K : Fin g → ℂ := fun i => (k i : ℂ)
  have hc : (fun i => (((Equiv.subRight n k) i : ℤ) : ℂ)) = K - N := by
    funext i; simp [K, N]
  have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hs.eq]
  rw [hc, ← Complex.exp_add]
  have key : Real.pi * Complex.I * ((K - N + a) ⬝ᵥ τ *ᵥ (K - N + a)) +
      2 * Real.pi * Complex.I * ((K - N + a) ⬝ᵥ (w + (M + τ *ᵥ N) + b)) =
      Real.pi * Complex.I * (2 * (a ⬝ᵥ M) - 2 * (N ⬝ᵥ b) - (N ⬝ᵥ τ *ᵥ N) - 2 * (N ⬝ᵥ w)) +
      (Real.pi * Complex.I * ((K + a) ⬝ᵥ τ *ᵥ (K + a)) +
        2 * Real.pi * Complex.I * ((K + a) ⬝ᵥ (w + b))) +
      (((k ⬝ᵥ m - n ⬝ᵥ m : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) := by
    have h1 := hsym N (K + a)
    push_cast
    rw [intCast_dotProduct', intCast_dotProduct']
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct, dotProduct_add,
      add_dotProduct] at h1 ⊢
    linear_combination (-(Real.pi * Complex.I)) * h1
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem _root_.GlobalTheory.ThetaAH.hermForm_pullback (h B : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (hᵀ * B * h.map (starRingEnd ℂ)) z w = (h *ᵥ z) ⬝ᵥ B *ᵥ star (h *ᵥ w) := by
  have hs : h.map (starRingEnd ℂ) *ᵥ star w = star (h *ᵥ w) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

private lemma inv_im_transpose_eq_and_mul_eq_one (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef) :
    (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)))ᵀ =
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) ∧
    ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *
      (τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) = 1 := by
  have hdet : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.mpr hY.det_pos.ne'
  constructor
  · rw [← Matrix.transpose_map]
    congr 1
    have := hY.isHermitian.inv
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · have := Matrix.nonsing_inv_mul _ hdet
    have h2 := congrArg (fun A => A.map (Complex.ofRealHom)) this
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2

private lemma re_quadratic_sub_hermitian_eq_im_form (S : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (Real.pi / 2 * (v ⬝ᵥ (S.map (fun x : ℝ => (x : ℂ)) *ᵥ v))).re +
      (Real.pi / 2 * (v ⬝ᵥ (S.map (fun x : ℝ => (x : ℂ)) *ᵥ v))).re
      + -Real.pi * (v ⬝ᵥ S.map (fun x : ℝ => (x : ℂ)) *ᵥ star v).re =
      -2 * Real.pi * ((fun i => (v i).im) ⬝ᵥ (S *ᵥ fun i => (v i).im)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

private lemma star_lattice_vector_eq (τ : Matrix (Fin g) (Fin g) ℂ) (m n : Fin g → ℤ) :
    star ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) =
      ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) -
        (2 * Complex.I) • ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ (fun i => (n i : ℂ))) := by
  funext i
  apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum] <;> ring

theorem _root_.GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (q : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) → (∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z)))) → (∀ z, ‖Complex.exp (q z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) = Real.exp (-2 * Real.pi * ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) ∧ ∀ (lam : Fin g → ℂ) (m n : Fin g → ℤ), h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) → ∃ χ : ℂ, ‖χ‖ = 1 ∧ ∀ z, Complex.exp (q (z + lam)) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) = χ * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z lam + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm lam lam) * (Complex.exp (q z) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ z)) := by
  intro g τ h Hm c₁ c₂ q hs hY hc₁ hc₂ hHm hq
  obtain ⟨hST, hSY⟩ := inv_im_transpose_eq_and_mul_eq_one τ hY
  set S : Matrix (Fin g) (Fin g) ℂ := ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) with hSdef
  have hSsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ S *ᵥ y = y ⬝ᵥ S *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hST]
  refine ⟨fun z => ?_, fun lam m n hlam => ?_⟩
  · rw [hq, hHm, _root_.GlobalTheory.ThetaAH.hermForm_pullback, Complex.norm_exp, sq, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    exact re_quadratic_sub_hermitian_eq_im_form _ (h *ᵥ z)
  set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
  set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
  have him : ∀ c : Fin g → ℂ, (∀ i, c i = 0 ∨ c i = 1 / 2) → (c ⬝ᵥ M).im = 0 ∧ (N ⬝ᵥ c).im = 0 := by
    intro c hc
    constructor
    · simp only [dotProduct, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hc i with h0 | h0 <;> simp [h0, M]
    · simp only [dotProduct, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hc i with h0 | h0 <;> simp [h0, N]
  refine ⟨Complex.exp (Real.pi * Complex.I * (M ⬝ᵥ N + 2 * (c₁ ⬝ᵥ M) - 2 * (N ⬝ᵥ c₂))), ?_,
    fun z => ?_⟩
  · have hMN : (M ⬝ᵥ N).im = 0 := by
      simp [dotProduct, Complex.im_sum, M, N]
    rw [Complex.norm_exp, Real.exp_eq_one_iff]
    simp [Complex.mul_re, hMN, (him c₁ hc₁).1, (him c₂ hc₂).2]
  obtain ⟨v, hv⟩ : ∃ v, h *ᵥ z = v := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, h *ᵥ lam = μ := ⟨_, rfl⟩
  rw [hμ] at hlam
  have hstar : star μ = μ - (2 * Complex.I) • ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ N) := by
    rw [hlam]; exact star_lattice_vector_eq τ m n
  have hSYN : S *ᵥ ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ N) = N := by
    rw [Matrix.mulVec_mulVec, hSY, Matrix.one_mulVec]
  have hSstar : S *ᵥ star μ = S *ᵥ μ - (2 * Complex.I) • N := by
    rw [hstar, Matrix.mulVec_sub, Matrix.mulVec_smul, hSYN]
  have f1 : v ⬝ᵥ S *ᵥ star μ = v ⬝ᵥ S *ᵥ μ - 2 * Complex.I * (v ⬝ᵥ N) := by
    rw [hSstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have f2 : μ ⬝ᵥ S *ᵥ star μ = μ ⬝ᵥ S *ᵥ μ - 2 * Complex.I * (μ ⬝ᵥ N) := by
    rw [hSstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have f3 : μ ⬝ᵥ N = M ⬝ᵥ N + N ⬝ᵥ τ *ᵥ N := by
    rw [hlam, add_dotProduct, dotProduct_comm (τ *ᵥ N)]
  have f4 : (v + μ) ⬝ᵥ S *ᵥ (v + μ) = v ⬝ᵥ S *ᵥ v + 2 * (v ⬝ᵥ S *ᵥ μ) + μ ⬝ᵥ S *ᵥ μ := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hSsym μ v]
    ring
  have f5 : N ⬝ᵥ v = v ⬝ᵥ N := dotProduct_comm _ _
  have htheta : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) =
      Complex.exp (Real.pi * Complex.I * (2 * (c₁ ⬝ᵥ M) - 2 * (N ⬝ᵥ c₂) - (N ⬝ᵥ τ *ᵥ N)
        - 2 * (N ⬝ᵥ v))) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ v := by
    rw [Matrix.mulVec_add, hv, hμ, hlam]
    exact _root_.GlobalTheory.ThetaAH.thetaChar_add_period hs c₁ c₂ v m n
  rw [htheta, hq (z + lam), hq z, hHm, _root_.GlobalTheory.ThetaAH.hermForm_pullback,
    _root_.GlobalTheory.ThetaAH.hermForm_pullback, Matrix.mulVec_add, hv, hμ,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  linear_combination (Real.pi / 2) * f4 - Real.pi * f1 - (Real.pi / 2) * f2 +
    (Real.pi * Complex.I) * f3 - (2 * Real.pi * Complex.I) * f5

end GlobalTheory.ThetaAH
end
