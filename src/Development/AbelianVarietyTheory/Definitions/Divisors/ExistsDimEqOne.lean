module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

structure AbVar (K : Type) [Field K] where

  X : Over (Sp K)
  [grp : GrpObj X]
  ab : IsAbelianScheme X

  dim : ℕ
  smooth : SmoothOfRelativeDimension dim X.hom

attribute [instance] AbVar.grp

namespace AbVar

variable {K : Type} [Field K]

instance (A : AbVar K) : IsCommMonObj A.X := A.ab.comm

def homSub (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  mul_mem' := fun {f g} hf hg => by
    have : IsMonHom f := hf
    have : IsMonHom g := hg
    exact inferInstanceAs (IsMonHom (lift f g ≫ μ[B.X]))
  one_mem' := by
    change IsMonHom (1 : A.X ⟶ B.X)
    rw [CategoryTheory.Hom.one_def]
    infer_instance
  inv_mem' := fun {f} hf => by
    have : IsMonHom f := hf
    change IsMonHom (f⁻¹)
    infer_instance

def Hom (A B : AbVar K) : Type := Additive (homSub A B)

def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul (α := homSub A B) f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul (α := homSub A B) f).2

def Hom.mk {A B : AbVar K} (f : A.X ⟶ B.X) [h : IsMonHom f] : Hom A B :=
  Additive.ofMul (α := homSub A B) ⟨f, h⟩

instance : Category (AbVar K) where
  Hom := Hom
  id A := Hom.mk (𝟙 A.X)
  comp f g := Hom.mk (f.hom ≫ g.hom)
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[simp] theorem id_hom (A : AbVar K) : Hom.hom (𝟙 A) = 𝟙 A.X := rfl

@[simp] theorem comp_hom {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) : Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

@[simp] theorem mk_hom {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : (Hom.mk f : Hom A B).hom = f := rfl

instance : Preadditive (AbVar K) where
  homGroup A B := inferInstanceAs (AddCommGroup (Additive (homSub A B)))
  add_comp _ _ _ f f' g := Subtype.ext (MonObj.mul_comp f.hom f'.hom g.hom)
  comp_add _ _ _ f g g' := Subtype.ext (MonObj.comp_mul f.hom g.hom g'.hom)

@[simp] theorem add_hom {A B : AbVar K} (f g : A ⟶ B) : Hom.hom (f + g) = f.hom * g.hom := rfl

@[simp] theorem zero_hom (A B : AbVar K) : Hom.hom (0 : A ⟶ B) = 1 := rfl

@[simp] theorem neg_hom {A B : AbVar K} (f : A ⟶ B) : Hom.hom (-f) = f.hom⁻¹ := rfl

@[simp] theorem nsmul_hom {A B : AbVar K} (n : ℕ) (f : A ⟶ B) : Hom.hom (n • f) = f.hom ^ n := rfl

@[simp] theorem zsmul_hom {A B : AbVar K} (n : ℤ) (f : A ⟶ B) : Hom.hom (n • f) = f.hom ^ n := rfl

def IsIsogeny {A B : AbVar K} (f : A ⟶ B) : Prop := IsFinite f.hom.left ∧ Surjective f.hom.left

def origin (A : AbVar K) : A.X.left :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X).left (IsLocalRing.closedPoint K)


open Classical in
def deg {A B : AbVar K} (f : A ⟶ B) : ℕ := if IsIsogeny f then f.hom.left.finrank B.origin else 0

abbrev End0 (A : AbVar K) : Type := ℚ ⊗[ℤ] End A

def toEnd0 (A : AbVar K) : End A →+* End0 A := Algebra.TensorProduct.includeRight.toRingHom

abbrev Pt (A : AbVar K) : Type := ptOver K (AlgebraicClosure K) ⟶ A.X

abbrev Gal (K : Type) [Field K] : Type := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

def ptMap {A B : AbVar K} (f : A ⟶ B) : A.Pt →* B.Pt :=
  MonoidHom.mk' (fun x => x ≫ f.hom) fun x y => MonObj.mul_comp x y f.hom

@[simp] theorem ptMap_apply {A B : AbVar K} (f : A ⟶ B) (x : A.Pt) : ptMap f x = x ≫ f.hom := rfl

section Tate

variable (l : ℕ) [Fact l.Prime]

abbrev Tl (A : AbVar K) : Type := Tate l A.Pt

abbrev Vl (A : AbVar K) : Type := ℚ_[l] ⊗[ℤ_[l]] Tl l A

def tmap (A B : AbVar K) : (A ⟶ B) →+ (Tl l A →ₗ[ℤ_[l]] Tl l B) :=
  AddMonoidHom.mk' (fun f => Tate.map l (ptMap f)) fun f g =>
    LinearMap.ext fun t => Tate.ext fun n => MonObj.comp_mul (t.lev n) f.hom g.hom

theorem lev_tmap {A B : AbVar K} (f : A ⟶ B) (t : Tl l A) (n : ℕ) :
    (tmap l A B f t).lev n = t.lev n ≫ f.hom := rfl

theorem tmap_comp {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    tmap l A C (f ≫ g) = tmap l B C g ∘ₗ tmap l A B f :=
  LinearMap.ext fun t => Tate.ext fun n => (Category.assoc (t.lev n) f.hom g.hom).symm

theorem tmap_id (A : AbVar K) : tmap l A A (𝟙 A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n => Category.comp_id (t.lev n)

def vmap {A B : AbVar K} (f : A ⟶ B) : Vl l A →ₗ[ℚ_[l]] Vl l B := (tmap l A B f).baseChange ℚ_[l]

def tend (A : AbVar K) : End A →+* Module.End ℤ_[l] (Tl l A) where
  toFun f := tmap l A A f.asHom
  map_one' := tmap_id l A
  map_mul' f g := tmap_comp l g.asHom f.asHom
  map_zero' := map_zero (tmap l A A)
  map_add' f g := map_add (tmap l A A) f.asHom g.asHom

end Tate

def IsCharpoly {A : AbVar K} (f : End A) (P : Polynomial ℤ) : Prop :=
  P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval n = (deg ((n : End A) - f).asHom : ℤ)


open Classical in
def charpoly {A : AbVar K} (f : End A) : Polynomial ℤ := if h : ∃ P, IsCharpoly f P then h.choose else 0

def trace {A : AbVar K} (f : End A) : ℤ := -(charpoly f).nextCoeff


def lam {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) : Pic Y.left :=
  CechPic.pull (x * y).left c - CechPic.pull x.left c - CechPic.pull y.left c

def IsAdj {A B : AbVar K} (c : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (n : ℤ) (h : B ⟶ A) : Prop :=
  n • lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X) = lam c (fst A.X B.X) (snd A.X B.X ≫ h.hom)

def IsAmpleCls {A : AbVar K} (c : Pic A.X.left) : Prop :=
  ∃ (L : LB A.X.left) (hL : L.IsLB), Out.RelAmple A.X L ∧ cls L hL = c

def zero (K : Type) [Field K] : AbVar K where
  X := 𝟙_ (Over (Sp K))
  ab := GlobalTheory.Diag.isAbelianScheme_unit _
  dim := 0
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Sp K)))

def prod (A B : AbVar K) : AbVar K where
  X := A.X ⊗ B.X
  ab := GlobalTheory.SemiProd.isAbelianScheme_tensor A.ab B.ab
  dim := A.dim + B.dim
  smooth := by
    have := A.smooth
    have := B.smooth
    have h : SmoothOfRelativeDimension B.dim (pullback.fst A.X.hom B.X.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := B.dim)).of_isPullback
        (IsPullback.of_hasPullback A.X.hom B.X.hom).flip B.smooth
    have := smoothOfRelativeDimension_comp (n := B.dim) (m := A.dim) (pullback.fst A.X.hom B.X.hom) A.X.hom
    rw [add_comm]
    exact this

def prodFst (A B : AbVar K) : prod A B ⟶ A := Hom.mk (A := prod A B) (fst A.X B.X)
  (h := inferInstanceAs (IsMonHom (fst A.X B.X)))

def prodSnd (A B : AbVar K) : prod A B ⟶ B := Hom.mk (A := prod A B) (snd A.X B.X)
  (h := inferInstanceAs (IsMonHom (snd A.X B.X)))

def prodLift {T A B : AbVar K} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ prod A B :=
  Hom.mk (B := prod A B) (lift f.hom g.hom) (h := inferInstanceAs (IsMonHom (lift f.hom g.hom)))

def baseChange (L : Type) [Field L] [Algebra K L] (A : AbVar K) : AbVar L where
  X := (Over.pullback (spMap (algebraMap K L))).obj A.X
  ab := GlobalTheory.isAbelianScheme_pullback_obj _ A.X A.ab
  dim := A.dim
  smooth := (smoothOfRelativeDimension_isStableUnderBaseChange (n := A.dim)).of_isPullback
    (IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))) A.smooth

def bcMap (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) : baseChange L A ⟶ baseChange L B :=
  Hom.mk (A := baseChange L A) (B := baseChange L B) ((Over.pullback (spMap (algebraMap K L))).map f.hom)
    (h := inferInstanceAs (IsMonHom ((Over.pullback (spMap (algebraMap K L))).map f.hom)))

@[reducible] def algΓ (A : AbVar K) : Algebra K Γ(A.X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.X.hom.appTop).hom.toAlgebra

def inter (A : AbVar K) {J : Type} [Fintype J] (c : J → Pic A.X.left) : ℤ :=
  letI := A.algΓ
  multiDiff c (chiPic K (structureModule A.X.left)) 0

def IsDualPair (A B : AbVar K) (P : LB (A.X ⊗ B.X).left) : Prop :=
  AbDual.IsDual A.X B.X P ∧ AbDual.IsDual B.X A.X (AbDual.swap P)


open GlobalTheory.WeierstrassCurve in
def ell (W : WeierstrassCurve K) [W.IsElliptic] : AbVar K where
  X := (ellPolAV W).A
  ab := (ellPolAV W).isAb
  dim := 1
  smooth := (ellPolAV W).smoothDim



theorem lam_eq {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    lam c x y = CechPic.lam c x y := by
  have h : CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
    rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
    exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
      have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
      rw [this]; exact hV) hc
  rw [lam, CechPic.lam, h, add_zero]

end AbVar

end GlobalTheory.AV
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

structure IsAmb (p : X ⟶ Sp k) : Prop where

  isDomain : IsDomain k

  finite : Module.Finite ℤ k

  isProjOver : IsProjOver p

theorem isAmb_of_isArithVar {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) : IsAmb p :=
  ⟨h.isDomain, h.finite, h.isProjOver⟩

theorem IsAmb.sub {p : X ⟶ Sp k} (h : IsAmb p) (i : Y ⟶ X) [IsClosedImmersion i] : IsAmb (i ≫ p) :=
  ⟨h.isDomain, h.finite, GlobalTheory.isProjOver_comp_of_finite k X Y i p inferInstance h.isProjOver⟩

theorem IsAmb.isNoetherian {p : X ⟶ Sp k} (h : IsAmb p) : IsNoetherian X := by

  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ k)
  exact GlobalTheory.isNoetherian_of_isProjOver h.isProjOver

def HasDim (x : X) (d : ℕ) : Prop := topologicalKrullDim (closure ({x} : Set X)) = d

def clo (x : X) : Scheme.{0} := (exists_isClosedImmersion_genericPoint x).choose

def cloι (x : X) : clo x ⟶ X := (exists_isClosedImmersion_genericPoint x).choose_spec.choose

instance (x : X) : IsClosedImmersion (cloι x) :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose

instance (x : X) : IsIntegral (clo x) :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose_spec.choose

instance [IsLocallyNoetherian X] (x : X) : IsLocallyNoetherian (clo x) :=
  LocallyOfFiniteType.isLocallyNoetherian (cloι x)

theorem cloι_genericPoint (x : X) : cloι x (genericPoint (clo x)) = x :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose_spec.choose_spec

section Val

variable [IsIntegral Y] {q : Y ⟶ Sp k} {e : ℕ}

def mixArch (L : Fin e → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : ℝ :=
  FibreProj.pol (fun n => (comb L n).archInt M e hr) / e.factorial

variable [IsLocallyNoetherian Y]

def recVal (h : Y → ℝ) (L : Fin e → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : ℝ :=
  ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - mixArch L M hr

end Val


open Classical in
def resArch {q : Y ⟶ Sp k} {e : ℕ} (L : Fin e → HermLB q) (N : HermLB q) (t : N.B.Sec) (z : Y) : ℝ :=
  if h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) then
    mixArch (fun a => (L a).restr (cloι z)) (N.restr (cloι z)) (isRatSec_ratOfSec _ h) else 0


open Classical in
def resCyc [IsLocallyNoetherian Y] {B : LB Y} (hB : B.IsLB) (t : B.Sec) (g : Y → ℝ) (z : Y) : ℝ :=
  if h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) then
    ∑ᶠ w, ((divOfSec (LB.isLB_pull hB (cloι z)) _ h).mult w : ℝ) * g (cloι z w) else 0

structure IsMix (p : X ⟶ Sp k) (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) : Prop where

  iso : ∀ (d : ℕ) (L M : Fin d → HermLB p) (x : X), d ≤ m → HasDim x d → (∀ a, (L a).Isometric (M a)) → T d L x = T d M x

  symm : ∀ (d : ℕ) (L : Fin d → HermLB p) (e : Equiv.Perm (Fin d)) (x : X), d ≤ m → HasDim x d →
    T d (fun a => L (e a)) x = T d L x

  add : ∀ (d : ℕ) (A B : HermLB p) (L : Fin d → HermLB p) (x : X), d + 1 ≤ m → HasDim x (d + 1) →
    T (d + 1) (Fin.cons (A.tens B) L) x = T (d + 1) (Fin.cons A L) x + T (d + 1) (Fin.cons B L) x

  zero : ∀ (L : Fin 0 → HermLB p) (x : X), HasDim x 0 → T 0 L x = Real.log (Nat.card (X.residueField x))

  recur : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q) (e : ℕ), e + 1 ≤ m → topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M : HermLB p) (L : Fin e → HermLB p) (M' : HermLB q) (L' : Fin e → HermLB q), (M.pull i hi).Isometric M' →
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r),
      T (e + 1) (Fin.cons M L) (i (genericPoint Y)) = recVal (fun z => T e L (i z)) L' M' hr

theorem isMix_zero (p : X ⟶ Sp k) : IsMix p 0 (fun _ _ x => Real.log (Nat.card (X.residueField x))) := by
  refine ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_, fun _ _ _ => rfl, ?_⟩
  · intros
    omega
  · intros
    omega

def ArchInteg : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e →
  ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr

def ArchRecip : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k)
  (e : ℕ), IsArithVar q (e + 1) → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec)
  (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t),
  (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) →
    mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) +
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z =
      mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) +
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def curvEv (G : V n → Matrix r r ℂ) (v : V n) : Matrix r r (Ev n) := (curvPoly G v).map (MvPolynomial.aeval sym)

def powAt (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Ev n := (curvEv G v ^ k).trace

def transAt (G G' : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Alt n :=
  ∑ a, ∑ i ∈ Finset.range k, ((curvEv G v ^ i *
    (conn G v (coordVec a) - conn G' v (coordVec a)).map (algebraMap ℂ (Ev n)) * curvEv G' v ^ (k - 1 - i)).trace : Ev n) * dz a

end Point

section Minors

variable {s : ℕ}

def leadMinor (G : Matrix (Fin s) (Fin s) ℂ) (j : ℕ) : ℂ :=
  (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).det

def grD (G : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) : ℝ := (leadMinor G (i + 1)).re / (leadMinor G i).re

def ldPart (G : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun i j =>
  (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det / leadMinor G j

end Minors

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

def HolUnitAt (T : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (T y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ a b,
    ∀ᶠ v in 𝓝 (A.e i y), DifferentiableAt ℂ (fun u => T ((A.e i).symm u) a b) v

def SmoothUnitAt (G : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (G y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ᶠ v in 𝓝 (A.e i y), MContDiffAt ∞ (fun u => G ((A.e i).symm u)) v

structure IsGramPair (G G' : M → M → Matrix r r ℂ) : Prop where

  smooth : ∀ y, SmoothUnitAt A (G y) y ∧ SmoothUnitAt A (G' y) y

  trans : ∀ y, ∀ᶠ z in 𝓝 y, ∃ T K K' : M → Matrix r r ℂ, HolUnitAt A T z ∧ HolUnitAt A K z ∧ HolUnitAt A K' z ∧
    ∀ᶠ w in 𝓝 z, G z w = T w * G y w * (K w)ᴴ ∧ G' z w = T w * G' y w * (K' w)ᴴ

def powFld (G : M → M → Matrix r r ℂ) (k : ℕ) (x : A.Pt) : Ev n := powAt (fun v => G x.pt (x.ch.symm v)) x.crd k

def chernFld (G : M → M → Matrix r r ℂ) (j : ℕ) (x : A.Pt) : Ev n := A.chern (G x.pt) j x

def transFld (G G' : M → M → Matrix r r ℂ) (k : ℕ) : A.Fld := fun x =>
  transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k

def DbarCoh (w w' : A.Pt → Ev n) : Prop :=
  A.IsForm (LineForm.fld A w) ∧ A.IsForm (LineForm.fld A w') ∧ A.dbar (LineForm.fld A w) = 0 ∧
    A.dbar (LineForm.fld A w') = 0 ∧ ∃ u, A.IsForm u ∧ LineForm.fld A w - LineForm.fld A w' = A.dbar u

end Manifold

section Variety

variable {F : Type} [Field F] {ι : Type} {m k : ι → ℕ} {X Y : Var F} {σ : F →+* ℂ}

def atlas (X : Var F) (σ : F →+* ℂ) : HolAtlas (CxPts X.str σ) X.dim where
  ι := AlgChart X.str σ X.dim
  e c := c.e
  cover y := have := X.smooth_str; AlgChart.exists_mem_source y
  holo c c' := c.holo_trans c'

structure IsMetricFr (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) : Prop where

  posDef : ∀ y, ∀ A ∈ E.S (under y), ∀ τ, (H A y τ).PosDef

  smooth : ∀ y, ∀ A ∈ E.S (under y), ∀ τ i j, CInfAt (fun z => (H A z τ i j).re) y ∧ CInfAt (fun z => (H A z τ i j).im) y

  trans : ∀ y, ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ τ,
    H A' y τ = (A' * A⁻¹).map (ratVal · y) τ * H A y τ * ((A' * A⁻¹).map (ratVal · y) τ)ᴴ

theorem isMetricFr_of_isMetricOn {E : Fr (ratOf X) m 0} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    (h : IsMetricOn E ⊤ H) : IsMetricFr E H :=
  ⟨fun y => h.posDef y mem_ptsIn_top, fun y => h.smooth y mem_ptsIn_top, fun y => h.trans y mem_ptsIn_top⟩

variable (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

def gramAt (τ : ι) (y z : CxPts X.str σ) : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := H (E.nonempty (under y)).choose z τ

def chernF (x : ι × ℕ) : (atlas X σ).Pt → Ev X.dim := chernFld (atlas X σ) (gramAt E H x.1) x.2

def grF (x : Root m) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => -Real.log (grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2)) p.crd)

def c1W {L : LB X.X} (ψ : Weight X.str σ L) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => ψ.φ (pick ψ.isLB p.pt) (p.ch.symm v)) p.crd)

def ptMap (σ : F →+* ℂ) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) : CxPts Y.str σ → CxPts X.str σ := PtsOver.map f hf _

def pullGram (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (B : Mat m Y.Fn) (z : CxPts Y.str σ) : Mat m ℂ :=
  fun τ => (B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ *
    H (E.nonempty (under (ptMap σ f hf z))).choose (ptMap σ f hf z) τ *
    ((B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ)ᴴ

end Variety

section Inhabitants

end Inhabitants

end GlobalTheory.ChernCalc
end
end
