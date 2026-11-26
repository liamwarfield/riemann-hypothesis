module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.LPdCut
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.IntOne
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

structure Steps : Prop where
  offEx : OffEx
  pairs : Pairs
  pn : PnFacts
  hyp : HypEmb
  cov : FinCov
  fib : FinFib
  comps : Comps
  ring : RingL
  lowT : LowTL
  ptVan : PtVanT
  low : LowL
  tower : TowerL
  aff : AffVan
  twBij : TwBij
  gysT : GysTL
  gys0 : GysinCondition
  qEasy : QEasy
  lim : LimOnto
  qOnto : QOnto
  qProj : QProj
  kunBij : KunBij
  kun : KunL
  swap : Swap
  slice : Slice
  ptInt : PtInt
  detect : DetectL
  dual : DualL
  supp : FinSupp
  cls : PnCls
  inj : InjL
  trComp : TrComp
  div : DivL
  basis : BasisOne
  top : TopPart

namespace Steps
variable (H : Steps) (hI : In) (hT : TrIn) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0)
include H hI hl

theorem low' : Low l k := H.low hI H.ptVan l k hl (H.ring hI l) (H.lowT hI l k hl)

theorem gysQ : Nonempty (GysQ k l) := by
  obtain ⟨G⟩ := H.gys0 hI H.twBij l k hl (H.tower hI l k hl) (H.gysT hI H.offEx k)
  obtain ⟨h1, h2, h3⟩ := H.qEasy l k G
  exact ⟨⟨fun h _ _ hn => G.q h hn, h1, H.qOnto hI H.lim l k hl G, h2, h3, H.qProj hI l k G⟩⟩

theorem kun' (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) : Kun l k d p :=
  H.kun l k d p (H.kunBij hI l k hl (H.ring hI l) d p hp)

theorem int_pt (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0) (hΛ : IsInt l p lam (add_zero _) Λ) (y : Pt p) :
    pb l y.1 0 (Λ (G.diag d p)) = lam (G.pt d y) • oneV l (S k) := by
  rw [H.ptInt l k hl d p hp (H.ring hI l) (H.low' hI l k hl) (H.kun' hI l k hl d p hp) lam Λ hΛ y,
    H.slice H.pairs l k hl d p hp (H.ring hI l) G y]

theorem int_one (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0)
    (hΛ : IsInt l p lam (add_zero _) Λ) : Λ (G.diag d p) = oneV l X := by
  rw [← sub_eq_zero]
  refine (H.low' hI l k hl).pts p hp.1 _ fun y => ?_
  rw [map_sub, H.int_pt hI l k hl G d p hp lam Λ hΛ y, h1, one_smul,
    (H.ring hI l).one_nat y.1 (LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)), sub_self]

include hT

theorem pt_ne (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ y : Pt p, G.pt d y ≠ 0 := by
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have := hp.1
  obtain ⟨t, U, z, hU, hz, hzU⟩ := H.cls hI H.pn H.hyp H.offEx l k hl hR hL (fun j d n hn => by
    have : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact H.aff hI H.ptVan k (l ^ j) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) d n 0 hn) ⟨G⟩ d
  obtain ⟨π, hπ, hf, hs⟩ := H.cov k d p hp hP hX
  obtain ⟨s, hs'⟩ := H.fib k p _ π hπ hf t U hU
  have hinj := H.inj hT l π hf hs (H.pn k d).2.1 (H.pn k d).2.2.1
    (LPdCut.unit_of (PNto k d) (isUnit_iff_ne_zero.2 hl)) (2 * d)
  have h0 : pb l (π ⁻¹ᵁ U).ι _ (pb l π (2 * d) z) = 0 := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply, hzU, map_zero]
  have hm := H.supp H.offEx H.pairs l k hl hR hL G d p inferInstance hp.2 s _ hs' _ h0
  by_contra hc
  have hc' : ∀ y : Pt p, G.pt d y = 0 := fun y => by_contra fun h => hc ⟨y, h⟩
  rw [Submodule.span_eq_bot.2 (by rintro _ ⟨y, rfl⟩; exact hc' y), Submodule.mem_bot] at hm
  exact hz (hinj (hm.trans (map_zero _).symm))

theorem tr_int (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam ≠ 0 ∧ ∀ y : Pt p, lam (G.pt d y) = 1 := by
  have hL := H.low' hI l k hl
  obtain ⟨y, hy⟩ := H.pt_ne hI hT l k hl G d p hp hP hX
  obtain ⟨lam, hlam⟩ : ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam (G.pt d y) = 1 := by
    obtain ⟨f, hf⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ_[l] _).1 hy)
    exact ⟨(f (G.pt d y))⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  refine ⟨lam, fun h => by simp [h] at hlam, fun y' => ?_⟩
  obtain ⟨Λ, hΛ⟩ := (H.kun' hI l k hl d p hp).int lam 0 (2 * d) (add_zero _)
  have h := hL.conn p hp.1 inferInstance (Λ (G.diag d p)) y y'
  rw [H.int_pt hI l k hl G d p hp lam Λ hΛ, H.int_pt hI l k hl G d p hp lam Λ hΛ, hlam] at h
  exact ((hL.line _).unique h rfl)

theorem detect' (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) : Detect l d X lam :=
  H.detect l k hl d p hp (H.ring hI l) (H.kun' hI l k hl d p hp) lam (G.diag d p)
    (H.swap H.pairs l k hl d p hp (H.ring hI l) G) (H.int_one hI l k hl G d p hp lam h1)

omit hl [IsAlgClosed k] in
theorem qDual : QDual := by
  intro l _ k _ _ hl d X p hp hP hX
  obtain ⟨G⟩ := H.gysQ hI l k hl
  obtain ⟨lam, h0, h1⟩ := H.tr_int hI hT l k hl G d p hp hP hX
  exact H.dual l k hl d p hp hX (H.ring hI l) (H.low' hI l k hl) lam (H.detect' hI hT l k hl G d p hp lam h1) h0

end Steps

theorem Detect.finite {l : ℕ} [Fact l.Prime] {d : ℕ} {X : Scheme.{0}} {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]}
    (h : Detect l d X lam) (n : ℤ) : FiniteDimensional ℚ_[l] (V l X n) := by
  classical
  obtain ⟨s, c, a, h⟩ := h
  refine FiniteDimensional.of_injective (LinearMap.pi fun t : Fin s =>
    if hn : n + c t = 2 * d then lam ∘ₗ (cupV l X hn).flip (a t) else 0) ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
  refine h n x fun t hn => ?_
  have := congrFun hx t
  simpa [dif_pos hn] using this

theorem Steps.qDiag (H : Steps) (hI : In) (hT : TrIn) : QDiag := by
  intro l _ k _ _ hl d X p hp hP W E π i r c hpb hi hr U hU e he hPB
  obtain ⟨G⟩ := H.gysQ hI l k hl
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have hK := H.kun' hI l k hl _ p hp
  have := hp.1
  obtain ⟨lam, h1⟩ := H.trComp H.comps H.offEx H.pairs l k hl hR G (d + 1) (fun p hp hP hX => by
    obtain ⟨lam, -, h⟩ := H.tr_int hI hT l k hl G _ p hp hP hX
    exact ⟨lam, h⟩) p hp hP
  have hD := H.detect' hI hT l k hl G _ p hp lam h1
  have := hD.finite (2 * ((d + 1 : ℕ) : ℤ))
  obtain ⟨s, a, ha⟩ := H.basis ℚ_[l] _ lam fun h0 => by
    obtain ⟨s, c, a, h⟩ := hD
    exact subsingleton_of_forall_eq 0 fun x => h _ x fun t hn => by rw [h0]; rfl
  obtain ⟨Λ, hΛ⟩ := hK.int lam 0 _ (add_zero _)
  obtain ⟨b, hb, hδ⟩ := H.top l k hl _ p hp hR hL hK lam s a ha Λ hΛ (G.diag (d + 1) p)
  rw [H.int_one hI l k hl G _ p hp lam h1 Λ hΛ] at hb
  have hr' : i ≫ π ≫ pullback.fst p p = r := by rw [← Category.assoc, hpb.w, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hΔ := (H.pairs k (d + 1) p inferInstance hp.2).1
  obtain ⟨U₀, hU₀⟩ := H.offEx.1 _ hΔ.cl
  have hUU : U = π ⁻¹ᵁ U₀ := TopologicalSpace.Opens.ext (hU.trans (H.offEx.2 _ _ _ _ hpb U₀ hU₀).symm)
  have h0 : pb l U.ι _ (pb l π _ (G.diag (d + 1) p)) = 0 := by
    rw [hUU, ← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply]
    unfold GysQ.diag GysQ.cls
    rw [dif_pos hΔ, G.off hΔ _ U₀ hU₀, map_zero]
  have hw : (2 : ℤ) + 2 * d = 2 * ((d + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨m, hm⟩ := H.div l k hl hR G p i (π ≫ pullback.fst p p) c (by rwa [Category.assoc])
    (by rw [← Category.assoc, hr']; infer_instance) U hU e he (by rwa [hr']) (2 * d) _ hw _ h0
  have key : ∀ (w : ℤ) (hw : 2 + 2 * d = w) (δ : V l (pullback p p) w) (a : Fin s → V l X w),
      pb l π _ δ = cupV l W hw e m → LinearIndependent ℚ_[l] a →
      δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w |
        ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v} →
      ∃ (δ : V l (pullback p p) (2 + 2 * d)) (m : V l W (2 * d)) (s : ℕ) (a : Fin s → V l X (2 + 2 * d)) (b : Fin s → V l X 0),
        pb l π _ δ = cupV l W rfl e m ∧ LinearIndependent ℚ_[l] a ∧ ∑ t, b t = oneV l X ∧
        δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {w : V l (pullback p p) (2 + 2 * d) |
          ∃ (n n' : ℤ) (h : n + n' = 2 + 2 * d) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ w = ext2 l p h u v} := by
    rintro _ rfl δ a h1 h2 h3
    exact ⟨δ, m, s, a, b, h1, h2, hb, h3⟩
  exact key _ hw _ a hm a.linearIndependent hδ

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPnFacts
section -- merged from Development.EtaleCohomology.EtaleTrace.LSmoothPf
open MvPolynomial

namespace LateralTheory.EtaleTrace.LSmoothPf

noncomputable def polyPres (k : Type) [CommRing k] (N : ℕ) :
    Algebra.SubmersivePresentation k (MvPolynomial (Fin N) k) (Fin N) PEmpty.{1} where
  toGenerators := Algebra.Generators.mvPolynomial k (Fin N)
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [Algebra.Generators.ker_eq_ker_aeval_val, ← RingHom.injective_iff_ker_eq_bot]
    intro a b h
    simpa using h
  map := PEmpty.elim
  map_inj a := by cases a
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    rw [Matrix.det_isEmpty, map_one]
    exact isUnit_one

theorem poly_ssmooth (k : Type) [CommRing k] (N : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension N k (MvPolynomial (Fin N) k) :=
  (polyPres k N).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

open CategoryTheory AlgebraicGeometry LateralTheory.EtaleTrace.LPdCut
attribute [local instance] MvPolynomial.gradedAlgebra

theorem spec_C_smooth (k : Type) [Field k] (N : ℕ) :
    SmoothOfRelativeDimension N (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := N) (R := k) (S := MvPolynomial (Fin N) k)).mpr
    (poly_ssmooth k N)

theorem Dp_cover (k : Type) [Field k] (N : ℕ) : ⨆ i, Dp k N i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i; exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · rw [eq_top_iff]
    intro p _hp
    clear _hp
    induction p using MvPolynomial.induction_on with
    | C a =>
      have ha : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0 :=
        MvPolynomial.isHomogeneous_C _ a
      have : MvPolynomial.C a = algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) ⟨_, ha⟩ := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem LSmooth_of (hC : LChart) : LSmooth := by
  intro k _ N
  choose j hj hc hr using fun i => hC k N i
  let 𝒰 : (PN k N).OpenCover := Scheme.Cover.mkOfCovers (Fin (N + 1)) _ j (fun x => by
    have hx : x ∈ (⊤ : (PN k N).Opens) := trivial
    rw [← Dp_cover k N] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : x ∈ Set.range (j i) := by rw [hr i]; exact hi
    obtain ⟨y, hy⟩ := this
    exact ⟨i, y, hy⟩) hj
  have hA : ∀ i, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) k))); infer_instance
  refine HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} N) 𝒰 (fun i => ?_)
  have h : SmoothOfRelativeDimension N (𝒰.f i ≫ PNto k N) := by
    change SmoothOfRelativeDimension N (j i ≫ PNto k N)
    rw [hc i]
    exact spec_C_smooth k N
  exact (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension.{0} N)).mp h

end LateralTheory.EtaleTrace.LSmoothPf
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LProperPf
noncomputable section
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LProperPf

open LateralTheory.EtaleTrace

theorem bij (k : Type) [Field k] (N : ℕ) :
    Function.Bijective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    simpa using this
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    have hp2 := hp
    rw [MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp2
    change _ = p
    conv_rhs => rw [hp2]
    rfl

instance tower (k : Type) [Field k] (N : ℕ) :
    IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance ft (k : Type) [Field k] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

theorem LProper_of : LPdCut.LProper := by
  intro k _ N
  have hi : IsIso (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bij k N)
  unfold PNto
  infer_instance

end LateralTheory.EtaleTrace.LProperPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.Gal.KunnethLefschetz.PnF
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

private def chartE (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) :
    Chart k i ≃+* MvPolynomial (Fin N) k :=
  (chartEquiv k i).trans (MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm).toRingEquiv

private theorem chartE_C (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) (a : k) :
    chartE k N i (HomogeneousLocalization.fromZeroRingHom (grading k N) _
      (algebraMap k (grading k N 0) a)) = MvPolynomial.C a := by
  have h : HomogeneousLocalization.fromZeroRingHom (grading k N) _
      (algebraMap k (grading k N 0) a) = polyToChart k i (MvPolynomial.C a) := by
    simp [polyToChart]
  rw [h]
  have h2 : chartToPoly k i (polyToChart k i (MvPolynomial.C a)) = MvPolynomial.C a := by
    rw [← RingHom.comp_apply, chartToPoly_polyToChart]
    rfl
  simp only [chartE, RingEquiv.trans_apply]
  change (MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm)
    (chartToPoly k i (polyToChart k i (MvPolynomial.C a))) = _
  rw [h2]
  simp

private theorem chart_holds : LPdCut.LChart := by
  intro k _ N i
  let e := chartE k N i
  let ι := Proj.awayι (grading k N) (MvPolynomial.X i) (X_mem i) one_pos
  have hiso : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (RingEquiv.toCommRingCatIso e).isIso_hom
    infer_instance
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ ι, inferInstance, ?_, ?_⟩
  · simp only [PNto, Category.assoc]
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact congrArg (AddMonoidAlgebra.coeff · _) (chartE_C k N i a)
  · have h := Scheme.Hom.opensRange_comp_of_isIso (Spec.map (CommRingCat.ofHom e.toRingHom)) ι
    rw [Proj.opensRange_awayι] at h
    exact congrArg (fun U : (PN k N).Opens => (U : Set (PN k N))) h

private theorem locNml (k : Type) [Field k] (d : ℕ) : TranscendenceTraces.LocNml (PN k d) := by
  intro s
  have hs : s ∈ (⊤ : (PN k d).Opens) := trivial
  rw [← LSmoothPf.Dp_cover k d] at hs
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
  obtain ⟨j, hj, -, hr⟩ := chart_holds k d i
  haveI := hj
  have hU : j.opensRange = LPdCut.Dp k d i := TopologicalSpace.Opens.ext hr
  refine ⟨j.opensRange, isAffineOpen_opensRange j, hU ▸ hi, ?_⟩
  have e1 := j.appIso ⊤
  rw [Scheme.Hom.image_top_eq_opensRange] at e1
  have e := (e1 ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩

private theorem iso0 (k : Type) [Field k] : IsIso (PNto k 0) := by
  obtain ⟨j, hj, hc, hr⟩ := chart_holds k 0 0
  have htop : LPdCut.Dp k 0 0 = ⊤ := by
    have := LSmoothPf.Dp_cover k 0
    simpa using this
  have hjiso : IsIso j := by
    refine (isIso_iff_isOpenImmersion_and_surjective j).2 ⟨hj, ⟨fun x => ?_⟩⟩
    have : x ∈ Set.range j := by
      rw [hr, htop]
      trivial
    exact this
  have hCiso : IsIso (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)) := by
    have hb : Function.Bijective (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k) :=
      ⟨MvPolynomial.C_injective _ _, MvPolynomial.C_surjective _⟩
    exact (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective _ hb)).isIso_hom
  have hP : PNto k 0 = inv j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)) := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  rw [hP]
  infer_instance

end UpperTheory.Gal.KunnethLefschetz.PnF

theorem UpperTheory.Gal.KunnethLefschetz.pnFacts_holds :
    UpperTheory.Gal.KunnethLefschetz.PnFacts := by
  unfold UpperTheory.Gal.KunnethLefschetz.PnFacts
  intro k _ d
  exact ⟨⟨LProperPf.LProper_of k d, LSmoothPf.LSmooth_of PnF.chart_holds k d⟩, Cov.PNIntegral_of k d, PnF.locNml k d, PnF.iso0 k⟩
end
end
