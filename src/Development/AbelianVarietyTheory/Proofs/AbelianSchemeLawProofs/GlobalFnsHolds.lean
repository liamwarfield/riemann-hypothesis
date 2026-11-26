module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroOfDvdPowUniformiser
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_chart {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by
  by_cases hi : (N.U i : Set X).Nonempty
  · have hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩
    have : Nonempty (N.U i ⊓ N.U j : X.Opens) := hij.to_subtype
    have h := s.compat i j
    rw [hj, map_zero, mul_zero] at h
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))
    rw [map_zero]
    exact h
  · have : N.U i = ⊥ := by
      ext1
      simpa using Set.not_nonempty_iff_eq_empty.1 hi
    have : Subsingleton Γ(X, N.U i) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _

theorem eq_zero_of_mem_pow_span {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by
  apply germ_injective_of_isIntegral X x hx
  rw [map_zero]
  rw [X.mem_basicOpen a x hx] at ha
  have hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro e
  have := Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this

theorem sec_eq_zero_of_dvd_pow_uniformiser :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) → Semi.lemmaBSt.{0} := by
  intro H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs
  have : GeometricallyIntegral G.hom := H _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨x, hx⟩ := G.hom.surjective (IsLocalRing.closedPoint V)
  obtain ⟨j, hj⟩ : ∃ j, x ∈ N.U j := by
    have : x ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact Opens.mem_iSup.1 this
  refine sec_eq_zero_of_chart N s j x hj ?_
  refine eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)
  intro h
  have h2 := ((Scheme.basicOpen_res G.left _ (homOfLE (le_top :
    N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2
  have h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π) := by
    rw [Scheme.preimage_basicOpen]
    exact h2
  rw [basicOpen_eq_of_affine] at h3
  have h4 : G.hom x ∈ PrimeSpectrum.basicOpen π := h3
  rw [hx] at h4
  exact h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem globalFns_holds : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

theorem rigidity_holds : RigiditySt :=
  rigidity_of_local_rigidity globalFns_holds local_rigidity

theorem lemmaB_holds : Semi.lemmaBSt.{0} :=
  sec_eq_zero_of_dvd_pow_uniformiser
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]

def ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* Γ(P, W) :=
  (p.appLE U W h).hom

theorem rs_ap (p : P ⟶ X) {U : X.Opens} {W W' : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W' ≤ W) (x : Γ(X, U)) :
    rs P h' (ap p h x) = ap p (h'.trans h) x :=
  congr($(p.appLE_map h (homOfLE h').op).hom x)

theorem ap_rs (p : P ⟶ X) {U U' : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U') (h' : U' ≤ U) (x : Γ(X, U)) :
    ap p h (rs X h' x) = ap p (h.trans fun _ hy => h' hy) x :=
  congr($(p.map_appLE h (homOfLE h').op).hom x)

theorem basicOpen_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (x : Γ(X, U)) :
    P.basicOpen (ap p h x) = W ⊓ p ⁻¹ᵁ X.basicOpen x :=
  Scheme.basicOpen_appLE p W U h x

theorem ap_cst (p : P ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {W : P.Opens}
    (h : W ≤ p ⁻¹ᵁ U) (r : R) : ap p h (cst f U r) = cst (p ≫ f) W r := by
  refine (ap_rs p h le_top _).trans ?_
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rs X h u.val := rfl

theorem le_pre (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W ≤ p ⁻¹ᵁ V) :
    W ≤ p ⁻¹ᵁ (U ⊓ V) := fun _ hy => ⟨h hy, h' hy⟩

theorem pre_left (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ U := fun _ hy => (h hy).1

theorem pre_right (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ V := fun _ hy => (h hy).2

def box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) : LB P :=
  ⟨H.ι × K.ι, fun a => p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2, fun a b =>
    Units.map (ap p (le_pre p (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).toMonoidHom
      (H.g a.1 b.1) *
    Units.map (ap q (le_pre q (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).toMonoidHom
      (K.g a.2 b.2)⟩

variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem rs_mul {U : X.Opens} {V : Y.Opens} {W W' : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ q ⁻¹ᵁ V)
    (h : W' ≤ W) (x : Γ(X, U)) (y : Γ(Y, V)) :
    rs P h (ap p h₁ x * ap q h₂ y) = ap p (h.trans h₁) x * ap q (h.trans h₂) y := by
  rw [map_mul, rs_ap, rs_ap]

theorem ap_g_self (hH : H.IsLB) (i : H.ι) {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U i)) :
    ap p h (H.g i i).val = 1 := by
  have h₁ := congrArg (fun u => ap p (pre_left p h) u.val) (hH.g_self i)
  simpa only [val_res, ap_rs, Units.val_one, map_one] using h₁

theorem ap_cocycle (hH : H.IsLB) (i j k : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j))
    (h₂ : W ≤ p ⁻¹ᵁ (H.U j ⊓ H.U k)) (h₃ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U k)) :
    ap p h₃ (H.g i k).val = ap p h₁ (H.g i j).val * ap p h₂ (H.g j k).val := by
  have e := congrArg (fun u => ap p (le_pre p h₁ (pre_right p h₂)) u.val) (hH.cocycle i j k)
  simp only [val_res, ap_rs, Units.val_mul, map_mul] at e
  exact e.symm

theorem ap_ratio {U V : X.Opens} {x y : Γ(X, V)} {r : Γ(X, U)}
    (e : rs X (inf_le_right : U ⊓ V ≤ V) x =
      rs X (inf_le_left : U ⊓ V ≤ U) r * rs X (inf_le_right : U ⊓ V ≤ V) y)
    {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ p ⁻¹ᵁ V) :
    ap p h₂ x = ap p h₁ r * ap p h₂ y := by
  have e' := congrArg (ap p (le_pre p h₁ h₂)) e
  simpa only [ap_rs, map_mul] using e'

theorem ap_compat (s : LB.Sec H) (i j : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ H.U i) (h₂ : W ≤ p ⁻¹ᵁ H.U j)
    (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j)) :
    ap p h₁ (s.f i) = ap p h (H.g i j).val * ap p h₂ (s.f j) := by
  have e : rs X inf_le_left (s.f i) = (H.g i j).val * rs X inf_le_right (s.f j) := s.compat i j
  have e' := congrArg (ap p h) e
  simpa only [ap_rs, map_mul] using e'

theorem isLB_box (hH : H.IsLB) (hK : K.IsLB) : (box p q H K).IsLB := by
  refine ⟨?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, K.U i by rw [hK.cover]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  · intro a
    refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
    rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
  · intro a b c
    refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
      (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
    exact (mul_mul_mul_comm _ _ _ _).trans
      (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)

def boxSec (s : LB.Sec H) (t : LB.Sec K) : LB.Sec (box p q H K) where
  f := fun a => ap p (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_left (s.f a.1) *
    ap q (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_right (t.f a.2)
  compat := fun a b => by
    refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (rs_mul p q _ _ _ _ _).symm))
    exact (congrArg₂ (· * ·) (ap_compat p s a.1 b.1 _ _ _) (ap_compat q t a.2 b.2 _ _ _)).trans
      (mul_mul_mul_comm _ _ _ _)

theorem nonzeroLocus_boxSec (s : LB.Sec H) (t : LB.Sec K) :
    nonzeroLocus (boxSec p q s t) = p ⁻¹ᵁ nonzeroLocus s ⊓ q ⁻¹ᵁ nonzeroLocus t := by
  have key : ∀ a : H.ι × K.ι, P.basicOpen ((boxSec p q s t).f a) =
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ p ⁻¹ᵁ X.basicOpen (s.f a.1)) ⊓
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ q ⁻¹ᵁ Y.basicOpen (t.f a.2)) := fun a =>
    (P.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (basicOpen_ap p _ _) (basicOpen_ap q _ _))
  ext y
  constructor
  · intro h
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have ha := (key a).le ha
    exact ⟨TopologicalSpace.Opens.mem_iSup.2 ⟨a.1, ha.1.2⟩, TopologicalSpace.Opens.mem_iSup.2 ⟨a.2, ha.2.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ k, X.basicOpen (s.f k) from h₁)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ k, Y.basicOpen (t.f k) from h₂)
    have hy : y ∈ p ⁻¹ᵁ H.U i ⊓ q ⁻¹ᵁ K.U j := ⟨X.basicOpen_le _ hi, Y.basicOpen_le _ hj⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (key (i, j)).ge ⟨⟨hy, hi⟩, hy, hj⟩⟩

theorem ratio_self (s : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) : r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k => X.basicOpen (s.f k)) (nonzeroLocus s)
    (fun k => homOfLE (le_iSup (fun k => X.basicOpen (s.f k)) k)) le_rfl r 1 fun k => ?_
  have hle : X.basicOpen (s.f k) ≤ nonzeroLocus s ⊓ H.U k :=
    le_inf (le_iSup (fun k => X.basicOpen (s.f k)) k) (X.basicOpen_le _)
  have e := congrArg (rs X hle) (h k)
  simp only [map_mul, rs_rs] at e
  have u : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) := X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  have e' : rs X (hle.trans inf_le_left) r = 1 := u.mul_right_cancel (e.symm.trans (_root_.one_mul _).symm)
  exact e'.trans (map_one (rs X (hle.trans inf_le_left))).symm

theorem isProjBy_of_isPullback {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (sq : IsPullback p q f g) (hf : IsProjBy f) (hg : IsProjBy g) : IsProjBy (p ≫ f) := by
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  obtain ⟨K, hK, n, t, ht, ht'⟩ := hg
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨box p q H K, isLB_box p q hH hK, m * n + m + n,
    fun a => boxSec p q (s (e a).1) (t (e a).2), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

end GlobalTheory.AbLaw.Segre

theorem GlobalTheory.AbLaw.isProjBy_tensor : ∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))),
    IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom := fun _ _ X Y hX hY =>
  GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback _ _ (IsPullback.of_hasPullback X.hom Y.hom) hX hY
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isOpenImmersion_of_section_of_etale {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have : Etale (s ≫ f) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp s f
  have : Mono s := (SplitMono.mk f hs).mono
  exact IsOpenImmersion.of_flat_of_mono s

theorem exists_section_of_etale {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Etale f] (x : X) :
    ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = 𝟙 _ ∧ x ∈ Set.range s := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let W : Set X := ⋃ s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = 𝟙 _}, Set.range s.1
  have hW : IsOpen W := isOpen_iUnion fun s => by
    have := isOpenImmersion_of_section_of_etale f s.1 s.2
    exact s.1.isOpenEmbedding.isOpen_range
  have hx : x ∈ W := by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := Wᶜ) ⟨x, hx⟩
      hW.isClosed_compl.isLocallyClosed
    replace hc' : IsClosed {c} := hc'
    exact hc (Set.mem_iUnion.mpr ⟨⟨_, pointOfClosedPoint_comp f c hc'⟩,
      IsLocalRing.closedPoint K, pointOfClosedPoint_apply f c hc' _⟩)
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  exact ⟨s.1, s.2, hs⟩

theorem exists_local_rational_torsion {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (n : ℕ) [Etale (mulA A n).left]
    {Z : Over (Spec (CommRingCat.of K))} (d : Z ⟶ A) (hd : d ^ n = 1) (p : Z.left) :
    ∃ (W : Over (Spec (CommRingCat.of K))) (c : W ⟶ Z) (_ : IsOpenImmersion c.left),
      p ∈ Set.range c.left ∧ ∃ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A,
        y ^ n = 1 ∧ c ≫ d = toUnit W ≫ y := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of K))},
      (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have e : d.left ≫ (mulA A n).left = Z.hom ≫ η[A].left := by
    rw [← Over.comp_left, hmul, hd, hone]
  let l : Z.left ⟶ pullback (mulA A n).left η[A].left := pullback.lift _ _ e
  obtain ⟨s, hs, t, ht⟩ := exists_section_of_etale (K := K)
    (pullback.snd (mulA A n).left η[A].left) (l p)
  have := isOpenImmersion_of_section_of_etale (pullback.snd (mulA A n).left η[A].left) s hs
  have hy : (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ A.hom = 𝟙 _ := by
    rw [← Over.w (mulA A n), Category.assoc, pullback.condition_assoc]
    erw [hη]
    exact (congrArg (s ≫ ·) (Category.comp_id _)).trans hs
  let y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A := Over.homMk _ hy
  refine ⟨Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, y, ?_, ?_⟩
  · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p t ht.symm
    exact ⟨w, hw⟩
  · rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    change (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ (mulA A n).left = 𝟙 _ ≫ η[A].left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ η[A].left) hs
  · apply Over.OverMorphism.ext
    change pullback.fst l s ≫ d.left =
      (pullback.fst l s ≫ Z.hom) ≫ s ≫ pullback.fst (mulA A n).left η[A].left
    have h1 : d.left = l ≫ pullback.fst (mulA A n).left η[A].left := (pullback.lift_fst _ _ _).symm
    have h2 : Z.hom = l ≫ pullback.snd (mulA A n).left η[A].left := (pullback.lift_snd _ _ _).symm
    have h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s := by
      rw [h2, pullback.condition_assoc]
      exact (congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)
    rw [h3, h1, pullback.condition_assoc]

theorem existsUnique_appTop_eq_of_flat {X Y : Scheme.{0}} (m : X ⟶ Y) [QuasiCompact m]
    [Surjective m] [Flat m] (f : Γ(X, ⊤))
    (h : ∀ {Z : Scheme.{0}} (a b : Z ⟶ X), a ≫ m = b ≫ m → a ≫ TLinPf.mOf f = b ≫ TLinPf.mOf f) :
    ∃! g : Γ(Y, ⊤), m.appTop.hom g = f := by
  refine ⟨TLinPf.fnOf (EffectiveEpi.desc m (TLinPf.mOf f) h), ?_, ?_⟩
  · beta_reduce
    rw [← TLinPf.fnOf_comp, EffectiveEpi.fac, TLinPf.fnOf_mOf]
  · intro g hg
    rw [← TLinPf.fnOf_mOf g]
    congr 1
    apply EffectiveEpi.uniq
    rw [TLinPf.comp_mOf, hg]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem existsUnique_descend_of_torsion_invariant {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [Etale (mulA A n).left] [Surjective (mulA A n).left] [QuasiCompact (mulA A n).left]
    (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U))
    (hf : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤
        ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) :
    ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  let m := (mulA A n).left
  have hm : m = (mulA A n).left := rfl
  let V := m ⁻¹ᵁ U
  let f' : Γ(V, ⊤) := V.topIso.inv.hom f
  have key : ∀ {Z : Scheme.{0}} (a b : Z ⟶ V), a ≫ (m ∣_ U) = b ≫ (m ∣_ U) →
      a ≫ TLinPf.mOf f' = b ≫ TLinPf.mOf f' := by
    intro Z a b hab
    have hab' : (a ≫ V.ι) ≫ m = (b ≫ V.ι) ≫ m := by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% hab]
    have hw : (a ≫ V.ι) ≫ A.hom = (b ≫ V.ι) ≫ A.hom := by
      rw [← Over.w (mulA A n), ← hm, ← Category.assoc, hab', Category.assoc _ m]
    let FinalForm : Over (Spec (CommRingCat.of K)) := Over.mk ((b ≫ V.ι) ≫ A.hom)
    let z₁ : FinalForm ⟶ A := Over.homMk (a ≫ V.ι) hw
    let z₂ : FinalForm ⟶ A := Over.homMk (b ≫ V.ι) rfl
    have hz : z₁ ^ n = z₂ ^ n := by
      rw [← hmul, ← hmul]
      exact Over.OverMorphism.ext hab'
    have hd : (z₁ * z₂⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hz, mul_inv_cancel]
    have hloc := exists_local_rational_torsion A n _ hd
    choose W c hc hp y hy hcy using hloc
    let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Z (fun p => (W p).left)
      (fun p => (c p).left) (fun p => ⟨p, hp p⟩) hc
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change (c p).left ≫ a ≫ _ = (c p).left ≫ b ≫ _
    let t : A ⟶ A := (toUnit A ≫ y p) * 𝟙 A
    have htm : t ≫ mulA A n = mulA A n := by
      rw [hmul, mul_pow, ← MonObj.comp_pow, hy p, MonObj.comp_one, _root_.one_mul]
    have htm' : t.left ≫ m = m := by rw [hm, ← Over.comp_left, htm]
    have e : V ≤ t.left ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, htm']
    have h1 : c p ≫ z₁ = c p ≫ z₂ ≫ t := by
      have h2 := hcy p
      rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul] at h2
      rw [h2, ← Category.assoc _ z₂, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    have h3 : (c p).left ≫ a = (c p).left ≫ b ≫ t.left.resLE V V e := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
      have := congr(($h1).left)
      simpa [z₁, z₂] using this
    have h4 : t.left.resLE V V e ≫ TLinPf.mOf f' = TLinPf.mOf f' := by
      rw [TLinPf.comp_mOf]
      congr 1
      exact (resLE_appTop_topIso_inv t.left e f).trans (congrArg _ (hf _ (hy p) e))
    rw [← Category.assoc, h3, Category.assoc, Category.assoc, h4]
  have : Surjective (m ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨g, hg, hu⟩ := existsUnique_appTop_eq_of_flat (m ∣_ U) f' key
  have h7 : ∀ g : Γ(A.left, U), (m ∣_ U).appTop.hom (U.topIso.inv.hom g) =
      V.topIso.inv.hom ((m.app U).hom g) := fun g => by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_topIso_inv, Scheme.Hom.appLE_eq_app]
  have hV : Function.Injective V.topIso.inv.hom := V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hU : Function.Bijective U.topIso.inv.hom := U.topIso.symm.commRingCatIsoToRingEquiv.bijective
  obtain ⟨g, rfl⟩ := hU.2 g
  refine ⟨g, hV ((h7 g).symm.trans hg), fun g' hg' => hU.1 (hu _ ?_)⟩
  exact (h7 g').trans (congrArg _ hg')

theorem torsion_invariant_descends :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧
        (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ),
      (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)),
      (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 →
        ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤
          ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)),
          (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) →
      ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f := by
  intro H K _ _ P n hn U f hf
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => hn (by rw [h, Nat.cast_zero])
  obtain ⟨h1, -, h3, h4⟩ := H _ P n hn1
  have : Etale (mulA P.A n).left := h4 (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : IsCommMonObj P.A := P.isAb.comm
  exact existsUnique_descend_of_torsion_invariant P.A n U f hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AbLaw.CubeOpen

theorem triv_comp {X Y Z : Scheme.{0}} {M : LB X} {f : Y ⟶ X} (h : Z ⟶ Y) {k : Z ⟶ X}
    (hk : h ≫ f = k) (ht : Triv (M.pull f)) : Triv (M.pull k) := by
  subst hk
  obtain ⟨t, ht⟩ := ht
  exact ⟨_, LB.isGen_pullGen M _ _ t ht h⟩

theorem triv_pull_pull {X Y Z : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (h : Z ⟶ Y)
    (ht : Triv (M.pull (h ≫ f))) : Triv ((M.pull f).pull h) := by
  obtain ⟨t, ht⟩ := ht
  have hle : ∀ j : PUnit.{1} → PUnit.{1} → M.ι,
      LB.wchart (M.pull f) (K := PUnit) (fun _ => h) j ≤
        LB.wchart M (K := PUnit) (fun _ => h ≫ f) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k =>
      Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
  refine ⟨⟨fun j => res (hle j) (LB.ts t (j PUnit.unit))⟩, (LB.isGen_iff _ _).2 fun i j => ?_⟩
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff M t).1 ht (i PUnit.unit) (j PUnit.unit))
  rw [LB.lcg_comp M (fun _ : PUnit.{1} => f) (fun _ => 1) h (i PUnit.unit) (j PUnit.unit)] at key
  erw [map_mul] at key
  simp only [LB.res_res] at key
  rw [LB.lcg_pull]
  change res _ (res (hle i) _) = _ * res _ (res (hle j) _)
  simp only [LB.res_res]
  exact key

theorem eq_bot_of_small {S : Type} [CommRing S] [IsLocalRing S] (J : Ideal S) (hJ : J.FG)
    (H : ∀ (I' : Ideal S) (e : S), e ∈ J → IsLocalRing.maximalIdeal S * J ≤ I' → I' ≤ J →
      J ≤ I' ⊔ Ideal.span {e} → J ≤ I') : J = ⊥ := by
  classical
  have key : ∀ s : Finset S, (s : Set S) ⊆ J →
      J ≤ IsLocalRing.maximalIdeal S * J ⊔ Ideal.span (s : Set S) →
      J ≤ IsLocalRing.maximalIdeal S * J := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ h; simpa using h
    | insert a s _ ih =>
      intro hs h
      rw [Finset.coe_insert] at hs h
      have hs' : (s : Set S) ⊆ J := (Set.subset_insert _ _).trans hs
      refine ih hs' (H _ a (hs (Set.mem_insert _ _)) le_sup_left
        (sup_le Ideal.mul_le_right (Ideal.span_le.2 hs')) ?_)
      rwa [Ideal.span_insert, sup_comm (Ideal.span {a}), ← sup_assoc] at h
  obtain ⟨s, hs⟩ := id hJ
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) J hJ ?_
    (IsLocalRing.maximalIdeal_le_jacobson _)
  exact key s (hs ▸ Ideal.subset_span) (hs.ge.trans le_sup_right)

theorem exists_ann {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) (hI : I.FG)
    (hIp : I ≤ p)
    (H : ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T), (∀ r ∉ p, IsUnit (g r)) →
      (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
      I ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {e})).comp g) → I ≤ RingHom.ker g) :
    ∃ c ∉ p, ∀ x ∈ I, c * x = 0 := by
  let S := Localization.AtPrime p
  have hJm : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIp
  have hbot : I.map (algebraMap R S) = ⊥ := by
    refine eq_bot_of_small _ (hI.map _) fun I' e he h₁ h₂ h₃ => ?_
    have hne : I' ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ h₂.trans hJm))
    haveI : Nontrivial (S ⧸ I') := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (S ⧸ I') :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I') Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk I') :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have := H (S ⧸ I') ((Ideal.Quotient.mk I').comp (algebraMap R S)) (Ideal.Quotient.mk I' e)
      (fun r hr => (IsLocalization.map_units S (⟨r, hr⟩ : p.primeCompl)).map (Ideal.Quotient.mk I')) ?_ ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem (I := I')).1 (this hx)
    · intro a ha
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact h₁ (Ideal.mul_mem_mul (fun hb => ha (hb.map _)) he)
    · exact fun hu => hJm he (IsUnit.of_map _ _ hu)
    · intro x hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h₃ (Ideal.mem_map_of_mem _ hx))
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, ← hyz, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 hy, zero_add, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hx : ∀ x ∈ I, ∃ c ∉ p, c * x = 0 := fun x hx => by
    have h0 : algebraMap R S x = 0 := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hx
      rwa [hbot, Ideal.mem_bot] at this
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl S x).1 h0
    exact ⟨c, c.2, hc⟩
  obtain ⟨s, rfl⟩ := hI
  choose! c hc using hx
  refine ⟨∏ y ∈ s, c y, ?_, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl fun y hy => (hc y (Ideal.subset_span hy)).1
  · intro x hx
    have : Ideal.span (s : Set R) ≤ LinearMap.ker (LinearMap.mulLeft R (∏ y ∈ s, c y)) := by
      refine Ideal.span_le.2 fun y hy => ?_
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c (show y ∈ s from hy)
      change (∏ y ∈ s, c y) * y = 0
      rw [hd, mul_comm (c y), _root_.mul_assoc, (hc y (Ideal.subset_span hy)).2, mul_zero]
    exact this hx

section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)

theorem isPullback_iso_comp {W P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (e : W ⟶ P) [IsIso e] : IsPullback (e ≫ a) (e ≫ b) f g :=
  h.of_iso (asIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

def sqMap : ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).left ⟶ (A ⊗ A).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) A A).left ≫ pullback.fst (A ⊗ A).hom φ

theorem isPullback_sqMap :
    IsPullback (sqMap φ A) ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).hom (A ⊗ A).hom φ := by
  have h := IsPullback.of_hasPullback (A ⊗ A).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) A A)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) A A).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) A A)
  rw [← hw]
  exact isPullback_iso_comp h _

theorem lift_sqMap (a b : A ⟶ A) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ sqMap φ A =
      pullback.fst A.hom φ ≫ (lift a b).left := by
  rw [sqMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _

end BaseChange

theorem triv_lift (hobs : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen)
    {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (M : LB (A ⊗ A).left)
    (hM : M.IsLB) (h₁ : Triv (M.pull (lift (𝟙 A) 1).left)) (h₂ : Triv (M.pull (lift 1 (𝟙 A)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (φ : Spec (CommRingCat.of T) ⟶ S) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (A ⊗ A).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫ φ) → Triv (M.pull π)) :
    Triv (M.pull (sqMap φ A)) := by
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine hobs T e he ((Over.pullback φ).obj A) (TLinPf.isAb_pullback φ A hA) (M.pull (sqMap φ A))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst A.hom φ) ?_ h₁)
    rw [← lift_sqMap, Functor.map_one, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst A.hom φ) ?_ h₂)
    rw [← lift_sqMap, Functor.map_one, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_sqMap φ A)))

theorem bijective_appTop (hG : GlobalFnsSt) {S S' X : Scheme.{0}} (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) {φ : S' ⟶ S} {π : X ⟶ B.left} {f : X ⟶ S'}
    (h : IsPullback π f B.hom φ) : Function.Bijective f.appTop.hom := by
  have h₁ : Function.Bijective (pullback.snd B.hom φ).appTop.hom :=
    hG _ _ (TLinPf.isAb_pullback φ B hB)
  have h₂ : Function.Bijective h.isoPullback.hom.appTop.hom :=
    ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)
  rw [← h.isoPullback_hom_snd, Scheme.Hom.comp_appTop]
  exact h₂.comp h₁

theorem triv_basicOpen_of_triv_fibre : GlobalFnsSt → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ (r : R) (I : Ideal R), g₀ r ≠ 0 ∧ I.FG ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g)) → (∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → Nonempty (Perf (A ⊗ A).hom M) → Triv (M.pull (lift (𝟙 A) 1).left) → Triv (M.pull (lift 1 (𝟙 A)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (A ⊗ A).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (A ⊗ A).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((A ⊗ A).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  intro hG hsee hobs R _ A _ hA M hM hP h₁ h₂ K _ g₀ X₀ π₀ f₀ h₀ ht₀
  have hB := Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  haveI := hB.proper
  haveI := hB.geomConnected
  obtain ⟨r, I, hr, hI, H⟩ := hsee R _ (A ⊗ A).hom M hM hP inferInstance inferInstance K g₀ X₀ π₀ f₀ h₀
    (bijective_appTop hG _ hB h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ X₀ π₀ f₀ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      refine (H T g _ _ _ (isPullback_sqMap (Spec.map (CommRingCat.ofHom g)) A) (hu r hr)).1 ?_
      refine triv_lift hobs A hA M hM h₁ h₂ T _ e he he' fun X' π f' hp => ?_
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
      exact (H _ _ X' π f' hp ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle)
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range (((A ⊗ A).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ (A ⊗ A).hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm) (hp.lift_fst _ _ _) ht

end GlobalTheory.AbLaw.CubeOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw

def finSecPullId {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) : LB.Sec (M.pull (𝟙 X)) where
  f := fun j => rs X (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) (s.f (j PUnit.unit))
  compat := fun i j => by
    have h := congrArg (rs X (inf_le_inf (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) i PUnit.unit)
      (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) :
        (M.pull (𝟙 X)).U i ⊓ (M.pull (𝟙 X)).U j ≤ M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)))
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at h
    erw [rs_rs, rs_rs] at h
    erw [rs_rs, rs_rs, h]
    congr 1
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    rfl

theorem finSec_eq_zero_of_cover {X : Scheme.{0}} {I : Type} (V : I → X.Opens) (hV : ⨆ i, V i = ⊤)
    {U : X.Opens} (x : Γ(X, U)) (hx : ∀ i, rs X (inf_le_left : U ⊓ V i ≤ U) x = 0) : x = 0 := by
  refine X.sheaf.eq_of_locally_eq' (fun i => U ⊓ V i) U (fun i => homOfLE inf_le_left) ?_ x 0 ?_
  · rw [← inf_iSup_eq, hV, inf_top_eq]
  · intro i
    exact (hx i).trans (map_zero (rs X (inf_le_left : U ⊓ V i ≤ U))).symm

theorem Perf.exists_relation {X : Scheme.{0}} {K : Type} [Field K] {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} (Q : Perf f M) (s : Fin (Q.a + 1) → LB.Sec M) :
    ∃ c : Fin (Q.a + 1) → K, c ≠ 0 ∧ ∀ i, ∑ k, cst f (M.U i) (c k) * (s k).f i = 0 := by
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec K (RingHom.id K) X (𝟙 X) f hpb
  let v : Fin (Q.a + 1) → Fin Q.a → K := fun k => (E.symm (finSecPullId (s k))).1
  have hv : ∀ k j, rs X (Q.le j) ((s k).f (Q.ch j)) = ∑ l, cst f (Q.W j) (v k l) * Q.u l j := by
    intro k j
    have h := hE (E.symm (finSecPullId (s k))) j
    rw [Equiv.apply_symm_apply] at h
    refine Eq.trans ?_ h
    exact (rs_rs _ _ _).symm
  have hdep : ¬ LinearIndependent K v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, k₀, hk₀⟩ := hdep
  have hc' : ∀ l, ∑ k, c k * v k l = 0 := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply] using this
  have hW : ∀ j, ∑ k, cst f (Q.W j) (c k) * rs X (Q.le j) ((s k).f (Q.ch j)) = 0 := by
    intro j
    simp only [hv, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Finset.sum_mul, ← map_sum, hc', map_zero, zero_mul, Finset.sum_const_zero]
  refine ⟨c, fun h => hk₀ (congrFun h k₀), fun i => ?_⟩
  refine finSec_eq_zero_of_cover Q.W Q.cover _ fun j => ?_
  have h₁ : ∀ k, rs X (inf_le_left : M.U i ⊓ Q.W j ≤ M.U i) ((s k).f i) =
      rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)) (M.g i (Q.ch j)).val *
        rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j) (rs X (Q.le j) ((s k).f (Q.ch j))) := by
    intro k
    have h := congrArg (rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)))
      ((s k).compat i (Q.ch j))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  have h₂ := congrArg (rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j)) (hW j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rs_cst, map_zero] at h₂
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rs_cst, h₁]
  simp only [mul_left_comm (cst f _ _), ← Finset.mul_sum, h₂, mul_zero]

theorem sections_finite_of_perf
    (hperf : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M))
    (hva : ∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)),
      IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)),
        (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s)
    (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left)
    (hM : M.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
      ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  obtain ⟨N, -, m, σ, hLB, hσ⟩ := hva _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.id_horiz _)
  have hsm : Smooth P.A.hom := by
    haveI := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g _
  obtain ⟨Q⟩ := hperf K P.A.left P.A.hom hsm ⟨_, hLB, m, σ, hσ⟩ M hM
  refine ⟨Q.a + 1, fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := Q.exists_relation s
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c k), fun h0 => hc ?_, h⟩
  funext k
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  exact hinj ((congrFun h0 k).trans (map_zero _).symm)

end GlobalTheory.AbLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFiniteStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.abelianVariety_lineBundle_sections_finite : (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  first | exact @GlobalTheory.AbLaw.sections_finite_of_perf | exact GlobalTheory.AbLaw.sections_finite_of_perf | (intros; apply GlobalTheory.AbLaw.sections_finite_of_perf <;> assumption)
end
end
