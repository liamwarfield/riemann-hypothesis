module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

section Reg

variable {X X' Y W : Scheme.{0}} (L : LB X) (L' : LB X')

def tr {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (I : (Y ⟶ X) → L.ι) (ψ : Y ⟶ X) :
    (Z.presheaf.stalk z)ˣ :=
  gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U (I ψ)) (L.g (J (r ≫ ψ)) (I ψ))

def Reg (F : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ)
    (c : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U) : Prop :=
  ∀ (y : Y) I I', Good L y I → Good L' y I' → ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' →
      F Z r z J J' = c _ (tr L r z J I) (tr L' r z J' I') * gm r z V u

variable {L L'}
variable {F G : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ}
  {c d : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U}

theorem Reg.mul (hF : Reg L L' F c) (hG : Reg L L' G d) :
    Reg L L' (fun Z r z J J' => F Z r z J J' * G Z r z J J') (fun U _ h h' => c U h h' * d U h h') := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  obtain ⟨V', hV', u', hu'⟩ := hG y I I' hI hI'
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, res inf_le_left u * res inf_le_right u', fun Z r z J J' hz hJ hJ' => ?_⟩
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz]
  show F Z r z J J' * G Z r z J J' = _
  rw [hu Z r z J J' hz.1 hJ hJ', hu' Z r z J J' hz.2 hJ hJ', _root_.mul_mul_mul_comm]

theorem Reg.inv (hF : Reg L L' F c) :
    Reg L L' (fun Z r z J J' => (F Z r z J J')⁻¹) (fun U _ h h' => (c U h h')⁻¹) := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  refine ⟨V, hV, u⁻¹, fun Z r z J J' hz hJ hJ' => ?_⟩
  show (F Z r z J J')⁻¹ = _
  rw [map_inv, hu Z r z J J' hz hJ hJ', mul_inv]

theorem good_exists {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem Reg.glue (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      F Z r z J J' = gm r z ⊤ a := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' → F Z r z J J' = gm r z V u := by
    intro y
    obtain ⟨I, hI⟩ := good_exists hL y
    obtain ⟨I', hI'⟩ := good_exists hL' y
    obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
    exact ⟨V, hV, u, fun Z r z J J' hz hJ hJ' => by rw [hu Z r z J J' hz hJ hJ', hc, _root_.one_mul]⟩
  choose V hV u hu using H
  obtain ⟨a, ha⟩ := glue_unit ⊤ V (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩) u
    (fun i j x hx => by
      obtain ⟨I, hI⟩ := good_exists hL x
      obtain ⟨I', hI'⟩ := good_exists hL' x
      exact (hu i _ (𝟙 Y) x I I' hx.1 hI hI').symm.trans (hu j _ (𝟙 Y) x I I' hx.2 hI hI'))
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hu (r z) Z r z J J' (hV _) hJ hJ', ← ha, gm_res r z _ (hV _)]

theorem Reg.rigid (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) {S : Scheme.{0}} (p : Y ⟶ S)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') : F Z r z J J' = F Z r' z J J' := by
  obtain ⟨a, ha⟩ := hF.glue hL hL' hc
  obtain ⟨a₀, e⟩ := hp a.val
  rw [ha Z r z J J' hJ hJ', ha Z r' z J J' hJ hJ']
  apply Units.ext
  have k : ∀ q : Z ⟶ Y, (gm q z ⊤ a).val = gs (q ≫ p) z ⊤ a₀ := fun q => by
    rw [← gs_unit q z ⊤ trivial, ← e]
    exact gs_pull q p z ⊤ trivial a₀
  rw [k, k, hr]

variable {K : Type} [Fintype K]

theorem reg_val {φ : K → (W ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z J _ => val t (r ≫ p) z J) (fun _ _ h _ => ∏ k, h (p ≫ φ k) ^ ε k) := by
  intro y I I' hI _
  refine ⟨p ⁻¹ᵁ LB.wchart L φ (fun k => I (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz hJ _ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

theorem reg_val' {φ : K → (W ⟶ X')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z _ J' => val t (r ≫ p) z J') (fun _ _ _ h' => ∏ k, h' (p ≫ φ k) ^ ε k) := by
  intro y I I' _ hI
  refine ⟨p ⁻¹ᵁ LB.wchart L' φ (fun k => I' (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz _ hJ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

def wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} (w : LB.Iso L' (LB.LinComb L pr ε)) {Z : Scheme.{0}} (q : Z ⟶ X') (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  gv w q z (fun k => J (q ≫ pr k)) (J' q)

theorem reg_wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) (p : Y ⟶ X') :
    Reg L L' (fun _ r z J J' => wv w (r ≫ p) z J J') (fun _ _ h h' => (∏ k, h (p ≫ pr k) ^ ε k) * (h' p)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (LB.wchart L pr (fun k => I (p ≫ pr k)) ⊓ L'.U (I' p)), ⟨hI.mem pr p, hI' p⟩,
    pullU p _ (w.s (fun k => I (p ≫ pr k), I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gm_isGen hw (r ≫ p) z _ (fun k => I (p ≫ pr k)) _ (I' p) (hJ.mem pr (r ≫ p)) hz.1 (hJ' _) hz.2).trans
    (congrArg (· * _) (congrArg₂ (· * ·) ?_ rfl))
  refine (gm_linComb L pr ε (r ≫ p) z _ _ (hJ.mem pr (r ≫ p)) hz.1).trans ?_
  rfl

end Reg

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg in
theorem reg_lam {S S' Y : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)} (hw : w.IsGen) (p : Y ⟶ (G2 B').left) :
    Reg M M' (fun _ r z J J' => lamVal w (r ≫ p) z J J')
      (fun _ _ h h' => (∏ k, h ((p ≫ β₂) ≫ lamφ B k) ^ lamε k) * (∏ k, h' (p ≫ lamφ B' k) ^ lamε k)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (((abelian₂ B M).pull β₂).U (fun _ => ind B I (p ≫ β₂)) ⊓ (abelian₂ B' M').U (ind B' I' p)),
    ⟨mem_pull.2 (good_ind hI (p ≫ β₂)), good_ind hI' p⟩,
    pullU p _ (w.s (fun _ => ind B I (p ≫ β₂), ind B' I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (lamVal_eq w (r ≫ p) z J J').trans ?_
  refine ((isGen_iff w).1 hw Z (r ≫ p) z _ (ind B I (p ≫ β₂)) _ (ind B' I' p) (good_ind hJ ((r ≫ p) ≫ β₂))
    (mem_pull.1 hz.1) (good_ind hJ' _) hz.2).trans (congrArg (· * _) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)))
  · refine (gm_linComb M (lamφ B) lamε ((r ≫ p) ≫ β₂) z _ _ (good_ind hJ ((r ≫ p) ≫ β₂)) (mem_pull.1 hz.1)).trans ?_
    rfl
  · refine (gm_linComb M' (lamφ B') lamε (r ≫ p) z _ _ (good_ind hJ' _) hz.2).trans ?_
    rfl

section Scale

variable {Y : Scheme.{0}} {M : LB Y}

def scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun i => res le_top a * t.s i⟩

theorem gm_scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scale a t).s i) = gm r z ⊤ a * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ h a))

theorem scale_isGen (a : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scale a t).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := congrArg (gm (𝟙 Y) y _) (ht i j)
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_scale a t _ y i hy.1, gm_scale a t _ y j hy.2, e, mul_left_comm]

end Scale

theorem mapsAtExp_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {K : Type}
    [Fintype K] {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) {p : Y ⟶ X'} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))} (ha : a.IsGen)
    {b : LB.Gen (LB.LinComb L (K := K) (fun i => p ≫ pr i) (fun i => n * ε i))} (hb : b.IsGen)
    (H : ∀ (y : Y) J J', Good L y J → Good L' y J' → val b (𝟙 Y) y J = wv w p y J J' ^ n * val a (𝟙 Y) y J') :
    MapsAtExp L L' pr ε w p n a b := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := good_exists hL y
  obtain ⟨J', hJ'⟩ := good_exists hL' y
  have e := H y J J' hJ hJ'
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])] at e
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun i => p ≫ pr i) (fun i => J (p ≫ pr i)) := Set.mem_iInter.2 fun i => hJ _
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun _ : PUnit => p) (fun _ => J' p) := Set.mem_iInter.2 fun i => hJ' _
  have eb := gen_trans hb (𝟙 Y) y (mapsAtExp_le_b L L' pr ε p jN jL hy) m₁
  have ea := gen_trans ha (𝟙 Y) y (mapsAtExp_le_a L L' pr ε p jN jL hy) m₂
  have ew := gm_isGen hw p y jN (fun i => J (p ≫ pr i)) jL (J' p) hy.1 (hJ.mem pr p) hy.2 (hJ' p)
  have el := gm_linComb L pr ε p y jN (fun i => J (p ≫ pr i)) hy.1 (hJ.mem pr p)
  refine (gm_res _ y _ hy _).trans (eb.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans
      ((congrArg (fun q : Y ⟶ X' => gv w q y jN jL) (Category.id_comp p)).trans
        (ew.trans (congrArg (fun x => x * _ * _) el)))))) ((gm_res _ y _ hy _).trans ea))).symm))
  rw [e]
  simp only [trF, wv, Category.id_comp, Fintype.prod_unique, mul_zpow, ← Finset.prod_zpow, inv_zpow, ← zpow_mul,
    mul_comm n]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp.Point
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsoSpecialisesToFieldPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsoSpecialisesToFieldPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.Spread

theorem spread_fibre : ∀ (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (G : Over M.Z) [GrpObj G], IsSemiAbelian G → ∀ (R' : Subalgebra o Ω) (B : Over (Sp R')) [GrpObj B], IsSemiAbelian B → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R'.val.toRingHom) a' → IsGrpPullback A₀ G M.pt ψ → ∀ (K : Type) [Field K] (s : Sp K ⟶ M.Z), R' ≤ M.O (s (closedPoint K)) → ∀ (yK : R' →+* K), (∀ x : R', yK x = M.val s x) → ∀ (AK : Over (Sp K)) [GrpObj AK] (φK : AK.left ⟶ B.left), IsGrpPullback AK B (spMap yK) φK → ∃ Ψ : AK.left ⟶ G.left, IsGrpPullback AK G s Ψ ∧ (∀ (e : B ⟶ B) (F : G ⟶ G) (e₀ : A₀ ⟶ A₀), e₀.left ≫ a' = a' ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left → ∀ eK : AK ⟶ AK, eK.left ≫ φK = φK ≫ e.left → eK.left ≫ Ψ = Ψ ≫ F.left) ∧ ∀ (b : Sp R' ⟶ B.left) (gγ : Over.mk M.pt ⟶ G) (w : Sp Ω ⟶ A₀.left), b ≫ B.hom = 𝟙 _ → w ≫ A₀.hom = 𝟙 _ → w ≫ a' = spMap R'.val.toRingHom ≫ b → w ≫ ψ = gγ.left → ∀ (T : Scheme.{0}) (x : T ⟶ AK.left) (v : T ⟶ G.left), x ≫ φK = x ≫ AK.hom ≫ spMap yK ≫ b → ValAt gγ (x ≫ AK.hom ≫ s) v → x ≫ Ψ = v := by
  intro o Ω _ _ _ _ M hN G _ hG R' B _ hB A₀ _ a' ψ ha' hψ K _ s hR' yK hyK AK _ φK hφK
  set z := s (closedPoint K) with hz
  haveI : IsNoetherianRing (M.O z) := M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z

  let ιO : Sp (M.O z) ⟶ M.Z :=
    Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z
  have key : ∀ {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) (hy : y (closedPoint C) ⤳ z)
      (r : M.O z →+* C), r.comp (M.stalkEquiv z).toRingHom =
        (M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y).hom →
      spMap r ≫ ιO = y := by
    intro C _ _ y hy r hr
    have e : (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
        CommRingCat.ofHom r = M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y := by
      ext a
      exact congrArg (fun f : M.Z.presheaf.stalk z →+* C => f a) hr
    have e2 : spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) =
        Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hy) :=
      (Spec.map_comp _ _).symm.trans ((congrArg Spec.map e).trans (Spec.map_comp _ _))
    change spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z = y
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.Z.fromSpecStalk z) e2).trans
      ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy)).trans ?_
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
  have hpt : spMap (algebraMap (M.O z) Ω) ≫ ιO = M.pt :=
    key M.pt (M.pt_specializes _ z) _ (by ext a; rfl)
  let v : M.O z →+* K := RatModel.valLoc s z specializes_rfl
  have hs : spMap v ≫ ιO = s := key s specializes_rfl v (by ext a; simp [v, RatModel.valLoc])

  let ι' : R' →+* M.O z := (Subalgebra.inclusion hR').toRingHom
  have hyv : yK = v.comp ι' := by
    ext x
    rw [hyK x, RingHom.comp_apply]
    exact (RatModel.valLoc_eq_val s specializes_rfl (ι' x)).symm
  have spc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hyK' : spMap yK = spMap v ≫ spMap ι' := by rw [hyv, spc]
  have hval : spMap R'.val.toRingHom = spMap (algebraMap (M.O z) Ω) ≫ spMap ι' := by
    rw [← spc]; rfl

  let BO := (Over.pullback (spMap ι')).obj B
  let GO := (Over.pullback ιO).obj G
  have hBO : IsGrpPullback BO B (spMap ι') (pullback.fst _ _) := isGrpPullback_pullback B _
  have hGO : IsGrpPullback GO G ιO (pullback.fst _ _) := isGrpPullback_pullback G _
  have hBOs : IsSemiAbelian BO := IsSemiAbelian.pullback _ B hB
  have hGOs : IsSemiAbelian GO := IsSemiAbelian.pullback _ G hG
  let j := spMap (algebraMap (M.O z) Ω)
  let a₀ : A₀.left ⟶ BO.left := pullback.lift a' (A₀.hom ≫ j) (by
    rw [ha'.1.w, hval, Category.assoc])
  have ha₀ : a₀ ≫ pullback.fst _ _ = a' := pullback.lift_fst _ _ _
  have ha₀' : a₀ ≫ BO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀B : IsGrpPullback A₀ BO j a₀ :=
    hBO.cancel (ha'.congr hval ha₀.symm) ha₀'
  let ψ₀ : A₀.left ⟶ GO.left := pullback.lift ψ (A₀.hom ≫ j) (by
    rw [hψ.1.w, ← hpt, Category.assoc])
  have hψ₀ : ψ₀ ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hψ₀' : ψ₀ ≫ GO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀G : IsGrpPullback A₀ GO j ψ₀ :=
    hGO.cancel (hψ.congr hpt.symm hψ₀.symm) hψ₀'
  have hj : GlobalTheory.IsGenericPointHom j := GlobalTheory.IsGenericPointHom.fractionField (M.O z) Ω
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec (M.O z)) hj
    hBOs hGOs hA₀B hA₀G

  let φO : AK.left ⟶ BO.left := pullback.lift φK (AK.hom ≫ spMap v) (by
    rw [hφK.1.w, hyK', Category.assoc])
  have hφO : φO ≫ pullback.fst _ _ = φK := pullback.lift_fst _ _ _
  have hφO' : φO ≫ BO.hom = AK.hom ≫ spMap v := pullback.lift_snd _ _ _
  have hAKB : IsGrpPullback AK BO (spMap v) φO := hBO.cancel (hφK.congr hyK' hφO.symm) hφO'

  obtain ⟨-, hGsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨hBOf, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian BO hBOs
  obtain ⟨-, hGOsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian GO hGOs
  obtain ⟨hjq, hjd⟩ := hj.quasiCompact_and_dominant
  have hEw : E.hom.left ≫ GO.hom = BO.hom := Over.w E.hom
  refine ⟨φO ≫ E.hom.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · refine ((hAKB.comp (isGrpPullback_of_iso E)).comp hGO).congr ?_ ?_
    · rw [Category.comp_id, hs]
    · simp only [Category.assoc]
  · intro e F e₀ he₀a he₀ψ eK heK
    let eO := (Over.pullback (spMap ι')).map e
    let FO := (Over.pullback ιO).map F
    have heO : eO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e.left := pullback.lift_fst _ _ _
    have heO' : eO.left ≫ BO.hom = BO.hom := Over.w eO
    have hFO : FO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.left := pullback.lift_fst _ _ _
    have hFO' : FO.left ≫ GO.hom = GO.hom := Over.w FO
    have h1 : e₀.left ≫ a₀ = a₀ ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, ha₀, Category.assoc, heO, ← Category.assoc, ha₀, he₀a]
      · change e₀.left ≫ a₀ ≫ BO.hom = a₀ ≫ eO.left ≫ BO.hom
        rw [heO', ha₀', ← Category.assoc, Over.w e₀]
    have h2 : e₀.left ≫ ψ₀ = ψ₀ ≫ FO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₀, Category.assoc, hFO, ← Category.assoc, hψ₀, he₀ψ]
      · change e₀.left ≫ ψ₀ ≫ GO.hom = ψ₀ ≫ FO.left ≫ GO.hom
        rw [hFO', hψ₀', ← Category.assoc, Over.w e₀]
    have h3 : eO ≫ E.hom = E.hom ≫ FO := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hA₀B.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← h1, Category.assoc, hE, ← Category.assoc, hE, h2]
    have h4 : eK.left ≫ φO = φO ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, Category.assoc, heO, ← Category.assoc, hφO, heK]
      · change eK.left ≫ φO ≫ BO.hom = φO ≫ eO.left ≫ BO.hom
        rw [heO', hφO', ← Category.assoc, Over.w eK]
    have h5 := congrArg (fun f => f.left ≫ pullback.fst G.hom ιO) h3
    simp only [Over.comp_left, Category.assoc, hFO] at h5
    rw [← Category.assoc, h4, Category.assoc, h5]
    simp only [Category.assoc]
  · intro b gγ w hb hw hwa hwψ T x vv hx hv
    by_cases hT : IsEmpty T
    · exact (isInitialOfIsEmpty (X := T)).hom_ext _ _
    obtain ⟨t₀⟩ := not_isEmpty_iff.1 hT
    obtain ⟨W, h, s', ⟨h1, h2⟩, hs', rfl⟩ := id hv
    have hzpt : (x ≫ AK.hom ≫ s) t₀ = z := by
      simp only [Scheme.Hom.comp_apply]
      exact congrArg s (Subsingleton.elim _ _)
    have hzW : z ∈ W := by rw [← hzpt, ← hs']; exact (s' t₀).2
    have hr : Set.range ιO ⊆ Set.range W.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hp : ιO p ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.range_fromSpecStalk] at hp
      exact Specializes.mem_open hp W.isOpen hzW
    let ℓ := IsOpenImmersion.lift W.ι ιO hr
    have hℓ : ℓ ≫ W.ι = ιO := IsOpenImmersion.lift_fac _ _ _
    let bO : Sp (M.O z) ⟶ BO.left := pullback.lift (spMap ι' ≫ b) (𝟙 _) (by
      rw [Category.assoc, hb, Category.comp_id, Category.id_comp])
    have hbO : bO ≫ pullback.fst _ _ = spMap ι' ≫ b := pullback.lift_fst _ _ _
    have hbO' : bO ≫ BO.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hEG : E.hom.left ≫ pullback.fst G.hom ιO ≫ G.hom = BO.hom ≫ ιO := by
      rw [pullback.condition, ← Category.assoc, ← hEw]; rfl
    have hσ : bO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ℓ ≫ h := by
      refine ext_of_isDominant_of_isSeparated G.hom ?_ j ?_
      · rw [Category.assoc, Category.assoc, hEG, ← Category.assoc, hbO', Category.id_comp, Category.assoc, h1, hℓ]
      · have hjb : j ≫ bO = w ≫ a₀ := by
          apply pullback.hom_ext
          · rw [Category.assoc, hbO, Category.assoc, ha₀, hwa, hval, Category.assoc]
          · change j ≫ bO ≫ BO.hom = w ≫ a₀ ≫ BO.hom
            rw [hbO', ha₀', ← Category.assoc, hw, Category.comp_id, Category.id_comp]
        rw [← Category.assoc, hjb, Category.assoc, ← Category.assoc a₀, hE, hψ₀, hwψ, ← Category.assoc]
        exact (h2 _ (by rw [Category.assoc, hℓ]; exact hpt)).symm
    have hxb : x ≫ φO = (x ≫ AK.hom ≫ spMap v) ≫ bO := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, hx, Category.assoc, hbO, hyK']
        simp only [Category.assoc]
      · change x ≫ φO ≫ BO.hom = (x ≫ AK.hom ≫ spMap v) ≫ bO ≫ BO.hom
        rw [hφO', hbO', Category.comp_id]
    refine ValAt.unique ?_ hv
    refine ⟨W, h, (x ≫ AK.hom ≫ spMap v) ≫ ℓ, ⟨h1, h2⟩, ?_, ?_⟩
    · rw [Category.assoc, hℓ]
      simp only [Category.assoc, hs]
    · have hxb' : x ≫ φO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ((x ≫ AK.hom ≫ spMap v) ≫ ℓ) ≫ h := by
        rw [← Category.assoc x φO, hxb, Category.assoc, hσ]
        simp only [Category.assoc]
      simpa only [Category.assoc] using hxb'.symm

end GlobalTheory.Poinc.Spread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsoSpecialisesToFieldPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_iso_specialises_to_fieldPoints : ∀ (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω), IsNormalScheme M.Z → ∀ (G : Over M.Z) [GrpObj G], IsSemiAbelian G → ∀ (R' : Subalgebra o Ω) (B : Over (Sp R')) [GrpObj B], IsSemiAbelian B → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R'.val.toRingHom) a' → IsGrpPullback A₀ G M.pt ψ → ∀ (K : Type) [Field K] (s : Sp K ⟶ M.Z), R' ≤ M.O (s (closedPoint K)) → ∀ (yK : R' →+* K), (∀ x : R', yK x = M.val s x) → ∀ (AK : Over (Sp K)) [GrpObj AK] (φK : AK.left ⟶ B.left), IsGrpPullback AK B (spMap yK) φK → ∃ Ψ : AK.left ⟶ G.left, IsGrpPullback AK G s Ψ ∧ (∀ (e : B ⟶ B) (F : G ⟶ G) (e₀ : A₀ ⟶ A₀), e₀.left ≫ a' = a' ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left → ∀ eK : AK ⟶ AK, eK.left ≫ φK = φK ≫ e.left → eK.left ≫ Ψ = Ψ ≫ F.left) ∧ ∀ (b : Sp R' ⟶ B.left) (gγ : Over.mk M.pt ⟶ G) (w : Sp Ω ⟶ A₀.left), b ≫ B.hom = 𝟙 _ → w ≫ A₀.hom = 𝟙 _ → w ≫ a' = spMap R'.val.toRingHom ≫ b → w ≫ ψ = gγ.left → ∀ (T : Scheme.{0}) (x : T ⟶ AK.left) (v : T ⟶ G.left), x ≫ φK = x ≫ AK.hom ≫ spMap yK ≫ b → ValAt gγ (x ≫ AK.hom ≫ s) v → x ≫ Ψ = v := by
  first | exact @GlobalTheory.Poinc.Spread.spread_fibre | exact GlobalTheory.Poinc.Spread.spread_fibre | (intros; apply GlobalTheory.Poinc.Spread.spread_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalk
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

def jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂) :
    integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.Z.presheaf.stalk z₂ :=
  (M₂.stalkEquiv z₂).symm.toRingHom.comp ((RingHom.id Ω₂).restrict _ (M₂.O z₂) h)

theorem stalkHom_jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : M₂.stalkHom z₂ (jMap z₂ h b) = b := by
  rw [← RatModel.coe_stalkEquiv]
  simp [jMap]

theorem jMap_mem_max_iff (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (c : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    jMap z₂ h c ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ ¬ ((c : Ω₂) ≠ 0 ∧ (c : Ω₂)⁻¹ ∈ M₂.O z₂) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← MulEquiv.isUnit_map (M₂.stalkEquiv z₂).toMulEquiv, RatModel.isUnit_O_iff]
  change ¬ ((M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂) ≠ 0 ∧ (M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂)⁻¹ ∈ M₂.O z₂) ↔ _
  rw [RatModel.coe_stalkEquiv, stalkHom_jMap]

theorem algHom_mem_integralClosure
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (τ : Ω₂ →ₐ[Ω₁] Ω₂) {b : Ω₂} (hb : b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    τ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ := by
  let τ' : Ω₂ →ₐ[M₁.Z.presheaf.stalk z₁] Ω₂ :=
    { τ.toRingHom with
      commutes' := fun x => by
        change τ (algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x) = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x
        rw [halg]
        exact τ.commutes _ }
  exact IsIntegral.map τ' hb

theorem algHom_mem_O
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (τ : Ω₂ →ₐ[Ω₁] Ω₂)
    (hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ → (τ s)⁻¹ ∈ M₂.O z₂)
    {x : Ω₂} (hx : x ∈ M₂.O z₂) : τ x ∈ M₂.O z₂ := by
  obtain ⟨b, hb, s, hs, hs0, hsO, rfl⟩ := hloc x hx
  rw [map_div₀, div_eq_mul_inv]
  exact mul_mem (hB _ (algHom_mem_integralClosure halg τ hb)) (hu s hs hs0 hsO)

end GlobalTheory.Poinc.RingSide

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

theorem exists_stalk_ringEquiv
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) (z₂ : M₂.Z)
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (H : ∀ b b' : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b' : Ω₂) = σ b →
      (jMap z₂ hB b ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ jMap z₂ hB b' ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂))) :
    ∃ σ₂ : M₂.Z.presheaf.stalk z₂ ≃+* M₂.Z.presheaf.stalk z₂, ∀ x, M₂.stalkHom z₂ (σ₂ x) = σ (M₂.stalkHom z₂ x) := by
  have hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have hs' : σ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.toAlgHom hs
    have key := H ⟨s, hs⟩ ⟨σ s, hs'⟩ rfl
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mp ⟨hs0, hsO⟩).2
  have hu' : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.symm.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have ht : σ.symm s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.symm.toAlgHom hs
    have key := H ⟨σ.symm s, ht⟩ ⟨s, hs⟩ (σ.apply_symm_apply s).symm
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mpr ⟨hs0, hsO⟩).2
  have hσ : ∀ x ∈ M₂.O z₂, σ x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.toAlgHom hu hx
  have hσ' : ∀ x ∈ M₂.O z₂, σ.symm x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.symm.toAlgHom hu' hx
  let e : M₂.O z₂ ≃+* M₂.O z₂ :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ.symm x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω₂))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : Ω₂))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω₂) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω₂) y) }
  refine ⟨(M₂.stalkEquiv z₂).trans (e.trans (M₂.stalkEquiv z₂).symm), fun x => ?_⟩
  rw [← RatModel.coe_stalkEquiv, ← RatModel.coe_stalkEquiv]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

theorem injective_of_ext
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    {V V' : Type} [CommRing V] [CommRing V'] (ev : M₁.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : M₂.Z.presheaf.stalk z₂ →+* V') (hev : Function.Injective ev) (hio : Function.Injective io)
    (hE : ∀ x x₂, M₂.stalkHom z₂ x₂ = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) → ev₂ x₂ = io (ev x)) :
    Function.Injective ev₂ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hy0
  have hY : M₂.stalkHom z₂ y ≠ 0 := by
    intro h
    apply hy0
    apply M₂.stalkHom_injective z₂
    rw [h, map_zero]
  have hYO : M₂.stalkHom z₂ y ∈ M₂.O z₂ := by
    rw [← RatModel.coe_stalkEquiv]
    exact (M₂.stalkEquiv z₂ y).2
  obtain ⟨b, hb, s, hs, hs0, -, hYe⟩ := hloc _ hYO
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_div] at hYe
    exact hY hYe
  have hjb : jMap z₂ hB ⟨b, hb⟩ = y * jMap z₂ hB ⟨s, hs⟩ := by
    apply M₂.stalkHom_injective z₂
    rw [map_mul, stalkHom_jMap, stalkHom_jMap, hYe]
    exact (div_mul_cancel₀ b hs0).symm
  have hev0 : ev₂ (jMap z₂ hB ⟨b, hb⟩) = 0 := by
    rw [hjb, map_mul, hy, zero_mul]
  have hbB : (⟨b, hb⟩ : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≠ 0 := fun h =>
    hb0 (congrArg Subtype.val h)
  have hne := Ideal.comap_ne_bot_of_integral_mem hbB (Ideal.mem_span_singleton_self _)
    (integralClosure.isIntegral _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  have h1 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = io (ev a) := by
    apply hE
    rw [stalkHom_jMap]
    exact halg a
  have h2 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = 0 := by
    rw [← hc, map_mul, map_mul, hev0, mul_zero]
  rw [h2] at h1
  have h3 : ev a = ev 0 := hio (by rw [map_zero, map_zero, ← h1])
  exact ha0 (hev h3)

end GlobalTheory.Poinc.RingSide


open GlobalTheory.Poinc.RingSide in
theorem GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  intro g n F W Z i X₁ act 𝔗 z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ x =
      algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔗.X₂.M.Z := by
    exact @GlobalTheory.IsNormalScheme.pred _ 𝔗.X₂.normal
  obtain ⟨𝔷, h𝔷⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁)
  obtain ⟨z₂, hz₂, hmem⟩ := GlobalTheory.Poinc.FinPts.maximal_point hN 𝔗.p_fin 𝔗.p_pt halg 𝔷 h𝔷
  have hB : ∀ b ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, b ∈ 𝔗.X₂.M.O z₂ :=
    fun b hb => GlobalTheory.Poinc.FinPts.mem_O_of_isIntegral hN 𝔗.p_pt halg hb hz₂
  have hloc := GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O _ _ _ _ X₁.M 𝔗.X₂.M 𝔗.p hN
    𝔗.p_fin 𝔗.p_pt z₁ z₂ hz₂
  refine ⟨z₂, jMap z₂ hB, hz₂, fun b => stalkHom_jMap z₂ hB b, ?_, ?_, ?_, ?_⟩
  · have hc : (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap (jMap z₂ hB) = 𝔷 := by
      ext c
      rw [Ideal.mem_comap, jMap_mem_max_iff, hmem c]
      tauto
    rw [hc]
    exact h𝔷
  · intro x hx
    exact GlobalTheory.Poinc.FinPts.isIntegral_of_mem_O 𝔗.p_fin 𝔗.p_pt halg hx
  · intro σ H
    exact exists_stalk_ringEquiv halg z₂ hB hloc σ H
  · intro V _ ev V' _ io ev₂ hev hio hE
    exact injective_of_ext halg hB hloc ev io ev₂ hev hio hE.2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalkStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_galois_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk | exact GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk | (intros; apply GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatrices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_of_coords {S : Scheme.{0}} {B C X : Over S} [GrpObj B] [GrpObj C] [GrpObj X]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a)
    (z : X ⟶ B) (h : ∀ a, IsMonHom (z ≫ pr a)) : IsMonHom z := by
  have hm : ∀ (T : Over S) (x y : T ⟶ X), (x * y) ≫ z = (x ≫ z) * (y ≫ z) := by
    intro T x y
    refine (huniv T (fun a => (x * y) ≫ z ≫ pr a)).unique (fun a => Category.assoc _ _ _) (fun a => ?_)
    haveI := hpr a
    haveI := h a
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← MonObj.mul_comp]
  exact { one_hom := by
            rw [MonObj.one_eq_one, MonObj.one_eq_one]
            exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ X ↦ x ≫ z) (hm _))
          mul_hom := by
            rw [MonObj.mul_eq_mul, hm, MonObj.mul_eq_mul, MonObj.comp_mul]
            simp }

theorem isMonHom_one {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] : IsMonHom (1 : B ⟶ C) :=
  inferInstanceAs (IsMonHom (toUnit B ≫ η[C]))

theorem exists_incl {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a) :
    ∃ z : Fin 8 → (C ⟶ B), (∀ u, IsMonHom (z u)) ∧ ∀ u v, z u ≫ pr v = if v = u then 𝟙 C else 1 := by
  choose z hz _ using fun u : Fin 8 => huniv C (fun v => if v = u then 𝟙 C else 1)
  refine ⟨z, fun u => isMonHom_of_coords pr hpr huniv (z u) fun a => ?_, hz⟩
  rw [hz u a]
  split_ifs
  · infer_instance
  · exact isMonHom_one

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_prod {S : Scheme.{0}} {X M : Over S} [GrpObj X] [GrpObj M] [IsCommMonObj M] {J : Type}
    (f : J → (X ⟶ M)) (hf : ∀ i, IsMonHom (f i)) (s : Finset J) : IsMonHom (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty]; exact isMonHom_one
  · intro a s ha ih
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact inferInstanceAs (IsMonHom (lift (f a) (∏ i ∈ s, f i) ≫ μ[M]))

theorem prod_comp {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] [IsCommMonObj M] [IsCommMonObj N] {J : Type}
    (f : J → (X ⟶ M)) (s : Finset J) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, f i ≫ g := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8


open PowChar in
theorem characters_eighthPower_elementaryMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W _ pr hpr huniv _ pG hpG hgen c hc
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have ext : ∀ {H H' : Over (Sp R)} [GrpObj H] [GrpObj H'], IsSemiAbelian H → IsSemiAbelian H' →
      ∀ (F₁ F₂ : H ⟶ H'), IsMonHom F₁ → IsMonHom F₂ →
        (Over.pullback (jK R)).map F₁ = (Over.pullback (jK R)).map F₂ → F₁ = F₂ := by
    intro H H' _ _ h h' F₁ F₂ h₁ h₂ e
    exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) H H' h h' _ inferInstance).unique
      ⟨h₁, e⟩ ⟨h₂, rfl⟩
  obtain ⟨z, hzm, hz⟩ := exists_incl pr hpr huniv
  have hic : ∀ u, ∃ ic : G ⟶ G', IsMonHom ic ∧ (Over.pullback (jK R)).map ic = U.gen.hom ≫ z u ≫ U'.gen.inv := by
    intro u
    haveI := hzm u
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G G' hG hG'
      (U.gen.hom ≫ z u ≫ U'.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose ic hicm hicg using hic
  have hicp : ∀ u v, ic u ≫ pG v = if v = u then 𝟙 G else 1 := by
    intro u v
    haveI := hicm u
    haveI := hpG v
    have key : (Over.pullback (jK R)).map (ic u ≫ pG v) ≫ U.gen.hom = U.gen.hom ≫ (if v = u then 𝟙 A.A else 1) := by
      rw [Functor.map_comp, Category.assoc, hgen v, ← Category.assoc, hicg u]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hz u v]
    by_cases h : v = u
    · rw [if_pos h] at key ⊢
      refine ext hG hG _ _ inferInstance inferInstance ?_
      rw [← cancel_mono U.gen.hom, key, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [if_neg h] at key ⊢
      refine ext hG hG _ _ inferInstance isMonHom_one ?_
      rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  have hpw : ∀ w, (∏ v, pG v ≫ ic v) ≫ pG w = pG w := by
    intro w
    haveI := hpG w
    rw [PowChar.prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hicp w w, if_pos rfl, Category.comp_id]
    · intro v _ hv
      rw [Category.assoc, hicp v w, if_neg (Ne.symm hv), MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hprod : (∏ v, pG v ≫ ic v) = 𝟙 G' := by
    have hm : IsMonHom (∏ v, pG v ≫ ic v) :=
      isMonHom_prod _ (fun v => by haveI := hpG v; haveI := hicm v; infer_instance) _
    refine ext hG' hG' _ _ hm inferInstance ?_
    rw [CategoryTheory.Functor.map_id, ← cancel_mono U'.gen.hom, Category.id_comp]
    refine (huniv _ (fun w => U'.gen.hom ≫ pr w)).unique (fun w => ?_) (fun w => rfl)
    rw [Category.assoc, ← hgen w, ← Category.assoc, ← Functor.map_comp, hpw w]
  have hinj : Function.Injective (RingHom.id R) := Function.injective_id
  have hk : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ h => h
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch R hR G' hG' D' A' U' G hG D A U (ic u) (hicm u)
  obtain ⟨hid, hone, -⟩ := torMatch_id_one_mul R hR G hG D A U G hG D A U
  obtain ⟨hid', hone', hmul'⟩ := torMatch_id_one_mul R hR G' hG' D' A' U' G' hG' D' A' U'
  obtain ⟨-, hone'', -⟩ := torMatch_id_one_mul R hR G hG D A U G' hG' D' A' U'
  have hdc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG v).left R hR G hG D A U
      (RingHom.id R) (ic u).left hinj hk (c v) (d u) (hc v) (hd u)
    rw [← Over.comp_left, hicp u v, RingHom.id_comp] at h1
    by_cases h : v = u
    · rw [if_pos h] at h1 ⊢
      rw [Over.id_left] at h1
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hid
    · rw [if_neg h] at h1 ⊢
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hone
  have hcd : ∑ v, (c v).comp (d v) = AddMonoidHom.id _ := by
    have hs : ∀ s : Finset (Fin 8), TorMatch U' U' (RingHom.id R) (∏ v ∈ s, pG v ≫ ic v).left
        (∑ v ∈ s, (c v).comp (d v)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · rw [Finset.prod_empty, Finset.sum_empty]
        exact hone'
      · intro a s ha ih
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have h1 := torMatch_comp R hR G' hG' D' A' U' R hR G hG D A U (RingHom.id R) (ic a).left R hR G' hG' D' A' U'
          (RingHom.id R) (pG a).left hinj hk (d a) (c a) (hd a) (hc a)
        rw [← Over.comp_left, RingHom.id_comp] at h1
        exact hmul' _ _ _ _ h1 ih
    have h2 := hs Finset.univ
    rw [hprod, Over.id_left] at h2
    exact torMatch_unique R hR G' hG' D' A' U' R hR G' hG' D' A' U' _ _ hinj _ _ h2 hid'
  refine ⟨?_, ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x u => d u x, fun y => ?_, fun x => ?_⟩
    · funext u
      have e : ∀ v, d u (c v (y v)) = if v = u then y v else 0 := fun v => by
        have := DFunLike.congr_fun (hdc u v) (y v)
        rw [AddMonoidHom.comp_apply] at this
        rw [this]
        split_ifs <;> rfl
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have := DFunLike.congr_fun hcd x
      simpa using this
  · intro a b f f₁ m hf hf₁ hff₁ hm w x
    haveI := hf
    haveI := hpG w
    have hfp : f ≫ pG w = if w = a then pG b else 1 := by
      have key : (Over.pullback (jK R)).map (f ≫ pG w) ≫ U.gen.hom = U'.gen.hom ≫ (if w = a then pr b else 1) := by
        rw [Functor.map_comp, Category.assoc, hgen w, ← Category.assoc, hff₁, Category.assoc, hf₁.2 w]
      by_cases h : w = a
      · rw [if_pos h] at key ⊢
        refine ext hG' hG _ _ inferInstance (hpG b) ?_
        rw [← cancel_mono U.gen.hom, key, hgen b]
      · rw [if_neg h] at key ⊢
        refine ext hG' hG _ _ inferInstance isMonHom_one ?_
        rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG w).left R hR G' hG' D' A' U'
      (RingHom.id R) f.left hinj hk (c w) m (hc w) (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G' hG' D' A' U' f hf m hm)
    rw [← Over.comp_left, hfp, RingHom.id_comp] at h1
    have e : m.comp (c w) = if w = a then c b else 0 := by
      by_cases h : w = a
      · rw [if_pos h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 (hc b)
      · rw [if_neg h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 hone''
    have := DFunLike.congr_fun e x
    rw [AddMonoidHom.comp_apply] at this
    rw [this]
    split_ifs <;> rfl

end GlobalTheory.Poinc.Eq8
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatricesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  first | exact @GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices | exact GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices | (intros; apply GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices <;> assumption)
end
end
