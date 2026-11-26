module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CombVal

section General

variable {S S' : Scheme.{0}} {G : CategoryTheory.Over S} {G' : CategoryTheory.Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem push_mul (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b)
    (x y : CategoryTheory.Over.mk a ⟶ G') (x₀ y₀ : CategoryTheory.Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hab
  exact h.2 (CategoryTheory.Over.mk a) x y x₀ y₀ hx hy

theorem push_one (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b) :
    (1 : CategoryTheory.Over.mk b ⟶ G).left = (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ := by
  subst hab
  exact (congrArg (fun z => z.left) (map_one (pushHom h (CategoryTheory.Over.mk a)))).symm

theorem one_left_congr {A : Scheme.{0}} {a b : A ⟶ S} (h : a = b) :
    (1 : CategoryTheory.Over.mk a ⟶ G).left = (1 : CategoryTheory.Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem push_mul₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) (x y : CategoryTheory.Over.mk a ⟶ G') (x' y' : CategoryTheory.Over.mk a₂ ⟶ G₂)
    (hx : x.left ≫ φ = x'.left ≫ φ₂) (hy : y.left ≫ φ = y'.left ≫ φ₂) :
    (x * y).left ≫ φ = (x' * y').left ≫ φ₂ := by
  have wx : (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w x]
    rfl
  have wy : (y.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w y]
    rfl
  let W : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (x.left ≫ φ) wx
  let W' : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (y.left ≫ φ) wy
  exact (push_mul h rfl x y W W' rfl rfl).symm.trans (push_mul h₂ hab.symm x' y' W W' hx hy)

theorem push_one₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) :
    (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk a₂ ⟶ G₂).left ≫ φ₂ :=
  (push_one h hab).symm.trans (push_one h₂ rfl)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] [Algebra c.F F]

abbrev qe (y : FrPt Xo c F) : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.XF c :=
  spMap (algebraMap F (DualNumber F)) ≫ Small.ptF y

theorem qe_fst (y : FrPt Xo c F) : qe y ≫ pullback.fst _ _ = spMap (algebraMap F (DualNumber F)) ≫ y.x := by
  rw [Category.assoc, Small.ptF_fst]

def liftP (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G :=
  CategoryTheory.Over.homMk (Y.m0.cart.1.lift p.left (qe y) ((CategoryTheory.Over.w p).trans (qe_fst y).symm)) (Y.m0.cart.1.lift_snd _ _ _)

theorem pointLift_fst (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) :
    (liftP Y y p).left ≫ Y.m0.toSABMap.φ = p.left :=
  Y.m0.cart.1.lift_fst _ _ _

theorem pointLift_eq (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) (P : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G)
    (h : P.left ≫ Y.m0.toSABMap.φ = p.left) : (liftP Y y p).left = P.left := by
  apply Y.m0.cart.1.hom_ext
  · exact (pointLift_fst Y y p).trans h.symm
  · exact (CategoryTheory.Over.w (liftP Y y p)).trans (CategoryTheory.Over.w P).symm

variable {Y : Model Xo c β} {X : Scheme.{0}} {tX : SAB H X} {f : X ⟶ Y.X} (m : SABMap tX Y.t f)
  {g : Spec (CommRingCat.of F) ⟶ X} {EC : Type} [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC)
  (y : FrPt Xo c F)

def Rd (p : tEps y.x ⟶ Xo.univ.t.G) (e : EC) : Prop :=
  (MC.pt e).left ≫ m.φ = (liftP Y y p).left ≫ Y.m.φ

variable {y}

theorem base_eq (hY : Small.ptY Y y = g ≫ f) :
    (spMap (algebraMap F (DualNumber F)) ≫ g) ≫ f = qe y ≫ Y.jQ ≫ pullback.fst _ _ := by
  rw [Category.assoc, Category.assoc, ← hY]
  rfl

theorem pt_zero : MC.pt 0 = 1 := by
  have h := MC.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem rd_one (hY : Small.ptY Y y = g ≫ f) : Rd m MC y 1 0 := by
  have h1 : (liftP Y y 1).left = (1 : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G).left := by
    refine pointLift_eq Y y 1 1 ?_
    exact ((push_one Y.m0.cart (qe_fst y)).symm).trans (one_left_congr rfl)
  unfold Rd
  rw [h1, pt_zero]
  exact push_one₂ m.cart Y.m.cart (base_eq hY)

theorem rd_mul (hY : Small.ptY Y y = g ≫ f) {p p' : tEps y.x ⟶ Xo.univ.t.G} {e e' : EC}
    (h : Rd m MC y p e) (h' : Rd m MC y p' e') : Rd m MC y (p * p') (e + e') := by
  have h1 : (liftP Y y (p * p')).left = (liftP Y y p * liftP Y y p').left := by
    refine pointLift_eq Y y _ _ ?_
    exact (push_mul Y.m0.cart (qe_fst y) (liftP Y y p) (liftP Y y p') p p'
      (pointLift_fst Y y p).symm (pointLift_fst Y y p').symm).symm
  unfold Rd
  rw [h1, MC.add]
  exact push_mul₂ m.cart Y.m.cart (base_eq hY) (MC.pt e) (MC.pt e') (liftP Y y p) (liftP Y y p') h h'

theorem scale_base (a : F) : spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap F (DualNumber F)) =
    spMap (algebraMap F (DualNumber F)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem rd_smul {p p₂ : tEps y.x ⟶ Xo.univ.t.G} {e : EC} (a : F)
    (hp : p₂.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ p.left) (h : Rd m MC y p e) :
    Rd m MC y p₂ (a • e) := by
  have h1 : (liftP Y y p₂).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (liftP Y y p).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [pointLift_fst, Category.assoc, pointLift_fst, hp]
    · have e₁ := CategoryTheory.Over.w (liftP Y y p)
      have e₂ := CategoryTheory.Over.w (liftP Y y p₂)
      refine e₂.trans ?_
      rw [Category.assoc, e₁]
      show qe y = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ qe y
      rw [qe, ← Category.assoc, scale_base]
  unfold Rd at h ⊢
  rw [h1, MC.smul, Category.assoc, Category.assoc, h]
  rfl

theorem rd_prod (hY : Small.ptY Y y = g ≫ f) :
    ∀ (n : ℕ) (u : Fin n → (tEps y.x ⟶ Xo.univ.t.G)) (e : Fin n → EC), (∀ i, Rd m MC y (u i) (e i)) →
      Rd m MC y (List.ofFn u).prod (∑ i, e i)
  | 0, u, e, _ => by
    simpa using rd_one m MC hY
  | n + 1, u, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact rd_mul m MC hY (h 0) (rd_prod hY n _ _ fun i => h i.succ)

end CombVal

theorem comb_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hY n v hv e he cf w hc
  obtain ⟨u, hu, rfl⟩ := hc
  refine ⟨CategoryTheory.Over.w ((List.ofFn u).prod), ?_⟩
  have h0 : ∀ j, CombVal.Rd m MC y (CategoryTheory.Over.homMk (v j) (hv j).1 : tEps y.x ⟶ Xo.univ.t.G) (e j) := he
  have h1 : ∀ j, CombVal.Rd m MC y (u j) (cf j • e j) := fun j => CombVal.rd_smul m MC (cf j) (hu j) (h0 j)
  exact CombVal.rd_prod m MC hY n u (fun j => cf j • e j) h1

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPointStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_lie_model_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem locallyQuasiFinite_pow_semiAbelian :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N →
      LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  intro S G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have : LocallyOfFiniteType (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType ((𝟙 G) ^ N).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker S G G _ hm inferInstance inferInstance
    fun Ω _ _ t => ?_
  simp only [MonObj.comp_pow, Category.comp_id]
  exact GlobalTheory.HomExt.finite_torsion_points hG t hN

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFiniteStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_map_locally_quasi_finite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian | exact GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelian
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelian
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open scoped CategoryTheory.Obj

theorem exists_extended_identification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr))) (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (b : t'.G.left ⟶ tX.G.left), IsGrpPullback t'.G tX.G (FinRd.Roots.gen T zV) b → (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) → ∃ Ψ : G.G.left ⟶ tX.G.left, IsGrpPullback G.G tX.G zV Ψ ∧ m2.φ ≫ Ψ = b ∧ ∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left := by
  intro E _ _ _ H hE X tX T zV G t' m2 b hb hact
  have hp : IsGrpPullback ((Over.pullback zV).obj tX.G) tX.G zV (Limits.pullback.fst tX.G.hom zV) :=
    isGrpPullback_pullback tX.G zV
  let ψ : t'.G.left ⟶ ((Over.pullback zV).obj tX.G).left :=
    Limits.pullback.lift b (t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))
      (by rw [hb.1.w, Category.assoc])
  have hψf : ψ ≫ Limits.pullback.fst tX.G.hom zV = b := Limits.pullback.lift_fst _ _ _
  have hψs : ψ ≫ ((Over.pullback zV).obj tX.G).hom =
      t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := Limits.pullback.lift_snd _ _ _
  have hψ : IsGrpPullback t'.G ((Over.pullback zV).obj tX.G)
      (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) ψ :=
    hp.cancel (hb.congr rfl hψf.symm) hψs
  have hj : GlobalTheory.IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) :=
    GlobalTheory.IsGenericPointHom.fractionField T.V T.Fr
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec T.V
  have hH' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback zV).obj tX.G) := by
    have h := tX.semi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; show Smooth (Limits.pullback.snd tX.G.hom zV); infer_instance
    · have := h.separated; show IsSeparated (Limits.pullback.snd tX.G.hom zV); infer_instance
    · have := h.quasiCompact; show QuasiCompact (Limits.pullback.snd tX.G.hom zV); infer_instance
    · have := h.geomConnected; show GeometricallyConnected (Limits.pullback.snd tX.G.hom zV); infer_instance
    · intro Ω _ _ q
      obtain ⟨F⟩ := h.fibres Ω (q ≫ zV)
      exact ⟨torusExtOfIso (pullCompIso q zV tX.G) F⟩
  obtain ⟨e, ⟨hmon, heq⟩, -⟩ := hE.generic_existsUnique_iso_of_extensions hS hj G.semi hH' m2.cart hψ
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G.G G.semi
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hH'
  refine ⟨e.hom.left ≫ Limits.pullback.fst tX.G.hom zV,
    ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · rw [← Category.assoc, heq, hψf]
  · have hB : ((Over.pullback zV).map (tX.act.act a)).left ≫ Limits.pullback.fst tX.G.hom zV =
        Limits.pullback.fst tX.G.hom zV ≫ (tX.act.act a).left := Limits.pullback.lift_fst _ _ _
    have hψa : (t'.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback zV).map (tX.act.act a)).left := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hB, hψf, ← Category.assoc ψ, hψf, hact]
      · have h₁ := hψs
        have h₂ := Over.w ((Over.pullback zV).map (tX.act.act a))
        have h₃ := Over.w (t'.act.act a)
        change _ ≫ ((Over.pullback zV).obj tX.G).hom = _ ≫ ((Over.pullback zV).obj tX.G).hom
        rw [Category.assoc, Category.assoc, h₂, h₁, ← Category.assoc, h₃]
    have key : G.act.act a ≫ e.hom = e.hom ≫ (Over.pullback zV).map (tX.act.act a) := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m2.cart.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m2.act a, Category.assoc, heq, hψa,
        ← Category.assoc, heq]
    have key' := congrArg (fun f => f.left ≫ Limits.pullback.fst tX.G.hom zV) key
    simp only [Over.comp_left, Category.assoc, hB] at key'
    simpa only [Category.assoc] using key'

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelianStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_pullback_semiabelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr))) (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (b : t'.G.left ⟶ tX.G.left), IsGrpPullback t'.G tX.G (FinRd.Roots.gen T zV) b → (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) → ∃ Ψ : G.G.left ⟶ tX.G.left, IsGrpPullback G.G tX.G zV Ψ ∧ m2.φ ≫ Ψ = b ∧ ∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_extended_identification | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_extended_identification | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_extended_identification <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtends
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.CommonModel

section Ext

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B] {GK : Over (Sp K)} [GrpObj GK]

theorem hom_unique (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a) (g₁ g₂ : A ⟶ B) [IsMonHom g₁] [IsMonHom g₂]
    (h : a ≫ g₁.left = a ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  have hmap : (Over.pullback (spMap (algebraMap V K))).map g₂ =
      (Over.pullback (spMap (algebraMap V K))).map g₁ := by
    have L : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) =
          pullback.fst A.hom (spMap (algebraMap V K)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have R : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.snd B.hom (spMap (algebraMap V K)) =
          pullback.snd A.hom (spMap (algebraMap V K)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [L, L, ← hio, Category.assoc, Category.assoc, h]
    · rw [R, R]
  obtain ⟨F, -, hu⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    ((Over.pullback (spMap (algebraMap V K))).map g₁) inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap⟩).symm

theorem hom_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ F : A ⟶ B, IsMonHom F ∧ a ≫ F.left = b := by
  obtain ⟨io, hiom, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  obtain ⟨ko, -, hko⟩ := grpPullback_iso ha (isGrpPullback_pullback A (spMap (algebraMap V K)))
  obtain ⟨ko', hko'm, hko'⟩ := grpPullback_iso hb (isGrpPullback_pullback B (spMap (algebraMap V K)))
  have := hiom
  have := hko'm
  obtain ⟨F, ⟨hFm, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply ha.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨F, hFm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst A.hom (spMap (algebraMap V K)) ≫ F.left =
      ((Over.pullback (spMap (algebraMap V K))).map F).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hF, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem iso_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ a ≫ e.hom.left = b := by
  obtain ⟨F, hFm, hF⟩ := hom_exists V K hA hB ha hb
  obtain ⟨F', hF'm, hF'⟩ := hom_exists V K hB hA hb ha
  have := hFm
  have := hF'm
  have h₁ : F ≫ F' = 𝟙 _ := hom_unique V K hA hA ha _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF, hF', Over.id_left, Category.comp_id])
  have h₂ : F' ≫ F = 𝟙 _ := hom_unique V K hB hB hb _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF', hF, Over.id_left, Category.comp_id])
  exact ⟨⟨F, F', h₁, h₂⟩, hFm, hF⟩

end Ext

end GlobalTheory.CompanionTheory.Ar.CommonModel

namespace GlobalTheory.CompanionTheory.Ar

theorem semiAbelian_commonModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  intro V K _ _ _ _ _ _ X X' x x' G G' _ _ GK _ φ φ' hG hG' hφ hφ'
  have pA := isGrpPullback_pullback G x
  have pB := isGrpPullback_pullback G' x'
  have sA : IsSemiAbelian ((Over.pullback x).obj G) := IsSemiAbelian.pullback x G hG
  have sB : IsSemiAbelian ((Over.pullback x').obj G') := IsSemiAbelian.pullback x' G' hG'

  have lift : ∀ {Y : Scheme.{0}} (y : Sp V ⟶ Y) (H : Over Y) [GrpObj H] (θ : GK.left ⟶ H.left),
      IsGrpPullback GK H (spMap (algebraMap V K) ≫ y) θ →
      ∃ κ : GK.left ⟶ ((Over.pullback y).obj H).left,
        IsGrpPullback GK ((Over.pullback y).obj H) (spMap (algebraMap V K)) κ ∧
          κ ≫ pullback.fst H.hom y = θ := by
    intro Y y H _ θ hθ
    have hp := isGrpPullback_pullback H y
    have w : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ ((Over.pullback y).obj H).hom =
        GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
    have f : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ pullback.fst H.hom y = θ := hp.1.lift_fst _ _ _
    exact ⟨_, hp.cancel (by rw [f]; exact hθ) w, f⟩
  obtain ⟨κ, hκ, hκφ⟩ := lift x G φ hφ
  obtain ⟨κ', hκ', hκφ'⟩ := lift x' G' φ' hφ'
  obtain ⟨e, hem, he⟩ := CommonModel.iso_exists V K sA sB hκ hκ'
  have := hem
  refine ⟨(Over.pullback x).obj G, inferInstance, pullback.fst G.hom x,
    e.hom.left ≫ pullback.fst G'.hom x', κ, pA, ?_, hκ, hκφ, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp pB).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, he, hκφ']

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtendsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_generic_iso_extends : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel | exact GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel | (intros; apply GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel <;> assumption)
end
end
