module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroScalarWeightCuspFormComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_mulVec_submatrix_mul_iff {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix m n R) (e : Equiv.Perm n) (C : Matrix n n R) (hC : IsUnit C.det) (cv : m → R) :
    (∃ a, (U.submatrix id e * C).mulVec a = cv) ↔ ∃ a, U.mulVec a = cv := by
  have hs : ∀ b, (U.submatrix id e).mulVec b = U.mulVec (b ∘ e.symm) := fun b => by
    have := Matrix.submatrix_mulVec_equiv U b (Equiv.refl m) e
    simpa using this
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(C.mulVec a) ∘ e.symm, by rw [← Matrix.mulVec_mulVec, hs]⟩
  · rintro ⟨a, rfl⟩
    have hC' : ∀ x, C.mulVec (C⁻¹.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
    refine ⟨C⁻¹.mulVec (a ∘ e), ?_⟩
    rw [← Matrix.mulVec_mulVec, hC', hs]
    congr 1
    funext i
    simp

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem cellFrames_topEigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht
  intro S _ _ y hy z hx k hz σ
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ev z _ hz).comp (cellθ κ k).toRingHom := ⟨_, rfl⟩
  have hzφ : spMap φ ≫ κ k.1 k.2 = z := hφ ▸ eq_spMap_ev k z hz
  have hxφ : y ≫ Y.j = spMap (φ.comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
    rw [← hx, ← hzφ, Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp']
    rfl
  have hV : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).V := hxφ ▸ le_preimage_comp _ (tau_le (A.V k.1).2 le_rfl)
  have hev : ev (y ≫ Y.j) (A.k k.1).V hV = φ.comp (cC A k.1) := by
    rw [ev_congr hxφ _ hV (hxφ ▸ hV)]
    exact ev_spMap_tau (A.V k.1).2 _ _
  have hM : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).M.U := (cellFrames hZ ht).inM hz hx
  have huAt : (cellFrames hZ ht).uAt k z hz σ = ((((A.k k.1).u σ).map (ev (y ≫ Y.j) _ hV)).submatrix id (k.2 σ)) *
      (cellMat (A.V k.1) σ).map φ := by
    refine Matrix.ext fun i j => ?_
    show (ev z _ hz) ((cellθ κ k) (uC A k.1 k.2 σ i j)) = _
    have e2 : ∀ x, (ev z _ hz) ((cellθ κ k) x) = φ x := fun x => by rw [hφ]; rfl
    rw [hev, e2, uC]
    exact RingHom.map_matrix_mul _ _ i j φ
  have hdet : IsUnit ((cellMat (A.V k.1) σ).map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_cellMat, map_one]
    exact isUnit_one
  refine SetLike.ext fun v => ?_
  obtain ⟨cv, rfl⟩ := (vec (A.k k.1).M.toMChart _ hM).surjective v
  refine Iff.trans ?_ ((vec_mem_eigLie _ _ hM σ cv).trans (((LowRank.pm_gen p (A.k k.1).M.toMChart σ hy hM).1 cv).trans
    ((A.k k.1).fix_iff σ _ hV hM cv))).symm
  rw [mem_initSpan, ← exists_mulVec_submatrix_mul_iff _ (k.2 σ) _ hdet, ← huAt]
  exact ⟨fun ⟨a, _, e⟩ => ⟨a, (vec (A.k k.1).M.toMChart _ hM).injective
      (((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).symm.trans e)⟩,
    fun ⟨a, e⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj),
      ((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).trans (congrArg (vec (A.k k.1).M.toMChart _ hM) e)⟩⟩

end GlobalTheory.FlagMod.FieldFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodulesStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellFrames_lastStep_eigenmodules : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen | exact GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen | (intros; apply GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescendsFg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegelDataDescent

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := _root_.GlobalTheory.SiegDesc.isPullback_of_isSquare (S' := S') (S := S) (A' := A') (A := A) (f := f) (φ := φ) (φ₂ := φ₂) hA h

end GlobalTheory.SiegelDataDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}


open Classical in
def trv (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R] (q : Sp R ⟶ X)
    (v : Sp (DualNumber R) ⟶ t.G.left) : Sp (DualNumber R) ⟶ t.G.left :=
  if h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p then hψ.lift v _ h ≫ g ≫ ψ else v

variable (hψ : IsPullback ψ G'.hom t.G.hom p) {R R' : Type} [CommRing R] [CommRing R']

theorem trv_eq (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (w : Sp (DualNumber R) ⟶ G'.left) (hw : w ≫ ψ = v) (hw' : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q) :
    trv hψ g q v = w ≫ g ≫ ψ := by
  have h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p := by
    rw [← hw, Category.assoc, hψ.w, ← Category.assoc, hw']
  rw [trv, dite_eq_left h]
  congr 1
  exact hψ.hom_ext (by rw [hψ.lift_fst, hw]) (by rw [hψ.lift_snd, hw'])


include hψ in
theorem exists_lift (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    ∃ w : Sp (DualNumber R) ⟶ G'.left, w ≫ ψ = v ∧ w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q :=
  ⟨hψ.lift v _ (by rw [hv, Category.assoc]), hψ.lift_fst _ _ _, hψ.lift_snd _ _ _⟩

theorem trv_over (g : G'.left ⟶ G'.left) {b : X ⟶ X} (hg : g ≫ G'.hom = G'.hom ≫ b) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', Category.assoc, Category.assoc, hψ.w, reassoc_of% hg, reassoc_of% hw']
  simp only [Category.assoc]

theorem trv_map (g : G'.left ⟶ G'.left) (σ : R →+* R') (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ v) = spMap (dualMap σ) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have e : spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, e, Category.assoc])]
  simp only [Category.assoc]

theorem trv_comp (g₁ g₂ : G'.left ⟶ G'.left) {b₁ : X ⟶ X} (hg₁ : g₁ ≫ G'.hom = G'.hom ≫ b₁) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ (g₁ ≫ g₂) q v = trv hψ g₂ (q ≫ b₁) (trv hψ g₁ q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ _ q w hw hw', trv_eq hψ g₁ q w hw hw', trv_eq hψ g₂ (q ≫ b₁) (w ≫ g₁) (Category.assoc _ _ _)
    (by rw [Category.assoc, hg₁, reassoc_of% hw'])]
  simp only [Category.assoc]

theorem trv_eq_self (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X)
    (hg : ∀ w : Sp (DualNumber R) ⟶ G'.left, w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q → w ≫ g = w)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v = v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', ← Category.assoc, hg w hw', hw]

end GlobalTheory.EqvTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem secMaps_secPull_of_pointwise : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LL.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ) (LM.pull fst)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k) →
    ∀ (th : LP.Sec) (σ : LL.Sec) (σ' : LM.Sec),
      (∀ (j : (LL.pull φ).ι) (i : LP.ι) (h : (LL.pull φ).U j ⊓ LP.U i ≤ φ ⁻¹ᵁ LL.U (j PUnit.unit)),
        (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
          (show Γ(XA, (LL.pull φ).U j ⊓ LP.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (th.f i)) →
      GlobalTheory.Cartier.SecMaps e σ' σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull th θ) (GlobalTheory.Cartier.secPull σ' fst) := by
  intro Y XA XG θ φ fst hfst LP LL LM hLL ψ e w₀ hw th σ σ' hth he
  subst hfst
  rintro ⟨J, K⟩
  apply fn_ext
  intro y hy
  have hj : (θ ≫ φ) y ∈ LM.U (J PUnit.unit) := mem_pull.1 hy.1
  have hk : θ y ∈ LP.U (K PUnit.unit) := mem_pull.1 hy.2
  obtain ⟨i, hi⟩ := exists_chart hLL ((θ ≫ φ) y)
  have hm1 : (θ ≫ φ) y ∈ LL.U i ⊓ LM.U (J PUnit.unit) := ⟨hi, hj⟩
  have hm2 : θ y ∈ (LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit) := ⟨mem_pull.2 hi, hk⟩
  have ha := congrArg (gs (θ ≫ φ) y (LL.U i ⊓ LM.U (J PUnit.unit))) (he (i, J PUnit.unit))
  have hb := congrArg (gs θ y ((LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit)))
    (hth (fun _ => i) (K PUnit.unit) (inf_le_left.trans fun x hx => mem_pull.1 hx))
  have hc := hw Y (𝟙 Y) y i (J PUnit.unit) (K PUnit.unit) hi hj hk
  simp only [Category.id_comp] at hc
  rw [gs_mul _ y _ hm1, gs_unit _ y _ hm1] at ha
  change gs _ y _ (resG XG _ _) = _ * gs _ y _ (resG XG _ _) at ha
  rw [gs_res _ y _ hm1, gs_res _ y _ hm1] at ha
  dsimp only at hb
  erw [gs_mul _ y _ hm2, gs_unit _ y _ hm2] at hb
  change _ = _ * gs _ y _ (resG XA _ _) at hb
  rw [gs_res _ y _ hm2] at hb
  have hb' : gs (θ ≫ φ) y (LL.U i) (σ.f i) =
      (gw ψ θ y i (K PUnit.unit)).val * gs θ y (LP.U (K PUnit.unit)) (th.f (K PUnit.unit)) :=
    (gs_pull θ φ y _ hi _).symm.trans ((gs_res θ y _ hm2 _).symm.trans hb)
  have hm3 : (𝟙 Y) y ∈ (LM.pull (θ ≫ φ)).U J := hy.1
  have hm4 : (𝟙 Y) y ∈ (LP.pull θ).U K := hy.2
  change gs (𝟙 Y) y _ (resG Y _ (resG Y _ _)) = _
  erw [gs_res _ y _ hy, gs_res _ y _ hm3, gs_pull (𝟙 Y) (θ ≫ φ) y _ hj, gs_mul _ y _ hy, gs_unit _ y _ hy]
  change _ = _ * gs (𝟙 Y) y _ (resG Y _ (resG Y _ _))
  erw [gs_res _ y _ hy, gs_res _ y _ hm4, gs_pull (𝟙 Y) θ y (LP.U (K PUnit.unit)) hk]
  simp only [Category.id_comp]
  change _ = (gw w₀ (𝟙 Y) y (J PUnit.unit) fun _ => K PUnit.unit).val * _
  rw [hc, Units.val_mul, _root_.mul_assoc, ← hb']
  dsimp only [id] at ha
  rw [ha, Units.inv_mul_cancel_left]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGermsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secMaps_secPull_of_pointwise_germs : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LL.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ) (LM.pull fst)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k) →
    ∀ (th : LP.Sec) (σ : LL.Sec) (σ' : LM.Sec),
      (∀ (j : (LL.pull φ).ι) (i : LP.ι) (h : (LL.pull φ).U j ⊓ LP.U i ≤ φ ⁻¹ᵁ LL.U (j PUnit.unit)),
        (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
          (show Γ(XA, (LL.pull φ).U j ⊓ LP.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (th.f i)) →
      GlobalTheory.Cartier.SecMaps e σ' σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull th θ) (GlobalTheory.Cartier.secPull σ' fst) := by
  first | exact @GlobalTheory.secMaps_secPull_of_pointwise | exact GlobalTheory.secMaps_secPull_of_pointwise | (intros; apply GlobalTheory.secMaps_secPull_of_pointwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.IsoComp

theorem pullIsoAlong {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (G : Y ⟶ XG) (hG : θ ≫ φ = G)
    {LP : LB XA} {LL : LB XG} (ψ : LB.Iso LP (LL.pull φ)) (hψ : PGen ψ) :
    ∃ w : LB.Iso (LP.pull θ) (LL.pull G), PGen w ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), G (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) := by
  subst hG
  have hle : ∀ (J : PUnit → LL.ι) (K : PUnit → LP.ι),
      (LL.pull (θ ≫ φ)).U J ⊓ (LP.pull θ).U K ≤ θ ⁻¹ᵁ ((LL.pull φ).U J ⊓ LP.U (K PUnit.unit)) :=
    fun J K x hx => ⟨(mem_pull (F := φ)).2 ((mem_pull (F := θ ≫ φ)).1 hx.1), (mem_pull (F := θ)).1 hx.2⟩
  obtain ⟨w, hw⟩ : ∃ w : LB.Iso (LP.pull θ) (LL.pull (θ ≫ φ)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), (θ ≫ φ) (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) :=
    ⟨⟨fun p => res (hle p.1 p.2) (pullU θ _ (ψ.s (p.1, p.2 PUnit.unit)))⟩, fun Z r z i K hi hK =>
      (gm_res r z (hle (fun _ => i) K) ⟨mem_pull.2 hi, hK⟩ _).trans
        (gm_pull r θ z _ (hle (fun _ => i) K ⟨mem_pull.2 hi, hK⟩) _)⟩
  refine ⟨w, fun Z r z j j' k k' hj hj' hk hk' => ?_, hw⟩
  rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', gm_pull_g LP θ r z k k' hk hk',
    hψ Z (r ≫ θ) z j j' (k PUnit.unit) (k' PUnit.unit) hj hj' ((mem_pull (F := θ)).1 hk) ((mem_pull (F := θ)).1 hk'), Category.assoc]

theorem isoAsPullId {X : Scheme.{0}} {LL LM : LB X} (e : LB.Iso LM LL) (he : e.IsGen) :
    ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), PGen eP ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) := by
  have hle : ∀ (J : PUnit → LL.ι) (j : LM.ι), (LL.pull (𝟙 X)).U J ⊓ LM.U j ≤ LL.U (J PUnit.unit) ⊓ LM.U j :=
    fun J j x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  obtain ⟨eP, hP⟩ : ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) :=
    ⟨⟨fun p => res (hle p.1 p.2) (e.s (p.1 PUnit.unit, p.2))⟩, fun Y f y i j hi hj =>
      gm_res f y (hle (fun _ => i) j) ⟨mem_pull.2 hi, hj⟩ _⟩
  refine ⟨eP, fun Y f y j j' k k' hj hj' hk hk' => ?_, hP⟩
  have hm : f y ∈ LL.U j ⊓ LM.U k ⊓ (LL.U j' ⊓ LM.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have hm' : f y ∈ (LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k') := hm
  have h1 := congrArg (gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k'))) (he (j, k) (j', k'))
  have hd : gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k')) ((LB.div LL LM).g (j, k) (j', k')) =
      gm f y (LL.U j ⊓ LL.U j') (LL.g j j') * (gm f y (LM.U k ⊓ LM.U k') (LM.g k k'))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ hm' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm' _))))
  rw [hP Y f y j k hj hk, hP Y f y j' k' hj' hk', Category.comp_id]
  exact (gm_res f y inf_le_left hm' _).symm.trans (h1.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) hd (gm_res f y inf_le_right hm' _))))

theorem isoCancelGerm : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL), ψ.IsGen → e.IsGen →
    ∃ w₀ : LB.Iso (LP.pull θ) (LM.pull fst), w₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k := by
  intro Y XA XG θ φ fst hfst LP LL LM hP hL hM ψ e hψ he
  obtain ⟨w'', hw'', hv''⟩ := pullIsoAlong θ φ (fst ≫ 𝟙 XG) (by rw [Category.comp_id, hfst]) ψ
    ((isGen_iff ψ).1 hψ)
  obtain ⟨eP, heP, hvP⟩ := isoAsPullId e he
  obtain ⟨w₀, T⟩ := exists_cancel hL eP w'' heP hw'' hM (pull_isLB hP θ)
  refine ⟨w₀, (isGen_iff w₀).2 (T.pgen_cancel hL heP hw''), fun Z r z i j k hi hj hk => ?_⟩
  have t := T Z r z i j (fun _ => k) hi hj (mem_pull.2 hk)
  rw [hv'' Z r z i (fun _ => k) hi (mem_pull.2 hk), hvP Z (r ≫ fst) z i j hi hj] at t
  rw [t, inv_mul_cancel_left]

end GlobalTheory.IsoComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGermsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_cancel_pulled_bundles_germs : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL), ψ.IsGen → e.IsGen →
    ∃ w₀ : LB.Iso (LP.pull θ) (LM.pull fst), w₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k := by
  first | exact @GlobalTheory.IsoComp.isoCancelGerm | exact GlobalTheory.IsoComp.isoCancelGerm | (intros; apply GlobalTheory.IsoComp.isoCancelGerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponent
set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore.NonzeroCusp

theorem laU_const {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : Unf Xo c σ r) (m n : ℕ) (k : V.Comp) :
    laU V (fun _ => m) n k = laU V 0 (n + 2 * m) k := by
  funext τ j
  have e : (n + 2 * m) / 2 = n / 2 + m := by omega
  simp only [laU, Pi.zero_apply, e]
  split_ifs <;> push_cast <;> ring

theorem exists_cuspOn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨n₀, hn₀, hev, f₀, hf₀, ⟨k, y⟩, hz, hne⟩ := GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component E H Dw l Xo c r U x hL _ hσ Z
  obtain ⟨hy, hlies⟩ := hz
  have hM : CuspMul Xo c U := cusp_mul_of_M5 siegelSpaceAlgebra_holds U
  have hD0 : ∀ m, Even m → Dom (0 : (E →+* ℂ) × ℕ → ℕ) m := fun m hm => ⟨fun _ => antitone_const, hm⟩
  have hpow : ∀ j : ℕ, f₀ ^ (j + 1) ∈ cusp Xo c U 0 ((j + 1) * n₀) := by
    intro j
    induction j with
    | zero => simpa using hf₀
    | succ j ih =>
      have h := hM 0 0 ((j + 1) * n₀) n₀ (f₀ ^ (j + 1)) f₀ (hD0 _ (hev.mul_left _)) (hD0 _ hev) ih hf₀
      have e1 : ((j + 1) * n₀ + n₀) = (j + 1 + 1) * n₀ := by ring
      rw [add_zero, e1] at h
      rw [pow_succ]
      exact h
  have hrd : ∀ j : ℕ, rdU (U c.F.val.toRingHom) (f₀ ^ (j + 1)) k y = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Formalism.L2.Pj.rdU_mul, Pi.mul_apply, Pi.mul_apply, ih]
      ring
  set M : ℕ := 4 * (finrank ℚ E * r) + 7 with hMdef
  obtain ⟨t, ht⟩ := hev
  have hMt : (M + 1) * n₀ = (M + 1) * t + (M + 1) * t := by rw [ht]; ring
  have ht1 : 1 ≤ t := by omega
  have hMt1 : M + 1 ≤ (M + 1) * t := Nat.le_mul_of_pos_right _ ht1
  set n : ℕ := (M + 1) * n₀ - 4 with hndef
  have hnev : Even n := ⟨(M + 1) * t - 2, by omega⟩
  have hnb : 4 * (finrank ℚ E * r) + 4 ≤ n := by omega
  have hn4 : n + 2 * 2 = (M + 1) * n₀ := by omega
  have hP : rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1)) ∈
      holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) (fun _ => 2) n) := by
    have e : laU (U c.F.val.toRingHom) (fun _ => 2) n = laU (U c.F.val.toRingHom) 0 ((M + 1) * n₀) :=
      funext fun k' => by rw [laU_const, hn4]
    rw [e]
    exact ⟨((mem_cusp Xo c U 0 _ _).1 (hpow M)).2 _ hσ, rdU_mem_offZero _ _⟩
  have hspan := hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hP
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U c.F.val.toRingHom) f k y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let ev : FDSec (U c.F.val.toRingHom).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U c.F.val.toRingHom) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    have h0 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = 0 := hle hspan
    have h1 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (M + 1) := hrd M
    exact pow_ne_zero _ hne (h1.symm.trans h0)
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  refine ⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, g, g.2, ?_⟩
  intro h0
  have e : rdU (U c.F.val.toRingHom) (g : Rul Xo c) k y = rdU (U c.F.val.toRingHom) f k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [h0, map_zero] at e
  exact hfy e.symm

end GlobalTheory.FlatCore.NonzeroCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponentStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  first | exact @GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | exact GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | (intros; apply GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestriction
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_bar (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R]
    {x : Sp R ⟶ Xo.XF c} {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} (h : ∃ j, FrU Xo c U τ j x v w) :
    ∃ vb wb, FrY Y (compactOf Y U) τ h.choose (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb :=
  (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R h.choose x).1 v w h.choose_spec

def restrictRule (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y) : RuleU Xo c :=
  fun R _ x v w =>
    haveI := Classical.propDecidable (∃ j, FrU Xo c U τ j x v w)
    if h : ∃ j, FrU Xo c U τ j x v w then
      σb R (x ≫ Y.jQ) (exists_bar Y U τ h).choose (exists_bar Y U τ h).choose_spec.choose
    else 0

theorem restrictRule_eq (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {σb : RuleY Y}
    (hσb : SecY Y (compactOf Y U) τ σb) {R : Type} [CommRing R] {j : c.F →+* R} {x : Sp R ⟶ Xo.XF c}
    {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin D.p → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} {wb : Fin D.q → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)}
    (h : FrU Xo c U τ j x v w) (hb : FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb) (hv : SameVecs Y x v vb)
    (hw : SameVecs Y x w wb) : restrictRule Y U τ σb R x v w = σb R (x ≫ Y.jQ) vb wb := by
  have hex : ∃ j, FrU Xo c U τ j x v w := ⟨j, h⟩
  obtain ⟨hb0, hv0, hw0⟩ := (exists_bar Y U τ hex).choose_spec.choose_spec
  have e : restrictRule Y U τ σb R x v w =
      σb R (x ≫ Y.jQ) (exists_bar Y U τ hex).choose (exists_bar Y U τ hex).choose_spec.choose := by
    unfold restrictRule
    rw [dite_eq_left hex]
  rw [e]
  have hx : x ≫ Y.jQ = spMap (RingHom.id R) ≫ (x ≫ Y.jQ) := by
    rw [DetExtendZero.spMap_id, Category.id_comp]
  have hx' : x = spMap (RingHom.id R) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
  have cv : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.p) (Fin D.p) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (vb k).left) ((exists_bar Y U τ hex).choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.p v vb v _ hx' hv hv0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.1.1 k).1) i
  have cw : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.q) (Fin D.q) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (wb k).left)
      ((exists_bar Y U τ hex).choose_spec.choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.q w wb w _ hx' hw hw0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have key := sec_chg hσb hb hb0 (g := RingHom.id R) (M := 1) (N := 1) ⟨hx, cv, cw⟩
  simpa using key.symm

theorem exists_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ σb hσb
  refine ⟨restrictRule Y U τ σb, isSection_of_chg ?_, ?_, ?_⟩
  · intro R R' _ _ g j j' x v w x' v' w' M N h h' hc
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    obtain ⟨vb', wb', hb', hv', hw'⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R' j' x').1 v' w' h'
    rw [restrictRule_eq Y U τ hσb h hb hv hw, restrictRule_eq Y U τ hσb h' hb' hv' hw']
    refine sec_chg hσb hb hb' ⟨by rw [hc.1, Category.assoc], fun i => ?_, fun i => ?_⟩
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.p v vb v' vb' hc.1 hv hv'
        _ i).mp (hc.2.1 i)
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.q w wb w' wb' hc.1 hw hw'
        _ i).mp (hc.2.2 i)
  · intro R _ j x v w vb wb h hb hv hw
    exact (restrictRule_eq Y U τ hσb h hb hv hw).symm
  · intro hnz R _ j x v w h
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    rw [restrictRule_eq Y U τ hσb h hb hv hw]
    exact hnz R j _ vb wb hb

end GlobalTheory.DetLine.Restrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestrictionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_determinantLine_section_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  first | exact @GlobalTheory.DetLine.Restrict.exists_restriction | exact GlobalTheory.DetLine.Restrict.exists_restriction | (intros; apply GlobalTheory.DetLine.Restrict.exists_restriction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.normW_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  intro V _ _ G _ _ A _ _ θ _ φ hφ he LP LL LM hP hL hM rA rL rM ψ e w₀ hpt hψ hε z JA JG gA gG
  have h1 : eSec ((Over.pullback (jK V)).obj G) ≫ θ.left = eSec A := by
    show η[(Over.pullback (jK V)).obj G].left ≫ θ.left = η[A].left
    rw [← Over.comp_left, IsMonHom.one_hom]
  have h2 : eSec ((Over.pullback (jK V)).obj G) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
    rw [← hφ, ← Category.assoc, h1, he]
  have p1 : θ.left (eSec ((Over.pullback (jK V)).obj G) z) = eSec A z := congrArg (fun f => f z) h1
  have p2 : pullback.fst G.hom (jK V) (eSec ((Over.pullback (jK V)).obj G) z) = eSec G (jK V z) :=
    congrArg (fun f => f z) h2
  have p3 : φ (eSec A z) = eSec G (jK V z) := congrArg (fun f => f z) he
  have hA : eSec A z ∈ LP.U (JA (eSec A)) := gA (eSec A)
  have hG : eSec G (jK V z) ∈ LM.U (JG (jK V ≫ eSec G)) := gG (jK V ≫ eSec G)
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (jK V z))

  have s2 := hpt _ (eSec ((Over.pullback (jK V)).obj G)) z i (JG (jK V ≫ eSec G)) (JA (eSec A))
    (by rw [p2]; exact hi) (by rw [p2]; exact hG) (by rw [p1]; exact hA)
  rw [h2, h1] at s2

  have s3 := (maps_iff ψ (fun _ : PUnit => eSec A) (fun _ => eSec G) (fun _ => 1) rA rL
    (spMap (algebraMap V (FractionRing V))) _ (rigPull_le φ _ he LL) (fun _ => rfl)).1 hψ
    _ (𝟙 _) z (fun _ => i) (fun _ => JA (eSec A))
    (fun _ => by show φ (eSec A z) ∈ _; rw [p3]; exact hi) (fun _ => hA)
  simp only [Category.id_comp, Fintype.prod_unique, zpow_one] at s3

  have hm : jK V z ∈ (LB.wchart LL (fun _ : PUnit => eSec G) (fun _ => i) ⊓
      LB.wchart LM (fun _ : PUnit => eSec G) (fun _ => JG (jK V ≫ eSec G)) : (Sp V).Opens) := by
    exact ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hG⟩
  have s4 := congrArg (gm (jK V) z _) (hε (fun _ => i, fun _ => JG (jK V ≫ eSec G)))
  have eU : gm (jK V) z _ ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s
      (fun _ => i, fun _ => JG (jK V ≫ eSec G))) =
      gm (jK V ≫ eSec G) z (LL.U i ⊓ LM.U (JG (jK V ≫ eSec G))) (e.s (i, JG (jK V ≫ eSec G))) := by
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (e.s (i, JG (jK V ≫ eSec G))))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hm _).trans (gm_pull _ _ z _ (show eSec G (jK V z) ∈ LL.U i ⊓ LM.U (JG (jK V ≫ eSec G)) from ⟨hi, hG⟩) _)
  have s4' := (gm_res _ z _ hm _).symm.trans (s4.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) eU (gm_res _ z _ hm _))))
  rw [val_of rA (𝟙 _) z JA (fun _ => JA (eSec A)) (fun _ => by rw [Category.id_comp]),
    val_of rM (jK V) z JG (fun _ => JG (jK V ≫ eSec G)) (fun _ => rfl), s2, _root_.mul_assoc, ← s3]
  exact inv_mul_eq_of_eq_mul s4'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_preserves_rigidification_at_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  first | exact @GlobalTheory.normW_origin | exact GlobalTheory.normW_origin | (intros; apply GlobalTheory.normW_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GlueRat

variable {S : Scheme.{0}} [IsIntegral S]

theorem genericPoint_mem' {U : S.Opens} {x : S} (hx : x ∈ U) : genericPoint S ∈ U :=
  ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

theorem unit_eq_of_germ {V : S.Opens} {a b : Γ(S, V)ˣ}
    (h : ∀ hg : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) hg (a : Γ(S, V)) =
      S.presheaf.germ V (genericPoint S) hg (b : Γ(S, V))) : a = b := by
  by_cases hg : genericPoint S ∈ V
  · exact Units.ext (germ_injective_of_isIntegral S (genericPoint S) hg (h hg))
  · exact unit_ext fun x hx => (hg (genericPoint_mem' hx)).elim

theorem germ_res_unit {U V : S.Opens} (hle : V ≤ U) (hg : genericPoint S ∈ V) (a : Γ(S, U)ˣ) :
    S.presheaf.germ V (genericPoint S) hg ((res hle a : Γ(S, V)ˣ) : Γ(S, V)) =
      S.presheaf.germ U (genericPoint S) (hle hg) (a : Γ(S, U)) :=
  S.presheaf.germ_res_apply (homOfLE hle) _ hg _

theorem exists_unit_of_local {W : S.Opens} (f : S.presheaf.stalk (genericPoint S))
    (H : ∀ x ∈ W, ∃ (V : S.Opens) (_ : V ≤ W) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f) :
    ∃ s : Γ(S, W)ˣ, ∀ h : genericPoint S ∈ W, S.presheaf.germ W (genericPoint S) h (s : Γ(S, W)) = f := by
  choose V hVW hxV u hu using fun x : W => H x.1 x.2
  obtain ⟨s, hs⟩ := glue_unit W V hVW (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩) u
    (fun i j z hz => by
      rw [← gm_res (𝟙 S) z (inf_le_left : V i ⊓ V j ≤ V i) hz,
        ← gm_res (𝟙 S) z (inf_le_right : V i ⊓ V j ≤ V j) hz]
      congr 1
      refine unit_eq_of_germ fun hg => ?_
      rw [germ_res_unit, germ_res_unit, hu i (hg.1), hu j hg.2])
  refine ⟨s, fun h => ?_⟩
  rw [← germ_res_unit (hVW ⟨_, h⟩) (hxV ⟨_, h⟩), hs]
  exact hu _ _

end GlobalTheory.GlueRat


open GlobalTheory.GlueRat in
theorem GlobalTheory.GlueRat.lbIso_of_rat : ∀ (S : Scheme.{0}) [IsIntegral S] (A B : LB S) (f : B.ι × A.ι → S.presheaf.stalk (genericPoint S)),
    (∀ p, ∀ x ∈ B.U p.1 ⊓ A.U p.2, ∃ (V : S.Opens) (_ : V ≤ B.U p.1 ⊓ A.U p.2) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f p) →
    (∀ p q (h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1) (h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2),
      f p * S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) =
        S.presheaf.germ _ (genericPoint S) h1 (B.g p.1 q.1 : Γ(S, B.U p.1 ⊓ B.U q.1)) * f q) →
    LBIso A B := by
  intro S _ A B f H1 H2
  choose s hs using fun p => exists_unit_of_local (f p) (H1 p)
  refine ⟨⟨s⟩, fun p q => unit_eq_of_germ fun hg => ?_⟩
  have hp : genericPoint S ∈ B.U p.1 ⊓ A.U p.2 := hg.1
  have hq : genericPoint S ∈ B.U q.1 ⊓ A.U q.2 := hg.2
  have h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1 := ⟨hg.1.1, hg.2.1⟩
  have h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2 := ⟨hg.1.2, hg.2.2⟩
  refine ((germ_res_unit _ hg _).trans (hs p hp)).trans ?_
  set O := (LB.div B A).U p ⊓ (LB.div B A).U q
  have lB : O ≤ B.U p.1 ⊓ B.U q.1 := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have lA : O ≤ A.U p.2 ⊓ A.U q.2 := le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have lq : O ≤ B.U q.1 ⊓ A.U q.2 := inf_le_right
  change f p = S.presheaf.germ O (genericPoint S) hg
    (((res lB (B.g p.1 q.1) * (res lA (A.g p.2 q.2))⁻¹ * res lq (s q) : Γ(S, O)ˣ)) : Γ(S, O))
  have e : S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) = 1 := by
    rw [← germ_res_unit lA hg, ← map_mul, Units.inv_mul, map_one]
  have H := H2 p q h1 h2
  simp only [Units.val_mul, map_mul, germ_res_unit, hs q hq]
  calc f p = f p * (S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2))) := by rw [e, _root_.mul_one]
    _ = _ := by rw [mul_comm (S.presheaf.germ O _ hg _), ← _root_.mul_assoc, H]; ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_compatible_rational_local_units : ∀ (S : Scheme.{0}) [IsIntegral S] (A B : LB S) (f : B.ι × A.ι → S.presheaf.stalk (genericPoint S)),
    (∀ p, ∀ x ∈ B.U p.1 ⊓ A.U p.2, ∃ (V : S.Opens) (_ : V ≤ B.U p.1 ⊓ A.U p.2) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f p) →
    (∀ p q (h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1) (h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2),
      f p * S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) =
        S.presheaf.germ _ (genericPoint S) h1 (B.g p.1 q.1 : Γ(S, B.U p.1 ⊓ B.U q.1)) * f q) →
    LBIso A B := by
  first | exact @GlobalTheory.GlueRat.lbIso_of_rat | exact GlobalTheory.GlueRat.lbIso_of_rat | (intros; apply GlobalTheory.GlueRat.lbIso_of_rat <;> assumption)
end
end
