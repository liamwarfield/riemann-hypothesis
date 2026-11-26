module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnBasicOpenOfComesFromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfBasicOpenTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_of_basicOpen_top {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

abbrev fnSp (A : Type) [CommRing A] : A →+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_comp_spMap {R₀ A : Type} [CommRing R₀] [CommRing A] (α : R₀ →+* A) {Z : Scheme.{0}}
    (s : Z ⟶ Sp A) (r : R₀) : (s ≫ spMap α).appTop.hom (fnSp R₀ r) = s.appTop.hom (fnSp A (α r)) := by
  have nat := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.appTop.hom nat.symm

def fnOn {R₀ : Type} [CommRing R₀] (W : (Sp R₀).Opens) : R₀ →+* Γ(W.toScheme, ⊤) :=
  W.ι.appTop.hom.comp (fnSp R₀)

theorem appTop_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) :
    t.appTop.hom (fnOn W r) = s.appTop.hom (fnSp A (α r)) := by
  have e : t.appTop.hom (fnOn W r) = (t ≫ W.ι).appTop.hom (fnSp R₀ r) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [e, h, appTop_comp_spMap]

theorem gm_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) (u : Γ(W.toScheme, ⊤)ˣ) (v : Aˣ)
    (hu : (u : Γ(W.toScheme, ⊤)) = fnOn W r) (hv : (v : A) = α r) (z : Z) :
    gm t z ⊤ u = gm s z ⊤ (unitOn v) := by
  rw [GlobalTheory.UU.gm_top t, GlobalTheory.UU.gm_top s]
  congr 1
  apply Units.ext
  show t.appTop.hom (u : Γ(W.toScheme, ⊤)) = s.appTop.hom (fnSp A (v : A))
  rw [hu, hv, appTop_fnOn W α t s h r]

theorem isUnit_fnOn {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) :
    IsUnit (fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) r) := by
  set W := (Sp R₀).basicOpen (fnSp R₀ f)
  have hf : IsUnit (fnOn W f) := isUnit_of_basicOpen_top _ (by
    have e := Scheme.preimage_basicOpen W.ι (fnSp R₀ f)
    rw [Scheme.Opens.ι_preimage_self] at e
    exact e.symm)
  exact isUnit_of_dvd_unit (map_dvd (fnOn W) hr |>.trans (by rw [map_pow])) (hf.pow N)

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ) (r : D₁.X → R₀)
    (hu : ∀ y, (u y : Γ(W'.toScheme, ⊤)) = fnOn W' (r y)) (hr : ∀ y, algebraMap R₀ (FractionRing R₀) (r y) = κ₀ y) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine gm_fnOn W' (algebraMap R₀ (FractionRing R₀)) _ _ ?_ (r y) _ _ (hu y) (hr y).symm z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.RescaleLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_isPullDeg_comp_of_preimage {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hW : specOf i ⁻¹ᵁ p.W = ⊤) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ', hv⟩ := PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''
      have ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J' :=
        ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂
      rw [ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_isPullDeg_comp_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  intro R R' R'' _ _ _ _ _ _ i j D D' D'' p q e
  exact exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)

end GlobalTheory.PullDegCompTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_comp_of_first_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  first | exact @GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top | exact GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top | (intros; apply GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegWhole

theorem exists_isPullDeg_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  intro R R' _ _ _ _ i D D' p ⟨ψ⟩
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme,
      g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩
  obtain ⟨b, hb, hc⟩ := p.psi_pr x
  refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans (by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _
      (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ)⟩

end GlobalTheory.PullDegWhole
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_whole_spectrum : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  first | exact @GlobalTheory.PullDegWhole.exists_isPullDeg_top | exact GlobalTheory.PullDegWhole.exists_isPullDeg_top | (intros; apply GlobalTheory.PullDegWhole.exists_isPullDeg_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSides
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSides
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleBoth

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_of_le {R : Type} [CommRing R] {W : (Sp R).Opens} (r : R) (h : W ≤ (Sp R).basicOpen (fnSp R r)) :
    IsUnit (fnOn W r) := isUnit_of_basicOpen_top _ (by
  have e := Scheme.preimage_basicOpen W.ι (fnSp R r)
  refine Eq.trans e.symm (top_le_iff.1 fun x _ => h x.2))

theorem mem_basicOpen_of_ne {R F : Type} [CommRing R] [Field F] (α : R →+* F) {r : R} (h : α r ≠ 0) {Z : Scheme.{0}}
    (s : Z ⟶ Sp F) (z : Z) : (s ≫ spMap α) z ∈ (Sp R).basicOpen (fnSp R r) := by
  have hpre : (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    refine (congrArg IsUnit (appTop_comp_spMap α s r)).mpr ?_
    exact ((IsUnit.mk0 _ h).map (fnSp _)).map s.appTop.hom
  exact (show z ∈ (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) from hpre.ge trivial)

theorem val_psiOn_rescale {R F : Type} [CommRing R] [IsDomain R] [Field F] (Q : DegPre R) (g : Q.X → (FractionRing R)ˣ)
    {W W₀ : (Sp R).Opens} (ψ : PsiOn Q W) (ψ₀ : PsiOn (GlobalTheory.PolDeg.rescale Q g) W₀) (y : Q.X) (a b : R)
    (hab : (g y : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a)
    (α : R →+* F) (hb : α b ≠ 0) (v : Fˣ) (hv : (v : F) * α b = α a) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme)
    (r₀ : Z ⟶ W₀.toScheme) (s : Z ⟶ Sp F) (hr : r ≫ W.ι = s ≫ spMap α) (hr₀ : r₀ ≫ W₀.ι = s ≫ spMap α)
    (z : Z) (J) (hJ : Good Q.P.L z J) :
    val (ψ₀.psi y) r₀ z J = gm s z ⊤ (unitOn v) * val (ψ.psi y) r z J := by
  have ha : α a ≠ 0 := hv ▸ mul_ne_zero v.ne_zero hb
  have ha' : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => ha (by rw [h, map_zero])
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => hb (by rw [h, map_zero])
  obtain ⟨W', l, l₀, la, lb, hm⟩ : ∃ W' : (Sp R).Opens, W' ≤ W ∧ W' ≤ W₀ ∧ W' ≤ (Sp R).basicOpen (fnSp R a) ∧
      W' ≤ (Sp R).basicOpen (fnSp R b) ∧ ∀ x, (s ≫ spMap α) x ∈ W' :=
    ⟨(W ⊓ W₀) ⊓ ((Sp R).basicOpen (fnSp R a) ⊓ (Sp R).basicOpen (fnSp R b)), inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right, fun x =>
      ⟨⟨(congrArg (fun q => q x ∈ W) hr).mp (r x).2, (congrArg (fun q => q x ∈ W₀) hr₀).mp (r₀ x).2⟩,
        mem_basicOpen_of_ne α ha s x, mem_basicOpen_of_ne α hb s x⟩⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Z ⟶ W'.toScheme, ρ ≫ W'.ι = s ≫ spMap α :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hm x), IsOpenImmersion.lift_fac _ _ _⟩
  let m : W'.toScheme ⟶ W.toScheme := (Sp R).homOfLE l
  let m₀ : W'.toScheme ⟶ W₀.toScheme := (Sp R).homOfLE l₀
  have f : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have f₀ : m₀ ≫ W₀.ι = W'.ι := Scheme.homOfLE_ι _ _
  have ua := isUnit_fnOn_of_le a la
  have ub := isUnit_fnOn_of_le b lb
  have hφ : m ≫ (toUnit (TW W) ≫ Q.c y).left = m₀ ≫ (toUnit (TW W₀) ≫ Q.c y).left := by
    show m ≫ W.ι ≫ (Q.c y).left = m₀ ≫ W₀.ι ≫ (Q.c y).left
    rw [← Category.assoc, f, ← Category.assoc, f₀]
  have key := GlobalTheory.PsiEvenPull.val_eq_of_app_injective Q.P.isLB
    (u := GlobalTheory.UU.scaleGen ub.unit (LB.pullGen Q.P.L _ _ (ψ₀.psi y) m₀))
    (u' := GlobalTheory.UU.scaleGen ua.unit (LB.pullGen Q.P.L _ _ (ψ.psi y) m))
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) hφ)
    (jK R ∣_ W') (GlobalTheory.PsiEvenPull.app_injective_generic W')
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ₀.psi_gen y) m₀))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m)) (fun x I hI => by
      have e : (jK R ∣_ W') ≫ W'.ι = (jK R ⁻¹ᵁ W').ι ≫ jK R := morphismRestrict_ι _ _
      have p := GlobalTheory.ArcSpecialise.psiOn_generic ψ y ((jK R ∣_ W') ≫ m) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f, e]) hI
      have p₀ := GlobalTheory.ArcSpecialise.psiOn_generic ψ₀ y ((jK R ∣_ W') ≫ m₀) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f₀, e]) hI
      have q : val ((GlobalTheory.PolDeg.rescale Q g).psi y) (jK R ⁻¹ᵁ W').ι x I =
          gm (jK R ⁻¹ᵁ W').ι x ⊤ (unitOn (g y)) * val (Q.psi y) (jK R ⁻¹ᵁ W').ι x I :=
        GlobalTheory.UU.val_scaleGen (unitOn (g y)) (Q.psi y) _ hI
      have ga := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e a ua.unit (Units.mk0 _ ha') ua.unit_spec rfl x
      have gb := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e b ub.unit (Units.mk0 _ hb') ub.unit_spec rfl x
      have w : unitOn (Units.mk0 _ ha') = unitOn (Units.mk0 _ hb') * unitOn (g y) :=
        (congrArg unitOn (Units.ext (hab.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hI).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hI).symm)
      refine (congrArg₂ (· * ·) gb ((val_pull hI _ _ _).trans (p₀.trans q))).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) ga ((val_pull hI _ _ _).trans p)).symm)
      rw [w, map_mul, _root_.mul_assoc]) Z ρ z J hJ
  have ga := gm_fnOn W' α _ _ hρ a ua.unit (Units.mk0 _ ha) ua.unit_spec rfl z
  have gb := gm_fnOn W' α _ _ hρ b ub.unit (Units.mk0 _ hb) ub.unit_spec rfl z
  have w : unitOn (Units.mk0 _ ha) = unitOn (Units.mk0 _ hb) * unitOn v :=
    (congrArg unitOn (Units.ext (hv.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
  have c : ρ ≫ m = r := by rw [← cancel_mono W.ι, Category.assoc, f, hρ, hr]
  have c₀ : ρ ≫ m₀ = r₀ := by rw [← cancel_mono W₀.ι, Category.assoc, f₀, hρ, hr₀]
  have k₂ := (congrArg₂ (· * ·) gb (val_pull hJ _ _ _)).symm.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm.trans
    (key.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) ga (val_pull hJ _ _ _)))))
  rw [w, map_mul, _root_.mul_assoc, c, c₀] at k₂
  exact mul_left_cancel k₂

theorem exists_isPullDeg_rescale : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  intro R V _ _ _ _ θ Q Q' h g g' ⟨ψ₀⟩ H
  have hsq : jK V ≫ specOf θ = 𝟙 (TK V).left ≫ spMap ((algebraMap V (FractionRing V)).comp θ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  obtain ⟨t, ht⟩ : ∃ t : (TK V).left ⟶ (TW (⊤ : (Sp R).Opens)).left, t ≫ (⊤ : (Sp R).Opens).ι = jK V ≫ specOf θ :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp R).Opens).ι (jK V ≫ specOf θ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have gp : IsGrpPullback Q'.P.A Q.P.A (spMap θ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec Q'.P.A) (fun _ => eSec Q.P.A) (fun _ => 1) Q'.rig Q.rig (spMap θ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : Q'.X, (Q'.c x).left ≫ proj h = spMap θ ≫ (Q.c (h.xe x)).left := h.c_pr
  have hv : ∀ (x : Q'.X) (z : (TK V).left) J J', Good Q.P.L z J → Good Q'.P.L z J' →
      val (ψ₀.psi (h.xe x)) t z J =
        (om h.w z J J' (Q'.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    obtain ⟨a, b, hb, hab, hab'⟩ := H x
    have e0 := val_psiOn_rescale Q g h.psiW ψ₀ (h.xe x) a b hab ((algebraMap V (FractionRing V)).comp θ)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hb) (g' x) hab' h.g t (𝟙 _)
      (h.g_comm.trans hsq) (ht.trans hsq) z J hJ
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn (g' x)) * val (Q'.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (g' x)) (Q'.psi x) (𝟙 _) hJ'
    refine e0.trans ?_
    rw [e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  obtain ⟨hD, h₁, h₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale Q g)
    (GlobalTheory.PolDeg.rescale Q' g') ψ₀ t ht gp h.w ((isGen_iff h.w).1 h.w_gen) hr h.xe hc hv
  exact ⟨hD, h₁, h₂⟩

end GlobalTheory.RescaleBoth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSidesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_rescale_both_sides : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  first | exact @GlobalTheory.RescaleBoth.exists_isPullDeg_rescale | exact GlobalTheory.RescaleBoth.exists_isPullDeg_rescale | (intros; apply GlobalTheory.RescaleBoth.exists_isPullDeg_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverPullbackMapLeftCompPullbackFstScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum

theorem over_pullback_map_left_comp_pullbackFst_scheme {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivFromPull

theorem divFrom_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  intro E _ _ _ H D' l c L R V _ _ _ _ Q _ oQ Q' _ oQ' iw θ I _ s ε e hD e' he' hact hs hdiv
  obtain ⟨g, hD0, hg, hxe, hac⟩ := hdiv
  have ψL : Nonempty (PsiOn (mulDeg L.D l.M') ⊤) := GlobalTheory.ArcPull.nonempty_psiOn_top _ (fun y => L.gen (l.M' • y))
  obtain ⟨hD1, hW1, hp1, hx1⟩ := GlobalTheory.T.exists_isPullDeg_whole_spectrum hD0 ψL
  have ψR : Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) := by
    have := GlobalTheory.PullDegUniq.nonempty_psiOn_pull hD1
    rw [hW1] at this
    simpa using this

  let n : Q'.X → I → ℤ := fun y k => (l.M' : ℤ) * ε k (e' y) (H.w0 • e' y)
  have hs0 : ∀ k, algebraMap V (FractionRing V) (θ (s k)) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
  have hr0 : ∀ k, algebraMap R (FractionRing R) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (fun h => hs k (by rw [h, map_zero]))
  let g' : Q'.X → (FractionRing V)ˣ := fun y =>
    (Units.mk0 (∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ n y k)
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs0 k)))⁻¹
  have hab : ∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧
      (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a) := by
    intro y
    have key : ∀ {K : Type} [Field K] (x : K), x ≠ 0 → ∀ m : ℤ, x ^ (-m) * x ^ m.toNat = x ^ (-m).toNat := by
      intro K _ x hx m
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
      congr 1
      omega
    have hgz : (g (hD.xe y) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s k) ^ (-n y k) := by
      have h := hg (hD.xe y)
      rw [Units.val_inv_eq_inv_val] at h
      rw [← inv_inv (g (hD.xe y) : FractionRing R), h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg]
      simp only [n, he' y]
    have hg'y : (g' y : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ (-n y k) := by
      simp only [g', Units.val_inv_eq_inv_val, Units.val_mk0, ← Finset.prod_inv_distrib, zpow_neg]
    refine ⟨∏ k, s k ^ (-n y k).toNat, ∏ k, s k ^ (n y k).toNat, ?_, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [map_pow]; exact pow_ne_zero _ (hs k)
    · rw [hgz, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow]
      exact key _ (hr0 k) _
    · rw [hg'y, map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow, map_pow, map_pow]
      exact key _ (hs0 k) _
  obtain ⟨h1, hp2, hx2⟩ := GlobalTheory.T.exists_isPullDeg_rescale_both_sides hD g g' ψR hab
  obtain ⟨r, hpr, hxr⟩ := GlobalTheory.T.exists_isPullDeg_comp_of_first_top hD1 h1 hW1
  refine ⟨g', r, fun y => ?_, fun y => ?_, fun x => ?_⟩
  · simp only [g', Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0, map_zpow]
    rfl
  · exact (hxr y).trans ((hx1 _).trans ((congrArg hD0.xe (hx2 y)).trans ((hxe _).trans (he' y).symm)))
  · letI := H.starRing
    have c₁ : (oQ'.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) =
        hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ≫ (oQ.onB.act x).left := by
      have := congrArg (fun m => m.left ≫ pullback.fst Q.P.A.hom (specOf θ)) (hact x)
      simpa only [Over.comp_left, Category.assoc, GlobalTheory.Mum.over_pullback_map_left_comp_pullbackFst_scheme] using this
    have hpr' : r.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf (θ.comp iw)) =
        (hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
      hpr.trans (by rw [hp1]; exact congrArg (· ≫ _) hp2)
    have key : (oQ'.onB.act x).left ≫ ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫
        pullback.fst L.D.P.A.hom (specOf iw)) = ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫
        hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left := by
      simp only [Category.assoc] at c₁ hac ⊢
      rw [reassoc_of% c₁]
      exact congrArg _ (congrArg _ ((hac x).trans (Category.assoc _ _ _).symm))
    exact (congrArg _ hpr').trans (key.trans (congrArg (· ≫ _) hpr'.symm))

end GlobalTheory.UCanon.DivFromPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromBase_stable_under_pullback_of_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  first | exact @GlobalTheory.UCanon.DivFromPull.divFrom_pull | exact GlobalTheory.UCanon.DivFromPull.divFrom_pull | (intros; apply GlobalTheory.UCanon.DivFromPull.divFrom_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOnRescale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegResc

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_le {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) {W : (Sp R₀).Opens}
    (hle : W ≤ (Sp R₀).basicOpen (fnSp R₀ f)) : IsUnit (fnOn W r) := by
  have e := appTop_fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) (RingHom.id R₀) ((Sp R₀).homOfLE hle) W.ι (by
    rw [Scheme.homOfLE_ι]
    exact (Category.comp_id _).symm.trans (congrArg (W.ι ≫ ·) (Spec.map_id _).symm)) r
  have := (isUnit_fnOn f r N hr).map ((Sp R₀).homOfLE hle).appTop.hom
  rw [e] at this
  exact this

theorem gm_mono {R₀ K : Type} [CommRing R₀] [Field K] (W : (Sp R₀).Opens) (α : R₀ →+* K) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp K) (h : t ≫ W.ι = s ≫ spMap α) {I : Type} [Fintype I] (a : I → R₀)
    (ha : ∀ k, IsUnit (fnOn W (a k))) (h0 : ∀ k, α (a k) ≠ 0) (n : I → ℤ) (v : Kˣ)
    (hv : (v : K) = ∏ k, α (a k) ^ n k) (z : Z) :
    gm t z ⊤ (∏ k, (ha k).unit ^ n k) = gm s z ⊤ (unitOn v) := by
  obtain rfl : v = ∏ k, Units.mk0 (α (a k)) (h0 k) ^ n k := Units.ext (by
    rw [hv]; simp)
  show _ = GlobalTheory.TauTwist.unitAt s z _
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  exact congrArg (· ^ n k) (gm_fnOn W α t s h (a k) _ _ (ha k).unit_spec rfl z)

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ)
    (hu : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (s : Z ⟶ (TK R₀).left), t ≫ W'.ι = s ≫ jK R₀ → ∀ z,
      gm t z ⊤ (u y) = gm s z ⊤ (unitOn (κ₀ y))) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine hu y _ _ ?_ z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

theorem exists_rescale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀) (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  classical
  have hf : φ (∏ k, s k) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hs k
  set f := ∏ k, s k with hfd
  set W' : (Sp R₀).Opens := h.W ⊓ (Sp R₀).basicOpen (fnSp R₀ f) with hW'
  have hsq : jK R ≫ specOf φ = 𝟙 (TK R).left ≫ spMap ((algebraMap R (FractionRing R)).comp φ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R (FractionRing R)))).symm
  have hpre : (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    rw [hsq]
    refine (congrArg IsUnit (appTop_comp_spMap ((algebraMap R (FractionRing R)).comp φ) (𝟙 _) f)).mpr ?_
    exact ((IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)).map (fnSp _)).map
      (Scheme.Hom.appTop (𝟙 (Sp (FractionRing R)))).hom
  obtain ⟨g, hg⟩ : ∃ g : (TK R).left ⟶ (TW W').left, g ≫ W'.ι = jK R ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W'.ι (jK R ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, (show y ∈ (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) from hpre.ge trivial)⟩
      rw [← h.g_comm]
      exact (h.g y).2), IsOpenImmersion.lift_fac _ _ _⟩
  have hle : W' ≤ h.W := inf_le_left
  have hU : ∀ k, IsUnit (fnOn W' (s k)) := fun k =>
    isUnit_fnOn_le f _ 1 (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) inf_le_right
  have s0 : ∀ k, algebraMap R₀ (FractionRing R₀) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R₀ _)).2 fun e => hs k (by rw [e, map_zero])
  obtain ⟨ψW, hψW⟩ := exists_psiOn_rescale D₁ κ₀ h.psiW hle (fun y => ∏ k, (hU k).unit ^ n y k)
    (fun y Z t r e z => gm_mono W' (algebraMap R₀ (FractionRing R₀)) t r e s hU s0 (n y) _ (h₀ y) z)
  have hgm : g ≫ (Sp R₀).homOfLE hle = h.g := by
    rw [← cancel_mono h.W.ι, Category.assoc, Scheme.homOfLE_ι, hg, h.g_comm]
  have hv : ∀ (x : D.X) (z : (TK R).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' :=
    fun x z J J' hJ hJ' => by
    rw [hψW _ g z J hJ, hgm]
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' =
        gm (𝟙 (TK R).left) z ⊤ (unitOn (κ x)) * val (D.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (κ x)) (D.psi x) (𝟙 _) hJ'
    have e3 := gm_mono W' ((algebraMap R (FractionRing R)).comp φ) g (𝟙 _) (by rw [hg, hsq]) s hU
      (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs k)) (n (h.xe x)) (κ x) (h₁ x) z
    rw [e3, e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap φ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap φ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : D.X, (D.c x).left ≫ proj h = spMap φ ≫ (D₁.c (h.xe x)).left := h.c_pr
  have hw : PGen h.w := (isGen_iff h.w).1 h.w_gen
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale D₁ κ₀)
    (GlobalTheory.PolDeg.rescale D κ) ψW g hg gp h.w hw hr h.xe hc hv
  exact ⟨hD, k₁, k₂⟩

theorem rescale_inv {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (x : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi x = D.psi x :=
  GlobalTheory.TorusExt.gen_ext_val D.P.isLB ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi_gen x)
    (D.psi_gen x) fun y J hJ => by
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (GlobalTheory.UU.val_scaleGen _ _ _ hJ)).trans ?_)
      show GlobalTheory.TauTwist.unitAt _ y (g x)⁻¹ * (GlobalTheory.TauTwist.unitAt _ y (g x) * _) = _
      rw [map_inv, inv_mul_cancel_left]

theorem exists_withPsi {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (ψ₁ : GlobalTheory.TauTwist.PsiFam D₁) (g₁ : ∀ χ, (ψ₁ χ).IsGen)
    (ψ : GlobalTheory.TauTwist.PsiFam D) (g : ∀ χ, (ψ χ).IsGen) (e₁ : D₁.psi = ψ₁) (e : D.psi = ψ) :
    ∃ h' : IsPullDeg φ (GlobalTheory.TauTwist.withPsi D₁ ψ₁ g₁) (GlobalTheory.TauTwist.withPsi D ψ g),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  subst e₁ e
  exact ⟨h, rfl, fun _ => rfl⟩

theorem exists_unscale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ)
    (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀)
    (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) =
      ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ D₁ D, proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  obtain ⟨h₂, a₁, a₂⟩ := exists_rescale h (fun y => (κ₀ y)⁻¹) (fun y => (κ y)⁻¹) s hs n h₀ h₁
  obtain ⟨h₃, b₁, b₂⟩ := exists_withPsi h₂ D₁.psi D₁.psi_gen D.psi D.psi_gen (funext (rescale_inv D₁ κ₀))
    (funext (rescale_inv D κ))
  exact ⟨h₃, b₁.trans a₁, fun x => (b₂ x).trans (a₂ x)⟩

theorem exists_rescale_inv {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ) :
    ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x :=
  exists_withPsi h D₁.psi D₁.psi_gen _ ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹).psi_gen) rfl
    (funext (rescale_inv D κ)).symm

theorem main : (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ D₁ D, h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ), ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) :=
  ⟨fun h κ₀ κ _ _ s hs n h₀ h₁ => exists_rescale h κ₀ κ s hs n h₀ h₁,
    fun κ₀ κ h _ _ s hs n h₀ h₁ => exists_unscale κ₀ κ h s hs n h₀ h₁, fun h κ => exists_rescale_inv h κ⟩

end GlobalTheory.PullDegResc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivIso

theorem exists_isPullDeg_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  intro E _ _ _ H D' l c L V _ _ _ Q _ oQ Q' _ oQ' iw I _ s ε e e' hs ⟨g, p, hg, hx, ha⟩ ⟨g', p', hg', hx', ha'⟩
  letI := H.starRing
  obtain ⟨q, q₁, q₂⟩ := GlobalTheory.PullDegTop.main.2.2.2 (RingHom.id_comp iw) p p' (fun y => L.gen (l.M' • y))
  have he : ∀ y : Q'.X, e (q.xe y) = e' y := fun y => (hx _).symm.trans ((q₂ y).trans (hx' y))
  obtain ⟨r, r₁, r₂⟩ := GlobalTheory.PullDegResc.main.2.1 g g' q s hs (fun y k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y)) hg
    (fun x => (hg' x).trans (Finset.prod_congr rfl fun k _ => by rw [← he x]; rfl))
  refine ⟨r, fun y => (congrArg e (r₂ y)).trans (he y), fun x => (GlobalTheory.PullDegTop.main.2.1 r _ _).2 ?_⟩
  have r' : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫
      p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) = p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
    (congrArg (· ≫ _) r₁).trans q₁
  have pb : IsPullback (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) Q.P.A.hom L.D.P.A.hom (spMap iw) :=
    (pull_grp p).1
  have w : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫ Q.P.A.hom =
      Q'.P.A.hom ≫ spMap (RingHom.id V) := (pull_grp r).1.w
  have b : (oQ.onB.act x).left ≫ p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha x).trans (Category.assoc _ _ _).symm
  have b' : (oQ'.onB.act x).left ≫ p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha' x).trans (Category.assoc _ _ _).symm
  refine pb.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r').trans (b'.trans (Eq.symm ?_)))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) b).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r')))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (oQ'.onB.act x))).trans (Eq.symm ?_))))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (oQ.onB.act x))).trans w)

end GlobalTheory.UCanon.DivIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_id_same_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  first | exact @GlobalTheory.UCanon.DivIso.exists_isPullDeg_id | exact GlobalTheory.UCanon.DivIso.exists_isPullDeg_id | (intros; apply GlobalTheory.UCanon.DivIso.exists_isPullDeg_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinDataTriple


open GlobalTheory.LinearUnifIso in
theorem act_comm_noeth : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ _ I hI D D' A A' G G' _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory.LinDataTriple

theorem GlobalTheory.triple_iso_of_linear_data_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  intro E _ _ _ H V _ _ _ hB t t' P P' hD hx hB'
  letI := H.starRing
  have hR : AdmBase V (maximalIdeal V) := hB.1
  have := hR.1
  obtain ⟨ψ, bc, -, hψm, hbcm, hbc', hP, -⟩ := GlobalTheory.unif_determined_by_data_normal V hR P.D P.A t.G t.semi P.U
    P'.D P'.A t'.G t'.semi P'.U hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hBl : ∀ x, (P'.oD.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) =
      (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) ≫ (P.oD.onB.act x).left := by
    intro x
    have e := congrArg (fun c => c.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) (hB' x)
    simp only [Over.comp_left, Category.assoc] at e
    rw [e]
    exact congrArg (hD.e.hom.left ≫ ·) (pullback.lift_fst _ _ _)
  have hact := GlobalTheory.LinDataTriple.act_comm_noeth hL.globalFns V (maximalIdeal V) rfl P.D P'.D P.A P'.A t.G t'.G
    t'.semi P.U P'.U hD bc hbcm hP (𝓞 E) P.oD P'.oD P.oA P'.oA t.act.toRingAct t'.act.toRingAct P.lin P'.lin hx hBl
  have hact' : ∀ a, (t'.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t.act.act a).left := by
    intro a
    have e := congrArg (fun c => c.left ≫ pullback.fst t.G.hom (specOf (RingHom.id V))) (hact a)
    simp only [Over.comp_left, Category.assoc] at e
    rw [← hbc', Category.assoc]
    exact e.trans (congrArg (bc.hom.left ≫ ·) (pullback.lift_fst _ _ _))
  have hLB : LBIso t'.PP.L (t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hP.lg
    rw [← P.bundle, ← P'.bundle, ← hbc']
    exact ⟨w, hw⟩
  have := P'.U.gen_hom
  have hp : IsProper (pullback.snd t'.G.hom (jK V)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (isGrpPullback_of_iso P'.U.gen).1 P'.A.isAb.proper
  have hab := GlobalTheory.RigCube.genericPoints_subset_abLocus t'.G t'.semi hp
  obtain ⟨ν, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H (Sp V) (Sp V) t t' (𝟙 _) ψ.hom.left ⟨inferInstance, hab⟩
    (isGrpPullback_of_iso ψ) hact' hLB
  exact ⟨ν⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleIso_of_linear_degenerationData_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  first | exact @GlobalTheory.triple_iso_of_linear_data_iso | exact GlobalTheory.triple_iso_of_linear_data_iso | (intros; apply GlobalTheory.triple_iso_of_linear_data_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.sabMap_of_same_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → ∀ {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, θ (s k) ≠ 0) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e → Nonempty (SABMap t t₁ (spMap θ)) := by
  intro E _ _ _ H D' l c L R V _ _ _ _ _ _ bR bV t₁ P₁ t P iw θ hθ I _ s ε e₁ e hs h₁ h
  classical

  set f : R := ∏ k, s k with hf
  have hfθ : θ f ≠ 0 := by
    rw [hf, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hs k
  have hdiv : ∀ k, ∃ n : ℕ, s k ∣ f ^ n := fun k =>
    ⟨1, by rw [pow_one, hf]; exact Finset.dvd_prod_of_mem s (Finset.mem_univ k)⟩
  have hpsi := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ h₁ f hdiv
  obtain ⟨t', P', hD, ⟨m⟩, hx, hact⟩ := GlobalTheory.T.exists_linearUniformisation_pullback_localMap R V bR bV t₁ P₁ θ hθ f hfθ hpsi
  let e' : P'.D.toPre.X ≃ₗ[𝓞 E] L.D.X := (hD.xe.toLinearEquiv hx).trans e₁
  have h' := GlobalTheory.T.comesFromBase_stable_under_pullback_of_data L P₁.D.toPre P₁.oD P'.D.toPre P'.oD iw θ s ε e₁ hD e' (fun y => rfl) hact hs h₁
  obtain ⟨hD₂, he₂, hact₂⟩ := GlobalTheory.T.exists_isPullDeg_id_same_coordinates L P'.D.toPre P'.oD P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e' e
    hs h' h
  have hx₂ : ∀ (x : 𝓞 E) y, hD₂.xe (x • y) = x • hD₂.xe y := by
    intro x y
    apply e'.injective
    rw [he₂, map_smul, map_smul, he₂]
  obtain ⟨m₂⟩ := GlobalTheory.T.tripleIso_of_linear_degenerationData_iso V bV t' t P' P hD₂ hx₂ hact₂
  exact GlobalTheory.TraitOrder.comp (Category.id_comp _) m m₂
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tripleMap_of_same_uniformised_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → ∀ {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, θ (s k) ≠ 0) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e → Nonempty (SABMap t t₁ (spMap θ)) := by
  first | exact @GlobalTheory.UCanon.sabMap_of_same_coords | exact GlobalTheory.UCanon.sabMap_of_same_coords | (intros; apply GlobalTheory.UCanon.sabMap_of_same_coords <;> assumption)
end
