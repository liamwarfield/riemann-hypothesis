module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_cancel_of_eq {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X}
    {F' : X'' ⟶ X'} {F'' : X'' ⟶ X} (e : F' ≫ F = F'') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)
    (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull F'')) (hw : PGen w) (hw'' : PGen w'')
    {Y Y' Y'' : Scheme.{0}} {φ : Y ⟶ X} {φ' : Y' ⟶ X'} {φ'' : Y'' ⟶ X''}
    {t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => 1))}
    {t' : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => φ') (fun _ => 1))}
    {t'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => φ'') (fun _ => 1))}
    {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} {h'' : Y'' ⟶ Y} (eh : h' ≫ h = h'') (hc : φ'' ≫ F' = h' ≫ φ')
    (H : PMaps w _ _ _ t' t h) (H'' : PMaps w'' _ _ _ t'' t h'') :
    ∃ w' : LB.Iso L'' (L'.pull F'), PGen w' ∧ PMaps w' _ _ _ t'' t' h' ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J' J'', Good L z J → Good L' z J' → Good L'' z J'' → ∀ x : Z ⟶ X'',
        om w'' z J J'' x = om w z J J' (x ≫ F') * om w' z J' J'' x := by
  subst e eh
  obtain ⟨w', T⟩ := exists_cancel hL w w'' hw hw'' hL' hL''
  refine ⟨w', T.pgen_cancel hL hw hw'', T.pmaps_cancel hL (fun _ => hc) H H'', fun Z z J J' J'' hJ hJ' hJ'' x => ?_⟩
  rw [om, om, om, Category.assoc]
  exact T Z x z _ _ _ (hJ (x ≫ F' ≫ F)) (hJ' (x ≫ F')) (hJ'' x)

theorem exists_isPullDeg_cancel : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  intro K₀ K₁ K _ _ _ α β D₀ D₁ D h₁ h
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, hΦ, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap α.injective ≫ jK K₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq α.injective)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, hΦ ▸ e₁⟩

end GlobalTheory.FieldPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFieldsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_isPullDeg_cancel | exact GlobalTheory.FieldPull.exists_isPullDeg_cancel | (intros; apply GlobalTheory.FieldPull.exists_isPullDeg_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull

theorem exists_pre_below : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  intro hL K₀ K _ _ i D P₀ Φ gp ⟨w₀, hw₀⟩ c₀ cadd hc
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨cub⟩ := (hL.cube _ P₀ ⟨P₀.L, rig, P₀.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P₀
  choose psi hpsi using fun χ : D.X => DVR.exists_gen_of_local (V := FractionRing K₀) P₀.L P₀.isLB (K := PUnit)
    (fun _ => ptK (c₀ χ)) (fun _ => -1)
  let D₀ : DegPre K₀ :=
    { P := P₀, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P₀.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P₀.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap i) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap i.injective ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap i.injective ≫ jK K₀ ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  choose ψ hψ vψ using fun χ : D.X => exists_down_om ((isGen_iff w).2 hw) P₀.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => D.xK χ) (genMap i.injective) (fun _ => hx χ) (psi χ) (hpsi χ)
  obtain ⟨hD, e, -, -⟩ := exists_isPullDeg_of_val i D₀ (TauTwist.withPsi D ψ hψ) gp w hw hr (AddEquiv.refl _) hc
    (fun x z J J' hJ hJ' => by
      have v := vψ x _ (𝟙 _) z J J' hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at v
      exact v)
  exact ⟨D₀, ψ, hψ, hD, rfl, heq_of_eq e⟩

end GlobalTheory.FieldPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationPreData_over_subfield : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  first | exact @GlobalTheory.FieldPull.exists_pre_below | exact GlobalTheory.FieldPull.exists_pre_below | (intros; apply GlobalTheory.FieldPull.exists_pre_below <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_psi_ratio {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (ψ : TauTwist.PsiFam D)
    (hψ : ∀ χ, (ψ χ).IsGen) (χ : D.X) : ∃ u : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
      val (D.psi χ) (𝟙 _) z J = TauTwist.unitAt (A := FractionRing R) (Z := (TK R).left) (𝟙 _) z u * val (ψ χ) (𝟙 _) z J :=
  TauTwist.exists_ratio (F := FractionRing R) D.P.isLB (fun _ _ _ => rfl) (D.psi_gen χ) (hψ χ)

theorem unitAt_genMap {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (z : (TK K).left) (v : (FractionRing K₁)ˣ) :
    TauTwist.unitAt (A := FractionRing K₁) (genMap β.injective) z v =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom v) :=
  (congrArg (fun r => TauTwist.unitAt (A := FractionRing K₁) r z v) (Category.id_comp _).symm).trans
    (TauTwist.unitAt_spMap (𝟙 _) (fracMap β.injective) z v)

theorem exists_isPullDeg_rescale {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (D₁ : DegPre K₁) (D : DegPre K)
    (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ))
    (q : D₁.X → (FractionRing K₁)ˣ)
    (hq : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ))) *
        val (ψ χ) (𝟙 _) z J) :
    ∃ hD : IsPullDeg β (TauTwist.rescale D₁ q) D, proj hD = proj h := by
  have key : ∀ (x : D.X) (z : (TK K).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val ((TauTwist.rescale D₁ q).psi (h.xe x)) (genMap β.injective) z J =
        (om h.w z J J' (D.xK x))⁻¹ * val (D.psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    have e := psi_val (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h (genMap β.injective) (𝟙 _) (fracMap_sq β.injective) hJ hJ' x
    rw [Category.id_comp] at e
    refine (TauTwist.val_psi_rescale q (h.xe x) _ hJ).trans ((congrArg₂ (· * ·) (unitAt_genMap β z _) e).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) rfl (hq x z J' hJ')).symm
  obtain ⟨hD, hp, -, -⟩ := exists_isPullDeg_of_val β (TauTwist.rescale D₁ q) D (Φ := proj (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h)
    (pull_grp (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.w
    ((isGen_iff h.w).1 h.w_gen) (pmaps_rig (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.xe h.c_pr key
  exact ⟨hD, hp⟩

theorem exists_ratio_descends (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) :
    ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁)
      (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) →
      ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D),
        PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  choose u hu using exists_psi_ratio D ψ hψ
  refine ⟨fun χ => FractionRing.algEquiv K K (u χ).val, fun K₁ _ β D₁ h ha => ?_⟩
  choose a₁ ha₁ using ha
  have key : ∀ χ, fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ χ)) = (u χ).val := fun χ => by
    rw [fracMap_algebraMap, ha₁]
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  have hne : ∀ χ, algebraMap K₁ (FractionRing K₁) (a₁ χ) ≠ 0 := fun χ e => (u χ).ne_zero (by
    rw [← key, e, map_zero])
  obtain ⟨q, hq⟩ : ∃ q : D₁.X → (FractionRing K₁)ˣ,
      ∀ χ, Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ)) = u χ :=
    ⟨fun y => Units.mk0 _ (hne (h.xe.symm y)), fun χ => Units.ext (by
      show fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ (h.xe.symm (h.xe χ)))) = _
      rw [AddEquiv.symm_apply_apply, key])⟩
  obtain ⟨hD, hp⟩ := exists_isPullDeg_rescale β D₁ D ψ hψ h q fun χ z J hJ => by
    rw [hq]; exact hu χ z J hJ
  exact ⟨_, _, hD, hp⟩

end GlobalTheory.FieldPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamilyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily : ∀ (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen), ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) → ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D), PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_ratio_descends | exact GlobalTheory.FieldPull.exists_ratio_descends | (intros; apply GlobalTheory.FieldPull.exists_ratio_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.NeutralPart

theorem _root_.GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (h : ∀ s : S, _root_.IsConnected (f ⁻¹' {s})) : GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  haveI : ConnectedSpace (f ⁻¹' {s}) := isConnected_iff_connectedSpace.mp (h s)
  haveI : ConnectedSpace (f.fiber s) :=
    (f.fiberHomeo s).symm.surjective.connectedSpace (f.fiberHomeo s).symm.continuous
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    instLocallyOfFiniteTypeSndScheme f (S.fromSpecResidueField s)
  exact _root_.GlobalTheory.RatPointConn.of_section (k := S.residueField s)
    (f.fiberToSpecResidueField s)
    (pullback.lift (S.fromSpecResidueField s ≫ e) (𝟙 _) (by simp [he]))
    (pullback.lift_snd _ _ _)

end GlobalTheory.SS.NeutralPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackTheta
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal

open GlobalTheory.VVRank

theorem span_translates_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  intro hL S _ _ P m N hN hm hunit th hth κ _ b₀ hb₀ α hα s₁ hs₁ I U t hU ht
  subst hN
  have hm0 : m ≠ 0 := by omega
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have hsurj : Surjective (mulA P.A m).left := (hL.mulN S P m hm).2.2.1
  have haff : IsAffine (baseOver S).left := ‹IsAffine S›
  obtain ⟨b, hb⟩ := hb₀ (baseOver S) (𝟙 _)
  refine span_eq_top_of_functionals b _ fun 𝔪 h𝔪 l hl y => ?_
  obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (baseOver S).left 𝔪 h𝔪
  let w : Spec (CommRingCat.of K) ⟶ S := u
  let h : Over.mk w ⟶ baseOver S := Over.homMk w (Category.comp_id _)
  have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
  have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  obtain ⟨b', hb'⟩ := hb₀ (Over.mk w) h
  obtain ⟨b₁', hb₁'⟩ := hth (Over.mk w) h
  refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L (m ^ 2 : ℕ) h) b b'
    (fun i => by rw [hb, hb', pullM_id P.A P.isLB]) _ ?_ l (fun c => (hu _).2 (hl c)) y)
  obtain ⟨ρ', k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P (m ^ 2 : ℕ) (Over.mk w)
  choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
  have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (SecM.ofSec P.A (t c)) =
      ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
    ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
  simp only [e]
  have hI : Nonempty I := ⟨(hU K w 1 (by have := P.isAb.comm; exact one_pow _)).choose⟩
  refine span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K w (m ^ 2) hk
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
    (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨c, hc'⟩ := hU K w θ.pt ((hL.kerPow S P (m ^ 2) (Nat.one_le_pow _ _ hm) (Over.mk w) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨c, (hU' c).1.trans hc'⟩
  · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (baseOver S) m) (hm := lift_snd _ _)
      (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
    have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral w _ _
        (IsPullback.of_hasPullback w P.A.hom).flip
    have hz := ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0
    exact b₁'.ne_zero 0 ((hb₁' 0).trans hz)

end GlobalTheory.ThetaReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackThetaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_translates_multiplicationPullback_theta : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.span_translates_mulPull | exact GlobalTheory.ThetaReal.span_translates_mulPull | (intros; apply GlobalTheory.ThetaReal.span_translates_mulPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdeal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem scalar_mem_of_psiIn : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  intro R V _ _ _ _ _ φ D D' β v xe _ hv hc gam hgam hψ ga a hS x J' hJ' p q hpq
  obtain ⟨ga', a', hS'⟩ := exists_psiScal V D'
  obtain ⟨m₀, hm₀, em₀⟩ := (PsiScalIn.main_local D' ga' a' hS' x J').1 hJ'
  obtain ⟨t, ht, Ht⟩ := CubTransport.exists_pmaps ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (φ := fun _ => (D.c (xe x)).left) (ε := fun _ => -1) (spMap φ) (fun _ => hc x)
    (ga (xe x)) (hS (xe x)).1
  obtain ⟨c, hcu⟩ := exists_unit_val_eq_mul D'.P.isLB (hS' x).1 ht
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose I hI using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  choose I' hI' using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have gI : Good D.P.L (Z := (TK V).left) z I := hI
  have gI' : Good D'.P.L (Z := (TK V).left) z I' := hI'
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    change (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc x, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (D.c (xe x)).left) hgam.symm
  have e₁ := CubTransport.val_pmaps (fun _ => hx) (hψ x) (𝟙 _) gI gI'
  have e₂ := CubTransport.val_pmaps (fun _ => hc x) Ht (jK V) gI gI'
  have e₃ := (hS (xe x)).2 (Over.mk (gam ≫ jK R)) (Over.homMk gam rfl) z I gI
  have e₄ := (hS' x).2 (TK V) (𝟙 _) z I' gI'
  have e₅ := hcu _ (jK V) z I' gI'
  rw [Category.id_comp, Fintype.prod_unique, Category.id_comp] at e₁
  rw [Fintype.prod_unique, ← hgam] at e₂
  obtain ⟨Ω, f₁, f₂⟩ : ∃ Ω : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk z)ˣ,
      val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I' ∧
        val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) t (jK V) z I' := ⟨_, e₁, e₂⟩
  have f₃ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I).val =
      gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I).val := e₃
  have f₄ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I').val =
      PsiScalIn.sig z (a' x).val * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga' x) (jK V) z I').val :=
    e₄.trans (congrArg₂ (· * ·) (PsiScalIn.gs_scal_id z _) rfl)
  let u : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom c.val
  have hu : gs (jK V) z ⊤ c.val = PsiScalIn.sig z (algebraMap V _ u) := by
    refine Eq.trans (congrArg (gs (jK V) z ⊤) ?_) (PsiScalIn.gs_toOpen z ⊤ trivial u)
    simp [u, DegPre.toOpen]
  have key : gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) = PsiScalIn.sig z (algebraMap V _ (m₀ * u)) := by
    rw [f₁, f₂, Units.val_mul, Units.val_mul, f₄, mul_left_comm (gs _ _ _ _), Units.mul_right_inj] at f₃
    have f₅ := f₃.symm.trans (congrArg (PsiScalIn.sig z (a' x).val * ·) (e₅.trans (congrArg (· * _) hu)))
    rw [← _root_.mul_assoc, Units.mul_left_inj] at f₅
    rw [map_mul, map_mul, em₀]
    exact f₅
  have hs : ∀ r : R, gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (algebraMap R (FractionRing R) r)) =
      PsiScalIn.sig z (algebraMap V _ (φ r)) := fun r => by
    have k : ∀ {A : Type} [CommRing A] (w : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of A)) (s : A),
        gs (𝟙 _) z ⊤ (scal w s) = cst w z s := fun w s =>
      (gs_pull (𝟙 _) w z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    refine (congrArg _ (PsiInt.scal_jK gam r).symm).trans ((k _ r).trans ?_)
    refine (congrArg (fun w => cst w z r) hgam).trans ((cst_comp (jK V) φ z r).trans ?_)
    refine Eq.trans ?_ (PsiScalIn.gs_toOpen z ⊤ trivial (φ r))
    exact (gs_res (jK V) z (U := ⊤) (V := ⊤) le_top trivial _).symm
  refine ⟨m₀ * u, J'.mul_mem_right u hm₀, IsFractionRing.injective V (FractionRing V) ((PsiScalIn.sig z).injective ?_)⟩
  rw [map_mul (algebraMap V _) (φ q), map_mul (PsiScalIn.sig z), ← hs, ← hs, ← key, ← hpq, ← gs_mul _ z ⊤ trivial]
  unfold scal
  rw [map_mul, map_mul]

end GlobalTheory.PsiRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdealStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  first | exact @GlobalTheory.PsiRing.scalar_mem_of_psiIn | exact GlobalTheory.PsiRing.scalar_mem_of_psiIn | (intros; apply GlobalTheory.PsiRing.scalar_mem_of_psiIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsImage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.AbelianImage

theorem exists_lift {S : Scheme.{0}} {T N G : Over S} [IsReduced T.left] (ν : N ⟶ G)
    [IsClosedImmersion ν.left] (g : T ⟶ G) (h : Set.range g.left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  let Z : TopologicalSpace.Closeds G.left :=
    ⟨Set.range ν.left, ν.left.isClosedEmbedding.isClosed_range⟩
  have h2 : ν.left.ker ≤ g.left.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1
      (show Z ≤ ν.left.ker.support from ν.left.range_subset_ker_support)).trans
      (ReducedSubgroup.vanishingIdeal_le_ker g.left Z h)
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem relDim_le_of_isDominant {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Y) [IsDominant p] (f : Y ⟶ Spec (.of k)) {a b : ℕ}
    (ha : SmoothOfRelativeDimension a (p ≫ f)) (hb : SmoothOfRelativeDimension b f) : b ≤ a := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨A', j', hj', ⟨y, hy⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := p x) (U := ⊤) trivial
  obtain ⟨A, j, hj, ⟨z, hz⟩, hr⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := p ⁻¹ᵁ j'.opensRange) ⟨y, hy⟩
  have hrange : Set.range (j ≫ p) ⊆ Set.range j' := by
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have hl := IsOpenImmersion.lift_fac j' (j ≫ p) hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j' (j ≫ p) hrange)
  obtain ⟨α, hα⟩ := Spec.map_surjective (j' ≫ f)
  rw [← hφ] at hl
  have : Nonempty (Spec A) := ⟨z⟩
  have : Nonempty (Spec A') := ⟨y⟩
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec A') := isIntegral_of_isOpenImmersion j'
  have : IsDomain A := (affine_isIntegral_iff A).1 inferInstance
  have : IsDomain A' := (affine_isIntegral_iff A').1 inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense ⟨_, z, rfl⟩⟩
  have : IsDominant (Spec.map φ ≫ j') := by rw [hl]; infer_instance
  have hd : IsDominant (Spec.map φ) := IsDominant.of_comp_of_isOpenImmersion _ j'
  have hinj : Function.Injective φ.hom := by
    have h1 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).1 hd.1
    rw [nilradical_eq_zero] at h1
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h1)
  letI : Algebra k A' := α.hom.toAlgebra
  letI : Algebra k A := (α ≫ φ).hom.toAlgebra
  have h1 := trdeg_eq_of_smoothOfRelativeDimension k Y f b hb A' j' hj' hα.symm
  have h2 := trdeg_eq_of_smoothOfRelativeDimension k X (p ≫ f) a ha A j hj (by
    rw [← Category.assoc, ← hl, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  have h3 := trdeg_le_of_injective (R := k) (A := A') (A' := A) ⟨φ.hom, fun _ => rfl⟩ hinj
  rw [h1, h2] at h3
  exact_mod_cast h3

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] [BraidedCategory 𝒞]

theorem isCommMonObj_of_mono {N G : 𝒞} [MonObj N] [MonObj G] [IsCommMonObj G] (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] : IsCommMonObj N := by
  refine ⟨?_⟩
  rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

omit [BraidedCategory 𝒞] in
theorem isMonHom_of_comp_mono {M N G : 𝒞} [MonObj M] [MonObj N] [MonObj G] (l : M ⟶ N) (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] [IsMonHom (l ≫ ν)] : IsMonHom l := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Cat

open RationalPoint in
theorem exists_image : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ ψ : B ⟶ G, IsMonHom ψ → ∃ (B' : Over (Sp k)) (_ : GrpObj B') (ν : B' ⟶ G) (π : B ⟶ B'), IsAbelianScheme B' ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ π ≫ ν = ψ ∧ (∀ F : G ⟶ G, IsMonHom F → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), ∃ y : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ψ ≫ F = y ≫ ψ) → ∃ F' : B' ⟶ B', IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ a, SmoothOfRelativeDimension a B.hom → ∃ a', a' ≤ a ∧ SmoothOfRelativeDimension a' B'.hom := by
  intro k _ _ G _ hG B _ hB ψ hψ
  obtain ⟨hc, hs, hsep, -, -⟩ := hG
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : IsProper (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have hZ : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  let φ : (𝟙_ (Over (Sp k)) ⟶ B) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  have hC : ∀ x, x ∈ φ.range ↔ Set.range x.left ⊆ Set.range ψ.left := fun x => by
    rw [range_left_subset_iff, ← Set.image_univ, pt_mem_image_iff ψ isClosed_univ]
    simp only [Set.mem_univ, true_and]
    rfl
  obtain ⟨N, _, ν, hν, hcl, hsm, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k G
    inferInstance φ.range _ hZ hC
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have : IsIntegral B.left := isIntegral_of_smooth_field_of_connectedSpace B.hom
  obtain ⟨π, hπ⟩ := exists_lift ν ψ hr.ge
  have : Surjective π.left := ⟨fun y => by
    obtain ⟨x, hx⟩ := hr.le ⟨y, rfl⟩
    refine ⟨x, ν.left.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hπ]
    rfl⟩
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have : ConnectedSpace N.left := π.left.surjective.connectedSpace π.left.continuous
  have : IsIntegral N.left := isIntegral_of_smooth_field_of_connectedSpace N.hom
  have hw : π.left ≫ N.hom = B.hom := Over.w π
  have : IsSeparated N.hom := by rw [← Over.w ν]; infer_instance
  have : UniversallyClosed (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed N.hom := UniversallyClosed.of_comp_surjective π.left N.hom
  have : GeometricallyConnected (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have hN : IsAbelianScheme N := ⟨isCommMonObj_of_mono ν, hsm, ⟨⟩,
    geometricallyConnected_of_surjective π.left N.hom⟩
  refine ⟨N, inferInstance, ν, π, hN, hν, hcl, hπ, fun F hF h => ?_, fun a ha => ?_⟩
  · have h1 : Set.range (ψ ≫ F).left ⊆ Set.range ψ.left :=
      ReducedSubgroup.range_subset_of_points (ψ ≫ F) hZ fun x => by
        obtain ⟨y, hy⟩ := h x
        exact (hC _).1 ⟨y, hy.symm⟩
    obtain ⟨F', hF'⟩ := exists_lift ν (ν ≫ F) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hr.le ⟨t, rfl⟩
      refine hr.ge (h1 ⟨x, ?_⟩)
      change F.left (ψ.left x) = F.left (ν.left t)
      rw [hx])
    have : IsMonHom (F' ≫ ν) := by rw [hF']; infer_instance
    exact ⟨F', isMonHom_of_comp_mono F' ν, hF'⟩
  · obtain ⟨b, hb⟩ := AbelianDim.exists_relDim k N hN
    exact ⟨b, relDim_le_of_isDominant π.left N.hom (hw ▸ ha) hb, hb⟩

end GlobalTheory.AbelianImage
end
