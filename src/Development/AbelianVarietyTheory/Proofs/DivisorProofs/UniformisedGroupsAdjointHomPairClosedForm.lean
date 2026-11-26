module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThick
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroups

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsSumData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomLiftOneId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

private theorem torusHomOf_iff_appTop₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

private theorem torus_eq₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) {s s' : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf h s) (hs' : TorusHomOf h s') :
    s = s' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
    GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop₂ h s).1 hs, (torusHomOf_iff_appTop₂ h s').1 hs']

private theorem torus_eq_one₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    {s : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf (fun _ => (0 : X)) s) :
    s = toUnit _ ≫ η[splitTorus S X'] := by
  have h0 : (charUnit S X 0).val = 1 := by
    have k := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
    rw [ofAdd_zero, map_one, Units.val_one] at k
    rw [k]
    simp
  have : s = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
    rw [map_one]
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
      (torusHomOf_iff_appTop₂ _ s).1 hs, h0]
    rfl
  rw [this, Hom.one_def]

private theorem pullback_prod_ext₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) {X Y : Over S₀} {Z : Over C}
    {a b : Z ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : a ≫ (Over.pullback f).map (fst X Y) = b ≫ (Over.pullback f).map (fst X Y))
    (h₂ : a ≫ (Over.pullback f).map (snd X Y) = b ≫ (Over.pullback f).map (snd X Y)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y)).hom_ext (by
    rintro ⟨⟨⟩⟩
    · exact h₁
    · exact h₂)

private theorem map_eta₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) (G : Over S₀) [MonObj G] :
    (Over.pullback f).map η[G] = toUnit _ ≫ η[(Over.pullback f).obj G] := by
  rw [Functor.obj.η_def, ← Category.assoc]
  have : toUnit ((Over.pullback f).obj (𝟙_ _)) ≫ Functor.LaxMonoidal.ε (Over.pullback f) = 𝟙 _ :=
    (IsTerminal.isTerminalObj (Over.pullback f) _ isTerminalTensorUnit).hom_ext _ _
  rw [this, Category.id_comp]

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem linHom_lift_one_id : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → LinHom U₂ U i₂ q₂ (lift 1 (𝟙 G₂)) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hS hU i₂ hi₁ hi₂
  have := hS.lim
  let xe : D.toPre.X ≃+ D₁.toPre.X × D₂.toPre.X := AddEquiv.ofBijective (q₁.prod q₂) hS.xsum
  have hxe : ∀ x, xe x = (q₁ x, q₂ x) := fun x => rfl
  let j₁ : D₁.toPre.X → D.toPre.X := fun y => xe.symm (y, 0)
  let j₂ : D₂.toPre.X → D.toPre.X := fun y => xe.symm (0, y)
  have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
    have k := hxe (j₁ y); simp only [j₁, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
    have k := hxe (j₂ y); simp only [j₂, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hone : IsMonHom (1 : G₂ ⟶ G₁) := by rw [Hom.one_def]; infer_instance
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have hq₁ := (U₁.gt e).q_hom
    have hq₂ := (U₂.gt e).q_hom
    have hiso : IsIso ((Over.pullback (thick R I e)).map (lift p₁ p₂)) := inferInstance
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    apply pullback_prod_ext₂
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂]
      simp
  ·
    refine ⟨GlobalTheory.SplitTorusPow.torusMap _ q₂, (torusHomOf_iff_appTop₂ _ _).2 fun χ =>
      GlobalTheory.SplitTorusPow.torusMap_char q₂ χ, ?_⟩
    have hT : TorusHomOf q₂ (GlobalTheory.SplitTorusPow.torusMap (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) q₂) :=
      (torusHomOf_iff_appTop₂ _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q₂ χ
    obtain ⟨t₁, ht₁, e₁⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, e₂⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    have c₁ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₁ = toUnit _ ≫ η[splitTorus _ D₁.toPre.X] := by
      refine torus_eq_one₂ ?_
      have k := TorusHomOf.comp hT ht₁
      simp only [(hj₁ _).2] at k
      exact k
    have c₂ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₂ = 𝟙 _ := by
      refine torus_eq₂ (fun χ => χ) ?_ (TorusHomOf.id _)
      have k := TorusHomOf.comp hT ht₂
      simp only [(hj₂ _).2] at k
      exact k
    have hi₁' := (U₁.gt e).i_hom
    apply pullback_prod_ext₂
    · simp only [Category.assoc]
      rw [e₁, ← Category.assoc _ t₁, c₁, ← Functor.map_comp, lift_fst, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc]
      rw [e₂, ← Category.assoc _ t₂, c₂, ← Functor.map_comp, lift_snd]
      simp

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSndOfIsProdUnif
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SndAdj

open GlobalTheory.CechPic

theorem psum_comp_hom {S : Scheme.{0}} {T H H' : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    (f : H ⟶ H') [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I ≫ f = psum H' (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem sum_cube_zero {S : Scheme.{0}} {T H : Over S} [GrpObj H] [IsCommMonObj H] {M : Type*} [AddCommGroup M]
    (F : (T ⟶ H) → M) (y : Fin 2 → (T ⟶ H)) (hy : y 0 = 1) :
    ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) • F (psum H y I.down) = 0 := by
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) • F (psum H y I))
    (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide]
  simp only [ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.psum_eq_prod]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [hy]

theorem gAdj_snd_of_isProdUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have cL : cls _ hL = CechPic.pull (fst G₁ G₂).left (cls _ hL₁) + CechPic.pull (snd G₁ G₂).left (cls _ hL₂) :=
    (cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj cubeLB
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL₂ _ _)).1 ?_
  rw [cls_linComb hL, cls_linComb hL₂, cL]
  simp only [map_add (f := _), ← CechPic.pull_comp, smul_add, Finset.sum_add_distrib]
  have h₁ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (fst G₁ G₂).left = (psum G₁ ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  have h₂ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (snd G₁ G₂).left = (psum G₂ ![fst G₂ (G₁ ⊗ G₂), snd G₂ (G₁ ⊗ G₂) ≫ snd G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [h₁, h₂]
  exact add_eq_right.2 (sum_cube_zero
    (fun u : G₂ ⊗ G₁ ⊗ G₂ ⟶ G₁ => CechPic.pull u.left (cls _ hL₁)) ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] rfl)

end GlobalTheory.MumProd.SndAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySum
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProdUnifSum

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  intro R _ _ _ hB D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  obtain ⟨U, hU⟩ := GlobalTheory.T.uniformisation_product_of_uniformisedGroups R hB D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  refine ⟨U, GlobalTheory.MumProd.gAdj_prod_fst R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    GlobalTheory.MumProd.SndAdj.gAdj_snd_of_isProdUnif R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    fun i₁ i₂ j₁ j₂ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨?_, hU.linHom_fst j₁ h5 h6, ?_, hU.linHom_snd j₂ h7 h8⟩⟩
  · exact GlobalTheory.MumProd.IsProdUnif.linHom_inl R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ h1 h2
  · exact GlobalTheory.MumProd.linHom_lift_one_id R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₂ h3 h4

end GlobalTheory.MumProdUnifSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_uniformised_groups_uniformised_by_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  first | exact @GlobalTheory.MumProdUnifSum.main | exact GlobalTheory.MumProdUnifSum.main | (intros; apply GlobalTheory.MumProdUnifSum.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegDataSecondFactorInclProjAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalTensorLineBundleSwapIsoSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

theorem adj_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := GlobalTheory.T.isMonHom_of_section_of_isIso_lift _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := GlobalTheory.T.partialSum_comp_monHom_eq_partialSum _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := GlobalTheory.T.partialSum_insert_killed_coordinate_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.exists_cubeBundle_iso_externalTensor_first_factor _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => GlobalTheory.T.latticeInclusion_first_factor_over_abelianInclusion _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.T.periods_sumDegenerationData_fst_cube_iso R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_degeneration_first_factor_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  first | exact @GlobalTheory.MumProd.adj_inl | exact GlobalTheory.MumProd.adj_inl | (intros; apply GlobalTheory.MumProd.adj_inl <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProdSwap

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem pullU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    pullU f V (res h a) = res (fun _ hx => h hx : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U a) := by
  apply Units.ext
  have e := congrArg (fun q => q.hom a.val) (f.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

variable {X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem swap_le (p : (LB.div (extLB L₂ L₁ f₂ f₁) L).ι) :
    (LB.div (extLB L₂ L₁ f₂ f₁) L).U p ≤ (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((p.1.2, p.1.1), p.2) :=
  fun _ hx => ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩

def swapIso (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) : LB.Iso L (extLB L₂ L₁ f₂ f₁) where
  s := fun p => res (swap_le p) (w.s ((p.1.2, p.1.1), p.2))

theorem gm_div {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (M N : LB X) (p q : M.ι × N.ι)
    (h : f y ∈ (LB.div M N).U p ⊓ (LB.div M N).U q) :
    gm f y _ ((LB.div M N).g p q) = gm f y _ (M.g p.1 q.1) * (gm f y _ (N.g p.2 q.2))⁻¹ := by
  show gm f y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ h _)
    ((map_inv _ _).trans (congrArg _ (gm_res f y _ h _))))

theorem gm_tens {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (M N : LB X) (p q : M.ι × N.ι)
    (h : f y ∈ (tensLB M N).U p ⊓ (tensLB M N).U q) :
    gm f y _ ((tensLB M N).g p q) = gm f y _ (M.g p.1 q.1) * gm f y _ (N.g p.2 q.2) := by
  show gm f y _ (res _ (M.g p.1 q.1) * res _ (N.g p.2 q.2)) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ h _) (gm_res f y _ h _))

theorem g_swap (i j : (LB.div (extLB L₂ L₁ f₂ f₁) L).ι)
    (hle : (LB.div (extLB L₂ L₁ f₂ f₁) L).U i ⊓ (LB.div (extLB L₂ L₁ f₂ f₁) L).U j ≤
      (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((i.1.2, i.1.1), i.2) ⊓ (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((j.1.2, j.1.1), j.2)) :
    (LB.div (extLB L₂ L₁ f₂ f₁) L).g i j =
      res hle ((LB.div (extLB L₁ L₂ f₁ f₂) L).g ((i.1.2, i.1.1), i.2) ((j.1.2, j.1.1), j.2)) := by
  apply unit_ext
  intro x hx
  have hx' := hle hx
  have e1 := (gm_div (𝟙 X) x (extLB L₂ L₁ f₂ f₁) L i j hx).trans
    (congrArg (· * _) (gm_tens (𝟙 X) x (L₂.pull f₂) (L₁.pull f₁) i.1 j.1 ⟨hx.1.1, hx.2.1⟩))
  have e2 := (gm_res (𝟙 X) x hle hx _).trans ((gm_div (𝟙 X) x (extLB L₁ L₂ f₁ f₂) L _ _ hx').trans
    (congrArg (· * _) (gm_tens (𝟙 X) x (L₁.pull f₁) (L₂.pull f₂) (i.1.2, i.1.1) (j.1.2, j.1.1) ⟨hx'.1.1, hx'.2.1⟩)))
  exact e1.trans ((congrArg₂ (· * ·) (mul_comm _ _) rfl).trans e2.symm)

theorem externalTensorLineBundleSwapIso_sections (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : (LB.div (extLB L₂ L₁ f₂ f₁) L).ι) :
    (swapIso w).s p = res (swap_le p) (w.s ((p.1.2, p.1.1), p.2)) := rfl

theorem swapIso_isGen {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) : (swapIso w).IsGen := by
  intro i j
  have hle : (LB.div (extLB L₂ L₁ f₂ f₁) L).U i ⊓ (LB.div (extLB L₂ L₁ f₂ f₁) L).U j ≤
      (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((i.1.2, i.1.1), i.2) ⊓ (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((j.1.2, j.1.1), j.2) :=
    fun _ hx => ⟨⟨⟨hx.1.1.2, hx.1.1.1⟩, hx.1.2⟩, ⟨⟨hx.2.1.2, hx.2.1.1⟩, hx.2.2⟩⟩
  have e := congrArg (res hle) (hw ((i.1.2, i.1.1), i.2) ((j.1.2, j.1.1), j.2))
  rw [map_mul] at e
  erw [res_res, res_res] at e
  rw [externalTensorLineBundleSwapIso_sections, externalTensorLineBundleSwapIso_sections]
  erw [res_res, res_res]
  rw [g_swap i j hle]
  exact e

theorem mapsAt₂_swap {Y : Scheme.{0}} {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} {p : Y ⟶ X} {n : ℤ}
    {a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    {b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))}
    {b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))}
    (h : MapsAt₂ w p n a b₁ b₂) : MapsAt₂ (swapIso w) p n a b₂ b₁ := by
  intro j₂ j₁ jL
  have hle : p ⁻¹ᵁ (LB.div (extLB L₂ L₁ f₂ f₁) L).U (extIdx (f₁ := f₂) (f₂ := f₁) j₂ j₁, jL) ≤
      p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) :=
    fun _ hx => ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
  have e := congrArg (res hle) (h j₁ j₂ jL)
  rw [map_mul, map_mul, map_zpow] at e
  erw [res_res, res_res, res_res] at e
  have key : pullU p _ ((swapIso w).s (extIdx j₂ j₁, jL)) = res hle (pullU p _ (w.s (extIdx j₁ j₂, jL))) :=
    pullU_res p (swap_le _) _
  rw [key, mul_comm]
  exact e

section Deg

variable {R : Type} [CommRing R] [IsDomain R]

theorem lift_swap_isIso {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} (f : T ⟶ A) (g : T ⟶ B)
    (h : IsIso (lift f g)) : IsIso (lift g f) := by
  have e : lift g f = lift f g ≫ lift (snd A B) (fst A B) := by ext <;> simp
  have hs : IsIso (lift (snd A B) (fst A B)) :=
    ⟨⟨lift (snd B A) (fst B A), by ext <;> simp, by ext <;> simp⟩⟩
  rw [e]
  infer_instance

theorem isSumDeg_swap {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} {q₁ : D.X →+ D₁.X}
    {q₂ : D.X →+ D₂.X} (h : IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂) : IsSumDeg D D₂ D₁ p₂ p₁ q₂ q₁ := by
  obtain ⟨w, hw, ⟨b₁, b₂, hm, hc₁, hc₂⟩, hψ⟩ := h.w
  refine ⟨h.hom₂, h.hom₁, lift_swap_isIso _ _ h.lim, ?_, h.c_pr₂, h.c_pr₁,
    ⟨swapIso w, swapIso_isGen hw, ⟨b₂, b₁, mapsAt₂_swap hm, hc₂, hc₁⟩, fun x => ?_⟩⟩
  · exact Prod.swap_bijective.comp h.xsum
  · obtain ⟨c₁, c₂, hm', h₁, h₂⟩ := hψ x
    exact ⟨c₂, c₁, mapsAt₂_swap hm', h₂, h₁⟩

end Deg

theorem adj_snd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I)
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ →
    ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] →
      i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ h i₂ j₂ h₁ h₂ h₃ h₄
  exact GlobalTheory.T.product_degeneration_first_factor_adjoint R I D D₂ D₁ p₂ p₁ q₂ q₁ (isSumDeg_swap h) i₂ j₂ h₂ h₁ h₄ h₃

end GlobalTheory.MumProdSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegDataSecondFactorInclProjAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumSumSnd

theorem adj_snd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ :=
  GlobalTheory.MumProdSwap.adj_snd

end GlobalTheory.MumSumSnd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegDataSecondFactorInclProjAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDegData_secondFactor_incl_proj_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ := by
  first | exact @GlobalTheory.MumSumSnd.adj_snd | exact GlobalTheory.MumSumSnd.adj_snd | (intros; apply GlobalTheory.MumSumSnd.adj_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProdAdj

theorem adj_first_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := GlobalTheory.isMonHom_section_of_prod_trivial _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.MumProd.exists_cubeIso _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => GlobalTheory.MumProd.c_inc_fst _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.MumProd.tau_sum_fst R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProdAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPairStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productData_firstFactor_adjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  first | exact @GlobalTheory.MumProdAdj.adj_first_factor | exact GlobalTheory.MumProdAdj.adj_first_factor | (intros; apply GlobalTheory.MumProdAdj.adj_first_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsSumData
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem prod_main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂), ∃ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂)) (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (q₁ : D.toPre.X →+ D₁.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSemiAbelian (G₁ ⊗ G₂) ∧ i₁ ≫ p₁ = 𝟙 _ ∧ i₂ ≫ p₂ = 𝟙 _ ∧ (∀ y, q₁ (j₁ y) = y) ∧ (∀ y, q₂ (j₂ y) = y) ∧ Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ ∧ Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ ∧ LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) ∧ GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂
  obtain ⟨D, p₁, p₂, q₁, q₂, pD⟩ := GlobalTheory.T.exists_product_degenerationData_sum R (maximalIdeal R) D₁ D₂
  obtain ⟨A, a₁, a₂, pA, -⟩ := GlobalTheory.T.exists_product_principallyPolarised_abelianScheme _ A₁ A₂
  obtain ⟨U, hg₁, hg₂, H⟩ := GlobalTheory.T.product_uniformised_groups_uniformised_by_sum R hR D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ pD pA
  haveI := pD.lim
  let e := AddEquiv.ofBijective (q₁.prod q₂) pD.xsum
  let i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A := lift (𝟙 _) (toUnit _ ≫ η[D₂.toPre.P.A]) ≫ inv (lift p₁ p₂)
  let i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A := lift (toUnit _ ≫ η[D₁.toPre.P.A]) (𝟙 _) ≫ inv (lift p₁ p₂)
  let j₁ : D₁.toPre.X →+ D.toPre.X := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
  let j₂ : D₂.toPre.X →+ D.toPre.X := e.symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _)
  have hinv₁ : inv (lift p₁ p₂) ≫ p₁ = fst _ _ := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hinv₂ : inv (lift p₁ p₂) ≫ p₂ = snd _ _ := by
    rw [IsIso.inv_comp_eq, lift_snd]
  have hi₁₁ : i₁ ≫ p₁ = 𝟙 _ := by simp only [i₁, Category.assoc, hinv₁, lift_fst]
  have hi₁₂ : i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] := by simp only [i₁, Category.assoc, hinv₂, lift_snd]
  have hi₂₁ : i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] := by simp only [i₂, Category.assoc, hinv₁, lift_fst]
  have hi₂₂ : i₂ ≫ p₂ = 𝟙 _ := by simp only [i₂, Category.assoc, hinv₂, lift_snd]
  have he : ∀ z, e (e.symm z) = z := e.apply_symm_apply
  have hj₁₁ : ∀ y, q₁ (j₁ y) = y := fun y => congrArg Prod.fst (he (y, 0))
  have hj₁₂ : ∀ y, q₂ (j₁ y) = 0 := fun y => congrArg Prod.snd (he (y, 0))
  have hj₂₁ : ∀ y, q₁ (j₂ y) = 0 := fun y => congrArg Prod.fst (he (0, y))
  have hj₂₂ : ∀ y, q₂ (j₂ y) = y := fun y => congrArg Prod.snd (he (0, y))
  obtain ⟨l₁, l₂, l₃, l₄⟩ := H i₁ i₂ j₁ j₂ hi₁₁ hi₁₂ hi₂₁ hi₂₂ hj₁₁ hj₁₂ hj₂₁ hj₂₂
  exact ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, GlobalTheory.T.isSemiAbelian_tensor_over_scheme _ G₁ G₂ hG₁ hG₂, hi₁₁, hi₂₂, hj₁₁, hj₂₂,
    GlobalTheory.T.productData_firstFactor_adjointPair R _ D D₁ D₂ p₁ p₂ q₁ q₂ pD i₁ j₁ hi₁₁ hi₁₂ hj₁₁ hj₁₂,
    GlobalTheory.T.productDegData_secondFactor_incl_proj_adjoint R _ D D₁ D₂ p₁ p₂ q₁ q₂ pD i₂ j₂ hi₂₁ hi₂₂ hj₂₁ hj₂₂, l₁, l₂, l₃, l₄, hg₁, hg₂⟩

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsSumDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_uniformised_groups_sum_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂), ∃ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂)) (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (q₁ : D.toPre.X →+ D₁.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSemiAbelian (G₁ ⊗ G₂) ∧ i₁ ≫ p₁ = 𝟙 _ ∧ i₂ ≫ p₂ = 𝟙 _ ∧ (∀ y, q₁ (j₁ y) = y) ∧ (∀ y, q₂ (j₂ y) = y) ∧ Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ ∧ Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ ∧ LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) ∧ GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  first | exact @GlobalTheory.MumProd.prod_main | exact GlobalTheory.MumProd.prod_main | (intros; apply GlobalTheory.MumProd.prod_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSwapComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

def chartPullPerm {X Y Y' : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ' : K' → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε' : K' → ℤ) (ε : K → ℤ) (h : Y' ⟶ Y) (e : K' ≃ K)
    (hc : ∀ k, φ' (e.symm k) = h ≫ φ k) (hε : ∀ k, ε' (e.symm k) = ε k) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) h :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j (e.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy (e.symm k)
      rw [hc] at this
      exact this
  { idx := fun j k => j (e.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (Fintype.prod_equiv e.symm _ _ fun k => ?_).symm
      rw [Category.id_comp, hc, hε] }

theorem psum_perm {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (I : Finset (Fin n)) : psum G x' I = h ≫ psum G x (I.map σ.toEmbedding) := by
  rw [CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => hx i

def chartPullCube {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (L : LB G.left) : ChartPull (cubeLB G x' L) (cubeLB G x L) h.left :=
  chartPullPerm L _ _ _ _ h.left (Equiv.ulift.trans ((Equiv.finsetCongr σ).trans Equiv.ulift.symm))
    (fun k => by
      show (psum G x' ((Equiv.finsetCongr σ).symm k.down)).left = h.left ≫ (psum G x k.down).left
      rw [psum_perm G h x x' σ hx, Over.comp_left]
      congr 3
      exact (Equiv.finsetCongr σ).apply_symm_apply k.down)
    (fun k => by
      show (-1 : ℤ) ^ (n - ((Equiv.finsetCongr σ).symm k.down).card) = (-1) ^ (n - k.down.card)
      simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply])

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_swap {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} (H : GAdj L₁ L₂ u u') : GAdj L₂ L₁ u' u :=
  LBIso.chartPull
    (chartPullCube G₁ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂, snd G₁ G₂ ≫ u'] ![fst G₂ G₁ ≫ u', snd G₂ G₁]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₁)
    (chartPullCube G₂ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂ ≫ u, snd G₁ G₂] ![fst G₂ G₁, snd G₂ G₁ ≫ u]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₂)
    (LBIso.symm H)

theorem gAdj_comp {S : Scheme.{0}} {G₁ G₂ G₃ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    [GrpObj G₃] [IsCommMonObj G₃] {L₁ : LB G₁.left} {L₂ : LB G₂.left} {L₃ : LB G₃.left} (hL₁ : L₁.IsLB)
    (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} {v : G₂ ⟶ G₃} {v' : G₃ ⟶ G₂}
    (H : GAdj L₁ L₂ u u') (H' : GAdj L₂ L₃ v v') : GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  LBIso.trans (LB.isLB_linComb hL₃ _ _) (LB.isLB_linComb hL₂ _ _) (LB.isLB_linComb hL₁ _ _)
    (LBIso.chartPull
      (chartPullCube G₃ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃ ≫ v, snd G₂ G₃]
        ![fst G₁ G₃ ≫ u ≫ v, snd G₁ G₃] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₃)
      (chartPullCube G₂ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃, snd G₂ G₃ ≫ v']
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂) H')
    (LBIso.chartPull
      (chartPullCube G₂ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂ ≫ u, snd G₁ G₂]
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂)
      (chartPullCube G₁ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂, snd G₁ G₂ ≫ u']
        ![fst G₁ G₃, snd G₁ G₃ ≫ v' ≫ u'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₁) H)

theorem gAdj_swap_comp :
    (∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : LB G₁.left)
      (L₂ : LB G₂.left), L₁.IsLB → L₂.IsLB → ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), GAdj L₁ L₂ u u' → GAdj L₂ L₁ u' u) ∧
    ∀ (S : Scheme.{0}) (G₁ G₂ G₃ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃]
      [IsCommMonObj G₃] (L₁ : LB G₁.left) (L₂ : LB G₂.left) (L₃ : LB G₃.left), L₁.IsLB → L₂.IsLB → L₃.IsLB →
      ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) (v : G₂ ⟶ G₃) (v' : G₃ ⟶ G₂), GAdj L₁ L₂ u u' → GAdj L₂ L₃ v v' →
        GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ H => gAdj_swap H,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ _ _ _ _ H H' => gAdj_comp h₁ h₂ h₃ H H'⟩

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullPerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjSwap

section Charts

variable {X Y Y' : Scheme.{0}}

def pullInv {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso B A) :
    LB.Iso A' B' where
  s p := (res (fun y hy => ⟨a.le _ hy.2, b.le _ hy.1⟩ :
      B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)))
    (pullU h _ (w.s (a.idx p.2, b.idx p.1))))⁻¹

theorem gm_pullInv {Z : Scheme.{0}} {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (b : ChartPull B' B h) (w : LB.Iso B A) (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullInv a b w).s p) =
      (gm (r ≫ h) z (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ hz _).trans
    (gm_pull r h z _ (show h (r z) ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) from ⟨a.le _ hz.2, b.le _ hz.1⟩) _)))

theorem pullInv_isGen {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    {w : LB.Iso B A} (hw : w.IsGen) : (pullInv a b w).IsGen := fun p q => unit_ext fun y hy => by
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((pullInv a b w).s p) =
        (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ := fun p hp =>
    (gm_pullInv a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) :=
    ⟨⟨a.le _ hy.1.2, b.le _ hy.1.1⟩, ⟨a.le _ hy.2.2, b.le _ hy.2.1⟩⟩
  have e := congrArg (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1))))
    (hw (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1))
  have e' : gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)) =
      gm h y (A.U (a.idx p.2) ⊓ A.U (a.idx q.2)) (A.g (a.idx p.2) (a.idx q.2)) *
        (gm h y (B.U (b.idx p.1) ⊓ B.U (b.idx q.1)) (B.g (b.idx p.1) (b.idx q.1)))⁻¹ *
        gm h y (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) (w.s (a.idx q.2, b.idx q.1)) :=
    (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B A h y (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1) hm) (gm_res h y _ hm _))))
  have d : gm (𝟙 Y') y ((LB.div B' A').U p ⊓ (LB.div B' A').U q) ((LB.div B' A').g p q) =
      gm (𝟙 Y') y (B'.U p.1 ⊓ B'.U q.1) (B'.g p.1 q.1) * (gm (𝟙 Y') y (A'.U p.2 ⊓ A'.U q.2) (A'.g p.2 q.2))⁻¹ :=
    gm_div A' B' (𝟙 Y') y p q hy
  refine (gm_res _ y _ hy _).trans ((val p hy.1).trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  rw [d, gm_res (𝟙 Y') y _ hy, val q hy.2, b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, e']
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem gm_gen_congr {M : LB X} (t : LB.Gen M) {r r' : Y ⟶ X} (hr : r = r') (y : Y) {i i' : M.ι} (hi : i = i') :
    gm r y (M.U i) (t.s i) = gm r' y (M.U i') (t.s i') := by
  subst hr hi; rfl

theorem gm_g_congr (L : LB X) (f : Y ⟶ X) (y : Y) {i i' j j' : L.ι} (hi : i = i') (hj : j = j') :
    gm f y (L.U i ⊓ L.U j) (L.g i j) = gm f y (L.U i' ⊓ L.U j') (L.g i' j') := by
  subst hi hj; rfl

def chartPullPerm (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (e : K ≃ K) (hc : ∀ k, φ' k = h ≫ φ (e k)) (hε : ∀ k, ε (e k) = ε k) :
    ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h where
  idx j k := j (e.symm k)
  le j y hy := Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy (e.symm k)
    rw [hc, Equiv.apply_symm_apply] at this
    exact this
  g y j j' hj hj' := by
    refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_ (gm_linComb L φ ε h y _ _
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj' (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)).symm)
    refine Fintype.prod_equiv e _ _ fun k => ?_
    simp only [hε, Category.id_comp, hc]
    exact congrArg (· ^ ε k) (gm_g_congr L _ y (congrArg j (e.symm_apply_apply k)).symm
      (congrArg j' (e.symm_apply_apply k)).symm)

end Charts

section Sums

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem psum_eq_prod {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I = ∏ i ∈ I, x i := by
  have hnd : ((List.finRange n).filter (· ∈ I)).Nodup := (List.nodup_finRange n).filter _
  calc psum G x I = (((List.finRange n).filter (· ∈ I)).map x).prod := by
        unfold psum
        generalize ((List.finRange n).filter (· ∈ I)) = l
        induction l with
        | nil => rfl
        | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons]; rfl
    _ = ∏ i ∈ I, x i := by
        rw [← List.prod_toFinset x hnd]
        congr 1
        ext i
        simp

theorem psum_perm {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G))
    (π : Equiv.Perm (Fin n)) (hx : ∀ i, x' i = σ ≫ x (π i)) (I : Finset (Fin n)) :
    psum G x' I = σ ≫ psum G x (I.map π.toEmbedding) := by
  calc psum G x' I = ∏ i ∈ I, x' i := psum_eq_prod x' I
    _ = ∏ i ∈ I, σ ≫ x (π i) := by simp only [hx]
    _ = σ ≫ ∏ i ∈ I, x (π i) := (map_prod (preHom (G := G) σ) _ I).symm
    _ = σ ≫ ∏ i ∈ I.map π.toEmbedding, x i := by rw [Finset.prod_map]; rfl
    _ = σ ≫ psum G x (I.map π.toEmbedding) := by rw [psum_eq_prod]

end Sums

def swapIdx : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.swap (0 : Fin 2) 1).finsetCongr.trans Equiv.ulift.symm)

theorem swapIdx_down (I : ULift.{0} (Finset (Fin 2))) :
    (swapIdx I).down = I.down.map (Equiv.swap (0 : Fin 2) 1).toEmbedding := rfl

end GlobalTheory.MumFam.AdjSwap

namespace GlobalTheory.MumFam


open AdjSwap in
theorem adj_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₁ a' a h' h := by
  intro R _ _ Q₁ Q₂ a a' h h' ⟨ha, ha', hc, hc', w, hw, hv⟩
  let σ : Q₂.B ⊗ Q₁.B ⟶ Q₁.B ⊗ Q₂.B := lift (snd Q₂.B Q₁.B) (fst Q₂.B Q₁.B)
  have hA : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] K.down).left =
      σ.left ≫ (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, AdjSwap.psum_perm σ ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hB : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] K.down).left =
      σ.left ≫ (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, AdjSwap.psum_perm σ ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hε : ∀ K : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - (swapIdx K).down.card)) = (-1) ^ (2 - K.down.card) :=
    fun K => by rw [swapIdx_down, Finset.card_map]
  let cA : ChartPull (cubeLB Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] Q₁.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L) σ.left :=
    AdjSwap.chartPullPerm Q₁.M.L _ _ _ σ.left swapIdx hA hε
  let cB : ChartPull (cubeLB Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] Q₂.M.L)
      (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) σ.left :=
    AdjSwap.chartPullPerm Q₂.M.L _ _ _ σ.left swapIdx hB hε
  refine ⟨ha', ha, hc', hc, pullInv cA cB w, pullInv_isGen cA cB hw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hp : (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left ≫ σ.left =
      (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left := by
    rw [← Over.comp_left]; congr 1; simp [σ]
  have key : adjVal (pullInv cA cB w) (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left z J₁ J₂ =
      (adjVal w (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left z J₂ J₁)⁻¹ := by
    let p' := (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left
    have m₁ := hJ₁.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left) p'
    have m₂ := hJ₂.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left) p'
    have e1 := gm_pullInv cA cB w p' z
      (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left),
        fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)) ⟨m₁, m₂⟩
    have i₁ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] k.down).left := fun k => by
      rw [hA, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have i₂ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] k.down).left := fun k => by
      rw [hB, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have e2 := gm_gen_congr w hp z (Prod.ext (funext fun k => congrArg J₂ (i₁ k)) (funext fun k => congrArg J₁ (i₂ k)) :
      ((cA.idx (fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)),
        cB.idx (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left))) :
          (LB.div (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L)
            (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)).ι) =
        (fun I => J₂ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] I.down).left),
          fun I => J₁ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left)))
    exact e1.trans (congrArg (·⁻¹) e2)
  have o := hv y' y z J₂ J₁ hJ₂ hJ₁
  rw [Q₂.tau_symm (h y') y z J₁ hJ₁, Q₁.tau_symm y' (h' y) z J₂ hJ₂] at o
  rw [key, o, inv_mul_cancel_left]

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupsAdjointHomPairClosedForm
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D₁ D₂ : DegData R (maximalIdeal R)}
  {A A₁ A₂ : PolAV (Sp (FractionRing R))} {G G₁ G₂ : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G₁] [IsCommMonObj G₁]
  [GrpObj G₂] [IsCommMonObj G₂]

theorem exists_linHom_end (hR : Base R) (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) {a a' h h'}
    (H : Adj (pol D) (pol D) a a' h h') : ∃ g, LinHom U.toUnifPre U.toUnifPre a h' g := by
  have hE := GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D a a' h h' H
  obtain ⟨b, hb⟩ := GlobalTheory.Mum.EndThick.formalEnd_exists R hR.1 D A G hG U a a' h h' hE
  obtain ⟨g, hg, e⟩ := GlobalTheory.T.mumford_formalEndomorphism_algebraic R hR D A G hG U a a' h h' hE b hb
  exact ⟨g, linHom_iff_linEnd.2 ⟨hg, (funext e : _ = b).symm ▸ hb⟩⟩

theorem exists_linHom (hR : Base R) (hG₁ : IsSemiAbelian G₁) (hG₂ : IsSemiAbelian G₂) (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁)
    (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A}
    {h : D₁.toPre.X →+ D₂.toPre.X} {h' : D₂.toPre.X →+ D₁.toPre.X} (H : Adj (pol D₁) (pol D₂) a a' h h') :
    ∃ u u', LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧
      GAdj U₁.LG.L U₂.LG.L u u' := by
  obtain ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, hG, ip₁, ip₂, jq₁, jq₂, ad₁, ad₂, l₁, r₁, l₂, r₂, g₁, g₂⟩ :=
    GlobalTheory.T.product_uniformised_groups_sum_data R hR D₁ A₁ G₁ hG₁ U₁ D₂ A₂ G₂ hG₂ U₂
  have H' := GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ ad₁) H) ad₂
  obtain ⟨g, hg⟩ := exists_linHom_end hR hG U H'
  obtain ⟨g', hg'⟩ := exists_linHom_end hR hG U (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ H')
  have ros : GAdj U.LG.L U.LG.L g g' := GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A _ hG U _ _ _ _ (GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D _ _ _ _ H') g g'
    (linHom_iff_linEnd.1 hg) (linHom_iff_linEnd.1 hg')
  refine ⟨_, _, ?_, ?_, GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U₂.LG.isLB _ _ _ _
    (GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U.LG.isLB _ _ _ _ g₁ ros)
    (GlobalTheory.MumFam.gAdj_swap_comp.1 _ _ _ _ _ U₂.LG.isLB U.LG.isLB _ _ g₂)⟩
  · have := (l₁.comp hg).comp r₂
    convert this using 1
    · change a = (i₁ ≫ (p₁ ≫ a) ≫ i₂) ≫ p₂
      simp only [Category.assoc, ip₂, Category.comp_id, reassoc_of% ip₁]
    · ext y
      change h' y = q₁ (j₁ (h' (q₂ (j₂ y))))
      rw [jq₁, jq₂]
  · have := l₂.comp (hg'.comp r₁)
    convert this using 1
    · change a' = i₂ ≫ (p₂ ≫ a' ≫ i₁) ≫ p₁
      simp only [Category.assoc, ip₁, Category.comp_id, reassoc_of% ip₂]
    · ext y
      change h y = q₂ (j₂ (h (q₁ (j₁ y))))
      rw [jq₁, jq₂]

end

theorem adj_groups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := fun R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂ _ _ _ _ H =>
  exists_linHom hR hG₁ hG₂ U₁ U₂ H

end GlobalTheory.MumAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupsAdjointHomPairClosedFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := by
  first | exact @GlobalTheory.MumAdj.adj_groups | exact GlobalTheory.MumAdj.adj_groups | (intros; apply GlobalTheory.MumAdj.adj_groups <;> assumption)
end
