module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUBalanced
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem allU_balanced : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Balanced U := by
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  intro R _ _ _ I hI D A G _ _ hG U
  exact ⟨GlobalTheory.RingActData.exists_oAct GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U,
    GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U⟩

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePrimitiveOfEvenNormData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.JoinPull

section Helpers

variable {X X₁ Z : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}

theorem part_g_of_eq (h : IsPart N M e π) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z) (i j : N.ι)
    (hi : ψ z ∈ M.U (π i)) (hj : ψ z ∈ M.U (π j)) :
    gm χ z (N.U i ⊓ N.U j) (N.g i j) = gm ψ z (M.U (π i) ⊓ M.U (π j)) (M.g (π i) (π j)) := by
  subst hχ; exact h.g _ ψ z i j hi hj

theorem part_g_eq_one (h : IsPart N M e π) (hM : M.IsLB) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z)
    (i j : N.ι) (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) : gm χ z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  rw [part_g_of_eq h ψ χ hχ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

end Helpers

theorem exists_iso_of_joinGen : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  intro X₁ X₂ M M' hM hM' h₁ h₂ F t ht
  obtain ⟨i₀⟩ := @nonempty_idx _ _ hM h₁
  obtain ⟨k₀⟩ := @nonempty_idx _ _ hM' h₂
  have hl := isPart_inl M' M
  have hr := isPart_inr M' M
  have le : ∀ a : (PUnit.{1} → M.ι) × M'.ι, (LB.div (M.pull F) M').U a ≤
      LB.wchart (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))) := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      rcases k with u | u
      · exact (hr.mem (k₀, a.1 PUnit.unit) (F y)).2 (mem_pull.1 hy.1)
      · exact (hl.mem (a.2, i₀) y).2 hy.2
  let c : ChartPull (LB.div (M.pull F) M')
      (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)))) (𝟙 X₂) :=
    { idx := fun a => Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))
      le := le
      g := fun y a b ha hb => by
        refine (gm_div M' (M.pull F) (𝟙 X₂) y a b ⟨ha, hb⟩).trans ?_
        refine Eq.trans ?_ (gm_linComb (join M' M) _ _ (𝟙 X₂) y _ _ (le a ha) (le b hb)).symm
        rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
        exact congrArg₂ (· * ·)
          ((gm_pull_g M F (𝟙 X₂) y a.1 b.1 ha.1 hb.1).trans ((part_g_of_eq hr (𝟙 X₂ ≫ F) _
            (Category.assoc _ _ _).symm y (k₀, a.1 PUnit.unit) (k₀, b.1 PUnit.unit) (mem_pull.1 ha.1)
            (mem_pull.1 hb.1)).symm.trans (zpow_one _).symm))
          ((congrArg (·⁻¹) (part_g_of_eq hl (𝟙 X₂) _ rfl y (a.2, i₀) (b.2, i₀) ha.2 hb.2).symm).trans
            (zpow_neg_one _).symm) }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z f z J hJ => ?_⟩
  have m : f z ∈ (LB.div (M.pull F) M').U (fun _ => rr J (f ≫ F), rl J f) :=
    ⟨mem_pull.2 (hr.good hJ (f ≫ F)), hl.good hJ f⟩
  have n := hJ.mem (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) f
  refine (gm_res f z _ m _).trans ((gen_trans ht f z (le _ m) n).trans ?_)
  have e₁ : trF (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))) f z
      (Sum.elim (fun _ => (k₀, rr J (f ≫ F))) (fun _ => (rl J f, i₀)))
      (fun k => J (f ≫ Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl) k)) = 1 := by
    rw [trF, Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
    exact (congrArg₂ (· * ·)
      ((congrArg (· ^ _) (part_g_eq_one hr hM (f ≫ F) _ (Category.assoc _ _ _).symm z
        (k₀, rr J (f ≫ F)) (J (f ≫ F ≫ coprod.inr))
        (congrArg (fun q => (J q).2) (Category.assoc _ _ _)) (hr.good hJ (f ≫ F)))).trans (one_zpow _))
      ((congrArg (· ^ _) (part_g_eq_one hl hM' f _ rfl z (rl J f, i₀) (J (f ≫ coprod.inl)) rfl
        (hl.good hJ f))).trans (one_zpow _))).trans (mul_one 1)
  exact (congrArg (· * _) e₁).trans (one_mul _)

end GlobalTheory.JoinPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoinStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_pullback_of_coprodJoin : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  first | exact @GlobalTheory.JoinPull.exists_iso_of_joinGen | exact GlobalTheory.JoinPull.exists_iso_of_joinGen | (intros; apply GlobalTheory.JoinPull.exists_iso_of_joinGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValEqOneOfGenericSpecDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValEqOneOfGenericSpecDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.GenOne

theorem unit_eq_one_of_generic (R : Type) [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (a : Γ(Spec (CommRingCat.of R), V)ˣ) (h : ∀ z, gm (jK R) z V a = 1) : a = 1 := by
  subst hV
  have h1 : pullU (jK R) ⊤ a = 1 := by
    refine unit_ext fun x _ => ?_
    rw [map_one, gm_pull (𝟙 _) (jK R) x ⊤ trivial, Category.id_comp]
    exact h x
  have h2 : (jK R).appTop.hom (a : Γ(Spec (CommRingCat.of R), ⊤)) = 1 := congrArg Units.val h1
  have h3 := congrArg (fun f => f.hom (a : Γ(Spec (CommRingCat.of R), ⊤)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [h2, map_one] at h3
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a : Γ(Spec (CommRingCat.of R), ⊤)) = 1 :=
    IsFractionRing.injective R (FractionRing R) (by rw [map_one]; exact h3.symm)
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h4

theorem val_eq_one_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ X)) (ε : K → ℤ), FormEq φ ε (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) (PEmpty.elim : PEmpty → ℤ) → ∀ t : LB.Gen (LB.LinComb L φ ε), t.IsGen → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ X) → L.ι), Good L z J → val t (jK R) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → val t r z J = 1 := by
  intro R _ _ X L hL K _ φ ε hF t ht hgen Z r z J hJ
  obtain ⟨t', -, hv⟩ := exists_gen hL hF t ht
  have htop : ∀ j : PEmpty → L.ι,
      L.wchart (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) j = ⊤ := by
    intro j
    simp [LB.wchart]
  have key : ∀ j, t'.s j = 1 := by
    intro j
    refine unit_eq_one_of_generic R _ (htop j) _ fun y => ?_
    choose J' hJ' using fun ψ : (TK R).left ⟶ X => exists_chart hL (ψ y)
    have h1 := (hv _ (jK R) y J' hJ').trans (hgen y J' hJ')
    have e : j = fun k => J' (jK R ≫ (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) k) :=
      funext fun k => k.elim
    subst e
    exact h1
  rw [← hv Z r z J hJ]
  exact (congrArg (gm r z _) (key _)).trans (map_one _)

end GlobalTheory.Mum.GenOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValEqOneOfGenericSpecDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_val_eq_one_of_generic_spec_domain : ∀ (R : Type) [CommRing R] [IsDomain R] {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ X)) (ε : K → ℤ), FormEq φ ε (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) (PEmpty.elim : PEmpty → ℤ) → ∀ t : LB.Gen (LB.LinComb L φ ε), t.IsGen → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ X) → L.ι), Good L z J → val t (jK R) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → val t r z J = 1 := by
  first | exact @GlobalTheory.Mum.GenOne.val_eq_one_of_generic | exact GlobalTheory.Mum.GenOne.val_eq_one_of_generic | (intros; apply GlobalTheory.Mum.GenOne.val_eq_one_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.PrimPull

theorem lamF {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] {X Y : Scheme.{0}} (x y : T ⟶ B)
    (f₁ : T.left ⟶ Y) (f₂ : Y ⟶ (G2 B).left) (hf : f₁ ≫ f₂ = (lift x y).left) (e : B.left ⟶ X)
    {U : Type} [CommGroup U] (h : (T.left ⟶ X) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (f₁ ≫ f₂ ≫ (psum B (x2 B) I.down).left ≫ e) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h ((x * y).left ≫ e) * (h (x.left ≫ e))⁻¹ * (h (y.left ≫ e))⁻¹ * h ((1 : T ⟶ B).left ≫ e) := by
  refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (GlobalTheory.PrimCocycle.prod_lam x y (fun q => h (q ≫ e)))
  rw [← Category.assoc f₁, hf]
  simp only [Category.assoc]

theorem lamFneg {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] {X : Scheme.{0}} (x y : T ⟶ B)
    (e : B.left ⟶ X) {U : Type} [CommGroup U] (h : (T.left ⟶ X) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B (x2 B) I.down).left ≫ e) ^ (-((-1 : ℤ) ^ (2 - I.down.card))) =
      (h ((x * y).left ≫ e) * (h (x.left ≫ e))⁻¹ * (h (y.left ≫ e))⁻¹ * h ((1 : T ⟶ B).left ≫ e))⁻¹ :=
  (GlobalTheory.MumBil.prodNeg (fun I : ULift.{0} (Finset (Fin 2)) => h ((lift x y).left ≫ (psum B (x2 B) I.down).left ≫ e))
    (fun I => (-1 : ℤ) ^ (2 - I.down.card))).trans
    (congrArg (·⁻¹) (lamF x y (lift x y).left (𝟙 _) (Category.comp_id _) e h |>.symm.trans (Finset.prod_congr rfl fun I _ => by rw [Category.id_comp])).symm)

theorem isPullDeg_of_primitive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.toPre.OAct O) (o' : D'.toPre.OAct O) (w : O), TraceFormTwistIso D.toPre o w → TraceFormTwistIso D'.toPre o' w → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom → ((∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x))) → (∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J) → ∃ hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre, hD.xe = xe ∧ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := by
  intro R _ _ _ hR D D' O _ _ _ _ o o' w hw hw' Φ xe hΦ hlin hwΛ
  obtain ⟨hact, hxe, hc⟩ := hlin
  obtain ⟨wΛ, gΛ, vΛ⟩ := hwΛ
  obtain ⟨u, hu, hu0, hup⟩ := hw
  obtain ⟨u', hu', hu0', hup'⟩ := hw'
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB
  have P₁ := isPart_inl D'.toPre.P.L D.toPre.P.L
  have P₂ := isPart_inr D'.toPre.P.L D.toPre.P.L
  have hN := join_isLB hM' hM
  obtain ⟨t₁, ht₁, vt₁⟩ := exists_gen_of_iso P₂ P₁ wΛ gΛ
  have g₁ := DVR.pullGen_isGen _ _ _ t₁ ht₁ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left
  have g₂ := P₁.gen_isGen hu'
  have g₃ := P₂.gen_isGen (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ u hu Φ.hom.left))
  have g₄ := P₂.gen_isGen (DVR.pullGen_isGen _ _ _ D.toPre.rig D.toPre.rig_gen (toUnit D'.toPre.P.A).left)
  have g₅ := P₁.gen_isGen (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ D'.toPre.rig D'.toPre.rig_gen (toUnit D'.toPre.P.A).left))
  have g := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃) g₄) g₅
  have E1 : (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left ≫ (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom)).left = (lift Φ.hom (o'.onB.act w ≫ Φ.hom)).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
  have q1 : (Φ.hom * (o'.onB.act w ≫ Φ.hom)).left = Φ.hom.left ≫ (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left := by
    rw [← Over.comp_left]
    refine congrArg Over.Hom.left ?_
    show _ = Φ.hom ≫ (𝟙 _ * o.onB.act w)
    rw [MonObj.comp_mul, Category.comp_id, hact]
  have q2 : (o'.onB.act w ≫ Φ.hom).left = Φ.hom.left ≫ (o.onB.act w).left := by
    rw [← Over.comp_left, hact]
  have q3 : (1 : D'.toPre.P.A ⟶ D.toPre.P.A).left = (toUnit D'.toPre.P.A).left ≫ eSec D.toPre.P.A := rfl
  have q4 : Φ.hom.left ≫ (toUnit D.toPre.P.A ≫ η).left = (toUnit D'.toPre.P.A).left ≫ eSec D.toPre.P.A := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]; rfl
  have q6 : (𝟙 D'.toPre.P.A * o'.onB.act w).left = (padd D'.toPre.P.A (𝟙 _) (o'.onB.act w)).left := rfl
  have q8 : (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = (toUnit D'.toPre.P.A).left ≫ eSec D'.toPre.P.A := rfl
  have q9 : (toUnit D'.toPre.P.A ≫ η).left = (toUnit D'.toPre.P.A).left ≫ eSec D'.toPre.P.A := rfl
  obtain ⟨t, ht, vt⟩ := exists_gen hN (φ' := Sum.elim (fun _ : PUnit => Φ.hom.left ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (ε' := Sum.elim (fun _ => (1:ℤ)) (fun _ => (-1:ℤ))) (by
      intro U _ h
      clear vΛ vt₁ hu0 hup hu0' hup' hxe hc g g₁ g₂ g₃ g₄ g₅ gΛ ht₁ hM hM' hN hu hu'
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [lamF Φ.hom (o'.onB.act w ≫ Φ.hom) _ _ E1, lamFneg, q1, q2, q3, q4, Category.comp_id, q8, q9, q6]
      simp only [Category.id_comp, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, zpow_one]
      clear q1 q2 q3 q4 q6 q8 q9 E1 t₁ u u' P₁ P₂ wΛ xe hΦ hact
      abel) _ g
  obtain ⟨w₀, hw₀, vw₀⟩ := GlobalTheory.T.exists_lineBundleIso_pullback_of_coprodJoin D.toPre.P.L D'.toPre.P.L hM hM' inferInstance inferInstance Φ.hom.left t ht
  have vw : ∀ (Z : Scheme.{0}) (f : Z ⟶ D'.toPre.P.A.left) (z : Z)
      (J : (Z ⟶ D'.toPre.P.A.left ⨿ D.toPre.P.A.left) → (join D'.toPre.P.L D.toPre.P.L).ι),
      Good (join D'.toPre.P.L D.toPre.P.L) z J →
      gw w₀ f z (rr J (f ≫ Φ.hom.left)) (rl J f) =
        GlobalTheory.PolDeg.lamVal wΛ (f ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left) z (rr J) (rl J) * val u' f z (rl J) *
          (val u (f ≫ Φ.hom.left) z (rr J))⁻¹ * val D.toPre.rig (f ≫ (toUnit D'.toPre.P.A).left) z (rr J) *
          (val D'.toPre.rig (f ≫ (toUnit D'.toPre.P.A).left) z (rl J))⁻¹ := by
    intro Z f z J hJ
    rw [vw₀ Z f z J hJ, vt Z f z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, vt₁ _ _ z J hJ,
      P₁.val_gen _ _ _ hJ, P₂.val_gen _ _ _ hJ, P₂.val_gen _ _ _ hJ, P₁.val_gen _ _ _ hJ, val_inv, val_inv,
      val_pull (P₂.good hJ), val_pull (P₂.good hJ), val_pull (P₁.good hJ)]
    rfl
  haveI := hΦ
  have c0' : D'.toPre.c 0 = 1 := by
    have h := D'.toPre.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 (h.symm : D'.toPre.c 0 * D'.toPre.c 0 = D'.toPre.c 0)
  have hone : ∀ {T : Over (Spec (CommRingCat.of R))} (s : T ⟶ 𝟙_ (Over (Spec (CommRingCat.of R)))),
      s ≫ η[D'.toPre.P.A] ≫ lift (𝟙 D'.toPre.P.A) (o'.onB.act w) = lift (1 : T ⟶ D'.toPre.P.A) 1 := by
    intro T s
    have e1 : (η[D'.toPre.P.A] : 𝟙_ _ ⟶ D'.toPre.P.A) ≫ o'.onB.act w = η := by
      haveI := o'.onB.hom w; exact IsMonHom.one_hom _
    rw [comp_lift, comp_lift, Category.comp_id, e1, Hom.one_def, toUnit_unique s (toUnit T)]
  have hjK : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have Z0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
      (J : (Z ⟶ D'.toPre.P.A.left ⨿ D.toPre.P.A.left) → (join D'.toPre.P.L D.toPre.P.L).ι),
      Good (join D'.toPre.P.L D.toPre.P.L) z J →
      GlobalTheory.PolDeg.lamVal wΛ (r ≫ eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left) z (rr J) (rl J) = 1 := by
    have E0 : eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left =
        (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) 1).left := by
      rw [eSec, ← Over.comp_left, ← hone (𝟙 _), Category.id_comp]
    have E0' : (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) 1).left ≫
        (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom)).left =
        (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A) 1).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    intro Z r z J hJ
    have key := GlobalTheory.T.generator_val_eq_one_of_generic_spec_domain R (join D'.toPre.P.L D.toPre.P.L) hN _ _ (by
        intro U _ h
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_empty, E0]
        rw [lamF 1 1 _ _ E0', lamFneg, _root_.mul_one, _root_.mul_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
      (LB.pullGen _ _ _ t₁ (eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left))
      (DVR.pullGen_isGen _ _ _ _ ht₁ _) (by
        intro y J hJ
        rw [val_pull hJ, vt₁ _ _ y J hJ]
        have E1g : jK R ≫ eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left =
            (lift (toUnit (TK R) ≫ D'.toPre.c 0) (toUnit (TK R) ≫ D'.toPre.c 0)).left := by
          rw [c0', MonObj.comp_one, ← hone (toUnit (TK R)), Over.comp_left, Over.comp_left, hjK]; rfl
        have v := vΛ 0 0 y (rr J) (rl J) (P₂.good hJ) (P₁.good hJ)
        rw [GlobalTheory.MumBil.tau_zero D'.tau_bimult (P₁.good hJ), map_zero, GlobalTheory.MumBil.tau_zero D.tau_bimult (P₂.good hJ),
          _root_.mul_one] at v
        rw [E1g]; exact v.symm) Z r z J hJ
    rw [val_pull hJ, vt₁ _ _ z J hJ] at key
    exact key
  have hE : eSec D'.toPre.P.A ≫ Φ.hom.left = eSec D.toPre.P.A := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hT : eSec D'.toPre.P.A ≫ (toUnit D'.toPre.P.A).left = 𝟙 _ := by
    rw [eSec, ← Over.comp_left, toUnit_unique (η ≫ toUnit D'.toPre.P.A) (𝟙 _)]; rfl
  have exJ : ∀ (Z : Scheme.{0}) (z : Z) (f : Z ⟶ D'.toPre.P.A.left) (p : D.toPre.P.L.ι) (q : D'.toPre.P.L.ι),
      Φ.hom.left (f z) ∈ D.toPre.P.L.U p → f z ∈ D'.toPre.P.L.U q →
      ∃ J, Good (join D'.toPre.P.L D.toPre.P.L) z J ∧ rr J (f ≫ Φ.hom.left) = p ∧ rl J f = q := by
    intro Z z f p q hp hq
    obtain ⟨J, hJ, e⟩ := exists_good (join D'.toPre.P.L D.toPre.P.L) hN z (K := Bool)
      (fun b => if b then (f ≫ Φ.hom.left) ≫ coprod.inr else f ≫ coprod.inl) (fun _ => (q, p)) (fun _ _ _ => rfl) (by
        rintro (_ | _)
        · exact (P₁.mem (q, p) (f z)).2 hq
        · exact (P₂.mem (q, p) _).2 hp)
    exact ⟨J, hJ, congrArg Prod.snd (e true), congrArg Prod.fst (e false)⟩
  have hr : PMaps w₀ (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1)
      D'.toPre.rig D.toPre.rig (𝟙 _) := by
    intro Z r z p q hp hq
    obtain ⟨J, hJ, ep, eq⟩ := exJ Z z (r ≫ eSec D'.toPre.P.A) (p PUnit.unit) (q PUnit.unit) (hp PUnit.unit) (hq PUnit.unit)
    have v := vw Z (r ≫ eSec D'.toPre.P.A) z J hJ
    rw [ep, eq] at v
    have a1 : GlobalTheory.PolDeg.lamVal wΛ ((r ≫ eSec D'.toPre.P.A) ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left) z
        (rr J) (rl J) = 1 := by
      rw [Category.assoc]; exact Z0 Z r z J hJ
    have a2 : val u' (r ≫ eSec D'.toPre.P.A) z (rl J) = 1 := by
      rw [← val_pull (P₁.good hJ), val_corr (P₁.good hJ) hu0' r, val_one]
    have a3 : val u ((r ≫ eSec D'.toPre.P.A) ≫ Φ.hom.left) z (rr J) = 1 := by
      rw [Category.assoc, hE, ← val_pull (P₂.good hJ), val_corr (P₂.good hJ) hu0 r, val_one]
    have a4 : (r ≫ eSec D'.toPre.P.A) ≫ (toUnit D'.toPre.P.A).left = r := by
      rw [Category.assoc, hT, Category.comp_id]
    have a5 : gm r z (LB.wchart D.toPre.P.L (fun _ => eSec D.toPre.P.A) p) (D.toPre.rig.s p) =
        val D.toPre.rig r z (rr J) := by
      refine (val_of _ _ _ _ p fun k => ?_).symm
      rw [← ep, ← hE, ← Category.assoc]
    have a6 : gm r z (LB.wchart D'.toPre.P.L (fun _ => eSec D'.toPre.P.A) q) (D'.toPre.rig.s q) =
        val D'.toPre.rig r z (rl J) := by
      refine (val_of _ _ _ _ q fun k => ?_).symm
      rw [← eq]
    simp only [Fintype.prod_unique, zpow_one, Category.comp_id]
    rw [v, a1, a2, a3, a4, a5, a6]
    group
  have hx : ∀ x, D'.toPre.xK x ≫ Φ.hom.left = D.toPre.xK (xe x) := fun x => by
    show (toUnit (TK R) ≫ D'.toPre.c x).left ≫ Φ.hom.left = (toUnit (TK R) ≫ D.toPre.c (xe x)).left
    rw [← Over.comp_left, Category.assoc, hc]
  have vΛr : ∀ (a b : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z)
      (J : (Z ⟶ D'.toPre.P.A.left ⨿ D.toPre.P.A.left) → (join D'.toPre.P.L D.toPre.P.L).ι),
      Good (join D'.toPre.P.L D.toPre.P.L) z J →
      val (D'.toPre.tau a b) r z (rl J) = GlobalTheory.PolDeg.lamVal wΛ
        (r ≫ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left) z (rr J) (rl J) *
        val (D.toPre.tau (xe a) (xe b)) r z (rr J) := by
    intro a b Z r z J hJ
    have C := corr_of_val hN (t := P₁.gen (D'.toPre.tau a b))
      (t' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁
        (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left) (P₂.gen (D.toPre.tau (xe a) (xe b))))
      (fun y J hJ => by
        rw [P₁.val_gen _ _ _ hJ, val_mul hJ, val_pull hJ, vt₁ _ _ _ _ hJ, P₂.val_gen _ _ _ hJ, Category.id_comp]
        exact vΛ a b y (rr J) (rl J) (P₂.good hJ) (P₁.good hJ))
    have := val_corr hJ C r
    rw [P₁.val_gen _ _ _ hJ, val_mul hJ, val_pull hJ, vt₁ _ _ _ _ hJ, P₂.val_gen _ _ _ hJ] at this
    exact this
  have hψ : ∀ x, PMaps w₀ (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1)
      (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _) := by
    intro x Z r z p q hp hq
    obtain ⟨J, hJ, ep, eq⟩ := exJ Z z (r ≫ D'.toPre.xK x) (p PUnit.unit) (q PUnit.unit) (hp PUnit.unit) (hq PUnit.unit)
    have v := vw Z (r ≫ D'.toPre.xK x) z J hJ
    rw [ep, eq] at v
    have m1 : (r ≫ D'.toPre.xK x) ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left =
        r ≫ (lift (toUnit (TK R) ≫ D'.toPre.c x) (toUnit (TK R) ≫ D'.toPre.c (w • x))).left := by
      rw [Category.assoc, o'.c_lin]
      congr 1
      show (toUnit (TK R) ≫ D'.toPre.c x).left ≫ _ = _
      rw [← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
    have m2 : (r ≫ D'.toPre.xK x) ≫ Φ.hom.left = r ≫ D.toPre.xK (xe x) := by rw [Category.assoc, hx]
    have m3 : (r ≫ D'.toPre.xK x) ≫ (toUnit D'.toPre.P.A).left = r ≫ (toUnit (TK R)).left := by
      rw [Category.assoc]; congr 1
      show (toUnit (TK R) ≫ D'.toPre.c x).left ≫ _ = _
      rw [← Over.comp_left, Category.assoc, toUnit_unique (D'.toPre.c x ≫ toUnit _) (𝟙 _), Category.comp_id]
    rw [m1, m2, m3] at v
    have A := val_corr (P₁.good hJ) (hup' x) r
    rw [val_mul (P₁.good hJ), val_mul (P₁.good hJ), val_pull (P₁.good hJ), DegPre.rigK, val_pull (P₁.good hJ)] at A
    have B := val_corr (P₂.good hJ) (hup (xe x)) r
    rw [val_mul (P₂.good hJ), val_mul (P₂.good hJ), val_pull (P₂.good hJ), DegPre.rigK, val_pull (P₂.good hJ)] at B
    have Cc := vΛr x (w • x) Z r z J hJ
    rw [hxe] at Cc
    have a5 : gm (r ≫ 𝟙 _) z (LB.wchart D.toPre.P.L (fun _ => D.toPre.xK (xe x)) p) ((D.toPre.psi (xe x)).s p) =
        val (D.toPre.psi (xe x)) r z (rr J) := by
      rw [Category.comp_id]
      refine (val_of _ _ _ _ p fun k => ?_).symm
      rw [← ep, ← hx, ← Category.assoc]
    have a6 : gm r z (LB.wchart D'.toPre.P.L (fun _ => D'.toPre.xK x) q) ((D'.toPre.psi x).s q) =
        val (D'.toPre.psi x) r z (rl J) := by
      refine (val_of _ _ _ _ q fun k => ?_).symm
      rw [← eq]
    simp only [Fintype.prod_unique]
    rw [a5, a6, v, eq_mul_inv_of_mul_eq B.symm, eq_mul_inv_of_mul_eq A.symm, Cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  have hs := specOf_id R
  have gp : IsGrpPullback D'.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr hs.symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  obtain ⟨w', g', r', ψ'⟩ := GlobalTheory.UnifUniq.exists_transport hF
    (fun (F : D'.toPre.P.A.left ⟶ D.toPre.P.A.left) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull F)) => w.IsGen ∧
      PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1)
        D'.toPre.rig D.toPre.rig (𝟙 _) ∧
      ∀ x, PMaps w (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1)
        (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _)) w₀ ⟨hw₀, hr, hψ⟩
  obtain ⟨W, hW, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  have hc₁' : ∀ x, (D'.toPre.c x).left ≫ Φ.hom.left = (D.toPre.c (xe x)).left := fun x => by
    rw [← Over.comp_left, hc]
  obtain ⟨hD, e₁, -, e₃⟩ := GlobalTheory.UnifUniq.exists_isPullDeg_id D.toPre D'.toPre W hW ψW e me w' g'
    ((congrArg (_ ≫ ·) hF).trans hE) r' xe (fun x => (congrArg (_ ≫ ·) hF).trans (hc₁' x)) ψ'
  exact ⟨hD, e₃, by rw [e₁]; exact hF⟩

end GlobalTheory.PrimPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degeneration_data_iso_of_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.toPre.OAct O) (o' : D'.toPre.OAct O) (w : O), TraceFormTwistIso D.toPre o w → TraceFormTwistIso D'.toPre o' w → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom → ((∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x))) → (∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J) → ∃ hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre, hD.xe = xe ∧ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := by
  first | exact @GlobalTheory.PrimPull.isPullDeg_of_primitive | exact GlobalTheory.PrimPull.isPullDeg_of_primitive | (intros; apply GlobalTheory.PrimPull.isPullDeg_of_primitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.HomConst

theorem map_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (ψ : G ⟶ G) :
    ((Over.pullback (thick R I e)).map ψ).left ≫ (fstG I e G).left = (fstG I e G).left ≫ ψ.left := by
  simp [fstG, pullback.lift_fst]

end GlobalTheory.Mum.Two.PullLin


open GlobalTheory.Mum.Two.PullLin GlobalTheory.Mum.Two.HomConst in
theorem GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  intro R _ _ _ hB D A G _ _ hG U D' A' U' hD ψ bc b hψ hbc hb hP
  obtain ⟨hR, -⟩ := hB
  obtain ⟨wL, -, he, -, hlev⟩ := hP.lg

  have lev : ∀ e, ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h = ((Over.pullback (thick R (maximalIdeal R) e)).map ψ).left ∧
      (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        h ≫ (U.gt e).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt e).pG) x k ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            h ≫ D.toPre.Oφ ((U.gt e).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt e).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) h _
            Oinvε _ hψ ((U.gt e).t (hD.xe x)))) := by
    intro e
    obtain ⟨h, h1, h2, h3, -⟩ := hlev e
    have : Mono (fstG (maximalIdeal R) e G).left :=
      inferInstanceAs (Mono (pullback.fst G.hom (thick R (maximalIdeal R) e)))
    refine ⟨h, (cancel_mono (fstG (maximalIdeal R) e G).left).1 ?_, h2, h3⟩
    rw [h1, hbc, map_fstG]
  refine ⟨fun e => ?_, ?_⟩
  · obtain ⟨h, rfl, h2, -⟩ := lev e
    have : Mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) := inferInstance
    refine Over.OverMorphism.ext ((cancel_mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))).1 ?_)
    rw [hb] at h2
    clear lev hlev hP wL he
    simp only [Over.comp_left, Category.assoc]
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · show (U'.gt e).q.left ≫ pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ b.left = _
      congr 1
      exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨-, -, -, hC⟩ := id hR
    obtain ⟨h₀, hT⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R (maximalIdeal R) hR D' D A' A G G U'.toUnifPre
      U.toUnifPre ψ hψ
    have key : (h₀ : D.toPre.X → D'.toPre.X) = hD.xe.symm := by
      haveI := hC
      obtain ⟨t, ht, hi⟩ := hT 0
      refine acts_unique (U'.gt 0) (U.gt 0) (acts_of_torusHomOf _ _ _ ht hi) ?_
      obtain ⟨h, rfl, -, h3⟩ := lev 0
      clear lev hlev hP wL he hT ht hi
      intro Z r z J₁ J₂ hJ₁ hJ₂ c χ
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [AddEquiv.symm_apply_apply]
      obtain ⟨hψk, M⟩ := h3 x
      have P := (maps_iff hD.w _ _ Oinvε _ _ _ _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψk ·) (fun _ => rfl)).1 M
      have e := P Z r z
        (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
        (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => hJ₂ _) (fun k => hJ₁ _)
      have h1 := GlobalTheory.ArcLieCompare.prod_Oφ_zero (D := D'.toPre) (U'.gt 0).pG r
        (r ≫ (fstG (maximalIdeal R) 0 G).left ≫ G.hom) (c.trans (by simp only [Category.assoc])) x
        (fun f => gw hD.w f z (J₂ (f ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) (J₁ f))
      rw [h1, _root_.one_mul] at e
      rw [val_of _ _ z J₂
          (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
          (fun k => by simp only [Category.assoc, hψk k]),
        val_of _ r z J₁ (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => rfl)]
      exact e
    rw [key] at hT
    exact hT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationPullbackAlongId_lies_over_dataIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  first | exact @GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus | exact GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus | (intros; apply GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.NormLam

theorem lbIso_cubeLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

theorem lbIso_lam_adj_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw P hP
  have hwh := oG.hom w
  have hwh' := oG.hom (star w)
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin a
  have hc := fun T : Over (Sp R) => GlobalTheory.PrimNorm.diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w) x.left) =
      fun x => GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act w) T x) :=
    fun T => funext fun x => GlobalTheory.PrimNorm.normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G),
      GlobalTheory.PrimNorm.postHom (oG.act w) T y * GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) (GlobalTheory.PrimNorm.postHom (oG.act w) T x) y =
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y) :=
    fun T x y => GlobalTheory.PrimNorm.diff₂_ptCls_adj hM (hadj w) x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _
      ((GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.cls U.LG.L)).symm))
    rw [hq]
    exact GlobalTheory.PrimNorm.diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have hN := cubeLB_isLB' ![𝟙 G, oG.act w] hM
  have hPL := P.L.isLB
  have cP : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x P.L.L).IsLB := fun x => cubeLB_isLB' x hPL
  have cN : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x (cubeLB G ![𝟙 G, oG.act w] U.LG.L)).IsLB :=
    fun x => cubeLB_isLB' x hN
  have cL : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x U.LG.L).IsLB := fun x => cubeLB_isLB' x hM

  have isoP : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] P.L.L) (cubeLB G ![x, y] U.LG.L) :=
    fun T x y => LBIso.trans (cP _) (cN _) (cL _) (lbIso_cubeLB' _ hP) (iso T x y)
  refine ⟨isoP _ (fst G G) (snd G G), fun a => ?_, ?_⟩
  · exact LBIso.trans (cP _) (cL _) (cP _) (isoP _ _ _)
      (LBIso.trans (cL _) (cL _) (cP _) (hadj a) (isoP _ _ _).symm)
  · exact LBIso.trans hPL hN (cP _) hP (LBIso.trans hN (cN _) (cP _) (iso G (𝟙 G) (oG.act w)).symm
      (lbIso_cubeLB' _ hP).symm)

end GlobalTheory.Mum.NormLam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_mumford_adjoint_primitive_of_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  first | exact @GlobalTheory.Mum.NormLam.lbIso_lam_adj_prim | exact GlobalTheory.Mum.NormLam.lbIso_lam_adj_prim | (intros; apply GlobalTheory.Mum.NormLam.lbIso_lam_adj_prim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMaps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {h : X' → X}
    {t t' : splitTorus S X ⟶ splitTorus S X'} (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht,
    (torusHomOf_iff_appTop _ _).1 ht']

theorem hom_eq_of_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨t, ht, j₁⟩ := i₁ e
  obtain ⟨t', ht', j₂⟩ := i₂ e
  have htt : t = t' := torusHomOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _
    ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))

end GlobalTheory.Mum.Two
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_ext_of_induced_maps : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  first | exact @GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus | exact GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus | (intros; apply GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.GenPol

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ (A' : PolAV (Sp (FractionRing R))) (gen' : (Over.pullback (jK R)).obj G ≅ A'.A), IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o oA oG hlin w hw hpsi P hP
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have : IsCommMonObj A.A := A.isAb.comm
  have hwA : IsMonHom (oA.act w) := oA.hom w
  have hwA' : IsMonHom (oA.act (star w)) := oA.hom (star w)
  have hs : oA.act w * oA.act (star w) = 𝟙 A.A := by
    rw [Hom.mul_def]
    change padd A.A (oA.act w) (oA.act (star w)) = 𝟙 A.A
    rw [← oA.map_add, hw, oA.map_one]
  have ha := (GlobalTheory.RosLam.rosatiAdj_iff_lamEq laws.globalFns _ A _ _ hwA hwA').1 (oA.rosati w)
  obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.CM.exists_normalised_polarisation laws (FractionRing R) A _ _ hwA hwA' hs ha
  let A' : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L', isLB := h1, rigid := h2, sym := h3,
      ample := h4, ktriv := h5 }
  refine ⟨A', U.gen, U.gen_hom, ?_⟩
  haveI := U.gen_hom
  have hLG := U.LG.isLB
  have hAL := A.isLB
  let φ := pullback.fst G.hom (jK R)
  let GK := (Over.pullback (jK R)).obj G
  let wGK := (Over.pullback (jK R)).map (oG.act w)
  have lbc : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have s1 : LBIso L' (cubeLB A.A ![𝟙 A.A, oA.act w] A.L) := by
    have e := GlobalTheory.LamCalc.lbIso_of_lamEq h6 (𝟙 A.A) (oA.act w)
    simp only [Category.comp_id] at e
    exact LBIso.trans h1 (lbc _ h1) (lbc _ hAL) h7 e
  have s2 := GlobalTheory.RigidBundleGlue.LBIso.pull s1 U.gen.hom.left
  have hext : LBIso (U.LG.L.pull φ) (A.L.pull U.gen.hom.left) := by
    obtain ⟨v, hv⟩ := U.ext
    exact LBIso.symm ⟨v, hv⟩
  have hgp := isGrpPullback_of_iso U.gen
  have s3 := GlobalTheory.ShapePull.iso_cubeLB_pull hgp (pushPt hgp.1.w (𝟙 GK)) hext
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 A.A) (b := oA.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      have e := congrArg (fun q => q.left) (hlin.ext w)
      simp only [Over.comp_left] at e
      simp only [pushPt, Over.homMk_left, Over.comp_left, Over.id_left, Category.id_comp]
      exact e)
  have hpb := isGrpPullback_pullback G (jK R)
  have s4 := GlobalTheory.ShapePull.iso_cubeLB_pull hpb (pushPt hpb.1.w (𝟙 GK)) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hLG φ))
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 G) (b := oG.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      show wGK.left ≫ φ = (𝟙 GK.left ≫ φ) ≫ (oG.act w).left
      rw [Category.id_comp]
      simp only [wGK, φ, Over.pullback_map_left, pullback.lift_fst])
  have s5 := GlobalTheory.RigidBundleGlue.LBIso.pull hP φ
  have e3 : (pushPt hgp.1.w (𝟙 GK)).left = U.gen.hom.left := by simp [pushPt]
  have e4 : (pushPt hpb.1.w (𝟙 GK)).left = φ := Category.id_comp _
  rw [e3] at s3
  rw [e4] at s4
  have i1 := pull_isLB h1 U.gen.hom.left
  have i2 := pull_isLB (lbc ![𝟙 A.A, oA.act w] hAL) U.gen.hom.left
  have i3 := lbc ![𝟙 GK, wGK] (pull_isLB hLG φ)
  have i4 := pull_isLB (lbc ![𝟙 G, oG.act w] hLG) φ
  have i5 := pull_isLB P.L.isLB φ
  exact LBIso.trans i1 i2 i5 s2 (LBIso.trans i2 i3 i5 s3.symm (LBIso.trans i3 i4 i5 s4 s5.symm))

end GlobalTheory.Mum.GenPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePrimitiveOfEvenNormData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum

theorem mumfordBundle_primitive_of_evenNorm_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (w : O) (ν : ℕ), w + star w = 1 → w * star w = (ν : O) → 1 ≤ ν → Even ν → TraceFormTwistIso D.toPre o w → LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin w ν hw hν hν1 hev hpsi
  haveI : CharZero R := hR.2
  obtain ⟨P, hP, hE⟩ := GlobalTheory.Mum.PrimCube.exists_cp_evenOn R hR D A G hG U O o oA oG hlin w hw hpsi
  obtain ⟨A', gen', hgen, hgL⟩ := GlobalTheory.Mum.GenPol.exists_polAV_generic R hR D A G hG U O o oA oG hlin w hw hpsi P hP
  obtain ⟨D', U', hLG, -⟩ := GlobalTheory.Mum.exists_unif_even R hR G P hG hE A' gen' hgen hgL
  obtain ⟨hlam, hadj, hprim⟩ := GlobalTheory.T.lineBundleIso_mumford_adjoint_primitive_of_twist R hR D A G hG U O o oA oG hlin w hw P hP
  rw [← hLG] at hlam hadj hprim
  obtain ⟨hbal1, hbal2⟩ := GlobalTheory.UT.allU_balanced R (maximalIdeal R) hR.1 D' A' G hG U'
  obtain ⟨oA', hoA'⟩ := GlobalTheory.PELOfUnif.exists_oAct_unif U'.toUnifPre oG hadj
  obtain ⟨md, o', hlin'⟩ := hbal1 O oA' oG hoA' hadj
  letI := md
  have hpsi' : TraceFormTwistIso D'.toPre o' w := hbal2 O o' oA' oG hlin' hadj w ν hw hν hν1 hev hprim
  obtain ⟨Φ, xe, hΦ, hov, hto, hcB, hxs, hxc, hwΛ⟩ :=
    GlobalTheory.T.polarisedDegenerationData_iso_of_mumfordBundle_iso R hR D A G hG U O o oA oG hlin D' A' U' o' oA' hlin' hlam
  obtain ⟨hD, hxe, heΦ⟩ := GlobalTheory.T.primitive_degeneration_data_iso_of_polarised_iso R hR D D' O o o' w hpsi hpsi' Φ xe hΦ ⟨hcB, hxs, hxc⟩ hwΛ
  obtain ⟨ψ, bc, φ, hψ, hbc, hcomp, hpu, -⟩ := GlobalTheory.unif_determined_by_data_normal R hR.1 D A G hG U D' A' G hG U' hD
  obtain ⟨hov', hto'⟩ := GlobalTheory.T.uniformisationPullbackAlongId_lies_over_dataIso R hR D A G hG U D' A' U' hD ψ.hom bc Φ.hom hψ hcomp heΦ hpu
  rw [hxe] at hto'
  have h1 : ψ.hom = 𝟙 G := GlobalTheory.T.uniformisedGroupHom_ext_of_induced_maps R hR D A G hG U D' A' U' ψ.hom (𝟙 G) Φ.hom xe.symm hψ inferInstance hov' hov hto' hto
  obtain ⟨wL, hwL, -⟩ := hpu.lg
  have hc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 G.left := by
    rw [hcomp, h1]; rfl
  have e1 : LBIso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)))) := ⟨wL, hwL⟩
  rw [hc, hLG] at e1
  have hL := U.LG.isLB
  have hPL := P.L.isLB
  have hN : (cubeLB G ![𝟙 G, oG.act w] U.LG.L).IsLB := GlobalTheory.LamCalc.cubeLB_isLB hL _
  have hL1 : (U.LG.L.pull (𝟙 G.left)).IsLB := pull_isLB hL _
  have e0 : LBIso U.LG.L (U.LG.L.pull (𝟙 G.left)) := (GlobalTheory.DescendedPrincipal.lbIso_pull_id hL).symm
  exact LBIso.trans hL hPL hN (LBIso.trans hL hL1 hPL e0 e1.symm) hP

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePrimitiveOfEvenNormDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_cubeLB_of_even_norm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (w : O) (ν : ℕ), w + star w = 1 → w * star w = (ν : O) → 1 ≤ ν → Even ν → TraceFormTwistIso D.toPre o w → LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) := by
  first | exact @GlobalTheory.Mum.mumfordBundle_primitive_of_evenNorm_data | exact GlobalTheory.Mum.mumfordBundle_primitive_of_evenNorm_data | (intros; apply GlobalTheory.Mum.mumfordBundle_primitive_of_evenNorm_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNorm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UChart

theorem w_zero_mul_conj_eq_norm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 * H.bar H.w0 = (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have e : (H.d + 1) / 4 = m := by omega
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hm
  rw [e, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

theorem exists_sab_pelUnif_of_norm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    [inst : Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E))
    (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) :
    ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), P.D = D ∧ HEq P.mod inst ∧ HEq P.oD oD := by
  letI := H.starRing
  obtain ⟨G, iG, cG, A, hG, ⟨U⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨oA, oG, hl⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hR D A G hG U (𝓞 E) oD
  have hd := H.d_mod
  let t : SAB H (Sp R) :=
    { G := G
      semi := hG
      act := ofRingAct oG
      PP := U.LG
      cub := U.cubG
      sym := GlobalTheory.isSymmetric_of_symmetry_generator U.LG U.symG U.symG_gen U.symG_rig
      adj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hG U (𝓞 E) oD oA oG hl a
      prim := GlobalTheory.T.lbIso_cubeLB_of_even_norm R hR D A G hG U (𝓞 E) oD oA oG hl H.w0 ((H.d + 1) / 4)
        (by show H.w0 + H.bar H.w0 = 1; rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]) (w_zero_mul_conj_eq_norm H) (by omega)
        (Nat.even_iff.2 (by omega)) hw }
  exact ⟨t, ⟨D, oD, A, oA, U, rfl, hl, hw⟩, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.UChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_pelUniformisation_of_norm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) [inst : Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)), (letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), P.D = D ∧ HEq P.mod inst ∧ HEq P.oD oD := by
  first | exact @GlobalTheory.UChart.exists_sab_pelUnif_of_norm | exact GlobalTheory.UChart.exists_sab_pelUnif_of_norm | (intros; apply GlobalTheory.UChart.exists_sab_pelUnif_of_norm <;> assumption)
end
