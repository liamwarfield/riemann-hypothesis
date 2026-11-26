module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Lemmata.GeneralBFactFurther.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section B2

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

def ExpBijF (U : UnifPre I D A G) : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen →
      (∀ t, ∃! s, U.ExpandsF F k w t s) ∧ ∀ s, ∃! t, U.ExpandsF F k w t s

end B2

def ExpBijectiveUniformisation : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G), ExpBijF U.toUnifPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Transport

variable {K : Type} [Field K] {G₁ G₂ : Over (Spec (CommRingCat.of K))} [GrpObj G₁] [GrpObj G₂]

omit [GrpObj G₁] [GrpObj G₂] in
lemma isIso_inv_left (e : G₁ ≅ G₂) : IsIso e.inv.left :=
  Functor.map_isIso (Over.forget _) e.inv

def torusExtOfIso (e : G₁ ≅ G₂) [IsMonHom e.hom] (T : TorusExtension G₁) : TorusExtension G₂ :=
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := T.B
    grpB := T.grpB
    isAbelian := T.isAbelian
    q := e.inv ≫ T.q
    q_hom := inferInstance
    q_flat := by rw [Over.comp_left]; have := T.q_flat; have := isIso_inv_left e; infer_instance
    q_surjective := by rw [Over.comp_left]; have := T.q_surjective; have := isIso_inv_left e; infer_instance
    q_quasiCompact := by rw [Over.comp_left]; have := T.q_quasiCompact; have := isIso_inv_left e; infer_instance
    i := T.i ≫ e.hom
    i_hom := inferInstance
    isKernel := by
      refine IsPullback.of_iso T.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }

end Transport

section Pull

variable {T S S' : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G]

def pullCompMon : (Over.pullback (p ≫ f)).mapMon.obj (Mon.mk G) ≅
    (Over.pullback p).mapMon.obj ((Over.pullback f).mapMon.obj (Mon.mk G)) :=
  (Functor.mapMonNatIso (Over.pullbackComp p f) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)

def pullCompIso : (Over.pullback (p ≫ f)).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G) :=
  (Mon.forget _).mapIso (pullCompMon p f G)

instance : IsMonHom (pullCompIso p f G).hom := by
  show IsMonHom (pullCompMon p f G).hom.hom
  infer_instance

theorem IsSemiAbelian.pullback (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
  refine
    { comm := ?_
      smooth := ?_
      separated := ?_
      quasiCompact := ?_
      geomConnected := ?_
      fibres := ?_ }
  · have := h.comm
    infer_instance
  · have := h.smooth
    change Smooth (pullback.snd G.hom f)
    infer_instance
  · have := h.separated
    change IsSeparated (pullback.snd G.hom f)
    infer_instance
  · have := h.quasiCompact
    change QuasiCompact (pullback.snd G.hom f)
    infer_instance
  · have := h.geomConnected
    change GeometricallyConnected (pullback.snd G.hom f)
    infer_instance
  · intro Ω _ _ q
    obtain ⟨E⟩ := h.fibres Ω (q ≫ f)
    exact ⟨torusExtOfIso (pullCompIso q f G) E⟩

def OAct.pullback [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G) : OAct O ((Over.pullback f).obj G) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

end Pull

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def ArcIn.restrict {k : Type} [CommRing k] [IsDomain k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)
    {O : Type} [CommRing O] (β : O →+* c.F) : ArcIn D l β k (bF.comp β) :=
  { a with geom := fun F _ _ _ r z => a.geom F (β r) (β z) }

def ArcWit.Agree {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (ψ : W.t.G ≅ W'.t.G) : Prop :=
  IsMonHom ψ.hom ∧ (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
  (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
    g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
    g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) ∧
  ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G) (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
    wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
      (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) ∧
    ∀ (n : ℕ) (ψn : (Out.thickObj (PowerSeries k) (Ideal.span {PowerSeries.X}) n W.t.G).left ⟶
        (Out.thickObj (PowerSeries k) (Ideal.span {PowerSeries.X}) n W'.t.G).left),
      ψn = ((Over.pullback (Out.thick (PowerSeries k) (Ideal.span {PowerSeries.X}) n)).map ψ.hom).left →
      ((W.P.U.gt n).pG.left ≫ W.φ = ψn ≫ (W'.P.U.gt n).pG.left ≫ W'.φ) ∧
      ∀ (A : Type) [CommRing A] [IsLocalRing A]
        (v : Sp A ⟶ (Out.thickObj (PowerSeries k) (Ideal.span {PowerSeries.X}) n W.t.G).left),
        (∀ (x : a.D₀.X) (pt₀ : Fin 4 → (Sp A ⟶ a.D₀.P.A.left)) (t₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ Out.Oinvε)),
          t₀.IsGen → GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) v) t₀ →
          GenRelR W'.w (LB.pullGen _ _ _ ((W'.P.U.gt n).t (W'.e x)) (v ≫ ψn)) t₀) ∧
        ∀ (j₀ : a.D₀.P.L.ι) (jM : W.P.D.toPre.P.L.ι) (jM' : W'.P.D.toPre.P.L.ι) (jL : W.P.U.LG.L.ι)
          (jL' : W'.P.U.LG.L.ι),
          ⊤ ≤ (v ≫ (W.P.U.gt n).pG.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) →
          ⊤ ≤ (v ≫ ψn ≫ (W'.P.U.gt n).pG.left) ⁻¹ᵁ
            (LB.div (a.D₀.P.L.pull W'.φ) W'.P.D.toPre.P.L).U (fun _ => j₀, jM') →
          ⊤ ≤ (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) ⁻¹ᵁ
            (LB.div (W'.P.U.LG.L.pull ψ.hom.left) W.P.U.LG.L).U (fun _ => jL', jL) →
          valR (v ≫ (W.P.U.gt n).pG.left) _ (W.w.s (fun _ => j₀, jM)).val *
              valR v _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL)).val =
            valR (v ≫ ψn ≫ (W'.P.U.gt n).pG.left) _ (W'.w.s (fun _ => j₀, jM')).val *
              valR (v ≫ ψn) _ ((W'.P.U.w n).s (fun _ => jM', fun _ => jL')).val *
              valR (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) _ (wL.s (fun _ => jL', jL)).val

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen

variable {V : Type} [CommRing V] [IsDomain V]

theorem isLocalization_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.general_b_fact_further.goal1 .. | (apply Bl.general_b_fact_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_further.goal1 <;> assumption)

theorem isOpenImmersion_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsOpenImmersion (spMap (algebraMap V (FractionRing V))) := by
  have := isLocalization_frac hϖ
  let e := IsLocalization.algEquiv (Submonoid.powers ϖ) (Localization.Away ϖ) (FractionRing V)
  have he : algebraMap V (FractionRing V) =
      (e : Localization.Away ϖ →+* FractionRing V).comp (algebraMap V (Localization.Away ϖ)) :=
    RingHom.ext fun x => (e.commutes x).symm
  have : IsIso (CommRingCat.ofHom (e : Localization.Away ϖ →+* FractionRing V)) :=
    ⟨⟨CommRingCat.ofHom (e.symm : FractionRing V →+* Localization.Away ϖ), by ext x; simp, by ext x; simp⟩⟩
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem opensRange_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    haveI := isOpenImmersion_frac hϖ
    (spMap (algebraMap V (FractionRing V))).opensRange =
      (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) := by
  have := isLocalization_frac hϖ
  rw [basicOpen_eq_of_affine]
  ext1
  exact PrimeSpectrum.localization_away_comap_range (FractionRing V) ϖ

theorem eq_zero_of_mul {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p] {r : V} (hr : r ≠ 0) (f : Γ(X, ⊤))
    (h : p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv r) * f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x hx => ?_
  show X.presheaf.germ ⊤ x hx f = X.presheaf.germ ⊤ x hx 0
  set r' := (Scheme.ΓSpecIso (CommRingCat.of V)).inv r with hr'def
  have hr' : r' ≠ 0 := by
    intro h0
    apply hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom h0
    rwa [hr'def, Iso.inv_hom_id_apply, map_zero] at this
  set g := (Sp V).presheaf.germ ⊤ (p.base x) trivial r' with hgdef
  have hg : g ≠ 0 := fun h0 =>
    hr' (germ_injective_of_isIntegral (Sp V) (U := ⊤) (p.base x) trivial (h0.trans (map_zero _).symm))
  let := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (X.presheaf.stalk x) := Flat.stalkMap p x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hg)
  have key : (p.stalkMap x).hom g * X.presheaf.germ ⊤ x hx f = 0 := by
    have h1 : (p.stalkMap x).hom g = X.presheaf.germ ⊤ x hx (p.appTop r') :=
      Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial r'
    rw [h1]
    show X.presheaf.germ ⊤ x hx (p.appTop r') * X.presheaf.germ ⊤ x hx f = 0
    rw [← map_mul, h, map_zero]
  have h2 : g • X.presheaf.germ ⊤ x hx f = g • 0 := by
    rw [smul_zero, Algebra.smul_def]
    exact key
  rw [hreg h2, map_zero]

theorem restrict_basicOpen_injective {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (hs : ∀ f : Γ(X, ⊤), s * f = 0 → f = 0) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op) := by
  have := isLocalization_basicOpen_of_qcqs (X := X) (U := ⊤) (by simpa using isCompact_univ)
    (by simpa using isQuasiSeparated_univ) s
  have hM : Submonoid.powers s ≤ nonZeroDivisors Γ(X, ⊤) :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_iff_right.2 fun f hf => hs f (by rwa [mul_comm] at hf))
  exact IsLocalization.injective (Γ(X, X.basicOpen s)) hM

theorem appTop_fst_injective [IsDiscreteValuationRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p]
    [QuasiCompact p] [QuasiSeparated p] :
    haveI := isOpenImmersion_frac (IsDiscreteValuationRing.exists_irreducible V).choose_spec
    Function.Injective (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  haveI := isOpenImmersion_frac hϖ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  set s := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) with hs
  have hrange : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ = X.basicOpen s := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackFst, opensRange_frac hϖ,
      Scheme.preimage_basicOpen_top]
  have hfac : (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop =
      X.presheaf.map (homOfLE le_top : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ ⟶ ⊤).op ≫
        ((pullback.fst p (spMap (algebraMap V (FractionRing V)))).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE _
  have hinj := restrict_basicOpen_injective s (fun f hf => eq_zero_of_mul p hϖ.ne_zero f hf)
  have hW : ∀ (W : X.Opens), W = X.basicOpen s →
      Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
    rintro W rfl
    exact hinj
  rw [hfac]
  intro a b hab
  simp only [CategoryTheory.comp_apply] at hab
  exact hW _ hrange ((ConcreteCategory.bijective_of_isIso _).1 hab)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
end
end
