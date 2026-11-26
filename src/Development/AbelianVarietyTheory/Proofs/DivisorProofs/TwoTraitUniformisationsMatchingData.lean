module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.TInj

theorem torusHomOf_comp' {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem torusHomOf_id' {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem iso_lin_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  intro R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ a ha
  have ha' : IsMonHom a.inv := inferInstance
  obtain ⟨b, hb, hbO⟩ := exists_abelian_hom R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨b', hb', hb'O⟩ := exists_abelian_hom R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  obtain ⟨h, hh⟩ := unifPre_hom_character_const R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨h', hh'⟩ := unifPre_hom_character_const R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  have oComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) c c',
      Over₀ Ua Ub f c → Over₀ Ub Ua g c' → Over₀ Ua Ua (f ≫ g) (c ≫ c') := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g c c' hf hg e
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg e, ← Category.assoc, hf e, Category.assoc]
  have tComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) k k',
      OnTorus Ua Ub f k → OnTorus Ub Ua g k' → OnTorus Ua Ua (f ≫ g) (fun χ => k (k' χ)) := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g k k' hf hg e
    obtain ⟨t, ht, hi⟩ := hf e
    obtain ⟨s, hs, hj⟩ := hg e
    refine ⟨t ≫ s, torusHomOf_comp' ht hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]
  have oId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), Over₀ Ua Ua (𝟙 Ga) (𝟙 _) := by
    intro Da Aa Ga _ _ Ua e
    simp
  have tId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), OnTorus Ua Ua (𝟙 Ga) (fun χ => χ) := by
    intro Da Aa Ga _ _ Ua e
    exact ⟨𝟙 _, torusHomOf_id' _, by simp⟩
  have u₁ := over₀_onTorus_unique R J hR D₁ D₁ A₁ A₁ G₁ G₁ U₁ U₁ (𝟙 G₁)
  have u₂ := over₀_onTorus_unique R J hR D₂ D₂ A₂ A₂ G₂ G₂ U₂ U₂ (𝟙 G₂)
  have bb : b ≫ b' = 𝟙 _ := u₁.1 _ _ (a.hom_inv_id ▸ oComp U₁ U₂ a.hom a.inv b b' hbO hb'O) (oId U₁)
  have bb' : b' ≫ b = 𝟙 _ := u₂.1 _ _ (a.inv_hom_id ▸ oComp U₂ U₁ a.inv a.hom b' b hb'O hbO) (oId U₂)
  have hh₁ : (fun χ => h (h' χ)) = fun χ => χ :=
    u₁.2 _ _ (a.hom_inv_id ▸ tComp U₁ U₂ a.hom a.inv h h' hh hh') (tId U₁)
  have hh₂ : (fun χ => h' (h χ)) = fun χ => χ :=
    u₂.2 _ _ (a.inv_hom_id ▸ tComp U₂ U₁ a.inv a.hom h' h hh' hh) (tId U₂)
  let hE : D₂.toPre.X ≃+ D₁.toPre.X :=
    { toFun := h, invFun := h', left_inv := fun χ => congrFun hh₂ χ, right_inv := fun χ => congrFun hh₁ χ,
      map_add' := h.map_add }
  have hL : Lin U₁ U₂ a.hom b hE.toAddMonoidHom := ⟨ha, hb, hbO, hh⟩
  exact ⟨b, hE, ⟨b', bb, bb'⟩, hL, coord_of_lin R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom b _ hL⟩

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupIso_abelianPart_character_isos : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  first | exact @GlobalTheory.TInj.iso_lin_coord | exact GlobalTheory.TInj.iso_lin_coord | (intros; apply GlobalTheory.TInj.iso_lin_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qImg_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  intro V _ _ _ J hJ D₁ D₂ b φ F _ _ _ hM k p p' hA
  obtain ⟨hmon, -, -, hnrm, hlast⟩ := hM
  obtain ⟨hex, hadd, -⟩ := GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom hmon hnrm F
  choose α hα hαu using hex
  let f : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' α fun x y =>
    (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1
      (hadd x y (x + y) (α x) (α y) (α (x + y)) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hα x) (hα y) (hα _))
  obtain ⟨h₁, hn₁, hi₁⟩ := p.eq
  obtain ⟨h₂, hn₂, hi₂⟩ := p'.eq
  obtain ⟨g', hg'A, hg'I⟩ := hlast p.y h₁ hi₁
  have e₁ : h₁ = k • p.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₁
  have e₂ : h₂ = k • p'.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₂
  have ep : p'.g = f p.g := hαu p.g p'.g hA
  have eg : g' = f h₁ := hαu h₁ g' hg'A
  have : g' = h₂ := by rw [eg, e₁, map_nsmul, ← ep, e₂]
  rw [← this] at hi₂
  exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws V J hJ D₂ F p'.y (φ p.y) g' hi₂ hg'I

end GlobalTheory.TInj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPairImage_latticePart_eq_of_match : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  first | exact @GlobalTheory.TInj.qImg_lattice | exact GlobalTheory.TInj.qImg_lattice | (intros; apply GlobalTheory.TInj.qImg_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisedGroupsSameSiegelFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisedGroupsSameSiegelFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem exists_iso_of_overPt : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing R) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (a : G₁ ≅ G₂) (cA : A₁.A ≅ A₂.A), IsMonHom a.hom ∧ IsMonHom cA.hom ∧ Gen₀ U₁ U₂ a.hom cA.hom ∧ cA.hom.left ≫ α₂ = α₁ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) := by
  intro X g n B _ ζ sX c R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hp₁, β₁, hsq₁, hL₁⟩ := hO₁
  obtain ⟨hp₂, β₂, hsq₂, hL₂⟩ := hO₂
  obtain ⟨cA, hcA, hcα⟩ := grpPullback_iso hp₁ hp₂
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  haveI := hcA
  let e : (Over.pullback (jK R)).obj G₁ ≅ (Over.pullback (jK R)).obj G₂ := U₁.gen ≪≫ cA ≪≫ U₂.gen.symm
  haveI : IsMonHom e.hom := by
    show IsMonHom (U₁.gen.hom ≫ cA.hom ≫ U₂.gen.inv)
    infer_instance
  obtain ⟨a, ⟨ha, hae⟩, -⟩ :=
    GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁ G₂ hG₁ hG₂ e
  refine ⟨a, cA, ha, hcA, ?_, hcα, ?_⟩
  · show (Over.pullback (jK R)).map a.hom ≫ U₂.gen.hom = U₁.gen.hom ≫ cA.hom
    rw [show (Over.pullback (jK R)).map a.hom = e.hom from hae]
    simp [e]
  · set β := (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left with hβdef
    have hβ : β ≫ β₂ = β₁ := by
      have h1 : (β ≫ β₂) ≫ (fst c.A c.A).left = β₁ ≫ (fst c.A c.A).left := by
        rw [Category.assoc, hsq₂.1, hsq₁.1, ← Category.assoc, hβdef, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, hcα]
      have h2 : (β ≫ β₂) ≫ (snd c.A c.A).left = β₁ ≫ (snd c.A c.A).left := by
        rw [Category.assoc, hsq₂.2, hsq₁.2, ← Category.assoc, hβdef, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, hcα]
      simp only [Over.fst_left, Over.snd_left] at h1 h2
      exact pullback.hom_ext h1 h2
    have iL₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb A₁.isLB _ _
    have iL₂ : ((abelian₂ A₂.A A₂.L).pull β).IsLB := pull_isLB (LB.isLB_linComb A₂.isLB _ _) _
    have iP₁ : (c.P.pull β₁).IsLB := pull_isLB c.isLB _
    have iP₂ : ((c.P.pull β₂).pull β).IsLB := pull_isLB (pull_isLB c.isLB _) _
    have h₃ : LBIso ((abelian₂ A₂.A A₂.L).pull β) ((c.P.pull β₂).pull β) :=
      LBIso.chartPull (chartPullPull _ β) (chartPullPull _ β) hL₂
    exact hL₁.trans iL₁ iP₁ iL₂ ((GlobalTheory.ClosedPol.lbIso_pull_comp c.isLB β₂ β β₁ hβ).trans iP₁ iP₂ iL₂ h₃.symm)

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisedGroupsSameSiegelFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_uniformisedGroups_same_siegelFibre : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing R) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (a : G₁ ≅ G₂) (cA : A₁.A ≅ A₂.A), IsMonHom a.hom ∧ IsMonHom cA.hom ∧ Gen₀ U₁ U₂ a.hom cA.hom ∧ cA.hom.left ≫ α₂ = α₁ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) := by
  first | exact @GlobalTheory.TInj.exists_iso_of_overPt | exact GlobalTheory.TInj.exists_iso_of_overPt | (intros; apply GlobalTheory.TInj.exists_iso_of_overPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

noncomputable section

namespace GlobalTheory.TInj

theorem lbIso_cube_of_lam {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (f : G ⟶ G')
    (H : LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ f) (snd G G ≫ f) : G2 G ⟶ G2 G').left)) :
    LBIso (cubeLB G' ![fst G G ≫ f, snd G G ≫ f] L') (cubeLB G ![fst G G ≫ 𝟙 G, snd G G ≫ 𝟙 G] L) := by
  have hΛ' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  have e₁ : cubeCls G (x2 G) (cls L hL) = CechPic.pull (lift (fst G G ≫ f) (snd G G ≫ f) : G2 G ⟶ G2 G').left
      (cubeCls G' (x2 G') (cls L' hL')) :=
    (cls_cubeLB G _ hL).symm.trans (((cls_eq_iff _ (pull_isLB hΛ' _)).2 H).trans
      ((cls_pull hΛ' _ _).trans (congrArg _ (cls_cubeLB G' _ hL'))))
  rw [pull_cubeCls G' _ ![fst G G ≫ f, snd G G ≫ f] _ (fun i => by fin_cases i <;> simp [x2])] at e₁
  refine (cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G' _ hL').trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  rw [← e₁]
  simp only [Category.comp_id]
  rfl


set_option maxHeartbeats 1000000 in
theorem two_unif_match : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (D₁ : DegData V (maximalIdeal V)) (A₁ : PolAV (Sp (FractionRing V))) (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (D₂ : DegData V (maximalIdeal V)) (A₂ : PolAV (Sp (FractionRing V))) (G₂ : Over (Sp V)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing V) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ ∀ k : ℕ, 1 ≤ k → ∀ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) k) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) k) (x₁ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₁.A) (x₂ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₂.A), QkToAkU U₁.toUnifPre (AlgebraicClosure (FractionRing V)) k p₁ x₁ → QkToAkU U₂.toUnifPre (AlgebraicClosure (FractionRing V)) k p₂ x₂ → x₁.left ≫ α₁ = x₂.left ≫ α₂ → QImg b φ p₁ p₂ := by
  intro X g n B _ ζ sX c V _ _ _ _ hc D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨a, cA, ha, hcA, gen, hα, hlbA⟩ := GlobalTheory.T.exists_iso_uniformisedGroups_same_siegelFibre c V (maximalIdeal V) hA D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂
    U₂.toUnifPre hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  obtain ⟨b, h, hbi, lin, coord⟩ := GlobalTheory.T.uniformisedGroupIso_abelianPart_character_isos V (maximalIdeal V) hA D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre a ha
  have hb : IsMonHom b := lin.2.1
  have hov : Over₀ U₁.toUnifPre U₂.toUnifPre a.hom b := lin.2.2.1
  have hlbG := GlobalTheory.T.mumfordBundleIso_genericFibre_extends_uniformisedGroups V (maximalIdeal V) hA D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre hG₁ a.hom cA.hom ha hcA
    gen hlbA
  have hlbB := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart V hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a.hom a.hom b b ha ha hb hb hov hov hlbG
  have hnrm : ∀ χ, ∃ u : LB.Gen (CmpLB D₁.toPre D₂.toPre b (h.toAddMonoidHom χ) χ), Nrm u :=
    fun χ => (coord χ).imp fun _ => And.left
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  have key := GlobalTheory.Mum.Two.KeyDvr.main V hc ϖ hϖ (AlgebraicClosure (FractionRing V)) v hv D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂
    U₁ U₂ a.hom cA.hom b h.toAddMonoidHom hcA gen lin coord h.injective
  obtain ⟨E, eG, eA, -, eh, -⟩ :=
    (GlobalTheory.IntEnd.exists_nsmul_and_neg GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D₁ A₁ G₁ hG₁ U₁).1 1
  have H₁ : LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L)
      (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E.aG] U₁.LG.L) := by
    rw [eG, pow_one, Category.comp_id, Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U₁.LG.isLB _ _)
  have H₂ : LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ cA.hom, snd A₁.A A₁.A ≫ cA.hom] A₂.L)
      (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) := by
    rw [eA, pow_one]
    exact lbIso_cube_of_lam A₁.isLB A₂.isLB cA.hom hlbA
  obtain ⟨φ', hφ', hhφ'⟩ := GlobalTheory.Mum.Two.periods_of_key V (maximalIdeal V) hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a.hom
    cA.hom b h.toAddMonoidHom hcA gen lin coord E E H₁ H₂ _ key
  have hφe : ∀ y₀, φ' y₀ = h.symm y₀ := fun y₀ => h.injective (by
    show h (φ' y₀) = h (h.symm y₀)
    rw [h.apply_symm_apply]
    exact (hhφ' y₀).trans (by rw [eh, one_smul]))
  have hM : Match D₁.toPre D₂.toPre b h.symm (AlgebraicClosure (FractionRing V)) := by
    refine ⟨hb, hbi, hlbB, hnrm, fun y₀ g₀ hy => ?_⟩
    obtain ⟨g', h1, h2⟩ := hφ' y₀ g₀ hy
    exact ⟨g', h1, hφe y₀ ▸ h2⟩
  refine ⟨b, h.symm, hM, fun k hk p₁ p₂ x₁ x₂ hq₁ hq₂ hx => ?_⟩
  obtain ⟨g', hg', -⟩ :=
    (GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b h.toAddMonoidHom hb hnrm (AlgebraicClosure (FractionRing V))).1 p₁.g
  obtain ⟨p', rfl, hp'⟩ := key k hk p₁ x₁ hq₁ g' hg'
  have hxx : x₁ ≫ cA.hom = x₂ := by
    apply Over.OverMorphism.ext
    apply hO₂.1.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hα, hx]
    · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Over.w]
  refine ⟨p', GlobalTheory.T.torsionPairImage_latticePart_eq_of_match V (maximalIdeal V) hA D₁ D₂ b h.symm _ hM k p₁ p' hg', hg',
    (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv V (maximalIdeal V) hA D₂ A₂ G₂ U₂ hG₂ _ k hk).2 p' p₂ x₂ (hxx ▸ hp') hq₂⟩

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_trait_uniformisations_matching_data : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (D₁ : DegData V (maximalIdeal V)) (A₁ : PolAV (Sp (FractionRing V))) (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (D₂ : DegData V (maximalIdeal V)) (A₂ : PolAV (Sp (FractionRing V))) (G₂ : Over (Sp V)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing V) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ ∀ k : ℕ, 1 ≤ k → ∀ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) k) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) k) (x₁ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₁.A) (x₂ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₂.A), QkToAkU U₁.toUnifPre (AlgebraicClosure (FractionRing V)) k p₁ x₁ → QkToAkU U₂.toUnifPre (AlgebraicClosure (FractionRing V)) k p₂ x₂ → x₁.left ≫ α₁ = x₂.left ≫ α₂ → QImg b φ p₁ p₂ := by
  first | exact @GlobalTheory.TInj.two_unif_match | exact GlobalTheory.TInj.two_unif_match | (intros; apply GlobalTheory.TInj.two_unif_match <;> assumption)
end
