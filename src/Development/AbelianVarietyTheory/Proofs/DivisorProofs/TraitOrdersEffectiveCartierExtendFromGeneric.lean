module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerTraitLatticeEquivLocalExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrWithProportionalValuations

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelOpenAbelianEighthPowerWithBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.FieldPt

theorem of_factor {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (V : M.Z.Opens) (v : V.toScheme ⟶ F.X) {T₀ : Scheme.{0}} (ξ : T₀ ⟶ V.toScheme)
    (cO : SiegPre g n ζ ((ξ ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (ξ ≫ V.ι)).obj FinalForm.G ⟶ cO.A))
    (hpbO : SiegPB cO F.univ (ξ ≫ v)) (hmonO : ∀ a, IsMonHom (prO a))
    (hunivO : ∀ (T' : Over T₀) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (ξ ≫ V.ι)).obj FinalForm.G,
      ∀ a, x ≫ prO a = y a)
    (hLO : LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι)))
      (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)))
    (hmatO : ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (ξ ≫ V.ι)).map f))
    {K : Type} [Field K] (t : Sp K ⟶ V.toScheme) (t' : Sp K ⟶ T₀) (ht : t' ≫ ξ = t)
    (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left) (hB : IsGrpPullback B FinalForm.G (t ≫ V.ι) φB) :
    ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧
      (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧
      (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧
      ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left →
        MatEnd pr' a b fB := by
  subst ht
  have hB' : IsGrpPullback B FinalForm.G (t' ≫ (ξ ≫ V.ι)) φB := hB.congr (Category.assoc _ _ _) rfl
  have hφ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (ξ ≫ V.ι) t' hB'
  have hφ'f : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) = φB :=
    pullback.lift_fst _ _ _
  have hφ's : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
      B.hom ≫ t' := pullback.lift_snd _ _ _
  generalize pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) = φ' at hφ hφ'f hφ's
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) _ (Sp K)
    ((ξ ≫ v) ≫ F.s) (((t' ≫ ξ) ≫ v) ≫ F.s) t' rfl (by rw [hid, Category.comp_id]; simp only [Category.assoc])).1 cO
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpbO hc'
  rw [← Category.assoc] at hcomp
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.GrpPullPow.pr_pull prO hφ hχ hmonO hunivO
  refine ⟨c', pr', hcomp, hmon', huniv', ?_, ?_⟩
  · intro L' hL' hiso
    have hL := FinalForm.L.isLB
    have e1 : LBIso (FinalForm.L.L.pull φB) ((FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))).pull φ') := by
      rw [← hφ'f]
      exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame FinalForm.L.L _ _ _ φ' fun _ => rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))) φ' φ' rfl)
        ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso _, ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen (pull_isLB hL _)⟩
    have e2 := LBIso.trans hL' (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hiso e1
    exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull cO.P c'.P _ L' prO pr' W cO.isLB c'.isLB (pull_isLB hL _) hL' hsq hP hpr'
      e2 hLO
  · intro a b f fB hf hfB
    refine GlobalTheory.MatEndPull.matEnd_pull prO pr' a b _ fB hφ hχ hpr' ?_ (hmatO a b f hf)
    apply pullback.hom_ext
    · have e : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.fst FinalForm.G.hom (ξ ≫ V.ι) ≫ f.left := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, hφ'f, e, ← Category.assoc, hφ'f, hfB]
    · have w1 : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.snd FinalForm.G.hom (ξ ≫ V.ι) := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, hφ's, w1, hφ's, ← Category.assoc, Over.w fB]

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv K _ t B _ φB hB
  obtain ⟨cO, prO, hpbO, hmonO, hunivO, hLO, hmatO⟩ := GlobalTheory.T.eighth_power_universal_object_at_model_stalk g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
    (t (IsLocalRing.closedPoint K))
  exact of_factor F W FinalForm pr V v _ cO prO hpbO hmonO hunivO hLO hmatO t _
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t) B φB hB

end GlobalTheory.Poinc.Eq8.FieldPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullbStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  first | exact @GlobalTheory.Poinc.Eq8.FieldPt.main | exact GlobalTheory.Poinc.Eq8.FieldPt.main | (intros; apply GlobalTheory.Poinc.Eq8.FieldPt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelOpenAbelianEighthPowerWithBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.SharpOnV

theorem lAb : ∀ {X : Scheme.{0}} (G : Over X) (V : X.Opens), (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ V.toScheme), IsProper (pullback.snd G.hom (t ≫ V.ι))) → (V : Set X) ⊆ abLocus G := by
  intro X G V h s hs K _ _ t ⟨p, hp⟩
  have hr : Set.range t.base ⊆ (V : Set X) := by
    rintro _ ⟨q, rfl⟩
    have : q = p := Subsingleton.elim _ _
    subst this
    rw [hp]; exact hs
  let t' := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
  have ht : t' ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have := h K t'
  rwa [ht] at this

theorem lGen : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ X) (gm : G'.left ⟶ G.left), IsGrpPullback G' G ξ gm → IsGrpPullback A'.A G (jK R ≫ ξ) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) := by
  intro X G _ R _ _ _ G' _ _ D' A' U' ξ gm hgm
  exact ((GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G' U'.gen U'.gen_hom).comp hgm).congr rfl (Category.assoc _ _ _)

theorem lLB : ∀ {X : Scheme.{0}} (L : LB X) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ X), L.IsLB → LBIso U'.LG.L (L.pull gm) → LBIso A'.L (L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm)) := by
  intro X L R _ _ _ G' _ _ D' A' U' gm hL hLB
  have hA := A'.isLB
  have ext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK R))) := U'.ext
  have H1 := GlobalTheory.ThetaAffineGlue.lbIso_comp (pull_isLB hA _) U'.LG.isLB hL ext hLB
  have H2 := GlobalTheory.ThetaAffineGlue.lbIso_pull H1 U'.gen.inv.left
  have hP : (A'.L.pull U'.gen.hom.left).IsLB := pull_isLB hA _
  have refl : LBIso (A'.L.pull U'.gen.hom.left) (A'.L.pull U'.gen.hom.left) :=
    LBIso.trans hP (pull_isLB hP _) hP (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP))
  have H4 := GlobalTheory.ThetaAffineGlue.lbIso_pull refl U'.gen.inv.left
  have e : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  rw [e] at H4
  have H3 : LBIso A'.L ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) :=
    LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) (LBIso.symm H4)
  exact LBIso.trans hA (pull_isLB hP _) (pull_isLB hL _) H3 H2

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → (V : Set M.Z) ⊆ abLocus FinalForm.G ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ V.toScheme, ξ₀ ≫ V.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ v) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  have hK := GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  refine ⟨lAb FinalForm.G V fun K _ _ t => ?_, ?_⟩
  · obtain ⟨c', pr', -, -, huniv, -, -⟩ := hK K t ((Over.pullback (t ≫ V.ι)).obj FinalForm.G) (pullback.fst _ _)
      (isGrpPullback_pullback _ _)
    exact GlobalTheory.T.isProper_eighth_fibre_power_over pr' huniv c'.ab.proper
  · intro R _ _ _ hB G' _ _ hsemi D' A' U' ξ gm hgm hLB ξ₀ hξ₀
    have hpb : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ V.ι) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) :=
      (lGen U' ξ gm hgm).congr hξ₀.symm rfl
    have hL := lLB FinalForm.L.L U' gm FinalForm.L.isLB hLB
    obtain ⟨c', pr', hSP, hmon, huniv, hlb, hmat⟩ := hK (FractionRing R) ξ₀ A'.A _ hpb
    refine ⟨c', pr', ⟨hSP, hmon, huniv, hlb A'.L A'.isLB hL⟩, fun a b f f' hf hff' => ?_⟩
    have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
      pullback.lift_fst _ _ _
    refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, hmat a b f _ hf ?_, by simp⟩
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hgi, reassoc_of% hmapf, hff']

end GlobalTheory.Poinc.Eq8.SharpOnV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelOpenAbelianEighthPowerWithBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → (V : Set M.Z) ⊆ abLocus FinalForm.G ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ V.toScheme, ξ₀ ≫ V.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ v) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  first | exact @GlobalTheory.Poinc.Eq8.SharpOnV.main | exact GlobalTheory.Poinc.Eq8.SharpOnV.main | (intros; apply GlobalTheory.Poinc.Eq8.SharpOnV.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupEqEighthPowerLatticeOverTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupEqEighthPowerLatticeOverTrait
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PeriodsEighth

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ M.Z) (D : DegPre R) (m : Fin 8 → Fin 8 → (D.X →+ D.X)) (T : Trait F) (ψ : R →+* T.V), ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∀ (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Sp (FractionRing T.V))) (U' : Unif (maximalIdeal T.V) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ι : D.X ≃+ D'.toPre.X), IsSemiAbelian G' → IsGrpPullback G' FinalForm.G (spMap ψ ≫ ξ) gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → CoordMap D D'.toPre ψ ι.toAddMonoidHom → (∀ a b, ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ (f a b).left ∧ ∀ m', EndChar U' f' m' → ∀ y, ι (m a b y) = m' (ι y)) → ∃ ρT : D.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ _ S ρ u c pr hsh M U₀ EE FinalForm hov V v hv f hf R _ _ _ ξ D m T ψ hT G' _ _ D' A' U'
    gm ι hG hpb hL hco hm
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  obtain ⟨ξ₀, h1, h2⟩ := hT
  obtain ⟨c', pr', hs', hmat⟩ := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hsh M U₀ EE FinalForm hov V v hv).2 T.V hBV G' hG
    D' A' U' (spMap ψ ≫ ξ) gm hpb hL ξ₀ h1
  have e0 : spMap (RingHom.id (FractionRing T.V)) ≫ T.y = ξ₀ ≫ v := by
    have : spMap (RingHom.id (FractionRing T.V)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, ← h2, Category.comp_id]
  have key : ∀ y₀ : Sp (FractionRing T.V) ⟶ F.X, spMap (RingHom.id (FractionRing T.V)) ≫ T.y = y₀ →
      ∀ c'' pr'', SharpBy F W A' y₀ c'' pr'' → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (T.ϖ ^ (qW W T.β (e y)).toNat)) ∧
      ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f →
        MatEnd pr'' a b f₁ → (Over.pullback (jK T.V)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m →
        ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro _ rfl c'' pr'' hs''
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n o ζ F W hW T T.V hBV inferInstance G' hG D' A' U' (RingHom.id _) (RingHom.id _)
      inferInstance (fun _ => rfl) c'' pr'' hs''
  obtain ⟨e, he1, he2⟩ := key _ e0 c' pr' hs'
  refine ⟨ι.trans e, fun y r hr => ?_, fun a b y => ?_⟩
  · obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D'.toPre (ι y)).2
      (GlobalTheory.PeriodFormCompare.psiIn_top D' _)
    obtain ⟨h0, ha⟩ := he1 _ _ hr'
    exact ⟨h0, (hco y r r' hr hr').trans ha⟩
  · obtain ⟨f', hfm, hf', hmm⟩ := hm a b
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom T.V hBV G' hG D' A' U' f' hfm
    obtain ⟨f₁, hf₁, hgen⟩ := hmat a b (f a b) f' (hf a b) hf'
    have := he2 a b f' f₁ m' hfm hf₁ hgen hm' (ι y)
    rw [← hmm m' hm' y] at this
    exact this

end GlobalTheory.Poinc.Eq8.PeriodsEighth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupEqEighthPowerLatticeOverTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterGroup_eq_eighthPower_lattice_over_trait : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ M.Z) (D : DegPre R) (m : Fin 8 → Fin 8 → (D.X →+ D.X)) (T : Trait F) (ψ : R →+* T.V), ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∀ (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Sp (FractionRing T.V))) (U' : Unif (maximalIdeal T.V) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ι : D.X ≃+ D'.toPre.X), IsSemiAbelian G' → IsGrpPullback G' FinalForm.G (spMap ψ ≫ ξ) gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → CoordMap D D'.toPre ψ ι.toAddMonoidHom → (∀ a b, ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ (f a b).left ∧ ∀ m', EndChar U' f' m' → ∀ y, ι (m a b y) = m' (ι y)) → ∃ ρT : D.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  first | exact @GlobalTheory.Poinc.Eq8.PeriodsEighth.main | exact GlobalTheory.Poinc.Eq8.PeriodsEighth.main | (intros; apply GlobalTheory.Poinc.Eq8.PeriodsEighth.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLoc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoTransOfSelfPt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LBIsoEnd

def SelfPt {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : L.ι), f y ∈ L.U i → gm f y (L.U i ⊓ L.U i) (L.g i i) = 1

theorem selfPt_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : SelfPt L :=
  fun _ f y _ hi => gm_self hL f y hi

theorem selfPt_of_lbIso {X : Scheme.{0}} {B P : LB X} (hB : B.IsLB) (H : LBIso B P) : SelfPt P := by
  intro Y f y k hk
  obtain ⟨w, hw⟩ := H
  obtain ⟨i, hi⟩ := exists_chart hB (f y)
  have hm : f y ∈ P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i) := ⟨⟨hk, hi⟩, hk, hi⟩
  have e := congrArg (gm f y (P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i))) (hw (k, i) (k, i))
  have e' := (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B P f y (k, i) (k, i) hm) (gm_res f y _ hm _))))
  rw [gm_self hB f y hi, inv_one, _root_.mul_one] at e'
  exact _root_.mul_eq_right.1 e'.symm

section Tri

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL : SelfPt L) (hL'' : SelfPt L'') {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [hL Y ((f ≫ F') ≫ F) y j hj] at a
  rw [hL'' Y f y k hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL : SelfPt L) (hL'' : SelfPt L'') :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1 h₂.2.1
          h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Tri

theorem lbIso_trans_of_selfPt {X : Scheme.{0}} {A B C : LB X} (hA : SelfPt A) (hB : B.IsLB) (hC : SelfPt C)
    (H : LBIso A B) (H' : LBIso B C) : LBIso A C := by
  obtain ⟨w', h'⟩ := H.chartPull (chartPullId A) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w, h⟩ := H'.chartPull (chartPullId B) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull C (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w'', T⟩ := exists_comp' hB w w' ((isGen_iff w).1 h) ((isGen_iff w').1 h') hC hA
  exact LBIso.chartPull (chartPullId A) (chartPullUnpull C _ (Category.id_comp _))
    ⟨w'', (isGen_iff w'').2 (T.pgen_comp hB ((isGen_iff w).1 h) ((isGen_iff w').1 h'))⟩

theorem lbIso_trans_end : ∀ (X : Scheme.{0}) (A B P : LB X), A.IsLB → B.IsLB → LBIso A B → LBIso P B → LBIso A P :=
  fun _ _ _ _ hA hB H H' =>
    lbIso_trans_of_selfPt (selfPt_of_isLB hA) hB (selfPt_of_lbIso hB H'.symm) H H'.symm

end GlobalTheory.LBIsoEnd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLoc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullComplete

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  intro Z G₀ _ _ hG₀ L R _ _ _ hR ξ _ D A U hL hψ V _ _ _ hV ψ hloc hgen
  have hG : IsSemiAbelian ((Over.pullback ξ).obj G₀) := IsSemiAbelian.pullback ξ G₀ hG₀
  have hpb := isGrpPullback_pullback G₀ ξ
  have hab : ξ ⁻¹' abLocus G₀ = abLocus ((Over.pullback ξ).obj G₀) :=
    Set.ext fun x => abLocus_pullback abLocusOne hG₀ hpb.1 x
  let W : (Sp R).Opens := ⟨ξ ⁻¹' abLocus G₀, by rw [hab]; exact GlobalTheory.AbLocusOpen.isOpen_abLocus_local _ hG⟩
  have hz : (jK V).base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hW : spMap ψ (genericPoint (Sp V)) ∈ W := by
    show ξ (spMap ψ (genericPoint (Sp V))) ∈ abLocus G₀
    rw [← hz]
    have := hgen (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    exact this
  let G := (Over.pullback ξ).obj G₀
  let G' := (Over.pullback (specOf ψ)).obj G
  have hbc : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 G'); infer_instance
  obtain ⟨D', A', hD, U', hP⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U V hV.1 ψ hloc W hψ hW
    G' (Iso.refl G') hbc
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback (specOf ψ) G hG
  let β : G'.left ⟶ G.left := (Iso.refl G').hom.left ≫ pullback.fst G.hom (specOf ψ)
  obtain ⟨hLB, hC, hE⟩ := GlobalTheory.Poinc.Eq8.PullUnif.main R hR G hG D A U V hV G' hG' D' A' U' ψ β hloc (Iso.refl G')
    hbc rfl hD hP
  let gm : G'.left ⟶ G₀.left := β ≫ pullback.fst G₀.hom ξ
  have hβ : IsGrpPullback G' G (specOf ψ) β :=
    ((isGrpPullback_of_iso (Iso.refl G')).comp (isGrpPullback_pullback G (specOf ψ))).congr (Category.id_comp _) rfl
  refine ⟨G', inferInstance, inferInstance, D', A', U', gm, hD.xe.symm, hG', hβ.comp hpb, ?_, hC, ?_⟩
  · exact GlobalTheory.LBIsoEnd.lbIso_trans_end _ _ _ _ U'.LG.isLB (pull_isLB U.LG.isLB β) hLB
      (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL β rfl))
  · intro f hf
    haveI := hf
    have e1 : ((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β =
        β ≫ ((Over.pullback ξ).map f).left := by
      show _ ≫ 𝟙 _ ≫ _ = (𝟙 _ ≫ _) ≫ _
      exact pullback.lift_fst _ _ _
    have e2 : ((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ = pullback.fst G₀.hom ξ ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f), inferInstance, ?_, ?_⟩
    · show _ ≫ β ≫ _ = (β ≫ _) ≫ _
      calc _ = (((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β) ≫ pullback.fst G₀.hom ξ :=
            (Category.assoc _ _ _).symm
        _ = (β ≫ ((Over.pullback ξ).map f).left) ≫ pullback.fst G₀.hom ξ := by rw [e1]
        _ = β ≫ (((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ) := Category.assoc _ _ _
        _ = β ≫ (pullback.fst G₀.hom ξ ≫ f.left) := by rw [e2]
        _ = _ := (Category.assoc _ _ _).symm
    · intro m m' hm hm' y
      exact hE _ _ inferInstance inferInstance e1 m m' hm hm' y

end GlobalTheory.Poinc.Eq8.PullComplete
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLocStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  first | exact @GlobalTheory.Poinc.Eq8.PullComplete.main | exact GlobalTheory.Poinc.Eq8.PullComplete.main | (intros; apply GlobalTheory.Poinc.Eq8.PullComplete.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Periods

theorem one_lattice {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (D : DegData R (maximalIdeal R)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)) (P : ∀ T : Trait F, (R →+* T.V) → Prop)
    (h : ∀ T ψ, P T ψ → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧
      ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y))) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), 1 ≤ c ∧ ∀ T ψ, P T ψ →
      ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  have hc : 0 < W 0 0 := by
    have := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  by_cases hex : ∃ T ψ, P T ψ
  swap
  · push_neg at hex
    exact ⟨PUnit, inferInstance, fun _ => 0, 1, le_rfl, fun T ψ hP => absurd hP (hex T ψ)⟩
  obtain ⟨T₀, ψ₀, hP₀⟩ := hex
  obtain ⟨e₀, -, he₀⟩ := h T₀ ψ₀ hP₀
  have hcoord : ∀ z, ∃ r, PsiCoord D.toPre (e₀.symm (Pi.single 0 z)) r := fun z =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre _).2 (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  choose p hp using hcoord
  refine ⟨T₀.D.toPre.X, inferInstance, p, (W 0 0).toNat, by omega, fun T ψ hP => ?_⟩
  obtain ⟨ρT, hρ, hm⟩ := h T ψ hP
  obtain ⟨π, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT.toAddMonoidHom
    ρT.surjective he₀ hm
  have hsingle : ∀ z, ρT (e₀.symm (Pi.single 0 z)) = Pi.single 0 (π z) := by
    intro z
    funext u
    have := hπ (e₀.symm (Pi.single 0 z)) u
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at this
    rw [this]
    by_cases hu : u = 0
    · subst hu; simp
    · simp [Pi.single_apply, hu]
  have hinj : Function.Injective π := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : ρT (e₀.symm (Pi.single 0 z)) = 0 := by rw [hsingle, hz, Pi.single_zero]
    have h2 : e₀.symm (Pi.single 0 z) = 0 := by simpa using h1
    have h3 : (Pi.single 0 z : Fin 8 → T₀.D.toPre.X) = 0 := by simpa using h2
    simpa using congrFun h3 0
  refine ⟨AddEquiv.ofBijective π ⟨hinj, hπs⟩, fun z => ?_⟩
  obtain ⟨h0, ha⟩ := hρ _ _ (hp z)
  rw [hsingle] at h0 ha
  have hq : qW W T.β (Pi.single 0 (π z)) = W 0 0 * T.β (π z) (π z) := by
    unfold qW
    rw [Finset.sum_eq_single 0 (fun u _ hu => by simp [Pi.single_eq_of_ne hu]) (by simp)]
    rw [Finset.sum_eq_single 0 (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
    simp
  refine ⟨(qW W T.β (Pi.single 0 (π z))).toNat, ?_, ha⟩
  rw [Int.toNat_of_nonneg h0, hq, Int.toNat_of_nonneg hc.le]
  rfl

end GlobalTheory.Poinc.Periods

theorem GlobalTheory.Poinc.Periods.trait_iso : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ M.Z) [IsCommMonObj ((Over.pullback ξ).obj FinalForm.G)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj FinalForm.G)), LBIso U.LG.L (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus FinalForm.G)) → ∀ (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)), (∀ a b, EndChar U ((Over.pullback ξ).map (f a b)) (m a b)) → ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R _ _ _ hB ξ _ D A U hL hP m hm T ψ hl ht
  have hVab := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv).1
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  have hgen : ∀ w, (jK T.V ≫ spMap ψ ≫ ξ) w ∈ abLocus FinalForm.G := by
    obtain ⟨ξ₀, hξ₀, -⟩ := ht
    intro w
    rw [← hξ₀]
    exact hVab (ξ₀ w).2
  obtain ⟨G', _, _, D', A', U', gm, ι, hG', hgm, hLB, hC, hE⟩ :=
    GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus M.Z FinalForm.G FinalForm.semi FinalForm.L.L R hB ξ D A U hL hP T.V hBV ψ hl hgen
  refine GlobalTheory.T.characterGroup_eq_eighthPower_lattice_over_trait g n o ζ F W hW o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R ξ D.toPre m
    T ψ ht G' D' A' U' gm ι hG' hgm hLB hC fun a b => ?_
  obtain ⟨f', hf'm, hf'c, hf'e⟩ := hE (f a b) (hf a b).1
  exact ⟨f', hf'm, hf'c, fun m' hm' => hf'e _ m' (hm a b) hm'⟩

theorem GlobalTheory.Poinc.Periods.main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u hu M U₀ EE FinalForm hO V v hv x
  obtain ⟨c, pr, hs⟩ := (sharpOver_iff F W ρ.P u).1 hu
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  have hB : GlobalTheory.Mum.Base R := ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩
  have hGs : IsSemiAbelian ((Over.pullback ξ).obj FinalForm.G) := IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi
  obtain ⟨hsb, hpr, huniq, hlb⟩ := hs
  choose f hf using matOn_exists o' Ω S ρ M U₀ EE FinalForm hO.ne c.A pr hpr huniq
  have hfm : ∀ a b, IsMonHom ((Over.pullback ξ).map (f a b)) := fun a b => by
    have := (hf a b).1
    infer_instance
  choose m hmc using fun a b => endChar_exists_of_isMonHom R hB _ hGs D A U _ (hfm a b)
  obtain ⟨Λ, _, p, c', hc', hall⟩ := GlobalTheory.Poinc.Periods.one_lattice D W hW m
    (fun T ψ => IsLocalHom ψ ∧ ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x))
    (fun T ψ hT => by
      obtain ⟨hl, ht⟩ := hT
      have e : spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x = spMap ψ ≫ ξ := by
        rw [hξ, ← Category.assoc]
        congr 1
        exact Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      rw [e] at ht
      exact GlobalTheory.Poinc.Periods.trait_iso g n o ζ F W hW o' Ω S ρ u c pr ⟨hsb, hpr, huniq, hlb⟩ M U₀ EE FinalForm hO V v hv f hf R hB ξ
        D A U hL hP m hmc T ψ hl ht)
  exact ⟨R, inferInstance, hRd, hloc, φ, Λ, inferInstance, p, c', hB, isCpl_self _, hc', fun T ψ hl ht => hall T ψ ⟨hl, ht⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_point_lattice_periods_traits : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  first | exact @GlobalTheory.Poinc.Periods.main | exact GlobalTheory.Poinc.Periods.main | (intros; apply GlobalTheory.Poinc.Periods.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitOrdersEffectiveCartierExtendFromGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Extend

theorem pow_exp_eq {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (h : Irreducible ϖ) {a b : ℕ}
    (e : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.dvd) ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.symm.dvd)

theorem form_eq_zero {X I : Type} [AddCommGroup X] (B : LinearMap.BilinForm ℤ X) (hB : ∀ a b, B a b = B b a) (b : I → X)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (h : ∀ i j, B (b i + b j) (b i + b j) = 0) : B = 0 := by
  have h1 : ∀ i j, B (b i) (b i) + 2 * B (b i) (b j) + B (b j) (b j) = 0 := by
    intro i j
    have := h i j
    simp only [map_add (f := _), LinearMap.add_apply] at this
    rw [hB (b j) (b i)] at this
    linarith
  have h2 : ∀ i, B (b i) (b i) = 0 := fun i => by have := h1 i i; linarith
  have h3 : ∀ i j, B (b i) (b j) = 0 := fun i j => by have := h1 i j; have := h2 i; have := h2 j; linarith
  refine LinearMap.ext_on_range hb fun i => LinearMap.ext_on_range hb fun j => ?_
  simpa using h3 i j

theorem evalZ_prop {g n : ℕ} (hn : 2 ≤ n) {F : SFam g n (zetaAway n)} {φ : InvFun ℤ} (hφ : IsPolFan id g φ) (T T' : Trait F)
    (e : T.D.toPre.X ≃+ T'.D.toPre.X) (m s : ℕ) (he : ∀ a b, (m : ℤ) * T'.β (e a) (e b) = s * T.β a b) :
    (m : ℝ) * φ.evalZ T'.β = s * φ.evalZ T.β := by
  have hon := hφ T.D.toPre.X (Trait.finrank_le g n hn F T)
  have hc : toReal T.β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := T.D.toPre.X) :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  have hc' : toReal (pull e.toIntLinearEquiv.toLinearMap T'.β) ∈ psdCone (bar := (id : ℤ → ℤ)) (X := T.D.toPre.X) :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 fun a b => T'.symm _ _) fun x => by
      simpa using T'.mono.nonneg 0 (e x)
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc s s.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal,
    ← hon.homog _ hc' m m.cast_nonneg]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h

theorem idlAlong_ne_bot {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) (h : (jK R ≫ ξ) (closedPoint (FractionRing R)) ∉ J.support) : idlAlong J ξ ≠ ⊥ := by
  intro h0
  have h1 := idlAlong_eq_top_of_notMem_support X J _ _ h
  have eq_map : ∀ {S : Type} [CommRing S] [IsLocalRing S] (χ : Sp S ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1),
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of S)).hom).hom := by
    intro S _ _ χ U hle
    have hx : χ (closedPoint S) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have h2 : idlAlong J (jK R ≫ ξ) = (idlAlong J ξ).map (algebraMap R (FractionRing R)) := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
    have hle' : ⊤ ≤ (jK R ≫ ξ) ⁻¹ᵁ U := fun x _ => hle (show jK R x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map ξ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (jK R ≫ ξ).appLE U ⊤ hle' = ξ.appLE U ⊤ hle ≫ (jK R).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [h0, Ideal.map_bot] at h2
  exact bot_ne_top (h2.symm.trans h1)

theorem isCpl_props {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] [IsLocalRing R]
    {j : O →+* R} (hj : IsCpl j) : Function.Injective j ∧ IsLocalHom j ∧
      ∀ (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ φ : O →+* V, IsLocalHom φ →
        ∃ ψ : R →+* V, IsLocalHom ψ ∧ ψ.comp j = φ := by
  obtain ⟨e, he⟩ := hj
  have hj : j = e.toRingHom.comp (algebraMap O _) := RingHom.ext fun a => (he a).symm
  have hl : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)) := inferInstance
  refine ⟨?_, ?_, fun V _ _ hV φ hφ => ?_⟩
  · rw [hj]
    exact e.injective.comp (AdicCompletion.of_injective (maximalIdeal O) O)
  · refine ⟨fun a ha => ?_⟩
    rw [← he, MulEquiv.isUnit_map] at ha
    exact isUnit_of_map_unit _ _ ha
  · obtain ⟨ψ, h1, h2⟩ := GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend O V hV φ hφ
    refine ⟨ψ.comp e.symm.toRingHom, ⟨fun a ha => ?_⟩, RingHom.ext fun a => ?_⟩
    · have := isUnit_of_map_unit ψ _ ha
      exact (MulEquiv.isUnit_map e.symm).1 this
    · rw [← h2, RingHom.comp_apply, ← he]
      simp

theorem orders_extend : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (D : GlobalTheory.EffCartierData M.Z) (ι : ℕ), (∀ z ∈ D.idealSheaf.support, z ∉ V) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ spMap S.R.val.toRingHom ≫ u → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M V v (𝟙 F.X) T ξ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hn F φ hφ W hW o' Ω _ _ _ _ S ρ u hu M U₀ EE FinalForm hU V v hv D ι hD hgen T ξ hT
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨R, _, _, _, j, Λ, _, p, c, hR, hj, hc, hper⟩ :=
    GlobalTheory.T.thetaModel_point_lattice_periods_traits g n _ _ F W hW o' Ω S ρ u hu M U₀ EE FinalForm hU V v hv (ξ (closedPoint T.V))
  haveI := hR.1.1
  haveI := hR.2
  obtain ⟨jinj, jloc, jext⟩ := isCpl_props hj
  obtain ⟨ψ, ψloc, hψ⟩ := jext T.V T.complete (Scheme.stalkClosedPointTo ξ).hom inferInstance
  have hξ : spMap (ψ.comp j) ≫ M.Z.fromSpecStalk (ξ (closedPoint T.V)) = ξ := by
    rw [hψ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  obtain ⟨d, hd⟩ : ∃ d, FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = Ideal.span {d} := by
    obtain ⟨i, hi⟩ := D.exists_mem (ξ (closedPoint T.V))
    exact ⟨_, D.stalkId_idealSheaf i _ hi⟩
  have hid : idlAlong D.idealSheaf ξ = Ideal.span {ψ (j d)} := by
    rw [idlAlong, hd, Ideal.map_span, Set.image_singleton, ← hψ]
    rfl
  obtain ⟨ξ₀, hξ₀, hξ₀'⟩ := hT
  have hmem : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ V := by
    rw [← hξ₀]
    exact (ξ₀ (closedPoint (FractionRing T.V))).2
  have hne := idlAlong_ne_bot D.idealSheaf ξ fun h => hD _ h hmem
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne T.irr
  refine ⟨a, ?_, ha⟩
  have hda : Associated (ψ (j d)) (T.ϖ ^ a) := Ideal.span_singleton_eq_span_singleton.1 (hid.symm.trans ha)
  obtain ⟨e, he⟩ := hper T ψ ψloc (by rw [hξ]; exact ⟨ξ₀, hξ₀, hξ₀'⟩)
  choose k hk hk' using he
  haveI := T.D.toPre.finX
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := T.D.toPre.X)
  obtain ⟨A, _, _, _, ϖ', ψ', m, m', k', hA, hϖ', ψ'inj, ψ'loc, hm, hm', hk''⟩ :=
    GlobalTheory.T.exists_complete_dvr_with_proportional_valuations R T.V T.ϖ T.irr ψ ψloc (Option (Fin N × Fin N))
      (fun i => i.elim (j d) fun ii => p (e.symm (b ii.1 + b ii.2)))
      (fun i => i.elim a fun ii => k (e.symm (b ii.1 + b ii.2)))
      (by rintro (_ | ii); exacts [hda, hk' _])
  obtain ⟨T', f, γ, finj, floc, -, hγ, hy⟩ := GlobalTheory.T.exists_trait_moduli_of_stalk_completeDVR g n _ _ F o' Ω M (spMap S.R.val.toRingHom ≫ u)
    (ξ (closedPoint T.V)) A hA (ψ'.comp j) (ψ'inj.comp jinj)
  have hrange : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (M.pt_specializes w _).mem_open V.isOpen hmem
  have hx₀ := IsOpenImmersion.lift_fac V.ι M.pt hrange
  obtain ⟨e', he'⟩ := hper T' (f.comp ψ') inferInstance
    ⟨spMap γ ≫ IsOpenImmersion.lift V.ι M.pt hrange, by rw [Category.assoc, hx₀]; exact hγ.symm,
      by rw [Category.comp_id, Category.assoc, hv _ hx₀, hy]⟩
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f finj).2 hϖ'.ne_zero) T'.irr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    exact hϖ'.not_isUnit ((isUnit_map_iff f ϖ').1 (associated_one_iff_isUnit.1 hr))
  have hpow : ∀ {x : A} {l : ℕ}, Associated x (ϖ' ^ l) → Associated (f x) (T'.ϖ ^ (r * l)) := by
    intro x l h
    have h1 := h.map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hr.pow_pow
  obtain ⟨a', ha', hid'⟩ := hgen T' _ γ hγ hy
  rw [GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk _ _ _ _ _ inferInstance, hd, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hid'
  have h0 := hk'' none
  have ea : a' = r * k' none := pow_exp_eq T'.irr (hid'.symm.trans (hpow h0.1))
  have h02 : m * k' none = m' * a := h0.2
  let E := e.symm.trans e'
  have hz := form_eq_zero ((m : ℤ) • pull E.toIntLinearEquiv.toLinearMap T'.β - ((m' * r : ℕ) : ℤ) • T.β)
    (fun x y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, pull_apply]
      rw [T.symm x y, T'.symm]) b hb (fun i i' => by
      obtain ⟨l, hl, hl'⟩ := he' (e.symm (b i + b i'))
      obtain ⟨h1, h2⟩ := hk'' (some (i, i'))
      have h3 : l = r * k' (some (i, i')) := pow_exp_eq T'.irr (hl'.symm.trans (hpow h1))
      have h4 := hk (e.symm (b i + b i'))
      rw [e.apply_symm_apply] at h4
      have h5 : (m : ℤ) * k' (some (i, i')) = m' * k (e.symm (b i + b i')) := by exact_mod_cast h2
      have hc0 : (c : ℤ) ≠ 0 := by omega
      change (m : ℤ) * T'.β (e' (e.symm (b i + b i'))) (e' (e.symm (b i + b i'))) -
        ((m' * r : ℕ) : ℤ) * T.β (b i + b i') (b i + b i') = 0
      refine mul_left_cancel₀ hc0 ?_
      rw [h3] at hl
      push_cast at hl ⊢
      linear_combination (-(m : ℤ)) * hl + r * h5 + m' * r * h4)
  have hev := evalZ_prop (by omega) hφ T T' E m (m' * r) fun x y =>
    sub_eq_zero.1 (congrArg (fun B : LinearMap.BilinForm ℤ T.D.toPre.X => B x y) hz)
  have h02' : (m : ℝ) * k' none = m' * a := by exact_mod_cast h02
  have hmr : ((m' : ℝ) * r) ≠ 0 := by
    have : m' ≠ 0 := by omega
    positivity
  refine mul_left_cancel₀ hmr ?_
  rw [ea] at ha'
  push_cast at ha' hev
  linear_combination (-(r : ℝ)) * h02' + m * ha' + ι * hev

end GlobalTheory.Poinc.Extend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitOrdersEffectiveCartierExtendFromGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitOrders_effectiveCartier_extend_from_generic : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (D : GlobalTheory.EffCartierData M.Z) (ι : ℕ), (∀ z ∈ D.idealSheaf.support, z ∉ V) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ spMap S.R.val.toRingHom ≫ u → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M V v (𝟙 F.X) T ξ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.Extend.orders_extend | exact GlobalTheory.Poinc.Extend.orders_extend | (intros; apply GlobalTheory.Poinc.Extend.orders_extend <;> assumption)
end
