module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData GlobalTheory.DegPull

namespace GlobalTheory.StrictPull

theorem exists_isPullDeg_of_strict (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens) (hW : Nonempty (PsiOn D W))
    (hη : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W)
    (P' : PolAV (Spec (CommRingCat.of R'))) (F : P'.A.left ⟶ D.P.A.left)
    (gp : IsGrpPullback P'.A D.P.A (specOf φ) F) (w : LB.Iso P'.L (D.P.L.pull F)) (hw : w.IsGen) (hs : Strict w) :
    ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = P'.g ∧ Strict hD.w := by
  obtain ⟨ψW⟩ := hW
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hF := gp.1
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) (specOf φ) (fun _ => hE) D.rig D.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D.P.isLB P'.isLB hw' D.sym D.sym_gen D.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D.X → (𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ P'.A), ∀ x,
      (c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ (D.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (specOf φ ≫ (D.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫ specOf φ))).left = specOf φ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D.c a) (toUnit _ ≫ D.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D.c_add]
    exact m
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = jK R' ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W.ι (jK R' ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R' y = genericPoint (Spec (CommRingCat.of R')) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R' (FractionRing R')) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
      show specOf φ (jK R' y) ∈ W
      rw [hy]; exact hη), IsOpenImmersion.lift_fac _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c x).left =
      ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := fun x => by
    show g ≫ W.ι ≫ (D.c x).left = (jK R' ≫ (c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi x) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen x) g)
  choose psi hpsi vpsi using fun x => exists_down_val hw' D.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  let D' : DegPre R' :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  refine ⟨D',
    ⟨e, e_hom, w, hw, hE, ?_, AddEquiv.refl _, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, hs⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ rig D.rig (specOf φ) _
      (rigPull_le (G' := P'.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 Hrig
  · refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

def polPull {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) : PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem exists_isPullDeg_strict : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D W) → (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = D.P.g ∧ Strict hD.w := by
  intro _ R R' _ _ _ _ φ D W hW hη
  obtain ⟨w, hw, hs⟩ := exists_strict D.P.isLB (pullback.fst D.P.A.hom (specOf φ))
  exact exists_isPullDeg_of_strict R R' φ D W hW hη (polPull D.P (specOf φ)) (pullback.fst D.P.A.hom (specOf φ))
    (isGrpPullback_pullback D.P.A (specOf φ)) w hw hs

end GlobalTheory.StrictPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_degPre_strict_lineBundle_iso : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D W) → (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = D.P.g ∧ Strict hD.w := by
  first | exact @GlobalTheory.StrictPull.exists_isPullDeg_strict | exact GlobalTheory.StrictPull.exists_isPullDeg_strict | (intros; apply GlobalTheory.StrictPull.exists_isPullDeg_strict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.ArcPsiVal

theorem gm_const {K F : Type} [Field K] [Field F] (g : K →+* F) (z : Sp F) (U : (Sp K).Opens) (hz : spMap g z ∈ U)
    (C : Γ(Sp K, U)ˣ) (c : K) (hC : C.val = resTop _ (scal (𝟙 (Sp K)) c)) :
    (gm (spMap g) z U C).val = toStk z (g c) := by
  rw [gm_val _ _ _ hz, hC]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
    ((spMap g).naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  have e2 := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  refine (congrArg ((Sp F).presheaf.germ _ z hz).hom e).trans ?_
  refine (TopCat.Presheaf.germ_res_apply (Sp F).presheaf _ z hz _).trans ?_
  exact congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e2.symm

theorem value_of_qVal {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (P : DegPre R) (ϖ : R)
    (χ : P.X) (n : ℤ) (h : QForm.QVal P ϖ χ n) (F : Type) [Field F] [Algebra (FractionRing R) F] (z : Sp F)
    (j : P.P.L.ι) (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ c : FractionRing R, HasVal ϖ c n ∧
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val = toStk z (algebraMap (FractionRing R) F c) := by
  have exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}}
      (f : A →+* F) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
      (a : Γ(X, U)ˣ) (z : Sp F) :
      ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
    let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
    refine ⟨Units.map g.toMonoidHom a, ?_⟩
    have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
    rw [← toStk_valF _ U z hz]
    congr 1
    have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
    rw [valF, dite_eq_left ht]
    have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
    have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
    rw [e1]
    exact e3
  obtain ⟨e, -, c, hc, hC⟩ := genHasVal_units _ _ _ _ _ _ h
  obtain ⟨C, hCv, hCt⟩ := hC (fun _ => j)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
    simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have ht : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart P.P.L (K := PUnit) (fun _ => (P.c χ).left) (fun _ => j) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => hj)
  have hz' : Out.jK R (Out.jFK (R := R) F z) ∈ LB.wchart P.P.L (K := PUnit) (fun _ => (P.c χ).left) (fun _ => j) :=
    ht (show Out.jK R (Out.jFK (R := R) F z) ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz : Out.jFK (R := R) F z ∈ LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j) :=
    Set.mem_iInter.2 fun k => by
      rw [QForm.ptK_eq]; exact Set.mem_iInter.1 hz' k
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g (𝟙 _) _ ht (e.s (fun _ => j)) z
  rw [Category.comp_id, hg] at hv
  refine ⟨_, hasVal_mul_unit hc v, ?_⟩
  have h2 := congrArg (gm (spMap (algebraMap (FractionRing R) F)) z
    (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))) hCt
  rw [map_mul, gm_res _ _ _ hz] at h2
  replace hv := (congrArg Units.val (gm_pull _ _ _ _ hz' (e.s (fun _ => j)))).trans hv
  rw [map_mul, map_mul]
  exact (congrArg Units.val h2).trans
    (congrArg₂ (· * ·) (gm_const (algebraMap (FractionRing R) F) z _ hz C c hCv) hv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem psi_value (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (P : DegPre R) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (y : a.D₀.X) (χ : P.X)
    (hc : (P.c χ).left ≫ φ = spMap f ≫ (a.D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (hG : GenRel w (LB.pullGen _ _ _ (P.psi χ) (Out.jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F))
        (algebraMap (FractionRing R) F (algebraMap R _ u) ^ (a.be y y / 2)))
    (z : Sp F) (j : P.P.L.ι) (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  have exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}}
      (f : A →+* F) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
      (a : Γ(X, U)ˣ) (z : Sp F) :
      ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
    let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
    refine ⟨Units.map g.toMonoidHom a, ?_⟩
    have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
    rw [← toStk_valF _ U z hz]
    congr 1
    have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
    rw [valF, dite_eq_left ht]
    have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
    have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
    rw [e1]
    exact e3
  obtain ⟨hp, hv⟩ := (genRel_iff w _ _ _ z).1 hG
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c χ).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c χ) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c χ)) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hpt : spMap f (cpt R) ∈ (a.D₀.c y).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
    have h1 : (x ≫ φ) (cpt R) ∈ a.D₀.P.L.U j₀ := hj₀
    rw [hc] at h1
    exact h1
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVle⟩ := (Sp O').isBasis_affineOpens.exists_subset_of_mem_open hpt
    ((a.D₀.c y).left ⁻¹ᵁ a.D₀.P.L.U j₀).isOpen
  have hle : Out.jK O' ⁻¹ᵁ V ≤ LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hVle hq
  obtain ⟨r, ⟨r, rfl⟩, hr⟩ := a.gen y (fun _ => j₀) V hV (Set.subset_univ _) hVle hle
  have htV : ⊤ ≤ spMap f ⁻¹ᵁ V := (top_le_iff_cpt _ _).2 hpV
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g (spMap f) V htV r z
  have hcomp : Out.jFK (R := O') F ≫ Out.jK O' = spMap g ≫ spMap f := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  have hzV : Out.jK O' (Out.jFK (R := O') F z) ∈ V := by
    have h1 : (spMap g ≫ spMap f) z ∈ V := htV (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [← hcomp] at h1
    exact h1
  have hr' : pullU (Out.jK O') V r = res hle ((a.D₀.psi y).s (fun _ => j₀)) := Units.ext hr
  rw [← hcomp, ← gm_pull _ _ _ _ hzV, hr'] at hu₀
  replace hu₀ := (congrArg Units.val (gm_res (Out.jFK (R := O') F) z hle hzV _)).symm.trans hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * u₀, H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem q_eq_of_hasArcData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ _ b a W _ _ _ f u χ hfi h
  obtain ⟨t, m, P, φ, he, w, e, -, -, -, -, hc, hG⟩ := h
  refine ⟨t, m, P, e.toAddEquiv, fun ϖ Q n hϖ hQ hu y => ?_⟩
  let F := AlgebraicClosure (FractionRing W)
  let g : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective _ _)
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing W) F (algebraMap W _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.D.toPre.P.isLB ((P.D.toPre.c (e y)).left (cpt W))
  obtain ⟨v, hv⟩ := psi_value a f u P.D.toPre φ w y (e y) (hc y) F hF ((hG F _ hF rfl).1 y) z j hj
  obtain ⟨d, hd, hd'⟩ := value_of_qVal P.D.toPre ϖ (e y) _ (hQ (e y)) F z j hj
  have e1 := (toStk z).injective (hd'.symm.trans hv)
  rw [← map_zpow₀, ← map_mul] at e1
  have e2 := (algebraMap (FractionRing W) F).injective e1
  obtain ⟨s, hs⟩ := hu
  refine hasVal_unique hϖ hd ⟨s ^ (a.be y y / 2) * v, ?_⟩
  rw [e2, hs, mul_zpow, ← zpow_mul, Units.val_mul, map_mul, _root_.mul_assoc]
  congr 2
  exact (map_zpow (((algebraMap W (FractionRing W)) : W →* FractionRing W).comp (Units.coeHom W)) s _).symm

end GlobalTheory.ArcPsiVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfFormStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_psi_valuation_eq_half_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  first | exact @GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | exact GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | (intros; apply GlobalTheory.ArcPsiVal.q_eq_of_hasArcData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.GoodTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_point {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem splitOver_of_abLocus {W : Type} [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (h : ∀ x, x ∈ abLocus G) : GlobalTheory.LN.SplitOver G (maximalIdeal W) := by
  letI := Ideal.Quotient.field (maximalIdeal W)
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W)) := (default : PrimeSpectrum _)
  have hp := ArcNotAbelian.isProper_fibre G hG (W ⧸ maximalIdeal W) (spMap (Ideal.Quotient.mk (maximalIdeal W))) p (h _)
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hab : IsAbelianScheme ((Over.pullback (spMap (Ideal.Quotient.mk (maximalIdeal W)))).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hp,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  unfold GlobalTheory.LN.SplitOver
  exact ⟨_, ZJ.isGt_splitExtOfAbelian _ hab⟩

theorem exists_pelUnif_subsingleton : LL → UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ Y.j = jK W ≫ χ → Set.range χ ⊆ abLocus Y.t.G → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Subsingleton P.D.toPre.X := by
  intro _ hU E _ _ _ H D l Xo c O _ β Y W _ _ _ hW χ y hy hab
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp W), Nonempty (SABMap t Y.t χ) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull χ Y.t
    exact ⟨_, ⟨m⟩⟩
  have ht : ∀ x, x ∈ abLocus t.G := fun x => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).1 (hab ⟨x, rfl⟩)
  obtain ⟨P, -⟩ := hU E H W hW t (polAt_of_point Y m _ y hy) (splitOver_of_abLocus t.G t.semi ht)
  refine ⟨t, m, P, ?_⟩
  have hmax : (maximalIdeal W ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (W ⧸ maximalIdeal W ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick W (maximalIdeal W) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GoodTrait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_trivial_torus_abelianLocus : LL → UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ Y.j = jK W ≫ χ → Set.range χ ⊆ abLocus Y.t.G → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Subsingleton P.D.toPre.X := by
  first | exact @GlobalTheory.GoodTrait.exists_pelUnif_subsingleton | exact GlobalTheory.GoodTrait.exists_pelUnif_subsingleton | (intros; apply GlobalTheory.GoodTrait.exists_pelUnif_subsingleton <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.ProjFinite

theorem exists_relAmple_of_isProjBy {R : Type} [CommRing R] {A : Over (Sp R)} (h : GlobalTheory.AbLaw.IsProjBy A.hom) :
    ∃ H : LB A.left, H.IsLB ∧ Out.RelAmple A H := by
  obtain ⟨H, hH, m, s, hs⟩ := h
  have e : GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ) = H := by
    cases H
    simp [GlobalTheory.AbLaw.pw]
  have k : ∀ s : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy A.hom (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)) s → Out.RelAmple A H :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hH le_rfl s hs
  rw [e] at k
  exact ⟨H, hH, k s hs⟩

theorem isProjBy_of_fieldExtension {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)}
    {A : Over (Sp K)} [IsProper A₀.hom] {φ : A.left ⟶ A₀.left} (h : IsPullback φ A.hom A₀.hom (spMap i))
    {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB) (hw : LBIso L (L₀.pull φ))
    (hA : Out.RelAmple A L) : GlobalTheory.AbLaw.IsProjBy A₀.hom := by
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  have h₀ : Out.RelAmple A₀ L₀ :=
    (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull i h hL₀
      ((isAmpleLB_of_relAmple_of_isAffine A hL hA).of_lbIso (LB.isLB_pull hL₀ φ) hw.symm))
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K₀ A₀ L₀ hL₀).1 h₀
  exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL₀ d, n, s, hs⟩

theorem exists_isPullback {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
    {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S} (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, φ ≫ π₁ = π₂ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, h₁.lift_fst _ _ _, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_finite_isProjBy : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  let Ω := AlgebraicClosure K
  let a : K →+* Ω := algebraMap K Ω
  let B : Over (Sp Ω) := (Over.pullback (spMap a)).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap a)) B.hom A.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨H, hH, hamp⟩ := exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme Ω B hB)
  let K₀ : Subfield Ω := a.fieldRange
  let j : K →+* K₀ := a.rangeRestrictField
  have sq₀ := IsPullback.of_hasPullback A.hom (spMap j)
  obtain ⟨φ, hφ, sq⟩ := exists_isPullback sq₀ sqB (spMap K₀.subtype) (spMap_comp _ _)
  obtain ⟨s, hs⟩ := GlobalTheory.LBDescent.exists_lb_subfield Ω K₀ _ _ _ _ φ H hH sq
  let L : IntermediateField K Ω := IntermediateField.adjoin K (s : Set Ω)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have h : K₀ ≤ L.toSubfield := by
    rintro _ ⟨x, rfl⟩
    exact L.algebraMap_mem x
  refine ⟨L, inferInstance, inferInstance, hfin, ?_⟩
  let C : Over (Sp L) := (Over.pullback (spMap (algebraMap K L))).obj A
  have sqC : IsPullback (pullback.fst A.hom (spMap (algebraMap K L))) C.hom A.hom (spMap (algebraMap K L)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨φ₁, hφ₁, sq₁⟩ := exists_isPullback sq₀ sqC (spMap (Subfield.inclusion h)) (spMap_comp _ _)
  obtain ⟨ψ, hψ, sq₂⟩ := exists_isPullback sqC sqB (spMap L.toSubfield.subtype) (spMap_comp _ _)
  obtain ⟨L₁, hL₁, hw⟩ := hs L.toSubfield h (IntermediateField.subset_adjoin K _) C.left C.hom φ₁ ψ sq₁
    (sq₀.hom_ext (by rw [Category.assoc, hφ₁, hψ, hφ]) (by
      rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc, sq.w]
      exact congrArg _ (spMap_comp _ _))) sq₂.w
  have : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) sqC hA.proper
  exact isProjBy_of_fieldExtension L.toSubfield.subtype sq₂ hL₁ hH hw hamp

end GlobalTheory.ProjFinite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.GenericFibre

theorem lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem unif_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ∧
      LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) ∧
      (letI := H.starRing; ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
        P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left) := by
  letI := H.starRing
  have := P.U.gen_hom
  refine ⟨?_, ?_, fun a => ?_⟩
  · have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
      have h := P.U.ext
      rw [P.bundle] at h
      exact h
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (Geo.Tor.chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (Geo.Tor.chartPullUnpull P.A.L _ hgi)
      (Geo.Tor.chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  · have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem fibre_eq_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  intro E _ _ _ H D l Xo c O _ β Y R _ _ I t χ m P F _ _ y hy o φ₀ hφ₀ hL₀ ha₀
  letI := H.starRing
  obtain ⟨g₁, l₁, a₁⟩ := unif_generic P
  set ψ := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hψ
  have g₂ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (ψ ≫ m.φ) := g₁.comp m.cart
  have g₃ : IsGrpPullback o.P.A Y.t.G (jFK (R := R) F ≫ jK R ≫ χ) (φ₀ ≫ Y.m.φ) :=
    (hφ₀.comp Y.m.cart).congr hy rfl
  have w₁ : (φ₀ ≫ Y.m.φ) ≫ Y.t.G.hom = (o.P.A.hom ≫ jFK (R := R) F) ≫ jK R ≫ χ :=
    g₃.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨φ, e₁, e₂⟩ : ∃ φ : o.P.A.left ⟶ P.A.A.left, φ ≫ ψ ≫ m.φ = φ₀ ≫ Y.m.φ ∧
      φ ≫ P.A.A.hom = o.P.A.hom ≫ jFK (R := R) F :=
    ⟨g₂.1.lift _ _ w₁, g₂.1.lift_fst _ _ _, g₂.1.lift_snd _ _ _⟩
  have lm : LBIso t.PP.L (Y.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have lY : LBIso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ) := by
    obtain ⟨w, hw, -⟩ := Y.m.lin
    exact ⟨w, hw⟩
  have l₂ : LBIso P.A.L (Y.t.PP.L.pull (ψ ≫ m.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) l₁ (lbIso_pull lm ψ rfl)
  have l₃ : LBIso o.P.L (Y.t.PP.L.pull (φ₀ ≫ Y.m.φ)) :=
    LBIso.trans o.P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL₀ (lbIso_pull lY φ₀ rfl)
  refine ⟨φ, g₂.cancel (g₃.congr rfl e₁.symm) e₂,
    LBIso.trans o.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB P.A.isLB _) l₃ (lbIso_pull l₂ φ e₁.symm).symm,
    fun x => g₂.1.hom_ext ?_ ?_, ?_⟩
  · have a₂ : (P.oA.act x).left ≫ ψ = ψ ≫ (t.act.act x).left := (a₁ x).trans (Category.assoc _ _ _).symm
    have a₃ : (P.oA.act x).left ≫ ψ ≫ m.φ = (ψ ≫ m.φ) ≫ (Y.t.act.act x).left := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.φ) a₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (ψ ≫ ·) (m.act x)).trans (Category.assoc _ _ _).symm)))
    have a₄ : (o.oa.act x).left ≫ φ₀ ≫ Y.m.φ = (φ₀ ≫ Y.m.φ) ≫ (Y.t.act.act x).left := by
      rw [← Category.assoc, ha₀ x, Category.assoc, Category.assoc]
      exact congrArg _ (Y.m.act x)
    rw [Category.assoc, e₁, a₄, Category.assoc φ, a₃, ← Category.assoc φ, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  · rw [← e₁, hψ, Category.assoc]

end GlobalTheory.Ex.GenericFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  first | exact @GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | exact GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | (intros; apply GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_normalised_unit (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (d : Γ(T.left, ⊤)ˣ),
      α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val α r z J = gm (r ≫ (fst T A).left) z ⊤ d * val α₀ r z J := by
  have hγ := DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ (ptSecT A 1).left)) (NormTheta.rigT_isGen (T := T) hρ c)
  obtain ⟨d, hd⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero]) hγ
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ hγ _))
  refine ⟨α, d, hα, corr_of_val hL fun y J hJ => ?_, fun Z r z J hJ => ?_⟩
  · rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormTheta.ptSec_fst, Category.comp_id,
      val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]
  · rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, hd _ _ z J hJ, Category.comp_id, mul_comm]

theorem isGenSec_smul {k : ℤ} {th : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (e : Γ(T.left, ⊤)ˣ) :
    IsGenSec A L k (SecM.toSec A ((e : Γ(T.left, ⊤)) • SecM.ofSec A th)) := fun s => by
  obtain ⟨r, hr⟩ := H s
  have e₁ : SecM.ofSec A s = r • SecM.ofSec A th := Subtype.ext (funext hr)
  have e₂ : SecM.ofSec A s = (r * (e⁻¹ : Γ(T.left, ⊤)ˣ)) • ((e : Γ(T.left, ⊤)) • SecM.ofSec A th) := by
    rw [← mul_smul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, e₁]
  exact ⟨_, fun j => congrArg (fun q => q.1 j) e₂⟩

theorem exists_thG (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a : ℤ)
    (ha : a = ((m ^ 2 : ℕ) : ℤ)) {I : Type} {x : I → (T ⟶ A)} (hx : ∀ i, x i ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)} {s₁ : LB.Sec (LPow A L a T)}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))}
    {U : I → ThetaGrp A L a T} {s₂ : I → LB.Sec (LPow A L a T)} {w : I → Γ(T.left, ⊤)}
    (hα : α.IsGen) (hτ : τ.IsGen)
    (h₁ : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a ((1 : ℕ) : ℤ) α th s₁)
    (hU : ∀ i, SymLift A L a (m ^ 2) (x i) (U i)) (h₂ : ∀ i, IsActOf A L a (U i) s₁ (s₂ i))
    (hw : ∀ i, IsValueAt A L a (s₂ i) 1 τ (w i)) :
    ∃ e : Γ(T.left, ⊤)ˣ, ∀ i, ThG A L ρ m th (x i) (e * w i) := by
  subst ha
  obtain ⟨α', d, hα', hn, hv⟩ := exists_normalised_unit hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α hα
  obtain ⟨b, hb⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, NormTheta.one_left, zpow_neg,
        mul_inv_cancel])
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (NormTheta.rigT_isGen (T := T) hρ ((m ^ 2 : ℕ) : ℤ))))
  refine ⟨d * b, fun i => ⟨hx i, SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i)), α',
    SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁), U i, hα', hn, ?_, hU i, ?_, fun y J hJ => ?_⟩⟩
  · refine VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A h₁ (𝟙 _) y hJ, hv _ _ y J hJ, gs_unit _ _ ⊤ trivial, Units.val_mul, _root_.mul_assoc]
  · refine VVRank.isTwistPull_of_sv A hL (U i).isGen fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A (h₂ i) (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, translT, lift_fst, mul_left_comm]
  · have q := ThetaPtMove.sv_of_isValueAt (hw i) (𝟙 _) y hJ
    have q' := hb _ (𝟙 _) y J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, mul_inv_eq_iff_eq_mul] at q'
    rw [Category.id_comp, q', Units.val_mul, ← gs_unit _ _ ⊤ trivial] at q
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      q, ptSecT_fst, Units.val_mul, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
    ring

end

theorem exists_gen_thG_of_isThetaPt : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  intro K _ P ρ hρ m Ix x v hx H
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, h₁, hU, h₂, hw, hv⟩ := ThetaCoord.isThetaPtOver_of_subsingleton P H
  obtain ⟨e, he⟩ := exists_thG P.isLB hρ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hx (th := th) (α := α) hα hτ h₁ hU h₂ hw
  refine ⟨_, isGenSec_smul hth (u * e⁻¹), fun i => ?_⟩
  have q := ThG.smul P.isLB (a := ((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)))
    (th' := SecM.toSec P.A (((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)) • SecM.ofSec P.A th))
    rfl (he i)
  rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, ← hv i] at q
  exact q

end GlobalTheory.Ex.OneGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstantStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt | exact GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.GenericFibre

theorem exists_iso_section {X₁ X₂ Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {g : Y ⟶ X₁} {f : Y ⟶ X₂} (i : X₁ ⟶ Y)
    (hi : i ≫ g = 𝟙 X₁) (w₀ : LB.Iso (L₁.pull g) (L₂.pull f)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso L₁ (L₂.pull (i ≫ f)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
  have pt : ∀ x : X₁, g (i x) = x := fun x => congrArg (fun q : X₁ ⟶ X₁ => q x) hi
  have le : ∀ p : (PUnit → L₂.ι) × L₁.ι, (L₂.pull (i ≫ f)).U p.1 ⊓ L₁.U p.2 ≤
      i ⁻¹ᵁ ((L₂.pull f).U p.1 ⊓ (L₁.pull g).U (fun _ => p.2)) := fun p y hy =>
    ⟨mem_pull.2 ((mem_pull (F := i ≫ f)).1 hy.1), mem_pull.2 (by rw [pt]; exact hy.2)⟩
  let w : LB.Iso L₁ (L₂.pull (i ≫ f)) := ⟨fun p => res (le p) (pullU i _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
    intro Z r z j k hj hk
    have hm : r z ∈ (L₂.pull (i ≫ f)).U (fun _ => j) ⊓ L₁.U k := ⟨(mem_pull (F := i ≫ f)).2 hj, hk⟩
    exact (gm_res r z (le (fun _ => j, k)) hm _).trans (gm_pull r i z _ (le (fun _ => j, k) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, key⟩
  rw [key Z r z j k hj hk, key Z r z j' k' hj' hk',
    BoxExpansion.pw_trans hw (r ≫ i) z (j₁ := k) (j₁' := k') (j₂ := j) (j₂' := j')
      (by show g (i (r z)) ∈ _; rw [pt]; exact hk) (by show g (i (r z)) ∈ _; rw [pt]; exact hk') hj hj',
    Category.assoc, Category.assoc, hi, Category.comp_id]

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ z J, Good L z J → sval s' (𝟙 _) z J = sval s h z J := by
  subst e
  exact ⟨pullSec L φ ε s h, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_isoData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  intro R _ _ I D A G _ _ U
  obtain ⟨w₀, hw₀⟩ := U.ext
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hi' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨w, hw, key⟩ := exists_iso_section U.gen.inv.left hi w₀ hw₀
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK R)
  have hp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨ρ, hρ, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw U.LG.isLB A.isLB (ρ₀ := U.LG.rig) U.LG.rigGen
  refine ⟨w₀, ρ, w, hp, ⟨hw₀, hρ, fun z JA JG hA hG => ?_⟩, hw, hr, fun F _ _ k σ th H => ?_⟩
  · have e₁ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
      (cubeMapOf hp₁).e_comm.trans (Category.id_comp _)
    have e₂ : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G :=
      (cubeMapOf hp₂).e_comm
    have := hr _ (𝟙 _) z JG JA hG hA
    rw [Category.id_comp, Category.id_comp, wVal, key _ _ _ _ _ (hG (eSec A.A ≫ _ ≫ _)) (hA _), ← Category.assoc, e₁, e₂] at this
    exact this.symm
  · obtain ⟨σ', hσ⟩ := exists_pull_sec σ (UnifPre.gFK (G := G) F) (fun _ : Fin 1 => UnifPre.gFK (G := G) F)
      (funext fun _ => (Category.comp_id _).symm)
    have e : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    refine ⟨σ', hσ, fun s hs => ⟨σ', BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e (Category.id_comp _)
      fun y J₁ J₂ h₁ h₂ => ?_, hs⟩⟩
    have e' : ((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [e, Category.assoc, hi', Category.comp_id]
    have := H _ (U.genF F).left y J₂ J₁ h₂ h₁
    rw [wVal, key _ _ _ _ _ (h₂ (((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ _ ≫ _)) (h₁ _),
      ← Category.assoc, ← Category.assoc, e', e, zpow_natCast] at this
    exact (hσ y J₂ h₂).trans this

end GlobalTheory.Ex.GenericFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  first | exact @GlobalTheory.Ex.GenericFibre.exists_isoData | exact GlobalTheory.Ex.GenericFibre.exists_isoData | (intros; apply GlobalTheory.Ex.GenericFibre.exists_isoData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Reframe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem reframe : ThetaUnifAV → ReframeSt := by
  intro hT Q L₀ g u₀ _ _ _
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, -, hEf, -⟩ := hT Q rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb L₀ Q.L g Q.g u₀ u ht₁ ht₂
    (𝟙 _) inferInstance
  have hF : ∀ z, u.ex (F z) = u₀.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ u₀.Λ := fun z => by rw [← u.ker, hF, u₀.ker]
  have cΛ : (u.Λ : Set (Fin Q.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cΛ₀ : (u₀.Λ : Set (Fin g → ℂ)).Countable := by
    have := u₀.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u₀.Λ)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    FibreUnif.eq_zero_of_smul_mem_countable cΛ₀ fun t =>
      (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := FibreUnif.surjective_of_countable F cΛ fun v => by
    obtain ⟨z, hz⟩ := u₀.ex_onto (u.ex v)
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hz] at this
    exact right_eq_mul.1 this
  exact ⟨u, Hm, χ, Ef, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, hEf, hF⟩

end GlobalTheory.Ex.Arch
end
