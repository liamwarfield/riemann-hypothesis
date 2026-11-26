module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelSectionOfIdealTorsionAtGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelSectionOfIdealTorsionAtGeometricPoint
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section
open CartesianMonoidalCategory MonObj

namespace GlobalTheory.TorsSpec

theorem exists_etaSecL_of_torsI : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (I : Ideal (𝓞 E)) (hI : l.Mb ≤ I) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (P : Sp Ω ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left)
    (hP : P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = x ≫ ℓ)
    (hT : ∀ a ∈ I, P ≫ ((GlobalTheory.EqvAct.pullAct TF Z φ).act a).left =
      P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ GlobalTheory.EqvAct.pullG TF Z φ).left), ∃ c, P = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ I hI Ω _ _ x P hP hT
  have cart := TF.Y.m.cart
  have hpb := GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ
  have hQw : (P ≫ GlobalTheory.EqvAct.pullψ TF Z φ) ≫ TF.Y.t.G.hom = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.jQ ≫ pullback.fst _ _) := by
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hP, Category.assoc, reassoc_of% hℓ, Category.assoc, j₀_ι]
    rfl
  let Q := cart.1.lift _ _ hQw
  have hQφ : Q ≫ TF.Y.m.φ = P ≫ GlobalTheory.EqvAct.pullψ TF Z φ := cart.1.lift_fst _ _ hQw
  have hQh : Q ≫ TF.Y.oF.t.G.hom = x ≫ i₀ TF.Y Z := cart.1.lift_snd _ _ hQw
  let Q' : Over.mk (x ≫ i₀ TF.Y Z) ⟶ TF.Y.oF.t.G := Over.homMk Q hQh
  have htu : ∀ {S : Scheme.{0}} (T : Over S), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have hcartη := eta_comp_of_isGrpPullback cart
  have hpbη := eta_comp_of_isGrpPullback hpb
  have htors : ∀ a ∈ I, Q' ≫ TF.Y.oF.t.act.act a = 1 := by
    intro a ha
    apply Over.OverMorphism.ext
    rw [Hom.one_def, Over.comp_left, Over.comp_left, htu]
    show Q ≫ _ = (x ≫ i₀ TF.Y Z) ≫ _
    apply cart.1.hom_ext
    · rw [Category.assoc, TF.Y.m.act, reassoc_of% hQφ, ← GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% (hT a ha),
        hpbη, Category.assoc, Category.assoc, hcartη, reassoc_of% hP]
      simp only [Category.assoc]
      rw [reassoc_of% hℓ, reassoc_of% j₀_ι]
      rfl
    · rw [Category.assoc, Over.w, hQh, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  let s0 : Xo.XF c ⟶ Sp (KA l) := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
  let β : KA l →+* Ω := (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ s0)).hom
  have hβ : (x ≫ i₀ TF.Y Z) ≫ s0 = spMap β :=
    ((congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage _)).symm
  have hg := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z) β hβ
  obtain ⟨TI, -, -, hη⟩ := hg.2
  have hMI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    apply hI
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hpow : Q' ^ l.M = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN, ← act_natCast (E := E) TF.Y.oF.t.act, htors _ hMI]
  obtain ⟨a, ha⟩ := (TI.onto l.M hM0 Q').1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have hev : Q' = TI.ev l.M (v • a) := by
    have e1 : TI.ev l.M (u • a) = 1 := by
      rw [TI.lin, ha]
      exact htors u (hI hu)
    have e2 := TI.add l.M (u • a) (v • a)
    rw [← add_smul, huv, one_smul, ha, e1, _root_.one_mul] at e2
    exact e2
  have hvm : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hQeta : Q = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta (v • a)).left := by
    have := congrArg (fun q => q.left) (hev.trans (hη _ hvm).symm)
    simp only [Q', Over.homMk_left, Over.comp_left, htu] at this
    exact this
  refine ⟨Submodule.Quotient.mk (v • a), hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, etaSecL_ψ, ← hQφ, hQeta]
    simp only [Category.assoc]
  · rw [hP, Category.assoc, etaSecL_w]

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelSectionOfIdealTorsionAtGeometricPointStatement
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelSection_of_ideal_torsion_at_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (I : Ideal (𝓞 E)) (hI : l.Mb ≤ I) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (P : Sp Ω ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left)
    (hP : P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = x ≫ ℓ)
    (hT : ∀ a ∈ I, P ≫ ((GlobalTheory.EqvAct.pullAct TF Z φ).act a).left =
      P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ GlobalTheory.EqvAct.pullG TF Z φ).left), ∃ c, P = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c := by
  first | exact @GlobalTheory.TorsSpec.exists_etaSecL_of_torsI | exact GlobalTheory.TorsSpec.exists_etaSecL_of_torsI | (intros; apply GlobalTheory.TorsSpec.exists_etaSecL_of_torsI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulAction
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_geomPt_range_eq_singleton (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  refine ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g, ?_⟩
  ext y
  have h := fun t => X.fromSpecResidueField_apply g
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g)))) t)
  simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
  exact ⟨fun ⟨t, e⟩ => e.symm.trans (h t),
    fun e => ⟨IsLocalRing.closedPoint _, (h _).trans e.symm⟩⟩

theorem exists_geomPt_stalk_over {X' : Scheme.{0}} [IsIntegral X'] {T : Scheme.{0}} (f : T ⟶ X') [Flat f]
    {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (p : T) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec (T.presheaf.stalk p)) (z : Sp Ω ⟶ V),
      y ≫ T.fromSpecStalk p ≫ f = z ≫ ℓ := by
  obtain ⟨p', hp', hfp'⟩ := Flat.generalizingMap f (genericPoint_specializes (f p))
  have hmem : p' ∈ Set.range (T.fromSpecStalk p) := by rw [Scheme.range_fromSpecStalk]; exact hp'
  obtain ⟨d, hd⟩ := hmem
  obtain ⟨Ω, hF, hA, y, hy⟩ := exists_geomPt_range_eq_singleton _ d
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    refine ((genericPoint_spec X').mem_open_set_iff (IsOpenImmersion.isOpen_range ℓ)).mpr ?_
    exact ⟨ℓ (Classical.arbitrary V), trivial, _, rfl⟩
  have hr : Set.range (y ≫ T.fromSpecStalk p ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨t, rfl⟩
    have ht : y t = d := by
      have : y t ∈ Set.range y := ⟨t, rfl⟩
      rw [hy] at this
      exact this
    simp only [Scheme.Hom.comp_apply, ht, hd, hfp']
    exact hgen
  exact ⟨Ω, hF, hA, y, IsOpenImmersion.lift ℓ _ hr, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory.TorsSpec

namespace GlobalTheory.TorsSpec

theorem valAt_comp {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (τ : torsion G n ⟶ torsion G n) (p q : (torsion G n).left) (hq : τ.left p = q) (c : M)
    (h : ValAt G n ℓ w q c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V)
    (hyz : y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ (torsion G n).left.fromSpecStalk p ≫ τ.left ≫ (torsion.ι G n).left = z ≫ w c := by
  subst hq
  have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ.left (x := p)
  have hw : τ.left ≫ (torsion G n).hom = (torsion G n).hom := Over.w τ
  have h1 := h Ω (y ≫ Spec.map (τ.left.stalkMap p)) z (by
    simpa only [Category.assoc, reassoc_of% key, hw] using hyz)
  simpa only [Category.assoc, reassoc_of% key] using h1

theorem class_act : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    (hlin : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a : M) (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w (r • a) → B = A ≫ act.act r)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P : Over.mk t ⟶ G) (r : 𝓞 E)
    (PT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hRT : RT ≫ (torsion.ι G n).left = (P ≫ act.act r).left) (x : Sp K) (cP cR : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = r • cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act hlin K _ _ t P r PT RT hPT hRT x cP cR hcP hcR
  haveI := GrpTangent.etale_torsion G hn
  haveI := mono_torsion_ι G n
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G)) (CartesianMonoidalCategory.toUnit_unique _ _))
  have hτ : (torsion.ι G n ≫ act.act r) ≫ mulN G n = 1 := by
    haveI := act.hom r
    rw [← act_natCast act n, Category.assoc, ← act.mul, mul_comm, act.mul, ← Category.assoc,
      act_natCast act n, hι, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  obtain ⟨τ, hτι⟩ := exists_lift_torsion n _ hτ
  have hτl : τ.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ (act.act r).left := by
    rw [← Over.comp_left, hτι, Over.comp_left]
  have hPR : PT ≫ τ.left = RT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτl, reassoc_of% hPT, hRT, Over.comp_left]
  have hq : τ.left (PT x) = RT x := by rw [← hPR, Scheme.Hom.comp_apply]
  obtain ⟨Ω, hF, hA, y, z, hyz⟩ := exists_geomPt_stalk_over (torsion G n).hom ℓ (PT x)
  have h1 := hcP Ω y z hyz
  have h2 := valAt_comp G n ℓ w τ (PT x) (RT x) hq cR hcR Ω y z hyz
  rw [hτl, reassoc_of% h1] at h2
  let A : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w cP) (by rw [Category.assoc, hw]; rfl)
  let B : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w (r • cP)) (by rw [Category.assoc, hw]; rfl)
  have h3 := congrArg (fun q => q.left) (hlin Ω z cP r A B rfl rfl)
  simp only [A, B, Over.homMk_left, Over.comp_left] at h3
  exact (hun Ω z _ _ (h3.trans ((Category.assoc _ _ _).trans h2))).symm

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulActionStatement
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointClassAtStalk_smul_action : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    (hlin : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a : M) (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w (r • a) → B = A ≫ act.act r)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P : Over.mk t ⟶ G) (r : 𝓞 E)
    (PT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hRT : RT ≫ (torsion.ι G n).left = (P ≫ act.act r).left) (x : Sp K) (cP cR : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = r • cP := by
  first | exact @GlobalTheory.TorsSpec.class_act | exact GlobalTheory.TorsSpec.class_act | (intros; apply GlobalTheory.TorsSpec.class_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTorsionPointClassAtStalkEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTorsionPointClassAtStalkEq
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_of_valAt_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ K _ _ t P Q PT QT hPT hQT x c hcP hcQ
  haveI hEt : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  let q := pq (IsLocalRing.closedPoint K)
  have hfq : (pullback.fst (torsion G n).hom (torsion G n).hom) q = PT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
  have hsq : (pullback.snd (torsion G n).hom (torsion G n).hom) q = QT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.snd (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_snd]
  haveI hdom : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk q) :=
    isDomain_stalk_of_etale (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q
  let Wp := pullback (torsion G n).hom (torsion G n).hom
  let R : Type := Wp.presheaf.stalk q
  let Ω := AlgebraicClosure (FractionRing R)
  let φ : R →+* Ω := algebraMap R Ω
  have hφ : Function.Injective φ := by
    have e : φ = (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) :=
      IsScalarTower.algebraMap_eq R (FractionRing R) Ω
    rw [e]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let ybar : Sp Ω ⟶ Spec (Wp.presheaf.stalk q) := Spec.map (CommRingCat.ofHom φ)
  haveI hyd : IsDominant ybar := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  let s0 : Sp Ω := IsLocalRing.closedPoint Ω
  have hgen : ∀ e, ybar s0 ⤳ e := by
    intro e
    have hr : Set.range ybar = {ybar s0} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨s0, rfl⟩, by rintro _ ⟨s, rfl⟩; rw [Subsingleton.elim s s0]⟩
    rw [specializes_iff_mem_closure, ← hr, ybar.denseRange.closure_range]
    trivial
  let f : Spec (Wp.presheaf.stalk q) ⟶ X' :=
    Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  obtain ⟨w', hw'q, hw'ξ⟩ := Flat.generalizingMap (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom)
    (genericPoint_specializes ((pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q))
  have hw'r : w' ∈ Set.range (Wp.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact hw'q
  obtain ⟨d, hd⟩ := hw'r
  have hξV : genericPoint X' ∈ Set.range ℓ := by
    rw [(genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range]
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, trivial, v, rfl⟩
  have hsp : (ybar ≫ f) s0 ⤳ genericPoint X' := by
    have h1 := (hgen d).map f.continuous
    have e2 : f d = (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) w' := by
      rw [← hd]; rfl
    rw [show (ybar ≫ f) s0 = f (ybar s0) from rfl, ← hw'ξ, ← e2]
    exact h1
  have H : Set.range (ybar ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s0]
    exact hsp.mem_open ℓ.isOpenEmbedding.isOpen_range hξV
  let z : Sp Ω ⟶ V := IsOpenImmersion.lift ℓ (ybar ≫ f) H
  have hz : z ≫ ℓ = ybar ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hcP' : ValAt G n ℓ w ((pullback.fst (torsion G n).hom (torsion G n).hom) q) c := by rw [hfq]; exact hcP
  have hcQ' : ValAt G n ℓ w ((pullback.snd (torsion G n).hom (torsion G n).hom) q) c := by rw [hsq]; exact hcQ
  have k1 : Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.fst (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have k2 : Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.snd (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have h1 := hcP' Ω (ybar ≫ Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k1])
  have h2 := hcQ' Ω (ybar ≫ Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k2, ← pullback.condition])
  rw [Category.assoc, reassoc_of% k1] at h1
  rw [Category.assoc, reassoc_of% k2] at h2
  have hu : Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
    refine ext_of_isDominant_of_isSeparated G.hom ?_ ybar (h1.trans h2.symm)
    simp only [Category.assoc, hιT, pullback.condition]
  have hpq : Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q = pq :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk pq
  apply Over.OverMorphism.ext
  rw [← hPT, ← hQT]
  calc PT ≫ (torsion.ι G n).left
      = pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [← Category.assoc, pullback.lift_fst]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [hu]
    _ = QT ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq, ← Category.assoc, pullback.lift_snd]

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTorsionPointClassAtStalkEqStatement
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_torsionPointClassAtStalk_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  first | exact @GlobalTheory.TorsSpec.eq_of_valAt_eq | exact GlobalTheory.TorsSpec.eq_of_valAt_eq | (intros; apply GlobalTheory.TorsSpec.eq_of_valAt_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionSmulAtGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionSmulAtGeometricPoint
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
open CartesianMonoidalCategory MonObj
noncomputable section

namespace GlobalTheory.TorsSpec

theorem etaSecL_smul_geom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a : LevelMod Dw l)
    (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (r • a)) : B = A ≫ (GlobalTheory.EqvAct.pullAct TF Z φ).act r := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have key : x ≫ i₀ TF.Y Z ≫ (TF.Y.oF.eta (r • b)).left =
      x ≫ i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ (TF.Y.oF.t.act.act r).left := by
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) from
      l.coprime ▸ Submodule.mem_top)
    have ev : ∀ d : Dw.La, TF.Y.oF.eta d = TF.Y.oF.eta (v • d) := fun d => by
      conv_lhs => rw [← one_smul (𝓞 E) d, ← huv, add_smul, TF.Y.oF.eta_add,
        TF.Y.oF.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
    obtain ⟨-, I, -, -, hη⟩ := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z)
      (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))).hom
      (Spec.map_preimage _).symm
    have e : toUnit (Over.mk (x ≫ i₀ TF.Y Z)) ≫ TF.Y.oF.eta (r • b) =
        (toUnit (Over.mk (x ≫ i₀ TF.Y Z)) ≫ TF.Y.oF.eta b) ≫ TF.Y.oF.t.act.act r := by
      rw [ev (r • b), ev b, hη _ (Submodule.smul_mem_smul hv Submodule.mem_top),
        hη _ (Submodule.smul_mem_smul hv Submodule.mem_top), smul_comm v r b, I.lin]
    have ht : (toUnit (Over.mk (x ≫ i₀ TF.Y Z))).left = x ≫ i₀ TF.Y Z := by
      simpa using Over.w (toUnit (Over.mk (x ≫ i₀ TF.Y Z)))
    have e' := congrArg (fun q => q.left) e
    simp only [Over.comp_left, ht] at e'
    simpa only [Category.assoc] using e'
  apply Over.OverMorphism.ext
  rw [hB, Over.comp_left, hA, ← Submodule.Quotient.mk_smul]
  apply pullback.hom_ext
  · have h1 := etaSecL_ψ TF Z φ ℓ hℓ b
    have h2 := etaSecL_ψ TF Z φ ℓ hℓ (r • b)
    simp only [Category.assoc]
    rw [GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% h1, h2, ← TF.Y.m.act r, reassoc_of% key]
  · have w1 := etaSecL_w TF Z φ ℓ hℓ (Submodule.Quotient.mk b)
    have w2 := etaSecL_w TF Z φ ℓ hℓ (Submodule.Quotient.mk (r • b))
    have w3 := Over.w ((GlobalTheory.EqvAct.pullAct TF Z φ).act r)
    simp only [Category.assoc]
    erw [w2, w3, w1]

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionSmulAtGeometricPointStatement
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelSection_smul_at_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a : LevelMod Dw l)
    (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (r • a)), B = A ≫ (GlobalTheory.EqvAct.pullAct TF Z φ).act r := by
  first | exact @GlobalTheory.TorsSpec.etaSecL_smul_geom | exact GlobalTheory.TorsSpec.etaSecL_smul_geom | (intros; apply GlobalTheory.TorsSpec.etaSecL_smul_geom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionAddAtGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionAddAtGeometricPoint
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem mul_comp_eq_of_isGrpPullback {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G]
    {G₁ : Over S₁} [GrpObj G₁] {G₂ : Over S₂} [GrpObj G₂] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
    {ψ₁ : G₁.left ⟶ G.left} {ψ₂ : G₂.left ⟶ G.left}
    (h₁ : IsGrpPullback G₁ G f₁ ψ₁) (h₂ : IsGrpPullback G₂ G f₂ ψ₂) {T : Scheme.{0}}
    {t₁ : T ⟶ S₁} {t₂ : T ⟶ S₂} (ht : t₁ ≫ f₁ = t₂ ≫ f₂)
    (A₁ B₁ : Over.mk t₁ ⟶ G₁) (A₂ B₂ : Over.mk t₂ ⟶ G₂)
    (hA : A₁.left ≫ ψ₁ = A₂.left ≫ ψ₂) (hB : B₁.left ≫ ψ₁ = B₂.left ≫ ψ₂) :
    (A₁ * B₁).left ≫ ψ₁ = (A₂ * B₂).left ≫ ψ₂ := by
  have key : ∀ (u : T ⟶ S) (e₁ : t₁ ≫ f₁ = u) (e₂ : t₂ ≫ f₂ = u),
      (A₁ * B₁).left ≫ ψ₁ = (A₂ * B₂).left ≫ ψ₂ := by
    intro u e₁ e₂
    have wA : (A₁.left ≫ ψ₁) ≫ G.hom = u := by
      rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w A₁]; exact e₁
    have wB : (B₁.left ≫ ψ₁) ≫ G.hom = u := by
      rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w B₁]; exact e₁
    let a : Over.mk u ⟶ G := Over.homMk (A₁.left ≫ ψ₁) wA
    let b : Over.mk u ⟶ G := Over.homMk (B₁.left ≫ ψ₁) wB
    have p₁ : (a * b).left = (A₁ * B₁).left ≫ ψ₁ := by
      subst e₁
      exact h₁.2 (Over.mk t₁) A₁ B₁ a b rfl rfl
    have p₂ : (a * b).left = (A₂ * B₂).left ≫ ψ₂ := by
      subst e₂
      exact h₂.2 (Over.mk t₂) A₂ B₂ a b hA hB
    exact p₁.symm.trans p₂
  exact key _ ht rfl

theorem etaSecL_add_geom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a b : LevelMod Dw l)
    (A B C : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ b) (hC : C.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (a + b)), C = A * B := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ Ω _ _ x a b A B C hA hB hC
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [← Submodule.Quotient.mk_add] at hC
  let y : Sp Ω ⟶ Xo.XF c := x ≫ i₀ TF.Y Z
  let u : Over.mk y ⟶ 𝟙_ (Over (Xo.XF c)) := Over.homMk y (Category.comp_id y)
  have hψ : ∀ (d : Dw.La) (D : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ),
      D.left = x ≫ etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk d) →
      D.left ≫ GlobalTheory.EqvAct.pullψ TF Z φ = (u ≫ TF.Y.oF.eta d).left ≫ TF.Y.m.φ := by
    intro d D hD
    rw [hD, Category.assoc, etaSecL_ψ]
    change _ = ((x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta d).left) ≫ TF.Y.m.φ
    simp only [Category.assoc]
  have ht : (x ≫ ℓ) ≫ φ ≫ (barComp TF.Y Z).ι = y ≫ TF.Y.j := by
    change _ = (x ≫ (TF.Y.j ⁻¹ᵁ barComp TF.Y Z).ι) ≫ TF.Y.j
    rw [Category.assoc, Category.assoc, ← Category.assoc ℓ, hℓ, morphismRestrict_ι]
  have hmul := mul_comp_eq_of_isGrpPullback (GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ) TF.Y.m.cart ht
    A B (u ≫ TF.Y.oF.eta a') (u ≫ TF.Y.oF.eta b') (hψ _ _ hA) (hψ _ _ hB)
  have hC' := hψ _ _ hC
  rw [TF.Y.oF.eta_add a' b', MonObj.comp_mul] at hC'
  ext1
  refine (GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ).1.hom_ext (hC'.trans hmul.symm) ?_
  rw [Over.w C, Over.w (A * B)]

end GlobalTheory.TorsSpec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionAddAtGeometricPointStatement
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelSection_add_at_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a b : LevelMod Dw l)
    (A B C : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ b) (hC : C.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (a + b)), C = A * B := by
  first | exact @GlobalTheory.TorsSpec.etaSecL_add_geom | exact GlobalTheory.TorsSpec.etaSecL_add_geom | (intros; apply GlobalTheory.TorsSpec.etaSecL_add_geom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionInjectiveAtGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionInjectiveAtGeometricPoint
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSecL_injective_at (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (c c' : LevelMod Dw l)
    (h : x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c') : c = c' := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ c'

  have h1 := congrArg (· ≫ GlobalTheory.EqvAct.pullψ TF Z φ) h
  simp only [Category.assoc, etaSecL_ψ] at h1
  set x' := x ≫ i₀ TF.Y Z with hx'
  have hsec : ∀ a : Dw.La, (TF.Y.oF.eta a).left ≫ TF.Y.oF.t.G.hom = (𝟙_ (Over _)).hom := fun a =>
    Over.w (TF.Y.oF.eta a)
  have h2 : x' ≫ (TF.Y.oF.eta b).left = x' ≫ (TF.Y.oF.eta b').left := by
    refine TF.Y.m.cart.1.hom_ext ?_ ?_
    · simpa [hx', Category.assoc] using h1
    · simp only [hx', Category.assoc, hsec]
  let T : Over (Xo.XF c) := Over.mk x'
  have h3 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b = CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b' := by
    ext
    simp only [Over.comp_left]
    exact h2

  obtain ⟨β, hβ⟩ : ∃ β : KA l →+* Ω, x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β :=
    let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (KA l)) :=
      x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
    ⟨(Spec.preimage f).hom, by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, f]⟩
  obtain ⟨-, I, -, -, hI⟩ := TF.Y.oF.geom Ω x' β hβ
  obtain ⟨d, hd⟩ : ∃ d : Dw.La, d = b - b' := ⟨_, rfl⟩
  have hmul : TF.Y.oF.eta b = TF.Y.oF.eta b' * TF.Y.oF.eta d := by
    rw [← TF.Y.oF.eta_add, hd, add_sub_cancel]
  have hd1 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta d = 1 := by
    rw [hmul, MonObj.comp_mul] at h3
    exact mul_left_cancel (h3.trans (mul_one _).symm)
  have h1top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1top
  have hud : u • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hu Submodule.mem_top
  have hvd : v • d ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hsplit : d = u • d + v • d := by rw [← add_smul, huv, one_smul]
  have hev : TF.Y.oF.eta d = TF.Y.oF.eta (v • d) := by
    conv_lhs => rw [hsplit]
    rw [TF.Y.oF.eta_add, TF.Y.oF.eta_ker _ hud, one_mul]
  have hI1 : I.ev l.M (v • d) = 1 := (hI _ hvd).symm.trans (by rw [← hev]; exact hd1)
  obtain ⟨e, he⟩ := (I.ker l.M (by have := l.three_le; omega) (v • d)).1 hI1
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h0 := Ideal.mem_span_singleton_self ((l.M : ℕ) : 𝓞 E)
    rw [← l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left :
      l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h0
  have hvd' : v • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [he, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  rw [Submodule.Quotient.eq, ← hd, hsplit]
  exact Submodule.add_mem _ hud hvd'

end GlobalTheory.TorsSpec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionInjectiveAtGeometricPointStatement
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelSection_injective_at_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (c c' : LevelMod Dw l)
    (h : x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c'), c = c' := by
  first | exact @GlobalTheory.TorsSpec.etaSecL_injective_at | exact GlobalTheory.TorsSpec.etaSecL_injective_at | (intros; apply GlobalTheory.TorsSpec.etaSecL_injective_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreInjectsLevelModule
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem one_left {X' : Scheme.{0}} {G : Over X'} [GrpObj G] {Y : Scheme.{0}} (t : Y ⟶ X') :
    (1 : Over.mk t ⟶ G).left = t ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.TorsSpec

namespace GlobalTheory.EqvAct


open GlobalTheory.TorsSpec in
theorem torsLevel_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ I g _ hMb Γ _ _ ι ρ _ X' _ φ ℓ ρ' hX _ hℓo hℓ hρ m hm hmv
  haveI := hX
  haveI := hℓo
  have hsemi : IsSemiAbelian (pullG TF Z φ) := IsSemiAbelian.pullback _ _ TF.Y.t.semi
  haveI := hsemi.smooth
  haveI := hsemi.separated
  haveI := hsemi.comm
  haveI : Nonempty (V₀ TF.Y Z) := by
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    exact ⟨⟨z, (j_mem_barComp Z z).2 hz⟩⟩
  have hn : IsUnit ((l.M : ℕ) : Γ(X', ⊤)) := by
    have h0 : IsUnit ((l.M : ℕ) : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by have := l.three_le; omega))
    have := h0.map (((φ ≫ s₀ TF.Y Z).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
    simpa using this
  have hnI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    have h0 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact hMb ((Ideal.mul_le_inf.trans inf_le_left) h0)
  have hmv' : ∀ γ x, etaSecL TF Z φ ℓ hℓ x ≫ m γ = (ρ γ).asIso.hom ≫ etaSecL TF Z φ ℓ hℓ (ι γ x) := by
    intro γ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (ι γ (Submodule.Quotient.mk b))
    rw [← ha]
    refine hmv γ a b ?_ _ _ (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_ψ TF Z φ ℓ hℓ b)
      (etaSecL_ψ TF Z φ ℓ hℓ a)
    rw [ha]
    exact ((ι γ).symm_apply_apply _).symm
  intro K _ _ t
  classical
  have hlift : ∀ P : Over.mk t ⟶ pullG TF Z φ, IsTorsI I (pullAct TF Z φ) P →
      ∃ PT : Sp K ⟶ (torsion (pullG TF Z φ) l.M).left, PT ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left ∧
        ∃ x, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT (IsLocalRing.closedPoint K)) x := by
    intro P hP
    have h1 : P ≫ mulN (pullG TF Z φ) l.M = 1 := by rw [← act_natCast (pullAct TF Z φ)]; exact hP _ hnI
    obtain ⟨PT, hPT⟩ := exists_lift_torsion l.M P h1
    have hPT' : PT.left ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left := by rw [← Over.comp_left, hPT]
    refine ⟨PT.left, hPT', GlobalTheory.T.exists_class_torsionPoint_localScheme (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ)
      (pullAct TF Z φ) I (GlobalTheory.T.exists_levelSection_of_ideal_torsion_at_geometricPoint TF Z φ ℓ hℓ I hMb) K PT.left (fun a ha => ?_) _⟩
    have e1 := congrArg Over.Hom.left (hP a ha)
    rw [Over.comp_left, one_left] at e1
    rw [reassoc_of% hPT', e1, ← Category.assoc, Over.w PT]
    rfl
  let PT : ∀ P, IsTorsI I (pullAct TF Z φ) P → (Sp K ⟶ (torsion (pullG TF Z φ) l.M).left) :=
    fun P h => Classical.choose (hlift P h)
  have hPT : ∀ P h, PT P h ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left :=
    fun P h => (Classical.choose_spec (hlift P h)).1
  let cl : ∀ P, IsTorsI I (pullAct TF Z φ) P → LevelMod Dw l :=
    fun P h => Classical.choose (Classical.choose_spec (hlift P h)).2
  have hcl : ∀ P h, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT P h (IsLocalRing.closedPoint K)) (cl P h) :=
    fun P h => Classical.choose_spec (Classical.choose_spec (hlift P h)).2
  have hun := GlobalTheory.T.levelSection_injective_at_geometricPoint TF Z φ ℓ hℓ
  refine ⟨fun P => if h : IsTorsI I (pullAct TF Z φ) P then cl P h else 0, ?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    have hPQ : IsTorsI I (pullAct TF Z φ) (P * Q) := fun a ha => by
      haveI := (pullAct TF Z φ).hom a
      rw [MonObj.mul_comp, hP a ha, hQ a ha, _root_.mul_one]
    simp only [dif_pos hP, dif_pos hQ, dif_pos hPQ]
    exact GlobalTheory.T.torsionPoint_class_mul_eq_add (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun
      (GlobalTheory.T.levelSection_add_at_geometricPoint TF Z φ ℓ hℓ) K t P Q _ _ _ (hPT P hP) (hPT Q hQ) (hPT _ hPQ) _ _ _ _ (hcl P hP) (hcl Q hQ)
      (hcl _ hPQ)
  · intro P a hP
    have hPa : IsTorsI I (pullAct TF Z φ) (P ≫ (pullAct TF Z φ).act a) := fun r hr => by
      rw [Category.assoc, ← (pullAct TF Z φ).mul]
      exact hP _ (I.mul_mem_left a hr)
    simp only [dif_pos hP, dif_pos hPa]
    exact GlobalTheory.T.torsionPointClassAtStalk_smul_action (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      (GlobalTheory.T.levelSection_smul_at_geometricPoint TF Z φ ℓ hℓ) K t P a _ _ (hPT P hP) (hPT _ hPa) _ _ _ (hcl P hP) (hcl _ hPa)
  · intro P Q hP hQ he
    simp only [dif_pos hP, dif_pos hQ] at he
    exact GlobalTheory.T.eq_of_torsionPointClassAtStalk_eq (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) K t P Q _ _
      (hPT P hP) (hPT Q hQ) _ _ (hcl P hP) (he ▸ hcl Q hQ)
  · intro γ ht P Q hP hQP
    have hQ : IsTorsI I (pullAct TF Z φ) Q := fun a ha => by
      refine Over.OverMorphism.ext ?_
      have e1 := congrArg Over.Hom.left (hP a ha)
      rw [one_left] at e1
      rw [Over.comp_left, one_left, hQP, Category.assoc, ← hm.2.1 γ a, ← Category.assoc, ← Over.comp_left, e1,
        Category.assoc, eta_comp_of_isGrpPullback (hm.1 γ), ← Category.assoc, ht]
    simp only [dif_pos hP, dif_pos hQ]
    exact GlobalTheory.T.torsionPoint_class_image_eq_level_action (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      ρ' ρ hρ ι m hm hmv' K t γ P Q _ _ (hPT P hP) (hPT Q hQ) hQP _ _ _ (hcl P hP) (hcl Q hQ)

end GlobalTheory.EqvAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreInjectsLevelModuleStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fibre_injects_levelModule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m := by
  first | exact @GlobalTheory.EqvAct.torsLevel_pull | exact GlobalTheory.EqvAct.torsLevel_pull | (intros; apply GlobalTheory.EqvAct.torsLevel_pull <;> assumption)
end
