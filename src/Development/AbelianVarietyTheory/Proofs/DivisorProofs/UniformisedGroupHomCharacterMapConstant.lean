module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.HomConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

def Acts (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left) (f : D₂.X → D₁.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J₁ : (Z ⟶ D₁.P.A.left) → D₁.P.L.ι)
    (J₂ : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D₁.P.L z J₁ → Good D₂.P.L z J₂ →
    r ≫ g₁.pG.left = r ≫ (fstG I e G₁).left ≫ G₁.hom ≫ eSec D₁.P.A →
    ∀ x, val (g₂.t x) (r ≫ a) z J₂ = val (g₁.t (f x)) r z J₁

theorem acts_of_torusHomOf (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) {f : D₂.X → D₁.X}
    {t : splitTorus _ D₁.X ⟶ splitTorus _ D₂.X} (ht : TorusHomOf f t)
    (hi : g₁.i ≫ a = t ≫ g₂.i) : Acts g₁ g₂ a.left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G₁).hom)
  let b : FinalForm ⟶ thickObj R I e G₁ := Over.homMk r rfl
  let τ := g₁.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g₁ b).2 h)
  have hτ : τ ≫ g₁.i = b := g₁.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g₂.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D₂ e G₂ g₂ FinalForm (τ ≫ t) 1 z J₂ hJ₂ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ FinalForm τ 1 z J₁ hJ₁ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((torusHomOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    {a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left} {f f' : D₂.X → D₁.X}
    (h : Acts g₁ g₂ a f) (h' : Acts g₁ g₂ a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J₁ hJ₁ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (ψ z)
  choose J₂ hJ₂ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₂.P.A.left => exists_chart D₂.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g₁ g₁.i).1 g₁.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ _ (𝟙 _) 1 z J₁ hJ₁ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J₁ J₂ hJ₁ hJ₂ c x).symm.trans (h' _ _ z J₁ J₂ hJ₁ hJ₂ c x)).trans (k _))


omit [IsDomain R] [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] in
theorem thickMap_comm (aG : G₁ ⟶ G₂) (e : ℕ) :
    thickMap R I e G₁ ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G₂ := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (aG : G₁ ⟶ G₂)
    {f : D₂.toPre.X → D₁.toPre.X}
    (h : Acts (U₁.gt (e + 1)) (U₂.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ c x
  have t : thickMap R I e G₁ ≫ (fstG I (e + 1) G₁).left = (fstG I e G₁).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G₁) ≫ (U₁.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G₁) ≫ (fstG I (e + 1) G₁).left ≫ G₁.hom ≫ eSec D₁.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U₁.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G₁.hom ≫ eSec D₁.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G₁) z J₁ J₂ hJ₁ hJ₂ up x
  have sq : (r ≫ thickMap R I e G₁) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G₂ := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ₂ (U₂.gt_t e x) _).symm.trans ((val_pull hJ₂ _ _ _).trans (k.trans
    ((val_pull hJ₁ _ _ _).symm.trans (val_corr hJ₁ (U₁.gt_t e (f x)) r))))

theorem exists_torus_hom (hR : AdmBase R I) (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ h : D₂.X →+ D₁.X, ∃ t, TorusHomOf h t ∧ g₁.i ≫ a = t ≫ g₂.i := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := EndTorus.connectedSpace_thickening I e
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₂.i_hom
  have hk := g₂.isKernel
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  have : Mono g₂.i := by
    have : Mono (η[thickObj R I e D₂.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  let t := hk.lift (g₁.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
  have ht : t ≫ g₂.i = g₁.i ≫ a := hk.lift_fst _ _ _
  have : IsMonHom (t ≫ g₂.i) := ht ▸ inferInstance
  have : IsMonHom t := EndTorus.isMonHom_of_mono t g₂.i
  obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
  exact ⟨h, t, (torusHomOf_iff_appTop _ _).2 hh, ht.symm⟩

end GlobalTheory.Mum.Two.HomConst


open GlobalTheory.Mum.Two.HomConst in
theorem GlobalTheory.Mum.Two.unifPre_hom_character_const : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have ex := fun e => exists_torus_hom hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D₂.toPre.X → D₁.toPre.X),
      Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a).left f →
      Acts (U₁.gt 0) (U₂.gt 0) ((Over.pullback (thick R I 0)).map a).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U₁ U₂ a k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ _ (down e _ (acts_of_torusHomOf _ _ _ (ht e) (hi e)))
    (acts_of_torusHomOf _ _ _ (ht 0) (hi 0))]
  exact ht e
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_characterMap_constant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  first | exact @GlobalTheory.Mum.Two.unifPre_hom_character_const | exact GlobalTheory.Mum.Two.unifPre_hom_character_const | (intros; apply GlobalTheory.Mum.Two.unifPre_hom_character_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCovering
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCovering
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverChern

open Set

section Cover

variable {n : ℕ} {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

theorem exists_evenly_covered_on
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {U : Set A} (hU : IsOpen U) {d : ℕ}
    (hfib : ∀ x ∈ U, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∈ U → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∈ U) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∈ U, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∈ U), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨V, hV, hVd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzU : ∀ z ∈ F, m z ∈ U := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ V z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    GlueCover.exists_sheet hd hρ hd' hρ' hm (hch z (hzU z hz)) (hV z).2 (hV z).1
  choose! M hMV hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ U, (isOpen_biInter_finset hMi).inter hU,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, inter_subset_right,
    fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMV z₁ h₁) (hMV z₂ h₂) (hVd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]

theorem glueMeas_preimage_of_cover_on
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {U : Set A} (hU : IsOpen U) {d : ℕ}
    (hfib : ∀ x ∈ U, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∈ U → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {S : Set A} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    glueMeas e' ρ' (m ⁻¹' S) = d * glueMeas e ρ S := by
  have hW : ∀ x : U, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧ W ⊆ U ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered_on hd hρ hd' hρ' hm hU hfib hch x.2
  choose W hWo hxW hWU hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  have key : (Measure.map m (glueMeas e' ρ')).restrict U =
      ((d : ℝ≥0∞) • glueMeas e ρ).restrict U := by
    refine Measure.ext_of_iUnion_eq_univ
      (s := fun o : Option C => o.elim Uᶜ fun c => W c.1) ?_ fun o => ?_
    · refine eq_univ_of_forall fun x => ?_
      by_cases hx : x ∈ U
      · have hmem : x ∈ ⋃ i ∈ C, W i := by
          rw [hCW]
          exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
        obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
        exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
      · exact mem_iUnion.2 ⟨none, hx⟩
    · cases o with
      | none =>
        show ((Measure.map m (glueMeas e' ρ')).restrict U).restrict Uᶜ =
          (((d : ℝ≥0∞) • glueMeas e ρ).restrict U).restrict Uᶜ
        rw [Measure.restrict_restrict hU.measurableSet.compl,
          Measure.restrict_restrict hU.measurableSet.compl, compl_inter_self,
          Measure.restrict_empty, Measure.restrict_empty]
      | some c =>
        show ((Measure.map m (glueMeas e' ρ')).restrict U).restrict (W c.1) =
          (((d : ℝ≥0∞) • glueMeas e ρ).restrict U).restrict (W c.1)
        ext Q hQ
        have hQW := hQ.inter (hWo c.1).measurableSet
        have hQWU := hQW.inter hU.measurableSet
        rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ, Measure.restrict_apply hQW,
          Measure.restrict_apply hQW, Measure.map_apply hm.measurable hQWU,
          hWQ c.1 _ hQWU fun y hy => hy.1.2, Measure.smul_apply, smul_eq_mul]
  have h := congrArg (fun μ : Measure A => μ S) key
  simp only [Measure.restrict_apply hS, inter_eq_left.2 hSU,
    Measure.map_apply hm.measurable hS, Measure.smul_apply, smul_eq_mul] at h
  exact h

end Cover

theorem chernPart_preimage_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ (n : ℕ), (∀ y ∈ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w)) → ∀ (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ U → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ)  ⁻¹' S) = n * φ.chernPart D ε S := by
  intro k _ X Y _ _ p q D hp hq σ π hπ B φ hφ ε U hU n hfib hchart hlift hdens S hS hSU
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  have hφ' := hφ.pull π hπ
  unfold Weight.chernPart
  refine glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (PtsOver.continuous_map π hπ _) hU hfib (fun z hz => ?_) hS hSU
  · rw [c.chernDens_trans c' hφ hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [c.chernDens_trans c' hφ' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, hc⟩ := hchart _ hz
    obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
    exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by rw [hdens c c' hc' w hw]⟩⟩

end GlobalTheory.CoverChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCoveringStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ (n : ℕ), (∀ y ∈ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w)) → ∀ (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ U → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ)  ⁻¹' S) = n * φ.chernPart D ε S := by
  first | exact @GlobalTheory.CoverChern.chernPart_preimage_of_cover | exact GlobalTheory.CoverChern.chernPart_preimage_of_cover | (intros; apply GlobalTheory.CoverChern.chernPart_preimage_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem polFib_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] (x : Sp R ⟶ Xo.X), PolFib Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) x := by
  intro E _ _ _ H Dw l Xo c R _ x
  obtain ⟨P', φ, hg, hc, hL⟩ :=
    GlobalTheory.PureType.exists_baseChange GlobalTheory.abelianSchemeLaws_all.1.polBaseChange x (GlobalTheory.objPolAV Xo.univ)
  exact ⟨P', φ, hg, hc, hL⟩

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] (x : Sp R ⟶ Xo.X), PolFib Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) x := by
  first | exact @GlobalTheory.UMin.polFib_univ | exact GlobalTheory.UMin.polFib_univ | (intros; apply GlobalTheory.UMin.polFib_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphic
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem coe_aeval_sym_substAlg {n : ℕ} (φ : V n → V n) (v : V n) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    ((MvPolynomial.aeval sym (GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) p) : Ev n) : Alt n) =
      pull (fderiv ℂ φ v) ((MvPolynomial.aeval sym p : Ev n) : Alt n) := by
  have h : ((Subalgebra.center ℂ (Alt n)).val.comp ((MvPolynomial.aeval sym).comp
      (GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)))) =
      (pull (fderiv ℂ φ v)).comp ((Subalgebra.center ℂ (Alt n)).val.comp (MvPolynomial.aeval sym)) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, GlobalTheory.ChernPull.substAlg, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, Subalgebra.coe_val, sym, (pull_dz _ _).1, (pull_dz _ _).2, Finset.sum_mul_sum,
      smul_mul_smul_comm, GlobalTheory.ChernPull.jac]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, ← map_mul, ← Algebra.smul_def]
  exact DFunLike.congr_fun h p

theorem chernAt_comp : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (φ : V n → V n) (v : V n), AnalyticAt ℂ φ v → MContDiffAt 2 H (φ v) → IsUnit (H (φ v)).det → ∀ j, (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt n) := by
  intro n r _ _ H φ v hφ h2 hu j
  rw [chernAt, chernAt, GlobalTheory.ChernPull.chernPoly_comp hφ h2 hu, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul,
    coe_aeval_sym_substAlg]

end GlobalTheory.CxForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphicStatement
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormOfGramMatrixAt_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (φ : V n → V n) (v : V n), AnalyticAt ℂ φ v → MContDiffAt 2 H (φ v) → IsUnit (H (φ v)).det → ∀ j, (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt n) := by
  first | exact @GlobalTheory.CxForm.chernAt_comp | exact GlobalTheory.CxForm.chernAt_comp | (intros; apply GlobalTheory.CxForm.chernAt_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {T : Scheme.{0}}
  (t : SAB H T)

def LatPres {R : Type} [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) {g M : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R) : Prop :=
  (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
    ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
        (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) cf w →
      (spMap (epsMul δ) ≫ w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (kind p) ↔
        ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1)

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)


abbrev LocAssign {X W : Scheme.{0}} (r : ℕ) (jB : W ⟶ X) (U : X.Opens) : Type 1 :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

end Free

end GlobalTheory.ArLieBase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

structure IsProdUnif (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (U : UnifPre I D A (G₁ ⊗ G₂))
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A) : Prop where
  gen_pr₁ : U.gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom
  gen_pr₂ : U.gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom
  wL : ∃ w : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left), w.IsGen
  q_pr₁ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₁ =
    (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ (U₁.gt e).q
  q_pr₂ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₂ =
    (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ (U₂.gt e).q
  i_pr₁ : ∀ (e : ℕ) (h : D₁.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = t ≫ (U₁.gt e).i
  i_pr₂ : ∀ (e : ℕ) (h : D₂.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = t ≫ (U₂.gt e).i

variable {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem IsProdUnif.linHom_fst (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₁ : D₁.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₁ y) = y) (h₂ : ∀ y, q₂ (j₁ y) = 0) : LinHom U U₁ p₁ j₁ (fst G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₁ e).symm, fun e => hU.i_pr₁ e j₁ h₁ h₂⟩

theorem IsProdUnif.linHom_snd (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₂ : D₂.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₂ y) = 0) (h₂ : ∀ y, q₂ (j₂ y) = y) : LinHom U U₂ p₂ j₂ (snd G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₂ e).symm, fun e => hU.i_pr₂ e j₂ h₁ h₂⟩

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

theorem chernMat_isForm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsForm fun (c : AlgChart p σ D) y => chernMat φ c y := by
  intro k _ X p σ D B φ hφ
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_, fun c y hy => ?_⟩
  · have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hm := ChartGlue.mem_over c.e hy hy'
    have e : (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => (φ.φ (pick φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
    unfold chernMat AlgChart.hess
    beta_reduce
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hφ.contDiffAt c' hy' (mem_pick _ y))), e₂, chg]
    have hJ : (Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l) =
        transMat c c' y := rfl
    rw [hJ]
    congr 1
  · intro v hv
    have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick φ.isLB (c.e.symm v))))
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v))) :=
      ⟨hv, mem_pick φ.isLB _⟩
    have hs : ContDiffOn ℝ ∞ (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v)))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart (hφ _) c)
    have hc : ContinuousAt
        (fun w => cHess D (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ)) w) v :=
      continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
        (ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb ho hs a b).continuousAt (ho.mem_nhds hm)
    refine ContinuousAt.continuousWithinAt (hc.congr ?_)
    filter_upwards [ho.mem_nhds hm] with w hw
    unfold chernMat
    beta_reduce
    rw [c.hess_eq hφ (c.e.map_target hw.1) hw.2 (mem_pick _ _), AlgChart.hess, c.e.right_inv hw.1]
  · have hd := hφ.contDiffAt c hy (mem_pick φ.isLB y)
    set g : V D → ℂ := fun v => ((φ.φ (pick φ.isLB y) (c.e.symm v) : ℝ) : ℂ) with hg
    have hg2 : ContDiffAt ℝ 2 g (c.e y) := Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd
    have hgc : (fun w => (starRingEnd ℂ) (g w)) = g := funext fun w => by simp [g]
    show (cHess D g (c.e y)).IsHermitian
    ext j l
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wd D l (ReciprocityTheory.L2DbarEstimates.wdb D j g) (c.e y)) =
      ReciprocityTheory.L2DbarEstimates.wd D j (ReciprocityTheory.L2DbarEstimates.wdb D l g) (c.e y)
    have h1 : (fun w => (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wdb D j g w)) = ReciprocityTheory.L2DbarEstimates.wd D j g := by
      funext w
      rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' D j g w, hgc]
    rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj' D l (ReciprocityTheory.L2DbarEstimates.wdb D j g) (c.e y), h1,
      ReciprocityTheory.L2DbarEstimates.comm_wd_wdb g (c.e y) hg2 j l]

end GlobalTheory.MixDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianScheme
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_mul_all (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (f : Form (A.hom ≫ 𝟙 (Sp R))) (a b : epsR R ⟶ A) :
    tanVal (a * b) f = tanVal a f + tanVal b f := by
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  have hP : AllPrim (dp0 R) (𝟙 _) A :=
    (GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison hC hH) R A g hA hg).1
  have hc : Form.cl _ f ∈ prim (dp0 R) (𝟙 _) A := by rw [hP]; trivial
  rw [mem_prim_iff] at hc
  have mμ : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R) (μ[A]).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m1 : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R)
      (SemiCartesianMonoidalCategory.fst A A).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m2 : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R)
      (SemiCartesianMonoidalCategory.snd A A).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have e0 : pullOver (dp0 R) (𝟙 _) μ[A] (Form.cl _ f) = mμ.pull1 (Form.cl _ f) := rfl
  have e1 : pullOver (dp0 R) (𝟙 _) (SemiCartesianMonoidalCategory.fst A A) (Form.cl _ f) =
    m1.pull1 (Form.cl _ f) := rfl
  have e2 : pullOver (dp0 R) (𝟙 _) (SemiCartesianMonoidalCategory.snd A A) (Form.cl _ f) =
    m2.pull1 (Form.cl _ f) := rfl
  have hcl : Form.cl _ (mμ.pullForm f - (m1.pullForm f + m2.pullForm f)) = 0 :=
    ((map_sub _ _ _).trans (congrArg₂ (· - ·) (IsMor.cl_pullForm mμ f)
      ((map_add _ _ _).trans (congrArg₂ (· + ·) (IsMor.cl_pullForm m1 f) (IsMor.cl_pullForm m2 f))))).trans
      ((congrArg₂ (· - ·) e0 (congrArg₂ (· + ·) e1 e2)).symm.trans (sub_eq_zero.2 hc))
  have hinj : Function.Injective (GlobalTheory.CechDR.clForm ((A ⊗ A).hom ≫ 𝟙 (Sp R))) :=
    (hH R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hg2).2.2.2.2.1.2.1
  have hcmp : GlobalTheory.CechDR.cmpForm _ (mμ.pullForm f - (m1.pullForm f + m2.pullForm f)) = 0 :=
    hinj (((GlobalTheory.CechDR.comparison_formClass _ _).symm.trans ((congrArg _ hcl).trans (map_zero _))).trans (map_zero _).symm)
  have h0 := GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero R (A ⊗ A) (lift a b) _ hcmp
  have h1 : tanVal (lift a b) (mμ.pullForm f) = tanVal (lift a b) (m1.pullForm f + m2.pullForm f) :=
    sub_eq_zero.1 ((map_sub _ _ _).symm.trans h0)
  calc tanVal (a * b) f = tanVal (lift a b ≫ μ[A]) f := by rw [Hom.mul_def]
    _ = tanVal (lift a b) (mμ.pullForm f) := tanVal_comp _ _ mμ f
    _ = tanVal (lift a b) (m1.pullForm f) + tanVal (lift a b) (m2.pullForm f) := h1.trans (map_add _ _ _)
    _ = tanVal (lift a b ≫ SemiCartesianMonoidalCategory.fst A A) f +
        tanVal (lift a b ≫ SemiCartesianMonoidalCategory.snd A A) f :=
      (congrArg₂ (· + ·) (tanVal_comp _ _ m1 f) (tanVal_comp _ _ m2 f)).symm
    _ = tanVal a f + tanVal b f :=
      congrArg₂ (fun x y ↦ tanVal x f + tanVal y f) (lift_fst a b) (lift_snd a b)

end GlobalTheory.TanAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianSchemeStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (f : Form (A.hom ≫ 𝟙 (Sp R))) (a b : epsR R ⟶ A), tanVal (a * b) f = tanVal a f + tanVal b f := by
  first | exact @GlobalTheory.TanAdd.tanVal_mul_all | exact GlobalTheory.TanAdd.tanVal_mul_all | (intros; apply GlobalTheory.TanAdd.tanVal_mul_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (f' g' : G₁ ⟶ G₁) (fA gA : A₁.A ⟶ A₂.A) (fA' gA' : A₁.A ⟶ A₁.A), Gen₀ U₁ U₂ f fA → Gen₀ U₁ U₂ g gA → Gen₀ U₁ U₁ f' fA' → Gen₀ U₁ U₁ g' gA' → LBIso (cubeLB G₂ ![fst G₁ G₁ ≫ f, snd G₁ G₁ ≫ g] U₂.LG.L) (cubeLB G₁ ![fst G₁ G₁ ≫ f', snd G₁ G₁ ≫ g'] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ fA, snd A₁.A A₁.A ≫ gA] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ fA', snd A₁.A A₁.A ≫ gA'] A₁.L) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ f g f' g' fA gA fA' gA' hf hg hf' hg' H
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have eG := (cls_cubeLB G₂ _ U₂.LG.isLB).symm.trans (((cls_eq_iff (LB.isLB_linComb U₂.LG.isLB _ _)
    (LB.isLB_linComb U₁.LG.isLB _ _)).2 H).trans (cls_cubeLB G₁ _ U₁.LG.isLB))
  have e := (key U₂ f g fA gA hf hg).symm.trans ((congrArg _ eG).trans (key U₁ f' g' fA' gA' hf' hg'))
  let v := lift (fst A₁.A A₁.A ≫ U₁.gen.inv) (snd A₁.A A₁.A ≫ U₁.gen.inv)
  have hv : v ≫ u = 𝟙 _ := by ext <;> simp [u, v]
  have canc : ∀ c : Pic (A₁.A ⊗ A₁.A).left,
      CechPic.pull v.left (CechPic.pull (inv δ).left (CechPic.pull δ.left (CechPic.pull u.left c))) = c := by
    intro c
    rw [← pull_comp (inv δ).left δ.left, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, pull_id,
      ← pull_comp v.left u.left, ← Over.comp_left, hv, Over.id_left, pull_id]
  have eA := (canc _).symm.trans ((congrArg (fun c => CechPic.pull v.left (CechPic.pull (inv δ).left c)) e).trans (canc _))
  exact (cls_eq_iff (LB.isLB_linComb A₂.isLB _ _) (LB.isLB_linComb A₁.isLB _ _)).1
    ((cls_cubeLB A₂.A _ A₂.isLB).trans (eA.trans (cls_cubeLB A₁.A _ A₁.isLB).symm))

end GlobalTheory.Mum.Two
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeBundleIso_uniformisedGroup_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (f' g' : G₁ ⟶ G₁) (fA gA : A₁.A ⟶ A₂.A) (fA' gA' : A₁.A ⟶ A₁.A), Gen₀ U₁ U₂ f fA → Gen₀ U₁ U₂ g gA → Gen₀ U₁ U₁ f' fA' → Gen₀ U₁ U₁ g' gA' → LBIso (cubeLB G₂ ![fst G₁ G₁ ≫ f, snd G₁ G₁ ≫ g] U₂.LG.L) (cubeLB G₁ ![fst G₁ G₁ ≫ f', snd G₁ G₁ ≫ g'] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ fA, snd A₁.A A₁.A ≫ gA] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ fA', snd A₁.A A₁.A ≫ gA'] A₁.L) := by
  first | exact @GlobalTheory.Mum.Two.lbIso_cubeLB_generic | exact GlobalTheory.Mum.Two.lbIso_cubeLB_generic | (intros; apply GlobalTheory.Mum.Two.lbIso_cubeLB_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelAbLocus

theorem relAmple_of_lbIso_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [IsProper A.hom]
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) (hA : RelAmple A L) : RelAmple A' L' := by
  have h₁ : RelAmple A' (L.pull φ) := AmpleBaseChange.relAmple_of_isPullback hL hA h
  obtain ⟨w, hw⟩ : LBIso L' ((L.pull φ).pull (𝟙 _)) :=
    e.chartPull (chartPullId _) (Geo.Tor.chartPullPull (L.pull φ) _ _ rfl)
  exact PolOfIso.relAmple_pull_of_affine (f := 𝟙 S') (φ := 𝟙 A'.left) (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (pull_isLB hL φ) hL' ((isGen_iff w).1 hw) (fun U hU => ⟨U, hU, fun _ hy => hy⟩) h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem abLocus_eq_range (Y : Model Xo c (RingHom.id c.F)) : abLocus Y.t.G = Set.range Y.j := by
  refine Set.Subset.antisymm (fun x hx => ?_) (GenFan.Tri.range_j_subset_abLocus Y)
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  obtain ⟨z, rfl⟩ := (pullback.fst Y.s (spMap (RingHom.id c.F))).surjective x
  have hz : z ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hx
  obtain ⟨w, rfl⟩ := hz
  exact ⟨w, rfl⟩

theorem pol_of_fac {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S S' : Scheme.{0}} {χ : S ⟶ Y.X}
    {t : SAB H S} (m : SABMap t Y.t χ) (x : S' ⟶ S) (y : S' ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) :
    RelAmple ((Over.pullback x).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom x)) ∧
      KTriv ((Over.pullback x).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom x)) := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H S') (p : S' ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  have e := LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃
  have := Y.oF.proper
  refine ⟨relAmple_of_lbIso_pull m₃.cart.1 Y.oF.t.PP.isLB hL e Y.oF.ample, ?_⟩
  obtain ⟨w, hw⟩ := e
  exact kTriv_pull m₃.cart Y.oF.t.PP.isLB hL ((isGen_iff w).1 hw) Y.oF.ktriv

theorem abLocus_eq_and_pol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : Scheme.{0}) (π : T ⟶ Y.X) (t : SAB H T), Nonempty (SABMap t Y.t π) → abLocus t.G = π ⁻¹' Set.range Y.j ∧ IsOpen (abLocus t.G) ∧ ∀ W : T.Opens, (W : Set T) ⊆ abLocus t.G → RelAmple ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) := by
  rintro E _ _ _ H Dw l Xo c Y T π t ⟨m⟩
  have hj := GenFan.Tri.isOpenImmersion_j_id Y
  have h₁ : abLocus t.G = π ⁻¹' Set.range Y.j := by
    ext x
    rw [← abLocus_eq_range Y]
    exact (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).symm
  refine ⟨h₁, ?_, fun W hW => ?_⟩
  · rw [h₁]
    exact Y.j.isOpenEmbedding.isOpen_range.preimage π.continuous
  · have hr : Set.range (W.ι ≫ π) ⊆ Set.range Y.j := by
      rintro _ ⟨w, rfl⟩
      have hw : w.1 ∈ π ⁻¹' Set.range Y.j := h₁ ▸ hW w.2
      exact hw
    exact pol_of_fac Y m W.ι (IsOpenImmersion.lift Y.j (W.ι ≫ π) hr) (IsOpenImmersion.lift_fac _ _ _)

end GlobalTheory.ModelAbLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : Scheme.{0}) (π : T ⟶ Y.X) (t : SAB H T), Nonempty (SABMap t Y.t π) → abLocus t.G = π ⁻¹' Set.range Y.j ∧ IsOpen (abLocus t.G) ∧ ∀ W : T.Opens, (W : Set T) ⊆ abLocus t.G → RelAmple ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) := by
  first | exact @GlobalTheory.ModelAbLocus.abLocus_eq_and_pol | exact GlobalTheory.ModelAbLocus.abLocus_eq_and_pol | (intros; apply GlobalTheory.ModelAbLocus.abLocus_eq_and_pol <;> assumption)
end
end
