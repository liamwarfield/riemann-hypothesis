module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeGramComplexConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace PositivityTheory.Xgn.HodgeGramConjugation

open scoped CategoryTheory.Obj

theorem val_spMap {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (σ : R →+* R') (x : Sp R ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (((spMap σ ≫ x).appLE U ⊤ h').hom f) =
      σ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)) := by
  have e := Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top
  have e' : (spMap σ).appLE ⊤ ⊤ le_top = (spMap σ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [← e, e']
  exact congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem appLE_comp {T X Y : Scheme.{0}} (x : T ⟶ Y) (ψ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ ψ ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((x ≫ ψ).appLE U ⊤ h').hom f = (x.appLE V ⊤ h).hom ((ψ.appLE U V e).hom f) := by
  rw [← Scheme.Hom.appLE_comp_appLE x ψ U V ⊤ e h]
  rfl

theorem top_le_invol {T X : Scheme.{0}} {c : T ⟶ T} (hc : c ≫ c = 𝟙 T) (x : T ⟶ X) (U : X.Opens) :
    ⊤ ≤ (c ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have k : ∀ y : T ⟶ X, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ (c ≫ y) ⁻¹ᵁ U := fun y hy t _ => hy (show c t ∈ (⊤ : T.Opens) from trivial)
  refine ⟨fun h => ?_, k x⟩
  have := k _ h
  rwa [← Category.assoc, hc, Category.id_comp] at this

abbrev cj : Sp ℂ ⟶ Sp ℂ := spMap (starRingEnd ℂ)

abbrev dj : Sp (DualNumber ℂ) ⟶ Sp (DualNumber ℂ) := spMap (dualMap (starRingEnd ℂ))

theorem cj_cj : cj ≫ cj = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext z
  simp

theorem dj_dj : dj ≫ dj = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  show dualMap (starRingEnd ℂ) (dualMap (starRingEnd ℂ) z) = z
  ext <;> simp [dualMap]

theorem dj_eps : dj ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  show dualMap (starRingEnd ℂ) (algebraMap ℂ (DualNumber ℂ) z) = algebraMap ℂ (DualNumber ℂ) (starRingEnd ℂ z)
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem valAt'_cj {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (cj ≫ x) U f = star (valAt' x U f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [dite_eq_left h, dite_eq_left ((top_le_invol cj_cj x U).2 h)]
    exact val_spMap _ x U h _ f
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ((top_le_invol cj_cj x U).1 h')), star_zero]

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (x ≫ ψ) U f = valAt' x (ψ ⁻¹ᵁ U) ((ψ.appLE U _ le_rfl).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)
  · rw [dite_eq_left h, dite_eq_left (show ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U from h)]
    unfold valAt
    rw [appLE_comp x ψ U _ le_rfl h]
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U from h)]

theorem top_le_pull {T X Y : Scheme.{0}} (L : LB X) (x : T ⟶ Y) (ψ : Y ⟶ X) (J : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull ψ).U J ↔ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (J PUnit.unit) :=
  ⟨fun h t ht => (mem_pull (F := ψ) (x := x t)).1 (h ht), fun h t ht => (mem_pull (F := ψ) (x := x t)).2 (h ht)⟩

theorem valAt'_pull_g {X Y : Scheme.{0}} (L : LB X) (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ X) (I J : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U I ⊓ (L.pull ψ).U J)) :
    valAt' x ((L.pull ψ).U I ⊓ (L.pull ψ).U J) ((L.pull ψ).g I J).val =
      valAt' (x ≫ ψ) (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) (L.g (I PUnit.unit) (J PUnit.unit)).val := by
  have le : (L.pull ψ).U I ⊓ (L.pull ψ).U J ≤ ψ ⁻¹ᵁ (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) := fun t ht => le (h ht)
  unfold valAt'
  rw [dite_eq_left h, dite_eq_left h']
  unfold valAt
  rw [appLE_comp x ψ _ _ le h h']
  congr 2
  have e : (L.pull ψ).g I J = res le (pullU ψ _ (L.g (I PUnit.unit) (J PUnit.unit))) := by
    have k : ∀ {M : Type} [CommGroup M] (a : PUnit.{1} → M), ∏ i, a i ^ (1 : ℤ) = a PUnit.unit := fun a => by
      rw [Fintype.prod_unique, zpow_one]
    exact k (fun _ => res le (pullU ψ _ (L.g (I PUnit.unit) (J PUnit.unit))))
  rw [e]
  rfl

theorem diffOn_star {g : ℕ} {F : (Fin g → ℂ) → ℂ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) (hF : DifferentiableOn ℂ F s) :
    DifferentiableOn ℂ (fun z => star (F (star z))) {z | star z ∈ s} := by
  intro z hz
  have := (hF.differentiableAt (hs.mem_nhds hz)).star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

theorem fderiv_star_star {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (fun z => star (F (star z))) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases h : DifferentiableAt ℂ F 0
  · have := h.hasFDerivAt.star_star
    rw [star_zero] at this
    have e := this.fderiv
    change fderiv ℂ (star ∘ F ∘ star) 0 (star w) = _
    rw [e]
    simp
  · have h' : ¬ DifferentiableAt ℂ (fun z => star (F (star z))) (0 : Fin g → ℂ) := fun h' => h (by
      have := h'.star_star
      rw [star_zero] at this
      have e : (star ∘ (fun z => star (F (star z))) ∘ star) = F := by
        ext z
        simp
      rwa [e] at this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

theorem lbIso_refl {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) : LBIso M M := by
  refine ⟨⟨fun p => M.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_div M M (𝟙 X) y p q hy)
    (gm_res _ y _ hy _)).trans ?_)))
  have e₁ := gm_cocycle hM (𝟙 X) y (i := p.1) (j := q.1) (k := q.2) hy.1.1 hy.2.1 hy.2.2
  have e₂ := gm_cocycle hM (𝟙 X) y (i := p.1) (j := p.2) (k := q.2) hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (M.g p.1 q.1) * (gm (𝟙 X) y _ (M.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (M.g q.1 q.2) =
    gm (𝟙 X) y _ (M.g p.1 p.2)
  rw [mul_right_comm, e₁, ← e₂, mul_inv_cancel_right]

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem inv_comm (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h A') (𝟙 A'))
  have e₁ : (𝟙 A' : A' ⟶ A')⁻¹ = GrpObj.inv := by rw [Hom.inv_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  rw [Hom.inv_def, Over.comp_left]
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem rigid_pull [IsCommMonObj A] [IsCommMonObj A'] (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : Out.Rigidified A L) :
    Out.Rigidified A' (L.pull φ) := by
  obtain ⟨t, ht⟩ := hL
  exact gen_chartPull (chartPullLinComb L φ (fun _ : PUnit => eSec A') (fun _ => eSec A) (fun _ => 1) f
    fun _ => (cubeMapOf h).e_comm) t ht

theorem sym_pull (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : Out.Sym A L) : Out.Sym A' (L.pull φ) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hL (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ := Scheme.Hom.resLE_comp_ι φ le
  refine gen_chartPull (chartPullLinComb L φ _ _ _ (φ.resLE _ _ le) fun k => ?_) t ht
  fin_cases k
  · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
    rw [Category.assoc, inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
  · exact hψ.symm

end Grp

def pullPol {S : Scheme.{0}} {K : Type} [Field K] (f : Sp K ⟶ S) (P : Out.PolAV S) : Out.PolAV (Sp K) where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)).of_isPullback (.of_hasPullback _ f) P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := rigid_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample := (amplePt S K f P.A _ _ (isGrpPullback_pullback P.A f) P.L _ P.isLB (pull_isLB P.isLB _)
    (lbIso_refl (pull_isLB P.isLB _)) P.ample P.ktriv).1
  ktriv := (amplePt S K f P.A _ _ (isGrpPullback_pullback P.A f) P.L _ P.isLB (pull_isLB P.isLB _)
    (lbIso_refl (pull_isLB P.isLB _)) P.ample P.ktriv).2

section Conj

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} [IsIso φ]

theorem inv_hom (h : IsGrpPullback A' A cj φ) : inv φ ≫ A'.hom = A.hom ≫ cj := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, h.1.w, Category.assoc, cj_cj, Category.comp_id]

def twPt (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) : 𝟙_ (Over (Sp ℂ)) ⟶ A' :=
  Over.homMk (cj ≫ y.left ≫ inv φ) (by
    have e : y.left ≫ A.hom = 𝟙 _ := Over.w y
    show (cj ≫ y.left ≫ inv φ) ≫ A'.hom = 𝟙 _
    rw [Category.assoc, Category.assoc, inv_hom h, reassoc_of% e, cj_cj])

theorem twPt_left (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    (twPt h y).left = cj ≫ y.left ≫ inv φ := rfl

theorem twPt_comp (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    (twPt h y).left ≫ φ = cj ≫ y.left := by
  rw [twPt_left]
  erw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem twPt_mul (h : IsGrpPullback A' A cj φ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    twPt h (x * y) = twPt h x * twPt h y := by
  let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ cj) ⟶ 𝟙_ (Over (Sp ℂ)) :=
    Over.homMk cj ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e := h.2 _ (twPt h x) (twPt h y) (U ≫ x) (U ≫ y) (twPt_comp h x).symm (twPt_comp h y).symm
  rw [← MonObj.comp_mul] at e
  refine Over.OverMorphism.ext ((cancel_mono φ).1 ?_)
  exact (twPt_comp h _).trans e

theorem twPt_inj (h : IsGrpPullback A' A cj φ) : Function.Injective (twPt h) := by
  intro x y e
  have e₁ : cj ≫ x.left = cj ≫ y.left := by rw [← twPt_comp h, ← twPt_comp h, e]
  have e₂ := congrArg (cj ≫ ·) e₁
  simp only [← Category.assoc, cj_cj, Category.id_comp] at e₂
  exact Over.OverMorphism.ext e₂

theorem twPt_surj (h : IsGrpPullback A' A cj φ) : Function.Surjective (twPt h) := by
  intro y
  have e : y.left ≫ A'.hom = 𝟙 _ := Over.w y
  refine ⟨Over.homMk (cj ≫ y.left ≫ φ) ?_, Over.OverMorphism.ext ?_⟩
  · show (cj ≫ y.left ≫ φ) ≫ A.hom = 𝟙 _
    rw [Category.assoc, Category.assoc, h.1.w, reassoc_of% e, cj_cj]
  · show cj ≫ (cj ≫ y.left ≫ φ) ≫ inv φ = y.left
    rw [Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id, ← Category.assoc, cj_cj, Category.id_comp]

theorem twPt_eq_one (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) : twPt h y = 1 ↔ y = 1 :=
  map_eq_one_iff (MonoidHom.mk' (twPt h) (twPt_mul h)) (twPt_inj h)

def conjLat {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin g → ℂ) where
  carrier := {z | star z ∈ Λ}
  add_mem' ha hb := by
    show star (_ + _) ∈ Λ
    rw [star_add]; exact Λ.add_mem ha hb
  zero_mem' := by
    show star (0 : Fin g → ℂ) ∈ Λ
    rw [star_zero]; exact Λ.zero_mem
  smul_mem' c z hz := by
    show star (c • z) ∈ Λ
    rw [star_zsmul]; exact Λ.smul_mem c hz

theorem top_le_tw (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A'.left.Opens) :
    ⊤ ≤ (twPt h y).left ⁻¹ᵁ U ↔ ⊤ ≤ y.left ⁻¹ᵁ (inv φ ⁻¹ᵁ U) :=
  top_le_invol cj_cj (y.left ≫ inv φ) U

theorem valAt'_tw (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A'.left.Opens) (f : Γ(A'.left, U)) :
    valAt' (twPt h y).left U f = star (valAt' y.left (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f)) :=
  (valAt'_cj (y.left ≫ inv φ) U f).trans (congrArg star (valAt'_comp y.left (inv φ) U f))

theorem top_le_tw_pull (h : IsGrpPullback A' A cj φ) (L : LB A.left) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (J : PUnit → L.ι) :
    ⊤ ≤ (twPt h y).left ⁻¹ᵁ (L.pull φ).U J ↔ ⊤ ≤ y.left ⁻¹ᵁ L.U (J PUnit.unit) := by
  refine (top_le_pull L (twPt h y).left φ J).trans ?_
  rw [twPt_comp]
  exact top_le_invol cj_cj y.left _

def conjUnif (h : IsGrpPullback A' A cj φ) {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : HolUnif A' (L.pull φ) g where
  ex z := twPt h (u.ex (star z))
  ex_add z w := by rw [star_add, u.ex_add, twPt_mul]
  ex_onto := (twPt_surj h).comp (u.ex_onto.comp star_involutive.surjective)
  Λ := conjLat u.Λ
  ker z := (twPt_eq_one h _).trans (u.ker _)
  discrete := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (β := u.Λ) (f := fun z => ⟨star z.1, z.2⟩)
      (Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _) ?_
    intro a b e
    exact Subtype.ext (star_injective (congrArg Subtype.val e))
  full := by
    have k : ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)),
        star w ∈ Submodule.span ℝ (conjLat u.Λ : Set (Fin g → ℂ)) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (show star (star x) ∈ u.Λ by rw [star_star]; exact hx)
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [star_smul, star_trivial a]; exact Submodule.smul_mem _ _ hx
    refine eq_top_iff.2 fun z _ => ?_
    have := k (star z) (by rw [u.full]; trivial)
    rwa [star_star] at this
  hol U f := by
    obtain ⟨h₁, h₂⟩ := u.hol (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f)
    simp only [top_le_tw, valAt'_tw]
    exact ⟨h₁.preimage continuous_star, diffOn_star h₁ h₂⟩
  fr J z := star (u.fr (J PUnit.unit) (star z))
  fr_hol J := by
    exact (diffOn_star (u.hol _ 0).1 (u.fr_hol (J PUnit.unit))).mono
      fun z hz => (top_le_tw_pull h L _ J).1 hz
  fr_ne J z hz := star_ne_zero.2 (u.fr_ne _ _ ((top_le_tw_pull h L _ J).1 hz))
  fr_compat I J z hz := by
    have hI := (top_le_tw_pull h L _ I).1 (fun t ht => (hz ht).1)
    have hJ := (top_le_tw_pull h L _ J).1 (fun t ht => (hz ht).2)
    rw [u.fr_compat _ (J PUnit.unit) (star z) (fun t ht => ⟨hI ht, hJ ht⟩), star_mul']
    congr 1
    refine Eq.symm ((valAt'_pull_g L _ φ I J hz).trans ?_)
    rw [twPt_comp]
    exact valAt'_cj _ _ _

theorem form_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ (Hm.map star).mulVec (star w) = star (star z ⬝ᵥ Hm.mulVec (star (star w))) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

theorem conj_isAH (h : IsGrpPullback A' A cj φ) {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (H : u.IsAH Hm χ) :
    (conjUnif h u).IsAH (Hm.map star) (fun l => star (χ ⟨star l.1, l.2⟩)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := H
  refine ⟨h₁.map _ (fun _ => rfl), fun z hz => ?_, fun l => by rw [norm_star, h₃], fun l J z hz => ?_⟩
  · rw [form_star, Complex.star_def, Complex.conj_re]
    exact h₂ _ (star_ne_zero.2 hz)
  · have e := h₄ ⟨star l.1, l.2⟩ (J PUnit.unit) (star z) ((top_le_tw_pull h L _ J).1 hz)
    show star (u.fr _ (star z)) = _ * star (u.fr _ (star (z + l.1)))
    rw [e, form_star, form_star, star_add]
    simp only [Complex.star_def, map_mul, ← Complex.exp_conj, map_add (f := _), map_div₀, Complex.conj_ofReal, map_ofNat]

def twVec (h : IsGrpPullback A' A cj φ) (v : epsR ℂ ⟶ A) : epsR ℂ ⟶ A' :=
  Over.homMk (dj ≫ v.left ≫ inv φ) (by
    have e : v.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
    show (dj ≫ v.left ≫ inv φ) ≫ A'.hom = spMap (algebraMap ℂ (DualNumber ℂ))
    rw [Category.assoc, Category.assoc, inv_hom h, reassoc_of% e, reassoc_of% dj_eps, cj_cj, Category.comp_id])

theorem twVec_comp (h : IsGrpPullback A' A cj φ) (v : epsR ℂ ⟶ A) : (twVec h v).left ≫ φ = dj ≫ v.left := by
  show (dj ≫ v.left ≫ inv φ) ≫ φ = _
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem conj_isDiff (h : IsGrpPullback A' A cj φ) {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (H : u.IsDiff w v) : (conjUnif h u).IsDiff (star w) (twVec h v) := by
  intro U hU f
  have hU' : ⊤ ≤ (v.left ≫ inv φ) ⁻¹ᵁ U := (top_le_invol dj_dj (v.left ≫ inv φ) U).1 hU
  have e := H (inv φ ⁻¹ᵁ U) hU' (((inv φ).appLE U _ le_rfl).hom f)
  have e₁ := val_spMap (dualMap (starRingEnd ℂ)) (v.left ≫ inv φ) U hU' hU f
  have e₂ := appLE_comp v.left (inv φ) U _ le_rfl hU' hU' f
  have e₃ : (fun z => valAt' ((conjUnif h u).ex z).left U f) =
      fun z => star (valAt' (u.ex (star z)).left (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f)) :=
    funext fun z => valAt'_tw h _ U f
  rw [e₃]
  refine Eq.trans ?_ ((congrArg star e).trans (fderiv_star_star _ w).symm)
  refine (congrArg TrivSqZeroExt.snd e₁).trans ?_
  rw [e₂]
  simp [dualMap]

end Conj

end PositivityTheory.Xgn.HodgeGramConjugation

end

open PositivityTheory.Xgn.HodgeGramConjugation in
theorem PositivityTheory.Xgn.hodge_gram_complex_conjugate_alt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  intro S G _ L x x' k v v' Γ hx hv ⟨Q, ψ, t, u, Hm, χ, W, hψ, hL, hAH, ht, hΓ⟩
  have : IsIso cj := ⟨cj, cj_cj, cj_cj⟩
  have h : IsGrpPullback (pullPol cj Q).A Q.A cj (pullback.fst Q.A.hom cj) := isGrpPullback_pullback Q.A cj
  have : IsIso (X := (pullPol cj Q).A.left) (pullback.fst Q.A.hom cj) :=
    inferInstanceAs (IsIso (pullback.fst Q.A.hom cj))
  refine ⟨pullPol cj Q, pullback.fst Q.A.hom cj ≫ ψ, fun i => twVec h (t i), conjUnif h u, Hm.map star, _,
    fun i => star (W i), (h.comp hψ).congr hx.symm rfl, ?_, conj_isAH h u hAH,
    fun i => ⟨?_, conj_isDiff h u (ht i).2⟩, fun i j => ?_⟩
  · exact hL.chartPull (chartPullSame L _ _ _ (pullback.fst Q.A.hom cj) fun _ => rfl) (chartPullPull Q.L _ _ rfl)
  · rw [hv, ← (ht i).1]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (twVec_comp h (t i))).trans (Category.assoc _ _ _))
  · have e : hermForm (Hm.map star) (star (W i)) (star (W j)) = star (hermForm Hm (W i) (W j)) := by
      unfold hermForm
      rw [form_star]
      simp only [star_star]
    refine Eq.trans ?_ (congrArg ((Real.pi : ℂ) * ·) e).symm
    rw [Matrix.map_apply, hΓ, star_mul', Complex.star_def, Complex.conj_ofReal]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZero
theorem UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re * H.rt0.im = 0 := by linarith
  have hr : H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InfNormConjugateInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  exact @PositivityTheory.Xgn.hodge_gram_complex_conjugate_alt

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_conjugate : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InfNormConjugateInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

open _root_.GlobalTheory.CompanionTheory.Ar (dualMap)

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_spMap_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B)
    {T : Scheme.{0}} (g : Sp A ⟶ T) : spMap a ≫ spMap b ≫ g = spMap (a.comp b) ≫ g := by
  rw [← Category.assoc, spMap_spMap]

theorem spMap_idR (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ :=
  Spec.map_id (CommRingCat.of A)

theorem algebraMap_dual (a : R) : algebraMap R (DualNumber R) a = TrivSqZeroExt.inl a := rfl

theorem dualMap_comp_algebraMap (f : R →+* R) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R (DualNumber R)).comp f := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_epsMul (f : R →+* R) (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  ext a <;> simp [dualMap, epsMul, algebraMap_dual]

theorem fst_comp_dualMap (f : R →+* R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_dualMap (f : R →+* R) (hf : ∀ a, f (f a) = a) :
    (dualMap f).comp (dualMap f) = RingHom.id _ := by
  ext a <;> simp [dualMap, hf, algebraMap_dual]

def trM (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) : epsAt x' ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    subst hx
    change spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap R (DualNumber R)) ≫ spMap f ≫ x
    rw [spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_algebraMap])

def tr (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  trM f hx ≫ v

theorem tr_left (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) :
    (tr f hx v).left = spMap (dualMap f) ≫ v.left := rfl

variable {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S}

theorem tr_mul (f : R →+* R) (hx : x' = spMap f ≫ x) (a b : epsAt x ⟶ G) :
    tr f hx (a * b) = tr f hx a * tr f hx b :=
  MonObj.comp_mul _ _ _

theorem tr_one (f : R →+* R) (hx : x' = spMap f ≫ x) : tr f hx (1 : epsAt x ⟶ G) = 1 := by
  rw [tr, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (trM f hx ≫ toUnit _) (toUnit _)]

def trHom (f : R →+* R) (hx : x' = spMap f ≫ x) : (epsAt x ⟶ G) →* (epsAt x' ⟶ G) where
  toFun := tr f hx
  map_one' := tr_one f hx
  map_mul' := tr_mul f hx

theorem tr_prod (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    tr f hx (List.ofFn u).prod = (List.ofFn fun i => tr f hx (u i)).prod := by
  have := map_list_prod (trHom (G := G) f hx) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact this

theorem isTanAt_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {v : epsAt x ⟶ G} (h : IsTanAt G x v) :
    IsTanAt G x' (tr f hx v) := by
  have h1 : (1 : Over.mk x' ⟶ G) = (Over.homMk (spMap f) hx.symm : Over.mk x' ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  unfold IsTanAt at h ⊢
  rw [h1, Over.comp_left, ← h, tr_left]
  change spMap _ ≫ spMap (dualMap f) ≫ v.left = spMap f ≫ spMap _ ≫ v.left
  rw [spMap_spMap_assoc, spMap_spMap_assoc, fst_comp_dualMap]

theorem isEigVec_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hx : x' = spMap f ≫ x) {τ : O →+* R}
    {v : epsAt x ⟶ G} (h : IsEigVec act x τ v) : IsEigVec act x' (f.comp τ) (tr f hx v) := by
  refine ⟨isTanAt_tr f hx h.1, fun a => ?_⟩
  have h2 : (tr f hx v ≫ act.act a).left = spMap (dualMap f) ≫ (v ≫ act.act a).left := by
    rw [tr, Category.assoc]; rfl
  rw [h2, h.2 a, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem isComb_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsAt x ⟶ G)}
    {w : epsAt x ⟶ G} (h : IsComb c v w) : IsComb (fun i => f (c i)) (fun i => tr f hx (v i)) (tr f hx w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => tr f hx (u i), fun i => ?_, tr_prod f hx u⟩
  rw [tr_left, hu, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem back (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) : x = spMap f ≫ x' := by
  have : f.comp f = RingHom.id R := RingHom.ext hf
  rw [hx, spMap_spMap_assoc, this, spMap_idR, Category.id_comp]

theorem tr_tr (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) (hx' : x = spMap f ≫ x')
    (v : epsAt x ⟶ G) : tr f hx' (tr f hx v) = v := by
  apply Over.OverMorphism.ext
  rw [tr_left, tr_left, spMap_spMap_assoc, dualMap_comp_dualMap f hf, spMap_idR, Category.id_comp]

theorem isEigFrame_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hf : ∀ a, f (f a) = a)
    (hx : x' = spMap f ≫ x) {τ : O →+* R} {n : ℕ} {v : Fin n → (epsAt x ⟶ G)} (h : IsEigFrame act x τ v) :
    IsEigFrame act x' (f.comp τ) (fun i => tr f hx (v i)) := by
  have hx' := back f hf hx
  refine ⟨fun i => isEigVec_tr act f hx (h.1 i), fun w hw => ?_⟩
  have hw0 : IsEigVec act x τ (tr f hx' w) := by
    have := isEigVec_tr act f hx' hw
    have e : f.comp (f.comp τ) = τ := RingHom.ext fun a => hf _
    rwa [e] at this
  obtain ⟨c, hc, hu⟩ := h.2 _ hw0
  refine ⟨fun i => f (c i), ?_, fun c' hc' => ?_⟩
  · have := isComb_tr f hx hc
    rwa [tr_tr f hf hx' hx] at this
  · have h3 := isComb_tr f hx' hc'
    simp only [tr_tr f hf hx hx'] at h3
    have h4 := hu _ h3
    funext i
    rw [← h4]
    exact (hf _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

namespace GlobalTheory.CompanionTheory.Ar.Flat


open ConjPt in
theorem hasInfNorm_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  intro E _ _ _ H D l Xo c U τ φ s t hl hs y v w Γ Δ hfr hΓ hΔ
  have hcc : ∀ z : ℂ, (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := fun z => Complex.conj_conj z
  obtain ⟨h1, h2, h3, h4⟩ := hfr
  have hy : under (spMap (starRingEnd ℂ) ≫ y) = spMap (starRingEnd ℂ) ≫ under y := Category.assoc _ _ _
  have hcomp : ∀ {A : Type} [CommRing A] (g : A →+* ℂ), (starRingEnd ℂ).comp ((starRingEnd ℂ).comp g) = g :=
    fun g => RingHom.ext fun a => hcc _
  let v' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.p := fun i => tr (starRingEnd ℂ) hy (v i)
  let w' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.q := fun i => tr (starRingEnd ℂ) hy (w i)
  have hfr' : IsFramed U τ s (spMap (starRingEnd ℂ) ≫ y) v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h1, spMap_spMap, hcomp]
    · rintro _ ⟨a, rfl⟩
      exact h2 ⟨(spMap (starRingEnd ℂ)) a, by simp⟩
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h3
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c τ)) = s.comp (tauIn c τ) :=
        RingHom.ext fun a => hcc _
      rwa [e] at this
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h4
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c (ComplexEmbedding.conjugate τ))) =
          s.comp (tauIn c (ComplexEmbedding.conjugate τ)) := RingHom.ext fun a => hcc _
      rwa [e] at this
  have hΓ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ v v' Γ hy (fun a => tr_left _ hy _) hΓ
  have hΔ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ w w' Δ hy (fun a => tr_left _ hy _) hΔ
  have hnat := hl.nat ℂ ℂ (starRingEnd ℂ) ((starRingEnd ℂ).comp s) y v w (spMap (starRingEnd ℂ) ≫ y) v' w'
    ⟨h1, h2, h3, h4⟩ rfl (fun i => tr_left _ hy _) (fun i => tr_left _ hy _)
  have hm := hs _ v' w' _ _ hfr' hΓ' hΔ'
  have hdet : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), ‖(M.map star).det‖ = ‖M.det‖ := by
    intro n M
    have : (M.map star).det = (starRingEnd ℂ) M.det := by
      rw [RingHom.map_det]; rfl
    rw [this, RCLike.norm_conj]
  rw [hnat, RCLike.norm_conj, hdet, hdet] at hm
  exact hm

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InfNormConjugateInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_norm_conjugate_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero H

theorem tauIn_rt_eq (τ : E →+* ℂ) (σ : c.F →+* ℂ) :
    σ (tauIn c τ H.rt) = H.rt0 ∨ σ (tauIn c τ H.rt) = -H.rt0 := by
  have h : (σ (tauIn c τ H.rt)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, H.sqrt_neg_disc_sq]; simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem gram_det_ne_zero {τ : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    {y : Sp ℂ ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {Γ : Matrix (Fin D.p) (Fin D.p) ℂ}
    (hf : IsFramed Set.univ τ σ y v w) (hΓ : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ) :
    Γ.det ≠ 0 := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hf.1, ← Spec.map_comp]; rfl
  obtain ⟨i, P, hP, hu⟩ := FU.onto _ hs
  obtain ⟨V, hV, hli, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y)
    (σ.comp (tauIn c τ)) (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) D.p v hP hu.symm (fun a => rfl)
    hf.2.2.1
  obtain ⟨Hm, hH, hpos, him⟩ := hP.2.2.2.2
  have hG := (hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hH him (under y) hu.symm D.p v V Γ
    (fun a => (hV a (V a)).2 rfl)).1 hΓ
  let M : Matrix (Fin D.p) (Fin g) ℂ := Matrix.of V
  have hΓM : Γ = (Real.pi : ℂ) • (M * Hm * M.conjTranspose) := by
    ext a b
    rw [hG a b, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, M,
      Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set z := Matrix.vecMul (star x) M with hz
  have hq : dotProduct (star x) (Γ.mulVec x) = (Real.pi : ℂ) * hermForm Hm z z := by
    rw [hΓM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hermForm, hz, Matrix.star_vecMul, star_star,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hx, dotProduct_zero] at hq
  have hz0 : z = 0 := by
    by_contra hne
    have := hpos z hne
    have h2 : (hermForm Hm z z) = 0 := by
      rcases mul_eq_zero.1 hq.symm with h | h
      · exact absurd h (by exact_mod_cast Real.pi_ne_zero)
      · exact h
    rw [h2] at this; simp at this
  have hinj : Function.Injective M.vecMul := Matrix.vecMul_injective_iff.2 hli
  have : star x = 0 := hinj (show Matrix.vecMul (star x) M = Matrix.vecMul 0 M by rw [← hz, hz0, Matrix.zero_vecMul])
  exact hx0 (by simpa using this)

theorem exists_infNorm_of_rt (hR : Geo.ResK.ResKStatement) (hG : GagaSections) {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {τ : E →+* ℂ} {φ : FrameFn Xo c}
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hr : 1 ≤ D.p + D.q) (hτ : τ (H.rt : E) = H.rt0) (hZ : Z.IsGeom) (hl : IsLineFn U τ φ)
    (hm : FlatOnModel Z τ φ) (σ : c.F →+* ℂ) (hσ : σ (tauIn c τ H.rt) = H.rt0) :
    ∃ t : ℝ, HasInfNorm U τ φ σ t := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hK : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
    have e : (IntermediateField.inclusion c.le) (baseKA l).ρ = tauIn c τ H.rt :=
      Subtype.ext (show H.rt0 = τ (H.rt : E) from hτ.symm)
    show σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0
    rw [e, hσ]
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.T.abelianScheme_laws_unconditional.1 E H D l Xo _ g ty hr hK hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) σ g ty FU
    hty hσ (fun a => rfl)
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ σ Φ φ hβ hr hτ hσ hZ hΦ hl hm
  refine ⟨Real.log ‖κ‖, fun y v w Γ Δ hf h1 h2 => ?_⟩
  have hf' : IsFramed Set.univ τ σ y v w := ⟨hf.1, Set.subset_univ _, hf.2.2⟩
  have hΓ : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 (gram_det_ne_zero FU hf' h1)
  have hΦ0 : ‖Φ y v w‖ ≠ 0 := norm_ne_zero_iff.2 (hΦ.ne y v w hf')
  have hn := congrArg Real.log (hΦ.norm y v w Γ Δ hf' h1 h2)
  rw [Real.log_mul (pow_ne_zero 2 hΦ0) hΓ, Real.log_pow] at hn
  rw [hκ y v w hf, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hκ0) hΦ0]
  push_cast at hn
  linarith

theorem flat_first_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → FlatLineGeneratorComponent := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y U Z τ φ hβ hr hτ hZ hl hm
  have key : ∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t := by
    intro s
    rcases tauIn_rt_eq (c := c) (H := H) τ s with h | h
    · exact exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm s h
    · obtain ⟨t, ht⟩ := exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm ((starRingEnd ℂ).comp s)
        (by rw [RingHom.comp_apply, h, map_neg, rt0_conj_neg_ne_zero, neg_neg])
      refine ⟨t, ?_⟩
      have := GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ _ t hl ht
      rwa [show (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s from RingHom.ext fun x => by simp] at this
  refine ⟨fun s => ?_, fun g ty FU i hty hmem => ?_⟩
  · obtain ⟨t, ht⟩ := key s
    exact ⟨t, ht, GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ s t hl ht⟩
  · obtain ⟨Φ, hΦ, hfl⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun a => rfl)
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ (algebraMap c.F ℂ) Φ φ hβ hr hτ hτ hZ hΦ hl hm
    obtain ⟨e, ρ, -, he, hρ⟩ := hfl i
    refine ⟨hmem, hl, e, κ * ρ, he, ?_⟩
    intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
    rw [hκ y v w h3, _root_.mul_assoc, hρ P y v w V W C Fm B h1 h2 ⟨h3.1, Set.subset_univ _, h3.2.2⟩ h4 h5 h6 h7 h8]

end GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_first_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGeneratorComponent := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga <;> assumption)
end
