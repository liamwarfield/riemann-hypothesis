module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.VeryAmplePull

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem cst_eq_appLE (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) :
    cst f W r = (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rfl

theorem appLE_cst {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (D : X.Opens) (W : X'.Opens)
    (e : W ≤ φ ⁻¹ᵁ D) (r : R) : (φ.appLE D W e).hom (cst f D r) = cst f' W (g r) := by
  have e₁ : f.appLE ⊤ D le_top ≫ φ.appLE D W e =
      (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top ≫ f'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ f ⊤ D W le_top e).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE f' (Spec.map (CommRingCat.ofHom g)) ⊤ ⊤ W le_top le_top).symm)
    simp only [h]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  have e₃ : (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom g)).appTop :=
    (Scheme.Hom.app_eq_appLE (Spec.map (CommRingCat.ofHom g)) (U := ⊤)).symm
  rw [cst_eq_appLE, cst_eq_appLE]
  refine (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e₁).trans ?_
  rw [e₃]
  exact congrArg (f'.appLE ⊤ W le_top).hom (congrArg (fun q => q.hom r) e₂).symm

theorem closure_eq_top {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) [IsClosedImmersion (pullback.lift φ f' h)]
    {D : X.Opens} (hD : IsAffineOpen D) {W : X'.Opens} (e : W = φ ⁻¹ᵁ D) (T : Subring Γ(X', W))
    (h₁ : ∀ a, (φ.appLE D W e.le).hom a ∈ T) (h₂ : ∀ c, cst f' W c ∈ T) (x : Γ(X', W)) : x ∈ T := by
  have H := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
  set p := pullback.fst f (Spec.map (CommRingCat.ofHom g)) with hp
  set q := pullback.snd f (Spec.map (CommRingCat.ofHom g)) with hq
  set u := pullback.lift φ f' h with hu
  have up : u ≫ p = φ := pullback.lift_fst _ _ _
  have uq : u ≫ q = f' := pullback.lift_snd _ _ _
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have e' : W = u ⁻¹ᵁ (p ⁻¹ᵁ D) := by rw [e, ← up]; rfl
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := D) le_top le_top
      (UY := p ⁻¹ᵁ D) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hD)
  have hs : Function.Surjective (u.appLE (p ⁻¹ᵁ D) W e'.le).hom := by
    subst e'
    rw [← Scheme.Hom.app_eq_appLE]
    exact u.app_surjective _ (hD.preimage p)
  obtain ⟨y, rfl⟩ := hs x
  change y ∈ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom
  refine (show ⊤ ≤ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom from ?_) trivial
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · have e₁ := congrArg (fun k => k.hom d) (Scheme.Hom.appLE_comp_appLE u p D (p ⁻¹ᵁ D) W le_rfl e'.le)
    simp only [up] at e₁
    exact (congrArg (· ∈ T) e₁).mpr (h₁ d)
  · have e₁ := congrArg (fun k => k.hom c) (Scheme.Hom.appLE_comp_appLE u q ⊤ (p ⁻¹ᵁ D) W le_top e'.le)
    simp only [uq] at e₁
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c
    exact (congrArg (· ∈ T) e₁).mpr (h₂ c)

theorem veryAmpleBy_pull : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : X' ⟶ X) (h : φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g))), IsClosedImmersion (pullback.lift φ f' h) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull φ)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → VeryAmpleBy f' H' s' := by
  intro R _ X f H n s hP ⟨hcov, hs⟩ R' _ g X' f' φ h hcl H' W s' hP' _ hs'
  have : IsAffineHom φ := by
    have : IsAffineHom (pullback.fst f (Spec.map (CommRingCat.ofHom g))) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))).flip inferInstance
    rw [← pullback.lift_fst φ f' h]
    infer_instance
  have loc : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans
      (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (φ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (φ y)
      have e := hs' i y j k hj hk
      rw [gs_stalkMap φ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (φ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap φ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage φ, fun j => (φ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (φ y)
    have hm : φ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs φ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j y l k hl hy.2
    have e₂ := hs' i y l k hl hy.2
    have e₃ := (Geo.Tor.gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE φ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · intro x
    refine closure_eq_top h haff (loc i) (RingHom.range _) (fun d => ?_) (fun c => ?_) x
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map g p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (RingHom.ext fun c => (appLE_cst h _ _ _ c).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.AbLaw.VeryAmplePull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolExtension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CubTransport

theorem isCub_of_surjective {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (β : A' →* A) (hβ : Function.Surjective β) (h : IsCub (fun a b c => θ (β a) (β b) (β c))) : IsCub θ := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y
    simpa only [map_one] using h.face x y
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y; obtain ⟨z, rfl⟩ := hβ z
    exact h.s01 x y z
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y; obtain ⟨z, rfl⟩ := hβ z
    exact h.s12 x y z
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨x', rfl⟩ := hβ x'; obtain ⟨x'', rfl⟩ := hβ x''; obtain ⟨y, rfl⟩ := hβ y
    simpa only [map_mul] using h.coc x x' x'' y

theorem isCub_mul_diff {A U : Type} [CommGroup A] [CommGroup U] {θ θ' : A → A → A → U} (hθ : IsCub θ) (Ω : A → U)
    (h : ∀ a b c, θ' a b c = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ a b c) : IsCub θ' :=
  isCub_of_twist hθ (MonoidHom.id A) (fun a => (Ω a)⁻¹) fun a b c => by
    rw [h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, MonoidHom.id_apply]
    abel

section DVR

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]


omit [IsDomain V] [IsDiscreteValuationRing V] [GrpObj G] [IsCommMonObj G] in
theorem corr_of_generic_val [IsSeparated G.hom] (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    {L : LB G.left} (hL : L.IsLB) {I I' : Type} [Fintype I] [Fintype I']
    {φ : I → (T.left ⟶ G.left)} {ε : I → ℤ} {φ' : I' → (T.left ⟶ G.left)} {ε' : I' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (y : (pullback T.hom (etaK V K) :)) J, Good L y J →
      val t (pullback.fst T.hom (etaK V K)) y J = val t' (pullback.fst T.hom (etaK V K)) y J) :
    LB.Gen.Corr L _ _ _ _ t t' :=
  corr_of_generic_of_isSeparated V K G T L φ ε φ' ε' t t' (corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_pull hJ, Category.id_comp]
    exact H y J hJ)

theorem nonempty_cubical_of_generic [IsSeparated G.hom] [Flat G.hom] (L : RigLB G) (t : LB.Gen (Theta G L.L))
    (ht : t.IsGen)
    (h : ∀ (T : Over (Spec (CommRingCat.of K))) (z : T.left) (J), Good L.L z J →
      IsCub (thV t (T := Over.mk (T.hom ≫ etaK V K)) z J)) : Nonempty (CubicalStr G L) := by
  have f₂ : Flat (G2 G).hom := by
    show Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have f₃ : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (G2 G).hom ≫ G.hom)
    infer_instance
  have f₄ : Flat (G4 G).hom := by
    show Flat (pullback.fst G.hom (G3 G).hom ≫ G.hom)
    infer_instance
  let ρ : ∀ T : Over (Spec (CommRingCat.of V)), Over.mk (pullback.snd T.hom (etaK V K) ≫ etaK V K) ⟶ T := fun T =>
    Over.homMk (pullback.fst T.hom (etaK V K)) pullback.condition
  have v : ∀ (T : Over (Spec (CommRingCat.of V))) (y : (pullback T.hom (etaK V K) :)) J, Good L.L y J →
      ∀ a b c : T ⟶ G, val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift a (lift b c)).left)
        (pullback.fst T.hom (etaK V K)) y J =
        thV t (T := Over.mk (pullback.snd T.hom (etaK V K) ≫ etaK V K)) y J (ρ T ≫ a) (ρ T ≫ b) (ρ T ≫ c) := by
    intro T y J hJ a b c
    refine (val_pull hJ _ _ _).trans ?_
    rw [thV, ← comp_lift, ← comp_lift]; rfl
  have v' : ∀ (y : (pullback (G3 G).hom (etaK V K) :)) J,
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (pullback.fst (G3 G).hom (etaK V K)) y J =
        thV t (T := Over.mk (pullback.snd (G3 G).hom (etaK V K) ≫ etaK V K)) y J
          (ρ _ ≫ x3 G 0) (ρ _ ≫ x3 G 1) (ρ _ ≫ x3 G 2) := by
    intro y J
    have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
      ext <;> simp [x3]
    rw [thV, ← comp_lift, ← comp_lift, e, Category.comp_id]; rfl
  refine ⟨⟨t, ht, fun i => corr_of_generic_val (K := K) (G2 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G3 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G3 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G4 G) L.isLB fun y J hJ => ?_⟩⟩
  · refine Eq.trans ?_ (val_one _).symm
    have C := h (Over.mk (pullback.snd (G2 G).hom (etaK V K))) y J hJ
    have o : ρ (G2 G) ≫ pzero G _ = 1 := map_one (preHom (ρ (G2 G)))
    fin_cases i
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₂ _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₃ _ _)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom (etaK V K))) y J hJ).s01 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom (etaK V K))) y J hJ).s12 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · have C := h (Over.mk (pullback.snd (G4 G).hom (etaK V K))) y J hJ
    have m : ∀ a b : G4 G ⟶ G, ρ (G4 G) ≫ padd G a b = (ρ (G4 G) ≫ a) * (ρ (G4 G) ≫ b) := fun a b =>
      MonObj.comp_mul _ _ _
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).symm)
    rw [m, m]
    exact C.coc _ _ _ _

variable [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem nonempty_cubical (hE : cubical_extendsSt.{0}) (gp : IsGrpPullback A G (etaK V K) F) (L : RigLB G)
    {M : RigLB A} (c : CubicalStr A M) (w : LB.Iso M.L (L.L.pull F)) (hw : w.IsGen) :
    Nonempty (CubicalStr G L) := by
  have hp := gp.1
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff w).1 hw) L.isLB M.isLB (φ' := thφ A (x3 A)) (ε := thε) c.t c.isGen
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = genericFiberCubeInclusion V K G := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  let κ : (G3 A).left ⟶ pullback (G3 G).hom (etaK V K) := pullback.lift (cubeMapOf gp).F3 (G3 A).hom
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
  have κ₁ : κ ≫ genericFiberCubeInclusion V K G = (cubeMapOf gp).F3 := pullback.lift_fst _ _ _
  have κ₂ : κ ≫ l.left = 𝟙 _ := hom_ext_triple _ fun i => by
    rw [Category.assoc, ← Over.comp_left, lx, Category.id_comp]
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, hx, ← Category.assoc]
      exact (congrArg (· ≫ _) κ₁).trans (f3 i)
    · rw [Category.assoc, Over.w, Over.w]
      exact pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, v₂⟩ := exists_gen L.isLB (φ' := fun I => genericFiberCubeInclusion V K G ≫ thφ G (x3 G) I) (ε' := thε)
    (fun U _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (by
      show _ = genericFiberCubeInclusion V K G ≫ _
      rw [← hl, Category.assoc]
      exact congrArg (l.left ≫ ·) ((cubeMapOf gp).psum_comm I.down)))
    (LB.pullGen L.L _ _ t₁ l.left) (DVR.pullGen_isGen _ _ _ _ ht₁ _)
  have C : ∀ (T : Over (Spec (CommRingCat.of K))) (z : T.left) (J), Good L.L z J →
      IsCub (fun a b d : T ⟶ A => val t₂ ((lift a (lift b d)).left ≫ κ) z J) := by
    intro T z J hJ
    choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart M.isLB (χ z)
    refine isCub_mul_diff (isCub_cubV c hJ') (fun q => gw w q.left z (J (q.left ≫ F)) (J' q.left)) fun a b d => ?_
    refine (v₂ _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
    rw [Category.assoc, κ₂, Category.comp_id]
    refine (v₁ _ _ z _ _ (hJ.mem _ _) (Good.mem hJ' _ _)).trans (congrArg₂ (· * ·) (Eq.trans ?_
      (prod_cub a b d (fun q => gw w q z (J (q ≫ F)) (J' q)))) rfl)
    exact Finset.prod_congr rfl fun I _ => by rw [Category.assoc]
  have q : ∀ (T : Over (Spec (CommRingCat.of K))) (a b d : T ⟶ A), (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T d))).left := fun T a b d => hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  obtain ⟨t, ⟨ht, htt⟩, -⟩ := hE V K G ((lift (1 : 𝟙_ _ ⟶ A) (lift 1 1)).left ≫ κ) (by
      rw [Category.assoc, κ₁, q, map_one, CubeExtension.eSec_three]
      refine hom_ext_triple _ fun i => ?_
      rw [Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, Hom.one_def]) L t₂ (corr_of_val L.isLB fun y J hJ => by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
      rw [Category.id_comp]
      exact (C (𝟙_ _) y J hJ).face 1 1) ht₂
  refine nonempty_cubical_of_generic (K := K) L t ht fun T z J hJ => isCub_of_surjective (pushHom gp T) (fun a => ?_) ?_
  · exact ⟨Over.homMk (hp.lift a.left T.hom (Over.w a)) (hp.lift_snd _ _ _), Over.OverMorphism.ext (hp.lift_fst _ _ _)⟩
  · refine (congrArg IsCub (funext fun a => funext fun b => funext fun d => ?_)).mpr (C T z J hJ)
    rw [← htt]
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [Category.assoc, κ₁, q]
    rfl


omit [IsCommMonObj A] [QuasiCompact G.hom] in
theorem exists_symmetry (gp : IsGrpPullback A G (etaK V K) F) {L : LB G.left} (hL : L.IsLB)
    {M : LB A.left} (hM : M.IsLB) (hs : Out.Sym A M) (w : LB.Iso M (L.pull F)) (hw : w.IsGen) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L) := by
  have hp := gp.1
  obtain ⟨U, hU, t, ht⟩ := hs (IsLocalRing.closedPoint K)
  obtain ⟨n, hn⟩ : ∃ n : pullback G.hom (etaK V K) ⟶ (A.hom ⁻¹ᵁ U).toScheme, n ≫ (A.hom ⁻¹ᵁ U).ι = hp.isoPullback.inv :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have : A.hom (hp.isoPullback.inv y) = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      exact (congrArg (· ∈ U) this).mpr hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hι : (ι[A]).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp A) (𝟙 A))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  obtain ⟨t₁, ht₁, -⟩ := exists_up ((isGen_iff w).1 hw) hL hM _ (DVR.pullGen_isGen _ _ _ _ ht n)
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hL
    (φ' := fun k : Fin 2 => pullback.fst G.hom (etaK V K) ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun _ _ k => Finset.prod_congr rfl fun i _ => congrArg (fun q => k q ^ (![1, -1] : Fin 2 → ℤ) i) (by
      fin_cases i
      · show (n ≫ _ ≫ (ι[A]).left) ≫ F = _ ≫ (ι[G]).left
        rw [← Category.assoc, hn, Category.assoc, hι, ← Category.assoc, hp.isoPullback_inv_fst]
      · show (n ≫ (A.hom ⁻¹ᵁ U).ι) ≫ F = _ ≫ 𝟙 _
        rw [hn, hp.isoPullback_inv_fst, Category.comp_id])) t₁ ht₁
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  let e : Spec (CommRingCat.of K) ⟶ pullback G.hom (etaK V K) := pullback.lift (etaK V K ≫ eSec G) (𝟙 _) (by
    rw [Category.assoc, a₁, Category.id_comp]; exact Category.comp_id _)
  have he : e ≫ pullback.fst G.hom (etaK V K) = etaK V K ≫ eSec G := pullback.lift_fst _ _ _
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hL _ _ t₂ ht₂ (pullback.snd G.hom (etaK V K)) e
    (pullback.lift_snd _ _ _) _ _ (LB.oneGen L) (LB.isGen_oneGen L) (by
      have : e ≫ pullback.fst G.hom (etaK V K) ≫ (ι[G]).left = e ≫ pullback.fst G.hom (etaK V K) := by
        rw [← Category.assoc, he, Category.assoc]
        exact congrArg (etaK V K ≫ ·) e₂
      simp [DVR.fsum, Fin.sum_univ_two, this, Finsupp.single_neg])
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hL (φ' := fun k : Fin 2 => eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ k => by simp [Fin.prod_univ_two, e₂]) (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := GenExtend.existsUnique_gen_extend V K G.left G.left G.hom (eSec G) inferInstance
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance) a₁ e he L hL
    (Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] u ρ hu hρ (corr_of_val hL fun y J hJ =>
      (val_corr hJ cu _).trans ((val_one _).trans
        ((val_pull hJ ρ _ _).trans ((vρ _ _ y J hJ).trans (val_one _))).symm))
  have : Flat (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := inferInstanceAs (Flat (𝟙 _))
  refine ⟨s, hs₁, corr_of_generic_val (K := K) (𝟙_ _) hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_corr hJ cu (pullback.snd _ _)).trans
    ((val_one _).trans (val_one _).symm)))
  rw [← hs₂]
  refine Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm
  rw [Category.assoc, he, ← Category.assoc, ← pullback.condition]
  exact congrArg (fun q => val s (q ≫ eSec G) y J) (Category.comp_id _).symm

end DVR

end GlobalTheory.PolExtension
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem weilQkIs_iff_of_comm (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (D : DegData R I) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    (p p' : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b) (w' : Frm D.toPre F k p'.g.b)
    (hw : w.IsGen) (hw' : w'.IsGen) (z : F)
    (H : ∀ s s₁ s₂ s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p' w' s s₁ → PhiRel D.toPre F k p w s₁ s₂ →
      PhiRel D.toPre F k p w s s₃ → PhiRel D.toPre F k p' w' s₃ s₄ → s₂ = z • s₄)
    (hne : ∃ s s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p w s s₃ ∧ PhiRel D.toPre F k p' w' s₃ s₄ ∧ s₄ ≠ 0)
    (hk : 1 ≤ k) (ζ : F) : WeilQkIs D.toPre F k p p' ζ ↔ ζ = z := by
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D F k hk p' w' hw'
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ s) := fun s => (hΦ _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s) := fun s => (hΦ' _ _).2 rfl
  constructor
  · intro h
    obtain ⟨s, s₃, s₄, h₃, h₄, h0⟩ := hne
    have a := (isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ s₃ s₄ (r' s) (r _) h₃ h₄)
    have b := H s _ _ s₃ s₄ (r' s) (r _) h₃ h₄
    exact smul_left_injective F h0 (a.symm.trans b)
  · rintro rfl v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
    obtain ⟨c, -, hc⟩ := TorsionImage.exists_smul_of_phiVal p w v hw hv
    obtain ⟨c', -, hc'⟩ := TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'
    have q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s := fun s t h =>
      hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)
    have q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s := fun s t h =>
      hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)
    rw [isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul,
      H s _ _ _ _ (r' s) (r _) (r s) (r' _), smul_comm c' ζ, smul_comm c ζ, smul_comm c c']

theorem weilQkIs_iff_weilIs : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.weilQkIs_iff_commutatorPairing_torsion : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  first | exact @GlobalTheory.UT.weilQkIs_iff_weilIs | exact GlobalTheory.UT.weilQkIs_iff_weilIs | (intros; apply GlobalTheory.UT.weilQkIs_iff_weilIs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

noncomputable def transl (x : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ x)

theorem comp_transl (x : 𝟙_ (Over S) ⟶ A) {T : Over S} (y : T ⟶ A) : y ≫ transl x = y * (toUnit T ≫ x) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem toUnit_mul_self {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) (T : Over S) :
    (toUnit T ≫ x) * (toUnit T ≫ x) = 1 := by
  rw [← MonObj.comp_mul, hx, MonObj.comp_one]

theorem transl_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) : transl x ≫ transl x = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]

theorem inv_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) :
    (GrpObj.inv : A ⟶ A) ≫ transl x = transl x ≫ (GrpObj.inv : A ⟶ A) := by
  rw [comp_transl, ← Hom.inv_def, transl, mul_inv, inv_eq_of_mul_eq_one_right (toUnit_mul_self hx A), Hom.inv_def,
    Category.id_comp]

theorem exists_restrict {X Y : Scheme.{0}} (p : X ⟶ Y) (h : X ⟶ X) (e : h ≫ p = p) (V : Y.Opens) :
    ∃ n : (p ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V).toScheme, n ≫ (p ⁻¹ᵁ V).ι = (p ⁻¹ᵁ V).ι ≫ h :=
  ⟨IsOpenImmersion.lift _ ((p ⁻¹ᵁ V).ι ≫ h) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (congrArg (fun q => q y.1 ∈ V) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩

theorem sym_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (h : Sym A L) :
    Sym A (L.pull (transl x).left) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := h s
  obtain ⟨n, hn⟩ := exists_restrict A.hom (transl x).left (Over.w _) U
  refine ⟨U, hU, _, LBxP.isGen_pullAlong L (transl x).left n _ _ _ (fun k => ?_) t ht⟩
  fin_cases k
  · show (_ ≫ _) ≫ _ = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    exact congrArg (fun q => _ ≫ q.left) (inv_transl hx)
  · exact hn.symm

theorem kTriv_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (hL : L.IsLB) (h : KTriv A L) :
    KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x))) V
  have k₂ : T ◁ transl x ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_transl hx, Category.comp_id]
  have k₃ : T ◁ transl x ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end GlobalTheory.PolTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteTorsionExt

theorem eq_of_isPullF {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T}
    {g₁ g₂ : GtPtF D F} (h₁ : GtPt.IsPullF F x g g₁) (h₂ : GtPt.IsPullF F x g g₂) : g₁ = g₂ := by
  obtain ⟨b₁, s₁, i₁, z₁, m₁⟩ := g₁
  obtain ⟨b₂, s₂, i₂, z₂, m₂⟩ := g₂
  obtain rfl : b₁ = b₂ := Over.OverMorphism.ext (h₁.1.trans h₂.1.symm)
  obtain rfl : s₁ = s₂ := funext fun χ => GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (i₁ χ) (i₂ χ)
    (DVR.corr_trans D.P.isLB (h₁.2 χ) (DVR.corr_symm (h₂.2 χ)))
  rfl

theorem main : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → I' ≠ ⊤ → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (x₁ : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ G') (gp : GtPt D'.toPre (𝟙_ (Over (Spec (CommRingCat.of R'))))), x₁ ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R' I' e) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G'), xe ≫ fstG I' e G' = toUnit _ ≫ x₁ ∧ xe ≫ (U'.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (LB.pullGen D'.toPre.P.L _ _ ((U'.gt e).t χ) xe.left) (LB.pullGen D'.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R' I' e))).left)) → ∀ (p : QkPt D.toPre F k) (g' : GtPtF D'.toPre F) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → IsPullGtF φ hD F p.g g' → GtPt.IsPullF F (toUnit (TF (R := R') F)).left gp g' → x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R') F) ≫ x₁).left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) → QkToAkU U.toUnifPre F k p x := by
  intro hL R R' _ _ _ _ _ I I' hR hR' φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU hI' F _ _ _ hF k hk x₁ gp hx₁ hxe
    p g' x hp hg hg' hx
  obtain ⟨p', hp', hpg'⟩ := (GlobalTheory.T.torsionPoint_qk_alt hL.globalFns R' I' hR' hI' D' A' G' U'.toUnifPre k x₁ gp hx₁ hxe).2 F
  have e : p'.g = g' := eq_of_isPullF hpg' hg'
  let y : TFK (R := R') F ⟶ (Over.pullback (jK R')).obj G' :=
    Over.homMk (pullback.lift (toUnit (TF (R := R') F) ≫ x₁).left (jFK (R := R') F)
      (Over.w (toUnit (TF (R := R') F) ≫ x₁))) (pullback.lift_snd _ _ _)
  have hy : (y ≫ U'.gen.hom).left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') =
      (toUnit (TF (R := R') F) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine GlobalTheory.T.qkToAk_descends_along_baseChange hL.globalFns hL.secBaseChange R R' I I' hR hR' φ D A G U G' bc hbc A' D' hD U' hU F hF k hk
    p x p' (y ≫ U'.gen.hom) (by rw [hp, hp', map_zero]) (e ▸ hg) ?_
    (GlobalTheory.T.qkToAkU_of_integral_torsion_point hL R' I' hR' hI' D' A' G' U' k hk x₁ gp hx₁ hxe F p' _ hp' hpg' hy)
  rw [hx, ← hy]
  simp only [Category.assoc]

end GlobalTheory.FiniteTorsionExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImage
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImage
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_twist_iff {S : Scheme.{0}} {A T : Over S} [GrpObj A] (L : LB A.left) (ψ : T ⊗ A ⟶ T ⊗ A)
    (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (n : ℤ) {W : Type} (g : W → Prop)
    (P : W → (LB.Sec (LPow A L n T) → LB.Sec (LPow A L n T) → Prop) → Prop) :
    (∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α)) ↔
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ m hm n n α) := by
  subst hm
  rfl

theorem exists_smul_of_pt_eq (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℤ)
    (x : TFK (R := R) F ⟶ A.A) (α β : LB.Gen (thetaLB A.A A.L n x)) (hα : α.IsGen) (hβ : β.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (t : LB.Sec (LPow A.A A.L n (TFK (R := R) F)))
      (u u' : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A F) (LPow A.A A.L n (TFK (R := R) F))),
      IsActOf A.A A.L n ⟨x, α, hα⟩ t u → IsActOf A.A A.L n ⟨x, β, hβ⟩ t u' → u' = c • u := by
  obtain ⟨a, ha⟩ := H1.exists_const A.L A.isLB (fst (TFK (R := R) F) A.A).left (BoxTheta.surj_fst hG A.isAb _)
    (LB.mulGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] _ _ β
      (LB.invGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun t u u' hu hu' => ?_⟩
  · rintro rfl
    let z : (TFK (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TFK (R := R) F).left ⟶ A.A.left => exists_chart A.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (lift (𝟙 _) x).left z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (FieldBaseChange.gs_zero' _ z ⊤ trivial)
  · refine FieldBaseChange.SecOver.ext _ _ fun j => sec_ext_val A.isLB (fun y J hJ => ?_) j
    have e := (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _)))).symm.trans
      (ha _ (𝟙 _) y J hJ)
    refine (BoxTheta.act_val _ t u' hu' (𝟙 _) y hJ).trans (Eq.trans ?_
      (FieldBaseChange.sval_smul' hJ (𝟙 _) c u).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) e (BoxTheta.act_val _ t u hu (𝟙 _) y hJ).symm)
    exact (congrArg (fun v : ((TFK (R := R) F ⊗ A.A).left.presheaf.stalk y)ˣ => v.val * _)
      (inv_mul_cancel_right _ _).symm).trans ((congrArg (· * _) (Units.val_mul _ _)).trans (_root_.mul_assoc _ _ _))

theorem indAt_translT_iff : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ N hN p x
  have hG := hL.1.globalFns
  have key := fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ)
    (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s',
      U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D.toPre F N p w s s')
  constructor
  · rintro ⟨-, H⟩ w₀ hw₀
    obtain ⟨α, w, hα, hw, h⟩ := (key w₀).1 (H w₀ hw₀)
    refine ⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩
    rintro ⟨y, β, hβ⟩ rfl
    obtain ⟨c, hc, hcs⟩ := exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ
    obtain ⟨w', hw', hΦ⟩ := ProdTorsion.exists_phiRel_smul hG p w hw c hc
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t
    have e₁ := hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)
    have e₂ : s' = c • e u := ((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))
    exact e₂ ▸ e₁
  · intro H
    refine ⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩
    haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    obtain ⟨θ, rfl⟩ := BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1
    obtain ⟨w, hw, h⟩ := (H w₀ hw₀).2 θ rfl
    exact ⟨θ.φ, w, θ.isGen, hw, h⟩

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImageStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.inducesFrobeniusOnSections_translation_iff_image : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  first | exact @GlobalTheory.UT.indAt_translT_iff | exact GlobalTheory.UT.indAt_translT_iff | (intros; apply GlobalTheory.UT.indAt_translT_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem isPullback_jO : IsPullback (jO hϖ hv (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TO hϖ hv) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) := by
  have H₁ : IsPullback (snd (TO hϖ hv) D.toPre.P.A).left (fst (TO hϖ hv) D.toPre.P.A).left D.toPre.P.A.hom
      (TO hϖ hv).hom := (IsPullback.of_hasPullback (TO hϖ hv).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jO_snd hϖ hv, ← Over.w (ιS hϖ hv)] at H₀
  exact H₀.of_right (jO_fst hϖ hv) H₁


include hϖ hv in
theorem exists_vge (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) : ∃ r : ℚ, VGe D F v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TO hϖ hv) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TO hϖ hv).hom D.toPre.P.A.hom))
  have : CompactSpace (TO hϖ hv).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of (Ov v))))
  have : QuasiSeparatedSpace (TO hϖ hv).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (Ov v))))
  have : CompactSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TO hϖ hv) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TO hϖ hv) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jO_snd hϖ hv, Category.assoc]) s
  obtain ⟨t, ht, S, hS⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors (Ov v)) (isPullback_jO hϖ hv (D := D)) hL
    (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := hTW V D.toPre k hk α (Ov v) (fO v hϖ hv) inferInstance S
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  obtain ⟨r, hr⟩ := wt_coe_of_ne (v := v) (inv_ne_zero ht0)
  refine ⟨r, n, fun i => (t : F)⁻¹ * ιr (v := v) (rr i), σ, σF, hσF, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, hr]
    exact le_add_of_nonneg_right (v_ιr _)
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS _ (𝟙 _) y _ (hJ.mem (fun a => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jO hϖ hv (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t)
    rw [show ιr (v := v) ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t) = (t : F) by simp [ιr]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jO hϖ hv).left) y hJ
  have g : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g, inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g, gs_jO, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jO_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]


include hϖ hv in
theorem exists_nuGe (hTW : TwistBCSpanStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) : ∃ r : ℚ, NuGe D Q F v k s r := by
  classical
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge hϖ hv hTW hk (s.s (e i))
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
  refine ⟨-m, ?_⟩
  rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
    obtain ⟨i, hi, -⟩ := he χ
    exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
  intro α hα
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
  have := hm ⟨i, rfl⟩
  exact VGe.mono (hr i) (by linarith)


include hϖ in
theorem finite_sublevel {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k) (l : D.toPre.X →+ ℚ)
    (q : ℚ) : {χ | (Q χ : ℚ) / k + l χ ≤ q}.Finite := by
  let β : LinearMap.BilinForm ℤ D.toPre.X := LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D hQ a b)
    (fun a a' b => by simp) (fun c a b => by simp) (fun a b b' => by simp) (fun c a b => by simp)
  have hβ : ∀ a, β a a = 2 * Q a := fun a => (QForm.two_Q_eq hϖ D hQ a).symm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine (ClassMin.finite_affine_sublevel (ClassMin.realExtension_ofIntBilin_posDef (β := β)
    (fun a b => QForm.bOf_comm D a b) (fun a ha => by have := QForm.Q_pos hϖ D hQ ha; rw [hβ]; omega))
    (inv_pos.2 hk') ((Rat.castHom ℝ).toAddMonoidHom.comp l) q).subset fun χ hχ => ?_
  have h : (((Q χ : ℚ) / k + l χ : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hχ
  show (k : ℝ)⁻¹ * ClassMin.ofIntBilin β χ + (l χ : ℝ) ≤ q
  rw [ClassMin.ofIntBilin_apply, hβ]
  push_cast at h ⊢
  refine le_of_eq_of_le ?_ h
  field_simp

end GlobalTheory.UT.CoefVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinMap

theorem exists_linear_of_rel {F M X : Type} [Field F] [AddCommGroup M] [Module F M] {N : X → Type}
    [∀ α, AddCommGroup (N α)] [∀ α, Module F (N α)] (E : M → (∀ α, N α) → Prop)
    (tot : ∀ t, ∃ s, E t s) (uq : ∀ t t' s s', E t s → E t' s' → (t = t' ↔ s = s'))
    (lin : ∀ (c : F) t t' s s', E t s → E t' s' → E (c • t + t') (fun α => c • s α + s' α)) :
    ∃ ex : ∀ α, M →ₗ[F] N α, (∀ t, E t (fun α => ex α t)) ∧ (∀ t s, E t s → ∀ α, s α = ex α t) ∧
      (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, ((∃ t s, E t s ∧ s α ≠ 0) ↔ ex α ≠ 0) := by
  choose e he using tot
  have hl : ∀ (c : F) t t' α, e (c • t + t') α = c • e t α + e t' α := fun c t t' α =>
    congrFun ((uq _ _ _ _ (he _) (lin c t t' _ _ (he t) (he t'))).1 rfl) α
  have h0 : ∀ α, e 0 α = 0 := fun α => by
    have h := hl 1 0 0 α
    simpa using h
  have hu : ∀ t s, E t s → ∀ α, s α = e t α := fun t s h α => congrFun ((uq _ _ _ _ h (he t)).1 rfl) α
  refine ⟨fun α => ⟨⟨fun t => e t α, fun t t' => ?_⟩, fun c t => ?_⟩, he, hu, fun t h => ?_, fun α => ⟨?_, fun h => ?_⟩⟩
  · simpa using hl 1 t t' α
  · simpa [h0] using hl c t 0 α
  · exact (uq _ _ _ _ (he t) (he 0)).2 (funext fun α => (h α).trans (h0 α).symm)
  · rintro ⟨t, s, h, hs⟩ hz
    exact hs ((hu t s h α).trans (LinearMap.congr_fun hz t))
  · by_contra hn
    refine h (LinearMap.ext fun t => ?_)
    by_contra ht
    exact hn ⟨t, e t, he t, ht⟩

theorem exists_expansion_linear : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U F _ _ k hk
  obtain ⟨ex, a, b, c, d⟩ := exists_linear_of_rel (F := F) (M := EA A (jFK (R := V) F) k) (N := fun α => WB D F k α)
    (fun t s => U.ExpF F k t.sec (fun α => (s α).sec))
    (fun t => GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U F k hk t.sec)
    (fun t t' s s' h h' => GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t.sec t'.sec _ _ h h')
    (fun c t t' s s' h h' => ExpLin.expF_linear V hV D A G U F k t.sec t'.sec _ _ _ _ c h h'
      (fun _ => rfl) (fun _ _ => rfl))
  refine ⟨ex, a, fun t s h α => b (SecMod.mk _ t) (fun α => SecMod.mk _ (s α)) h α, c, fun α => Iff.trans ?_ (d α)⟩
  constructor
  · rintro ⟨t, s, h, j, hj⟩
    exact ⟨SecMod.mk _ t, fun α => SecMod.mk _ (s α), h, fun hz => hj ((SecMod.eq_zero_iff_coord _).1 hz j)⟩
  · rintro ⟨t, s, h, hs⟩
    exact ⟨t.sec, fun α => (s α).sec, h, not_forall.1 fun hz => hs ((SecMod.eq_zero_iff_coord _).2 hz)⟩

end GlobalTheory.UU.ExpLinMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamilyStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_fourierJacobi_expansion_family : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  first | exact @GlobalTheory.UU.ExpLinMap.exists_expansion_linear | exact GlobalTheory.UU.ExpLinMap.exists_expansion_linear | (intros; apply GlobalTheory.UU.ExpLinMap.exists_expansion_linear <;> assumption)
end
end
