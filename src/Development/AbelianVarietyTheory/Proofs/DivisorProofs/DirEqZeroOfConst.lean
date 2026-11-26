module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyParamNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyParamNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MonoParam

theorem t_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i y z, gam i y z = gam i z y) → ∀ i, t i ≠ 0 := by
  intro R _ _ Q m t gam hM hli hsym i hti
  have hdiag : ∀ y, gam i y y = 0 := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := hM y
    have h0 := GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
    have hni : n i = 0 := by
      by_contra hne
      apply h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hti]; exact zero_pow hne), mul_zero]
    rw [hn i, hni]; simp
  have hz : gam i = 0 := by
    refine LinearMap.ext₂ fun y z => ?_
    have h := hdiag (y + z)
    simp only [map_add (f := _), LinearMap.add_apply, hdiag y, hdiag z, hsym i z y] at h
    simp only [LinearMap.zero_apply]
    omega
  exact hli.ne_zero i hz

end GlobalTheory.MonoParam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyParamNeZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomialBoundaryFamily_param_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i y z, gam i y z = gam i z y) → ∀ i, t i ≠ 0 := by
  first | exact @GlobalTheory.MonoParam.t_ne_zero | exact GlobalTheory.MonoParam.t_ne_zero | (intros; apply GlobalTheory.MonoParam.t_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackLineBundleAutomorphismEqConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackLineBundleAutomorphismEqConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAutConst

theorem main : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  intro A _ B' _ X L π hB hL w hw
  have hP := (isGen_iff w).1 hw
  have hg : ∀ (j j' : L.ι) (x : B'.left), π x ∈ L.U j → π x ∈ L.U j' →
      gm (𝟙 B'.left) x _ ((L.pull π).g (fun _ => j) (fun _ => j')) = gm (𝟙 _ ≫ π) x _ (L.g j j') := by
    intro j j' x hj hj'
    have hp : (𝟙 B'.left : B'.left ⟶ B'.left) x ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    show gm _ x _ (∏ _k : PUnit, (res _ (pullU π _ (L.g j j'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ x _ hp _).trans (gm_pull _ π x (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)
  obtain ⟨u, hu⟩ := glue_unit (⊤ : B'.left.Opens)
    (fun j : L.ι => (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, mem_pull.2 hj, mem_pull.2 hj⟩)
    (fun j => w.s (fun _ => j, fun _ => j)) (fun j j' x hx => by
      have hj : π x ∈ L.U j := mem_pull.1 hx.1.1
      have hj' : π x ∈ L.U j' := mem_pull.1 hx.2.1
      have e := hP _ (𝟙 _) x j j' (fun _ => j) (fun _ => j') hj hj' (mem_pull.2 hj) (mem_pull.2 hj')
      rw [hg j j' x hj hj', mul_inv_cancel] at e
      exact e.trans (_root_.one_mul _))
  let e₁ : Γ(Sp A, ⊤) ≃+* Γ(B'.left, ⊤) :=
    RingEquiv.ofBijective B'.hom.appTop.hom (GlobalTheory.globalFns_holds _ B' hB)
  let e₂ : A ≃+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let e : A ≃+* Γ(B'.left, ⊤) := e₂.trans e₁
  refine ⟨Units.map e.symm.toMonoidHom u, fun Z x z j hj => ?_⟩
  have hl : pullU B'.hom ⊤ (unitOn (Units.map e.symm.toMonoidHom u)) = u :=
    Units.ext (e.apply_symm_apply u.val)
  have hm : x z ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j) := ⟨mem_pull.2 hj, mem_pull.2 hj⟩
  refine (congrArg (gm x z _) (hu j)).symm.trans ((gm_res x z _ hm _).trans ?_)
  exact (congrArg (gm x z ⊤) hl).symm.trans (gm_pull x B'.hom z ⊤ trivial _)

end GlobalTheory.PullAutConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackLineBundleAutomorphismEqConstStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackLineBundle_automorphism_eq_const : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  exact @GlobalTheory.PullAutConst.main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitEqOfGermEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitEqOfGermEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualUnitGerm

theorem primeSpectrum_subsingleton (k : Type) [Field k] : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  have key : ∀ p : PrimeSpectrum (DualNumber k), p.asIdeal = maximalIdeal (DualNumber k) := by
    intro p
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro x hx
    have hn : IsNilpotent x := by
      rcases TrivSqZeroExt.isUnit_or_isNilpotent x with h | h
      · exact absurd h hx
      · exact h
    exact (nilpotent_iff_mem_prime.1 hn) p.asIdeal p.isPrime
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

theorem unit_eq_of_germ_eq : ∀ (k : Type) [Field k] (z : Sp (DualNumber k)) (u v : (DualNumber k)ˣ), gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn u) = gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn v) → u = v := by
  intro k _ z u v h
  have hs : Subsingleton (Sp (DualNumber k)) := primeSpectrum_subsingleton k
  have h1 : (unitOn u).val = (unitOn v).val := by
    refine TopCat.Presheaf.section_ext (Sp (DualNumber k)).sheaf ⊤ _ _ fun x hx => ?_
    obtain rfl : x = z := Subsingleton.elim _ _
    have := congrArg Units.val h
    rw [gm_val _ x ⊤ hx, gm_val _ x ⊤ hx] at this
    exact this
  exact Units.ext
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv).1 h1)

end GlobalTheory.DualUnitGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitEqOfGermEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_unit_eq_of_germ_eq : ∀ (k : Type) [Field k] (z : Sp (DualNumber k)) (u v : (DualNumber k)ˣ), gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn u) = gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn v) → u = v := by
  first | exact @GlobalTheory.DualUnitGerm.unit_eq_of_germ_eq | exact GlobalTheory.DualUnitGerm.unit_eq_of_germ_eq | (intros; apply GlobalTheory.DualUnitGerm.unit_eq_of_germ_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackAbelianSchemeDualNumberEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackAbelianSchemeDualNumberEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualRigidityField

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem eq_of_eq_closedFibre {K : Type} [Field K] (A' G' : Over (Sp (DualNumber K))) [GrpObj A'] [GrpObj G']
    (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hab : pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ a.left =
      pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ b.left)
    (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  haveI := subsingleton_sp_dualNumber K
  let j := pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
  have hj : IsPullback j (pullback.snd A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) A'.hom
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := IsPullback.of_hasPullback _ _
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (GlobalTheory.globalFns_holds _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem pullback_eq : ∀ {R : Type} [CommRing R] (k : Type) [Field k] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (f : R →+* DualNumber k) (π₁ π₂ : B'.left ⟶ A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsGrpPullback B' A (spMap f) π₁ → IsGrpPullback B' A (spMap f) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ = π₂ := by
  intro R _ k _ A _ g B' _ f π₁ π₂ hA hg h1 h2 hx
  have hB := (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A B' π₂ g h2 hA hg).1
  let α : B' ⟶ B' := Over.homMk (h2.1.lift π₁ B'.hom h1.1.w) (h2.1.lift_snd _ _ _)
  have hα : α.left ≫ π₂ = π₁ := h2.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom h1 h2 (𝟙 A) α (by rw [hα]; rfl)
  have hα1 : α = 𝟙 B' := by
    refine eq_of_eq_closedFibre B' B' α (𝟙 B') hB ?_ (by rw [IsMonHom.one_hom, Category.comp_id])
    apply h2.1.hom_ext
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [hα]
      exact hx _ _ _ pullback.condition
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [Over.w α]
  rw [← hα, hα1, Over.id_left, Category.id_comp]

end GlobalTheory.DualRigidityField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackAbelianSchemeDualNumberEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupPullback_abelianScheme_dualNumber_eq : ∀ {R : Type} [CommRing R] (k : Type) [Field k] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (f : R →+* DualNumber k) (π₁ π₂ : B'.left ⟶ A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsGrpPullback B' A (spMap f) π₁ → IsGrpPullback B' A (spMap f) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ = π₂ := by
  first | exact @GlobalTheory.DualRigidityField.pullback_eq | exact GlobalTheory.DualRigidityField.pullback_eq | (intros; apply GlobalTheory.DualRigidityField.pullback_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndepIntBilinFormCharZeroCombinationEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndepIntBilinFormCharZeroCombinationEqZero
namespace GlobalTheory

theorem linIndep_intBilinForm_charZero_comb_eq_zero
    {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X)
    (k : Type) [Field k] [CharZero k] (a : Fin m → k) :
    LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  intro hli hsum

  let L : LinearMap.BilinForm ℤ X →ₗ[ℤ] (X → X → ℚ) :=
    { toFun := fun B y z => ((B y z : ℤ) : ℚ)
      map_add' := by intro B C; funext y z; simp
      map_smul' := by intro n B; funext y z; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro B hB
    ext y z
    have := congrFun (congrFun hB y) z
    simpa [L] using this
  have hZ : LinearIndependent ℤ (L ∘ gam) := hli.map' L hker
  have hQ : LinearIndependent ℚ (L ∘ gam) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
  funext j
  by_contra hj
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℚ (V := k) hj
  have hrel : ∑ i, ℓ (a i) • (L ∘ gam) i = 0 := by
    funext y z
    have h0 := congrArg ℓ (hsum y z)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul, L,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have := (Fintype.linearIndependent_iff.mp hQ) _ hrel j
  exact hℓ this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndepIntBilinFormCharZeroCombinationEqZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero : ∀ {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X) (k : Type) [Field k] [CharZero k] (a : Fin m → k), LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  first | exact @GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | exact GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | (intros; apply GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstPointCone

theorem unitOn_one {A : Type} [CommRing A] : unitOn (1 : Aˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)

theorem dir_eq_zero_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i, t i ∈ maximalIdeal R) → (∀ i y z, gam i y z = gam i z y) → ∀ (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (a : Fin m → k), (∀ r, (ρ r).snd = 0) → IsConstAlong Q t gam ρ a → a = 0 := by
  intro R _ _ _ Q m t gam hmon hli _ hs k _ _ ρ a hρ hc
  have hρc : constHom ρ = ρ := by
    ext r
    · simp [constHom, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [constHom, TrivSqZeroExt.algebraMap_eq_inl, hρ]
  obtain ⟨B', _, π₁, π₂, w, c', h1, h2, h3, hw, hc', hrel⟩ := hc
  rw [hρc] at h2 hc' hrel
  have hπ : π₁ = π₂ := GlobalTheory.T.groupPullback_abelianScheme_dualNumber_eq k Q.P.A Q.P.g B' ρ π₁ π₂ Q.P.isAb Q.P.smoothDim h1 h2 h3
  subst hπ
  have hab : IsAbelianScheme B' :=
    (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback ρ Q.P.A B' π₁ Q.P.g h1 Q.P.isAb Q.P.smoothDim).1
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.pulledBackLineBundle_automorphism_eq_const B' Q.P.L π₁ hab Q.P.isLB w hw
  obtain ⟨zz⟩ : Nonempty (Sp (DualNumber k)) := inferInstance
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.P.L zz J := by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB zz (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    exact ⟨J, hJ⟩
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₁), fun _ => J (c' x ≫ π₁))) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn lam) := by
    intro x
    have hmem : π₁ (c' x zz) ∈ Q.P.L.U (J (c' x ≫ π₁)) := by
      have := hJ (c' x ≫ π₁)
      simpa using this
    rw [hlam _ (c' x) zz _ hmem, (hc' x).1]
  have htne := GlobalTheory.T.monomialBoundaryFamily_param_ne_zero Q t gam hmon hli hs
  have key : ∀ y z, ∑ i, a i * (gam i y z : k) = 0 := by
    intro y z
    obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.exists_unitPartOfPeriodTau_monomial Q t gam hmon hs htne y z
    let e : (DualNumber k)ˣ := ⟨1 + TrivSqZeroExt.inr (∑ i, a i * (gam i y z : k)),
      1 - TrivSqZeroExt.inr (∑ i, a i * (gam i y z : k)), by ext <;> simp, by ext <;> simp⟩
    have h := hrel y z τ₀ hτ e rfl zz J hJ
    rw [hW (y + z), hW y, hW z, hW 0] at h
    have h' : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) = gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn 1) := by
      rw [unitOn_one, map_one]
      have hG : ∀ G : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ, G * G⁻¹ * G⁻¹ * G = 1 := fun G => by group
      rw [hG, _root_.one_mul] at h
      exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
    have he := GlobalTheory.T.dualNumber_unit_eq_of_germ_eq k zz _ _ h'
    have := congrArg (fun u : (DualNumber k)ˣ => TrivSqZeroExt.snd (u : DualNumber k)) he
    simpa [e] using this
  exact GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero gam k a hli key

end GlobalTheory.ConstPointCone
