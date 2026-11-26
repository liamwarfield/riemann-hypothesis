module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodBalance

variable {R : Type} [CommRing R] [IsDomain R]

def cst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R))

theorem cst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (cst ξ) :=
  (RingHom.injective (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).comp
    (IsFractionRing.injective R (FractionRing R))

theorem cst_eq (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    cst ξ r = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
      (((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat

variable [IsLocalRing R]

theorem unit_gm (ξ : Spec (CommRingCat.of (FractionRing R))) (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (closedPoint R : Spec (CommRingCat.of R)) ∈ U) (a : Γ(Spec (CommRingCat.of R), U)ˣ) :
    ∃ u : Rˣ, (gm (jK R) ξ U a).val = cst ξ u := by
  obtain rfl := DVR.eq_top_of_closedPoint_mem U hU
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom a, ?_⟩
  rw [gm_val _ ξ ⊤ trivial, cst_eq]
  refine congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
    (congrArg ((jK R).app ⊤).hom ?_)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a.val).symm

theorem unit_gm' (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} (p : Spec (CommRingCat.of R) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint R) ∈ U) (a : Γ(X, U)ˣ) :
    ∃ u : Rˣ, (gm (jK R ≫ p) ξ U a).val = cst ξ u := by
  have h : p (jK R ξ) ∈ U := by
    have := DVR.eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK R ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK R) p ξ U h]
  exact unit_gm ξ _ hU _

theorem exists_good_integral (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of R)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_psi (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (r : R) (hr : PsiCoord D χ r) :
    ∃ u : Rˣ, (val (D.psi χ) (𝟙 _) ξ J).val = cst ξ (u * r) := by
  obtain ⟨j, hj, h, e⟩ := hr
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have hm : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j :=
    h (show ξ ∈ jK R ⁻¹ᵁ ⊤ from trivial)
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  have h1 : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val = cst ξ r := by
    refine (gm_val _ ξ _ hm _).trans (Eq.trans ?_ (cst_eq ξ r).symm)
    have e' : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = _ := Eq.trans ?_ e
    · rw [e']
      exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm
    · congr 1
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j = (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, (congrArg Units.val t).trans ?_⟩
  refine (Units.val_mul _ _).trans ?_
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ h1
  refine (congrArg Units.val h2).trans ?_
  rw [Units.inv_eq_of_mul_eq_one_left]
  rw [hu, ← map_mul, Units.inv_mul, map_one]

omit [IsLocalRing R] in
theorem val_tau (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) ξ J = val (D.psi (a + b)) (𝟙 _) ξ J * (val (D.psi a) (𝟙 _) ξ J)⁻¹ *
      (val (D.psi b) (𝟙 _) ξ J)⁻¹ * (val D.rigK (𝟙 _) ξ J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem coord_balance {O : Type} [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] (ρ : D.OAct O) (x : O)
    (a b : D.X) {r₁ r₂ r₃ s₁ s₂ s₃ : R} (h₁ : PsiCoord D (x • a + b) r₁) (h₂ : PsiCoord D (x • a) r₂)
    (h₃ : PsiCoord D b r₃) (k₁ : PsiCoord D (a + star x • b) s₁) (k₂ : PsiCoord D a s₂)
    (k₃ : PsiCoord D (star x • b) s₃) : ∃ u : Rˣ, u * (r₁ * s₂ * s₃) = s₁ * r₂ * r₃ := by
  haveI := ρ.onB.hom x
  haveI := ρ.onB.hom (star x)
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨w, hw, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ (ρ.onB.rosati x)
  have hc := ρ.tau_bal x w hw h₀ a b
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 _))
  have e1 := val_tau D ξ hJ (x • a) b
  have e2 := val_tau D ξ hJ a (star x • b)
  have e3 := val_pull hJ w (D.pt2 a b) (𝟙 _)
  have hp : 𝟙 _ ≫ D.pt2 a b = jK R ≫ (lift (D.c a) (D.c b)).left := by
    simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift]
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, (val w (jK R ≫ (lift (D.c a) (D.c b)).left) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun k => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⊗ D.P.A ⟶ D.P.A, rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k = q.left := by
      fin_cases k <;> exact ⟨_, rfl⟩
    have := hJc ((lift (D.c a) (D.c b)).left ≫ rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k) (by
      rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
    exact this
  have e3' := e3.trans (congrArg (fun q => val w q ξ J) hp)
  have e4 := (congrArg₂ (@HMul.hMul _ _ ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ instHMul)
    e1 e3').symm.trans (e.trans e2)
  obtain ⟨u₁, g₁⟩ := val_psi D ξ hJ hJc _ _ h₁
  obtain ⟨u₂, g₂⟩ := val_psi D ξ hJ hJc _ _ h₂
  obtain ⟨u₃, g₃⟩ := val_psi D ξ hJ hJc _ _ h₃
  obtain ⟨v₁, f₁⟩ := val_psi D ξ hJ hJc _ _ k₁
  obtain ⟨v₂, f₂⟩ := val_psi D ξ hJ hJc _ _ k₂
  obtain ⟨v₃, f₃⟩ := val_psi D ξ hJ hJc _ _ k₃
  have key : ∀ {G : Type} [CommGroup G] (A₁ A₂ A₃ B₁ B₂ B₃ Z W : G),
      A₁ * A₂⁻¹ * A₃⁻¹ * Z⁻¹ * W = B₁ * B₂⁻¹ * B₃⁻¹ * Z⁻¹ → W * A₁ * B₂ * B₃ = B₁ * A₂ * A₃ := by
    intro G _ A₁ A₂ A₃ B₁ B₂ B₃ Z W h
    have h' := congrArg Additive.ofMul h
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    rw [← sub_eq_zero] at h' ⊢
    refine Eq.trans ?_ h'
    abel
  have e5 := congrArg Units.val (key _ _ _ _ _ _ _ _ e4)
  have e6 : cst ξ (v * (u₁ * r₁) * (v₂ * s₂) * (v₃ * s₃)) = cst ξ ((v₁ * s₁) * (u₂ * r₂) * (u₃ * r₃)) := by
    rw [map_mul, map_mul, map_mul, map_mul (cst ξ) (_ * _) (_ * r₃), map_mul (cst ξ) (_ * s₁), ← hv, ← g₁, ← g₂,
      ← g₃, ← f₁, ← f₂, ← f₃]
    exact e5
  have e7 := cst_injective ξ e6
  refine ⟨(v₁ * u₂ * u₃)⁻¹ * (v * u₁ * v₂ * v₃), ?_⟩
  rw [Units.val_mul, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
  push_cast
  linear_combination e7

theorem norm_unit {R C : Type} [CommRing R] [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h1 := hf u
  have h2 := hf (u⁻¹ : Rˣ)
  have h3 := norm_nonneg (f u)
  nlinarith

theorem betaAt_balanced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t : SAB H (Sp R)) (U : PELUnif (maximalIdeal R) t) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord U.D.toPre χ r → f r ≠ 0) → ∀ (x : 𝓞 E) a b, betaAt U.D.toPre f p (x • a) b = betaAt U.D.toPre f p a (H.bar x • b) := by
  intro E _ _ _ H R _ _ _ _ t U C _ _ f p hR hf hne x a b
  letI := H.starRing
  have hex : ∀ χ, ∃ r, PsiCoord U.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main R U.D hR χ).1).imp fun _ h => h.1
  have hv : ∀ χ, vPsiAt U.D.toPre f p χ = -Real.logb p ‖f (hex χ).choose‖ := fun χ => dif_pos (hex χ)
  have hn : ∀ χ, ‖f (hex χ).choose‖ ≠ 0 := fun χ => norm_ne_zero_iff.2 (hne χ _ (hex χ).choose_spec)
  obtain ⟨u, hu⟩ := coord_balance U.D.toPre U.oD x a b (hex (x • a + b)).choose_spec (hex (x • a)).choose_spec
    (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec (hex (H.bar x • b)).choose_spec
  have h := congrArg (fun r => Real.logb p ‖f r‖) hu
  simp only [map_mul, norm_mul, norm_unit f hf u, one_mul] at h
  rw [Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _),
    Real.logb_mul (hn _) (hn _), Real.logb_mul (hn _) (hn _)] at h
  simp only [betaAt, hv]
  linarith

end GlobalTheory.PeriodBalance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

noncomputable section

namespace GlobalTheory

universe u v

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx
      apply hZ'
      rw [connectedComponent_eq hyx]
      exact hZ.1.isConnected.subset_connectedComponent hy
  rw [← isClosed_compl_iff, h]
  refine Set.Finite.isClosed_biUnion
    (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun Z hZ => hZ.1)) fun Z hZ => ?_
  exact isClosed_of_mem_irreducibleComponents Z hZ.1

theorem geometricallyConnected_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)

  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    let s := pointOfClosedPoint f x hx
    have hs : s ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
    let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
    have ht : IsPullback t y p s := by
      refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
      rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
      exact IsPullback.of_id_fst
    obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k)
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
    obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
    rw [Subsingleton.elim a' b']
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    by_contra hc
    push Not at hc
    have h₁ : (p '' U).Nonempty := hc.1.image _
    have h₂ : (p '' Uᶜ).Nonempty := (Set.nonempty_compl.2 hc.2).image _
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU.isOpen
    have o₂ : IsOpen (p '' Uᶜ) := p.isOpenMap _ hU.compl.isOpen
    have hcov : p '' U ∪ p '' Uᶜ = Set.univ := by
      rw [← Set.image_union, Set.union_compl_self, Set.image_univ, p.surjective.range_eq]
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hx⟩ := nonempty_inter_closedPoints
      (nonempty_inter o₁ o₂ hcov h₁ h₂) (o₁.inter o₂).isLocallyClosed
    exact hb (fib x hx a b hax hbx ▸ ha)
  exact ⟨hne⟩

section Sub

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A N : C} [GrpObj N]

theorem exists_grpObj_of_mono_of_fac (n : A ⟶ N) [Mono n] (e : 𝟙_ C ⟶ A) (m : A ⊗ A ⟶ A) (i : A ⟶ A)
    (he : e ≫ n = η[N]) (hm : m ≫ n = (n ⊗ₘ n) ≫ μ[N]) (hi : i ≫ n = n ≫ ι[N]) :
    ∃ _ : GrpObj A, IsMonHom n := by
  have he' : ∀ {T : C} (t : T ⟶ 𝟙_ C), t ≫ e ≫ n = 1 := fun t => by
    rw [he, Hom.one_def, toUnit_unique t (toUnit _)]
  have hm' : ∀ {T : C} (t : T ⟶ A ⊗ A), t ≫ m ≫ n = (t ≫ fst _ _ ≫ n) * (t ≫ snd _ _ ≫ n) :=
    fun t => by
      rw [hm, Hom.mul_def, ← Category.assoc]
      congr 1
      ext <;> simp
  have hm'' : m ≫ n = (fst _ _ ≫ n) * (snd _ _ ≫ n) := by simpa using hm' (𝟙 _)
  have hi' : i ≫ n = n⁻¹ := by rw [hi, Hom.inv_def]
  letI : GrpObj A :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
          he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono n, Category.assoc, hm', Category.assoc, Category.assoc,
          hm' (A ◁ m), whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, hm', hm', MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc]
        simp
      left_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, inv_mul_cancel]
      right_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, mul_inv_cancel] }
  exact ⟨this, ⟨he, hm⟩⟩

end Sub

theorem finite_points_of_isOpenMap_unit {k : Type} [Field k] [IsAlgClosed k] (N : Over (Sp k))
    [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    (h : IsOpenMap η[N].left) : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  have hF : Function.Injective F := fun x y hxy =>
    Over.OverMorphism.ext (ext_of_apply_closedPoint_eq N.hom x.w y.w hxy)
  have ho : ∀ x, IsOpen {F x} := fun x => by
    have hx : η[N] ≫ (GrpObj.mulRight x).hom = x := by
      simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    have h₁ : IsOpenMap x.left := by
      rw [← hx, Over.comp_left]
      exact (GrpObj.mulRight x).hom.left.isOpenMap.comp h
    have h₂ := h₁ {pt} (by
      have : Subsingleton (Sp k) := inferInstance
      convert isOpen_univ
      exact Set.eq_univ_of_forall fun a => this.elim _ _)
    rwa [Set.image_singleton] at h₂
  obtain ⟨t, -, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_nhds_subcover
    (fun y => {y}) (by rintro _ ⟨x, rfl⟩; exact (ho x).mem_nhds rfl)
  have : (Set.range F).Finite := t.finite_toSet.subset fun y hy => by simpa using ht hy
  exact (Set.finite_range_iff hF).1 this

theorem exists_neutralComponent : ∀ (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N], Smooth N.hom → QuasiCompact N.hom → ∃ (N₀ : Over (Sp k)) (_ : GrpObj N₀) (ν : N₀ ⟶ N) (g : ℕ), IsMonHom ν ∧ IsOpenImmersion ν.left ∧ IsClosedImmersion ν.left ∧ GeometricallyConnected N₀.hom ∧ SmoothOfRelativeDimension g N₀.hom ∧ (g = 0 → Finite (𝟙_ (Over (Sp k)) ⟶ N)) := by
  intro k _ _ N _ hs hq
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let e₀ : N.left := η[N].left pt
  let U : N.left.Opens := ⟨connectedComponent e₀, isOpen_connectedComponent_of_noetherianSpace e₀⟩
  let N₀ : Over (Sp k) := Over.mk (U.ι ≫ N.hom)
  let ν : N₀ ⟶ N := Over.homMk U.ι rfl
  have hνo : IsOpenImmersion ν.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range ν.left = connectedComponent e₀ := U.range_ι
  have hνc : IsClosedImmersion ν.left := .of_isPreimmersion _ (hr ▸ isClosed_connectedComponent)
  have : Mono ν := Over.mono_of_mono_left ν
  have hsm : Smooth N₀.hom := inferInstanceAs (Smooth (U.ι ≫ N.hom))
  have hc : ConnectedSpace N₀.left :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := e₀))
  have hg : GeometricallyConnected N₀.hom := geometricallyConnected_of_isAlgClosed N₀.hom

  have fac : ∀ (T : Over (Sp k)) [ConnectedSpace T.left] (φ : T ⟶ N) (t : 𝟙_ _ ⟶ T),
      t ≫ φ = η[N] → ∃ ψ : T ⟶ N₀, ψ ≫ ν = φ := by
    intro T _ φ t ht
    have hsub : Set.range φ.left ⊆ Set.range ν.left := by
      rw [hr]
      refine (isConnected_range φ.left.continuous).subset_connectedComponent ⟨t.left pt, ?_⟩
      simp only [e₀, ← ht, Over.comp_left, Scheme.Hom.comp_apply]
    refine ⟨Over.homMk (IsOpenImmersion.lift ν.left φ.left hsub) ?_, ?_⟩
    · rw [← ν.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac ν.left φ.left hsub)
  have : ConnectedSpace (𝟙_ (Over (Sp k))).left := inferInstanceAs (ConnectedSpace (Sp k))
  obtain ⟨e, he⟩ := fac (𝟙_ _) η[N] (𝟙 _) (Category.id_comp _)
  have : ConnectedSpace (N₀ ⊗ N₀).left :=
    inferInstanceAs (ConnectedSpace ↥(pullback N₀.hom N₀.hom))
  obtain ⟨m, hm⟩ := fac (N₀ ⊗ N₀) ((ν ⊗ₘ ν) ≫ μ[N]) (lift e e)
    (by simpa [he] using lift_comp_one_left (𝟙 _) η[N])
  obtain ⟨i, hi⟩ := fac N₀ (ν ≫ ι[N]) e (by simp [reassoc_of% he])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono_of_fac ν e m i he hm hi
  obtain ⟨g, hgd⟩ := exists_dim_of_preconnected N₀.hom (e.left pt)
  refine ⟨N₀, G, ν, g, hG, hνo, hνc, hg, hgd, ?_⟩
  rintro rfl
  have : Etale N₀.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hgd
  have : Etale (e.left ≫ N₀.hom) := by
    rw [e.w]; exact inferInstanceAs (Etale (𝟙 (Sp k)))
  have : Etale e.left := Etale.of_comp e.left N₀.hom
  refine finite_points_of_isOpenMap_unit N ?_
  rw [← he, Over.comp_left]
  exact (e.left ≫ ν.left).isOpenMap

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.FamRigid

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct])
    (fun a b w => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c a w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem re_eq_imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).re = imForm Hm (Complex.I • z) w := by
  simp [imForm_apply, hermForm, smul_dotProduct]

theorem isBounded_sublevel {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (c : ℝ) :
    Bornology.IsBounded {z : Fin g → ℂ | (hermForm Hm z z).re ≤ c} := by
  have hc : Continuous fun z : Fin g → ℂ => (hermForm Hm z z).re := by
    unfold hermForm
    refine Complex.continuous_re.comp ?_
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨m, hm, hle⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le' hc.continuousOn
    (a := 0) (fun b hb => hp b (by rintro rfl; simp at hb))
  refine (Metric.isBounded_closedBall (x := (0 : Fin g → ℂ)) (r := 1 + c / m)).subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  rw [mem_closedBall_zero_iff]
  by_cases h0 : z = 0
  · subst h0
    have : 0 ≤ c := by simpa [hermForm] using hz
    have := div_nonneg this hm.le
    simp only [norm_zero]
    linarith
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 h0
    have h1 := hle ((‖z‖⁻¹ : ℝ) • z) (by simp [norm_smul, hn.ne'])
    have h2 : (hermForm Hm ((‖z‖⁻¹ : ℝ) • z) ((‖z‖⁻¹ : ℝ) • z)).re =
        ‖z‖⁻¹ * ‖z‖⁻¹ * (hermForm Hm z z).re := by
      rw [re_eq_imForm, re_eq_imForm, smul_comm, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul, _root_.mul_assoc]
    rw [h2] at h1
    have h3 : m * (‖z‖ * ‖z‖) ≤ c := by
      have := mul_le_mul_of_nonneg_right h1 (mul_pos hn hn).le
      refine this.trans (le_trans (le_of_eq ?_) hz)
      field_simp
    have h4 : ‖z‖ * ‖z‖ ≤ c / m := by
      rw [le_div_iff₀ hm]; linarith
    nlinarith

theorem finite_order {g : ℕ} {L : Type} [AddCommGroup L] [Module.Finite ℤ L] (P : L →+ (Fin g → ℂ))
    (hinj : Function.Injective P) (hd : DiscreteTopology P.range)
    (hsp : Submodule.span ℝ (Set.range P) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (δ : L ≃ₗ[ℤ] L)
    (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ a, P (δ a) = k (P a))
    (hiso : ∀ a b, (hermForm Hm (P (δ a)) (P (δ b))).im = (hermForm Hm (P a) (P b)).im) :
    ∃ n, 0 < n ∧ δ ^ n = 1 := by
  have hB : (imForm Hm).compl₁₂ (k.restrictScalars ℝ) (k.restrictScalars ℝ) = imForm Hm := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.compl₁₂_apply, LinearMap.restrictScalars_apply, ← hk, imForm_apply, hiso]
  have hQ : ∀ a, (hermForm Hm (P (δ a)) (P (δ a))).re = (hermForm Hm (P a) (P a)).re := by
    intro a
    rw [re_eq_imForm, re_eq_imForm, hk, ← map_smul]
    conv_rhs => rw [← hB]
    rfl
  have hQn : ∀ (n : ℕ) a, (hermForm Hm (P ((δ ^ n) a)) (P ((δ ^ n) a))).re =
      (hermForm Hm (P a) (P a)).re := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih => intro a; rw [pow_succ', LinearEquiv.mul_apply, hQ, ih]
  have hper : ∀ a, ∃ n, 0 < n ∧ (δ ^ n) a = a := by
    intro a
    have hfin := Metric.finite_isBounded_inter_isClosed (s := (P.range : Set (Fin g → ℂ)))
      DiscreteTopology.isDiscrete (isBounded_sublevel Hm hp (hermForm Hm (P a) (P a)).re)
      AddSubgroup.isClosed_of_discrete
    obtain ⟨m, n, hmn, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => P ((δ ^ n) a)) (t := _ ∩ (P.range : Set (Fin g → ℂ))) (fun n => Set.mem_inter
        (show P ((δ ^ n) a) ∈ {z : Fin g → ℂ | (hermForm Hm z z).re ≤ (hermForm Hm (P a) (P a)).re}
          from (hQn n a).le) ⟨_, rfl⟩) hfin
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    refine ⟨d + 1, Nat.succ_pos _, ?_⟩
    have := hinj he
    rw [add_assoc, pow_add, LinearEquiv.mul_apply] at this
    exact ((δ ^ m).injective this).symm
  choose N hN hNa using hper
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := L)
  refine ⟨∏ a ∈ S, N a, Finset.prod_pos fun a _ => hN a, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hS ?_
  intro a ha
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N (Finset.mem_coe.1 ha)
  rw [hd]
  change (δ ^ (N a * d)) a = a
  clear hd
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.mul_succ, pow_add, LinearEquiv.mul_apply, hNa, ih]

theorem ex_eq_of_level_group : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P P' : (U.Di i).La →+ (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P → IsPeriod (U.Di i) ty P' → (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P' (gam a) = h₀ *ᵥ P a) → IsUnit h₀.det ∧ U.u i P = U.u i P' ∧ ∀ z, (U.ex i P' (h₀ *ᵥ z)).left = (U.ex i P z).left := by
  intro hMink E _ _ _ H D l Xo σ g ty U i P P' gam h₀ hP hP' hiso hM hA hh
  have hsurj : Function.Surjective h₀.mulVec := by
    have : LinearMap.range (h₀.mulVecLin.restrictScalars ℝ) = ⊤ := by
      rw [eq_top_iff, ← hP'.2.2.2.1, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨P (gam.symm a), by simp [← hh]⟩
    exact LinearMap.range_eq_top.1 this
  have hu : IsUnit h₀ := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hpt : U.u i P = U.u i P' := (U.fibre i P P' hP hP').2
    ⟨gam, LinearEquiv.ofBijective h₀.mulVecLin ⟨Matrix.mulVec_injective_iff_isUnit.2 hu, hsurj⟩,
      hiso, hM, hA, hh⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hu, hpt, ?_⟩
  obtain ⟨h₁, gam₁, hex, hh₁, hiso₁, hM₁, -⟩ :=
    GlobalTheory.T.familyUnif_exp_unique_alt E H D l Xo σ g ty U i i P P' hP hP' hpt
  have hM₁' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La),
      ∃ e, gam₁ a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := U.t_surj i b
      obtain ⟨e₁, he₁⟩ := hM₁ (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam₁ (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have f₀ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hM
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam₁ hiso₁ hM₁'
  haveI := (U.Di i).fin
  haveI : Module.Finite ℤ (U.Di i).La := Module.Finite.trans (𝓞 E) _
  obtain ⟨-, hinj, hd, hsp, Hm, -, hp, hE⟩ := hP'
  haveI : Module.IsTorsionFree ℤ (U.Di i).La :=
    Function.Injective.moduleIsTorsionFree P' hinj (fun r x => map_zsmul P' r x)
  haveI : Module.Free ℤ (U.Di i).La := Module.free_of_finite_type_torsion_free'
  let δ : (U.Di i).La ≃ₗ[ℤ] (U.Di i).La := (gam₁.symm.trans gam).toAddEquiv.toIntLinearEquiv
  have hδ : ∀ a, δ a = gam (gam₁.symm a) := fun a => rfl
  obtain ⟨n, hn, hδn⟩ := finite_order P' hinj hd hsp Hm hp δ
    (h₀.mulVecLin ∘ₗ h₁.symm.toLinearMap)
    (fun a => by
      have := hh₁ (gam₁.symm a)
      rw [gam₁.apply_symm_apply] at this
      rw [hδ, hh, this]
      simp)
    (fun a b => by
      rw [hE, hE, hδ, hδ, hiso, ← hiso₁, gam₁.apply_symm_apply, gam₁.apply_symm_apply])
  have hδ1 := hMink _ δ n l.M hn hδn l.three_le (fun y => by
    obtain ⟨e, he⟩ := f₀ (gam₁.symm y)
    obtain ⟨e', he'⟩ := f₁ (gam₁.symm y)
    rw [gam₁.apply_symm_apply] at he'
    refine ⟨e - e', ?_⟩
    rw [hδ, he, smul_sub]
    conv_rhs => rw [he']
    abel)
  have hg : ∀ a, gam a = gam₁ a := fun a => by
    have := hδ (gam₁ a)
    rw [hδ1, gam₁.symm_apply_apply] at this
    exact this.symm
  have hlin : h₀.mulVecLin.restrictScalars ℝ = h₁.toLinearMap.restrictScalars ℝ := by
    refine LinearMap.ext_on hP.2.2.2.1 ?_
    rintro _ ⟨a, rfl⟩
    change h₀ *ᵥ P a = h₁ (P a)
    rw [← hh, ← hh₁, hg]
  intro z
  have : h₀ *ᵥ z = h₁ z := LinearMap.congr_fun hlin z
  rw [this, hex]

end GlobalTheory.FamRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.GlobalTheory.T.uniformization_period_lattice_change : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P P' : (U.Di i).La →+ (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P → IsPeriod (U.Di i) ty P' → (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P' (gam a) = h₀ *ᵥ P a) → IsUnit h₀.det ∧ U.u i P = U.u i P' ∧ ∀ z, (U.ex i P' (h₀ *ᵥ z)).left = (U.ex i P z).left := by
  first | exact @GlobalTheory.FamRigid.ex_eq_of_level_group | exact GlobalTheory.FamRigid.ex_eq_of_level_group | (intros; apply GlobalTheory.FamRigid.ex_eq_of_level_group <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionBaseChange

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1

section Pointwise

variable {X X' Z : Scheme.{0}}

theorem mem_nonzeroLocus {M : LB X} (s : M.Sec) (x : X) :
    x ∈ nonzeroLocus s ↔ ∃ k, x ∈ M.U k ∧ IsUnit (gs (𝟙 X) x _ (s.f k)) := by
  refine Opens.mem_iSup.trans (exists_congr fun k => ⟨fun h => ?_, fun ⟨h, hu⟩ => ?_⟩)
  · have hk : x ∈ M.U k := X.basicOpen_le _ h
    refine ⟨hk, ?_⟩
    rw [gs_eq (𝟙 X) x _ hk]
    exact (X.mem_basicOpen _ _ hk).1 h
  · rw [gs_eq (𝟙 X) x _ h] at hu
    exact (X.mem_basicOpen _ _ h).2 hu

theorem mem_nonzeroLocus_of_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB)
    {s : L.Sec} {s' : L'.Sec}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k))
    {x : X'} (hx : F x ∈ nonzeroLocus s) : x ∈ nonzeroLocus s' := by
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 hx
  obtain ⟨k, hk⟩ := exists_chart hL' x
  refine (mem_nonzeroLocus s' _).2 ⟨k, hk, ?_⟩
  have e := h _ (𝟙 _) x j k hj hk
  rw [Category.id_comp, gs_stalkMap F x _ hj] at e
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem fibre_nonzero_of_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB)
    {s : L.Sec} {s' : L'.Sec}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k))
    {S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} (hF : IsPullback F p' p t)
    (hs : ∀ y : S, ∃ x : X, p x = y ∧ x ∈ nonzeroLocus s) (y : S') : ∃ x : X', p' x = y ∧ x ∈ nonzeroLocus s' := by
  obtain ⟨x, hx, hn⟩ := hs (t y)
  obtain ⟨x', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF x y hx
  exact ⟨x', h₂, mem_nonzeroLocus_of_pull hL' h (by rwa [show F x' = x from h₁])⟩

theorem gs_comp_stalkMap {Y : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ X) (z : Z) (U : X.Opens) (h : p (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs p (r z) U a) = gs (r ≫ p) z U a := by
  have e := gs_pull (𝟙 Y) p (r z) U h a
  rw [Category.id_comp] at e
  exact (congrArg (r.stalkMap z).hom e.symm).trans ((gs_stalkMap r z (p ⁻¹ᵁ U) h _).symm.trans (gs_pull r p z U h _))

theorem existsUnique_of_local {S : Scheme.{0}} (Rel : ∀ U : S.Opens, Γ(S, U) → Prop) (small : S.Opens → Prop)
    (cov : ∀ (x : S) (W : S.Opens), x ∈ W → ∃ U, U ≤ W ∧ x ∈ U ∧ small U)
    (hres : ∀ (U W : S.Opens) (h : U ≤ W) (a : Γ(S, W)), Rel W a → Rel U (resG S h a))
    (hloc : ∀ a : Γ(S, ⊤), (∀ x : S, ∃ U, x ∈ U ∧ Rel U (resG S le_top a)) → Rel ⊤ a)
    (hu : ∀ U, small U → ∃! a, Rel U a) : ∃! a, Rel ⊤ a := by
  have eq : ∀ (W W' : S.Opens) (a : Γ(S, W)) (a' : Γ(S, W')), Rel W a → Rel W' a' → ∀ x ∈ W ⊓ W',
      gs (𝟙 S) x W a = gs (𝟙 S) x W' a' := fun W W' a a' h h' x hx => by
    obtain ⟨U, le, hxU, hU⟩ := cov x _ hx
    have e := (hu U hU).unique (hres U W (le.trans inf_le_left) a h) (hres U W' (le.trans inf_le_right) a' h')
    exact (gs_res (𝟙 S) x _ hxU a).symm.trans ((congrArg (gs (𝟙 S) x U) e).trans (gs_res (𝟙 S) x _ hxU a'))
  choose U _ hxU hU using fun x : S => cov x ⊤ trivial
  choose a ha _ using fun x => hu (U x) (hU x)
  obtain ⟨g, hg, -⟩ := S.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩) a (fun i j => fn_ext (V := U i ⊓ U j) fun y hy =>
      (gs_res (𝟙 S) y inf_le_left hy _).trans ((eq _ _ _ _ (ha i) (ha j) y hy).trans
        (gs_res (𝟙 S) y inf_le_right hy _).symm))
  have hg' : Rel ⊤ g := hloc g fun x => ⟨U x, hxU x, (congrArg (Rel (U x)) (hg x)).mpr (ha x)⟩
  exact ⟨g, hg', fun g' h' => fn_ext fun x _ => eq _ _ _ _ h' hg' x ⟨trivial, trivial⟩⟩

end Pointwise

theorem generates_local (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∀ (C : Type) [CommRing C] (t : Sp C ⟶ S), (∀ z, t z ∈ V) →
      ∀ θ : (LPow P.A P.L (1 : ℕ) (Over.mk t)).Sec,
        (∀ z : Sp C, ∃ y, (fst (Over.mk t) P.A).left y = z ∧ y ∈ nonzeroLocus θ) →
        ∀ s : (LPow P.A P.L (1 : ℕ) (Over.mk t)).Sec, ∃! a : C, ∀ j, ∀ y ∈ (LPow P.A P.L (1 : ℕ) (Over.mk t)).U j,
          gs (𝟙 _) y _ (s.f j) = cst (fst (Over.mk t) P.A).left y a * gs (𝟙 _) y _ (θ.f j) := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl p
  refine ⟨V, hV, fun C _ t ht => ?_⟩
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : Spec (CommRingCat.of C) ⟶ (overRes (T := baseOver S) V).left,
      t₀ ≫ (overRes (T := baseOver S) V).hom = t :=
    ⟨IsOpenImmersion.lift V.ι t (by rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact ht z), by
      show _ ≫ (V.ι ≫ 𝟙 S) = t
      rw [Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _⟩
  intro θ hθ s
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L (1 : ℕ) (baseAt t₀)),
      IsPullSec P.A P.L (1 : ℕ) (homAt t₀ ▷ P.A) (whiskerRight_snd (homAt t₀) P.A) (b i) b' := fun i => by
    have gen : ∀ (φ' : Fin 1 → ((baseAt t₀ ⊗ P.A).left ⟶ P.A.left))
        (_ : (fun _ : Fin 1 => (homAt t₀ ▷ P.A).left ≫ (snd (overRes (T := baseOver S) V) P.A).left) = φ'),
        ∃ s' : LB.Sec (LB.LinComb P.L φ' (fun _ => ((1 : ℕ) : ℤ))), ∀ j (le : LB.wchart P.L φ' j ≤
          (homAt t₀ ▷ P.A).left ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (snd (overRes (T := baseOver S) V) P.A).left) j),
          s'.f j = ((baseAt t₀ ⊗ P.A).left.presheaf.map (homOfLE le).op).hom
            (((homAt t₀ ▷ P.A).left.app _).hom ((b i).f j)) := by
      rintro _ rfl
      exact ⟨DVR.pullSec P.L _ _ (b i) _, fun _ _ => rfl⟩
    obtain ⟨s', hs'⟩ := gen (fun _ => (snd (baseAt t₀) P.A).left)
      (funext fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t₀) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, hsp⟩ := hb C t₀ b' hb'
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  rw [Set.range_unique] at hsp
  have li : ∀ r : Γ((baseAt t₀).left, ⊤),
      r • (SecM.ofSec P.A (b' hq.default) : SecM P.A P.L (1 : ℕ) (baseAt t₀)) = 0 → r = 0 := fun r hr =>
    Fintype.linearIndependent_iff.1 hli (fun _ => r) (by rw [Fintype.sum_unique]; exact hr) hq.default
  have sp : ∀ σ : SecM P.A P.L (1 : ℕ) (baseAt t₀), ∃ r : Γ((baseAt t₀).left, ⊤), r • SecM.ofSec P.A (b' hq.default) = σ :=
    fun σ => Submodule.mem_span_singleton.1 (hsp.ge Submodule.mem_top)
  have key : ∀ (r : Γ((baseAt t₀).left, ⊤)) (σ τ : LB.Sec (LPow P.A P.L (1 : ℕ) (baseAt t₀))),
      r • (SecM.ofSec P.A τ : SecM P.A P.L (1 : ℕ) (baseAt t₀)) = SecM.ofSec P.A σ ↔
      ∀ j, ∀ y ∈ (LPow P.A P.L (1 : ℕ) (baseAt t₀)).U j,
        gs (𝟙 _) y _ (σ.f j) = gs (fst (baseAt t₀) P.A).left y ⊤ r * gs (𝟙 _) y _ (τ.f j) := fun r σ τ => by
    have e : ∀ j, ∀ y ∈ (LPow P.A P.L (1 : ℕ) (baseAt t₀)).U j, gs (𝟙 _) y _ (liftHom P.A _ r * τ.f j) =
        gs (fst (baseAt t₀) P.A).left y ⊤ r * gs (𝟙 _) y _ (τ.f j) := fun j y hy =>
      (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y le_top hy _).trans
        ((gs_pull (𝟙 _) (fst (baseAt t₀) P.A).left y ⊤ trivial _).trans (by rw [Category.id_comp]))) rfl)
    exact ⟨fun h j y hy => (congrArg (gs (𝟙 _) y _) (congrFun (congrArg Subtype.val h) j)).symm.trans (e j y hy),
      fun h => Subtype.ext (funext fun j => fn_ext fun y hy => (e j y hy).trans (h j y hy).symm)⟩
  obtain ⟨u, hu⟩ := sp (SecM.ofSec P.A θ)
  have un : IsUnit u := (baseAt t₀).left.toRingedSpace.isUnit_of_isUnit_germ ⊤ u fun z _ => by
    obtain ⟨y, rfl, hy⟩ := hθ z
    obtain ⟨j, hj, h⟩ := (mem_nonzeroLocus θ y).1 hy
    have h' := isUnit_of_mul_isUnit_left (((key u θ _).1 hu j y hj) ▸ h)
    rw [gs_stalkMap _ y ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at h'
    exact h'
  obtain ⟨u, rfl⟩ := un
  obtain ⟨r, hr⟩ := sp (SecM.ofSec P.A s)
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  obtain ⟨a, ha⟩ := bij.2 (r * (u⁻¹).val)
  refine ⟨a, (key _ s θ).1 ?_, fun a' ha' => bij.1 ?_⟩
  · refine (congrArg (fun c : Γ((baseAt t₀).left, ⊤) =>
      c • (SecM.ofSec P.A θ : SecM P.A P.L (1 : ℕ) (baseAt t₀))) ha).trans ?_
    rw [← hu, smul_smul, Units.inv_mul_cancel_right, hr]
  · have e := (key _ s θ).2 ha'
    rw [← hu, smul_smul, ← hr, ← sub_eq_zero, ← sub_smul] at e
    exact ((Units.eq_mul_inv_iff_mul_eq u).2 (sub_eq_zero.1 (li _ e))).trans ha.symm

theorem generates (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {R' : Type} [CommRing R']
    {t : Sp R' ⟶ S} {X' : Scheme.{0}} {q : X' ⟶ Sp R'} {φ : X' ⟶ P.A.left} (hφ : IsPullback φ q P.A.hom t) {L' : LB X'}
    (hL' : L'.IsLB) (hw : LBIso L' (P.L.pull φ)) (θ : L'.Sec) (hθ : ∀ y : Sp R', ∃ x : X', q x = y ∧ x ∈ nonzeroLocus θ)
    (s : L'.Sec) : ∃! a : R', ∀ i, s.f i = constFn q _ a * θ.f i := by
  choose V hV H using generates_local hS P
  let Rel : ∀ U : (Sp R').Opens, Γ(Sp R', U) → Prop := fun U a => ∀ k, ∀ x ∈ L'.U k, q x ∈ U →
    gs (𝟙 X') x _ (s.f k) = gs q x U a * gs (𝟙 X') x _ (θ.f k)
  have main : ∃! a, Rel ⊤ a := by
    refine existsUnique_of_local Rel (fun U => IsAffineOpen U ∧ ∃ p, U ≤ t ⁻¹ᵁ V p) (fun x W hx => ?_)
      (fun U W h a ha k x hk hx => (ha k x hk (h hx)).trans (congrArg₂ (· * ·) (gs_res q x h hx a).symm rfl))
      (fun a h k x hk _ => ?_) ?_
    · obtain ⟨U, hU, hxU, le⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W ⊓ t ⁻¹ᵁ V (t x) from ⟨hx, hV _⟩)
      exact ⟨U, fun y hy => (le hy).1, hxU, hU, t x, fun y hy => (le hy).2⟩
    · obtain ⟨U, hU, h'⟩ := h (q x)
      exact (h' k x hk hU).trans (congrArg₂ (· * ·) (gs_res q x le_top hU a) rfl)
    rintro U ⟨hU, p, hp⟩
    let u : Sp Γ(Sp R', U) ⟶ Sp R' := hU.fromSpec
    have hι : IsOpenImmersion u := hU.isOpenImmersion_fromSpec
    have mι : ∀ z, u z ∈ U := fun z => hU.range_fromSpec.le ⟨z, rfl⟩
    let T : Over S := Over.mk (u ≫ t)
    have big : IsPullback (snd T P.A).left (fst T P.A).left P.A.hom (u ≫ t) := (IsPullback.of_hasPullback _ _).flip
    let ρ : (T ⊗ P.A).left ⟶ X' := hφ.lift (snd T P.A).left ((fst T P.A).left ≫ u) (by rw [Category.assoc]; exact big.w)
    have ρ₁ : ρ ≫ φ = (snd T P.A).left := hφ.lift_fst _ _ _
    have ρ₂ : ρ ≫ q = (fst T P.A).left ≫ u := hφ.lift_snd _ _ _
    have sq : IsPullback ρ (fst T P.A).left q u := IsPullback.of_right (by rw [ρ₁]; exact big) ρ₂ hφ
    have hρ : IsOpenImmersion ρ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip hι
    have hM : (LPow P.A P.L (1 : ℕ) T).IsLB := DVR.linComb_isLB P.L P.isLB _ _
    have m : ∀ (j : Fin 1 → P.L.ι) (y : (T ⊗ P.A).left), y ∈ (LPow P.A P.L (1 : ℕ) T).U j →
        ρ y ∈ (P.L.pull φ).U (fun _ => j 0) := fun j y h =>
      mem_pull.2 ((congrArg (fun e => e y ∈ P.L.U (j 0)) ρ₁).mpr (Set.mem_iInter.1 h 0))
    let cp : ChartPull (LPow P.A P.L (1 : ℕ) T) (P.L.pull φ) ρ :=
      { idx := fun j _ => j 0
        le := m
        g := fun y i j hi hj => (gm_linComb P.L _ _ (𝟙 _) y i j hi hj).trans
          (Eq.trans (by rw [ρ₁, Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp])
            (gm_pull_g P.L φ ρ y _ _ (m i y hi) (m j y hj)).symm) }
    obtain ⟨w, hw'⟩ := LBIso.chartPull cp (chartPullPull L' ρ ρ rfl) hw.symm
    have down := sec_pull_down ((isGen_iff w).1 hw') hL' hM
    obtain ⟨θU, hθU⟩ := down θ
    obtain ⟨sU, hsU⟩ := down s
    have G := H p _ (u ≫ t) (fun z => hp (mι z)) θU (fibre_nonzero_of_pull hM hθU sq hθ) sU
    have key : ∀ (a : Γ(Sp R', U)) (y : (T ⊗ P.A).left) k j, ρ y ∈ L'.U k → y ∈ (LPow P.A P.L (1 : ℕ) T).U j →
        (gs (𝟙 _) y _ (sU.f j) = cst (fst T P.A).left y a * gs (𝟙 _) y _ (θU.f j) ↔
        gs (𝟙 X') (ρ y) _ (s.f k) = gs q (ρ y) U a * gs (𝟙 X') (ρ y) _ (θ.f k)) := fun a y k j hk hj => by
      have hq : q (ρ y) ∈ U := (congrArg (fun e => e y ∈ U) ρ₂).mpr (mι _)
      have inj : Function.Injective (ρ.stalkMap y).hom := (ConcreteCategory.bijective_of_isIso (ρ.stalkMap y)).1
      have c : (ρ.stalkMap y).hom (gs q (ρ y) U a) = cst (fst T P.A).left y a := by
        rw [gs_comp_stalkMap ρ q y U hq, ρ₂]
        refine (gs_fromSpec hU le_rfl _ y a).trans (congrArg _ ?_)
        simp
      have e₁ := hsU _ (𝟙 _) y k j hk hj
      have e₂ := hθU _ (𝟙 _) y k j hk hj
      rw [Category.id_comp] at e₁ e₂
      rw [← inj.eq_iff, map_mul, c, ← gs_stalkMap ρ y _ hk, ← gs_stalkMap ρ y _ hk, e₁, e₂, mul_left_comm,
        Units.mul_right_inj]
    refine (existsUnique_congr fun a => ⟨fun h k x hk hx => ?_, fun h j y hj => ?_⟩).1 G
    · obtain ⟨z, hz⟩ : ∃ z, u z = q x := hU.range_fromSpec.ge hx
      obtain ⟨y, h₁, -⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
      obtain rfl : ρ y = x := h₁
      obtain ⟨j, hj⟩ := exists_chart hM y
      exact (key a y k j hk hj).1 (h j y hj)
    · obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
      exact (key a y k j hk hj).2 (h k _ hk ((congrArg (fun e => e y ∈ U) ρ₂).mpr (mι _)))
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv
  obtain ⟨r, hr, hu⟩ := main
  obtain ⟨a, rfl⟩ := bij.2 r
  exact ⟨a, (sec_eq_iff _ _ _ _).2 fun k x hk => hr k x hk trivial,
    fun a' ha' => bij.1 (hu _ fun k x hk _ => (sec_eq_iff _ _ _ _).1 ha' k x hk)⟩

theorem generates_and_baseChange : Out.SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ P.A.left) (L' : LB A'.left) (w : LB.Iso L' (P.L.pull φ)) (th : P.L.Sec), IsPullback φ A'.hom P.A.hom (spMap f) → L'.IsLB → w.IsGen → (∀ y : Sp R, ∃ x : P.A.left, P.A.hom x = y ∧ x ∈ Out.nonzeroLocus th) → (∀ s : P.L.Sec, ∃! a : R, ∀ i, s.f i = constFn P.A.hom _ a * th.f i) ∧ ∃ th' : L'.Sec, (∀ (j : (P.L.pull φ).ι) (i : L'.ι) (h : (P.L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ P.L.U (j PUnit.unit)), (φ.appLE _ _ h).hom (th.f (j PUnit.unit)) = (show Γ(A'.left, (P.L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (th'.f i)) ∧ (∀ y : Sp R', ∃ x : A'.left, A'.hom x = y ∧ x ∈ Out.nonzeroLocus th') ∧ (∀ s : L'.Sec, ∃! a : R', ∀ i, s.f i = constFn A'.hom _ a * th'.f i) := by
  intro hS R R' _ _ _ f P A' φ L' w th hφ hL' hw hth
  have refl : LBIso P.L (P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull P.L _ rfl) (chartPullId _)
      (exists_iso_linComb (F := 𝟙 P.A.left) P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
  refine ⟨generates hS P (t := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) P.isLB refl th hth, ?_⟩
  obtain ⟨th', h⟩ := sec_pull_down ((isGen_iff w).1 hw) P.isLB hL' th
  have nz := fibre_nonzero_of_pull hL' h hφ hth
  refine ⟨th', fun j i le => fn_ext fun y hy => ?_, nz, generates hS P hφ hL' ⟨w, hw⟩ th' nz⟩
  refine (gs_appLE φ _ _ le (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (le hy) hy.2).trans (Eq.symm ?_))
  exact (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))

end GlobalTheory.SectionBaseChange
end
end
