module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsAwayNotMem
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PairCompat
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScalePowMono
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSCompScaleS
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem toAlgHom_restrict {S : Type} [CommRing S] (R : Type) [CommRing R] [Algebra S R] (A A' : Type) [CommRing A]
    [Algebra S A] [Algebra R A] [IsScalarTower S R A] [CommRing A'] [Algebra S A'] [Algebra R A'] [IsScalarTower S R A']
    [Algebra A A'] [IsScalarTower R A A'] [IsScalarTower S A A'] :
    (IsScalarTower.toAlgHom R A A').restrictScalars S = IsScalarTower.toAlgHom S A A' := AlgHom.ext fun _ => rfl

section Wrap

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

include C in
theorem tanS_lift {y' : sp (R₀ := S) (DualNumber A') ⟶ G} (hy' : TanS y') :
    ∃ m ∈ M, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y =
        spMap (scaleS (S := S) (algebraMap (Localization.Away s) A' m)) ≫ y' := by
  obtain ⟨h', hh', rfl⟩ := tanS_chart C hy'
  have hh'' : IsTanAt ((IsScalarTower.toAlgHom (Localization.Away s) A A').comp (epsA C A)) h' := by
    intro b
    rw [hh' b]
    show algebraMap (Localization.Away s) A' (eps C b) = algebraMap A A' (algebraMap (Localization.Away s) A (eps C b))
    exact IsScalarTower.algebraMap_apply _ _ _ _
  obtain ⟨m, hm, h, hh, he⟩ := tan_lift (epsA C A) M h' hh''
  refine ⟨m, hm, pushR G (pt C h), chart_tanS C h hh, ?_⟩
  rw [← toAlgHom_restrict (Localization.Away s) A A', chart_map, he, chart_scale]

include C in
theorem tanS_uniq {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₁ = spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₂) :
    ∃ m ∈ M, spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₁ =
      spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₂ := by
  obtain ⟨g₁, t₁, rfl⟩ := tanS_chart C h₁
  obtain ⟨g₂, t₂, rfl⟩ := tanS_chart C h₂
  rw [← toAlgHom_restrict (Localization.Away s) A A', chart_map, chart_map] at he
  obtain ⟨m, hm, hc⟩ := tan_uniq (epsA C A) M g₁ g₂ t₁ t₂ (chart_inj C he)
  exact ⟨m, hm, by rw [chart_scale, chart_scale, hc]⟩

end Wrap

section Scale

variable {S : Type} [CommRing S]

private theorem dualMapS_fst' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).fst = j y.fst := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

private theorem dualMapS_snd' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).snd = j y.snd := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

private theorem scaleS_fst' {A : Type} [CommRing A] [Algebra S A] (c : A) (y : DualNumber A) :
    (scaleS (S := S) c y).fst = y.fst := by
  simp [scaleS]

private theorem scaleS_snd' {A : Type} [CommRing A] [Algebra S A] (c : A) (y : DualNumber A) :
    (scaleS (S := S) c y).snd = c * y.snd := by
  simp [scaleS]

theorem scaleS_comp {A : Type} [CommRing A] [Algebra S A] (a b : A) :
    (scaleS (S := S) a).comp (scaleS b) = scaleS (a * b) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [scaleS] <;> ring

theorem dualMapS_comp_scaleS {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    (c : A) : (dualMapS j).comp (scaleS c) = (scaleS (j c)).comp (dualMapS j) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst', scaleS_fst', scaleS_fst',
      dualMapS_fst']
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd', scaleS_snd', scaleS_snd',
      dualMapS_snd', map_mul]

theorem dualMapS_comp {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') : (dualMapS j').comp (dualMapS j) = dualMapS (j'.comp j) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.comp_apply, dualMapS_fst', dualMapS_fst', dualMapS_fst', AlgHom.comp_apply]
  · rw [AlgHom.comp_apply, dualMapS_snd', dualMapS_snd', dualMapS_snd', AlgHom.comp_apply]

theorem scaleS_one {A : Type} [CommRing A] [Algebra S A] : scaleS (S := S) (1 : A) = AlgHom.id S _ := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [scaleS]

variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem res_scale {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A') (c : A)
    (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j) ≫ spMap (scaleS c) ≫ y = spMap (scaleS (j c)) ≫ spMap (dualMapS j) ≫ y := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, dualMapS_comp_scaleS]

theorem scale_scale {A : Type} [CommRing A] [Algebra S A] (a b : A) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) a) ≫ spMap (scaleS b) ≫ y = spMap (scaleS (a * b)) ≫ y := by
  rw [← Category.assoc, spMap_comp, scaleS_comp]

theorem res_res {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j') ≫ spMap (dualMapS j) ≫ y = spMap (dualMapS (j'.comp j)) ≫ y := by
  rw [← Category.assoc, spMap_comp, dualMapS_comp]

end Scale

section Over

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

abbrev Qv (s t : S) : Type := Localization.Away (algebraMap S (Localization.Away s) t)

abbrev qL (s t : S) : Localization.Away s →ₐ[S] Qv s t := IsScalarTower.toAlgHom S _ _

theorem isUnit_qv (s t : S) : IsUnit (algebraMap S (Qv s t) t) := by
  rw [IsScalarTower.algebraMap_apply S (Localization.Away s) (Qv s t)]
  exact IsLocalization.Away.algebraMap_isUnit _

def qR (s t : S) : Localization.Away t →ₐ[S] Qv s t :=
  { IsLocalization.Away.lift t (isUnit_qv s t) with
    commutes' := fun r => IsLocalization.Away.lift_eq t (isUnit_qv s t) r }

theorem dualMapR_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    dualMapR (g.comp f) = (dualMapR g).comp (dualMapR f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMapR]

theorem glue_tan' {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  refine glue_tan s hs w hw ?_
  intro k l T α β hαβ
  have hin : ∀ x : S, α (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s k)) x)) =
      β (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s l)) x)) := by
    intro x
    have h1 := RingHom.congr_fun hαβ (TrivSqZeroExt.inl x)
    simpa [dAway, dualMapR] using h1
  have heps : α (TrivSqZeroExt.inr 1) = β (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun hαβ (TrivSqZeroExt.inr 1)
    simpa [dAway, dualMapR] using h1
  have hu : IsUnit (α (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s k)) (s l)))) := by
    rw [hin]
    exact (IsLocalization.Away.algebraMap_isUnit (s l)).map (β.comp (TrivSqZeroExt.inlHom _ _))
  obtain ⟨g0, hg0⟩ : ∃ g0 : Qv (s k) (s l) →+* T, ∀ a,
      g0 (algebraMap (Localization.Away (s k)) (Qv (s k) (s l)) a) = α (TrivSqZeroExt.inl a) :=
    ⟨IsLocalization.Away.lift _ (g := α.comp (TrivSqZeroExt.inlHom _ _)) hu,
      fun a => IsLocalization.Away.lift_eq _ (g := α.comp (TrivSqZeroExt.inlHom _ _)) hu a⟩
  have he2 : α (TrivSqZeroExt.inr 1) * α (TrivSqZeroExt.inr 1) = 0 := by
    rw [← map_mul]; simp
  obtain ⟨gm, hgm⟩ : ∃ gm : DualNumber (Qv (s k) (s l)) →+* T, ∀ x,
      gm x = g0 x.fst + g0 x.snd * α (TrivSqZeroExt.inr 1) :=
    ⟨{ toFun := fun x => g0 x.fst + g0 x.snd * α (TrivSqZeroExt.inr 1)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
           op_smul_eq_mul, map_add, map_mul]
         linear_combination (-(g0 x.snd * g0 y.snd)) * he2
       map_zero' := by simp
       map_add' := fun x y => by
         simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]
         ring }, fun _ => rfl⟩
  have hdec : ∀ {R : Type} [CommRing R] (x : DualNumber R),
      x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
    intro R _ x
    ext <;> simp
  have hR : g0.comp (qR (s k) (s l)).toRingHom = β.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (s l))
    ext x
    show g0 (qR (s k) (s l) (algebraMap S _ x)) = β (TrivSqZeroExt.inl (algebraMap S _ x))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S (Localization.Away (s k)) (Qv (s k) (s l)),
      hg0, hin]
  have hR' : ∀ a, g0 (qR (s k) (s l) a) = β (TrivSqZeroExt.inl a) := fun a => RingHom.congr_fun hR a
  have hα : α = gm.comp (dualMapS (qL (s k) (s l))).toRingHom := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hgm]
    conv_lhs => rw [hdec x]
    rw [map_add (f := _), map_mul]
    simp [dualMapS_fst', dualMapS_snd', hg0]
  have hβ : β = gm.comp (dualMapS (qR (s k) (s l))).toRingHom := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hgm]
    conv_lhs => rw [hdec x]
    rw [map_add (f := _), map_mul]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualMapS_fst', dualMapS_snd', hR', heps]
  have hk := congrArg (fun f => f.left) (hQ k l)
  simp only [Over.comp_left, spMap, Over.homMk_left] at hk
  rw [hα, hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, hk]


set_option backward.isDefEq.respectTransparency false in
theorem tan_ext_cover {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    {v₁ v₂ : sp (R₀ := S) (DualNumber S) ⟶ G}
    (h : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₁ =
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₂) : v₁ = v₂ := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (toL (s k))) ≫ Spec.map (CommRingCat.ofHom (dAway (s k))) := by
    show Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← toL_comp]
  rw [e]
  have hk := congrArg (fun q => Over.Hom.left q) (h k)
  simp only [Over.comp_left] at hk
  have hr : (dualMapS (Algebra.ofId S (Localization.Away (s k)))).toRingHom = dAway (s k) := by
    ext x <;> simp [dualMapS_fst', dualMapS_snd', dAway, dualMapR,
      TrivSqZeroExt.algebraMap_eq_inl']
  rw [spMap_left, hr] at hk
  calc
    _ = Spec.map (CommRingCat.ofHom (toL (s k))) ≫
        (Spec.map (CommRingCat.ofHom (dAway (s k))) ≫ Over.Hom.left v₁) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom (toL (s k))) ≫
        (Spec.map (CommRingCat.ofHom (dAway (s k))) ≫ Over.Hom.left v₂) := by rw [hk]
    _ = _ := (Category.assoc _ _ _).symm

end Over

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Maps

variable {S : Type} [CommRing S]

def awayHom (u : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u)) :
    Localization.Away u →ₐ[S] B :=
  { IsLocalization.Away.lift u hu with commutes' := fun r => IsLocalization.Away.lift_eq u hu r }

def qHom (u v : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u))
    (hv : IsUnit (algebraMap S B v)) : Qv u v →ₐ[S] B :=
  { IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) (g := (awayHom u B hu).toRingHom)
      (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact hv) with
    commutes' := fun r => by
      show IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) _
        (algebraMap (Localization.Away u) (Qv u v) (algebraMap S (Localization.Away u) r)) = algebraMap S B r
      rw [IsLocalization.Away.lift_eq]
      exact (awayHom u B hu).commutes r }

theorem away_unit (u : S) : IsUnit (algebraMap S (Localization.Away u) u) :=
  IsLocalization.Away.algebraMap_isUnit u

theorem unit_of_map {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] [Algebra B B']
    [IsScalarTower S B B'] {u : S} (h : IsUnit (algebraMap S B u)) : IsUnit (algebraMap S B' u) := by
  rw [IsScalarTower.algebraMap_apply S B B']
  exact h.map _

end Maps

section Extend

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem scale_pow_add {A : Type} [CommRing A] [Algebra S A] (x : A) (a b : ℕ) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) (x ^ a)) ≫ spMap (scaleS (x ^ b)) ≫ y = spMap (scaleS (x ^ (a + b))) ≫ y := by
  rw [scale_scale, pow_add]

theorem scale_pow_mono {A : Type} [CommRing A] [Algebra S A] (x : A) {m M : ℕ} (hm : m ≤ M)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h : spMap (scaleS (S := S) (x ^ m)) ≫ y₁ = spMap (scaleS (x ^ m)) ≫ y₂) :
    spMap (scaleS (S := S) (x ^ M)) ≫ y₁ = spMap (scaleS (x ^ M)) ≫ y₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm m d, ← scale_pow_add x d m y₁, ← scale_pow_add x d m y₂, h]

variable [∀ s : S, Smooth (Gs G s).hom]

include G in
theorem fp_chart {s : S} (C : Chart (Gs G s)) : Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U) := by
  haveI := chart_smooth (C := C)
  infer_instance

theorem tanS_away_lift {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y' : sp (R₀ := S) (DualNumber (Localization.Away (algebraMap S A t))) ⟶ G} (hy' : TanS y') :
    ∃ N : ℕ, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (algebraMap S A t)) t ^ N)) ≫ y' := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, y, hy, heq⟩ := tanS_lift C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) hy'
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, y, hy, ?_⟩
  rw [heq, map_pow, ← IsScalarTower.algebraMap_apply]

theorem tanS_away_uniq {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₁ =
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₂) :
    ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S A t ^ N)) ≫ y₁ = spMap (scaleS (algebraMap S A t ^ N)) ≫ y₂ := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, heq⟩ := tanS_uniq C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) h₁ h₂ he
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, ?_⟩
  rw [map_pow, ← IsScalarTower.algebraMap_apply] at heq
  exact heq

end Extend

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem away_ext {S : Type} [CommRing S] (u : S) {B : Type} [CommRing B] [Algebra S B]
    (f g : Localization.Away u →ₐ[S] B) : f = g := by
  first
  | exact Subsingleton.elim f g
  | exact (IsLocalization.algHom_subsingleton (Submonoid.powers u)).elim f g
  | exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers u)
      (by ext x; simp))

abbrev Rv {S : Type} [CommRing S] (a b c : S) : Type := Localization.Away (algebraMap S (Qv a b) c)

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]


set_option maxHeartbeats 800000 in
theorem pair_compat (a b t : S) (C : Chart (Gs G a)) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away t)) ⟶ G}
    {za : sp (R₀ := S) (DualNumber (Localization.Away a)) ⟶ G} {zb : sp (R₀ := S) (DualNumber (Localization.Away b)) ⟶ G}
    (ha : TanS za) (hb : TanS zb) (N₁ : ℕ)
    (har : spMap (dualMapS (qL a t)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a t) t ^ N₁)) ≫ spMap (dualMapS (qR a t)) ≫ y₀)
    (hbr : spMap (dualMapS (qL b t)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Qv b t) t ^ N₁)) ≫ spMap (dualMapS (qR b t)) ≫ y₀) :
    ∃ M : ℕ, spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qR a b)) ≫ zb := by
  have ut : IsUnit (algebraMap S (Rv a b t) t) := by
    rw [IsScalarTower.algebraMap_apply S (Qv a b) (Rv a b t)]
    exact IsLocalization.Away.algebraMap_isUnit _
  have ua : IsUnit (algebraMap S (Rv a b t) a) :=
    unit_of_map (B := Qv a b) (unit_of_map (B := Localization.Away a) (away_unit a))
  have ub : IsUnit (algebraMap S (Rv a b t) b) := unit_of_map (B := Qv a b) (isUnit_qv a b)
  obtain ⟨ρa, -⟩ : ∃ f : Qv a t →ₐ[S] Rv a b t, True := ⟨qHom a t _ ua ut, trivial⟩
  obtain ⟨ρb, -⟩ : ∃ f : Qv b t →ₐ[S] Rv a b t, True := ⟨qHom b t _ ub ut, trivial⟩
  apply tanS_away_uniq C (A := Qv a b) t (tanS_restrict _ ha) (tanS_restrict _ hb)
  have e1 : spMap (dualMapS (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t))) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Rv a b t) t ^ N₁)) ≫ spMap (dualMapS (ρa.comp (qR a t))) ≫ y₀ := by
    rw [res_res, show (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t)).comp (qL a b) = ρa.comp (qL a t) from away_ext _ _ _,
      ← res_res, har, res_scale, map_pow, AlgHom.commutes, res_res]
  have e2 : spMap (dualMapS (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t))) ≫ spMap (dualMapS (qR a b)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Rv a b t) t ^ N₁)) ≫ spMap (dualMapS (ρb.comp (qR b t))) ≫ y₀ := by
    rw [res_res, show (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t)).comp (qR a b) = ρb.comp (qL b t) from away_ext _ _ _,
      ← res_res, hbr, res_scale, map_pow, AlgHom.commutes, res_res]
  rw [e1, e2, show ρa.comp (qR a t) = ρb.comp (qR b t) from away_ext _ _ _]

set_option maxHeartbeats 800000 in
theorem tan_extend {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤) (C : ∀ k, Chart (Gs G (s k)))
    (k0 : Fin n) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away (s k0))) ⟶ G} (hy₀ : TanS y₀) :
    ∃ N : ℕ, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k0)))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ N)) ≫ y₀ := by
  classical
  have h1 : ∀ k, ∃ N : ℕ, ∃ z : sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G, TanS z ∧
      spMap (dualMapS (qL (s k) (s k0))) ≫ z =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s k0)) (s k0) ^ N)) ≫ spMap (dualMapS (qR (s k) (s k0))) ≫ y₀ :=
    fun k => tanS_away_lift (C k) (A := Localization.Away (s k)) (s k0) (tanS_restrict _ hy₀)
  choose N z hz hzr using h1
  let N₁ := Finset.univ.sup N
  obtain ⟨z', hz', hz'r⟩ : ∃ z' : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G, (∀ k, TanS (z' k)) ∧
      ∀ k, spMap (dualMapS (qL (s k) (s k0))) ≫ z' k =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s k0)) (s k0) ^ N₁)) ≫ spMap (dualMapS (qR (s k) (s k0))) ≫ y₀ := by
    refine ⟨fun k => spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ (N₁ - N k))) ≫ z k,
      fun k => tanS_scale _ (hz k), fun k => ?_⟩
    rw [res_scale, hzr k, map_pow, AlgHom.commutes, scale_pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := N) (Finset.mem_univ k))]
  have h3 : ∀ k l, ∃ M : ℕ,
      spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s l)) (s k0) ^ M)) ≫ spMap (dualMapS (qL (s k) (s l))) ≫ z' k =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s l)) (s k0) ^ M)) ≫ spMap (dualMapS (qR (s k) (s l))) ≫ z' l :=
    fun k l => pair_compat (s k) (s l) (s k0) (C k) (hz' k) (hz' l) N₁ (hz'r k) (hz'r l)
  have h4 : ∃ M₀ : ℕ,
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ M₀)) ≫ z' k0 =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ M₀)) ≫
          spMap (scaleS (algebraMap S (Localization.Away (s k0)) (s k0) ^ N₁)) ≫ y₀ := by
    apply tanS_away_uniq (C k0) (A := Localization.Away (s k0)) (s k0) (hz' k0) (tanS_scale _ hy₀)
    rw [hz'r k0, res_scale, map_pow, AlgHom.commutes, show qR (s k0) (s k0) = qL (s k0) (s k0) from away_ext _ _ _]
  choose M hM using h3
  obtain ⟨M₀, hM₀⟩ := h4
  let M₂ := max M₀ (Finset.univ.sup fun p : Fin n × Fin n => M p.1 p.2)
  obtain ⟨w, hwd⟩ : ∃ w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G,
      ∀ k, w k = spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ M₂)) ≫ z' k :=
    ⟨_, fun _ => rfl⟩
  have hw : ∀ k, TanS (w k) := fun k => by rw [hwd]; exact tanS_scale _ (hz' k)
  have hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l := by
    intro k l
    rw [hwd k, hwd l, res_scale, res_scale (qR (s k) (s l)), map_pow, map_pow, AlgHom.commutes, AlgHom.commutes]
    exact scale_pow_mono _ (le_trans (Finset.le_sup (f := fun p : Fin n × Fin n => M p.1 p.2) (Finset.mem_univ (k, l)))
      (le_max_right _ _)) (hM k l)
  obtain ⟨v, hv, hres⟩ := glue_tan' s hs w hw hQ
  refine ⟨M₂ + N₁, v, hv, ?_⟩
  rw [hres k0, hwd k0, scale_pow_mono _ (le_max_left _ _) hM₀, scale_pow_add]

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem ofId_ext {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] (f g : S →ₐ[S] B) : f = g := Subsingleton.elim f g

theorem exists_away_not_mem {S : Type} [CommRing S] {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (p : Ideal S) [p.IsPrime] : ∃ k, s k ∉ p := by
  by_contra hne
  push_neg at hne
  have hle : Ideal.span (Set.range s) ≤ p := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hne k
  rw [hs, top_le_iff] at hle
  exact Ideal.IsPrime.ne_top ‹p.IsPrime› hle

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]

section Prime

variable (p : Ideal S) [p.IsPrime]

@[instance_reducible]
def awayAtPrime (t : S) (ht : t ∉ p) : Algebra (Localization.Away t) (Localization.AtPrime p) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) p.primeCompl
    ((Submonoid.powers_le (P := p.primeCompl)).mpr ht)

theorem tan_prime_lift {y' : sp (R₀ := S) (DualNumber (Localization.AtPrime p)) ⟶ G} (hy' : TanS y') :
    ∃ q ∈ p.primeCompl, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.AtPrime p) q)) ≫ y' := by
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  obtain ⟨_, ⟨q, hq, rfl⟩, y₀, hy₀, he⟩ := tanS_lift (C k0) (A := Localization.Away (s k0)) M hy'
  obtain ⟨N, w, hw, hwr⟩ := tan_extend s hs C k0 hy₀
  refine ⟨s k0 ^ N * q, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N) hq, w, hw, ?_⟩
  rw [show Algebra.ofId S (Localization.AtPrime p) =
      (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _, ← res_res, hwr, res_scale, he, scale_scale,
    map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply, map_mul, map_pow]

theorem tan_prime_uniq {w : sp (R₀ := S) (DualNumber S) ⟶ G} (hw : TanS w)
    (h1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w = 1) :
    ∃ q ∈ p.primeCompl, spMap (scaleS (S := S) q) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have hwk : ∀ k, TanS (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w) :=
    fun k => tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra S A], TanS (1 : sp (R₀ := S) (DualNumber A) ⟶ G) :=
    fun A _ _ => comp_one' _
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hc0⟩ := tanS_uniq (C k0) (A := Localization.Away (s k0))
    (A' := Localization.AtPrime p) M (hwk k0) (hone _) (by
      rw [res_res, comp_one', show (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) = Algebra.ofId S (Localization.AtPrime p) from ofId_ext _ _, h1])
  rw [comp_one'] at hc0
  have h2 : ∀ k, ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) q₀)) ≫
        spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w =
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫ 1 := by
    intro k
    apply tanS_away_uniq (C k) (A := Localization.Away (s k)) (s k0) (tanS_scale _ (hwk k)) (hone _)
    rw [comp_one', res_scale, res_res, AlgHom.commutes,
      show (qL (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k))) =
        (qR (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _,
      ← res_res, show algebraMap S (Qv (s k) (s k0)) q₀ = qR (s k) (s k0) (algebraMap S (Localization.Away (s k0)) q₀)
        from ((qR (s k) (s k0)).commutes q₀).symm, ← res_scale]
    rw [show algebraMap (Localization.Away (s k0)) (Localization.Away (s k0)) (algebraMap S (Localization.Away (s k0)) q₀) =
      algebraMap S (Localization.Away (s k0)) q₀ from rfl] at hc0
    rw [hc0, comp_one']
  choose N hN using h2
  let N₂ := Finset.univ.sup N
  refine ⟨s k0 ^ N₂ * q₀, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N₂) hq₀, ?_⟩
  refine tan_ext_cover s hs fun k => ?_
  rw [comp_one', res_scale, Algebra.ofId_apply, map_mul, map_pow, ← scale_scale,
    scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), comp_one']

end Prime

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Hom

variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]

def preH {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) : (X ⟶ M) →* (Y ⟶ M) :=
  MonoidHom.mk' (f ≫ ·) fun a b => MonObj.comp_mul f a b

theorem pre_prod {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) {d : ℕ} (v : Fin d → (X ⟶ M)) :
    f ≫ (List.ofFn v).prod = (List.ofFn fun i => f ≫ v i).prod := by
  have h := map_list_prod (preH (M := M) f) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

theorem scale_prodPts {d : ℕ} (a : R) (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ M)) :
    spMap (scaleD a) ≫ prodPts c v = prodPts (a • c) v := by
  unfold prodPts
  rw [pre_prod]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  have hs : (scaleD a).comp (scaleD (c i)) = scaleD ((a • c) i) := by
    apply AlgHom.ext
    intro x
    refine TrivSqZeroExt.ext ?_ ?_
    all_goals (simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, AlgHom.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Pi.smul_apply]; try ring)
  rw [← Category.assoc, spMap_comp, hs]

end Hom

section Push

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

def pushforwardHom : (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) :=
  MonoidHom.mk' (pushR G) fun a b => by
    show iotaB ≫ Geo.Tor.pushPt _ (a * b) = (iotaB ≫ Geo.Tor.pushPt _ a) * (iotaB ≫ Geo.Tor.pushPt _ b)
    rw [← MonObj.comp_mul]
    congr 1
    exact map_mul (Geo.Tor.pushHom (Geo.Tor.isGrpPullback_pullback G (fB R R')) _) a b

theorem pushR_prod {d : ℕ} (v : Fin d → (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G)) :
    pushR G (List.ofFn v).prod = (List.ofFn fun i => pushR G (v i)).prod := by
  have h := map_list_prod (pushforwardHom (R := R) (R' := R') (P := P) G) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

end Push

theorem isGrpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G'' G (g ≫ f) F) :
    Geo.Tor.IsGrpPullback G'' ((Over.pullback f).obj G) g
      (pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc])) := by
  have hfst : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.fst G.hom f = F := pullback.lift_fst _ _ _
  have hsnd : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.snd G.hom f = G''.hom ≫ g := pullback.lift_snd _ _ _
  have hP := Geo.Tor.isGrpPullback_pullback G f
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback G.hom f)
    rw [hfst]
    exact h.1
  · intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · let x₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (x₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w x₀))
      let y₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (y₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w y₀))
      let x₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (x.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w x) =≫ (g ≫ f))
      let y₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (y.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w y) =≫ (g ≫ f))
      have e1 : (x₀' * y₀').left = (x₀ * y₀).left ≫ pullback.fst G.hom f :=
        hP.2 _ x₀ y₀ x₀' y₀' rfl rfl
      have e2 : (x₀'' * y₀'').left = (x * y).left ≫ F := h.2 T x y x₀'' y₀'' rfl rfl
      have e3 : (x₀' * y₀').left = (x₀'' * y₀'').left := by
        refine Geo.Tor.mul_left_congr (Category.assoc T.hom g f) x₀' y₀' x₀'' y₀'' ?_ ?_
        · show x₀.left ≫ pullback.fst G.hom f = x.left ≫ F
          rw [hx, Category.assoc, hfst]
        · show y₀.left ≫ pullback.fst G.hom f = y.left ≫ F
          rw [hy, Category.assoc, hfst]
      rw [Category.assoc, hfst, ← e1, e3, e2]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x * y)]
      exact Over.w (x₀ * y₀)

end ReciprocityTheory.ChartRestriction.G.Chart
