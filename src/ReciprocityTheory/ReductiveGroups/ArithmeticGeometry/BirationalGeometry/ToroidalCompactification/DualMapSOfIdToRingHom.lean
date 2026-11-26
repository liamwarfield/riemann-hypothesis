module

public import Lemmata.MiscLemmasQ.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TanSRestrict
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ChartAway
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TanLoc
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

section TanLoc

variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]

def dualMapS {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A') :
    DualNumber A →ₐ[S] DualNumber A' := Bl.ThirdBlockLemmaB.goal1 ι

theorem dualMapS_fst {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).fst = ι x.fst := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

theorem dualMapS_snd {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).snd = ι x.snd := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

def scaleS {A : Type} [CommRing A] [Algebra S A] (c : A) : DualNumber A →ₐ[S] DualNumber A :=
  (scaleD c).restrictScalars S

theorem scaleS_fst {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) : (scaleS (S := S) c x).fst = x.fst := by
  simp [scaleS, scaleD]

theorem scaleS_snd {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) :
    (scaleS (S := S) c x).snd = c * x.snd := by
  simp [scaleS, scaleD]

variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)

def IsTanAt (h : B →ₐ[S] DualNumber A) : Prop := ∀ b, (h b).fst = e b

section Lin

variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)


include hsm in
def derOf (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) : Derivation S B A where
  toFun b := (h b).snd
  map_add' a b := by simp
  map_smul' r b := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    show (h (a * b)).snd = a • (h b).snd + b • (h a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hsm, hsm, hh, hh]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem derOf_apply (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) (b : B) : derOf e hsm h hh b = (h b).snd := rfl


include hsm in
def ofLin (g : Ω[B⁄S] →ₗ[B] A) : B →ₐ[S] DualNumber A where
  toFun b := TrivSqZeroExt.inl (e b) + TrivSqZeroExt.inr (g (KaehlerDifferential.D S B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, Derivation.leibniz, map_add (f := _), map_smul, hsm, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem ofLin_fst (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).fst = e b := by simp [ofLin]

theorem ofLin_snd (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).snd = g (KaehlerDifferential.D S B b) := by
  simp [ofLin]

end Lin

variable {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

theorem isLocalizedModule_tan [Module B A] [Module B A'] (hsm : ∀ (b : B) (a : A), b • a = e b * a)
    (hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a) (f : A →ₗ[B] A') (hf : ∀ a, f a = algebraMap A A' a) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B M) f := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨_, ⟨m, hm, rfl⟩⟩ := x
    have hu : IsUnit (algebraMap A A' (e (algebraMap S B m))) := by
      rw [AlgHom.commutes]
      exact IsLocalization.map_units A' (⟨algebraMap S A m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩ :
        Algebra.algebraMapSubmonoid A M)
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hu
    constructor
    · intro a₁ a₂ h
      simp only [Module.algebraMap_end_apply, hsm'] at h
      rw [← hu] at h
      exact u.isUnit.mul_left_cancel h
    · intro a
      refine ⟨((u⁻¹ : A'ˣ) : A') * a, ?_⟩
      simp only [Module.algebraMap_end_apply, hsm', ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨⟨a, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A M) y
    refine ⟨⟨a, ⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩⟩, ?_⟩
    show algebraMap S B m • y = f a
    rw [hsm', hf, AlgHom.commutes, ← h, mul_comm]
  · rw [hf, hf] at hx
    obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, h⟩ := IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hx
    refine ⟨⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩, ?_⟩
    show algebraMap S B m • x₁ = algebraMap S B m • x₂
    rw [hsm, hsm, AlgHom.commutes]
    exact h

end TanLoc

section Main

variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B]
  {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

theorem tan_lift (h' : B →ₐ[S] DualNumber A') (hh' : IsTanAt ((IsScalarTower.toAlgHom S A A').comp e) h') :
    ∃ m ∈ M, ∃ h : B →ₐ[S] DualNumber A, IsTanAt e h ∧
      (dualMapS (IsScalarTower.toAlgHom S A A')).comp h = (scaleS (algebraMap S A' m)).comp h' := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  have : IsScalarTower S B A' := ⟨fun r b a => by
    show ι (e (r • b)) * a = r • (ι (e b) * a)
    rw [map_smul, map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  have hsm'' : ∀ (b : B) (a : A'), b • a = (ι.comp e) b * a := fun _ _ => rfl
  let g' := (derOf (ι.comp e) hsm'' h' hh').liftKaehlerDifferential
  obtain ⟨g, ⟨_, ⟨m, hm, rfl⟩⟩, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g'
  refine ⟨m, hm, ofLin e hsm g, fun b => ofLin_fst e hsm g b, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst, scaleS_fst, ofLin_fst, hh']
    rfl
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd, scaleS_snd, ofLin_snd]
    have := LinearMap.congr_fun hg (KaehlerDifferential.D S B b)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    refine this.trans ?_
    show (algebraMap S B m) • g' (KaehlerDifferential.D S B b) = _
    rw [hsm', Derivation.liftKaehlerDifferential_comp_D, derOf_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem tan_uniq (h₁ h₂ : B →ₐ[S] DualNumber A) (t₁ : IsTanAt e h₁) (t₂ : IsTanAt e h₂)
    (heq : (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₁ = (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₂) :
    ∃ m ∈ M, (scaleS (algebraMap S A m)).comp h₁ = (scaleS (algebraMap S A m)).comp h₂ := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  let g₁ := (derOf e hsm h₁ t₁).liftKaehlerDifferential
  let g₂ := (derOf e hsm h₂ t₂).liftKaehlerDifferential
  have hfg : f.comp g₁ = f.comp g₂ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    show f (g₁ (KaehlerDifferential.D S B b)) = f (g₂ (KaehlerDifferential.D S B b))
    simp only [g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply]
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq b)
    simp only [AlgHom.comp_apply, dualMapS_snd] at this
    exact this
  obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g₁ g₂ hfg
  refine ⟨m, hm, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_fst, scaleS_fst, t₁, t₂]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_snd, scaleS_snd]
    have := LinearMap.congr_fun hc (KaehlerDifferential.D S B b)
    simp only [LinearMap.smul_apply, g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply] at this
    change algebraMap S B m • (h₁ b).snd = algebraMap S B m • (h₂ b).snd at this
    rwa [hsm, hsm, AlgHom.commutes] at this

end Main

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G]

abbrev Gs (s : S) : Over (Spec (CommRingCat.of (Localization.Away s))) :=
  (Over.pullback (fB S (Localization.Away s))).obj G


set_option backward.isDefEq.respectTransparency.types false in
theorem chart_away (U : G.left.Opens) (hU : IsAffineOpen U) (s : S)
    (hs : ∀ x : Spec (CommRingCat.of S), s ∉ x.asIdeal → (η[G]).left x ∈ U) : Nonempty (Chart (Gs G s)) := by
  have hP := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback G (fB S (Localization.Away s))
  have key : (η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s)) =
      fB S (Localization.Away s) ≫ (η[G]).left := by
    have h1 := congrArg (fun m => m.left)
      (map_one (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hP
        (Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))))))
    simp only [one_left'] at h1
    change (1 : Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))) ⟶ Gs G s).left ≫
      pullback.fst G.hom (fB S (Localization.Away s)) = _ at h1
    rw [one_left'] at h1
    simp
  have hs' : ∀ y : Spec (CommRingCat.of (Localization.Away s)),
      s ∉ ((fB S (Localization.Away s)).base y).asIdeal := by
    intro y hy
    have hu : IsUnit (algebraMap S (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit s
    have hmem : algebraMap S (Localization.Away s) s ∈ y.asIdeal := hy
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hf : IsAffineHom (fB S (Localization.Away s)) := inferInstance
  have : IsAffineHom (pullback.fst G.hom (fB S (Localization.Away s))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback G.hom (fB S (Localization.Away s))).flip hf
  refine ⟨⟨pullback.fst G.hom (fB S (Localization.Away s)) ⁻¹ᵁ U, hU.preimage _, ?_⟩⟩
  intro y _
  have hk : (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) =
      (η[G]).left.base ((fB S (Localization.Away s)).base y) := by
    change ((η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s))).base y =
      (fB S (Localization.Away s) ≫ (η[G]).left).base y
    rw [key]
  show (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) ∈ U
  rw [hk]
  exact hs _ (hs' y)

theorem exists_cover : ∃ (n : ℕ) (s : Fin n → S), Ideal.span (Set.range s) = ⊤ ∧ ∀ i, Nonempty (Chart (Gs G (s i))) := by
  classical
  have htop : Ideal.span {t : S | Nonempty (Chart (Gs G t))} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : Spec (CommRingCat.of S) := ⟨M, hM.isPrime⟩
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show (η[G]).left p ∈ (⊤ : G.left.Opens) by simp)
    obtain ⟨V, ⟨t, rfl⟩, hpV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (PrimeSpectrum.isBasis_basic_opens (R := S)))
      (show p ∈ ((η[G]).left ⁻¹ᵁ U : (Spec (CommRingCat.of S)).Opens) from hpU)
    have hc : Nonempty (Chart (Gs G t)) := chart_away G U hU t (fun x hx => hVle hx)
    exact hpV (hle (Ideal.subset_span hc))
  obtain ⟨T, hsub, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp htop
  refine ⟨T.card, fun i => (T.equivFin.symm i : S), ?_, ?_⟩
  · have hr : Set.range (fun i => (T.equivFin.symm i : S)) = (T : Set S) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (T.equivFin.symm i).2
      · intro hx
        exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
    rw [hr]
    exact hspan
  · intro i
    exact hsub (T.equivFin.symm i).2

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

def TanS {A : Type} [CommRing A] [Algebra S A] (y : sp (R₀ := S) (DualNumber A) ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom S A A) ≫ y = 1

theorem tanS_restrict {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) : TanS (spMap (dualMapS j) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A' A').comp (dualMapS j) = j.comp (TrivSqZeroExt.fstHom S A A) := by
    refine AlgHom.ext fun x => ?_
    simp [dualMapS_fst]
  rw [e, ← spMap_comp, Category.assoc, hy, comp_one'']

theorem tanS_scale {A : Type} [CommRing A] [Algebra S A] (c : A) {y : sp (R₀ := S) (DualNumber A) ⟶ G}
    (hy : TanS y) : TanS (spMap (scaleS c) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A A).comp (scaleS c) = TrivSqZeroExt.fstHom S A A := by
    refine AlgHom.ext fun x => ?_
    simp [scaleS_fst]
  rw [e, hy]

theorem fst_restrict (s : S) (A : Type) [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
    [IsScalarTower S (Localization.Away s) A] :
    (TrivSqZeroExt.fstHom (Localization.Away s) A A).restrictScalars S = TrivSqZeroExt.fstHom S A A := rfl

section Chart

variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]

abbrev epsA (A : Type) [CommRing A] [Algebra (Localization.Away s) A] :
    Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] A :=
  (Algebra.ofId (Localization.Away s) A).comp (eps C)

theorem tanS_chart {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) :
    ∃ h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A, IsTanAt (epsA C A) h ∧ y = pushR G (pt C h) := by
  have hy' : pushR G (pullR (G := G) (R' := Localization.Away s) y) = y :=
    pushR_pullR (G := G) (R' := Localization.Away s) y
  have h0 : spMap (TrivSqZeroExt.fstHom (Localization.Away s) A A) ≫
      pullR (G := G) (R' := Localization.Away s) y = pt C (epsA C A) := by
    apply pushR_inj (G := G)
    rw [pushR_spMap, fst_restrict, hy', hy]
    simp only [epsA]
    rw [pt_eps, pushR_one]
  have hnil : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom (Localization.Away s) A A), IsNilpotent a := by
    intro a ha
    have h1 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pow_two, h1]
  have hcov := le_preimage_of_nil C (TrivSqZeroExt.fstHom (Localization.Away s) A A)
    (fun a => ⟨TrivSqZeroExt.inl a, by simp⟩) hnil _ (epsA C A) h0
  obtain ⟨h, hh⟩ := exists_pt C _ hcov
  refine ⟨h, ?_, ?_⟩
  · have h1 : pt C ((TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h) = pt C (epsA C A) := by
      rw [← spMap_pt, ← hh, h0]
    have h2 := pt_injective C h1
    intro b
    simpa using AlgHom.congr_fun h2 b
  · rw [← hy', hh]

theorem chart_tanS (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) (hh : IsTanAt (epsA C A) h) :
    TanS (pushR G (pt C h)) := by
  unfold TanS
  rw [← fst_restrict s A, ← pushR_spMap, spMap_pt]
  have e : (TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h = epsA C A := by
    refine AlgHom.ext fun b => ?_
    simpa using hh b
  rw [e]
  simp only [epsA]
  rw [pt_eps, pushR_one]

theorem chart_inj {h₁ h₂ : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A}
    (e : pushR G (pt C h₁) = pushR G (pt C h₂)) : h₁ = h₂ :=
  pt_injective C (pushR_inj (G := G) e)

theorem chart_map {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[Localization.Away s] A')
    (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (dualMapS (j.restrictScalars S)) ≫ pushR G (pt C h) = pushR G (pt C ((dualMapS j).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

theorem chart_scale (c : A) (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (scaleS (S := S) c) ≫ pushR G (pt C h) = pushR G (pt C ((scaleS c).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

def upS {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[S] A') : A →ₐ[Localization.Away s] A' :=
  { j with
    commutes' := fun r => by
      have : (j : A →+* A').comp (algebraMap (Localization.Away s) A) = algebraMap (Localization.Away s) A' :=
        IsLocalization.ringHom_ext (Submonoid.powers s) (by
          ext a
          simp [← IsScalarTower.algebraMap_apply])
      exact RingHom.congr_fun this r }

end Chart

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Dual

variable {S : Type} [CommRing S] (s : S)

abbrev dAway : DualNumber S →+* DualNumber (Localization.Away s) := dualMapR (algebraMap S (Localization.Away s))

theorem eq_inl_add_inr {R : Type} [CommRing R] (x : DualNumber R) :
    x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
  ext <;> simp

theorem dAway_eps : dAway s (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by
  ext <;> simp [dAway, dualMapR]

theorem dAway_inl (a : S) : dAway s (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (algebraMap S _ a) := by
  ext <;> simp [dAway, dualMapR]

theorem dAway_ext {T : Type} [CommRing T] {χ₁ χ₂ : DualNumber (Localization.Away s) →+* T}
    (h : χ₁.comp (dAway s) = χ₂.comp (dAway s)) : χ₁ = χ₂ := by
  have hinl : χ₁.comp (TrivSqZeroExt.inlHom _ _) = χ₂.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    refine RingHom.ext fun a => ?_
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inl a)
    simp only [RingHom.comp_apply, dAway_inl] at h1
    simpa using h1
  have heps : χ₁ (TrivSqZeroExt.inr 1) = χ₂ (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inr 1)
    simp only [RingHom.comp_apply, dAway_eps] at h1
    exact h1
  refine RingHom.ext fun x => ?_
  have h1 := RingHom.congr_fun hinl x.fst
  have h2 := RingHom.congr_fun hinl x.snd
  simp only [RingHom.comp_apply, TrivSqZeroExt.inlHom_apply] at h1 h2
  rw [eq_inl_add_inr x, map_add (f := _), map_add (f := _), map_mul, map_mul, heps, h1, h2]

theorem dAway_lift {T : Type} [CommRing T] (gg : DualNumber S →+* T) (hu : IsUnit (gg (TrivSqZeroExt.inl s))) :
    ∃ χ : DualNumber (Localization.Away s) →+* T, χ.comp (dAway s) = gg := by
  let g0 : S →+* T := gg.comp (TrivSqZeroExt.inlHom S S)
  have hu0 : IsUnit (g0 s) := hu
  let φ : Localization.Away s →+* T := IsLocalization.Away.lift s hu0
  have hφ : ∀ a : S, φ (algebraMap S _ a) = gg (TrivSqZeroExt.inl a) := fun a =>
    IsLocalization.lift_eq _ a
  let e := gg (TrivSqZeroExt.inr 1)
  have he : e * e = 0 := by
    simp only [e, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
  refine ⟨{ toFun := fun x => φ x.fst + φ x.snd * e
            map_one' := by simp
            map_mul' := fun x y => by
              simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
                MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add, map_mul]
              linear_combination (-(φ x.snd * φ y.snd)) * he
            map_zero' := by simp
            map_add' := fun x y => by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]; ring }, ?_⟩
  refine RingHom.ext fun x => ?_
  conv_rhs => rw [eq_inl_add_inr x]
  simp only [RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, dAway, dualMapR,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add, map_add, map_mul, hφ]
  simp only [zero_mul, add_zero, e]

end Dual

section Iso

variable {S : Type} [CommRing S] (s : S)

abbrev Ld : Type := Localization.Away (TrivSqZeroExt.inl s : DualNumber S)

theorem isUnit_dAway : IsUnit (dAway s (TrivSqZeroExt.inl s)) := by
  rw [dAway_inl]
  exact (IsLocalization.Away.algebraMap_isUnit s).map (TrivSqZeroExt.inlHom _ _)

def toL : DualNumber (Localization.Away s) →+* Ld s :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose

theorem toL_comp : (toL s).comp (dAway s) = algebraMap (DualNumber S) (Ld s) :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose_spec

def fromL : Ld s →+* DualNumber (Localization.Away s) :=
  IsLocalization.Away.lift (TrivSqZeroExt.inl s) (isUnit_dAway s)

theorem fromL_comp : (fromL s).comp (algebraMap (DualNumber S) (Ld s)) = dAway s :=
  IsLocalization.lift_comp _

theorem fromL_toL : (fromL s).comp (toL s) = RingHom.id _ := by
  apply dAway_ext s
  rw [RingHom.comp_assoc, toL_comp, fromL_comp, RingHom.id_comp]

end Iso

section Glue

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in
theorem glue_tan {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (s k)) →+* T)
      (β : DualNumber (Localization.Away (s l)) →+* T), α.comp (dAway (s k)) = β.comp (dAway (s l)) →
      Spec.map (CommRingCat.ofHom α) ≫ (w k).left = Spec.map (CommRingCat.ofHom β) ≫ (w l).left) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  let f : ∀ k, 𝒰.X k ⟶ G.left := fun k => Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left
  have hf : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ f k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ f l := by
    refine fun (k : Fin n) (l : Fin n) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (s k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (s l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber S) (Ld (s k))) = B.hom.comp (algebraMap (DualNumber S) (Ld (s l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (s k))).comp (dAway (s k)) = (B.hom.comp (toL (s l))).comp (dAway (s l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (s k))) (B.hom.comp (toL (s l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s l))) ≫ (w l).left
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  let g := 𝒰.glueMorphisms f hf
  have hι : ∀ k : Fin n, 𝒰.f k ≫ g = f k := fun k => Scheme.Cover.ι_glueMorphisms 𝒰 f hf k
  have hg : ∀ k : Fin n, Spec.map (CommRingCat.ofHom (dAway (s k))) ≫ g = (w k).left := by
    intro k
    have e : Spec.map (CommRingCat.ofHom (dAway (s k))) = Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ 𝒰.f k := by
      show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
    rw [e, Category.assoc, hι k]
    show Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  have hover : g ≫ G.hom = (sp (R₀ := S) (DualNumber S)).hom := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
    rw [← Category.assoc, hι k]
    show (Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber S)))
    rw [Category.assoc, Over.w (w k)]
    show Spec.map (CommRingCat.ofHom (toL (s k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber (Localization.Away (s k))))) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← toL_comp, RingHom.comp_assoc]
    congr 1
    refine RingHom.ext fun r => ?_
    simp [TrivSqZeroExt.algebraMap_eq_inl', dAway_inl]
  let v : sp (R₀ := S) (DualNumber S) ⟶ G := Over.homMk g hover
  have hres : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := fun k =>
    Over.OverMorphism.ext (hg k)
  refine ⟨v, ?_, hres⟩
  apply Over.OverMorphism.ext
  let 𝒱 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) _ hs).openCover
  refine Scheme.Cover.hom_ext 𝒱 _ _ fun (k : Fin n) => ?_
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
        (spMap (TrivSqZeroExt.fstHom S S S)).left =
      (spMap (TrivSqZeroExt.fstHom S (Localization.Away (s k)) (Localization.Away (s k)))).left ≫
        (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left := by
    rw [spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (dualMapS_fst (Algebra.ofId S (Localization.Away (s k))) x).symm
  have h1 := congrArg (fun q => Over.Hom.left q) (hw k)
  simp only [Over.comp_left] at h1
  show Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      ((spMap (TrivSqZeroExt.fstHom S S S)).left ≫ v.left) =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫ (1 : sp (R₀ := S) S ⟶ G).left
  rw [← Category.assoc, e1, Category.assoc]
  have h2 : (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left ≫ v.left = (w k).left :=
    congrArg (fun q => Over.Hom.left q) (hres k)
  rw [h2, h1, one_left', one_left']
  show (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k))))) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap S S)) ≫ _)
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id]

end Glue

end ReciprocityTheory.ChartRestriction.G.Chart
