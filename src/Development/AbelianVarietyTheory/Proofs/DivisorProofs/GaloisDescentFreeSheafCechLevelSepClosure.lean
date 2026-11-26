module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisLocallyConstantTupleRingTensorPowerUnivers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecLocallyConstant
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LCSec

variable (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]

def preQ {S T : DiscreteQuotient X} (h : T ≤ S) : (S → B) →+* (T → B) where
  toFun g t := g (DiscreteQuotient.ofLE h t)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def stage : (DiscreteQuotient X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of (S.unop → B)
  map f := CommRingCat.ofHom (preQ X B (leOfHom f.unop))
  map_id S := by
    refine CommRingCat.hom_ext (RingHom.ext fun g => funext fun t => ?_)
    exact congrArg g (DiscreteQuotient.ofLE_refl_apply t)
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun h => funext fun t => ?_)
    exact congrArg h (DiscreteQuotient.ofLE_ofLE _ _ t).symm

def pullQ (S : DiscreteQuotient X) : (S → B) →+* LocallyConstant X B where
  toFun g := ⟨fun x => g (S.proj x), S.proj_isLocallyConstant.comp g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def lcCocone : Cocone (stage X B) where
  pt := CommRingCat.of (LocallyConstant X B)
  ι := { app := fun S => CommRingCat.ofHom (pullQ X B S.unop)
         naturality := fun S T f => by
           refine CommRingCat.hom_ext (RingHom.ext fun g => LocallyConstant.ext fun x => ?_)
           exact congrArg g (DiscreteQuotient.ofLE_proj _ x) }

def lcCoconeIsColimit : IsColimit (lcCocone X B) := by
  haveI : ReflectsColimitsOfShape (DiscreteQuotient X)ᵒᵖ (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  apply Types.FilteredColimit.isColimitOf
  · intro f
    refine ⟨op f.discreteQuotient, ⇑f.lift, ?_⟩
    exact LocallyConstant.ext fun x => rfl
  · intro S T g h e
    change pullQ X B S.unop g = pullQ X B T.unop h at e
    refine ⟨op (S.unop ⊓ T.unop), (homOfLE inf_le_left).op, (homOfLE inf_le_right).op, ?_⟩
    change preQ X B _ g = preQ X B _ h
    funext q
    obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ q
    have hx := congrArg (fun φ : LocallyConstant X B => φ x) e
    change g (S.unop.proj x) = h (T.unop.proj x) at hx
    exact (congrArg g (DiscreteQuotient.ofLE_proj _ x)).trans (hx.trans (congrArg h (DiscreteQuotient.ofLE_proj _ x).symm))

end GlobalTheory.EtC.LCSec

namespace GlobalTheory.EtC.LCSec

theorem res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (y : Sec F U) :
    Sec.res a (Sec.res b y) = Sec.res (a ≫ b) y := by
  simp [Sec.res]

theorem sec_pi_bijective (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (S : Type) [Finite S] :
    Function.Bijective (fun (y : Sec F (Spec (CommRingCat.of (S → B)))) (s : S) =>
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) := by
  obtain ⟨hc⟩ := GlobalTheory.EtC.spec_pi_cofan_isColimit S (fun _ => B) (S → B) (RingEquiv.refl _)
  exact GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R F _ S _ _ hc

theorem res_eval_pullQ (R : Type) [CommRing R] (F : Shv R) (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]
    (S : DiscreteQuotient X) (y : Sec F (Spec (CommRingCat.of (S → B)))) (x : X) :
    Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y) =
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) (S.proj x)))) y := by
  rw [res_res, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory.EtC.LCSec


open GlobalTheory.EtC.LCSec in
theorem GlobalTheory.EtC.sec_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
  intro R _ F hF X _ _ B _
  have hfin := ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).2.mp hF) _ (stage X B) (lcCocone X B) (lcCoconeIsColimit X B)
  have hrep : ∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∃ (S : DiscreteQuotient X)
      (y : Sec F (Spec (CommRingCat.of (S → B)))), Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y = t := by
    intro t
    obtain ⟨S, y, hy⟩ := hfin.1 t
    exact ⟨S.unop, y, hy⟩
  have hzero : ∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))),
      (∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = 0) → t = 0 := by
    intro t ht
    obtain ⟨S, y, rfl⟩ := hrep t
    have hall : ∀ s : S, Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y = 0 := by
      intro s
      obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ s
      rw [← res_eval_pullQ]
      exact ht x
    have hy : y = 0 := by
      apply (sec_pi_bijective R F B S).1
      funext s
      exact (hall s).trans (map_zero _).symm
    rw [hy]
    exact map_zero _
  refine ⟨fun t => ?_, fun t₁ t₂ h => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨S, y, rfl⟩ := hrep t
    have he : (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y)) =
        (fun s : S => Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) ∘ S.proj :=
      funext fun x => res_eval_pullQ R F X B S y x
    rw [he]
    exact S.proj_isLocallyConstant.comp _
  · have h0 := hzero (t₁ - t₂) fun x => by
      change (F.obj.map _).hom (t₁ - t₂) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h x)
    exact sub_eq_zero.mp h0
  · let f : LocallyConstant X (Sec F (Spec (CommRingCat.of B))) := ⟨ψ, hψ⟩
    obtain ⟨y, hy⟩ := (sec_pi_bijective R F B f.discreteQuotient).2 (⇑f.lift)
    refine ⟨Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B f.discreteQuotient))) y, fun x => ?_⟩
    rw [res_eval_pullQ]
    exact congrFun hy (f.discreteQuotient.proj x)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionFinitarySheafSectionLocallyConstant
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSmooth

abbrev sr (Ω : Type) [Field Ω] (s : Finset Ω) : Subring Ω := Subring.closure (s : Set Ω)

variable (Ω : Type) [Field Ω]

theorem sr_mono {s t : Finset Ω} (h : s ≤ t) : sr Ω s ≤ sr Ω t :=
  Subring.closure_mono (Finset.coe_subset.2 h)

def incl {s t : Finset Ω} (h : s ≤ t) : CommRingCat.of (sr Ω s) ⟶ CommRingCat.of (sr Ω t) :=
  CommRingCat.ofHom (Subring.inclusion (sr_mono Ω h))

theorem incl_apply {s t : Finset Ω} (h : s ≤ t) (y : sr Ω s) : ((incl Ω h).hom y : Ω) = (y : Ω) := by
  rw [incl, CommRingCat.hom_ofHom, Subring.coe_inclusion]

theorem incl_id (s : Finset Ω) : incl Ω (le_refl s) = 𝟙 _ := by
  ext x; rfl

theorem incl_comp {s t u : Finset Ω} (h : s ≤ t) (h' : t ≤ u) : incl Ω (h.trans h') = incl Ω h ≫ incl Ω h' := by
  ext x
  simp only [incl, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Subring.coe_inclusion]

theorem incl_comp_subtype {s t : Finset Ω} (h : s ≤ t) :
    incl Ω h ≫ CommRingCat.ofHom (sr Ω t).subtype = CommRingCat.ofHom (sr Ω s).subtype := by
  ext y
  rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    Subring.coe_subtype, Subring.coe_subtype, incl_apply]

def diag : Finset Ω ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (sr Ω s)
  map {s t} h := incl Ω h.le
  map_id s := incl_id Ω s
  map_comp f g := incl_comp Ω f.le g.le

def cocone : Cocone (diag Ω) where
  pt := CommRingCat.of Ω
  ι := { app := fun s => CommRingCat.ofHom (sr Ω s).subtype
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact incl_comp_subtype Ω h.le }

theorem cocone_ι (s : Finset Ω) : (cocone Ω).ι.app s = CommRingCat.ofHom (sr Ω s).subtype := rfl

theorem cocone_ι_apply (s : Finset Ω) (y : sr Ω s) : ((cocone Ω).ι.app s).hom y = (y : Ω) := rfl

theorem surj (x : Ω) : ∃ (s : Finset Ω) (y : sr Ω s), x = ((cocone Ω).ι.app s).hom y :=
  ⟨{x}, ⟨x, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, (cocone_ι_apply Ω {x} ⟨x, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩).symm⟩

theorem inj [DecidableEq Ω] (i j : Finset Ω) (xi : sr Ω i) (xj : sr Ω j)
    (h : ((cocone Ω).ι.app i).hom xi = ((cocone Ω).ι.app j).hom xj) :
    ∃ (k : Finset Ω) (f : i ⟶ k) (g : j ⟶ k), ((diag Ω).map f).hom xi = ((diag Ω).map g).hom xj := by
  refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, Subtype.ext ?_⟩
  rw [cocone_ι_apply, cocone_ι_apply] at h
  change ((incl Ω (le_sup_left : i ≤ i ⊔ j)).hom xi : Ω) = ((incl Ω (le_sup_right : j ≤ i ⊔ j)).hom xj : Ω)
  rw [incl_apply, incl_apply, h]

def coconeIsColimit [DecidableEq Ω] : IsColimit (cocone Ω) := by
  haveI : ReflectsColimitsOfShape (Finset Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone Ω)) ?_ ?_)
  · intro x
    exact surj Ω x
  · intro i j xi xj h
    exact inj Ω i j xi xj h

end GlobalTheory.EtC.GalSmooth

namespace GlobalTheory.EtC


open GalSmooth in
theorem galois_sec_isLocallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (x : Sec F (Spec (CommRingCat.of Ω))),
      IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω => Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
  intro R _ F hF K Ω _ _ _ _ x
  classical
  obtain ⟨s, y, hy⟩ := (((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).2.1 hF) (Finset Ω) (diag Ω) (cocone Ω)
    (coconeIsColimit Ω)).1 x
  have key : ∀ τ : Ω ≃ₐ[K] Ω, Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
      ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (sr Ω s).subtype))).hom y := by
    intro τ
    rw [← hy, cocone_ι]
    show _ = ((onRings F).map (CommRingCat.ofHom (sr Ω s).subtype ≫ CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
    rw [Functor.map_comp]
    rfl
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ₀
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | τ₀⁻¹ * σ ∈ (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp [one_mem])] with τ hτ
  have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
    have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b (IntermediateField.subset_adjoin K _ hb)
    have h2 := congrArg τ₀ h1
    simpa [AlgEquiv.mul_apply] using h2
  have hc : (τ : Ω →+* Ω).comp (sr Ω s).subtype = (τ₀ : Ω →+* Ω).comp (sr Ω s).subtype := by
    ext a
    exact RingHom.eqOn_set_closure hs a.2
  rw [key τ, key τ₀, hc]

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentFreeSheafCechLevelSepClosure
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open Simplicial

namespace GlobalTheory.EtC.GalSec

theorem freePresheaf_map_freeMk {R : Type} [CommRing R] (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  exact ModuleCat.free_map_apply (uliftFunctor.{1, 0}.map (P.map g)) (ULift.up x)

theorem val_nat {R : Type} [CommRing R] {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) {U V : Scheme.{0}} (g : V ⟶ U)
    (x : P.obj (op U)) : val s V (P.map g.op x) = Sec.res g (val s U x) := by
  unfold val freeGen
  calc _ = (s.hom.app (op V)).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
        ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)))) := by
          rw [freePresheaf_map_freeMk]
    _ = _ := ?_
  have e1 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  have e2 := congrArg
    (fun φ => φ.hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom (ModuleCat.freeMk (ULift.up x))))
    (s.hom.naturality g.op)
  simp only [ModuleCat.hom_comp] at e1 e2
  exact (congrArg (fun z => (s.hom.app (op V)).hom z) e1).trans e2

theorem cechPt_nat {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X)
    (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) =
      cechPt f k (g ≫ x) (fun i => g ≫ y i) (fun i => by rw [Category.assoc, h i]) := by
  unfold cechPt
  have hL : yoneda.map g ≫ WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i))
      (fun i => by rw [← Functor.map_comp, h i]) =
      WidePullback.lift (yoneda.map (g ≫ x)) (fun i => yoneda.map (g ≫ y i))
      (fun i => by rw [← Functor.map_comp, Category.assoc, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, Functor.map_comp]
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base, Functor.map_comp]
  erw [← NatTrans.naturality_apply]
  rw [← hL]
  simp
  rfl

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x') (hy : y = y') :
    cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx hy
  rfl

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (t : Sec F U) :
    Sec.res (a ≫ b) t = Sec.res a (Sec.res b t) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (t : Sec F U) : Sec.res (𝟙 U) t = t := by
  simp [Sec.res]

end GlobalTheory.EtC.GalSec

namespace GlobalTheory.EtC.GalSec

theorem ofHom_one (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] :
    CommRingCat.ofHom (((1 : Ω ≃ₐ[K] Ω) : Ω ≃ₐ[K] Ω) : Ω →+* Ω) = 𝟙 (CommRingCat.of Ω) := by
  ext a
  rfl

theorem tailG_cons_one (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    tailG K Ω k (Fin.cons 1 g) = g := by
  funext i
  simp [tailG]

theorem mul_cons_tailG (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    (fun i => σ 0 * (Fin.cons 1 (tailG K Ω k σ) : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) i) = σ := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [tailG]

theorem continuous_tailG (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) : Continuous (tailG K Ω k) := by
  unfold tailG
  exact continuous_pi fun i => ((continuous_apply 0).inv).mul (continuous_apply i.succ)

private theorem gal_sec_of_lemma {R : Type} [CommRing R] {F : Shv R} (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (k : ℕ)
    (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F)
    (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) =
      Sec.res (Spec.map (CommRingCat.ofHom ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω)))
        (Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (tailG K Ω k σ))))
          (val s (Spec (CommRingCat.of (LCRing K Ω k)))
            (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k)))
              (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i)))
              (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))) := by
  have hb : (ptHom K Ω k σ).comp (baseHom K Ω k) = algebraMap K Ω := by
    rw [← legHom_comp K Ω k 0, ← RingHom.comp_assoc, ptHom_legHom]
    exact RingHom.ext fun a => (σ 0).commutes a
  rw [← res_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ)) = ptHom K Ω k σ from rfl,
    ← val_nat, cechPt_nat]
  congr 1
  apply cechPt_congr
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  · funext i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ptHom_legHom]

theorem gal_sec_of (TopsChoicePartA : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i) (TopsChoiceSecondBound : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])))) (S2 : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x) (S3 : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Sec F (Spec (CommRingCat.of Ω))), IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω => Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x)) : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  intro R _ F hF K Ω _ _ _ _ k
  obtain ⟨hlim⟩ := TopsChoiceSecondBound (k + 1) K Ω (LCRing K Ω k) (algebraMap K Ω) (baseHom K Ω k) (legHom K Ω k)
    (legHom_comp K Ω k) (TopsChoicePartA K Ω k)
  let f := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let Z := Spec (CommRingCat.of (LCRing K Ω k))
  let x : Z ⟶ _ := Spec.map (CommRingCat.ofHom (baseHom K Ω k))
  let y (i : Fin (k + 1)) : Z ⟶ _ := Spec.map (CommRingCat.ofHom (legHom K Ω k i))
  have h (i : Fin (k + 1)) : y i ≫ f = x := by
    dsimp [y, f, x]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp]
  let P := (cech f).obj (op ⦋k⦌)
  let p : P.obj (op Z) := cechPt f k x y h
  have hbij : Function.Bijective (fun s : (free R).obj P ⟶ F => val s Z p) := by
    have e (U : Scheme.{0}) : Function.Bijective (fun g : U ⟶ Z => P.map g.op p) := by
      have hb := CechPts.bij f k x y h hlim U
      constructor
      · intro g g' hg
        apply hb.1
        exact (CechPts.map_cechPt f k x y h g).symm.trans
          (hg.trans (CechPts.map_cechPt f k x y h g'))
      · intro v
        obtain ⟨g, hg⟩ := hb.2 v
        exact ⟨g, (CechPts.map_cechPt f k x y h g).trans hg⟩
    have hval (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (v : P.obj (op U)) :
        val s U v = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up v)) := rfl
    constructor
    · intro s s' hs
      apply Sheaf.hom_ext
      apply sheafify_hom_ext _ _ _ F.property
      apply NatTrans.ext
      funext U
      apply ModuleCat.free_hom_ext
      rintro ⟨v⟩
      obtain ⟨g, rfl⟩ := (e U.unop).2 v
      change val s U.unop (P.map g.op p) = val s' U.unop (P.map g.op p)
      change val s Z p = val s' Z p at hs
      rw [val_nat, val_nat, hs]
    · intro a
      choose c hc using fun (U : Scheme.{0}) (v : P.obj (op U)) => (e U).2 v
      dsimp only at hc
      let φ (U : Scheme.{0}) (v : P.obj (op U)) := Sec.res (c U v) a
      have hφ (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)) :
          φ V (P.map g.op v) = Sec.res g (φ U v) := by
        have hccomp : c V (P.map g.op v) = g ≫ c U v := by
          apply (e V).1
          dsimp only
          rw [hc, op_comp, Functor.map_comp_apply, hc]
        dsimp [φ]
        rw [hccomp, res_comp]
      refine ⟨FreeHom.desc P F φ hφ, ?_⟩
      have hcid : c Z p = 𝟙 Z := by
        apply (e Z).1
        dsimp only
        rw [hc, op_id, Functor.map_id_apply]
      change val (FreeHom.desc P F φ hφ) Z p = a
      rw [hval]
      have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫
          (FreeHom.desc P F φ hφ).hom = FreeHom.descP P F φ hφ := by
        have he := ((sheafificationAdjunction Scheme.etaleTopology.{0}
          (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (FreeHom.descP P F φ hφ)
        rw [Adjunction.homEquiv_unit] at he
        exact he
      rw [hdesc]
      change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up p)) = a
      erw [ModuleCat.freeDesc_apply]
      change Sec.res (c Z p) a = a
      rw [hcid, res_id]
  obtain ⟨hloc, hinj, hsurj⟩ := S2 R F hF (Fin k → (Ω ≃ₐ[K] Ω)) Ω
  refine ⟨?_, ?_, ?_⟩
  · intro s s' hss
    apply hbij.1
    apply hinj
    funext g
    have e := congrFun hss (Fin.cons 1 g)
    simp only at e
    rw [gal_sec_of_lemma, gal_sec_of_lemma] at e
    simpa [tailG_cons_one, ofHom_one, res_id] using e
  · intro s
    rw [IsLocallyConstant.iff_eventually_eq]
    intro σ
    have h1 := (continuous_tailG K Ω k).continuousAt (x := σ) |>.eventually
      ((IsLocallyConstant.iff_eventually_eq _).mp (hloc (val s (Spec (CommRingCat.of (LCRing K Ω k))) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k))) (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))) (tailG K Ω k σ))
    have h2 := (continuous_apply 0 : Continuous fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => σ 0).continuousAt (x := σ)
      |>.eventually ((IsLocallyConstant.iff_eventually_eq _).mp
        (S3 R F hF K Ω (Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (tailG K Ω k σ)))) (val s (Spec (CommRingCat.of (LCRing K Ω k))) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k))) (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))))
        (σ 0))
    filter_upwards [h1, h2] with τ e1 e2
    rw [gal_sec_of_lemma, gal_sec_of_lemma, e1]
    exact e2
  · intro φ hφ heq
    have hψ : IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => φ (Fin.cons 1 g)) :=
      hφ.comp_continuous (continuous_const.finCons continuous_id)
    obtain ⟨t, ht⟩ := hsurj _ hψ
    obtain ⟨s, hs⟩ := hbij.2 t
    refine ⟨s, fun σ => ?_⟩
    rw [gal_sec_of_lemma]
    simp only at hs
    rw [hs, ht, ← heq, mul_cons_tailG]

end GlobalTheory.EtC.GalSec

namespace GlobalTheory.EtC.GalSec

theorem gal_sec : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  have hsections : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B],
        (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))),
          IsLocallyConstant (fun x : X =>
            Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧
        Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) =>
          Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧
        ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ →
          ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x,
            Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
    intro R _ F hF X _ _ B _
    have hfin := (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF _ (LCSec.stage X B) (LCSec.lcCocone X B)
        (LCSec.lcCoconeIsColimit X B)
    have hrep (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) :
        ∃ (S : DiscreteQuotient X) (y : Sec F (Spec (CommRingCat.of (S → B)))),
          Sec.res (Spec.map (CommRingCat.ofHom (LCSec.pullQ X B S))) y = t := by
      obtain ⟨S, y, hy⟩ := hfin.1 t
      exact ⟨S.unop, y, hy⟩
    have hzero (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))))
        (ht : ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = 0) :
        t = 0 := by
      obtain ⟨S, y, rfl⟩ := hrep t
      have hy : y = 0 := by
        apply (LCSec.sec_pi_bijective R F B S).1
        funext s
        obtain ⟨x, rfl⟩ := S.proj_surjective s
        exact ((LCSec.res_eval_pullQ R F X B S y x).symm.trans (ht x)).trans (map_zero _).symm
      rw [hy]
      exact map_zero _
    refine ⟨fun t => ?_, fun t₁ t₂ h => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨S, y, rfl⟩ := hrep t
      have he : (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
          (Sec.res (Spec.map (CommRingCat.ofHom (LCSec.pullQ X B S))) y)) =
          (fun s : S => Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) ∘ S.proj :=
        funext (LCSec.res_eval_pullQ R F X B S y)
      rw [he]
      exact S.proj_isLocallyConstant.comp _
    · apply sub_eq_zero.mp (hzero (t₁ - t₂) fun x => ?_)
      change (F.obj.map _).hom (t₁ - t₂) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h x)
    · let q : LocallyConstant X (Sec F (Spec (CommRingCat.of B))) := ⟨ψ, hψ⟩
      obtain ⟨y, hy⟩ := (LCSec.sec_pi_bijective R F B q.discreteQuotient).2 (⇑q.lift)
      refine ⟨Sec.res (Spec.map (CommRingCat.ofHom (LCSec.pullQ X B q.discreteQuotient))) y, fun x => ?_⟩
      rw [LCSec.res_eval_pullQ]
      exact congrFun hy (q.discreteQuotient.proj x)
  have haction : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
        (x : Sec F (Spec (CommRingCat.of Ω))),
        IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω =>
          Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
    intro R _ F hF K Ω _ _ _ _ x
    classical
    have elements := (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF
    obtain ⟨s, y, hy⟩ := (elements (Finset Ω) (GalSmooth.diag Ω) (GalSmooth.cocone Ω)
      (GalSmooth.coconeIsColimit Ω)).1 x
    have restrict_eq (τ : Ω ≃ₐ[K] Ω) :
        Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
          ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (GalSmooth.sr Ω s).subtype))).hom y := by
      rw [← hy, GalSmooth.cocone_ι]
      show _ = ((onRings F).map (CommRingCat.ofHom (GalSmooth.sr Ω s).subtype ≫
        CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
      rw [Functor.map_comp]
      rfl
    rw [IsLocallyConstant.iff_eventually_eq]
    intro τ₀
    have : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
      IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
    let H := (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup
    have hopen : IsOpen (Set.ofPred fun σ : Ω ≃ₐ[K] Ω => τ₀⁻¹ * σ ∈ H) :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
    have hmem : τ₀⁻¹ * τ₀ ∈ H := by
      rw [inv_mul_cancel]
      exact H.one_mem
    filter_upwards [hopen.mem_nhds hmem] with τ hτ
    have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
      have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b
        (IntermediateField.subset_adjoin K _ hb)
      simpa [AlgEquiv.mul_apply] using congrArg τ₀ hfix
    have hc : (τ : Ω →+* Ω).comp (GalSmooth.sr Ω s).subtype =
        (τ₀ : Ω →+* Ω).comp (GalSmooth.sr Ω s).subtype := by
      ext a
      exact RingHom.eqOn_set_closure hs a.2
    rw [restrict_eq τ, restrict_eq τ₀, hc]
  exact gal_sec_of GlobalTheory.T.galoisLocallyConstantTupleRing_tensorPower_universal
    GlobalTheory.T.spec_widePushout_isLimit_widePullback hsections haction

end GlobalTheory.EtC.GalSec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentFreeSheafCechLevelSepClosureStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisDescent_freeSheaf_cechLevel_sepClosure : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  first | (exact @GlobalTheory.EtC.GalSec.gal_sec) | (exact GlobalTheory.EtC.GalSec.gal_sec) | (intros; apply GlobalTheory.EtC.GalSec.gal_sec  <;> assumption)
end
