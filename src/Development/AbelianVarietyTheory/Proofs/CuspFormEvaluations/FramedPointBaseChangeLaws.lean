module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramedBaseChange

theorem spec_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spec_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  simp [spMap]

theorem dual_id (T : Type) [CommRing T] : dualMap (RingHom.id T) = RingHom.id _ :=
  RingHom.ext fun x => by
    show TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pulledGroup_hom_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {W : Scheme.{0}} (a b : W ⟶ Gx x)
    (hs : a ≫ (snd (Over.mk x) Xo.univ.t.G).left = b ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : a ≫ (fst (Over.mk x) Xo.univ.t.G).left = b ≫ (fst (Over.mk x) Xo.univ.t.G).left) : a = b := by
  have hw : a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = b ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    have e1 := Over.w (snd (Over.mk x) Xo.univ.t.G)
    rw [← e1, ← Category.assoc, hs, Category.assoc]
  let a' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk b hw.symm
  have e : a' = b' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext hf
    · exact Over.OverMorphism.ext hs
  exact congrArg CommaMorphism.left e

theorem refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid := spec_algHom_id c.F S
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    show spMap (dualMap (RingHom.id S)) = _
    rw [dual_id]
    simp [spMap]
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _,
    Category.id_comp _, by rw [eid]; exact (Category.id_comp _).trans (Category.comp_id _).symm, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
    exact spec_comp φ.toRingHom ψ.toRingHom
  have edsp : spMap (dualMap (ψ.comp φ).toRingHom) =
      spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (ψ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, esp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem cancel {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (κ : T →ₐ[c.F] U) {y0 : FrPt Xo c S} {y : FrPt Xo c T} {z : FrPt Xo c U}
    (h₁ : FrMap φ y0 y) (h₂ : FrMap (κ.comp φ) y0 z) : FrMap κ y z := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (κ.comp φ).toRingHom = spMap κ.toRingHom ≫ spMap φ.toRingHom :=
    spec_comp φ.toRingHom κ.toRingHom
  have edsp : spMap (dualMap (κ.comp φ).toRingHom) =
      spMap (dualMap κ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (κ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  have hx : spMap κ.toRingHom ≫ y.x = z.x := by rw [hx2, hx1, esp, Category.assoc]
  let pm : Gx z.x ⟶ Gx y.x :=
    ((Over.homMk (spMap κ.toRingHom) hx : Over.mk z.x ⟶ Over.mk y.x) ▷ Xo.univ.t.G).left
  have hs : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have hf : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
      (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap κ.toRingHom := by
    rw [← Over.comp_left, whiskerRight_fst]
    rfl
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pulledGroup_hom_ext
    · rw [Category.assoc, hs1, hs, hs2]
    · rw [Category.assoc, hf1, ← Category.assoc, hf, Category.assoc, ← esp, hf2]
  refine ⟨?_, ?_, pm, hs, hf, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    rw [← ha1 i h1', ← ha2 i h2']
    have e : pm1.appLE _ _ h1' ≫ pm.appLE _ _ h = pm2.appLE ((PPx y0.x).U i) ((PPx z.x).U i) h2' := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hcomp _ _ _ _
    rw [← e, CommRingCat.hom_comp, RingHom.comp_apply]

theorem unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h₁ : FrMap φ y z) (h₂ : FrMap φ y z') :
    z = z' := by
  obtain ⟨x1, o1, u1, tan1, eig1, basis1, s1, gen1⟩ := z
  obtain ⟨x2, o2, u2, tan2, eig2, basis2, s2, gen2⟩ := z'
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  dsimp only at hx1 hu1 pm1 hs1 hf1 ha1 hx2 hu2 pm2 hs2 hf2 ha2
  have hx : x1 = x2 := hx1.trans hx2.symm
  subst hx
  have hu : u1 = u2 := funext fun τ => funext fun i => (hu1 τ i).trans (hu2 τ i).symm
  subst hu
  have hpm : pm1 = pm2 := pulledGroup_hom_ext _ _ (hs1.trans hs2.symm) (hf1.trans hf2.symm)
  subst hpm
  have hsf : s1.f = s2.f := funext fun i =>
    (ha1 i (chart_le pm1 hs1 i)).symm.trans (ha2 i (chart_le pm1 hs1 i))
  obtain ⟨f1, c1⟩ := s1
  obtain ⟨f2, c2⟩ := s2
  dsimp only at hsf
  subst hsf
  rfl

theorem isPullSec {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z)
    (h : ptO Xo z.x ⟶ ptO Xo y.x) (hh : h.left = spMap φ.toRingHom) :
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s := by
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  have hpm : pm = (h ▷ Xo.univ.t.G).left := by
    apply pulledGroup_hom_ext
    · rw [hs, ← Over.comp_left, whiskerRight_snd]
    · rw [hf, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hh]
  subst hpm
  intro j
  exact (ha j (chart_le _ hs j)).symm

end GlobalTheory.FramedBaseChange

namespace GlobalTheory

theorem framedPoint_baseChange_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMap (AlgHom.id c.F S) y y) ∧ (∀ (S T U : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U] [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) (y : FrPt Xo c S) (z : FrPt Xo c T) (w : FrPt Xo c U), FrMap φ y z → (FrMap ψ z w ↔ FrMap (ψ.comp φ) y w)) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMap φ y z' → z = z') ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → ∀ h : ptO Xo z.x ⟶ ptO Xo y.x, h.left = spMap φ.toRingHom → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s :=
  fun _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ y => FramedBaseChange.refl y,
     fun _ _ _ _ _ _ _ _ _ φ ψ _ _ _ h₁ =>
       ⟨fun h₂ => FramedBaseChange.trans φ ψ h₁ h₂, fun h₂ => FramedBaseChange.cancel φ ψ h₁ h₂⟩,
     fun _ _ _ _ _ _ φ _ _ _ h₁ h₂ => FramedBaseChange.unique φ h₁ h₂,
     fun _ _ _ _ _ _ φ _ _ hm h hh => FramedBaseChange.isPullSec φ hm h hh⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnivPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def pol (Xo : Moduli D l) : PolAV Xo.X := GlobalTheory.Obj.toPolAV Xo.univ

theorem smooth (Xo : Moduli D l) : Smooth Xo.s :=
  haveI := Xo.smooth
  SmoothOfRelativeDimension.smooth D.dim Xo.s

theorem isLocallyNoetherian (Xo : Moduli D l) : IsLocallyNoetherian Xo.X := by
  haveI := smooth Xo
  exact LocallyOfFiniteType.isLocallyNoetherian Xo.s

theorem isReduced (Xo : Moduli D l) : IsReduced Xo.X := by
  haveI := smooth Xo
  exact GlobalTheory.isReduced_of_smooth_of_isReduced Xo.s

theorem isUnit_natCast (Xo : Moduli D l) (n : ℕ) (hn : 0 < n) : IsUnit (n : Γ(Xo.X, ⊤)) := by
  have hK : IsUnit (n : KA l) := by
    haveI : CharZero (KA l) := (RingHom.charZero_iff (algebraMap (KA l) ℂ).injective).2 inferInstance
    exact (isUnit_iff_ne_zero).2 (Nat.cast_ne_zero.2 hn.ne')
  have hΓ := hK.map ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
  have hX := hΓ.map Xo.s.appTop.hom
  simpa using hX

end UnivPol

theorem moduli_univ_polAV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), IsLocallyNoetherian Xo.X ∧ IsReduced Xo.X ∧ (∀ n : ℕ, 0 < n → IsUnit (n : Γ(Xo.X, ⊤))) ∧ IsAbelianScheme Xo.univ.t.G ∧ ∀ (p : ∀ (A : Over Xo.X) [GrpObj A] [IsCommMonObj A], LB A.left → ℕ → Prop), (∀ P : PolAV Xo.X, p P.A P.L P.g) → p Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo
  exact ⟨UnivPol.isLocallyNoetherian Xo, UnivPol.isReduced Xo, UnivPol.isUnit_natCast Xo,
    ObjDim.isAbelianScheme Xo.univ, fun p h => h (UnivPol.pol Xo)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.exists_faithfullyFlat_pushout (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁]
    [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁)
    (φ₂ : S →ₐ[F] S₂) (h : φ₂.toRingHom.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁ := by
  letI : Algebra S S₁ := φ₁.toRingHom.toAlgebra
  letI : Algebra S S₂ := φ₂.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S₂ := RingHom.faithfullyFlat_algebraMap_iff.1 h
  letI : Algebra F (S₁ ⊗[S] S₂) :=
    ((Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂).comp
      (algebraMap F S₁)).toAlgebra
  have hff : (algebraMap S₁ (S₁ ⊗[S] S₂)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  refine ⟨S₁ ⊗[S] S₂, inferInstance, inferInstance,
    { (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂) with commutes' := fun c => rfl },
    { (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] S₁ ⊗[S] S₂).toRingHom with
      commutes' := fun c => ?_ }, ?_, hff, hff.injective⟩
  · show (1 : S₁) ⊗ₜ[S] algebraMap F S₂ c = algebraMap F S₁ c ⊗ₜ[S] (1 : S₂)
    rw [← φ₁.commutes, ← φ₂.commutes]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm
  · exact AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s

attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat (F S S' : Type) [Field F] [CommRing S]
    [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S')
    (h : φ.toRingHom.FaithfullyFlat) (w : S')
    (hw : ∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T),
      ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) : ∃! v : S, φ v = w := by
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := RingHom.faithfullyFlat_algebraMap_iff.1 h
  have hinj := h.injective
  letI : Algebra F (S' ⊗[S] S') :=
    ((Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S').comp
      (algebraMap F S')).toAlgebra
  let ψ₁ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S') with commutes' := fun c => rfl }
  let ψ₂ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom with
      commutes' := fun c => by
        show (1 : S') ⊗ₜ[S] algebraMap F S' c = algebraMap F S' c ⊗ₜ[S] (1 : S')
        rw [← φ.commutes]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm }
  have hcomp : ψ₁.comp φ = ψ₂.comp φ :=
    AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s
  have hw' : w ⊗ₜ[S] (1 : S') = (1 : S') ⊗ₜ[S] w := hw (S' ⊗[S] S') ψ₁ ψ₂ hcomp
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' w).1
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]; exact hw')
  exact ⟨v, hv, fun v' hv' => hinj (hv'.trans hv.symm)⟩

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.faithfullyFlat_points_baseChange_descent : (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), φ.Flat → (∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : S →+* K), ∃ χ : B →+* K, χ.comp φ = ψ) → φ.FaithfullyFlat) ∧ (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B) (e : B), φ.Flat → ((algebraMap B (Localization.Away e)).comp φ).Flat) ∧ (∀ (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁] [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁) (φ₂ : S →ₐ[F] S₂), φ₂.toRingHom.FaithfullyFlat → ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T), ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁) ∧ ∀ (F S S' : Type) [Field F] [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S'), φ.toRingHom.FaithfullyFlat → ∀ w : S', (∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T), ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) → ∃! v : S, φ v = w := by
  refine ⟨fun S B _ _ φ hflat hpt => ?_, fun S B _ _ φ e hflat => ?_,
    fun F S S₁ S₂ _ _ _ _ _ _ _ φ₁ φ₂ h => _root_.GlobalTheory.exists_faithfullyFlat_pushout F S S₁ S₂ φ₁ φ₂ h,
    fun F S S' _ _ _ _ _ φ h w hw => _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat F S S' φ h w hw⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨hflat, fun p => ?_⟩
    obtain ⟨χ, hχ⟩ := hpt (AlgebraicClosure p.asIdeal.ResidueField)
      ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
        (algebraMap S p.asIdeal.ResidueField))
    refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext ?_⟩
    show Ideal.comap φ (RingHom.ker χ) = p.asIdeal
    rw [RingHom.comap_ker, hχ, RingHom.ker_comp_of_injective _
      (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).injective,
      Ideal.ker_algebraMap_residueField]
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.2 inferInstance)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZhStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ)

theorem act_natCast (m : ℕ) : Xo.univ.t.act.act m = 𝟙 Xo.univ.t.G ^ m := by
  induction m with
  | zero =>
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]; exact mul_eq_left.1 h.symm
  | succ m ih => rw [Nat.cast_succ, Xo.univ.t.act.add, ih, Xo.univ.t.act.one, pow_succ]

theorem comp_list_prod {T T' : Over Xo.X} (h : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map fun x => h ≫ x).prod = h ≫ L.prod := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.prod_nil, MonObj.comp_one]
  | cons x L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem inZh_comp {T T' : Over Xo.X} (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) :
    InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := comp_list_prod Xo h (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j))
    rw [ha.2 mu hmu cm hcm i, MonObj.comp_one, List.map_ofFn] at h1
    simpa only [Function.comp_def, Category.assoc] using h1

theorem inZh_mul {T : Over Xo.X} (a a' : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a)
    (ha' : InZh Xo Λ N a') : InZh Xo Λ N (fun b => a b * a' b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [mul_pow, ha.1 b, ha'.1 b, _root_.mul_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have h2 := ha'.2 mu hmu cm hcm i
    rw [List.prod_ofFn] at h1 h2 ⊢
    have h3 : ∀ j, (a j * a' j) ≫ Xo.univ.t.act.act (cm i j) =
        (a j ≫ Xo.univ.t.act.act (cm i j)) * (a' j ≫ Xo.univ.t.act.act (cm i j)) := fun j => by
      have := Xo.univ.t.act.hom (cm i j)
      exact MonObj.mul_comp _ _ _
    simp only [h3]
    rw [Finset.prod_mul_distrib, h1, h2, _root_.mul_one]

theorem geoInj_comp {S T : Type} [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X)
    (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hz : GeoInj Xo x0 z) :
    GeoInj Xo x1 (fun i b => h ≫ z i b) := by
  intro k _ χ g hg i j hij
  let g' : ptO Xo (spMap (χ.comp ψ) ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap (χ.comp ψ)) rfl
  have hc : spMap (χ.comp ψ) = g.left ≫ h.left := by
    rw [hg, hh]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine hz k (χ.comp ψ) g' rfl (funext fun b => Over.OverMorphism.ext ?_)
  have h1 := congrArg (fun f => f.left) (congrFun hij b)
  change spMap (χ.comp ψ) ≫ (z i b).left = spMap (χ.comp ψ) ≫ (z j b).left
  rw [hc]
  simpa only [Over.comp_left, Category.assoc] using h1

theorem inZh_of_killedBy (hΛ : Λ.TrivAt l.M) {T : Over Xo.X} (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) : InZh Xo Λ N u := by
  classical
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [pow_two, pow_mul, (hu b).1, one_pow]
  · obtain ⟨k, hk, -, hk2⟩ := hΛ
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨hN, e, he⟩ := hu j
    have hv : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.La := by
      refine hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_)
      intro b _
      by_cases hb : b = j
      · subst hb; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne hb]; exact Submodule.zero_mem _
    obtain ⟨m, hm⟩ := Submodule.mem_one.1 (hmu _ hv i (Set.mem_univ i))
    have hm' : (m : E) = (k : E) * mu i j := by
      have : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = (k : E) • (Pi.single j (1 : E) : Fin n → E) := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one] at hm
      exact hm
    have hcmk : cm i j * k = N * m := by
      apply RingOfIntegers.ext
      have h1 : ((cm i j * k : 𝓞 E) : E) = (cm i j : E) * (k : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      have h2 : ((N * m : 𝓞 E) : E) = (N : E) * (m : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      rw [h1, h2, hcm, hm']; ring
    have hM : (l.M : 𝓞 E) ∈ l.Mb := by
      have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
        rw [l.prod]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf h1).1
    have hcop : IsCoprime (k : 𝓞 E) ((l.M : 𝓞 E) ^ e) := (Nat.Coprime.cast hk).pow_right
    obtain ⟨p, q, hpq⟩ := hcop
    have hsplit : cm i j = N * (m * p) + (cm i j * q) * (l.M : 𝓞 E) ^ e := by
      linear_combination (-cm i j) * hpq + p * hcmk
    have := Xo.univ.t.act.hom (m * p)
    show u j ≫ Xo.univ.t.act.act (cm i j) = 1
    rw [hsplit, Xo.univ.t.act.add, MonObj.comp_mul,
      he _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hM e)), _root_.mul_one, Xo.univ.t.act.mul,
      ← Category.assoc, act_natCast, MonObj.comp_pow, Category.comp_id, hN, MonObj.one_comp]

end GlobalTheory.ZhStable

namespace GlobalTheory

theorem inZh_geoInj_stable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) :=
  fun _ _ _ _ _ _ _ Xo _ Λ N =>
    ⟨fun _ _ h a => ZhStable.inZh_comp Xo Λ N h a, fun _ a a' => ZhStable.inZh_mul Xo Λ N a a',
      fun _ _ _ _ x0 x1 ψ h hh _ z => ZhStable.geoInj_comp Xo x0 x1 ψ h hh z,
      fun hΛ _ u => ZhStable.inZh_of_killedBy Xo Λ N hΛ u⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inZh_geoInj_stable_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) := by
  first | exact @GlobalTheory.inZh_geoInj_stable | exact GlobalTheory.inZh_geoInj_stable | (intros; apply GlobalTheory.inZh_geoInj_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatSmulCoeffIsIntegral
namespace GlobalTheory.NatMultipleIntegralCoefficients

theorem exists_nat_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : σ →₀ ℕ, IsIntegral ℤ (AddMonoidAlgebra.coeff ((N : K) • P) m) := by
  classical
  have halg : ∀ x : K, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hx : ∀ x : K, ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
    intro x
    obtain ⟨y, hy, h⟩ := (halg x).exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · rw [e] at h
      simpa using h
    · rw [e] at h
      have h2 := h.neg
      simpa using h2
  choose n hn hi using hx
  refine ⟨∏ m ∈ P.support, n (P.coeff m), Finset.prod_pos fun m _ => hn _, fun m => ?_⟩
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ P.support
  · rw [← Finset.prod_erase_mul _ _ hm, Nat.cast_mul, mul_assoc]
    refine IsIntegral.mul ?_ (hi _)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K)
      (x := ((∏ k ∈ P.support.erase m, n (P.coeff k) : ℕ) : ℤ)))
  · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.NatMultipleIntegralCoefficients
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_natCast_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m, IsIntegral ℤ (((N : K) • P).coeff m) := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | (apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral ..)

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (t : k) (hP : P ∈ HHa r n k cc isX a) :
    t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1,
    fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_natCast_smul_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ N : ℕ, 0 < N ∧ (N : c.F) • P ∈ harmA c a n ∧ ((N : c.F) • P).support = P.support := by
  intro E _ _ _ H Dw l c a n P hP
  haveI := c.fin
  obtain ⟨N, hN, h⟩ := exists_natCast_smul_coeff_isIntegral (K := c.F) P
  refine ⟨N, hN, ⟨smul_mem_HHa _ hP, fun m => h m⟩, ?_⟩
  have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, hN']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsUniqueIsTwistPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_isTwistPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T : Over S) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])), α.IsGen → ∀ s : LB.Sec (LPow A L b T), ∃! s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  intro S A _ L hL T ψ m hm a b α hα s
  obtain ⟨s₀, hs₀⟩ := ThetaPtExist.exists_isTwistPull hL ψ m hm a b α hα s
  refine ⟨s₀, hs₀, fun s₁ hs₁ => ?_⟩

  have hf : ∀ j, s₁.f j = s₀.f j :=
    sec_ext_val (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) hL
      (fun y J hJ => (twist_val hs₁ (𝟙 _) y hJ).trans (twist_val hs₀ (𝟙 _) y hJ).symm)

  obtain ⟨f₁, c₁⟩ := s₁
  obtain ⟨f₀, c₀⟩ := s₀
  obtain rfl : f₁ = f₀ := funext hf
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistBaseChange

theorem eq_pullS_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') : s' = GlobalTheory.VVRank.pullS A a h s := by

  exact DVR.SecOps.sec_ext H

theorem isTwistPull_baseChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T T' : Over S) (h : T' ⟶ T) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (ψ' : T' ⊗ A ⟶ T' ⊗ A) (m' : T' ⊗ A ⟶ A) (hm' : ψ' ≫ snd T' A = m'), ψ' ≫ h ▷ A = h ▷ A ≫ ψ → ∀ (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])), α.IsGen → α'.IsGen → LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α (h ▷ A).left) → ∀ (s : LB.Sec (LPow A L b T)) (t : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L b T')) (t' : LB.Sec (LPow A L a T')), IsTwistPull A L ψ m hm a b α s t → IsPullSec A L b (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) t t' → IsTwistPull A L ψ' m' hm' a b α' s' t' := by
  intro S A _ L hL T T' h ψ m hm ψ' m' hm' hψ a b α α' hα hα' hcorr s t s' t' hst hs ht
  obtain rfl := eq_pullS_of_isPullSec A b h hs
  obtain rfl := eq_pullS_of_isPullSec A a h ht

  have e : ψ'.left ≫ (h ▷ A).left = (h ▷ A).left ≫ ψ.left := by
    rw [← Over.comp_left, hψ, Over.comp_left]
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' (fun y J hJ => ?_)

  have hv : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ hcorr _).trans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ α _ _)
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ,
    GlobalTheory.VVRank.sv_of_isTwistPull A hst _ y hJ, hv]
  simp only [Category.id_comp, e]

end GlobalTheory.TwistBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPowMulCoprimeLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pow_mul_coprime_le {R : Type} [CommRing R] [IsDedekindDomain R] (A K : Ideal R) (hK : K ≠ 0) :
    ∃ (j : ℕ) (J : Ideal R), A ^ j * J ≤ K ∧ A ⊔ J = ⊤ := by
  classical
  rw [Ne, Submodule.zero_eq_bot] at hK
  have hne : ({J : Ideal R | ∃ j : ℕ, A ^ j * J ≤ K}).Nonempty := ⟨K, 0, by simp⟩
  obtain ⟨J, ⟨j, hj⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _ hne
  refine ⟨j, J, hj, ?_⟩

  have hKJ : K ≤ J := by
    by_contra h
    refine hmax (J ⊔ K) ⟨j, ?_⟩ (lt_of_le_of_ne le_sup_left ?_)
    · rw [Ideal.mul_sup]
      exact sup_le hj (Ideal.mul_le_inf.trans inf_le_right)
    · intro e
      exact h (le_sup_right.trans e.symm.le)
  have hJ0 : J ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot]
    rintro rfl
    exact hK (le_bot_iff.mp hKJ)

  by_contra hne'
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne'
  have hJP : J ≤ P := le_trans le_sup_right hle
  have hAP : A ≤ P := le_trans le_sup_left hle
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hJP
  have hQmem : A ^ (j + 1) * Q ≤ K :=
    calc A ^ (j + 1) * Q = A ^ j * (A * Q) := by rw [pow_succ, _root_.mul_assoc]
      _ ≤ A ^ j * (P * Q) := Ideal.mul_mono_right (Ideal.mul_mono_left hAP)
      _ = A ^ j * J := by rw [hQ]
      _ ≤ K := hj
  have hJQ : J ≤ Q := by
    rw [hQ]
    exact (Ideal.mul_le_inf.trans inf_le_right)
  have hQJ : Q = J := by
    by_contra h
    exact hmax Q ⟨j + 1, hQmem⟩ (lt_of_le_of_ne hJQ (Ne.symm h))
  rw [hQJ] at hQ

  exact hP.ne_top (mul_right_cancel₀ hJ0 (hQ.symm.trans (Ideal.top_mul J).symm))

private theorem comp_act_eq_one_of_pow_eq_killed {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) :
    ∀ x ∈ Ideal.span {(N : 𝓞 E)} * l.Mb, w ≫ Xo.univ.t.act.act x = 1 := by
  unfold KilledBy at ht
  have h0 : Xo.univ.t.act.act 0 = 1 := by
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    have h' := congrArg (fun f => f * (Xo.univ.t.act.act 0)⁻¹) h
    simpa using h'.symm

  have hnat : ∀ (n : ℕ) (y : 𝓞 E), Xo.univ.t.act.act ((n : 𝓞 E) * y) = Xo.univ.t.act.act y ^ n := by
    intro n y
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, Xo.univ.t.act.add, ih, pow_succ]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm b hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    have := Xo.univ.t.act.hom b
    have := Xo.univ.t.act.hom c
    have e : c * (N : 𝓞 E) * b = (N : 𝓞 E) * b * c := by ring
    rw [e, Xo.univ.t.act.mul, hnat, ← Category.assoc, MonObj.comp_pow, ← MonObj.pow_comp, hw, ht b hb,
      MonObj.one_comp]
  · intro y z hy hz
    rw [Xo.univ.t.act.add, MonObj.comp_mul, hy, hz, _root_.one_mul]

theorem exists_root_killedBy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) (I J : Ideal (𝓞 E)) (hI : I ≤ l.Mb) (hIJ : I ⊔ J = ⊤)
    (hle : I * J ≤ Ideal.span {(N : 𝓞 E)} * l.Mb) :
    ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo I t' := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hIJ ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ J)
  have ht' := ht
  unfold KilledBy at ht'
  refine ⟨w ≫ Xo.univ.t.act.act j, ?_, ?_⟩
  · have := Xo.univ.t.act.hom j
    rw [← MonObj.pow_comp, hw]
    have h1 : t ≫ Xo.univ.t.act.act i = 1 := ht' i (hI hi)
    calc t ≫ Xo.univ.t.act.act j = (t ≫ Xo.univ.t.act.act i) * (t ≫ Xo.univ.t.act.act j) := by
          rw [h1, _root_.one_mul]
      _ = t ≫ Xo.univ.t.act.act (i + j) := by rw [Xo.univ.t.act.add, MonObj.comp_mul]
      _ = t := by rw [hij, Xo.univ.t.act.one, Category.comp_id]
  · unfold KilledBy
    intro a ha
    rw [Category.assoc, ← Xo.univ.t.act.mul]
    exact comp_act_eq_one_of_pow_eq_killed Xo t w N ht hw _ (hle (_root_.mul_comm a j ▸ Ideal.mul_mem_mul ha hj))

theorem exists_root_killedBy_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Over Xo.X) (t w : T ⟶ Xo.univ.t.G) (N : ℕ), 0 < N → KilledBy Xo l.Mb t → w ^ N = t → (∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) t') ∧ (N = l.M → ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo (l.Mb ^ 2) t') := by
  intro E _ _ _ H Dw l Xo T t w N hN ht hw
  have hMb0 : l.Mb ≠ 0 := by
    intro h
    have hp := l.prod
    rw [h, zero_mul, Submodule.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hp
    have hM : l.M = 0 := by exact_mod_cast hp
    have := l.three_le
    omega
  have hN0 : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  obtain ⟨j, J, hj, hcop⟩ := exists_pow_mul_coprime_le l.Mb _ (mul_ne_zero hN0 hMb0)
  refine ⟨?_, ?_⟩
  · obtain ⟨t', ht'N, ht'⟩ := exists_root_killedBy Xo t w N ht hw (l.Mb ^ (j + 1)) J
      (Ideal.pow_le_self (Nat.succ_ne_zero j)) (Ideal.pow_sup_eq_top hcop)
      (by rw [pow_succ', _root_.mul_assoc]; exact (Ideal.mul_le_inf.trans inf_le_right).trans hj)
    exact ⟨t', ht'N, j + 1, ht'⟩
  · intro hNM
    refine exists_root_killedBy Xo t w N ht hw (l.Mb ^ 2) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
      (Ideal.pow_le_self two_ne_zero) (Ideal.pow_sup_eq_top l.coprime) (le_of_eq ?_)
    rw [sq, _root_.mul_assoc, l.prod, _root_.mul_comm, hNM]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.BetaExistsOfNeOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem betaExists_of_ne_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (c : Coeff l) (n bad : ℕ), bad ≠ 1 → BetaExists (Dw := Dw) c n bad :=
  fun E _ _ _ H Dw l c n bad _ => BetaEx.betaExists E H Dw l c n bad

end GlobalTheory
end
