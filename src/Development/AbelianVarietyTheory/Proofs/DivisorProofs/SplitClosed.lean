module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def TwoTorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x : Over.mk (spMap (algebraMap (FractionRing R) F) ≫ jK R) ⟶ G),
    x * x = 1 → ∃ y : Over.mk (jK R) ⟶ G, x.left = spMap (algebraMap (FractionRing R) F) ≫ y.left

def SplitClosed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem abelianScheme_constLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (s : R₀ →+* R), π.comp s = RingHom.id R₀ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (_ : IsGrpPullback A₀ A (spMap π) i),
        IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom := by
  intro R R₀ _ _ π s hs A₀ _ g hA hg
  have hAs := isGrpPullback_pullback A₀ (spMap s)
  have hid : spMap π ≫ spMap s = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
    exact Spec.map_id _
  have hBA := isGrpPullback_pullback ((Over.pullback (spMap s)).obj A₀) (spMap π)
  have hB0 := (hBA.comp hAs).congr hid rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso hB0 (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h0B := isGrpPullback_of_iso e.symm
  refine ⟨(Over.pullback (spMap s)).obj A₀, inferInstance, _, (h0B.comp hBA).congr (Category.id_comp _) rfl,
    isAbelianScheme_pullback_obj (spMap s) A₀ hA, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def UT (N : Near π G) : Over (pullback π π) := Over.mk (pullback.snd N.U.hom (pullback.fst π π ≫ π))

def toS (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback N.U.hom π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [Category.assoc, hp]; exact pullback.condition)

def embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback G.hom p :=
  pullback.lift (toS N p hp ≫ N.u) (pullback.snd _ _) (by
    rw [Category.assoc, N.u_over, toS, pullback.lift_snd])

def emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⟶ (Over.pullback p).obj G :=
  Over.homMk (embL N p hp) (pullback.lift_snd _ _ _)

def sum [GrpObj G] (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⊗ UT N ⟶ (Over.pullback p).obj G :=
  (fst (UT N) (UT N) ≫ emb N p hp) * (snd (UT N) (UT N) ≫ emb N p hp)

end GlobalTheory.Mum.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_le_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) :
    α ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hW hy

theorem locInt_le_gen {S G Y T : Scheme.{0}} (g : G ⟶ S) (α : Y ⟶ G) (t : Y ⟶ T) (e : T ⟶ S)
    (hpb : α ≫ g = t ≫ e) (W : G.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) :
    α ⁻¹ᵁ W ≤ t ⁻¹ᵁ (e ⁻¹ᵁ U) := by
  intro y hy
  have h1 : g (α y) ∈ U := hWU hy
  have h2 : (α ≫ g) y = (t ≫ e) y := by rw [hpb]
  show e (t y) ∈ U
  rw [← Scheme.Hom.comp_apply, ← h2]
  exact h1

def LocInt {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left) {Y : Scheme.{0}}
    (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : α ≫ G.hom = t ≫ M.gp) {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens) (hW : W ≤ L.U j) (hWU : W ≤ G.hom ⁻¹ᵁ U),
    IsAffineOpen W → IsAffineOpen U →
    ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)),
      (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j)) =
        ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb W U hWU)).hom (b m)

theorem le_preimage_of_comp_eq {X X' S : Scheme.{0}} (g : X ⟶ S) (g' : X ⟶ X') (h : X' ⟶ S) (e : g' ≫ h = g)
    (U : S.Opens) : g ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ U) := by
  intro x hx
  show h (g' x) ∈ U
  rw [← Scheme.Hom.comp_apply, e]
  exact hx

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open GlobalTheory.DeRham (push push_comp push_congr push_id push_mul)
open GlobalTheory.AbDual (isMonHom_one push_one)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

theorem isMonHom_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact isMonHom_one A A
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem push_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    haveI := isMonHom_id_pow A n
    push κ t ((𝟙 A) ^ n : A ⟶ A) = (n : R) • LinearMap.id := by
  induction n with
  | zero =>
    haveI := isMonHom_id_pow A 0
    rw [push_congr κ t (pow_zero (𝟙 A)), push_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    haveI := isMonHom_id_pow A n
    haveI := isMonHom_id_pow A (n + 1)
    haveI : IsMonHom ((𝟙 A) ^ n * 𝟙 A) := inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))
    rw [push_congr κ t (pow_succ (𝟙 A) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]

end Push

theorem bijective_push {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)
    {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) (h : B ⟶ A)
    [IsMonHom f] [IsMonHom h] (m : ℕ) (hm : IsUnit (m : R)) (e₁ : f ≫ h = 𝟙 A ^ m) (e₂ : h ≫ f = 𝟙 B ^ m) :
    Function.Bijective (push κ t f) := by
  haveI := isMonHom_id_pow A m
  haveI := isMonHom_id_pow B m
  have k₁ : ∀ x, push κ t h (push κ t f x) = (m : R) • x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₁, push_id_pow]; rfl
  have k₂ : ∀ y, push κ t f (push κ t h y) = (m : R) • y := fun y ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₂, push_id_pow]; rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push κ t h ((↑hm.unit⁻¹ : R) • y), ?_⟩⟩
  · have e := congrArg (push κ t h) hxy
    rw [k₁, k₁] at e
    exact (hm.smul_left_cancel).1 e
  · rw [k₂, smul_smul, hm.mul_val_inv, one_smul]

end GlobalTheory.PolPrimeTo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirational
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hb E'
  have e := GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s
  have hc : ∀ a, Cartier.constFn p a ∈ E'.ring.comap (functionFieldMap s) := fun a => by
    show functionFieldMap s (Cartier.constFn p a) ∈ E'.ring
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  let ψ : E'.ring.comap (functionFieldMap s) →+* E'.ring :=
    (functionFieldMap s).restrict _ E'.ring fun _ hx => hx
  have hψb : Function.Bijective ψ := by
    refine ⟨fun x y h => Subtype.ext (hb.1 (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hb.2 (y : Y.functionField)
    exact ⟨⟨x, show functionFieldMap s x ∈ E'.ring from hx ▸ y.2⟩, Subtype.ext hx⟩
  let eq : E'.ring.comap (functionFieldMap s) ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  have hdvr : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap s)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eq.symm
  have hcomp : eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem) =
      (Cartier.constFn p).codRestrict _ hc := by
    refine RingHom.ext fun a => eq.injective ?_
    rw [RingHom.comp_apply]
    erw [RingEquiv.apply_symm_apply]
    exact Subtype.ext (RingHom.congr_fun e a).symm
  have hess : ((Cartier.constFn p).codRestrict _ hc).EssFiniteType := by
    rw [← hcomp]
    have h1 := E'.essFiniteType
    letI := ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem).toAlgebra
    letI := (eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem)).toAlgebra
    haveI : Algebra.EssFiniteType k E'.ring := h1
    let f : E'.ring →ₐ[k] E'.ring.comap (functionFieldMap s) :=
      { eq.symm.toRingHom with commutes' := fun _ => rfl }
    exact Algebra.EssFiniteType.of_surjective f eq.symm.surjective
  exact ⟨⟨E'.ring.comap (functionFieldMap s), hc, hdvr, hess⟩, fun _ => Iff.rfl⟩

end GlobalTheory.Discrepancy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirationalStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_target_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective | exact GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section Gen

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem corrForm_antisymm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x := by
  obtain ⟨n, a, b, hc, hφ⟩ := id H
  let s : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)
  have ms : IsMor κ ((A ⊗ A).hom ≫ t) κ ((A ⊗ A).hom ≫ t) (RingHom.id R) s.left :=
    IsMor.of_over κ (φ := s.left) (by rw [← Category.assoc, Over.w])
  have hz := isChern_pull ms hc
  rw [crystallinePull2_sum_cup s ms] at hz
  simp only [pullOver_pullOver, s, lift_fst, lift_snd] at hz
  have e' : LBIso (P.pull s.left) P :=
    (cls_eq_iff (pull_isLB hP _) hP).1 ((cls_eq_iff hP (pull_isLB hP _)).2 hs).symm
  have hz' := (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ (pull_isLB hP _) hP e' _ hz
  have H' : IsCorrForm κ t A A P (-φ.flip) := by
    refine ⟨n, fun k ↦ -b k, a, (congrArg (IsChern κ ((A ⊗ A).hom ≫ t) P) ?_).mp hz', fun u v ↦ ?_⟩
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Submodule.coe_neg, map_neg, LinearMap.map_neg, LinearMap.neg_apply]
      exact (neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)).symm
    · simp only [LinearMap.neg_apply, LinearMap.flip_apply]
      rw [hφ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_neg, neg_mul, mul_comm]
  have e := congrArg (fun f ↦ f x y) (H.unique C hP H')
  simpa using e

end Gen

section Jet

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

end Jet

section Diag

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

end Diag

section Props

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  {I : Type} [Fintype I]

end Props

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

end BC

end GlobalTheory.JetIsotropic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem isLocalRing_dualNumber_field (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

theorem pic_sp_local_eq_zero (R : Type) [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨V, hV, h⟩ := exists_pull_eq_zero c (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have e := pull_eq_zero_of_mem V (𝟙 _) (fun z ↦ by rw [hV']; trivial) h
  rwa [pull_id] at e

theorem ringHom_dualNumber_factor {k K : Type} [CommRing k] [Field K] (φ : DualNumber k →+* K) :
    φ = (φ.comp (dnInl k)).comp (dnFst k) := by
  have hε : φ DualNumber.eps = 0 := by
    have e : φ DualNumber.eps * φ DualNumber.eps = 0 := by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 e
  refine RingHom.ext fun x ↦ ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add (f := _), DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, hε, mul_zero, add_zero]
  rfl

theorem fam_of_triv_mod_eps : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k]
    (s : Sp (DualNumber k) ⟶ S) (D : LB (A ⊗ Over.mk s).left) (hD : D.IsLB),
    GlobalTheory.CechPic.pull (A ◁ ptMap s (dnFst k)).left (cls D hD) = 0 → Fam A D := by
  intro S A _ hA k _ s D hD h0
  haveI := isLocalRing_dualNumber_field k
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)
  haveI : IsLocallyNoetherian (Over.mk s).left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  refine ⟨hD, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A (Over.mk s) hA D hD ?_ ?_⟩
  · rw [triv_ev_iff hD]
    exact pic_sp_local_eq_zero _ _
  · intro K _ _ s' t
    obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
    set ψ : k →+* K := φ.hom.comp (dnInl k)
    have ht : t.left = spMap ψ ≫ spMap (dnFst k) := by
      rw [← hφ, ← Spec.map_comp]
      congr 1
      ext1
      exact ringHom_dualNumber_factor φ.hom
    have hN : (ev D (fst A (Over.mk s')) (snd A (Over.mk s') ≫ t)).IsLB := pull_isLB hD _
    refine (isAdditive_iff hN).2 fun Y a a' y ↦ ?_
    have key : ∀ b : Y ⟶ A, evc hN b y = 0 := fun b ↦ by
      rw [evc_ev hD, lift_fst, lift_snd_assoc]
      let u : Y ⟶ Over.mk (spMap (dnFst k) ≫ s) := Over.homMk (y.left ≫ spMap ψ) (by
        have e1 : y.left ≫ s' = Y.hom := by simpa using Over.w y
        have e2 : t.left ≫ s = s' := by simpa using Over.w t
        simp only [Over.mk_hom]
        rw [Category.assoc, ← Category.assoc (spMap ψ), ← ht, e2, e1])
      have hu : y ≫ t = u ≫ ptMap s (dnFst k) := by
        refine Over.OverMorphism.ext ?_
        simp only [Over.comp_left, ptMap_left, ht]
        rfl
      rw [hu, evc, ← lift_whiskerLeft, Over.comp_left, pull_comp, h0, map_zero]
    rw [key, key, key, add_zero]

end GlobalTheory.DualOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilonStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFamily_of_trivial_mod_epsilon : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] (s : Sp (DualNumber k) ⟶ S) (D : LB (A ⊗ Over.mk s).left) (hD : D.IsLB), GlobalTheory.CechPic.pull (A ◁ ptMap s (dnFst k)).left (cls D hD) = 0 → Fam A D := by
  first | exact @GlobalTheory.DualOpen.fam_of_triv_mod_eps | exact GlobalTheory.DualOpen.fam_of_triv_mod_eps | (intros; apply GlobalTheory.DualOpen.fam_of_triv_mod_eps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPolAV
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PowPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.SiegelPower

def siegLam (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] (P : PolAV (Sp R)) [IsCommMonObj P.A] :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := P.A
  ab := P.isAb
  P := abelian₂ P.A P.L
  isLB := LB.isLB_linComb P.isLB _ _
  rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG P.isAb (pull_isLB (LB.isLB_linComb P.isLB _ _) _) _

theorem det_eq_one {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hpd : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (hdet : IsUnit (W + W.transpose).det) : (W + W.transpose).det = 1 := by
  have h₁ := hpd.det_pos
  have h₂ : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).det = (((W + W.transpose).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [h₂] at h₁
  rcases Int.isUnit_iff.1 hdet with h | h
  · exact h
  · rw [h] at h₁; norm_num at h₁

theorem exists_pow_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ P.A)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ P'.g = r * P.g ∧ LBIso P'.L (LB.LinComb P.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ P r W hpd hdet
  have := P.isAb.comm
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLam hG P
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hfin : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := inferInstanceAs (IsFinite (𝟙 P.A.left))
  have hamp : RelAmple c.A c.diag := by
    have e := lbIso_diag L₁ P
    have h := relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB hfin
    exact (relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) (lbPow P.L 2) 1 one_pos P.isAb P.isAb
      (LB.isLB_linComb P.isLB _ _) hfin).2.2.2 _ hD e (h.2.1.2 P.ample)
  let G := Out.powObj P.A r
  let pr : Fin r → (G ⟶ P.A) := Out.powPr P.A
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ P.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit P.A r).lift (Fan.mk T y), fun u => (Out.powIsLimit P.A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit P.A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme P.A P.isAb r
            g := r * P.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r P.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit P.A r⟩, rfl, ?_⟩
  refine lbIso_nested P.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls P.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls P.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.PowPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPower
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

section SlopeTestRemainingChoices

open GlobalTheory GlobalTheory.CM GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_lam_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) [IsCommMonObj P.A] {T : Over S}
    (z : T ⟶ P.A) (h : lam (cls P.L P.isLB) (fst T P.A ≫ z) (snd T P.A) = 0) : z = 1 := by
  have hL := P.isLB
  have hc : (cubeLB P.A ![fst T P.A ≫ z, snd T P.A] P.L).IsLB := LB.isLB_linComb hL _ _
  have g₂ : GlobalTheory.KerPow.HasGen P.L
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) :=
    (cls_eq_zero_iff hc).1 ((cls_cube_two hL _ _ hc).trans h)
  have g₃ : LocGen P.L (fst T P.A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T P.A).left z.left (b := (fst T P.A ≫ z).left) rfl
  have b₀ := locGen_base hL (fst T P.A).left (1 : T ⟶ P.A).left (b := (1 : T ⊗ P.A ⟶ P.A).left)
    (congrArg (fun q : T ⊗ P.A ⟶ P.A => q.left) (MonObj.comp_one (fst T P.A) : fst T P.A ≫ (1 : T ⟶ P.A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ P.A ⟶ P.A).left, (fst T P.A ≫ z).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen P.ktriv z (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T P.A ≫ z) * snd T P.A).left * (k (fst T P.A ≫ z).left)⁻¹ * (k (snd T P.A).left)⁻¹ *
    k (1 : T ⊗ P.A ⟶ P.A).left *
    (k (1 : T ⊗ P.A ⟶ P.A).left ^ (1 : ℤ) * k (fst T P.A ≫ z).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T P.A ≫ z) * snd T P.A).left ^ (1 : ℤ) * k (snd T P.A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end SlopeTestRemainingChoices

end GlobalTheory.KillSquare

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

theorem pow_sq_eq_one_of_lam_trivial : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), IsMonHom ψ → IsMonHom ρ →
      ψ ≫ ρ = (𝟙 A) ^ N → ρ ≫ ψ = (𝟙 P.A) ^ N →
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ^ (N * N) = 1 := by
  intro A _ hA M hM P ψ ρ N hψ hρ h1 h2 hiso T x hx
  haveI : IsCommMonObj A := hA.comm
  haveI := P.isAb
  have hL := P.isLB
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ P.A P.isAb P.L hL
  set ℓ := cls P.L hL
  set m := cls M hM

  have hlamA : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hpair : lam m (fst A A) (snd A A) = lam ℓ (fst A A ≫ ψ) (snd A A ≫ ψ) := by
    have hlamP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb hL _ _
    have e := (cls_eq_iff hlamA (pull_isLB hlamP _)).2 hiso
    exact (cls_cube_two hM (fst A A) (snd A A) hlamA).symm.trans (e.trans (Elliptic.cls_pull_lam hL _ _ _))

  have hx0 : lam m (fst A T) (snd A T ≫ x) = 0 := by
    rw [← Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamA _)]
    exact (cls_eq_zero_iff _).2 hx
  have e1 := congrArg (pull (lift (fst A T) (snd A T ≫ x)).left) hpair
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e1
  rw [e1] at hx0

  have e2 := congrArg (pull (lift (fst P.A T ≫ ρ) (snd P.A T)).left) hx0
  simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, Category.assoc] at e2
  have e3 : fst P.A T ≫ ρ ≫ ψ = fst P.A T ^ N := by
    rw [h2, MonObj.comp_pow, Category.comp_id]
  rw [e3, lam_pow_left hL hΘ, ← lam_pow_right hL hΘ, ← MonObj.comp_pow] at e2

  have hz : (x ≫ ψ) ^ N = 1 := by
    refine GlobalTheory.KillSquare.eq_one_of_lam_eq_zero P _ ?_
    have e4 := congrArg (pull (lift (snd T P.A) (fst T P.A)).left) e2
    simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at e4
    rw [lam_comm] at e4
    simpa only [Category.assoc] using e4
  rw [pow_mul]
  have e5 : x ^ N = (x ≫ ψ) ≫ ρ := by
    rw [Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
  rw [e5, ← MonObj.pow_comp, hz, MonObj.one_comp]

end GlobalTheory.KillSquare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RosatiSymmetry

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem padd_comm' {T : Over S} (x y : T ⟶ A) : padd A x y = padd A y x := by
  show x * y = y * x
  exact mul_comm x y

abbrev sw : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)

theorem sw_padd (x y : A ⊗ A ⟶ A) : sw A ≫ padd A x y = padd A (sw A ≫ x) (sw A ≫ y) := by
  simp only [padd, comp_lift_assoc]

theorem formEq_sw (f g : A ⟶ A) (Y : Scheme.{0}) (p : Y ⟶ (A ⊗ A).left) :
    FormEq (fun k => p ≫ (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k)
      (fun k => p ≫ rosatiφ A f g k) rosatiε := by
  intro U _ h
  have e0 : (sw A).left ≫ (padd A (fst A A ≫ g) (snd A A)).left = (padd A (fst A A) (snd A A ≫ g)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst_assoc, lift_snd]
  have e1 : (sw A).left ≫ (fst A A ≫ g).left = (snd A A ≫ g).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have e2 : (sw A).left ≫ (snd A A).left = (fst A A).left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : (sw A).left ≫ (padd A (fst A A) (snd A A ≫ f)).left = (padd A (fst A A ≫ f) (snd A A)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst, lift_snd_assoc]
  have e4 : (sw A).left ≫ (fst A A).left = (snd A A).left := by
    rw [← Over.comp_left, lift_fst]
  have e5 : (sw A).left ≫ (snd A A ≫ f).left = (fst A A ≫ f).left := by
    rw [← Over.comp_left, lift_snd_assoc]
  simp only [Fin.prod_univ_six, rosatiφ, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.head_cons, e0, e1, e2, e3, e4, e5]
  simp only [neg_neg, zpow_neg, zpow_one]
  ac_rfl

theorem formEq_sw' (f g : A ⟶ A) :
    FormEq (fun k => (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k) (rosatiφ A f g) rosatiε := by
  simpa only [Category.id_comp] using formEq_sw A f g _ (𝟙 _)

theorem rosatiAdj_symm (L : LB A.left) (hL : L.IsLB) (f g : A ⟶ A) (h : RosatiAdj A L f g) : RosatiAdj A L g f := by
  intro s
  obtain ⟨U, hs, t, ht⟩ := h s
  refine ⟨U, hs, ?_⟩
  have hW : (A ⊗ A).hom ⁻¹ᵁ U ≤ (sw A).left ⁻¹ᵁ ((A ⊗ A).hom ⁻¹ᵁ U) := by
    intro x hx
    show ((sw A).left ≫ (A ⊗ A).hom) x ∈ U
    rw [Over.w]; exact hx
  let σ := (sw A).left.resLE ((A ⊗ A).hom ⁻¹ᵁ U) ((A ⊗ A).hom ⁻¹ᵁ U) hW
  have hσ : σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left := Scheme.Hom.resLE_comp_ι _ _
  have hF : FormEq (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) (fun k => - rosatiε k)
      (fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A g f k) rosatiε := by
    have e : (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) =
        fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left ≫ rosatiφ A f g k := by
      funext k; rw [← Category.assoc, hσ, Category.assoc]
    rw [e]; exact formEq_sw A g f _ _
  obtain ⟨t', ht', -⟩ := exists_gen hL hF (LB.invGen L _ _ (LB.pullGen L _ _ t σ))
    (DVR.invGen_isGen L _ _ _ (DVR.pullGen_isGen L _ _ t ht σ))
  exact ⟨t', ht'⟩

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum.RosatiSymmetry
variable {R : Type} [CommRing R] [IsDomain R]

theorem val_tau_symm (D : DegPre R) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (r : Z ⟶ (TK R).left) (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  simp only [DegPre.tau, val_mul hJ, val_inv]
  have e : val (D.psi (a + b)) r z J = val (D.psi (b + a)) r z J := by rw [add_comm]
  rw [e, mul_right_comm (val (D.psi (b + a)) r z J)]

theorem tauBal_symm (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) (H : D.TauBal f g a a') :
    D.TauBal g f a' a := by
  intro u' hu' hn y y'
  have hL := D.P.isLB
  obtain ⟨u, hu, hv⟩ := exists_gen hL (formEq_sw' D.P.A f g)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u' (sw D.P.A).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ u' hu' _))
  have hz : zero2 D.P.A ≫ (sw D.P.A).left = zero2 D.P.A := by
    rw [zero2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hp : D.pt2 y' y ≫ (sw D.P.A).left = D.pt2 y y' := by
    rw [DegPre.pt2, DegPre.pt2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hnu : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) := by
    refine corr_of_val hL fun z J hJ => ?_
    have h1 := val_corr hJ hn (𝟙 _)
    rw [val_pull hJ, val_one] at h1
    rw [val_pull hJ, val_one, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hz, h1, inv_one]
  have H' := H u hu hnu y' y
  refine corr_of_val hL fun z J hJ => ?_
  have h2 := val_corr hJ H' (𝟙 _)
  rw [val_mul hJ, val_pull hJ, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hp] at h2
  rw [val_mul hJ, val_pull hJ, val_tau_symm D hJ _ (a' y) y', ← h2, val_tau_symm D hJ _ (a y') y]
  group

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum

theorem endData_symm_and_ofOAct : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    (∀ (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X), EndData D a a' h h' → EndData D a' a h' h) ∧
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (x : O),
      EndData D (o.onB.act x) (o.onB.act (star x)) (DistribSMul.toAddMonoidHom D.X x)
        (DistribSMul.toAddMonoidHom D.X (star x)) := by
  intro R _ _ D
  refine ⟨fun a a' h h' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h2, h1, RosatiSymmetry.rosatiAdj_symm D.P.A D.P.L D.P.isLB a a' h3,
    h5, h4, RosatiSymmetry.tauBal_symm D a a' h h' h6⟩, fun O _ _ _ o x => ?_⟩
  exact ⟨o.onB.hom x, o.onB.hom (star x), o.onB.rosati x, fun y => o.c_lin x y, fun y => o.c_lin (star x) y,
    o.tau_bal x⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GalMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') (σ : Gal ρ) (a : G'.left ⟶ G'.left) : Prop :=
  IsGrpPullback G' G' (spMap (Gal.hom σ)) a ∧
    ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem holUnif_dim_eq_of_linear {A : Over (Sp ℂ)} [GrpObj A] {L L' : LB A.left} {g g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A L' g') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := GlobalTheory.AHWeil.eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

end GlobalTheory.RealMult.Obj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrict
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem functionFieldMap_bijective_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  intro X Y _ _ s _ U hU hiso
  have hg : s (genericPoint Y) = genericPoint X := by
    have h := (genericPoint_spec Y).image s.continuous
    rw [Set.image_univ, s.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec X)
  have hmem : genericPoint Y ∈ s ⁻¹ᵁ U := by
    change s (genericPoint Y) ∈ U
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩) :=
    ((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _
  have h2 : IsIso (s.stalkMap (genericPoint Y)) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1
  have h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h) := by
    rintro x y rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  unfold functionFieldMap
  have h4 := h3 _ _ hg (hg ▸ specializes_rfl)
  exact ConcreteCategory.bijective_of_isIso _

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCalculusStatement
set_option autoImplicit false
noncomputable section
open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical

namespace GlobalTheory.JetCalcPf

end GlobalTheory.JetCalcPf

namespace GlobalTheory.JetCalcPf

variable {I : Type} [Fintype I] {n : ℕ}

end GlobalTheory.JetCalcPf
end
end
