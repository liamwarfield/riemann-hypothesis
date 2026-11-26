module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem isDual_of_iso (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left) (h : IsDual A B' P') (hP : P.IsLB) (x : B ⟶ B') (hx : IsIso x)
    (hm : IsMonHom x) (e : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : IsDual A B P := by
  have c : cls P hP = cls _ (pull_isLB h.isLB (lift (fst A B) (snd A B ≫ x)).left) :=
    (cls_eq_iff _ _).2 e
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    rw [evc, c, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (M : LB (A ⊗ T).left) (hM : M.IsLB) (w : T ⟶ B),
      LBIso M (ev P (fst A T) (snd A T ≫ w)) ↔ LBIso M (ev P' (fst A T) (snd A T ≫ w ≫ x)) := by
    intro T M hM w
    rw [← cls_eq_iff hM (pull_isLB hP _), ← cls_eq_iff hM (pull_isLB h.isLB _), cls_ev hP, cls_ev h.isLB, key,
      Category.assoc]
  refine ⟨hP, (isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (triv_ev_iff hP _ _).2 ?_, fun T M hM hM' ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ x)
  · rw [key, MonObj.one_comp]
    exact (triv_ev_iff h.isLB _ _).1 h.zero
  · obtain ⟨z, hz, hu⟩ := h.univ T M hM hM'
    refine ⟨z ≫ inv x, (iso T M hM _).2 ?_, fun w hw ↦ ?_⟩
    · rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · rw [← hu _ ((iso T M hM w).1 hw), Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem transport : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → P.IsLB → ∀ x : B ⟶ B', IsIso x → IsMonHom x → LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsDual A B P :=
  fun S A B B' _ _ _ P P' h hP x hx hm e ↦ isDual_of_iso S A B B' P P' h hP x hx hm e

end GlobalTheory.AbDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pullTop {X Y : Scheme.{0}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ := Units.map f.appTop.hom

def pmap {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ T ⟶ A' ⊗ T := lift (fst A T ≫ q) (snd A T)

def actMap {A N : Over S} [GrpObj A] (i : N ⟶ A) (T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (N ⊗ T) * (snd A (N ⊗ T) ≫ fst N T ≫ i)) (snd A (N ⊗ T) ≫ snd N T)

def prMap (A N T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T := lift (fst A (N ⊗ T)) (snd A (N ⊗ T) ≫ snd N T)

def IsCharacter {N T : Over S} [GrpObj N] (χ : Γ((N ⊗ T).left, ⊤)ˣ) : Prop :=
  pullTop (lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T)).left χ =
    pullTop (lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T)).left χ * pullTop (snd N (N ⊗ T)).left χ

def IsPullGen {X Y : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) : Prop :=
  ∀ (k l : M.ι) (W : X.Opens) (h₁ : W ≤ p ⁻¹ᵁ M.U k) (h₂ : W ≤ p ⁻¹ᵁ M.U l) (h₃ : W ≤ p ⁻¹ᵁ (M.U k ⊓ M.U l)),
    res h₁ (e k) = res h₃ (pullU p _ (M.g k l)) * res h₂ (e l)

def IsEquivGen {A A' N T : Over S} [GrpObj A] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ)
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) : Prop :=
  IsPullGen (pmap q T).left M e ∧
    ∀ (k : M.ι) (W : (A ⊗ (N ⊗ T)).left.Opens)
      (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))
      (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)),
      res h₁ (pullU (actMap i T).left _ (e k)) =
        res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ (e k))

end GlobalTheory.CharKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_map_dvd_of_valuationRing {V T : Type} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing T] [IsDomain T] (ψ : V →+* T) (hψ : Function.Injective ψ) [IsLocalHom ψ] {a b : V}
    (ha : a ≠ 0) (h : ψ a ∣ ψ b) : a ∣ b := by
  rcases ValuationRing.dvd_total a b with hab | hba
  · exact hab
  · obtain ⟨c, hc⟩ := hba
    obtain ⟨d, hd⟩ := h
    have hb : b ≠ 0 := by rintro rfl; exact ha (by simpa using hc)
    have hψb : ψ b ≠ 0 := fun e => hb (hψ (e.trans (map_zero ψ).symm))
    have h1 : ψ b * (ψ c * d) = ψ b * 1 := by
      rw [mul_one]; nth_rewrite 2 [hd]; rw [hc, map_mul]; ring
    have hcu : IsUnit (ψ c) := IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hψb h1)
    have hc' : IsUnit c := isUnit_of_map_unit ψ c hcu
    exact (Units.dvd_mul_right (u := hc'.unit)).mp (by rw [IsUnit.unit_spec, ← hc])

theorem dvd_of_forall_complete_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
      ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  intro R _ _ _ _ _ _ f g hg H
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hg' : algebraMap R K g ≠ 0 := fun e => hg (hinj (e.trans (map_zero _).symm))
  by_contra hnd
  have hx : ¬ ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) →
      algebraMap R K f / algebraMap R K g ∈ V := by
    intro hall
    obtain ⟨r, hr⟩ := GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring (R := R) (K := K) hall
    apply hnd
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hg']
  push_neg at hx
  obtain ⟨V, hV, h1, h2, hxV⟩ := hx
  have hdom : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring :=
    (GlobalTheory.localSubring_range_le_valuationSubring_iff _ _).mpr ⟨h1, h2⟩
  obtain ⟨-, hc, -, h, hρi, hρl⟩ :=
    (GlobalTheory.discreteValuationRing_dominating_noetherian_local R K K).2.2 V hdom
  have hd := H (AdicCompletion (maximalIdeal V) V) hc _ hρi hρl
  let a : V := ⟨algebraMap R K g, h g⟩
  let b : V := ⟨algebraMap R K f, h f⟩
  have ha : a ≠ 0 := fun e => hg' (congrArg Subtype.val e)
  obtain ⟨c, hcab⟩ := dvd_of_map_dvd_of_valuationRing (algebraMap V (AdicCompletion (maximalIdeal V) V))
    (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V) ha hd
  apply hxV
  have : algebraMap R K f = algebraMap R K g * (c : K) := congrArg Subtype.val hcab
  rw [this, mul_div_cancel_left₀ _ hg']
  exact c.2

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominatingStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_forall_complete_dvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  first | exact @GlobalTheory.Poinc.dvd_of_forall_complete_dvr | exact GlobalTheory.Poinc.dvd_of_forall_complete_dvr | (intros; apply GlobalTheory.Poinc.dvd_of_forall_complete_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surj_restrict_snd {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (Y : Over S)
    (V : Y.left.Opens) : Function.Surjective ((snd A Y).left ∣_ V).appTop.hom := by
  let T : Over S := Over.mk (V.ι ≫ Y.hom)
  let j : T ⟶ Y := Over.homMk V.ι rfl
  let m : (A ⊗ T).left ⟶ (A ⊗ Y).left := (lift (fst A T) (snd A T ≫ j)).left
  have hT : IsPullback (fst A T).left (snd A T).left A.hom (V.ι ≫ Y.hom) := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : m ≫ (fst A Y).left = (fst A T).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : m ≫ (snd A Y).left = (snd A T).left ≫ V.ι := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]; rfl
  have H : IsPullback m (snd A T).left (snd A Y).left V.ι :=
    IsPullback.of_right (by rw [m₁]; exact hT) m₂ hY
  let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict (snd A Y).left V) H.flip
  have he : e.hom ≫ (snd A T).left = (snd A Y).left ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hq : Function.Surjective (snd A T).left.appTop.hom := surj_snd GlobalTheory.SemiRigid.globalFns hA T
  have hi : Function.Surjective e.hom.appTop.hom := by
    have : IsIso (e.hom.app ⊤) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  rw [← he]
  exact surj_comp hi hq

theorem same_of_local : ∀ (S : Scheme.{0}) (A T U : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (Y : Over S) (y : Y ⟶ T) (u : Y ⟶ U),
    (∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      Same A N M (z ≫ y) (z ≫ u)) → Same A N M y u := by
  intro S A T U _ hA N M hN hM Y y u loc
  rw [same_iff hN.isLB hM.isLB]
  rw [← sub_eq_zero]
  obtain ⟨L, hL, hc⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hc, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 (CubeGlue.triv_of_locally_triv hL (snd A Y).left (lift 1 (𝟙 Y)).left ?_
    (surj_restrict_snd hA Y) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key]
    simp only [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  · intro p
    obtain ⟨Z, z, hz, ⟨q, hq⟩, hs⟩ := loc p
    refine ⟨z.left.opensRange, ⟨q, hq⟩, ?_⟩
    let V := (snd A Y).left ⁻¹ᵁ z.left.opensRange
    let X' : Over S := Over.mk (V.ι ≫ (A ⊗ Y).hom)
    let i : X' ⟶ A ⊗ Y := Over.homMk V.ι rfl
    have hr : Set.range (i ≫ snd A Y).left ⊆ Set.range z.left := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    let t : X' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ snd A Y).left hr) (by
      rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have ht : t ≫ z = i ≫ snd A Y := by
      ext1; exact IsOpenImmersion.lift_fac _ _ _
    rw [same_iff hN.isLB hM.isLB] at hs
    have e := congrArg (CechPic.pull (lift (i ≫ fst A Y) t).left) hs
    simp only [pull_evc, lift_fst, lift_snd_assoc] at e
    rw [← Category.assoc t z y, ← Category.assoc t z u, ht, Category.assoc, Category.assoc] at e
    show Triv (L.pull i.left)
    rw [key, pull_evc, pull_evc]
    exact e

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.SpecialConn

variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))

abbrev thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.mk _

def thickR (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1 + 1) →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem thickR_comp (n : ℕ) : (thickR O n).comp (thickQ O (n + 1)) = thickQ O n := rfl

def thickFib (n : ℕ) : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (thickQ O n)))

def thickι (n : ℕ) : thickFib f n ⟶ Y := pullback.fst _ _

def thickTr (n : ℕ) : thickFib f n ⟶ thickFib f (n + 1) :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom (thickR O n))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, thickR_comp])

theorem thickTr_ι (n : ℕ) : thickTr f n ≫ thickι f (n + 1) = thickι f n :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.SpecialConn
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

namespace GlobalTheory.SpecialConn

theorem range_spec_map_eq {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] [Nontrivial S] (φ : O →+* S)
    (hφ : ∀ Q : Ideal S, Q.IsPrime → IsLocalRing.maximalIdeal O ≤ Q.comap φ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) = {IsLocalRing.closedPoint O} := by
  have key : ∀ Q : PrimeSpectrum S, Spec.map (CommRingCat.ofHom φ) Q = IsLocalRing.closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap φ = IsLocalRing.maximalIdeal O
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap φ).ne_top) (hφ _ Q.2)
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem range_thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom (thickQ O n))) = {IsLocalRing.closedPoint O} := by
  haveI : Nontrivial (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  refine range_spec_map_eq _ fun Q hQ => ?_
  have h : IsLocalRing.maximalIdeal O ^ (n + 1) ≤ Q.comap (thickQ O n) := fun a ha => by
    change Ideal.Quotient.mk _ a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.zero_mem
  exact (Ideal.IsPrime.comap (thickQ O n)).le_of_pow_le h

theorem range_residue (O : Type) [CommRing O] [IsLocalRing O] :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = {IsLocalRing.closedPoint O} := by
  refine range_spec_map_eq _ fun Q hQ a ha => ?_
  change IsLocalRing.residue O a ∈ Q
  rw [(IsLocalRing.residue_eq_zero_iff a).2 ha]
  exact Q.zero_mem

end GlobalTheory.SpecialConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncIso

theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{0}} (Z : Closeds X) (U : X.affineOpens) (s : Γ(X, U.1)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U ↔
      ∀ x ∈ (U.1 : Set X), x ∈ (Z : Set X) → x ∉ X.basicOpen s := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · rintro h x hxU hxZ hxs
    rw [← U.2.range_fromSpec] at hxU
    obtain ⟨p, rfl⟩ := hxU
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hxs
    rw [U.2.fromSpec_preimage_basicOpen] at hp
    exact hp (h p hxZ)
  · intro h p hpZ
    by_contra hs
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [U.2.fromSpec_preimage_basicOpen]; exact hs
    have hpU : U.2.fromSpec p ∈ (U.1 : Set X) := by
      rw [← U.2.range_fromSpec]; exact ⟨p, rfl⟩
    exact h _ hpU hpZ hp

theorem rsp_ringEquiv {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    {n : ℕ} {x : Fin n → R} (h : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n x) : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp S n (fun i => e (x i)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have hr : Set.range (fun i => e (x i)) = e '' Set.range x := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Ideal.map_span, h1]
  ext y
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hz ((isUnit_map_iff e z).1 hu)
  · intro hy
    refine ⟨e.symm y, (IsLocalRing.mem_maximalIdeal _).2 fun hu => hy ?_, e.apply_symm_apply y⟩
    simpa using (isUnit_map_iff e (e.symm y)).2 hu

theorem snc_vanishingIdeal_of_isIso {A B : Scheme.{0}} (f : A ⟶ B) [IsIso f] (Z : Closeds B) (Z' : Closeds A)
    (hZ : ∀ a : A, a ∈ Z' ↔ f a ∈ Z) (h : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z)) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z') := by
  intro a
  obtain ⟨hreg, U, hU, n, g, J, hrsp, hid⟩ := h (f a)
  let e : B.presheaf.stalk (f a) ≃+* A.presheaf.stalk a := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
  have he : ∀ t, e t = f.stalkMap a t := fun _ => rfl
  let U' : A.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hU' : a ∈ U'.1 := hU
  refine ⟨IsRegularLocalRing.of_ringEquiv e, U', hU', n, fun i => f.app U.1 (g i), J, ?_, ?_⟩
  · have hg : ∀ i, A.presheaf.germ U'.1 a hU' (f.app U.1 (g i)) = e (B.presheaf.germ U.1 (f a) hU (g i)) := by
      intro i
      rw [he, Scheme.Hom.germ_stalkMap_apply]
    simp only [hg]
    exact rsp_ringEquiv e hrsp
  · let φ : Γ(B, U.1) ≃+* Γ(A, U'.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
    have hφ : ∀ t, φ t = f.app U.1 t := fun _ => rfl
    ext t
    obtain ⟨s, rfl⟩ : ∃ s, φ s = t := φ.surjective t
    have key : φ s ∈ (Scheme.IdealSheafData.vanishingIdeal Z').ideal U' ↔
        s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
      rw [mem_vanishingIdeal_ideal_iff, mem_vanishingIdeal_ideal_iff, hφ, ← Scheme.preimage_basicOpen]
      constructor
      · intro H b hbU hbZ hbs
        obtain ⟨a', rfl⟩ : ∃ a', f a' = b := ⟨(inv f) b, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
        exact H a' hbU ((hZ a').2 hbZ) hbs
      · intro H a' ha'U ha'Z ha's
        exact H (f a') ha'U ((hZ a').1 ha'Z) ha's
    rw [key, hid, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    have hp : (∏ i ∈ J, f.app U.1 (g i)) = φ (∏ i ∈ J, g i) := by
      rw [map_prod]; rfl
    rw [hp, map_dvd_iff]

end GlobalTheory.SncIso

namespace GlobalTheory.VarFlag

open GlobalTheory.Toroidal (gen genι genBd genBdIdeal mem_genBd)

theorem snc_genBdIdeal_of_snc_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.LogKS.boundary Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.Toroidal.genBdIdeal Y) := by
  intro h
  refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y) (GlobalTheory.LogKS.interior Y).compl (genBd Y) ?_ h
  intro a
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  rw [mem_genBd]
  show a ∉ Set.range Y.jQ ↔ genι Y a ∉ Set.range Y.j
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Model.j, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, hinj ?_⟩
    rw [← hx, Model.j, Scheme.Hom.comp_apply]

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundaryStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.LogKS.boundary Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.Toroidal.genBdIdeal Y) := by
  first | exact @GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary | exact GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary | (intros; apply GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivial
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem eq_const_of_isKS_zero : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → IsTanX y x' → IsKS (psiSet H) y x' 0 →
        x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  intro P G E _ _ _ H Dw l Xo c K _ _ y x' hpq hx hks
  obtain ⟨A, _, A', _, π, π', i, h, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_group_lift_kodaira_spencer_zero P E H Dw l Xo c K y x' hpq hx hks
  obtain ⟨q, hq1, hq2⟩ := GlobalTheory.T.group_lift_tangent_compatibility P G E H Dw l Xo c K y x' hpq hx A A' π π' i h h1 h2 h3 h4
  obtain ⟨o, m⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  have e := Xo.unram K x' o m
    (GlobalTheory.T.group_lift_tangent_uniqueness P G E H Dw l Xo c K y x' hpq hx A A' π π' i q h h1 h2 h3 hq1 hq2 o m)
  rw [← hx.2]
  conv_lhs => rw [e]
  rfl

end GlobalTheory.FlagTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivialStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_zero_tangent_trivial : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  first | exact @GlobalTheory.FlagTan.eq_const_of_isKS_zero | exact GlobalTheory.FlagTan.eq_const_of_isKS_zero | (intros; apply GlobalTheory.FlagTan.eq_const_of_isKS_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def SympCond {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (T : Over S)
    (t₁ : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left) (β : cycAway M →+* k) (z : kˣ),
      x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      (∀ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = 1 ↔ ∃ c, a = M • c) ∧
      (∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, g ^ M = 1 →
        ∃ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = g) ∧
      ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a)
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv c) (unitOn (z ^ (2 * omegaStd a c)))

theorem zetaAway_pow_self (M : ℕ) (hM : M ≠ 0) : zetaAway M ^ M = 1 :=
  Subtype.ext (by simpa [zetaAway, zeta] using (Complex.isPrimitiveRoot_exp M hM).pow_eq_one)

theorem zetaAway_pow_eq (M : ℕ) (hM : M ≠ 0) {k k' : ℕ} (h : (k : ZMod M) = k') :
    zetaAway M ^ k = zetaAway M ^ k' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod k' M, pow_add, pow_add, pow_mul, pow_mul, zetaAway_pow_self M hM,
    one_pow, one_pow, h]

theorem isMultOf_unique {h M : ℕ} (hh : 1 ≤ h) {a : sympSimGrp h M} {n n' : ℕ} (hn : IsMultOf a n)
    (hn' : IsMultOf a n') : (n : ZMod M) = n' := by
  let i : Fin h := ⟨0, hh⟩
  have e1 := hn (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have e2 := hn' (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have h1 : omegaMod M (Pi.single (Sum.inl i) (1 : ZMod M)) (Pi.single (Sum.inr i) 1) = 1 := by
    simp [omegaMod, Pi.single_apply]
  rw [h1, _root_.mul_one] at e1 e2
  rw [← e1, ← e2]

end GlobalTheory.HTSympCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kernel_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H)
    (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧
    ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  intro R _ _ A _ hA L hL ha
  obtain ⟨Z, i, hci, hfin, hflat, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds R A hA L hL ha
  haveI : IsClosedImmersion i.left := hci
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hmem : ∀ (T : Over (Sp R)) (z : T ⟶ Z), GlobalTheory.MemKL A L (z ≫ i) := fun T z => (hZ T _).2 ⟨z, rfl⟩
  have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ A) = η[A] := by
    show toUnit _ ≫ η[A] = η[A]
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨o, ho⟩ := (hZ _ η[A]).1 (e1 ▸ memKL_one hL _)
  have e2 : (i ⊗ₘ i) ≫ μ[A] = (fst Z Z ≫ i) * (snd Z Z ≫ i) := by
    show (i ⊗ₘ i) ≫ μ[A] = lift (fst Z Z ≫ i) (snd Z Z ≫ i) ≫ μ[A]
    rw [lift_fst_comp_snd_comp]
  obtain ⟨m, hm⟩ := (hZ _ ((i ⊗ₘ i) ≫ μ[A])).1 (e2 ▸ GlobalTheory.UU.InK.mul hL (hmem _ _) (hmem _ _))
  have e3 : i ≫ GrpObj.inv = (𝟙 Z ≫ i)⁻¹ := by
    rw [Category.id_comp]; rfl
  obtain ⟨n, hn⟩ := (hZ _ (i ≫ GrpObj.inv)).1 (e3 ▸ GlobalTheory.UU.InK.inv hL (hmem _ _))
  obtain ⟨G, hG⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  exact ⟨Z, G, i, hG, hmono, hfin, hflat, hZ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H) (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  first | exact @GlobalTheory.kernel_finiteFlat_subgroup | exact GlobalTheory.kernel_finiteFlat_subgroup | (intros; apply GlobalTheory.kernel_finiteFlat_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem IsDual.eq_of_evc {S : Scheme.{0}} {A B' T : Over S} [GrpObj A] [GrpObj B'] {P' : LB (A ⊗ B').left}
    (h : IsDual A B' P') {y₁ y₂ : T ⟶ B'}
    (e : evc h.isLB (fst A T) (snd A T ≫ y₁) = evc h.isLB (fst A T) (snd A T ≫ y₂)) : y₁ = y₂ := by
  have hM : (ev P' (fst A T) (snd A T ≫ y₁)).IsLB := pull_isLB h.isLB _
  have ha : IsAdditive (ev P' (fst A T) (snd A T ≫ y₁)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
    rw [evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)
  exact (h.univ T _ hM ha).unique ((cls_eq_iff hM hM).1 rfl)
    ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)

theorem comp_mul_eq {S : Scheme.{0}} {G Y : Over S} [MonObj G] (f : Y ⟶ G ⊗ G) :
    f ≫ μ = (f ≫ fst G G) * (f ≫ snd G G) := by
  show _ = lift _ _ ≫ μ
  rw [lift_comp_fst_snd]

theorem isMonHom_of_classifying : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → IsAdditive (swap P') → P.IsLB →
    IsAdditive (swap P) → ∀ x : B ⟶ B', LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsMonHom x := by
  intro S A B B' _ _ _ P P' h' ha' hP ha x e
  have hP' := h'.isLB
  have hE : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB hP' _
  have c : cls P hP = cls _ hE := (cls_eq_iff hP hE).2 e
  have K : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B), evc hP a b = evc hP' a (b ≫ x) := by
    intro Y a b
    have k := evc_ev hP' (fst A B) (snd A B ≫ x) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, c]
  have hs : (swap P).IsLB := pull_isLB hP _
  have hs' : (swap P').IsLB := pull_isLB hP' _
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 ha Y b b' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at k
  have addR' : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B'),
      evc hP' a (b * b') = evc hP' a b + evc hP' a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs').1 ha' Y b b' a
    rwa [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs'] at k
  have oneR : ∀ (Y : Over S) (a : Y ⟶ A), evc hP a (1 : Y ⟶ B) = 0 := fun Y a ↦ by
    rw [← evc_swap hP hs]; exact ha.evc_one hs a
  have oneR' : ∀ (Y : Over S) (a : Y ⟶ A), evc hP' a (1 : Y ⟶ B') = 0 := fun Y a ↦ by
    rw [← evc_swap hP' hs']; exact ha'.evc_one hs' a
  have u : ∀ (G : Over S) [MonObj G], snd A (𝟙_ (Over S)) ≫ (η : 𝟙_ (Over S) ⟶ G) = 1 := fun G _ ↦ by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over S))) (toUnit _)]
  refine ⟨?_, ?_⟩
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← K, u, u, oneR, oneR']
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← Category.assoc, comp_mul_eq, comp_mul_eq, ← K, addR, K, K, ← addR']
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

end GlobalTheory.AbDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefPow

theorem height_pow (HE : GlobalTheory.Published.ArExists) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) (L : HermLB p) (n : ℕ)
    {h h' : X → ℝ} (H : L.IsArithHeight h) (H' : (L.pow n).IsArithHeight h') : h' x = n * h x := by
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    PtHtComb.height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  rw [← hht H', ← hht H, ← hF, ← hF, HermLB.icls_pow, map_nsmul, nsmul_eq_mul]

theorem isNef_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  intro HC k _ X _ p D hX M n N
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨h₀, H₀⟩ := hex (HermLB.triv p)
    have H : (M.pow 0).IsArithHeight h₀ := M.isometric_pow_zero.symm.isArithHeight hX H₀
    have T := (H₀.isNef_iff hX).1 (HermLB.isNef_triv p D)
    exact (H.isNef_iff hX).2 ⟨N.semiPos.pow 0, T.2⟩
  · have : Module.Finite ℤ k := hX.finite
    refine ⟨N.semiPos.pow n, (nefFib_pow_iff k X p hX.isProjOver M n hn).2 N.vertical,
      fun Z i _ _ _ hc hd => ?_⟩
    obtain ⟨h, H⟩ := hex M
    obtain ⟨h', H'⟩ := hex (M.pow n)
    obtain ⟨r, hr⟩ := exists_isRatSec ((M.pow n).restr i).isLB
    obtain ⟨r₀, hr₀, h0⟩ := N.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H'.point Z i hc hd r hr, height_pow HE hX (HtSelfInter.isAlgPt_genericPoint i hc hd) M n H H',
      H.point Z i hc hd r₀ hr₀]
    exact mul_nonneg (Nat.cast_nonneg _) h0

end GlobalTheory.NefPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_pow_of_isNef : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  first | exact @GlobalTheory.NefPow.isNef_pow | exact GlobalTheory.NefPow.isNef_pow | (intros; apply GlobalTheory.NefPow.isNef_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.factor_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L)
    (y : Sp L ⟶ M.S) (hρ : Function.Injective ρ) (hy : y ≫ M.π = spMap ρ) :
    ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  have hI := M.integral
  have hdom := M.dominant
  have hsub : ∀ (K : Type) [Field K] (a b : Sp K), a = b := fun K _ a b =>
    PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])
  let p : Sp L := IsLocalRing.closedPoint L
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y p) (U := ⊤) trivial
  have hyV : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub L z p]; exact hxV
  obtain ⟨q, hq⟩ := M.gp.denseRange.exists_mem_open V.isOpen ⟨y p, hxV⟩
  have hgV : Set.range M.gp ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub (FractionRing R) z q]; exact hq
  haveI : Nonempty V := ⟨⟨y p, hxV⟩⟩
  haveI : IsDomain Γ(M.S, V) := IsIntegral.component_integral V
  set yV := IsOpenImmersion.lift hV.fromSpec y hyV with hyVdef
  set gV := IsOpenImmersion.lift hV.fromSpec M.gp hgV with hgVdef
  have hyf : yV ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  have hgf : gV ≫ hV.fromSpec = M.gp := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨by', hby⟩ := Spec.map_surjective yV
  obtain ⟨bg, hbg⟩ := Spec.map_surjective gV
  obtain ⟨c, hc⟩ := Spec.map_surjective (hV.fromSpec ≫ M.π)
  have hcy : by'.hom.comp c.hom = ρ := by
    have e : Spec.map (c ≫ by') = Spec.map (CommRingCat.ofHom ρ) := by
      rw [Spec.map_comp, hby, hc, ← Category.assoc, hyf, hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hcg : bg.hom.comp c.hom = algebraMap R (FractionRing R) := by
    have e : Spec.map (c ≫ bg) = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
      rw [Spec.map_comp, hbg, hc, ← Category.assoc, hgf, M.gp_π]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hdV : IsDominant gV := by
    haveI : IsDominant (gV ≫ hV.fromSpec) := by rw [hgf]; exact hdom
    exact IsDominant.of_comp_of_isOpenImmersion gV hV.fromSpec
  have hinj : Function.Injective bg.hom := by
    rw [← hbg] at hdV
    have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bg.hom).1 hdV.denseRange
    rw [nilradical_eq_zero] at h
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h)
  let ga : FractionRing R →+* L := IsFractionRing.lift hρ
  have hga : ∀ r, ga (algebraMap R _ r) = ρ r := IsFractionRing.lift_algebraMap hρ
  have key : ∀ b, by'.hom b = ga (bg.hom b) := by
    intro b
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (bg.hom b)
    have hs0 : ρ s ≠ 0 := (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero s.2)
    have hcs : bg.hom (c.hom s) = algebraMap R (FractionRing R) s := RingHom.congr_fun hcg s
    have hcr : bg.hom (c.hom r) = algebraMap R (FractionRing R) r := RingHom.congr_fun hcg r
    have h1 : c.hom s * b = c.hom r := hinj (by
      rw [map_mul, hcs, hcr, ← hrs]; exact IsLocalization.mk'_spec' (FractionRing R) r s)
    have h2 := congrArg by'.hom h1
    have hys : by'.hom (c.hom s) = ρ s := RingHom.congr_fun hcy s
    have hyr : by'.hom (c.hom r) = ρ r := RingHom.congr_fun hcy r
    rw [map_mul, hys, hyr] at h2
    rw [← hrs, IsFractionRing.lift_mk', eq_div_iff hs0, mul_comm]
    exact h2
  refine ⟨ga, hga, ?_⟩
  have e : by' = bg ≫ CommRingCat.ofHom ga := by ext b; exact key b
  rw [← hyf, ← hby, e, Spec.map_comp, Category.assoc, hbg, hgf]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_field_point_through_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L) (y : Sp L ⟶ M.S), Function.Injective ρ → y ≫ M.π = spMap ρ → ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  first | exact @GlobalTheory.Mum.Modif.factor_gp | exact GlobalTheory.Mum.Modif.factor_gp | (intros; apply GlobalTheory.Mum.Modif.factor_gp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem semiAbelian_hom_extend_generic : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E]
    (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H →
    ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  intro E _ _ _ _ G H _ _ hG hH f hf
  exact GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds E (FractionRing E) G H hG hH f

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E] (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f → ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  first | exact @GlobalTheory.Desc.semiAbelian_hom_extend_generic | exact GlobalTheory.Desc.semiAbelian_hom_extend_generic | (intros; apply GlobalTheory.Desc.semiAbelian_hom_extend_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LBDescent

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

abbrev Triple : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Triple f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    calc (pullback.fst _ _ ≫ pullback.fst f f) ≫ f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫
          pullback.snd f f ≫ f := by rw [Category.assoc, pullback.condition]
      _ = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f ≫ f := pullback.condition_assoc _
      _ = (pullback.snd _ _ ≫ pullback.snd f f) ≫ f := by rw [pullback.condition, Category.assoc])

def chart (L : LB X) (i j : L.ι) : (pullback f f).Opens :=
  pullback.fst f f ⁻¹ᵁ L.U i ⊓ pullback.snd f f ⁻¹ᵁ L.U j

def DescCompat (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (z : ↥(pullback f f)) (i i' j j' : L.ι), pullback.fst f f z ∈ L.U i → pullback.fst f f z ∈ L.U i' →
    pullback.snd f f z ∈ L.U j → pullback.snd f f z ∈ L.U j' →
    gm (𝟙 _) z _ (φ i' j') =
      gm (pullback.fst f f) z _ (L.g i i') * gm (𝟙 _) z _ (φ i j) * gm (pullback.snd f f) z _ (L.g j' j)

def DescCocycle (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (w : ↥(Triple f)) (i j k : L.ι), pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U j → pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ L.U k →
    gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ (φ i j) *
      gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ (φ j k) = gm (pr13 f) w _ (φ i k)

end GlobalTheory.LBDescent
end
end
