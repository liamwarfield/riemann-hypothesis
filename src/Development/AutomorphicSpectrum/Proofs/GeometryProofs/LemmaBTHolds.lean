module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGeneric
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelOfTorsion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnit
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem torsion_etale_of_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  exact @PositivityTheory.HtPt.Mi.torsion_etale

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnitStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_etale_of_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | exact GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProper
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProper
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

theorem nTorsion_finite_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom :=
  @PositivityTheory.HtPt.Mi.torsion_finite

end GlobalTheory.CompanionTheory.Ar.BT.Tors
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProperStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_finite_of_proper : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLift
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.TorsEnd

theorem endomorphism_restricts_to_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left :=
  @PositivityTheory.HtPt.Mi.torsion_end

end GlobalTheory.CompanionTheory.Ar.BT.TorsEnd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLiftStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_endomorphism_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials
namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_sub_one {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a - 1) = valAt y ⊤ le_top a - 1 := by
  simp [valAt]

theorem omega_isDerAtOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i ht hsm L _ _ M
  obtain ⟨θ, hsurj, hker, hpin⟩ := Tan.omega_canon R T Γ S G x N i ht hsm L M
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
  have hex := fun e : L => (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have pin : ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w := by
    intro f w
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    constructor
    · intro h
      obtain ⟨s, hs⟩ := hsec f.1
      refine ⟨s, hs, fun e => ?_⟩
      obtain ⟨v, a, b⟩ := hex e
      refine ⟨v, a, b, ?_⟩
      rw [(hpin f w s hs).1 h e v a b, h0]
      simp
    · rintro ⟨s, hs, hv⟩
      refine (hpin f w s hs).2 fun e v a b => ?_
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp
  refine ⟨θ, ⟨hsurj, pin⟩, hker, ?_⟩
  rintro χ w ⟨s, hs, hv⟩
  have hχ : (fun t => ((χ t : Rˣ) : R)) ∈ Γ.btOrder ⊤ :=
    char_mem_hopfOrder R T _ (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) χ
  rw [OrderApi.dlogChar_of_mem _ χ hχ]
  refine (pin _ w).2 ⟨s - 1, fun t => ?_, fun e => ?_⟩
  · rw [valAt_sub_one, hs t]
    simp
  · obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [valAt_sub_one, c]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentialsStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_to_invariant_differentials : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | exact GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtale
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtale
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.EtaleTop

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem stalk_spec_normal [IsIntegrallyClosed R] (y : Spec (CommRingCat.of R)) :
    IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) y
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

theorem genPt_asIdeal (Γ : QFGroup R T) (t : T) (x : Spec (CommRingCat.of (FractionRing R))) :
    (Γ.G.hom ((Γ.pt t).left x)).asIdeal = ⊥ := by
  have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
  have : Γ.G.hom ((Γ.pt t).left x) = (genPt R).hom x := by
    rw [← hw]; rfl
  rw [this]
  show Ideal.comap (algebraMap R (FractionRing R)) x.asIdeal = ⊥
  have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime
  rw [hx, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

theorem eq_of_specializes_bot {y z : Spec (CommRingCat.of R)} (h : y ⤳ z) (hz : z.asIdeal = ⊥) :
    y = z := by
  have h' : @LE.le (PrimeSpectrum R) _ y z := (PrimeSpectrum.le_iff_specializes (R := R) y z).2 h
  have h'' : y.asIdeal ≤ z.asIdeal := h'
  refine PrimeSpectrum.ext (le_antisymm h'' ?_)
  rw [hz]; exact bot_le

theorem eq_of_specializes_lqf {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] {a b : X}
    (h : a ⤳ b) (e : f a = f b) : a = b := by
  have hd := (f.isDiscrete_preimage_singleton (f b)).to_subtype
  have : (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val this.eq

theorem eq_of_specializes_pt [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (x : Spec (CommRingCat.of (FractionRing R))) (g : Γ.G.left) (s t : T)
    (hs : (Γ.pt s).left x ⤳ g) (ht : (Γ.pt t).left x ⤳ g) : s = t := by
  have := Γ.quasiFinite
  obtain ⟨h1, h2⟩ := stalk_spec_normal (R := R) (Γ.G.hom g)
  have hdom : IsDomain (Γ.G.left.presheaf.stalk g) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth Γ.G.hom g).1
  let e₀ : Spec (Γ.G.left.presheaf.stalk g) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have key : ∀ u : T, (Γ.pt u).left x ⤳ g → Γ.G.left.fromSpecStalk g e₀ = (Γ.pt u).left x := by
    intro u hu
    have hr : (Γ.pt u).left x ∈ Set.range (Γ.G.left.fromSpecStalk g) := by
      rw [Scheme.range_fromSpecStalk]; exact hu
    obtain ⟨a, ha⟩ := hr
    have he₀a : e₀ ⤳ a := (PrimeSpectrum.le_iff_specializes (R := Γ.G.left.presheaf.stalk g) e₀ a).1
      (show (⊥ : Ideal _) ≤ _ from bot_le)
    have h3 : Γ.G.left.fromSpecStalk g e₀ ⤳ (Γ.pt u).left x := ha ▸ he₀a.map (Γ.G.left.fromSpecStalk g).continuous
    refine eq_of_specializes_lqf Γ.G.hom h3 ?_
    exact eq_of_specializes_bot (h3.map Γ.G.hom.continuous) (genPt_asIdeal Γ u x)
  exact Γ.pt_inj s t x x ((key s hs).symm.trans (key t ht))

theorem genPt_appLE (f : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R))
    (hf : f = (genPt R).hom) (e) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
  subst hf
  have : (genPt R).hom.appLE ⊤ ⊤ e = (genPt R).hom.appTop := rfl
  rw [this]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop ≫ _ = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem regularAt_const [Finite T] [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (φ : T → R) (g : Γ.G.left) :
    Γ.RegularAt (fun h => algebraMap R (FractionRing R) (φ h)) g := by
  classical
  let x₀ : Spec (CommRingCat.of (FractionRing R)) :=
    (IsLocalRing.closedPoint (FractionRing R) : PrimeSpectrum _)
  let P : T → Γ.G.left := fun t => (Γ.pt t).left x₀
  let Z : Set Γ.G.left := ⋃ t ∈ {t | ¬ P t ⤳ g}, closure {P t}
  have hZ : IsClosed Z := (Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure
  let U : Γ.G.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hgU : g ∈ U := by
    show g ∉ Z
    simp only [Z, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro t ht hg
    exact ht (specializes_iff_mem_closure.2 hg)
  have hPU : ∀ t, P t ∈ U → P t ⤳ g := by
    intro t ht
    by_contra hn
    exact ht (Set.mem_biUnion (x := t) hn (subset_closure rfl))
  refine ⟨U, hgU, ?_⟩
  by_cases hex : ∃ t₀, P t₀ ⤳ g
  · obtain ⟨t₀, ht₀⟩ := hex
    refine ⟨(Γ.G.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ t₀)), ?_⟩
    intro t h
    have htU : P t ∈ U := h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
    have := eq_of_specializes_pt Γ hE x₀ g t t₀ (hPU t htU) ht₀
    subst this
    have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
    have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Γ.G.hom.appLE ⊤ U le_top ≫
        (Γ.pt t).left.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
          CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
      erw [Scheme.Hom.appLE_comp_appLE_assoc]
      exact genPt_appLE _ hw _
    exact congrArg (fun m => m.hom (φ t)) key
  · refine ⟨0, fun t h => ?_⟩
    exact absurd ⟨t, hPU t (h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial))⟩ hex

theorem btOrder_top_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  intro R _ _ _ T _ _ Γ hE
  refine eq_top_iff.2 fun f _ => Algebra.subset_adjoin ?_
  intro t g _
  exact regularAt_const Γ hE (fun h => f (t * h)) g

end GlobalTheory.CompanionTheory.Ar.BT.EtaleTop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtaleStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale | exact GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHolds
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ, ?_,
    fun hN => GlobalTheory.T.btOrder_eq_top_of_etale R T Γ
      (GlobalTheory.T.torsion_group_etale_of_unit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => GlobalTheory.T.exists_dual_to_invariant_differentials R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
    obtain ⟨hoi, htr⟩ := GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact GlobalTheory.T.btOrder_embedding_iso_finite R T Γ j hj
      (GlobalTheory.T.torsion_group_finite_of_proper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := GlobalTheory.T.torsion_group_endomorphism_lift R T Γ S G x N i hi a
    refine GlobalTheory.T.btOrder_comap_hom R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      GlobalTheory.T.btOrder_base_change_generic R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := GlobalTheory.T.hopf_order_scalar_extension R T R' _
      (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LemmaBT_holds : GlobalTheory.CompanionTheory.Ar.BT.LemmaBT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | exact GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds <;> assumption)
end
