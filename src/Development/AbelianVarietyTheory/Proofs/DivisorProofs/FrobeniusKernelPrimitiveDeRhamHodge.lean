module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpenStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOneOfAbsoluteFrobeniusPullZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPowTransitionOfFrobeniusKillsClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPowTransitionOfFrobeniusKillsClass
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FrobKill

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}}
  {s : X ⟶ Sp R}

abbrev tU (s : X ⟶ Sp R) (U : AffOp X) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop)


include hR in
theorem cast_sec (U : X.Opens) : (p : Sec s U) = 0 := by
  rw [← map_natCast (algebraMap R (Sec s U)), hR, map_zero]

abbrev resHom (s : X ⟶ Sp R) {U V : AffOp X} (a : U ⟶ V) : tU s U ⟶ tU s V :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := tU s V) (Sec.res s (leOfHom a.unop))
    (affPt_res s (leOfHom a.unop))

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta (U : AffOp X) : tU s U ⟶ h.obj (tU s U) :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := h.obj (tU s U))
    { frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) with
      commutes' := fun r ↦ by
        show frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) (algebraMap R (Sec s U.unop.1) r) = _
        rw [frobR_apply]
        change _ = algebraMap R (Sec s U.unop.1) (frobR p R hR r)
        rw [frobR_apply, map_pow] }
    (by
      have h0 : (p : Γ(Sp (Sec s U.unop.1), ⊤)) = 0 :=
        GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_sec p hR U.unop.1)
      change spMap (frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1)) ≫ affPt s U.unop =
        affPt s U.unop ≫ GlobalTheory.VB.frob X p hX
      rw [← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX _ h0])

theorem eta_φ (U : AffOp X) (b : Sec s U.unop.1) : (eta p hR h U).φ b = b ^ p :=
  frobR_apply p _ (cast_sec p hR U.unop.1) b

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  intro p _ R _ hR X s hX h f hf
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hf
  have hg' : ∀ {T T' : Thick (dp0 R) s} (φ : T ⟶ T'), g T' - φ.φ (g T) = ev f (h.functor.map φ) :=
    fun {T T'} φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun U ↦ (show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U)),
    fun U ↦ ?_, fun U V a ↦ ?_⟩
  · let p₁ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagExt R (Sec s U.unop.1)).i
      fun _ ↦ rfl
    let p₂ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagSec R (Sec s U.unop.1))
      (fst_derSec _)
    let P := (diagExt R (Sec s U.unop.1)).thick (affPt s U.unop) (affPt_w s U.unop)
    have e : eta p hR h U ≫ h.functor.map p₁ = eta p hR h U ≫ h.functor.map p₂ :=
      Thick.hom_ext fun b ↦ by
        change (diagExt R (Sec s U.unop.1)).i ((eta p hR h U).φ b) =
          diagSec R (Sec s U.unop.1) ((eta p hR h U).φ b)
        rw [eta_φ]
        ext
        · simp
        · rw [snd_derSec, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Sec s U.unop.1),
            cast_sec p hR, zero_smul]
          simp
    have k := (ev_comp f (eta p hR h U) (h.functor.map p₁)).symm.trans
      ((congrArg (ev f) e).trans (ev_comp f (eta p hR h U) (h.functor.map p₂)))
    have k' : p₁.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) =
        p₂.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := k
    have h1 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₁.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) := hg' p₁
    have h2 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₂.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := hg' p₂
    have key : p₁.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) =
        p₂.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) := by
      rw [map_sub, map_sub]
      linear_combination -h1 + h2 - k'
    have l := congrArg (TrivSqZeroExt.snd (R := Sec s U.unop.1)) key
    change ((diagExt R (Sec s U.unop.1)).i _).snd = (diagSec R (Sec s U.unop.1) _).snd at l
    rw [snd_derSec] at l
    exact l.symm.trans (by simp)
  · have k := ev_sq f (eta p hR h U) (h.functor.map (resHom s a)) (resHom s a) (eta p hR h V)
      fun c ↦ by
        change Sec.res s (leOfHom a.unop) ((eta p hR h U).φ c) = (eta p hR h V).φ (Sec.res s (leOfHom a.unop) c)
        rw [eta_φ, eta_φ, map_pow]
    have k' : Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) =
        (ev f (resHom s a)) ^ p + (show Sec s V.unop.1 from ev f (eta p hR h V)) := by
      rw [← eta_φ p hR h V]; exact k
    have hg'' : (show Sec s V.unop.1 from g (tU s V)) - Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from g (tU s U)) =
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) :=
      hg' (resHom s a)
    change (ev f (resHom s a)) ^ p = _
    rw [map_sub]
    linear_combination -hg'' - k'

end GlobalTheory.CechDR.FrobKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPowTransitionOfFrobeniusKillsClassStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_pow_transition_of_frobenius_kills_class : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  first | exact @GlobalTheory.CechDR.FrobKill.exists_closed_pow | exact GlobalTheory.CechDR.FrobKill.exists_closed_pow | (intros; apply GlobalTheory.CechDR.FrobKill.exists_closed_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOneOfAbsoluteFrobeniusPullZero
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR.FrobKill

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow_local : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  intro p _ R _ hR X s hX h f hf
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hf
  have hg' : ∀ {T T' : Thick (dp0 R) s} (φ : T ⟶ T'), g T' - φ.φ (g T) = ev f (h.functor.map φ) :=
    fun {T T'} φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun U ↦ (show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U)),
    fun U ↦ ?_, fun U V a ↦ ?_⟩
  · let p₁ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagExt R (Sec s U.unop.1)).i
      fun _ ↦ rfl
    let p₂ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagSec R (Sec s U.unop.1))
      (fst_derSec _)
    let P := (diagExt R (Sec s U.unop.1)).thick (affPt s U.unop) (affPt_w s U.unop)
    have e : eta p hR h U ≫ h.functor.map p₁ = eta p hR h U ≫ h.functor.map p₂ :=
      Thick.hom_ext fun b ↦ by
        change (diagExt R (Sec s U.unop.1)).i ((eta p hR h U).φ b) =
          diagSec R (Sec s U.unop.1) ((eta p hR h U).φ b)
        rw [eta_φ]
        ext
        · simp
        · rw [snd_derSec, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Sec s U.unop.1),
            cast_sec p hR, zero_smul]
          simp
    have k := (ev_comp f (eta p hR h U) (h.functor.map p₁)).symm.trans
      ((congrArg (ev f) e).trans (ev_comp f (eta p hR h U) (h.functor.map p₂)))
    have k' : p₁.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) =
        p₂.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := k
    have h1 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₁.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) := hg' p₁
    have h2 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₂.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := hg' p₂
    have key : p₁.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) =
        p₂.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) := by
      rw [map_sub, map_sub]
      linear_combination -h1 + h2 - k'
    have l := congrArg (TrivSqZeroExt.snd (R := Sec s U.unop.1)) key
    change ((diagExt R (Sec s U.unop.1)).i _).snd = (diagSec R (Sec s U.unop.1) _).snd at l
    rw [snd_derSec] at l
    exact l.symm.trans (by simp)
  · have k := ev_sq f (eta p hR h U) (h.functor.map (resHom s a)) (resHom s a) (eta p hR h V)
      fun c ↦ by
        change Sec.res s (leOfHom a.unop) ((eta p hR h U).φ c) = (eta p hR h V).φ (Sec.res s (leOfHom a.unop) c)
        rw [eta_φ, eta_φ, map_pow]
    have k' : Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) =
        (ev f (resHom s a)) ^ p + (show Sec s V.unop.1 from ev f (eta p hR h V)) := by
      rw [← eta_φ p hR h V]; exact k
    have hg'' : (show Sec s V.unop.1 from g (tU s V)) - Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from g (tU s U)) =
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) :=
      hg' (resHom s a)
    change (ev f (resHom s a)) ^ p = _
    rw [map_sub]
    linear_combination -hg'' - k'


end GlobalTheory.CechDR.FrobKill

namespace GlobalTheory.ConjSeq

theorem sec_exists_pow_of_D_eq_zero_local : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩


theorem eq_sub_of_pow_eq_sub (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsReduced B]
    (hB : (p : B) = 0) {c x y : B} (h : c ^ p = x ^ p - y ^ p) : c = x - y := by
  have e : (c - (x - y)) ^ p = 0 := by
    rw [← frobR_apply p B hB, map_sub, map_sub, frobR_apply, frobR_apply, frobR_apply, h, sub_self]
  exact sub_eq_zero.1 (IsReduced.eq_zero _ ⟨p, e⟩)

theorem mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 k) s (dp0 k) s (frobR p k hk) (GlobalTheory.VB.frob X p hX)) (c : FirstDeRham s), h.pull1 c = 0 → c ∈ F1 s := by
  intro p _ k _ _ hk X _ s _ hX h c hc
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  have hex : ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1,
      (∀ U, KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧
      ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V),
        (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p =
          u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) :=
    GlobalTheory.CechDR.FrobKill.exists_closed_pow_local p k hk X s hX h f hc
  obtain ⟨u, hu, hf⟩ := hex
  choose w hw using fun U : GlobalTheory.CechDR.AffOp X ↦ sec_exists_pow_of_D_eq_zero_local p k hk X s U.unop (u U) (hu U)
  refine LinearMap.mem_ker.2 (GlobalTheory.CechDR.cmpO_injective k X s ?_)
  rw [map_zero, ← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine GlobalTheory.CatCoh.H1.mk_eq_zero.2 ⟨w, funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_⟩
  have : IsReduced (GlobalTheory.CechDR.Sec s V.unop.1) :=
    inferInstanceAs (_root_.IsReduced Γ(X, V.unop.1))
  have hp : (p : GlobalTheory.CechDR.Sec s V.unop.1) = 0 := by
    rw [← map_natCast (algebraMap k (GlobalTheory.CechDR.Sec s V.unop.1)), hk, map_zero]
  have e := hf U V a
  rw [← hw V, ← hw U, map_pow] at e
  exact (eq_sub_of_pow_eq_sub p hp e).symm

end GlobalTheory.ConjSeq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOneOfAbsoluteFrobeniusPullZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltrationOne_of_frobenius_pull_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 k) s (dp0 k) s (frobR p k hk) (GlobalTheory.VB.frob X p hX)) (c : FirstDeRham s), h.pull1 c = 0 → c ∈ F1 s := by
  first | exact @GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero | exact GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero | (intros; apply GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodge
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem frobDR_eq_zero_mem_F1prim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ c : primDR A, frobDR p k hk A c = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ k _ _ hk A _ hA c hc
  have hI : IsIntegral A.left := GlobalTheory.PrimVan.isIntegral_left hA
  have hS : Smooth (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact hA.smooth
  exact GlobalTheory.T.mem_hodgeFiltrationOne_of_frobenius_pull_eq_zero p k hk A.left (A.hom ≫ 𝟙 _) (cast_left p k hk A)
    (frobMor p k hk A (cast_left p k hk A)).isMor c.1 (congrArg Subtype.val hc)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodgeStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_kernel_primitive_de_rham_hodge : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ c : primDR A, frobDR p k hk A c = 0 → c ∈ PrimitiveSubmodule A := by
  first | exact @GlobalTheory.frobDR_eq_zero_mem_F1prim | exact GlobalTheory.frobDR_eq_zero_mem_F1prim | (intros; apply GlobalTheory.frobDR_eq_zero_mem_F1prim <;> assumption)
end
