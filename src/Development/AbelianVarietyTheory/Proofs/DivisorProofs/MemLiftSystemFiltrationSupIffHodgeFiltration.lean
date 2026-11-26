module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

namespace Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀}

def viaDR (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) :
    CoefMap (((RingHom.id R₀).comp (RingHom.id R₀)).comp π) (O (divided₂ hI) (s₀ ≫ spMap π)) (OAff s₀) :=
  ((redMor hI hk s₀).coef.comp (CoefMap.restrict (O (dp0 R₀) s₀) (IsTriv s₀).ι)).comp
    (ptCoef (F := OAff s₀) (fun U ↦ affPt s₀ U.unop) (fun U ↦ affPt_w s₀ U.unop)
      fun _ _ a ↦ affPt_res s₀ (leOfHom a.unop))

variable (S : Sys I π s₀) (hI : I ^ 2 = 0) (hk : RingHom.ker π = I)

def redTrans : ((S.coef hI).comp S.redO).G ⟶ (viaDR hI hk s₀).G where
  app U :=
    { φ := { (S.p U : S.F.obj U →+* Sec s₀ U.unop.1) with
        commutes' := fun r ↦ (S.semi U).map_algebraMap r }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := by
        refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_, fun n hn a ha ↦ ?_⟩
        · exact Ideal.mem_comap.2 (Ideal.mem_bot.2 ((S.ker U a).2 ha))
        · change (dp0 _).dpow n (S.p U a) = S.p U _
          rw [(S.ker U a).2 ha, dpow_eval_zero _ hn]
          exact ((S.ker U _).2 ((divided₂ (map_sq hI _)).dpow_mem hn ha)).symm
      pt := by
        change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop ≫ 𝟙 X₀
        rw [Cris.spMap_id, Category.id_comp, Category.comp_id] }
  naturality U V a := Thick.hom_ext fun b ↦ S.nat a b

theorem redO_r (c : Cr hI π s₀) :
    S.redO.pull1 (S.r hI c) = cmpO s₀ (toH1O s₀ (rho hI hk s₀ c)) := by
  refine (CoefMap.pullCohomologyOne_comp _ _ c).symm.trans
    ((CoefMap.pullCohomologyOne_eq_of_natTrans _ (viaDR hI hk s₀) (S.redTrans hI hk) (fun _ _ ↦ rfl) c).trans ?_)
  rw [viaDR, CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp]
  rfl

end Sys

end GlobalTheory.LiftSys

namespace GlobalTheory.LiftSys

theorem Sys.mem_K_sup_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀,
      c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  intro R R₀ _ _ I hI π _ hk X₀ s₀ S hBC hF c
  have key : ∀ c, rho hI hk s₀ c ∈ F1 s₀ ↔ S.redO.pull1 (S.r hI c) = 0 := fun c ↦ by
    rw [Sys.redO_r S hI hk c]
    change toH1O s₀ (rho hI hk s₀ c) = 0 ↔ _
    exact ⟨fun h ↦ by rw [h, map_zero],
      fun h ↦ GlobalTheory.CechDR.cmpO_injective R₀ X₀ s₀ (h.trans (map_zero _).symm)⟩
  rw [key]
  constructor
  · intro h
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 h
    have h0 : S.r hI k = 0 := hk'
    rw [map_add (f := _), h0, zero_add]
    refine (key i).1 ?_
    rw [(hBC.2 i).2 hi]
    exact Submodule.zero_mem _
  · intro h
    obtain ⟨z, hz⟩ := H1.mk_surjective _ (S.r hI c)
    rw [← hz, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h
    obtain ⟨g₀, hg₀⟩ := h
    choose g hg using fun U ↦ S.surj U (g₀ U)
    let z' : Z1 S.F := z - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
    have hz' : S.IsIdealValuedLiftSystemCocycle z' := by
      intro U V a
      rw [← S.ker]
      have e := congrFun (congrFun (congrFun hg₀ U) V) a
      rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
      change g₀ V - mp (OAff s₀) a (g₀ U) = S.p V (z.1 U V a) at e
      change S.p V (z.1 U V a - (g V - mp S.F a (g U))) = 0
      rw [map_sub, map_sub, S.nat, hg, hg, ← e, sub_self]
    obtain ⟨c', hc', hrc'⟩ := hF z' hz'
    have hr : S.r hI (c - c') = 0 := by
      rw [map_sub, hrc', ← hz, map_sub, sub_sub_cancel]
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    exact Submodule.mem_sup.2 ⟨c - c', hr, c', hc', sub_add_cancel c c'⟩

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltrationStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀, c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  first | exact @GlobalTheory.LiftSys.Sys.mem_K_sup_iff | exact GlobalTheory.LiftSys.Sys.mem_K_sup_iff | (intros; apply GlobalTheory.LiftSys.Sys.mem_K_sup_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch.Aff

theorem pinched_of_iso (g : ℕ) {S S' Z B' C Y B₂ C₂ Y₂ : Scheme.{0}} {s' : S' ⟶ S} {z : Z ⟶ S}
    {b' : B' ⟶ S'} {e : C ⟶ Z} {i : Y ⟶ B'} {q : Y ⟶ C}
    {b₂ : B₂ ⟶ S'} {e₂ : C₂ ⟶ Z} {i₂ : Y₂ ⟶ B₂} {q₂ : Y₂ ⟶ C₂}
    (eB : B' ≅ B₂) (eC : C ≅ C₂) (eY : Y ≅ Y₂)
    (hb : b' = eB.hom ≫ b₂) (he : e = eC.hom ≫ e₂) (hi : i ≫ eB.hom = eY.hom ≫ i₂)
    (hq : q ≫ eC.hom = eY.hom ≫ q₂) (x : B') (h : Pinched g s' z b₂ e₂ i₂ q₂ (eB.hom x)) :
    Pinched g s' z b' e i q x := by
  obtain ⟨U, U', V, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := h
  refine ⟨U, U', V, u, p, j ≫ eB.inv, n, k ≫ eC.inv, hu, ?_, inferInstance, ?_, ?_, ?_⟩
  · simpa [hb] using hp
  · obtain ⟨t, ht⟩ := hx
    refine ⟨t, ?_⟩
    simp [ht]
  · simpa [he] using hn
  · intro T a a' h
    obtain ⟨y, hy1, hy2⟩ := hl T a a' h
    refine ⟨y ≫ eY.inv, ?_, ?_⟩
    · have : eY.inv ≫ i = i₂ ≫ eB.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hi]; simp
      rw [Category.assoc, this, ← Category.assoc, hy1, Category.assoc]
    · have : eY.inv ≫ q = q₂ ≫ eC.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hq]; simp
      rw [Category.assoc, this, ← Category.assoc, hy2, Category.assoc]

theorem isPushout_of_isPullback_Spec {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (H : IsPullback (Spec.map h) (Spec.map k) (Spec.map f) (Spec.map g)) :
    IsPushout f g h k := by
  have w : k.op ≫ g.op = h.op ≫ f.op := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact H.w.symm
  exact (IsPullback.of_map Scheme.Spec w H.flip).unop

end GlobalTheory.Pinch.Aff

namespace GlobalTheory.Pinch.Aff

theorem pinched_affine_of_spec : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  intro H R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hB hC hsm hss h1 h2 y
  haveI : IsAffine Y := IsAffine.of_isPullback h1
  haveI := hsm
  set φc : CommRingCat.of R' ⟶ Γ(B', ⊤) := Spec.preimage (B'.isoSpec.inv ≫ b') with hφc
  set δc : CommRingCat.of (R ⧸ c) ⟶ Γ(C, ⊤) := Spec.preimage (C.isoSpec.inv ≫ e) with hδc
  set πc : Γ(B', ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom) with hπc
  set ψc : Γ(C, ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom) with hψc
  have eφ : spMap φc.hom = B'.isoSpec.inv ≫ b' := by simp [spMap, φc]
  have eδ : spMap δc.hom = C.isoSpec.inv ≫ e := by simp [spMap, δc]
  have eπ : spMap πc.hom = Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom := by simp [spMap, πc]
  have eψ : spMap ψc.hom = Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom := by simp [spMap, ψc]
  have hφs : φc.hom.Smooth := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hφc, Spec.map_preimage]
    infer_instance
  have hδ : δc = (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).inv ≫ e.appTop := by
    apply Spec.map_injective
    rw [hδc, Spec.map_preimage, Spec.map_comp, Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hδs : δc.hom.IsStandardSmoothOfRelativeDimension g := by
    rw [hδ, CommRingCat.hom_comp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).mpr hss
  have hp1 : IsPushout (CommRingCat.ofHom (φc.hom.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c))
      (CommRingCat.ofHom πc.hom) (CommRingCat.ofHom (ψc.hom.comp δc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap πc.hom) (spMap ψc.hom ≫ spMap δc.hom) (spMap φc.hom ≫ spMap (algebraMap R R'))
      (spMap (Ideal.Quotient.mk c))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h1 Y.isoSpec B'.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hp2 : IsPushout (CommRingCat.ofHom (δc.hom.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom ψc.hom) (CommRingCat.ofHom (πc.hom.comp φc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap ψc.hom) (spMap πc.hom ≫ spMap φc.hom) (spMap δc.hom ≫ spMap (Ideal.Quotient.mk c))
      (spMap (algebraMap R R'))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h2 Y.isoSpec C.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hP := H R R' hinj c hc g Γ(B', ⊤) Γ(C, ⊤) Γ(Y, ⊤) φc.hom δc.hom πc.hom ψc.hom hφs hδs hp1 hp2
    (Y.isoSpec.hom y)
  have hpt : spMap πc.hom (Y.isoSpec.hom y) = B'.isoSpec.hom (i y) := by
    rw [eπ]; simp
  rw [hpt] at hP
  refine pinched_of_iso g B'.isoSpec C.isoSpec Y.isoSpec ?_ ?_ ?_ ?_ (i y) hP
  · rw [eφ]; simp
  · rw [eδ]; simp
  · rw [eπ]; simp
  · rw [eψ]; simp

end GlobalTheory.Pinch.Aff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectraStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_charts_affine_of_spectra : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  first | exact @GlobalTheory.Pinch.Aff.pinched_affine_of_spec | exact GlobalTheory.Pinch.Aff.pinched_affine_of_spec | (intros; apply GlobalTheory.Pinch.Aff.pinched_affine_of_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdeal
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroSummand

variable {R : Type} [CommRing R] (I : Ideal R) {C : Type 1} [AddCommGroup C] [Module R C]

theorem smul_top_eq_sup {P Q : Submodule R C} (h : IsCompl P Q) :
    I • (⊤ : Submodule R C) = I • P ⊔ I • Q := by
  rw [← h.sup_eq_top, Submodule.smul_sup]

theorem sup_smul_top_eq {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊔ I • (⊤ : Submodule R C) = P ⊔ I • Q := by
  rw [smul_top_eq_sup I h, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • P ≤ P)]

theorem inf_smul_top {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊓ I • (⊤ : Submodule R C) = I • P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxJ⟩ := Submodule.mem_inf.mp hx
    rw [smul_top_eq_sup I h, Submodule.mem_sup] at hxJ
    obtain ⟨a, ha, b, hb, rfl⟩ := hxJ
    have hbQ : b ∈ Q := Submodule.smul_le_right hb
    have hbP : b ∈ P := by
      have e : b = (a + b) - a := by abel
      rw [e]; exact P.sub_mem hxP (Submodule.smul_le_right ha)
    have hb0 : b = 0 := (Submodule.disjoint_def.mp h.disjoint) b hbP hbQ
    simpa [hb0] using ha
  · exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)

theorem smul_smul_top (hI : I ^ 2 = 0) : I • I • (⊤ : Submodule R C) = ⊥ := by
  rw [← Submodule.mul_smul, ← sq, hI, Submodule.zero_eq_bot, Submodule.bot_smul]

theorem smul_le_of_sup_eq (hI : I ^ 2 = 0) {K F : Submodule R C}
    (h : K ⊔ I • ⊤ = F ⊔ I • ⊤) : I • K ≤ I • F := by
  calc I • K ≤ I • (K ⊔ I • ⊤) := Submodule.smul_mono le_rfl le_sup_left
    _ = I • F := by rw [h, Submodule.smul_sup, smul_smul_top I hI, sup_bot_eq]

end GlobalTheory.SqZeroSummand


open GlobalTheory.SqZeroSummand in
theorem GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero :
    ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  intro R _ I hI C _ _ F K N hFN hKF
  have isCompl_of : K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N := by
    intro hi
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxN
      have hx : x ∈ F ⊔ I • N := by
        rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hxK
      obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hbN : b ∈ N := Submodule.smul_le_right hb
      have hyN : y ∈ N := by
        have e : y = (y + b) - b := by abel
        rw [e]; exact N.sub_mem hxN hbN
      have hy0 : y = 0 := (Submodule.disjoint_def.mp hFN.disjoint) y hy hyN
      subst hy0
      rw [zero_add] at hxK hxN ⊢
      have hbJ : b ∈ K ⊓ I • (⊤ : Submodule R C) :=
        ⟨hxK, Submodule.smul_mono le_rfl le_top hb⟩
      rw [hi] at hbJ
      exact (Submodule.disjoint_def.mp hFN.disjoint) b hbJ.1 hbN
    · rw [codisjoint_iff, eq_top_iff, ← hFN.sup_eq_top]
      have h1 : I • F ≤ K := by
        have : I • F ≤ K ⊓ I • ⊤ := by
          rw [hi]; exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)
        exact this.trans inf_le_left
      have h2 : F ≤ K ⊔ N := by
        calc F ≤ F ⊔ I • ⊤ := le_sup_left
          _ = K ⊔ I • ⊤ := hKF.symm
          _ = K ⊔ (I • F ⊔ I • N) := by rw [smul_top_eq_sup I hFN]
          _ ≤ K ⊔ N := sup_le le_sup_left
              (sup_le (h1.trans le_sup_left) (Submodule.smul_le_right.trans le_sup_right))
      exact sup_le h2 le_sup_right
  refine ⟨isCompl_of, ?_⟩
  rintro ⟨N', hKN'⟩
  have hi : K ⊓ I • ⊤ = F ⊓ I • ⊤ := by
    rw [inf_smul_top I hKN', inf_smul_top I hFN]
    exact le_antisymm (smul_le_of_sup_eq I hI hKF) (smul_le_of_sup_eq I hI hKF.symm)
  have hKN := isCompl_of hi
  refine ⟨hi, (N.projection K hKN.symm) ∘ₗ F.subtype, ?_, ?_, ?_⟩
  · intro c
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    refine ⟨?_, Submodule.projection_apply_mem _ _, Submodule.sub_projection_mem _ _⟩
    have hc : c.1 ∈ K ⊔ I • N := by
      rw [← sup_smul_top_eq I hKN, hKF]; exact Submodule.mem_sup_left c.2
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp hc
    rw [← hkb, map_add (f := _), (Submodule.projection_apply_eq_zero_iff _).mpr hk, zero_add,
      Submodule.projection_apply_of_mem_left _ (Submodule.smul_le_right hb)]
    exact Submodule.smul_mono le_rfl le_top hb
  · intro c hc
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have h' : c.1 ∈ K ⊓ I • (⊤ : Submodule R C) := by rw [hi]; exact ⟨c.2, hc⟩
    exact (Submodule.projection_apply_eq_zero_iff _).mpr h'.1
  · intro k hk
    have hk' : k ∈ F ⊔ I • N := by
      rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hk
    obtain ⟨f, hf, b, hb, hfb⟩ := Submodule.mem_sup.mp hk'
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have hbN : b ∈ N := Submodule.smul_le_right hb
    have ef : f = k - b := by rw [← hfb]; abel
    rw [ef, map_sub, (Submodule.projection_apply_eq_zero_iff _).mpr hk,
      Submodule.projection_apply_of_mem_left _ hbN]
    abel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdealStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  first | exact @GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | exact GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | (intros; apply GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegForm
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.ConjSchr

variable {D : D7}

theorem symplO_negS (S T : HSp D) (x y : WO S T) :
    symplO (GlobalTheory.ChiGrid.negSp S) T x y = -symplO S T x y := by
  simp only [symplO, hO, GlobalTheory.ChiGrid.negSp_gram, GlobalTheory.CjNeg.inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

def cjF {X : Type} (g : X → ℂ) : X → ℂ := fun w => starRingEnd ℂ (g w)

theorem heisO_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ S T x (cjF g) = cjF (heisO ψ (GlobalTheory.ChiGrid.negSp S) T x g) := by
  funext w
  simp only [cjF, heisO, map_mul, GlobalTheory.CjNeg.conj_psi hψ, GlobalTheory.CjNeg.symplOH_negS, neg_neg]

theorem cjF_cjF {X : Type} (g : X → ℂ) : cjF (cjF g) = g := by
  funext w; simp [cjF]

def conjLin {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g := cjF (T (cjF g))
  map_add' g h := by
    have : cjF (g + h) = cjF g + cjF h := by funext w; simp [cjF]
    funext w; simp [this, cjF]
  map_smul' c g := by
    have : cjF (c • g) = starRingEnd ℂ c • cjF g := by funext w; simp [cjF]
    funext w; simp [this, cjF]

theorem conjLin_apply {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (g : X → ℂ) :
    conjLin T g = cjF (T (cjF g)) := rfl

theorem isSBHalf_cjF {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (cjF Φ) := by
  obtain ⟨hs, k, hk, hinv, hsupp⟩ := h
  refine ⟨fun t ht => hs t ?_, k, hk, fun u hu hue t => ?_, fun t ht => hsupp t ?_⟩
  · intro h0; apply ht; simp [cjF, h0]
  · simp only [cjF, hinv u hu hue t]
  · intro h0; apply ht; simp [cjF, h0]

theorem isPlaceModel_conjLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {e : AE D}
    {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO (GlobalTheory.ChiGrid.negSp S) T) (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) e Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (cjF f₀) (conjLin T₀) := by
  constructor
  · intro Φ hΦ x hx
    have e1 := h.trans _ (isSBHalf_cjF hΦ) x hx
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => Φ (t + x)) = fun t => cjF Φ (t + x) := rfl
    rw [e2, e1]
  · intro Φ hΦ y hy
    have e1 := h.modul _ (isSBHalf_cjF hΦ) y hy
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO (GlobalTheory.ChiGrid.negSp S) T t y) * cjF Φ t := by
      funext t; simp only [cjF, map_mul, GlobalTheory.CjNeg.conj_psi hψ, symplO_negS]
    rw [e2, e1]
  · have e2 : cjF ((1 : ℂ) • halfInd e Λ) = (1 : ℂ) • halfInd e Λ := by
      funext t; simp only [cjF, one_smul, halfInd]; split_ifs <;> simp
    rw [conjLin_apply, e2, h.vac]

end GlobalTheory.ConjSchr

open GlobalTheory.ConjSchr in
theorem GlobalTheory.ConjSchr.conj_schroedinger_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  intro D ψ hψ A WW e ΛA ΛW vac Φ f hT
  have hL : latO (GlobalTheory.Grid.neg A) WW ΛA ΛW (fun _ => True) = latO A WW ΛA ΛW (fun _ => True) :=
    GlobalTheory.CoreRowLat.latO_negSp A WW ΛA ΛW _
  obtain ⟨⟨T₀, h0⟩, hall⟩ := hT
  have hf : f = T₀ Φ := hall T₀ h0
  rw [hL] at h0
  refine ⟨conjLin T₀, isPlaceModel_conjLin hψ h0, ?_⟩
  show cjF f = conjLin T₀ (cjF Φ)
  rw [conjLin_apply, cjF_cjF, hf]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegFormStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerModel_complexConjugate_negForm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  first | exact @GlobalTheory.ConjSchr.conj_schroedinger_neg | exact GlobalTheory.ConjSchr.conj_schroedinger_neg | (intros; apply GlobalTheory.ConjSchr.conj_schroedinger_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isLocalization_away_of_absorb {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) {f : R} (hf : f ∈ c) :
    IsLocalization.Away f (Localization.Away (algebraMap R R' f)) := by
  have hmap : ∀ a : R, algebraMap R (Localization.Away (algebraMap R R' f)) a =
      algebraMap R' (Localization.Away (algebraMap R R' f)) (algebraMap R R' a) := fun a =>
    IsScalarTower.algebraMap_apply R R' _ a
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [hmap, map_pow, map_pow]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (algebraMap R R' f))
  · intro z
    obtain ⟨⟨r', ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z
    obtain ⟨y, -, hy⟩ := hc f hf r'
    refine ⟨⟨y, ⟨f ^ (n + 1), n + 1, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hmap, hmap, hy, map_pow, map_pow, pow_succ, map_mul, ← hz, map_pow]
    ring
  · intro a b h
    rw [hmap, hmap] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R R' f)) h
    refine ⟨⟨f ^ k, k, rfl⟩, hinj ?_⟩
    simp only [map_mul, map_pow] at hk ⊢
    exact hk

theorem pinched_off : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ R' _ _ hinj c hc g B' C Y b' e i q hsm x hx
  obtain ⟨f, hfc, hfx⟩ : ∃ f ∈ c, f ∉ ((b' ≫ spMap (algebraMap R R')) x).asIdeal := by
    by_contra hno
    push_neg at hno
    apply hx
    have hr : Set.range (spMap (Ideal.Quotient.mk c)) =
        PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk c)) :=
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    rw [hr, Ideal.mk_ker]
    exact hno
  haveI : IsLocalization.Away f (Localization.Away (algebraMap R R' f)) :=
    isLocalization_away_of_absorb hinj c hc hfc
  let l' : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R' := spMap (algebraMap R' _)
  let h : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R := spMap (algebraMap R _)
  haveI : IsOpenImmersion l' := IsOpenImmersion.of_isLocalization (algebraMap R R' f)
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isLocalization f
  have hcomp : l' ≫ spMap (algebraMap R R') = h := by
    simp only [l', h, spMap, ← Spec.map_comp]
    congr 1
  have hrange : Set.range h = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range _ f
  have hrange' : Set.range l' =
      (PrimeSpectrum.basicOpen (algebraMap R R' f) : Set (PrimeSpectrum R')) :=
    PrimeSpectrum.localization_away_comap_range _ _
  let j : pullback b' l' ⟶ B' := pullback.fst b' l'
  let u : pullback b' l' ⟶ Sp R := pullback.snd b' l' ≫ h
  have hju : j ≫ b' ≫ spMap (algebraMap R R') = u := by
    simp only [j, u, ← hcomp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hsmu : SmoothOfRelativeDimension g u := by
    haveI : SmoothOfRelativeDimension g (pullback.snd b' l') :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback b' l') hsm
    haveI : SmoothOfRelativeDimension 0 h := inferInstance
    have := smoothOfRelativeDimension_comp g 0 (pullback.snd b' l') h
    simpa using this
  have hD : ∀ t : ↥(pullback b' l'), f ∉ (u t).asIdeal := fun t => by
    have : u t ∈ Set.range h := ⟨pullback.snd b' l' t, rfl⟩
    rw [hrange] at this
    exact this
  have hEmpty : ∀ (T : Scheme.{0}) (a : T ⟶ pullback b' l') (a' : T ⟶ Sp (R ⧸ c)),
      a ≫ u = a' ≫ spMap (Ideal.Quotient.mk c) → IsEmpty T := by
    intro T a a' w
    refine ⟨fun t => hD (a t) ?_⟩
    have e1 : u (a t) = spMap (Ideal.Quotient.mk c) (a' t) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    rw [e1]
    show Ideal.Quotient.mk c f ∈ (a' t).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hfc]
    exact Ideal.zero_mem _
  have w1 : 𝟙 (pullback b' l') ≫ u = (j ≫ b') ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, Category.assoc, hju]
  have w2 : Scheme.emptyTo (pullback b' l') ≫ u = (Scheme.emptyTo C ≫ e) ≫ spMap (Ideal.Quotient.mk c) :=
    Scheme.empty_ext _ _
  refine ⟨pullback b' l', pullback b' l', ∅, u, 𝟙 _, j, Scheme.emptyTo _, Scheme.emptyTo C, hsmu,
    ⟨⟨w1⟩, ⟨PullbackCone.IsLimit.mk w1 (fun s => s.fst) (fun s => Category.comp_id _) (fun s => ?_)
      (fun s m h1 _ => by simpa using h1)⟩⟩, inferInstance, ?_,
    ⟨⟨w2⟩, ⟨PullbackCone.IsLimit.mk w2
      (fun s => haveI := hEmpty _ _ _ s.condition; isInitialOfIsEmpty.to _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s m _ _ => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)⟩⟩, ?_⟩
  · have hr : Set.range s.snd ⊆ Set.range l' := by
      rintro _ ⟨t, rfl⟩
      rw [hrange']
      have e1 : spMap (algebraMap R R') (s.snd t) = u (s.fst t) := by
        rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
      have := hD (s.fst t)
      rw [← e1] at this
      exact this
    have hl : IsOpenImmersion.lift l' s.snd hr ≫ l' = s.snd := IsOpenImmersion.lift_fac l' s.snd hr
    have hl2 : IsOpenImmersion.lift l' s.snd hr = s.fst ≫ pullback.snd b' l' := by
      rw [← cancel_mono h, ← hcomp, ← Category.assoc, hl, ← s.condition]
      show s.fst ≫ (pullback.snd b' l' ≫ h) = _
      rw [← hcomp]
      simp only [Category.assoc]
    show s.fst ≫ j ≫ b' = s.snd
    rw [← hl, hl2]
    exact congrArg (s.fst ≫ ·) pullback.condition
  · rw [IsOpenImmersion.range_pullbackFst l' b']
    show b' x ∈ Set.range l'
    rw [hrange']
    exact hfx
  · intro T a a' _
    haveI : IsEmpty T := ⟨fun t => isEmptyElim (a' t)⟩
    exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_chart_off_closed_part_from_base : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  first | exact @GlobalTheory.Pinch.pinched_off | exact GlobalTheory.Pinch.pinched_off | (intros; apply GlobalTheory.Pinch.pinched_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectio
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

section Transport

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {P B : LB Y}

def isoSec (w : LB.Iso P B) (hw : w.IsGen) : (LB.div B P).Sec := ⟨fun i => (w.s i : _), fun i j => by
  have := congrArg Units.val (hw i j)
  rw [Units.val_mul] at this
  exact this⟩

theorem val_congr_pt {O : Y.Opens} {R : Type} [CommRing R] {x x' : Sp R ⟶ Y} (h : x = x') (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst h; rfl

theorem val_restr_eq {O O' : Y.Opens} (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ Y) (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

end Transport


set_option maxHeartbeats 1000000 in
theorem exists_rule_of_cls_pull : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  intro D T j Y e o hG hE Z TF la L hL hc
  have hP : (L.pull (π₀ TF.X Z)).IsLB := LB.isLB_pull hL _
  have hB := isLB_L₀ TF.X Z la
  obtain ⟨w, hw⟩ := (cls_eq_iff hP hB).1 ((cls_pull hL _ hP).trans hc)
  let C := divChart hB hP
  let G : H0 (str₀ TF.X Z) (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))) ⊤ := H0.ofSec _ ⊤ (isoSec w hw)
  let sOf : H0 (s₀ TF.Y Z) L ⊤ → H0 (str₀ TF.X Z) (L₀ TF.X Z la) ⊤ := fun t =>
    C.mul (H0.pull (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) G
  choose f hf hf' using fun t => exists_suppOn_sec₀_eq _ _ _ _ _ _ _ _ _ (AllWt.exOf _ la 0) (H0.restr le_top (sOf t))
  refine ⟨fun t => (f t).1, fun t ht => ?_, fun yy v hv k hk => ?_⟩
  · have hs : sOf t ∈ vanBd TF.X Z la := (mem_vanBd _ _).2 fun y hy hn => by
      obtain ⟨τ, ha, hb, hcc⟩ := C.cover y
      have u1 : IsUnit (H0.germ (C.c τ) y (memTop y) hcc (sOf t)) := by
        rw [← ger_toSec]; exact (isUnit_ger_iff _ hcc).2 hn
      have e3 := C.germ_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G τ y (memTop y) ha hb hcc
      have u1' : IsUnit (H0.germ (C.a τ) y (memTop y) ha
          (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) *
          H0.germ (C.b τ) y (memTop y) hb G) := (congrArg IsUnit e3).mp u1
      have u2 := (congrArg IsUnit (H0.germ_pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top (C.a τ) y (memTop y) ha t)).mp
        (isUnit_of_mul_isUnit_left u1')
      have u3 := (isUnit_map_iff (Scheme.Hom.stalkMap (π₀ TF.X Z) y).hom _).1 u2
      rw [← ger_toSec] at u3
      obtain ⟨v', hv'⟩ := ht ((isUnit_ger_iff _ _).1 u3)
      refine hy (show TF.X.π (inc₀ TF.X Z y) ∈ LogKS.interior TF.Y from ⟨i₀ TF.Y Z v', ?_⟩)
      rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply, hv', ← Scheme.Hom.comp_apply, morphismRestrict_ι,
        Scheme.Hom.comp_apply]
    obtain ⟨g, hg⟩ := vanBd_le_space D T j Y e o hG hE Z TF la hs
    have e0 : f t = Submodule.inclusion (cusp_le_secZ Z Y.U la) g := by
      refine sub_eq_zero.1 (eq_zero_of_sec₀ TF.X Z (Submodule.sub_mem _ (hf t) g.2.2) ?_)
      rw [map_sub, hf' t, ← hg]
      exact sub_self _
    show (f t).1 ∈ _
    rw [e0]
    exact g.2
  · have e1 : TF.X.ptY yy ≫ TF.X.π = v ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
      rw [(TF.X.lies_ptY yy).1, j₀_ι, ← Category.assoc, hv]
      rfl
    have hr : Set.range (TF.X.ptY yy) ⊆ Set.range (inc₀ TF.X Z) := by
      rintro _ ⟨s, rfl⟩
      refine ⟨⟨_, show TF.X.π (TF.X.ptY yy s) ∈ barComp TF.Y Z from ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
      exact ((v ≫ j₀ TF.Y Z) s).2
    let zz := IsOpenImmersion.lift (inc₀ TF.X Z) (TF.X.ptY yy) hr
    have hzz : zz ≫ inc₀ TF.X Z = TF.X.ptY yy := IsOpenImmersion.lift_fac _ _ _
    have e2 : zz ≫ π₀ TF.X Z = v ≫ j₀ TF.Y Z := by
      have h1 : (zz ≫ π₀ TF.X Z) ≫ (barComp TF.Y Z).ι = (v ≫ j₀ TF.Y Z) ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, Category.assoc, ← e1, ← hzz, Category.assoc]
        exact congrArg (zz ≫ ·) (morphismRestrict_ι TF.X.π (barComp TF.Y Z))
      exact (cancel_mono _).1 h1
    obtain ⟨k', hk'⟩ := exists_chart_of_field (TF.X.F.isLB_LL (AllWt.exOf (T.Q.Dw j) la 0)) (TF.X.pt yy ≫ TF.X.inc)
    obtain ⟨Q, tt, hQ, htt⟩ := FlagCover.exists_chartFr_frBor TF.X yy k' hk'
    have hO : ⊤ ≤ (TF.X.pt yy ≫ TF.X.inc) ⁻¹ᵁ flagOpen TF.X :=
      FlagMod.le_preimage_map TF.X.inc (top_le_inc TF.X) le_top
    have hzO : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by rw [hzz, ← FlagCover.pt_inc]; exact hO
    have hzk : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ (TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0)).U k' := by
      rw [hzz, ← FlagCover.pt_inc]; exact hk'
    have hTop : ⊤ ≤ zz ⁻¹ᵁ (⊤ : (Y₀ TF.X Z).Opens) := fun _ _ => trivial
    have hz1 : ⊤ ≤ zz ⁻¹ᵁ U₀ TF.X Z := hzO
    have hz2 : ⊤ ≤ zz ⁻¹ᵁ (L₀ TF.X Z la).U (pIdx _ (inc₀ TF.X Z) k') := fun s hs => mem_pIdx.2 (hzk hs)
    have hπ1 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ (⊤ : (X₀ TF.Y Z).Opens) := fun _ _ => trivial
    have hπ2 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ L.U k := by rw [e2]; exact hk
    have hz3 : ⊤ ≤ zz ⁻¹ᵁ (L.pull (π₀ TF.X Z)).U (pIdx L (π₀ TF.X Z) k) := fun s hs => mem_pIdx.2 (hπ2 hs)
    have hz4 : ⊤ ≤ zz ⁻¹ᵁ (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))).U
        (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) := fun s hs => ⟨hz2 hs, hz3 hs⟩
    have hu : IsUnit (H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G) := by
      rw [H0.val_ofSec]
      exact (w.s (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)).isUnit.map (GlobalTheory.TangentOrigin.evalPt zz _ hz4)
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℂˣ, ∀ g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0),
        evR _ _ g.1 yy = c0.val * H0.val (TF.X.pt yy ≫ TF.X.inc) k' hO hk' (secOf TF.X _ g) :=
      ⟨_, fun g => evR_eq_val_secOf g hO hQ htt⟩
    refine ⟨c0 * hu.unit, fun t => ?_⟩
    show evR _ _ (f t).1 yy = _
    rw [hc0 (f t)]
    rw [val_congr_pt (p := flagStr TF.X) (B := TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0))
      ((FlagCover.pt_inc TF.X yy).trans hzz.symm) k' hO hk' hzO hzk]
    rw [show H0.val (zz ≫ inc₀ TF.X Z) k' hzO hzk (secOf TF.X _ (f t)) =
        H0.val zz (pIdx _ (inc₀ TF.X Z) k') hz1 hz2 (sec₀ TF.X Z _ (f t)) from
      (H0.val_pull (inc₀ TF.X Z) le_rfl zz (pIdx _ _ k') hz1 hz2 hzO hzk _).symm]
    rw [hf' t, val_restr_eq le_top zz _ hTop hz1 hz2]
    have e4 : H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) =
        H0.val (v ≫ j₀ TF.Y Z) k le_top hk t :=
      (H0.val_pull (π₀ TF.X Z) le_top zz (pIdx _ _ k) hTop hz3 hπ1 hπ2 t).trans (val_congr_pt e2 k hπ1 hπ2 le_top hk t)
    have e5 : H0.val zz (pIdx _ (inc₀ TF.X Z) k') hTop hz2 (sOf t) =
        H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) *
          H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G :=
      C.val_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) zz
        hTop hz3 hz4 hz2
    rw [e5, e4, Units.val_mul, IsUnit.unit_spec]
    ring

end GlobalTheory.OrbitSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectioStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  first | exact @GlobalTheory.OrbitSep.exists_rule_of_cls_pull | exact GlobalTheory.OrbitSep.exists_rule_of_cls_pull | (intros; apply GlobalTheory.OrbitSep.exists_rule_of_cls_pull <;> assumption)
end
end
