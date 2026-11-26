module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem fp_HH1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : FP R (HH1 A.hom) (2 * g) := by
  have hcl := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hs
  have h0 := (GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs).2.1
  have hinj : Function.Injective (clAll (OAff A.hom) hcl) := by
    unfold clAll
    exact (ofForm_injective_of_H0Const R _ _ h0).comp (LinearEquiv.ofTop _ hcl).symm.injective
  have hex : Function.Exact (clAll (OAff A.hom) hcl) (toHO1 A.hom) := by
    rw [LinearMap.exact_iff]
    change Fil1 (OAff A.hom) = _
    rw [Fil1_eq_range]
    unfold clAll
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).1 R _ _ _ g g _ _ hinj (GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hs) hex
    (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).1
  rwa [two_mul]

theorem rank_prim_HH1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  intro R _ A _ g hA hs
  refine ⟨fp_HH1 R A g hA hs, fun x ↦ ?_⟩
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have ax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.2
  set i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : HH1 A.hom × HH1 A.hom →ₗ[R] HH1 (A ⊗ A).hom :=
    (deRhamH1Pullback (fst A A)).coprod (deRhamH1Pullback (snd A A))
  let r : HH1 (A ⊗ A).hom →ₗ[R] HH1 A.hom × HH1 A.hom := (deRhamH1Pullback i₁).prod (deRhamH1Pullback i₂)
  have hrf : ∀ p, r (f p) = p := by
    rintro ⟨a, b⟩
    show (deRhamH1Pullback i₁ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b), deRhamH1Pullback i₂ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b)) = (a, b)
    rw [map_add (f := _), map_add (f := _), (ax a).1, (ax b).2.1, (ax a).2.2.2.1, (ax b).2.2.2.2.1, add_zero, zero_add]
  have hM : FP R (HH1 A.hom × HH1 A.hom) (2 * (g + g)) := by
    have := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ _ _ (fp_HH1 R A g hA hs) (fp_HH1 R A g hA hs)
    rwa [← mul_add] at this
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ _ hM (fp_HH1 R (A ⊗ A) (g + g) hAA hsAA) f r hrf
  obtain ⟨p, hp⟩ := hbij.2 (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)
  have hry : r (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x) = 0 := by
    show (deRhamH1Pullback i₁ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x),
      deRhamH1Pullback i₂ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)) = (0, 0)
    rw [map_sub, map_sub, map_sub, map_sub, (ax x).1, (ax x).2.1, (ax x).2.2.1,
      (ax x).2.2.2.1, (ax x).2.2.2.2.1, (ax x).2.2.2.2.2, sub_self, sub_zero, sub_zero, sub_self]
  have hp0 : p = 0 := by rw [← hrf p, hp, hry]
  have h0 : deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x = 0 := by rw [← hp, hp0, map_zero]
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_h1_rank_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.rank_prim_HH1 | exact GlobalTheory.AbCoh.rank_prim_HH1 | (intros; apply GlobalTheory.AbCoh.rank_prim_HH1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedge
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedge
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem cupSum_eq_zero_iff_wsum_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (n : ℕ)
    (u v : Fin n → Glob1 F) :
    ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  have hcl : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F (formZZ F ⟨w, hc ▸ Submodule.mem_top⟩) :=
    fun w ↦ rfl
  have hsum : ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) =
      Hyp2.mk F (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hcl, cupHyp_mk, map_sum]
  have hval : ∀ T, (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.2 T = wsum F u v T := by
    intro T
    simp only [Submodule.coe_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_η, wsum]
    rfl
  have h1 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    simp only [Submodule.coe_sum, Prod.fst_sum, Finset.sum_apply, coe_cupZZ, cupTot_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change mp F ψ 0 * 0 = 0
    simp
  have h2 : ∀ T T' (φ : T ⟶ T'), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.1 T T' φ = 0 := by
    intro T T' φ
    simp only [Submodule.coe_sum, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_a]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change (0 : F.obj T') • _ - (0 : F.obj T') • _ = 0
    simp
  rw [hsum, Hyp2.mk_eq_zero]
  constructor
  · rintro ⟨e, he⟩
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (dTot1 F e).1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
      rw [he]; exact h1 T T' T'' φ ψ
    have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' = p1 F φ (e.2 T) + D R _ (e.1 T T' φ) := fun T T' φ ↦ by
      have := (congrArg (fun x : Tot2 F ↦ x.2.1 T T' φ) he).trans (h2 T T' φ)
      rw [dTot1_a] at this
      rw [sub_sub, sub_eq_zero] at this
      exact this
    have hη : ∀ T, dOne R _ (e.2 T) = wsum F u v T := fun T ↦ by
      have := congrArg (fun x : Tot2 F ↦ x.2.2 T) he
      rw [dTot1_η] at this
      rw [this, hval]
    have hf : e.1 ∈ Z1 F := by
      rw [commAlgFunctorCocyclesOne_eq_ker]
      funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    obtain ⟨c, hcz⟩ := hs (CatCoh.H1.mk F ⟨e.1, hf⟩)
    obtain ⟨cz, rfl⟩ := Hyp1.mk_surjective F c
    rw [toO_mk, CatCoh.H1.mk_eq_mk] at hcz
    obtain ⟨g, hg⟩ := hcz
    have hg' : ∀ T T' (φ : T ⟶ T'), g T' - mp F φ (g T) = cz.1.1 T T' φ - e.1 T T' φ := fun T T' φ ↦
      congrFun (congrFun (congrFun hg T) T') φ
    let θ : A0 F := fun T ↦ e.2 T - (cz.1.2 T - D R _ (g T))
    have hθ : θ ∈ Glob1 F := by
      intro T T' φ
      simp only [θ, map_sub, p1_D]
      have hgT : g T' = mp F φ (g T) + (cz.1.1 T T' φ - e.1 T T' φ) := by rw [← hg' T T' φ]; abel
      rw [ha T T' φ, cechDeRhamTotalCocyclesOne.conn cz φ, hgT]
      simp only [map_add (f := _), map_sub]
      abel
    have hθc : (⟨θ, hθ⟩ : Glob1 F) ∈ Closed1 F := hc ▸ Submodule.mem_top
    funext T
    have hθ0 : dOne R _ (e.2 T - (cz.1.2 T - D R _ (g T))) = 0 := hθc T
    rw [map_sub, map_sub, cechDeRhamTotalCocyclesOne.closed cz T, dOne_D, sub_zero, sub_zero] at hθ0
    rw [← hη T, hθ0]; rfl
  · intro hw
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine Tot2.ext (fun T T' T'' φ ψ ↦ (h1 T T' T'' φ ψ).symm) (fun T T' φ ↦ (h2 T T' φ).symm)
      fun T ↦ ?_
    rw [hval, hw]; rfl

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (u v : Fin n → Glob1 F), ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  first | exact @GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero | exact GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero | (intros; apply GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamHypercohomologyCupAnticomm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamHypercohomologyCupAnticomm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem cupHyp_add_cupHyp_swap : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  intro R _ C _ F a b
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add (f := _)]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · simp only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply,
      cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]
    ring
  · simp only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ,
      cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    module
  · simp only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η,
      Pi.zero_apply, map_zero]
    rw [wedge_swap (a.1.2 T), neg_add_cancel]

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamHypercohomologyCupAnticommStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  first | exact @GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | exact GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | (intros; apply GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section Helpers

variable {R : Type} [CommRing R]

theorem cup_self_eq_zero_of_wedgeO' {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F)
    (x : CatCoh.H1 F) : cup F x x = 0 := by
  obtain ⟨e, he⟩ := hW
  rw [← he]
  have : exteriorPower.ιMulti R 2 ![x, x] = 0 :=
    AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
  rw [this, map_zero]

theorem fn_cupZZ_self_exact {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F) (c : cechDeRhamTotalCocyclesOne F) :
    ∃ f, d1 F f = (cupZZ F c c).1.1 := by
  have h := cup_self_eq_zero_of_wedgeO' hW (H1.mk F (cechDeRhamTotalCocyclesOne.fn F c))
  rw [cup_mk, H2.mk_eq_zero] at h
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf⟩

variable {Y A : Over (Sp R)}

theorem pH2_cupHH_over (f : Y ⟶ A) (a b : HH1 A.hom) :
    deRhamH2Pullback f (cupHH A.hom a b) = cupHH Y.hom (deRhamH1Pullback f a) (deRhamH1Pullback f b) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.1 a b

theorem toHO1_pH1_over (f : Y ⟶ A) (a : HH1 A.hom) : toHO1 Y.hom (deRhamH1Pullback f a) = pO1 f (toHO1 A.hom a) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.2 a

theorem pH1_clAll_over (f : Y ⟶ A) (hc : Closed1 (OAff A.hom) = ⊤) (hc' : Closed1 (OAff Y.hom) = ⊤)
    (w : GlobForm A.hom) : deRhamH1Pullback f (clAll (OAff A.hom) hc w) = clAll (OAff Y.hom) hc' (pF f w) :=
  GlobalTheory.T.pull_closed_form_class R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) hc hc' w

end Helpers

section Wsum

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem wsum_finAppend {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem wsum_neg_first {n : ℕ} (u v : Fin n → Glob1 F) : wsum F (fun k ↦ -u k) v = -wsum F u v := by
  funext T
  simp only [wsum, Submodule.coe_neg, Pi.neg_apply, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]

theorem wsum_eq_add_of_cupSum_eq (hc : Closed1 F = ⊤) (hsur : Function.Surjective (toO F)) {m : ℕ}
    (u₁ v₁ u₂ v₂ u₃ v₃ : Fin m → Glob1 F)
    (h : ∑ k, cupHyp F (clAll F hc (u₁ k)) (clAll F hc (v₁ k)) =
      ∑ k, cupHyp F (clAll F hc (u₂ k)) (clAll F hc (v₂ k)) + ∑ k, cupHyp F (clAll F hc (u₃ k)) (clAll F hc (v₃ k))) :
    wsum F u₁ v₁ = wsum F u₂ v₂ + wsum F u₃ v₃ := by
  have h2 : ∑ k, cupHyp F (clAll F hc (Fin.append (Fin.append u₁ (fun k ↦ -u₂ k)) (fun k ↦ -u₃ k) k))
      (clAll F hc (Fin.append (Fin.append v₁ v₂) v₃ k)) = 0 := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]
    rw [h]
    abel
  have h3 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hsur _ _ _).1 h2
  rw [wsum_finAppend, wsum_finAppend, wsum_neg_first, wsum_neg_first] at h3
  rw [← sub_eq_zero, ← h3]
  abel

end Wsum

theorem cupHH_self_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ a : HH1 A.hom, cupHH A.hom a a = 0 := by
  intro R _ A _ g hA hs a
  have hb := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hb2 := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hc := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hs
  have hc2 := GlobalTheory.T.abelianScheme_globalOneForms_closed R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hsur := GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hs
  have hsur2 := GlobalTheory.T.de_rham_to_structure_h1_surjective R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hW := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).2.1
  have hP : ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x := (GlobalTheory.T.de_rham_h1_rank_primitive R A g hA hs).2
  have hPF : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  have hax := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  have anti := GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm R _ (OAff (A ⊗ A).hom)

  have hprim : deRhamH2Pullback μ[A] (cupHH A.hom a a) =
      deRhamH2Pullback (fst A A) (cupHH A.hom a a) + deRhamH2Pullback (snd A A) (cupHH A.hom a a) := by
    rw [pH2_cupHH_over, pH2_cupHH_over, pH2_cupHH_over, hP a]
    have h := anti (deRhamH1Pullback (fst A A) a) (deRhamH1Pullback (snd A A) a)
    simp only [map_add (f := _), LinearMap.add_apply]
    linear_combination (norm := module) h

  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective _ a
  obtain ⟨n, a', w, hz⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R _ (OAff A.hom) hb.1 hb.2.1 hc hsur (cupZZ _ c c) (fn_cupZZ_self_exact hW c)
  rw [← cupHyp_mk] at hz
  change cupHH A.hom _ _ = _ at hz
  set z := cupHH A.hom (Hyp1.mk _ c) (Hyp1.mk _ c)
  clear_value z

  have hcross : ∑ k, (cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (fst A A) (a' k)) (clAll _ hc2 (pF (snd A A) (w k))) +
      cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (snd A A) (a' k)) (clAll _ hc2 (pF (fst A A) (w k)))) = 0 := by
    have h := hprim
    rw [hz] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2, hP, hPF, map_add (f := _), LinearMap.add_apply,
      Finset.sum_add_distrib] at h
    rw [Finset.sum_add_distrib]
    linear_combination (norm := module) h

  have hk : ∀ l : Glob1 (OAff A.hom) →ₗ[R] R, ∑ k, l (w k) • toO (OAff A.hom) (a' k) = 0 := by
    intro l
    have h2 : ∑ k, cupHH (A ⊗ A).hom
        (Fin.append (fun k ↦ deRhamH1Pullback (fst A A) (a' k)) (fun k ↦ deRhamH1Pullback (snd A A) (a' k)) k)
        (clAll _ hc2 (Fin.append (fun k ↦ pF (snd A A) (w k)) (fun k ↦ pF (fst A A) (w k)) k)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← Finset.sum_add_distrib]
      exact hcross
    have h3 := GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero R _ _ hb2.1 hb2.2.1 hc2 hsur2 (n + n) _ _ h2
      (l ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
    rw [Fin.sum_univ_add] at h3
    simp only [Fin.append_left, Fin.append_right, LinearMap.comp_apply, (hax.2.1 _).2.2.2.1,
      (hax.2.1 _).2.2.2.2.1, map_zero, zero_smul, Finset.sum_const_zero, add_zero] at h3
    have h4 := congrArg (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero] at h4
    simpa only [toHO1_pH1_over, (hax.1 _).1] using h4

  obtain ⟨m, ⟨Φ⟩⟩ := hb.1
  obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R _ (OAff A.hom) hb.2.1 m Φ
  have hu : ∀ i, ∃ u : Glob1 (OAff A.hom), clAll _ hc u = ∑ k, L i (w k) • a' k := by
    intro i
    have hm : ∑ k, L i (w k) • a' k ∈ Fil1 (OAff A.hom) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fil1, LinearMap.mem_ker, map_sum]
      simpa only [map_smul] using hk (L i)
    rw [Fil1_eq_range] at hm
    obtain ⟨ω, hω⟩ := hm
    refine ⟨ω.1, ?_⟩
    rw [← hω]
    rfl
  choose u hu using hu
  have hz2 : z = ∑ i, cupHyp (OAff A.hom) (clAll _ hc (u i)) (clAll _ hc (Φ.w i)) := by
    rw [hz]
    simp only [hu]
    conv_lhs => enter [2, k]; rw [hL (w k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_comm

  have hwp : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (Φ.w k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (Φ.w k)) +
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (Φ.w k)) := by
    have h := hprim
    rw [hz2] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2] at h
    exact wsum_eq_add_of_cupSum_eq _ hc2 hsur2 _ _ _ _ _ _ h
  have hw0 := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hs m u Φ.w hwp
  rw [hz2]
  exact (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R _ _ hc hsur m u Φ.w).2 hw0

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelianStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_self_zero_de_rham_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ a : HH1 A.hom, cupHH A.hom a a = 0 := by
  first | exact @GlobalTheory.AbCoh.cupHH_self_eq_zero | exact GlobalTheory.AbCoh.cupHH_self_eq_zero | (intros; apply GlobalTheory.AbCoh.cupHH_self_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SpanCup

theorem sum_append {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) {n m : ℕ} (a : Fin n → M) (b : Fin n → N)
    (a' : Fin m → M) (b' : Fin m → N) :
    ∑ k, B (a k) (b k) + ∑ k, B (a' k) (b' k) = ∑ k, B (Fin.append a a' k) (Fin.append b b' k) := by
  rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

theorem exists_sum_ιMulti {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (x y : Fin n → M), w = ∑ k, exteriorPower.ιMulti R 2 ![x k, y k] := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨n, x, y, rfl⟩ := hu
    obtain ⟨m, x', y', rfl⟩ := hv
    refine ⟨n + m, Fin.append x x', Fin.append y y', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r v _ hv =>
    obtain ⟨n, x, y, rfl⟩ := hv
    refine ⟨n, fun k ↦ r • x k, y, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • x k, y k] : Fin 2 → M) = Function.update ![x k, y k] 0 (r • ![x k, y k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cechDeRhamFunctionPart_cup_eq_cup (a b : cechDeRhamTotalCocyclesOne F) : fn2 F (cupZZ F a b) = cupZ F (cechDeRhamTotalCocyclesOne.fn F a) (cechDeRhamTotalCocyclesOne.fn F b) := rfl

end GlobalTheory.AbCoh.SpanCup


open GlobalTheory.AbCoh.SpanCup in
theorem GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) →
    WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  intro R _ C _ F hfr h0 hc hsurj hw z
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F z
  obtain ⟨e, he⟩ := hw
  obtain ⟨n, x, y, hxy⟩ := exists_sum_ιMulti (e.symm (H2.mk F (fn2 F c)))
  have hrep : ∀ u : H1 F, ∃ p : cechDeRhamTotalCocyclesOne F, toO F (Hyp1.mk F p) = u := fun u ↦ by
    obtain ⟨q, hq⟩ := hsurj u
    obtain ⟨p, rfl⟩ := Hyp1.mk_surjective F q
    exact ⟨p, hq⟩
  choose p hp using hrep
  have hcls : H2.mk F (fn2 F c) = ∑ k, cup F (x k) (y k) := by
    have h := congrArg e hxy
    rw [LinearEquiv.apply_symm_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    simp only [he]
  obtain ⟨c', hc'⟩ : ∃ c' : cechDeRhamTotalCocyclesTwo F, c' = c - ∑ k, cupZZ F (p (x k)) (p (y k)) := ⟨_, rfl⟩
  have hfn : ∃ f, d1 F f = c'.1.1 := by
    have h : H2.mk F (fn2 F c') = 0 := by
      rw [hc']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum]
      rw [hcls, sub_eq_zero]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [cechDeRhamFunctionPart_cup_eq_cup, ← cup_mk, ← toO_mk, ← toO_mk, hp, hp]
    exact H2.mk_eq_zero.1 h
  obtain ⟨m, a, w, hm⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R C F hfr h0 hc hsurj c' hfn
  refine ⟨m + n, Fin.append a (fun k ↦ Hyp1.mk F (p (x k))),
    Fin.append (fun k ↦ clAll F hc (w k)) (fun k ↦ Hyp1.mk F (p (y k))), ?_⟩
  rw [← sum_append, ← hm, hc']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, cupHyp_mk, sub_add_cancel]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCupsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_h2_generated_by_cups : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  first | exact @GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | exact GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | (intros; apply GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem upd_congr {J : Type} [DecidableEq J] (p : M →ₗ[R] H) (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0)
    (u : J → M) (j : J) (a b : M) (hab : p a = p b) :
    F (Function.update u j a) = F (Function.update u j b) := by
  have h1 : a = b + (a - b) := by abel
  rw [h1, F.map_update_add, hF (Function.update u j (a - b)) j (by simp [hab]), add_zero]

noncomputable def descend {J : Type} (p : M →ₗ[R] H) (hp : Function.Surjective p)
    (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0) :
    H [⋀^J]→ₗ[R] Q where
  toFun v := F (fun k => Function.surjInv hp (v k))
  map_update_add' := by
    intro _ v j x y
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (Function.surjInv hp x + Function.surjInv hp y)
      (by simp [Function.surjInv_eq hp]), F.map_update_add]
  map_update_smul' := by
    intro _ v j c x
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (c • Function.surjInv hp x)
      (by simp [Function.surjInv_eq hp]), F.map_update_smul, RingHom.id_apply]
  map_eq_zero_of_eq' := by
    intro v a b hv hab
    exact F.map_eq_zero_of_eq _ (by simp [hv]) hab

end GlobalTheory.ExtSqKer

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem fin_two_vector_eq_matrixVecCons (u : Fin 2 → M) : u = ![u 0, u 1] := by
  ext k; fin_cases k <;> rfl

theorem congr_two (p : M →ₗ[R] H) (F : M [⋀^Fin 2]→ₗ[R] Q)
    (hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0)
    (u u' : Fin 2 → M) (h : ∀ k, p (u k) = p (u' k)) : F u = F u' := by
  calc F u = F (Function.update u 0 (u 0)) := by rw [Function.update_eq_self]
    _ = F (Function.update u 0 (u' 0)) := upd_congr p F hF u 0 _ _ (h 0)
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 ((Function.update u 0 (u' 0)) 1)) := by
        rw [Function.update_eq_self]
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 (u' 1)) :=
        upd_congr p F hF _ 1 _ _ (by simpa using h 1)
    _ = F u' := by
        congr 1; ext k; fin_cases k <;> simp

end GlobalTheory.ExtSqKer


open GlobalTheory.ExtSqKer in
theorem GlobalTheory.exteriorSquare_ker_of_surjective (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  set S : Set (⋀[R]^2 M) := {x | ∃ (a : M) (w : W), x = exteriorPower.ιMulti R 2 ![a, i w]}
  set N : Submodule R (⋀[R]^2 M) := Submodule.span R S
  let F : M [⋀^Fin 2]→ₗ[R] (⋀[R]^2 M ⧸ N) := N.mkQ.compAlternatingMap (exteriorPower.ιMulti R 2)
  have hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0 := by
    intro u j hj
    obtain ⟨w, hw⟩ := (hex (u j)).1 hj
    simp only [F, LinearMap.compAlternatingMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    fin_cases j
    · have e : u = ![u 1, i w] ∘ Equiv.swap 0 1 := by
        ext k; fin_cases k <;> simp [hw]
      rw [e, AlternatingMap.map_swap _ _ (by decide)]
      exact N.neg_mem (Submodule.subset_span ⟨u 1, w, rfl⟩)
    · rw [fin_two_vector_eq_matrixVecCons u]
      exact Submodule.subset_span ⟨u 0, w, by simp [hw]⟩
  let g := exteriorPower.alternatingMapLinearEquiv (descend p hp F hF)
  have hg : g ∘ₗ exteriorPower.map 2 p = N.mkQ := by
    apply exteriorPower.linearMap_ext
    ext m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      exteriorPower.map_apply_ιMulti, g, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change F _ = F m
    exact congr_two p F hF _ _ (fun k => by simp [Function.surjInv_eq hp])
  have hN : t ∈ N := by
    have := congrArg (fun f => f t) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_zero, Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hN
  choose a w haw using fun k => (x k).2
  refine ⟨n, fun k => c k • a k, w, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haw k]
  have e : ![c k • a k, i (w k)] = Function.update ![a k, i (w k)] 0 (c k • a k) := by
    ext l; fin_cases l <;> simp
  rw [e, AlternatingMap.map_update_smul]
  congr 2
  ext l; fin_cases l <;> simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero : ∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Surjective p → Function.Exact i p → ∀ t : ⋀[R]^2 M, exteriorPower.map 2 p t = 0 → ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W), t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  first | exact @GlobalTheory.exteriorSquare_ker_of_surjective | exact GlobalTheory.exteriorSquare_ker_of_surjective | (intros; apply GlobalTheory.exteriorSquare_ker_of_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Wedge

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem update_pair_vector_zero (a b x : M) : Function.update ![a, b] 0 x = ![x, b] := by
  funext i; fin_cases i <;> simp

theorem update_pair_vector_one (a b x : M) : Function.update ![a, b] 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp

def ιTwo : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 0 a a'
      simpa only [update_pair_vector_zero] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 0 r a
      simpa only [update_pair_vector_zero] using h)
    (fun a b b' ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 1 b b'
      simpa only [update_pair_vector_one] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 1 r b
      simpa only [update_pair_vector_one] using h)

theorem ιTwo_apply (a b : M) : ιTwo a b = exteriorPower.ιMulti R 2 ![a, b] := by
  rw [ιTwo, LinearMap.mk₂_apply]

theorem ιTwo_self (a : M) : ιTwo (R := R) a a = 0 := by
  rw [ιTwo_apply]
  exact (exteriorPower.ιMulti R 2 (M := M)).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

theorem ιTwo_swap (a b : M) : ιTwo (R := R) b a = -ιTwo a b := by
  have h := ιTwo_self (R := R) (a + b)
  simp only [map_add (f := _), LinearMap.add_apply, ιTwo_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem sum_sum_ιTwo_of_symm {n : ℕ} (x : Fin n → M) (c : Fin n → Fin n → R)
    (hc : ∀ a b, c a b = c b a) : ∑ a, ∑ b, c a b • ιTwo (R := R) (x a) (x b) = 0 := by
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun a b ↦ c a b • ιTwo (R := R) (x a) (x b))]
  refine Finset.sum_involution (fun p _ ↦ p.swap) (fun p _ ↦ ?_) (fun p _ hp ↦ ?_)
    (fun p _ ↦ by simp) (fun p _ ↦ Prod.swap_swap p)
  · simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hc p.2 p.1, ιTwo_swap (x p.1), smul_neg, add_neg_cancel]
  · intro he
    apply hp
    have : p.1 = p.2 := (Prod.ext_iff.1 he).2
    simp only [this, ιTwo_self, smul_zero]

end Wedge

section Forget

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fnZZ2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hypercohomologyTwoToAlgebraCohomology : Hyp2 F →ₗ[R] CatCoh.H2 F :=
  Submodule.mapQ _ _ (fnZZ2 F) (by rintro _ ⟨e, rfl⟩; exact ⟨e.1, rfl⟩)

theorem hypercohomologyTwo_cup_forget_forms (a b : Hyp1 F) : hypercohomologyTwoToAlgebraCohomology F (cupHyp F a b) = cup F (toO F a) (toO F b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rfl

def cupProductWedge (halt : ∀ a, cupHyp F a a = 0) : Hyp1 F [⋀^Fin 2]→ₗ[R] Hyp2 F where
  toFun v := cupHyp F (v 0) (v 1)
  map_update_add' v i a b := by fin_cases i <;> simp
  map_update_smul' v i r a := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

def cupWedge (halt : ∀ a, cupHyp F a a = 0) : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F :=
  exteriorPower.alternatingMapLinearEquiv (cupProductWedge F halt)

theorem cupWedge_ιTwo (halt : ∀ a, cupHyp F a a = 0) (a b : Hyp1 F) :
    cupWedge F halt (ιTwo a b) = cupHyp F a b := by
  rw [ιTwo_apply, cupWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem exact_clAll_toO (hc : Closed1 F = ⊤) : Function.Exact (clAll F hc) (toO F) := by
  intro y
  constructor
  · intro hy
    have h : y ∈ Fil1 F := hy
    rw [Fil1_eq_range] at h
    obtain ⟨ω, rfl⟩ := h
    exact ⟨ω.1, rfl⟩
  · rintro ⟨w, rfl⟩
    have h : clAll F hc w ∈ Fil1 F := by
      rw [Fil1_eq_range]; exact ⟨_, rfl⟩
    exact h

end Forget

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem exists_wedge_hyp_equiv : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F →
    (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  intro R _ C _ F hF h0 hc hs hw halt
  let e₀ := cupWedge F halt
  have e₀_ι : ∀ a b, e₀ (ιTwo a b) = cupHyp F a b := cupWedge_ιTwo F halt
  have hsurj : Function.Surjective e₀ := by
    intro z
    obtain ⟨n, a, b, rfl⟩ := GlobalTheory.T.hyper_h2_generated_by_cups R C F hF h0 hc hs hw z
    exact ⟨∑ k, ιTwo (a k) (b k), by simp only [map_sum, e₀_ι]⟩
  have hex := exact_clAll_toO F hc
  have hinj : Function.Injective e₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    obtain ⟨ew, hew⟩ := hw

    have hcomm : ew.toLinearMap ∘ₗ exteriorPower.map 2 (toO F) = hypercohomologyTwoToAlgebraCohomology F ∘ₗ e₀ := by
      refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      have hv' : (toO F) ∘ v = ![toO F (v 0), toO F (v 1)] := by funext i; fin_cases i <;> rfl
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti, hv', hew]
      rw [hv, ← ιTwo_apply, e₀_ι, hypercohomologyTwo_cup_forget_forms]
      rfl
    have h1 : exteriorPower.map 2 (toO F) t = 0 := by
      apply ew.injective
      have := LinearMap.congr_fun hcomm t
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [this, ht, map_zero, map_zero]
    obtain ⟨m, a, w, rfl⟩ := GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero R (Glob1 F) (Hyp1 F) (CatCoh.H1 F) (clAll F hc) (toO F) hs hex t h1
    simp only [← ιTwo_apply] at ht ⊢
    have hsum : ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, e₀_ι] using ht
    obtain ⟨N, ⟨Φ⟩⟩ := hF
    obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
    let x : Fin N → Hyp1 F := fun i ↦ clAll F hc (Φ.w i)
    have hcl : ∀ v : Glob1 F, clAll F hc v = ∑ i, l i v • x i := by
      intro v
      conv_lhs => rw [hl v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, x]

    let Mi : Fin N → Hyp1 F := fun i ↦ ∑ k, l i (w k) • a k
    have ht1 : ∑ k, ιTwo (R := R) (a k) (clAll F hc (w k)) = ∑ i, ιTwo (Mi i) (x i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hcl, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Mi]
      exact Finset.sum_comm
    have hM0 : ∀ i, toO F (Mi i) = 0 := by
      intro i
      have := GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero R C F ⟨N, ⟨Φ⟩⟩ h0 hc hs m a w hsum (l i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [Mi, map_sum, map_smul] using this
    have hMu : ∀ i, ∃ u, clAll F hc u = Mi i := fun i ↦ (hex (Mi i)).1 (hM0 i)
    choose u hu using hMu
    rw [ht1]
    simp only [← hu]
    have hcup : ∑ i, cupHyp F (clAll F hc (u i)) (clAll F hc (Φ.w i)) = 0 := by
      rw [← ht, ht1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← hu, map_sum, e₀_ι, x]
    have hw2 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hs N u Φ.w).1 hcup
    have hsym := (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R C F ⟨N, ⟨Φ⟩⟩ h0 N u Φ.w).1 hw2
    let c : Fin N → Fin N → R := fun p q ↦ ∑ i, l p (u i) * l q (Φ.w i)
    have hc' : ∀ p q, c p q = c q p := by
      intro p q
      have := hsym (l p) (l q)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c]
      rw [this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    have step : ∀ i, ιTwo (R := R) (clAll F hc (u i)) (x i) =
        ∑ p, ∑ q, (l p (u i) * l q (Φ.w i)) • ιTwo (R := R) (x p) (x q) := by
      intro i
      rw [hcl (u i)]
      conv_lhs => rw [show x i = ∑ q, l q (Φ.w i) • x q from hcl (Φ.w i)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by rw [mul_comm]
    have hexp : ∑ i, ιTwo (R := R) (clAll F hc (u i)) (x i) = ∑ p, ∑ q, c p q • ιTwo (R := R) (x p) (x q) := by
      simp only [step]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [c, Finset.sum_smul]
    rw [hexp]
    exact sum_sum_ιTwo_of_symm x c hc'
  refine ⟨LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun a b ↦ ?_⟩
  have := e₀_ι a b
  rw [ιTwo_apply] at this
  exact this

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_h2_exterior_square_iso : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  first | exact @GlobalTheory.AbCoh.exists_wedge_hyp_equiv | exact GlobalTheory.AbCoh.exists_wedge_hyp_equiv | (intros; apply GlobalTheory.AbCoh.exists_wedge_hyp_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham := by
  intro R _ A _ g hA hg
  obtain ⟨hfr, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hO, hW, hB1, -⟩ := GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg
  have hcl := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hg
  have hs := GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hg
  have hH := (GlobalTheory.T.de_rham_h1_rank_primitive R A g hA hg).1
  refine ⟨⟨hH.1, hH.2.1, fun p ↦ (hH.2.2 p).trans (by push_cast; rfl)⟩,
    GlobalTheory.T.hyper_h2_exterior_square_iso R _ (OAff A.hom) hfr h0 hcl hs hW (GlobalTheory.T.cup_self_zero_de_rham_abelian R A g hA hg),
    GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg, hO, ⟨hcl, ofForm_injective_of_H0Const R _ (OAff A.hom) h0, hs⟩, ?_⟩
  intro R' _ _ X' s' φ h
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ := GlobalTheory.T.de_rham_global_forms_base_change R A g hA hg R' X' s' φ h
  obtain ⟨e₃, he₃⟩ := hB1 R' X' s' φ h
  refine ⟨⟨e₁, fun c ↦ ?_⟩, ⟨e₂, fun c ↦ ?_⟩, e₃, fun c ↦ ?_⟩
  · rw [he₁]; exact isPull1_pullHH1 h.w c
  · rw [he₂]; exact isPullForm_pullForm h.w c
  · rw [he₃]; exact isPullO_pullHO1 h.w c

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegeneratesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates : GlobalTheory.Published.AbelianHodgeDeRham := by
  first | exact @GlobalTheory.AbCoh.abelianHodgeDeRham | exact GlobalTheory.AbCoh.abelianHodgeDeRham | (intros; apply GlobalTheory.AbCoh.abelianHodgeDeRham <;> assumption)
end
