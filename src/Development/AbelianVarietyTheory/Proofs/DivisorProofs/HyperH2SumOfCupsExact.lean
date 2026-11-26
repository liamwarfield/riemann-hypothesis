module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh

theorem hyp2_eq_sum_cup_of_fn_exact : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ c : cechDeRhamTotalCocyclesTwo F, (∃ f, d1 F f = c.1.1) → ∃ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), Hyp2.mk F c = ∑ k, cupHyp F (a k) (clAll F hc (w k)) := by
  intro R _ C _ F hfr h0 hc hs c ⟨f, hf⟩
  obtain ⟨m, ⟨fr⟩⟩ := hfr
  have hcl : ∀ (w : Glob1 F) (T : C), dOne R _ (w.1 T) = 0 := fun w T ↦
    (show w ∈ Closed1 F by rw [hc]; trivial) T
  have hclAll : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F ⟨(0, w.1), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨zero_mem _,
      fun T T' φ ↦ by simpa using w.2 φ, fun T ↦ hcl w T⟩⟩ := fun w ↦ rfl
  set c' : cechDeRhamTotalCocyclesTwo F := c - ⟨dTot1 F (f, 0), dTot1_mem F _⟩ with hc'
  have hmk : Hyp2.mk F c = Hyp2.mk F c' := by
    rw [hc', map_sub, (Hyp2.mk_eq_zero (c := ⟨dTot1 F (f, 0), dTot1_mem F _⟩)).2 ⟨(f, 0), rfl⟩, sub_zero]
  have hz : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c'.1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    change c.1.1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [hf, sub_self]
  set a : A1 F := c'.1.2.1 with ha
  have hacoc : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ := by
    intro T T' T'' φ ψ
    rw [ha, cechDeRhamTotalCocyclesTwo.one c' φ ψ, hz, map_zero, add_zero]
  let g : Fin m → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    simp only [hacoc φ ψ, map_add (f := _), fr.nat]⟩
  have hE : ∀ i, ∃ e : cechDeRhamTotalCocyclesOne F, e.1.1 = (g i).1 := by
    intro i
    obtain ⟨x, hx⟩ := hs (H1.mk F (g i))
    obtain ⟨e0, rfl⟩ := Hyp1.mk_surjective F x
    rw [toO_mk, H1.mk_eq_mk] at hx
    obtain ⟨h, hh⟩ := hx
    refine ⟨e0 - ⟨dTot0 F h, dTot0_mem F h⟩, ?_⟩
    change e0.1.1 - d0 F h = (g i).1
    rw [hh]; change e0.1.1 - (e0.1.1 - (g i).1) = (g i).1; abel
  choose e he using hE
  let η' : W0 F 2 := fun T ↦ c'.1.2.2 T - ∑ i, wedge R _ ((e i).1.2 T) ((fr.w i).1 T)
  have hη' : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η' T' = pOm F 2 φ (η' T) := by
    intro T T' φ
    have hd : dOne R _ (a T T' φ) = ∑ i, wedge R _ (D R _ (fr.δ i T' (a T T' φ))) ((fr.w i).1 T') := by
      conv_lhs => rw [fr.sum T' (a T T' φ)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, dOne_smul, hcl]
    have hw : ∀ i, (fr.w i).1 T' = p1 F φ ((fr.w i).1 T) := fun i ↦ (fr.w i).2 φ
    have he' : ∀ i, (e i).1.2 T' = p1 F φ ((e i).1.2 T) + D R _ (fr.δ i T' (a T T' φ)) := by
      intro i; rw [cechDeRhamTotalCocyclesOne.conn (e i) φ, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [η', map_sub, map_sum, pOm_wedge]
    rw [cechDeRhamTotalCocyclesTwo.two c' φ, ← ha, hd]
    simp only [he', map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib, ← hw]
    abel
  obtain ⟨n, u, v, huv⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨m, ⟨fr⟩⟩ h0 η' hη'
  refine ⟨m + n, Fin.append (fun i ↦ Hyp1.mk F (e i)) (fun k ↦ clAll F hc (u k)), Fin.append fr.w v, ?_⟩
  rw [Fin.sum_univ_add]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fin.append_left, Fin.append_right, hclAll, cupHyp_mk, ← map_sum, ← map_add (f := _), hmk]
  congr 1
  apply Subtype.ext
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) (fun T ↦ ?_)
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.fst_add, Prod.fst_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_apply, hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Prod.fst_add, Prod.fst_sum,
      Pi.add_apply, Finset.sum_apply, coe_cupZZ, cupTot_a, Pi.zero_apply, zero_smul, sub_zero,
      Finset.sum_const_zero, add_zero, he]
    exact fr.sum T' (a T T' φ)
  · have := congrFun huv T
    simp only [η', wsum] at this
    simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_η]
    rw [← this]; abel
end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExactStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_h2_sum_of_cups_exact : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ c : cechDeRhamTotalCocyclesTwo F, (∃ f, d1 F f = c.1.1) → ∃ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), Hyp2.mk F c = ∑ k, cupHyp F (a k) (clAll F hc (w k)) := by
  first | exact @GlobalTheory.AbCoh.hyp2_eq_sum_cup_of_fn_exact | exact GlobalTheory.AbCoh.hyp2_eq_sum_cup_of_fn_exact | (intros; apply GlobalTheory.AbCoh.hyp2_eq_sum_cup_of_fn_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

open Opposite

namespace GlobalTheory.CechPoset

section Bij

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem sec_res_self (s : X ⟶ Sp R) {U : X.Opens} (h : U ≤ U) (c : Sec s U) : Sec.res s h c = c :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_id (op U))

theorem ker_res (s : X ⟶ Sp R) (g : LinearMap.ker (d0 (OAff s))) {U V : X.affineOpens}
    (h : V.1 ≤ U.1) : g.1 (op V) = Sec.res s h (g.1 (op U)) := by
  have := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (op U)) (op V))
    (homOfLE (show V ≤ U from h)).op
  rw [amitsur_d0_apply] at this
  exact sub_eq_zero.1 this

variable {κ : Type} [LinearOrder κ]

theorem kerF_res (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (g : LinearMap.ker (d0 (covF s D hD))) {I J : Finset κ} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) {U : X.Opens} (hU : U ≤ ⨅ k ∈ J, D k) (hU' : U ≤ ⨅ k ∈ I, D k) :
    Sec.res s hU' (g.1 (ne I hI)) = Sec.res s hU (g.1 (ne J hJ)) := by
  have e := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (ne I hI)) (ne J hJ))
    (homOf (a := ne I hI) (b := ne J hJ) h)
  rw [amitsur_d0_apply] at e
  have e' : g.1 (ne J hJ) = Sec.res s (show (⨅ k ∈ J, D k) ≤ ⨅ k ∈ I, D k from
      biInf_mono fun _ hk ↦ h hk) (g.1 (ne I hI)) := sub_eq_zero.1 e
  rw [e']
  exact Sec.res_res s _ hU _

end Bij

theorem restrictCompatibleFamilyToIntersections_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type}
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  intro hcov
  have hle1 : ∀ i : κ, D i ≤ ⨅ k ∈ ({i} : Finset κ), D k := fun i ↦
    le_iInf₂ fun k hk ↦ by rw [Finset.mem_singleton.1 hk]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : ∀ i : κ, g.1 (op (cov D hD (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))) = 0 :=
      fun i ↦ congrFun (congrArg Subtype.val hg) (ne {i} (Finset.singleton_nonempty i))
    apply Subtype.ext
    funext V
    show g.1 V = 0
    let Idx := {p : X.affineOpens × κ // p.1.1 ≤ V.unop.1 ⊓ D p.2}
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : Idx ↦ j.1.1.1) V.unop.1
      (fun j ↦ homOfLE (j.2.trans inf_le_left)) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, D i := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      obtain ⟨W, hWB, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ V.unop.1 ⊓ D i from ⟨hx, hi⟩)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨W, hWB⟩, i), hWle⟩, hxW⟩
    · intro j
      have hW : j.1.1.1 ≤ V.unop.1 := j.2.trans inf_le_left
      have hWi : j.1.1.1 ≤ (cov D hD (OrderDual.toDual ⟨{j.1.2}, Finset.singleton_nonempty _⟩)).1 :=
        (j.2.trans inf_le_right).trans (hle1 j.1.2)
      have e1 := ker_res s g (U := V.unop) (V := j.1.1) hW
      have e2 := ker_res s g (V := j.1.1) hWi
      rw [h0, map_zero] at e2
      show Sec.res s hW (g.1 V) = Sec.res s hW 0
      rw [map_zero, ← e1, e2]
  · intro g'
    let sf : ∀ i : κ, Sec s (D i) := fun i ↦ Sec.res s (hle1 i) (g'.1 (ne {i} (Finset.singleton_nonempty i)))
    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 D sf := by
      intro i j
      show Sec.res s inf_le_left (sf i) = Sec.res s inf_le_right (sf j)
      have hij : D i ⊓ D j ≤ ⨅ k ∈ ({i, j} : Finset κ), D k := le_iInf₂ fun k hk ↦ by
        obtain hk | hk := Finset.mem_insert.1 hk
        · rw [hk]; exact inf_le_left
        · rw [Finset.mem_singleton.1 hk]; exact inf_le_right
      exact (Sec.res_res s (hle1 i) inf_le_left _).symm.trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_left.trans (hle1 i))).trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty j) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_right.trans (hle1 j))).symm.trans
        (Sec.res_res s (hle1 j) inf_le_right _)))
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' D ⊤ (fun i ↦ homOfLE le_top) hcov.symm.le sf hcomp
    let g : LinearMap.ker (d0 (OAff s)) := ⟨fun V ↦ Sec.res s le_top (G : Γ(X, ⊤)), by
      rw [LinearMap.mem_ker]
      funext U U' φ
      rw [amitsur_d0_apply]
      show Sec.res s le_top (G : Γ(X, ⊤)) - Sec.res s _ (Sec.res s le_top (G : Γ(X, ⊤))) = 0
      exact sub_eq_zero.2 (Sec.res_res s _ _ _)⟩
    refine ⟨g, Subtype.ext (funext fun I ↦ ?_)⟩
    show Sec.res s le_top (G : Γ(X, ⊤)) = g'.1 I
    have hm := mn_mem I
    have hi : (cov D hD I.unop).1 ≤ D (mn I) := iInf₂_le (mn I) hm
    have hGi : Sec.res s (le_top : D (mn I) ≤ ⊤) (G : Γ(X, ⊤)) = sf (mn I) := hG (mn I)
    refine (Sec.res_res s le_top hi _).trans ?_
    rw [hGi]
    exact (Sec.res_res s (hle1 (mn I)) hi _).symm.trans
      ((kerF_res s D hD g' (Finset.singleton_nonempty (mn I)) (sub_nonempty I)
        (Finset.singleton_subset_iff.2 hm) le_rfl _).trans (sec_res_self s _ _))

end GlobalTheory.CechPoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.res0_bijective_of_affine_intersections_of_iSup_eq_top : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)), ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  first | exact @GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective | exact GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective | (intros; apply GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f f' : a ⟶ b) : f = f' :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_transport0 (g : C0 F) {a a' b : (NE κ)ᵒᵖ} (e : a = a') (f : a ⟶ b) (f' : a' ⟶ b) :
    mp F f (g a) = mp F f' (g a') := by
  subst e; rw [hom_eq f f']

theorem mp_transport1 {p : ℕ} (x : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (e : s = s')
    {b : (NE κ)ᵒᵖ} (f : ne s.1 (card_nonempty s) ⟶ b) (f' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F f (x s) = mp F f' (x s') := by
  subst e; rw [hom_eq f f']

theorem ne_eq_ne {s s' : Finset κ} (hs : s.Nonempty) (hs' : s'.Nonempty) (e : s = s') :
    ne s hs = ne s' hs' := by
  subst e; rfl

theorem min'_pair {i j : κ} (h : i < j) : ({i, j} : Finset κ).min' (Finset.insert_nonempty _ _) = i :=
  le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
    (Finset.le_min' _ _ _ (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> [exact le_rfl; exact h.le]))

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (z : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F z a b f = if h : mn b < mn a then
      -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))
        (z ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) else 0 := by
  simp only [e1, LinearMap.pi_apply]; split_ifs <;> simp

end GlobalTheory.CechHOneInj

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem δ_pair (z : CC F 1) (g : C0 F) (hg : e1 F z = d0 F g) {i j : κ} (h : i < j)
    (hs : ({i, j} : Finset κ).card = 1 + 1) :
    δ F 0 (fun s => g (ne s.1 (card_nonempty s))) ⟨{i, j}, hs⟩ = z ⟨{i, j}, hs⟩ := by
  have hi : i ∈ ({i, j} : Finset κ) := Finset.mem_insert_self _ _
  have hj : j ∈ ({i, j} : Finset κ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have sij : ({i} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hi
  have sji : ({j} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hj
  have ei : ({i, j} : Finset κ).erase i = {j} := Finset.erase_insert (by simp [h.ne])
  have ej : ({i, j} : Finset κ).erase j = {i} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨h.ne, Or.inl rfl⟩
  have h1 := congrFun (congrFun (congrFun hg (ne {i} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sij)
  have h2 := congrFun (congrFun (congrFun hg (ne {j} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sji)
  have mi : mn (ne ({i} : Finset κ) (Finset.singleton_nonempty _)) = i := Finset.min'_singleton i
  have mj : mn (ne ({j} : Finset κ) (Finset.singleton_nonempty _)) = j := Finset.min'_singleton j
  have mij : mn (ne ({i, j} : Finset κ) (Finset.insert_nonempty _ _)) = i := min'_pair h
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dite_eq_right (by rw [mi, mij]; exact lt_irrefl i)] at h1
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dite_eq_left (by rw [mj, mij]; exact h)] at h2
  have key := mp_transport1 F z
    (s := ⟨{mn (ne {i, j} (Finset.insert_nonempty _ _)), mn (ne {j} (Finset.singleton_nonempty _))},
      Finset.card_pair (by rw [mj, mij]; exact h.ne)⟩) (s' := ⟨{i, j}, hs⟩)
    (Subtype.ext (by simp only [mj, mij])) (homOf (pair_subset (homOf sji))) (𝟙 _)
  rw [mp_id] at key
  have si : GlobalTheory.cubeSign ({i, j} : Finset κ) i = 1 :=
    GlobalTheory.cubeSign_eq_one_of_forall_le (by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact le_rfl
      · exact h.le)
  have sj : GlobalTheory.cubeSign ({i, j} : Finset κ) j = -1 := by
    have := GlobalTheory.cubeSign_erase_of_lt hi h (t := ({i, j} : Finset κ))
    rw [ei, GlobalTheory.cubeSign_singleton] at this
    linarith
  rw [δ_apply, Fintype.sum_eq_add ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h.ne]) (by
    rintro ⟨x, hx⟩ ⟨ha, hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact absurd rfl ha
    · exact absurd rfl hb)]
  dsimp only
  have tj := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty j) ei)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨i, hi⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {j} (Finset.singleton_nonempty j)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sji)
  have ti := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty i) ej)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨j, hj⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {i} (Finset.singleton_nonempty i)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sij)
  rw [si, sj, one_smul, neg_smul, one_smul]
  linear_combination h2 - h1 + key + tj - ti

theorem exists_cech_primitive : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 →
    ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  intro κ _ R _ F z _ g hg
  refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_⟩
  funext t
  obtain ⟨s, hs⟩ := t
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hs
  rcases lt_or_gt_of_ne hij with h | h
  · exact δ_pair F z g hg h hs
  · revert hs
    rw [Finset.pair_comm i j]
    exact δ_pair F z g hg h

end GlobalTheory.CechHOneInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundaryStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_primitive_of_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 → ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  first | exact @GlobalTheory.CechHOneInj.exists_cech_primitive | exact GlobalTheory.CechHOneInj.exists_cech_primitive | (intros; apply GlobalTheory.CechHOneInj.exists_cech_primitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

def triVal (c : CC F 2) (X : (NE κ)ᵒᵖ) (s : Finset κ) : F.obj X :=
  if h : s.card = 2 + 1 ∧ s ⊆ sub X then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := X) h.2) (c ⟨s, h.1⟩)
  else 0

variable {F}

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f g : a ⟶ b) : f = g := Subsingleton.elim _ _

theorem triVal_eq (c : CC F 2) (X : (NE κ)ᵒᵖ) {s : Finset κ} (hs : s.card = 2 + 1) (h : s ⊆ sub X) :
    mp F (homOf (a := ne s (card_nonempty ⟨s, hs⟩)) (b := X) h) (c ⟨s, hs⟩) = triVal F c X s := by
  unfold triVal; rw [dite_eq_left ⟨hs, h⟩]

theorem triVal_map (c : CC F 2) {X Y : (NE κ)ᵒᵖ} (f : X ⟶ Y) {s : Finset κ} (h : s ⊆ sub X) :
    mp F f (triVal F c X s) = triVal F c Y s := by
  unfold triVal
  by_cases hs : s.card = 2 + 1
  · rw [dite_eq_left ⟨hs, h⟩, dite_eq_left ⟨hs, h.trans (sub_subset f)⟩, ← mp_comp]
    congr 1
  · rw [dite_eq_right (fun h' => hs h'.1), dite_eq_right (fun h' => hs h'.1), map_zero]

theorem alternatingToOrderedCechDegreeTwo_apply_triple (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then -triVal F c d {mn d, mn b, mn a} else 0 := by
  unfold e2
  simp only [LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← triVal_eq c d (card_three h.1 h.2) (triple_subset f g)]
    rfl
  · rfl

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem triVal_eq' (c : CC F 2) {X : (NE κ)ᵒᵖ} (s : {s : Finset κ // s.card = 2 + 1})
    (f : ne s.1 (card_nonempty s) ⟶ X) : mp F f (c s) = triVal F c X s.1 := by
  obtain ⟨s, hs⟩ := s
  rw [← triVal_eq c X hs (sub_subset f), hom_eq f (homOf (sub_subset f))]

theorem triVal_rel (c : CC F 2) (hc : δ F 2 c = 0) (X : (NE κ)ᵒᵖ) {w x y z : κ}
    (h1 : w < x) (h2 : x < y) (h3 : y < z) (hs : ({w, x, y, z} : Finset κ) ⊆ sub X) :
    triVal F c X {x, y, z} - triVal F c X {w, y, z} + triVal F c X {w, x, z} - triVal F c X {w, x, y} = 0 := by
  have ht : ({w, x, y, z} : Finset κ).card = 2 + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
      Finset.card_insert_of_notMem (by simp [h2.ne, (h2.trans h3).ne]), Finset.card_pair h3.ne]
  have e := congrArg (mp F (homOf (a := ne _ (card_nonempty ⟨_, ht⟩)) (b := X) hs))
    (congrFun hc ⟨_, ht⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [δ_apply, map_sum, Pi.zero_apply, map_zero] at e
  have e' : ∑ i ∈ ({w, x, y, z} : Finset κ), GlobalTheory.cubeSign ({w, x, y, z} : Finset κ) i •
      triVal F c X (({w, x, y, z} : Finset κ).erase i) = 0 := by
    rw [← e, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← mp_comp, triVal_eq']
  rw [Finset.sum_insert (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
    Finset.sum_insert (by simp [h2.ne, (h2.trans h3).ne]), Finset.sum_pair h3.ne] at e'
  have hwx := h1.ne; have hwy := (h1.trans h2).ne; have hwz := (h1.trans (h2.trans h3)).ne
  have hxy := h2.ne; have hxz := (h2.trans h3).ne; have hyz := h3.ne
  simp only [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h1, h2, h3, h1.trans h2,
    h1.trans (h2.trans h3), h2.trans h3, lt_irrefl, not_lt_of_gt, if_true, if_false] at e'
  simp only [Finset.insert_empty, Finset.card_empty, Finset.card_singleton,
    Finset.card_pair hwx, Finset.card_insert_of_notMem (show w ∉ ({x, y} : Finset κ) by simp [hwx, hwy]),
    Finset.card_pair hxy] at e'
  rw [Finset.erase_insert (by simp [hwx, hwy, hwz]),
    Finset.erase_insert_of_ne hwx, Finset.erase_insert (by simp [hxy, hxz]),
    Finset.erase_insert_of_ne hwy, Finset.erase_insert_of_ne hxy,
    Finset.erase_insert (by simp [hyz]),
    Finset.erase_insert_of_ne hwz, Finset.erase_insert_of_ne hxz,
    Finset.erase_insert_of_ne hyz, Finset.erase_singleton] at e'
  norm_num at e'
  linear_combination e'

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem alternatingToOrderedCechDegreeTwo_map_apply (c : CC F 2) {a b d g : (NE κ)ᵒᵖ} (f : a ⟶ b) (f' : b ⟶ d) (f'' : d ⟶ g) :
    mp F f'' (e2 F c a b d f f') =
      if mn d < mn b ∧ mn b < mn a then -triVal F c g {mn d, mn b, mn a} else 0 := by
  rw [alternatingToOrderedCechDegreeTwo_apply_triple]
  split_ifs
  · rw [map_neg, triVal_map c f'' (triple_subset f f')]
  · exact map_zero _

theorem e2_mem_Z2_of_delta_eq_zero (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2) (hc : δ F 2 c = 0) :
    e2 F c ∈ Z2 F := by
  intro a b d g φ ψ χ
  have hab := mn_le_of_hom φ; have hbd := mn_le_of_hom ψ; have hdg := mn_le_of_hom χ
  have hs : ({mn g, mn d, mn b, mn a} : Finset κ) ⊆ sub g := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mn_mem g
    · exact sub_subset χ (mn_mem d)
    · exact sub_subset (ψ ≫ χ) (mn_mem b)
    · exact sub_subset (φ ≫ ψ ≫ χ) (mn_mem a)
  have hrel : mn g < mn d → mn d < mn b → mn b < mn a →
      triVal F c g {mn d, mn b, mn a} - triVal F c g {mn g, mn b, mn a} +
        triVal F c g {mn g, mn d, mn a} - triVal F c g {mn g, mn d, mn b} = 0 :=
    fun h1 h2 h3 => triVal_rel c hc g h1 h2 h3 hs
  rw [alternatingToOrderedCechDegreeTwo_map_apply, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple]
  generalize mn a = xa at *
  generalize mn b = xb at *
  generalize mn d = xd at *
  generalize mn g = xg at *
  rcases hdg.lt_or_eq with h1 | rfl <;> rcases hbd.lt_or_eq with h2 | rfl <;>
    rcases hab.lt_or_eq with h3 | rfl <;>
    simp_all [lt_irrefl, not_lt_of_ge, le_of_lt]
  rw [if_pos (h2.trans h3), if_pos (h1.trans h2)]
  linear_combination -hrel
end GlobalTheory.CechPoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := by
  first | exact @GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | exact GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | (intros; apply GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (φ ψ : a ⟶ b) : φ = ψ :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

noncomputable def V (f : Z1 F) (b : (NE κ)ᵒᵖ) (x : κ) : F.obj b :=
  if hx : x ∈ sub b then
    f.1 (ne {x} (Finset.singleton_nonempty x)) b
      (homOf (show ({x} : Finset κ) ⊆ sub b from Finset.singleton_subset_iff.2 hx))
  else 0

variable {F}

theorem V_res (f : Z1 F) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b) {x : κ} (hx : x ∈ sub a) :
    mp F φ (V F f a x) = V F f b x - f.1 a b φ := by
  unfold V
  rw [dite_eq_left hx, dite_eq_left (sub_subset φ hx)]
  have e := Z1.comp f (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := a)
    (Finset.singleton_subset_iff.2 hx)) φ
  rw [hom_eq (_ ≫ φ) (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := b)
    (Finset.singleton_subset_iff.2 (sub_subset φ hx)))] at e
  rw [e]
  ring

noncomputable def zc (f : Z1 F) : CC F 1 := fun t =>
  V F f (ne t.1 (card_nonempty t)) (t.1.min' (card_nonempty t)) -
    V F f (ne t.1 (card_nonempty t)) (t.1.max' (card_nonempty t))

theorem zc_res (f : Z1 F) (s : {s : Finset κ // s.card = 1 + 1}) (b : (NE κ)ᵒᵖ)
    (h : sub (ne s.1 (card_nonempty s)) ⊆ sub b) :
    mp F (homOf h) (zc f s) = V F f b (s.1.min' (card_nonempty s)) - V F f b (s.1.max' (card_nonempty s)) := by
  unfold zc
  rw [map_sub, V_res f (homOf h) (x := s.1.min' (card_nonempty s)) (Finset.min'_mem _ _),
    V_res f (homOf h) (x := s.1.max' (card_nonempty s)) (Finset.max'_mem _ _)]
  ring

theorem pair_min_max {s : Finset κ} {x y : κ} (hs : s = {x, y}) (h : x < y) (hne : s.Nonempty) :
    s.min' hne = x ∧ s.max' hne = y := by
  subst hs
  constructor
  · exact le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact le_rfl
      · exact h.le))
  · exact le_antisymm (Finset.max'_le _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact h.le
      · exact le_rfl)) (Finset.le_max' _ _ (by simp))

theorem exists_triple {s : Finset κ} (h : s.card = 3) : ∃ a b c, a < b ∧ b < c ∧ s = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  all_goals first
    | exact absurd (h1.trans h3) (not_lt.2 h2.le)
    | exact absurd (h2.trans h3) (not_lt.2 h1.le)
    | exact absurd (h1.trans h2) (not_lt.2 h3.le)
    | exact absurd (h3.trans h1) (not_lt.2 h2.le)
    | exact absurd (h2.trans h1) (not_lt.2 h3.le)
    | exact absurd (h3.trans h2) (not_lt.2 h1.le)
    | (refine ⟨x, y, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨x, z, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, x, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, z, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, x, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, y, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem erase3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset κ).erase a = {b, c} ∧ ({a, b, c} : Finset κ).erase b = {a, c} ∧
      ({a, b, c} : Finset κ).erase c = {a, b} := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> ext w <;> simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;>
    constructor
  all_goals first
    | (rintro ⟨hw, h | h | h⟩ <;> first | exact absurd h hw | (subst h; simp))
    | (rintro (h | h) <;> subst h <;> simp [hab.ne, hab.ne', hbc.ne, hbc.ne', hac.ne, hac.ne'])

theorem sign3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    GlobalTheory.cubeSign ({a, b, c} : Finset κ) a = 1 ∧ GlobalTheory.cubeSign ({a, b, c} : Finset κ) b = -1 ∧
      GlobalTheory.cubeSign ({a, b, c} : Finset κ) c = 1 := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hab, hbc, hac,
    not_lt.2 hab.le, not_lt.2 hbc.le, not_lt.2 hac.le, Finset.card_pair hab.ne]

theorem part2 (f : Z1 F) : f.1 - e1 F (zc f) = d0 F (fun a => V F f a (mn a)) := by
  funext a b φ
  simp only [Pi.sub_apply, amitsur_d0_apply]
  rw [V_res f φ (mn_mem a)]
  by_cases h : mn b < mn a
  · have e : e1 F (zc f) a b φ = -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b)
        (pair_subset φ)) (zc f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) := by
      simp [e1, h]
    have z := zc_res f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b (pair_subset φ)
    obtain ⟨h1, h2⟩ := pair_min_max (s := ({mn b, mn a} : Finset κ)) rfl h (Finset.insert_nonempty _ _)
    rw [h1, h2] at z
    rw [e]
    linear_combination z
  · have e : e1 F (zc f) a b φ = 0 := by simp [e1, h]
    have e' : mn b = mn a := le_antisymm (mn_le_of_hom φ) (not_lt.1 h)
    rw [e, e']
    ring

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def term3 {M : Type} [AddCommGroup M] (W : κ → M) (a b c x : κ) : M :=
  GlobalTheory.cubeSign ({a, b, c} : Finset κ) x • (if x = a then W b - W c else if x = b then W a - W c else W a - W b)

theorem sum3 {M : Type} [AddCommGroup M] (W : κ → M) {a b c : κ} (hab : a < b) (hbc : b < c) :
    ∑ x ∈ ({a, b, c} : Finset κ), term3 W a b c x = 0 := by
  have hac := hab.trans hbc
  rw [Finset.sum_insert (by simp [hab.ne, hac.ne]), Finset.sum_insert (by simp [hbc.ne]),
    Finset.sum_singleton]
  obtain ⟨s1, s2, s3⟩ := sign3 hab hbc
  simp only [term3, if_pos rfl, if_neg hab.ne', if_neg hac.ne', if_neg hbc.ne', s1, s2, s3, one_smul, neg_smul]
  norm_num

theorem part1 (f : Z1 F) : δ F 1 (zc f) = 0 := by
  funext t
  rw [δ_apply]
  obtain ⟨s, hs⟩ := t
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_triple (s := s) (by rw [hs])
  have hac := hab.trans hbc
  obtain ⟨e1', e2', e3'⟩ := erase3 hab hbc
  refine (Finset.sum_congr rfl
    (g := fun i : ({a, b, c} : Finset κ) => term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c i.1)
    fun i _ => ?_).trans ?_
  · have z := zc_res f (GlobalTheory.Cube.eraseIdx ⟨{a, b, c}, hs⟩ i) (ne _ (card_nonempty ⟨_, hs⟩))
      (Finset.erase_subset i.1 _)
    rw [z]
    obtain ⟨x, hx⟩ := i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{x, b, c}, hs⟩ ⟨x, by simp⟩).1) e1' hbc
        (card_nonempty _)
      rw [h1, h2, term3, if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, x, c}, hs⟩ ⟨x, by simp⟩).1) e2' hac
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hab.ne', if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, b, x}, hs⟩ ⟨x, by simp⟩).1) e3' hab
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hac.ne', if_neg hbc.ne']
  · refine (Finset.sum_coe_sort ({a, b, c} : Finset κ)
      (term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c)).trans ?_
    exact sum3 _ hab hbc

end GlobalTheory.CechPoset.CechPosetH1Surjective


open GlobalTheory.CechPoset.CechPosetH1Surjective in
theorem GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F),
    ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g :=
  fun F f => ⟨zc f, part1 f, fun a => V F f a (mn a), part2 f⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_cocycle_cohomologous_posetOneCocycle : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F), ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g := by
  first | exact @GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous | exact GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous | (intros; apply GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous <;> assumption)
end
end
