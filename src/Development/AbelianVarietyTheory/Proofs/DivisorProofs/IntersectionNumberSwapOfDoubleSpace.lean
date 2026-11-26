module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBase
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem interNumRed_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  intro F _ Y W y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hemb := W.δ.isClosedEmbedding
  have hcl : Set.range W.δ = closure {W.δ (genericPoint Y.X)} := by
    rw [← Set.image_singleton, hemb.closure_image_eq, genericPoint_spec Y.X, Set.image_univ]
  have hf : ∀ r : F, W.δ.appTop (algebraMap F Γ(W.Z, ⊤) r) = algebraMap F Γ(Y.X, ⊤) r := fun r => by
    show W.δ.appTop ((W.p₁ ≫ Y.str).appTop ((Scheme.ΓSpecIso (.of F)).inv r)) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, W.δ₁, Category.id_comp]
    rfl
  show interNumRed F _ _ = _
  rw [InterModel.interNumRed_eq_interNumOn F W.δ _ hcl, interNumOn_eq_interNum_pull hf fun i => isLB_toLB (y i)]
  refine (interNum_congr_cls F _ (fun i => isLB_toLB (e i)) (fun i => LB.isLB_pull (isLB_toLB (y i)) _) fun i => ?_).symm
  rw [cls_pull (isLB_toLB (y i))]
  rcases h i with h | h
  · rw [← PullPres.pull_cls_toLB _ _ W.p₁ _ _ h, ← CechPic.pull_comp, W.δ₁, CechPic.pull_id]
  · rw [← PullPres.pull_cls_toLB _ _ W.p₂ _ _ h, ← CechPic.pull_comp, W.δ₂, CechPic.pull_id]

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBaseStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  first | exact @GlobalTheory.FlagPush.interNumRed_section | exact GlobalTheory.FlagPush.interNumRed_section | (intros; apply GlobalTheory.FlagPush.interNumRed_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem Dbl.num_eq_zero_of_isPull : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (q : W.Z ⟶ Y.X) [IsDominant q] (y : Fin (Y.dim + 1) → CartierDiv W.Z) (e : Fin (Y.dim + 1) → Y.Dv), (∀ i, IsPull q (y i) (e i)) → W.num y = 0 := by
  intro F _ Y W hW q _ y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hp : IsProjOver (strHom F (X := W.Z)) := by
    rw [strHom_eq (f := W.p₁ ≫ Y.str) fun _ => rfl]
    exact W.proj
  have hd : topologicalKrullDim W.Z ≤ (0 + (Y.dim + 1) : ℕ) := by
    rw [Nat.zero_add]; exact hW
  have hg : topologicalKrullDim (closure ({q (genericPoint W.Z)} : Set Y.X)) < (Y.dim + 1 : ℕ) := by
    refine lt_of_le_of_lt (topologicalKrullDim_subspace_le _ _) ?_
    rw [Y.topologicalKrullDim_eq]
    exact_mod_cast Nat.lt_succ_self _
  have key := GlobalTheory.PullVanish.interNum_pull_eq_zero F 0 (Y.dim + 1) W.Z Y.X hp hd q hg Fin.elim0
    (fun i => i.elim0) (fun i => toLB (e i)) (fun i => isLB_toLB _)
  have hL : ∀ x, (Sum.elim (Fin.elim0 : Fin 0 → LB W.Z) (fun a => (toLB (e a)).pull q) x).IsLB := by
    rintro (i | a)
    · exact i.elim0
    · exact pull_isLB (isLB_toLB _) q
  rw [← interNum_comp_equiv F _ hL (Equiv.emptySum (Fin 0) (Fin (Y.dim + 1))).symm] at key
  refine Eq.trans ?_ key
  refine interNum_congr_cls F _ (fun i => isLB_toLB _) (fun i => hL _) fun i => ?_
  exact ((cls_pull (isLB_toLB (e i)) q (pull_isLB (isLB_toLB _) q)).trans
    (GlobalTheory.Cartier.PullPres.pull_cls_toLB _ _ q (y i) (e i) (h i))).symm

end GlobalTheory.FlagPush
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (q : W.Z ⟶ Y.X) [IsDominant q] (y : Fin (Y.dim + 1) → CartierDiv W.Z) (e : Fin (Y.dim + 1) → Y.Dv), (∀ i, IsPull q (y i) (e i)) → W.num y = 0 := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull | exact GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull | (intros; apply GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush.Dbl

theorem num_cons_eq_mul_of_supp_eq_range : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  intro F _ Y W hW Θ hΘ hsupp
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hstr : strHom F W.Z = W.p₁ ≫ Y.str := GlobalTheory.strHom_eq fun _ => rfl
  have hp : IsProjOver (strHom F (X := W.Z)) := hstr ▸ W.proj
  have : IsLocallyNoetherian W.Z := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType (strHom F (X := W.Z)) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (strHom F W.Z)
  obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq Θ hΘ
  set η := genericPoint Y.X
  set w₀ := W.δ η
  have hδ := W.δ.isClosedEmbedding
  have hcl : closure ({w₀} : Set W.Z) = Set.range W.δ := by
    rw [← Set.image_singleton, hδ.closure_image_eq, (genericPoint_spec Y.X).def, Set.image_univ]
  have hd : topologicalKrullDim (closure ({w₀} : Set W.Z)) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hδ.isEmbedding hcl.symm, Y.topologicalKrullDim_eq]
  have hw₀ : w₀ ∈ Θ.supp := by
    show w₀ ∈ (Θ.supp : Set W.Z); rw [hsupp]; exact ⟨η, rfl⟩
  have hmax : ¬ IsMax w₀ := fun h =>
    Θ.genericPoint_notMem_supp ((h (genericPoint_specializes w₀)).mem_closed Θ.supp.isClosed hw₀)
  have hc := GlobalTheory.SecCycle.coheight_eq_one_of_dim_closure hW hmax hd
  refine ⟨Θ.mult w₀, ?_, fun y => ?_⟩
  · have hws : w₀ ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := fun h =>
      (GlobalTheory.Cartier.notMem_supp_divOfSec.2 h) (e.symm ▸ hw₀)
    have := GlobalTheory.SecCycle.mult_divOfSec_ne_zero (isLB_toLB Θ) s hs hc hws
    rwa [e] at this
  · have hcons : (fun i => toLB ((Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) i)) =
        (Fin.cons (toLB Θ) (fun i => toLB (y i)) : Fin (Y.dim + 1) → LB W.Z) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hF := GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult F W.Z hp Y.dim hW (toLB Θ)
      (isLB_toLB Θ) (fun i => toLB (y i)) (fun i => isLB_toLB (y i)) s hs
    rw [e] at hF
    show interNum F (structureModule W.Z) _ = _
    rw [hcons, hF]
    refine finsum_eq_single _ w₀ fun w hw => ?_
    by_cases hm : Θ.mult w = 0
    · rw [hm, zero_mul]
    obtain ⟨y', rfl⟩ : w ∈ Set.range W.δ := by
      rw [← hsupp]; exact CartierDiv.mem_supp_of_mult_ne_zero hm
    have hy' : y' ≠ η := fun h => hw (by rw [h])
    have hnot : w₀ ∉ closure ({W.δ y'} : Set W.Z) := fun h => by
      have h1 : W.δ y' ⤳ W.δ η := specializes_iff_mem_closure.2 h
      have h2 : y' ⤳ η := hδ.isInducing.specializes_iff.1 h1
      exact hy' (h2.antisymm (genericPoint_specializes y')).eq
    have hsp : w₀ ⤳ W.δ y' := specializes_iff_mem_closure.2 (hcl.symm ▸ ⟨y', rfl⟩ : W.δ y' ∈ closure ({w₀} : Set W.Z))
    have h1 : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) + 1 ≤ topologicalKrullDim (closure ({w₀} : Set W.Z)) :=
      topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz =>
        ⟨w₀, subset_closure rfl, hnot, hsp.trans (specializes_iff_mem_closure.2 hz)⟩
    rw [hd] at h1
    have hlt : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) < (Fintype.card (Fin Y.dim) : ℕ) := by
      rw [Fintype.card_fin]; exact GlobalTheory.SheafCycle.lt_of_add_one_le_natCast h1
    rw [GlobalTheory.SheafCycle.interNumRed_eq_zero F hp (fun i => isLB_toLB (y i)) _ hlt, mul_zero]

end GlobalTheory.FlagPush.Dbl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | exact GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | (intros; apply GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDim
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.ProjVar.Var

theorem interPoly_eq_zero_of_isHomogeneous (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ)
    (P : MvPolynomial κ ℝ) (hP : P.IsHomogeneous k) (hk : k ≠ Y.dim) : Y.interPoly gr P = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight 1 d = k := hP (mem_support_iff.mp hd)
  have e : monomial d (AddMonoidAlgebra.coeff P d) = AddMonoidAlgebra.coeff P d • basisMonomials κ ℝ d := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hk
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, ← hs, map_sum]
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

end GlobalTheory.ProjVar.Var
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDimStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim : ∀ (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ Y.dim → Y.interPoly gr P = 0 := by
  first | exact @GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | exact GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | (intros; apply GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntersectionFormPicardDoubleSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intersectionForm_picard_doubleSpace : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∃ T : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => Pic W.Z) ℤ, (∀ (σ : Equiv.Perm (Fin (Y.dim + 1))) (y : Fin (Y.dim + 1) → Pic W.Z), T (y ∘ σ) = T y) ∧ ∀ y : Fin (Y.dim + 1) → CartierDiv W.Z, T (fun i => toPic (y i)) = W.num y := by
  intro F _ Y W hW
  let := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hv : DiffVanish (Y.dim + 1 + 1) (chiPic F (structureModule W.Z)) :=
    diffVanish_chiPic_of_isProjOver (algebraΓOfHom_algebraMap (W.p₁ ≫ Y.str)) (structureModule W.Z) W.proj
      (by rw [GlobalTheory.QCoh.suppDim_structureModule]; exact hW)
  refine ⟨hv.form, fun σ y => hv.form_comp_perm y σ, fun y => ?_⟩
  rw [hv.form_apply _ 0]
  show _ = interNum F (structureModule W.Z) fun i => toLB (y i)
  rw [interNum_eq_multiDiff F _ fun i => isLB_toLB (y i)]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAntisymmOfDoublePointSymmMultilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAntisymmOfDoublePointSymmMultilinear
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.MultiLevel

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial in
open Classical in
private theorem exists_fin_sum_single_eq_of_degree_eq {κ : Type} :
    ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n → ∃ s : Fin n → κ, ∑ i, Finsupp.single (s i) 1 = m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    refine ⟨Fin.elim0, ?_⟩
    rw [Finsupp.degree_eq_zero_iff] at hm
    simp [hm]
  | succ n ih =>
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hm0
    have hle : Finsupp.single x 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hx
      omega
    have hsplit : m - Finsupp.single x 1 + Finsupp.single x 1 = m := tsub_add_cancel_of_le hle
    have hdeg : (m - Finsupp.single x 1).degree = n := by
      have h := congrArg Finsupp.degree hsplit
      rw [map_add (f := _), Finsupp.degree_single, hm] at h
      omega
    obtain ⟨s, hs⟩ := ih _ hdeg
    refine ⟨Fin.cons x s, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hs, add_comm, hsplit]


open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial in
open Classical in
theorem _root_.GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear : ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (A : Type) [AddCommGroup A] (n : ℕ) (T : (Fin (n + 1) → A) →ₘₗ[ℤ] ℤ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1) → A), T (y ∘ σ) = T y) → ∀ (u v : κ → A) (L : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (μ : ℤ), μ ≠ 0 → (∀ x, x ≠ a → x ≠ b → u x = v x) → u a + u b = v a + v b → (∀ s : Fin (n + 1) → κ, T (u ∘ s) = 0) → (∀ s : Fin (n + 1) → κ, T (v ∘ s) = 0) → (∀ (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ n → L P = 0) → (∀ s : Fin n → κ ⊕ κ, ((T (Fin.cons (v b - u a) (Sum.elim u v ∘ s)) : ℤ) : ℝ) = μ * L (∏ i, X (Sum.elim id id (s i)))) → ∀ Q : MvPolynomial κ ℝ, L (rename (Equiv.swap a b) Q) = - L Q := by
  intro κ a b hab A _ n T hT u v L μ hμ hoff hsum hu hv hL hmix
  set w := v b - u a with hw
  set d := u a - v a with hd
  have hcons : ∀ (x y : A) (Z : Fin n → A),
      T (Fin.cons (x - y) Z) = T (Fin.cons x Z) - T (Fin.cons y Z) := by
    intro x y Z
    simp only [← MultilinearMap.curryLeft_apply, map_sub, MultilinearMap.sub_apply]
  have hmixeq : ∀ t t' : Fin n → κ ⊕ κ, (∀ i, Sum.elim id id (t i) = Sum.elim id id (t' i)) →
      T (Fin.cons w (Sum.elim u v ∘ t)) = T (Fin.cons w (Sum.elim u v ∘ t')) := by
    intro t t' htt
    have h1 := hmix t
    have h2 := hmix t'
    have e : (∏ i, X (Sum.elim id id (t i)) : MvPolynomial κ ℝ) = ∏ i, X (Sum.elim id id (t' i)) := by
      simp only [htt]
    rw [e, ← h2] at h1
    exact_mod_cast h1
  have hZ : ∀ (t : Fin n → κ ⊕ κ) (k : Fin n),
      T (Fin.cons w (Function.update (Sum.elim u v ∘ t) k d)) = 0 := by
    intro t k
    rw [Fin.cons_update, hd, T.map_update_sub, ← Fin.cons_update, ← Fin.cons_update]
    have e1 : Function.update (Sum.elim u v ∘ t) k (u a) =
        Sum.elim u v ∘ Function.update t k (Sum.inl a) := by
      funext i
      by_cases h : i = k <;> simp [h, Function.update_apply]
    have e2 : Function.update (Sum.elim u v ∘ t) k (v a) =
        Sum.elim u v ∘ Function.update t k (Sum.inr a) := by
      funext i
      by_cases h : i = k <;> simp [h, Function.update_apply]
    rw [e1, e2, sub_eq_zero]
    apply hmixeq
    intro i
    by_cases h : i = k <;> simp [h, Function.update_apply]
  have hposition : ∀ (Y : Fin n → A) (k : Fin n),
      T (Fin.cons d (Function.update Y k w)) = T (Fin.cons w (Function.update Y k d)) := by
    intro Y k
    rw [← hT (Equiv.swap 0 k.succ) (Fin.cons d (Function.update Y k w))]
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [Equiv.swap_apply_left]
    · by_cases h : i = k
      · subst h
        simp only [Function.comp_apply, Equiv.swap_apply_right, Fin.cons_zero, Fin.cons_succ,
          Function.update_self]
      · have hne : i.succ ≠ k.succ := fun e => h (Fin.succ_injective _ e)
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) hne]
        simp [h]
  have hw' : w = u b - v a := by
    rw [hw, sub_eq_sub_iff_add_eq_add, add_comm (v b), add_comm (u b)]
    exact hsum.symm
  have hva : v a = u a - d := by rw [hd, sub_sub_cancel]
  have hua : u a = v a + d := by rw [hd, add_sub_cancel]
  have hu_side : ∀ s' : Fin n → κ, T (Fin.cons w (u ∘ s')) = T (Fin.cons d (u ∘ s')) := by
    intro s'
    have h1 : T (Fin.cons (u b) (u ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hu _
    have h2 : T (Fin.cons (u a) (u ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hu _
    rw [hw', hcons, hva, hcons, h1, h2]
    abel
  have hv_side : ∀ s' : Fin n → κ, T (Fin.cons w (v ∘ s')) = - T (Fin.cons d (v ∘ s')) := by
    intro s'
    have h1 : T (Fin.cons (v b) (v ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hv _
    have h2 : T (Fin.cons (v a) (v ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hv _
    rw [hw, hcons, h1, hua]
    simp only [← MultilinearMap.curryLeft_apply, map_add (f := _), MultilinearMap.add_apply] at h2 ⊢
    rw [h2]
    abel
  have hdiff : ∀ x : κ, ∃ ε : ℤ, u (Equiv.swap a b x) - v x = ε • w := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      refine ⟨1, ?_⟩
      rw [Equiv.swap_apply_left, one_smul, hw']
    · by_cases hxb : x = b
      · subst hxb
        refine ⟨-1, ?_⟩
        rw [Equiv.swap_apply_right, neg_smul, one_smul, hw]
        abel
      · refine ⟨0, ?_⟩
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, hoff x hxa hxb, sub_self, zero_smul]
  have hchain : ∀ s : Fin n → κ, T (Fin.cons d (v ∘ s)) = T (Fin.cons d (u ∘ Equiv.swap a b ∘ s)) := by
    intro s
    let Y : ℕ → Fin n → A := fun k i => if (i : ℕ) < k then u (Equiv.swap a b (s i)) else v (s i)
    have hY : ∀ k, ∃ t : Fin n → κ ⊕ κ, Y k = Sum.elim u v ∘ t := by
      intro k
      refine ⟨fun i => if (i : ℕ) < k then Sum.inl (Equiv.swap a b (s i)) else Sum.inr (s i), ?_⟩
      funext i
      simp only [Y, Function.comp_apply]
      split_ifs <;> rfl
    have hstep : ∀ k, T (Fin.cons d (Y k)) = T (Fin.cons d (Y 0)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← ih]
        by_cases hk : k < n
        · let K : Fin n := ⟨k, hk⟩
          have e1 : Y (k + 1) = Function.update (Y k) K (u (Equiv.swap a b (s K))) := by
            funext i
            by_cases hi : i = K
            · subst hi
              simp [Y, K]
            · have hik : (i : ℕ) ≠ k := fun e => hi (Fin.ext e)
              simp only [Y, Function.update_apply, hi, if_false]
              by_cases hlt : (i : ℕ) < k
              · rw [if_pos hlt, if_pos (by omega)]
              · rw [if_neg hlt, if_neg (by omega)]
          have e0 : Y k = Function.update (Y k) K (v (s K)) := by
            rw [eq_comm, Function.update_eq_self_iff]
            simp [Y, K]
          obtain ⟨ε, hε⟩ := hdiff (s K)
          obtain ⟨t, ht⟩ := hY k
          rw [← sub_eq_zero, e1]
          conv_lhs => rw [e0]
          rw [Function.update_idem, Fin.cons_update, Fin.cons_update, ← T.map_update_sub,
            ← Fin.cons_update, hε, Fin.cons_update, T.map_update_smul, ← Fin.cons_update, hposition, ht,
            hZ, smul_zero]
        · have e : Y (k + 1) = Y k := by
            funext i
            have h1 : (i : ℕ) < k := by omega
            have h2 : (i : ℕ) < k + 1 := by omega
            simp [Y, h1, h2]
          rw [e]
    have e0 : Y 0 = v ∘ s := by
      funext i
      simp [Y]
    have en : Y n = u ∘ Equiv.swap a b ∘ s := by
      funext i
      simp [Y, i.2]
    rw [← e0, ← en]
    exact (hstep n).symm
  have hkey : ∀ s : Fin n → κ,
      T (Fin.cons w (u ∘ Equiv.swap a b ∘ s)) = - T (Fin.cons w (u ∘ s)) := by
    intro s
    have hm := hmixeq (Sum.inl ∘ s) (Sum.inr ∘ s) (fun i => rfl)
    have el : Sum.elim u v ∘ (Sum.inl ∘ s) = u ∘ s := rfl
    have er : Sum.elim u v ∘ (Sum.inr ∘ s) = v ∘ s := rfl
    rw [el, er] at hm
    rw [hm, hv_side, hchain, ← hu_side (Equiv.swap a b ∘ s), neg_neg]
  have hmono : ∀ s : Fin n → κ,
      L (∏ i, X (Equiv.swap a b (s i))) = - L (∏ i, X (s i)) := by
    intro s
    have hμR : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ
    have h1 := hmix (Sum.inl ∘ s)
    have h2 := hmix (Sum.inl ∘ (Equiv.swap a b ∘ s))
    have el : Sum.elim u v ∘ (Sum.inl ∘ s) = u ∘ s := rfl
    have el' : Sum.elim u v ∘ (Sum.inl ∘ (Equiv.swap a b ∘ s)) = u ∘ Equiv.swap a b ∘ s := rfl
    rw [el] at h1
    rw [el', hkey] at h2
    simp only [Function.comp_apply, Sum.elim_inl, id] at h1 h2
    apply mul_left_cancel₀ hμR
    rw [← h2, mul_neg, ← h1]
    push_cast
    ring
  have hlin : L ∘ₗ (rename (Equiv.swap a b) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial κ ℝ).toLinearMap = -L := by
    refine (basisMonomials κ ℝ).ext fun m => ?_
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.neg_apply]
    by_cases hm : m.degree = n
    · obtain ⟨s, hs⟩ := exists_fin_sum_single_eq_of_degree_eq n m hm
      have e1 : monomial m (1 : ℝ) = ∏ i, X (s i) := by
        rw [← hs, monomial_sum_one]
        rfl
      rw [e1, map_prod]
      simp only [rename_X]
      exact hmono s
    · rw [hL _ _ (isHomogeneous_monomial (1 : ℝ) rfl) hm,
        hL _ _ (isHomogeneous_monomial (1 : ℝ) rfl).rename_isHomogeneous hm, neg_zero]
  intro Q
  exact LinearMap.congr_fun hlin Q

end GlobalTheory.FlagPush.MultiLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAntisymmOfDoublePointSymmMultilinearStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_antisymm_of_doublePoint_symmMultilinear : ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (A : Type) [AddCommGroup A] (n : ℕ) (T : (Fin (n + 1) → A) →ₘₗ[ℤ] ℤ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1) → A), T (y ∘ σ) = T y) → ∀ (u v : κ → A) (L : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (μ : ℤ), μ ≠ 0 → (∀ x, x ≠ a → x ≠ b → u x = v x) → u a + u b = v a + v b → (∀ s : Fin (n + 1) → κ, T (u ∘ s) = 0) → (∀ s : Fin (n + 1) → κ, T (v ∘ s) = 0) → (∀ (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ n → L P = 0) → (∀ s : Fin n → κ ⊕ κ, ((T (Fin.cons (v b - u a) (Sum.elim u v ∘ s)) : ℤ) : ℝ) = μ * L (∏ i, X (Sum.elim id id (s i)))) → ∀ Q : MvPolynomial κ ℝ, L (rename (Equiv.swap a b) Q) = - L Q := by
  exact GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSwapOfDoubleSpace
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Dbl

theorem interPoly_rename_swap : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (gr : κ → Y.Dv) (D₁ D₂ : κ → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ a → x ≠ b → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ a) + toPic (D₁ b) = toPic (D₂ a) + toPic (D₂ b) ∧ toPic Θ = toPic (D₂ b) - toPic (D₁ a) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ → ∀ Q : MvPolynomial κ ℝ, Y.interPoly gr (rename (Equiv.swap a b) Q) = - Y.interPoly gr Q := by
  intro F _ Y W hW κ a b hab gr D₁ D₂ Θ ⟨h₁, h₂, hx, hsum, hΘ, hE, hS⟩
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.T.exists_intersectionForm_picard_doubleSpace F Y W hW
  obtain ⟨μ, hμ, hc⟩ := GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section F Y W hW Θ hE hS
  let N : AddSubgroup (CartierDiv W.Z) := (toPic (X := W.Z)).ker
  let π : CartierDiv W.Z →+ CartierDiv W.Z ⧸ N := QuotientAddGroup.mk' N
  let φ : (CartierDiv W.Z ⧸ N) →+ Pic W.Z := QuotientAddGroup.kerLift toPic
  have hφ : Function.Injective φ := QuotientAddGroup.kerLift_injective _
  have hπ (D : CartierDiv W.Z) : φ (π D) = toPic D := rfl
  let T' : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => CartierDiv W.Z ⧸ N) ℤ :=
    T.compLinearMap fun _ => φ.toIntLinearMap
  have hT' (y : Fin (Y.dim + 1) → CartierDiv W.Z) : T' (fun i => π (y i)) = W.num y := hT y
  refine GlobalTheory.T.linearForm_antisymm_of_doublePoint_symmMultilinear κ a b hab (CartierDiv W.Z ⧸ N) Y.dim T' (fun σ y => hTs σ fun i => φ (y i))
    (fun x => π (D₁ x)) (fun x => π (D₂ x))
    (Y.interPoly gr) μ hμ (fun x ha hb => hφ (hx x ha hb)) (hφ ?_) (fun s => ?_) (fun s => ?_)
    (fun k P hP hk => GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim F Y κ gr k P hP hk) (fun s => ?_)
  · simpa only [map_add (f := _), hπ] using hsum
  · exact (hT' (fun i => D₁ (s i))).trans
      (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₁ _ (fun i => gr (s i)) fun i => h₁ (s i))
  · exact (hT' (fun i => D₂ (s i))).trans
      (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₂ _ (fun i => gr (s i)) fun i => h₂ (s i))
  · have hΘ' : π (D₂ b) - π (D₁ a) = π Θ := hφ (by simp only [map_sub, hπ, hΘ])
    have e : (Fin.cons (π (D₂ b) - π (D₁ a))
        (Sum.elim (fun x => π (D₁ x)) (fun x => π (D₂ x)) ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z ⧸ N) =
        fun i => π ((Fin.cons Θ (Sum.elim D₁ D₂ ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z) i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, hΘ']
      · simp only [Fin.cons_succ, Function.comp_apply]
        cases s j <;> rfl
    have r := GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base F Y W (Sum.elim D₁ D₂ ∘ s) (gr ∘ fun i => Sum.elim id id (s i)) fun i => by
      simp only [Function.comp_apply]
      cases s i with
      | inl x => exact Or.inl (h₁ x)
      | inr x => exact Or.inr (h₂ x)
    rw [e, hT', hc, r, Var.interPoly_prod]
    push_cast
    rfl

end GlobalTheory.FlagPush.Dbl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSwapOfDoubleSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_swap_of_doubleSpace : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (gr : κ → Y.Dv) (D₁ D₂ : κ → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ a → x ≠ b → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ a) + toPic (D₁ b) = toPic (D₂ a) + toPic (D₂ b) ∧ toPic Θ = toPic (D₂ b) - toPic (D₁ a) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ → ∀ Q : MvPolynomial κ ℝ, Y.interPoly gr (rename (Equiv.swap a b) Q) = - Y.interPoly gr Q := by
  first | exact @GlobalTheory.FlagPush.Dbl.interPoly_rename_swap | exact GlobalTheory.FlagPush.Dbl.interPoly_rename_swap | (intros; apply GlobalTheory.FlagPush.Dbl.interPoly_rename_swap <;> assumption)
end
