module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionNonvanishingOfBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionNonvanishingOfBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.FieldDescent

open scoped TensorProduct


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC in
theorem exists_sec_of_pull {F E : Type} [Field F] [Field E] [Algebra F E] {Y X : Scheme.{0}}
    {p : Y ⟶ Sp F} {q : X ⟶ Sp E} {π : X ⟶ Y} (H : IsPullback π q p (spMap (algebraMap F E)))
    [CompactSpace Y] [Y.IsSeparated] {N : LB Y} (hN : N.IsLB) (σ : (N.pull π).Sec) (x : X)
    (hx : x ∈ nonzeroLocus σ) : ∃ θ : N.Sec, π x ∈ nonzeroLocus θ := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover N hN
  letI instV : ∀ a, Algebra F Γ(Y, V a) := fun a => (algX p (V a)).toAlgebra
  letI instW : ∀ ab : Fin n × Fin n, Algebra F Γ(Y, V ab.1 ⊓ V ab.2) := fun ab => (algX p _).toAlgebra
  let δ : (∀ a, Γ(Y, V a)) →ₗ[F] (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) :=
    { toFun := fun f ab => dfun N V c hVc f ab.1 ab.2
      map_add' := fun f g => by
        funext ab
        simp only [dfun, Pi.add_apply, map_add (f := _), mul_add]
        abel
      map_smul' := fun r f => by
        funext ab
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun N V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext a b; exact congrFun h (a, b)
    · intro h; funext ab; exact congrFun (congrFun h ab.1) ab.2
  have hV'c : ∀ a, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ ≤ (N.pull π).U (fun _ => c a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hVc a hy.1
  let m' : ∀ a, Γ(X, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤) := fun a => ReciprocityTheory.ChartRestriction.G.DVR.rs (hV'c a) (σ.f (fun _ => c a))
  let t : (∀ a, Γ(Y, V a)) ⊗[F] E := (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))).symm
    (fun a => (eTens p q π H (V a) (hVa a)).symm (m' a))
  have hpt : ∀ a, (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))) t a =
      (eTens p q π H (V a) (hVa a)).symm (m' a) := fun a => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor E t = 0 := by
    apply (TensorProduct.piLeft (R := F) (N := E) (M := fun ab : Fin n × Fin n => Γ(Y, V ab.1 ⊓ V ab.2))).injective
    rw [map_zero]
    funext ab
    obtain ⟨a, b⟩ := ab
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (a, b) : (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) →ₗ[F] _).comp δ =
        (rsL p (V a) (V a ⊓ V b) inf_le_left).comp (LinearMap.proj a) -
          (mulL p (V a ⊓ V b) (ReciprocityTheory.ChartRestriction.G.Semi.res (pair_le N V c hVc a b) (N.g (c a) (c b))).val).comp
            ((rsL p (V b) (V a ⊓ V b) inf_le_right).comp (LinearMap.proj b)) := by
      ext f; rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p q π H (V a ⊓ V b) ((hVa a).inf (hVa b))).injective
    rw [map_sub, eTens_rs p q π H (V a) (V a ⊓ V b) (hVa a) _ inf_le_left, eTens_mul,
      eTens_rs p q π H (V b) (V a ⊓ V b) (hVa b) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (N.pull π).U (fun _ => c a) := Set.mem_iInter.2 fun _ => hVc a hy.1.1
    have hyl : y ∈ (N.pull π).U (fun _ => c b) := Set.mem_iInter.2 fun _ => hVc b hy.1.2
    have hyk' : y ∈ π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ π ⁻¹ᵁ V b ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : π y ∈ V a ⊓ V b := hy.1
    simp only [m']
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_mul _ y _ hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyk', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyl', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ y _ hφy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (N.pull π) σ (fun _ => c a) (fun _ => c b) y hyk hyl,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g N π (𝟙 _) y (fun _ => c a) (fun _ => c b) hyk hyl, Category.id_comp]
  let b := Module.Basis.ofVectorSpace F E
  let e₁ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ a, Γ(Y, V a)) b
  let e₂ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) b
  have nat : ∀ u β, e₂ (δ.rTensor E u) β = δ (e₁ u β) := by
    intro u β
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m a =>
      simp only [LinearMap.rTensor_tmul, e₁, e₂, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
        Finsupp.mapRange_apply, map_smul]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  have hβ : ∀ β, dfun N V c hVc (e₁ t β) = 0 := fun β =>
    (hδ _).1 (by rw [← nat, ht, map_zero, Finsupp.zero_apply])
  choose θ hθ using fun β => exists_glue N V c hVc hN hcov (e₁ t β) (hβ β)
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj⟩ : ∃ j, π x ∈ V j := TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  have hxj : x ∈ π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤ := ⟨hj, trivial⟩
  have hxc : x ∈ (N.pull π).U (fun _ => c j) := hV'c j hxj
  have hu := (mem_nonzeroLocus_iff_isUnit σ hxc).1 hx
  rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res (𝟙 X) x (hV'c j) hxj] at hu
  change IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j)) at hu
  have hexp : t = (e₁ t).sum fun β m => m ⊗ₜ[F] b β := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : m' j = (e₁ t).sum fun β m => (π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (m j) *
      algX q (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) (b β) := by
    have h1 := hpt j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hexp, piLeft_apply_eq, Finsupp.sum, map_sum] at h1
    simp only [LinearMap.rTensor_tmul, LinearMap.proj_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingEquiv.apply_symm_apply (eTens p q π H (V j) (hVa j)) (m' j), ← h1, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eTens_tmul]
  have key : ∀ β, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _
      ((π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (e₁ t β j)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun β => by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 X) x hxj, Category.id_comp, ← hθ β]
    simp only [ev]
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res π x (hVc j) hj, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← mem_nonzeroLocus_iff_pull (θ β) π x (hVc j hj)]
    exact hcon (θ β)
  have hmem : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, Finsupp.sum, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj, map_sum, map_sum]
    refine Ideal.sum_mem _ fun β _ => ?_
    rw [map_mul, map_mul, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj]
    exact Ideal.mul_mem_right _ _ (key β)
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

theorem exists_sec_tens_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  intro k E _ _ _ Y X p q π H hP L M hL hM x ⟨s, hs⟩
  have : IsProper p := CommonModel.isProper_of_isProjOver hP
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hN := isLB_tens hL hM
  have hNp := LB.isLB_pull hN π
  have hT := isLB_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π)
  have iso : LBIso ((tens L M).pull π) (tens (L.pull π) (M.pull π)) := by
    refine (cls_eq_iff hNp hT).1 ?_
    rw [cls_pull hN π hNp, cls_tens hL hM hN, map_add (f := _), cls_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π) hT,
      cls_pull hL π, cls_pull hM π]
  obtain ⟨s₂, hs₂⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hNp hT iso s
  exact exists_sec_of_pull H hN s₂ x (hs₂ ▸ hs)

end GlobalTheory.FieldDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionNonvanishingOfBaseChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange | exact GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange | (intros; apply GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPointSpecializesInOpenOfFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPointSpecializesInOpenOfFiniteType
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem closedPoint_specializing_in_open : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  intro k _ X q _ U y hy
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  have hne : (closure ({y} : Set X) ∩ (U : Set X)).Nonempty := ⟨y, subset_closure rfl, hy⟩
  have hlc : IsLocallyClosed (closure ({y} : Set X) ∩ (U : Set X)) :=
    ⟨U, closure {y}, U.isOpen, isClosed_closure, Set.inter_comm _ _⟩
  obtain ⟨x, ⟨hxc, hxU⟩, hx⟩ := nonempty_inter_closedPoints hne hlc
  exact ⟨x, (mem_closedPoints_iff).1 hx, specializes_iff_mem_closure.2 hxc, hxU⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPointSpecializesInOpenOfFiniteTypeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  first | exact @GlobalTheory.closedPoint_specializing_in_open | exact GlobalTheory.closedPoint_specializing_in_open | (intros; apply GlobalTheory.closedPoint_specializing_in_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.EffGen

theorem core_gen (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] (hq : IsProjOver q) (hD : 1 ≤ D) :
    letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (N N' B : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : X),
      IsClosed ({x} : Set X) → IsNef ℂ N → IsBig ℂ N → IsNef ℂ N' → (D + 1).choose 2 < m →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed ℂ Z (fun _ : Fin e => N)) →
      cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, x ∈ nonzeroLocus s := by
  letI := algebraΓOfHom q
  intro K N N' B hN hN' hB m x hx hNn hNb hN'n hm hpos hBc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul hNN ℂ X q hq N N' hN hN' (2 * m - 1) 2 hNn hNb hN'n (by omega)
  obtain ⟨m', D₀, U, hm', hD₀, hcur, hxU, hklt, hnk⟩ := GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective hK.2 X q D hq hD N₀ 2 x two_pos hn₀ hb₀ hx
    (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ hxZ he hdim
      have h2 := GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed hNN ℂ X q hq N N' N₀ hN hN' h₀ (2 * m - 1) 2 Z e hNn hN'n hc₀ hdim
      have h3 : ((2 * m - 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * m - 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * m - 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : ((((D + 1).choose 2 : ℕ) : ℝ) * 2) ^ e < ((2 * m - 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        have : (D + 1).choose 2 * 2 < 2 * m - 1 := by omega
        exact_mod_cast this
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)
  obtain ⟨J, hJ, hvan⟩ := GlobalTheory.NadelApp.nadel_canonical_add hK.1 X q D hq K B N hB D₀ m' 2 hm' two_pos hD₀ hNn hNb
    (fun C hC => by
      have e1 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq B N N' hB hN hN' m 1 C hC (by rw [hBc, one_smul])
      have e2 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq N₀ N N' h₀ hN hN' (2 * m - 1) 2 C hC hc₀
      have e3 := hcur C hC
      rw [e3, e1, e2]
      have : ((2 * m - 1 : ℕ) : ℚ) = 2 * m - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [this]
      ring)
  exact GlobalTheory.T.exists_section_nonvanishing_point ℂ X q hq (tens K.bundle B) (isLB_tens K.isLB hB) J x U hx hxU
    (fun y hy => by
      rw [hJ]
      constructor
      · intro h
        by_contra hne
        exact h (hklt y hy hne)
      · rintro rfl
        exact hnk) (hvan 1 one_pos)

theorem effective_generation : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  intro hK hNN F _ _ Y p D _ hproj hgc hD1
  letI := algebraΓOfHom p
  intro K N N' B hN hN' hB a m y hNn hN'n hm hdec hBc
  obtain ⟨N₁, N₂, h₁, h₂, ha, hcls, hamp, hN₂⟩ := hdec
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  let σ : F →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := F)).toRingHom
  letI : Algebra F ℂ := σ.toAlgebra
  let π := pullback.fst p (spMap (algebraMap F ℂ))
  let q := pullback.snd p (spMap (algebraMap F ℂ))
  have H : IsPullback π q p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hXi, hXn, hsm, hqp, hsurj⟩ := GlobalTheory.T.baseChange_smooth_projective_variety_properties F ℂ Y _ p q π D H hproj hgc
  haveI := hXi; haveI := hXn; haveI := hsm
  letI := algebraΓOfHom q
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  obtain ⟨y', rfl⟩ := hsurj y
  haveI : Smooth q := SmoothOfRelativeDimension.smooth D q
  obtain ⟨m₁, A, s₁, hm₁, hA, hAa, hy⟩ := hamp
  obtain ⟨x, hxc, hyx, hxU⟩ := GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType ℂ _ q (π ⁻¹ᵁ nonzeroLocus s₁) y' hy
  have hAx : AmpleAt (N₁.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine Y _ π N₁ h₁ x ⟨m₁, A, s₁, hm₁, hA, hAa, hxU⟩
  have hNnC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N hNn
  have hN'nC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N' hN'n
  have hN₂C := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N₂ hN₂
  have hc : a • cls (N.pull π) (pull_isLB hN π) = cls (N₁.pull π) (pull_isLB h₁ π) + cls (N₂.pull π) (pull_isLB h₂ π) := by
    rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add (f := _)]
  have hbig := GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hcB : cls (B.pull π) (pull_isLB hB π) = m • cls (N.pull π) (pull_isLB hN π) + cls (N'.pull π) (pull_isLB hN' π) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add (f := _), map_nsmul]
  obtain ⟨s, hs⟩ := core_gen hK hNN _ q D hqp hD1 (CanonLB.baseChange H K) (N.pull π) (N'.pull π) (B.pull π)
    _ _ _ m x hxc hNnC hbig hN'nC hm hpos hcB
  exact GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange F ℂ Y _ p q π H hproj K.bundle B K.isLB hB y' ⟨s, hyx.mem_open (nonzeroLocus s).isOpen hs⟩

end GlobalTheory.EffGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effective_generation_canonical_nef_numberField : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.EffGen.effective_generation | exact GlobalTheory.EffGen.effective_generation | (intros; apply GlobalTheory.EffGen.effective_generation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCanonTensPullId
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModifRefl

theorem exists_sec_canon_tens_pull_id : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (𝟙 Y ≫ p)] (B : LB Y), B.IsLB → ∀ (s : H0 p (tens (CanonLB.all p D).bundle B) ⊤) (y : Y), y ∈ nonzeroLocus (toSec s) → ∃ s' : H0 (𝟙 Y ≫ p) (tens (CanonLB.all (𝟙 Y ≫ p) D).bundle (B.pull (𝟙 Y))) ⊤, y ∈ nonzeroLocus (toSec s') := by
  intro k _ Y p D _ inst2 B hB s y hy
  revert inst2
  generalize hq : 𝟙 Y ≫ p = q
  simp only [Category.id_comp] at hq
  subst hq
  intro inst2
  have hK : (CanonLB.all p D).bundle.IsLB := (CanonLB.all p D).isLB
  have hBp : (B.pull (𝟙 Y)).IsLB := LB.isLB_linComb hB _ _
  have H1 : LBIso (tens (B.pull (𝟙 Y)) (CanonLB.all p D).bundle) (tens B (CanonLB.all p D).bundle) :=
    GlobalTheory.CechPic.tens_congr_left hK (DescendedPrincipal.lbIso_pull_id hB)
  have H : LBIso (tens (CanonLB.all p D).bundle (B.pull (𝟙 Y))) (tens (CanonLB.all p D).bundle B) :=
    LBIso.trans (isLB_tens hK hBp) (isLB_tens hBp hK) (isLB_tens hK hB)
      (GlobalTheory.CechPic.tens_comm_iso hK hBp)
      (LBIso.trans (isLB_tens hBp hK) (isLB_tens hB hK) (isLB_tens hK hB) H1
        (GlobalTheory.CechPic.tens_comm_iso hB hK))
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_tens hK hBp) (isLB_tens hK hB) H (toSec s)
  refine ⟨H0.ofSec p ⊤ t, ?_⟩
  have e : toSec (H0.ofSec p ⊤ t) = t := by
    unfold toSec
    exact Equiv.ofBijective_symm_apply_apply _ _ _
  rw [e, ht]
  exact hy

end GlobalTheory.ModifRefl
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem gapGe_stdWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')

private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }

private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }

private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }

private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]

theorem cls_common_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih =>
    rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

end GlobalTheory.HSApp
