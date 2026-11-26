module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutation
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem mem_range_of_tmul_eq {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (x : Ω)
    (h : x ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] x) : x ∈ (algebraMap L Ω).range := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap L Ω).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  let m : Ω ⊗[L] Ω →ₗ[L] Ω := TensorProduct.lid L Ω ∘ₗ TensorProduct.map g LinearMap.id
  have e := congrArg m h
  simp only [m, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, hg1,
    one_smul, LinearEquiv.coe_coe] at e
  exact ⟨g x, by rw [Algebra.algebraMap_eq_smul_one]; exact e⟩

theorem factor_of_epi {O F Ω₀ Ω : Type} [CommRing O] [Field F] [Field Ω₀] [Field Ω]
    (β : O →+* F) (hβ : Epi (CommRingCat.ofHom β)) (a : O →+* Ω₀) (fn : Ω₀ →+* Ω) (cst : F →+* Ω)
    (h : fn.comp a = cst.comp β) : ∃ a' : F →+* Ω₀, a'.comp β = a := by
  let _ := fn.toAlgebra
  have e : CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[Ω₀] Ω).comp cst) =
      CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Ω →ₐ[Ω₀] Ω ⊗[Ω₀] Ω).toRingHom.comp cst) := by
    ext o
    have ho : cst (β o) = algebraMap Ω₀ Ω (a o) := by
      rw [RingHom.algebraMap_toAlgebra]; exact (RingHom.congr_fun h o).symm
    change cst (β o) ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst (β o)
    rw [ho, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have e2 := hβ.left_cancellation _ _ e
  have key : ∀ u : F, ∃ w : Ω₀, fn w = cst u := by
    intro u
    have hu := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e2) u
    change cst u ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst u at hu
    obtain ⟨w, hw⟩ := mem_range_of_tmul_eq (L := Ω₀) (cst u) hu
    exact ⟨w, by rw [← hw, RingHom.algebraMap_toAlgebra]⟩
  choose g hg using key
  have inj := fn.injective
  refine ⟨{ toFun := g
            map_one' := inj (by rw [hg, map_one, map_one])
            map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := inj (by rw [hg, map_zero, map_zero])
            map_add' := fun x y => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }, ?_⟩
  ext o
  apply inj
  change fn (g (β o)) = fn (a o)
  rw [hg]
  exact (RingHom.congr_fun h o).symm

theorem eq_genPt_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hf : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)
  have : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, rfl⟩ := this
  let _ := hf.toField
  have : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum _) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

theorem mem_of_dense_of_noGen {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  classical
  have hCi : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent y) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη : hCi.genericPoint = y := hy _ (hgen.specializes mem_irreducibleComponent)
  rw [hη] at hgen
  have hmax := irreducibleComponent_mem_irreducibleComponents y
  set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD
  have hDc : IsClosed D := by
    rw [hD, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hyD : y ∉ D := by
    rintro ⟨C, ⟨hC, hne⟩, hyC⟩
    have hle : irreducibleComponent y ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)
    exact hne (le_antisymm (hmax.2 hC.1 hle) hle)
  obtain ⟨u, huD, huU⟩ := hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩
  have huC : u ∈ irreducibleComponent y := by
    by_contra hne
    refine huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩,
      mem_irreducibleComponent⟩
    intro e
    exact hne (by
      have : u ∈ irreducibleComponent u := mem_irreducibleComponent
      rw [Set.mem_singleton_iff.1 e] at this
      exact this)
  exact (hgen.specializes huC).mem_open hU huU

theorem noetherianSpace_baseChange {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

theorem gen_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y),
    Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A hmono
  have hepi : Epi (CommRingCat.ofHom β) := by
    have h1 : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := hmono
    have h2 : Mono (CommRingCat.ofHom β).op := Scheme.Spec.mono_of_mono_map h1
    exact unop_epi_of_mono (CommRingCat.ofHom β).op
  let a : O →+* A.Ω₀ := (Spec.preimage (A.ξ₀ ≫ Y.s)).hom
  have ha : spMap a = A.ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : A.fn.comp a = A.cst.comp β := by
    have h1 : spMap (A.fn.comp a) = spMap (A.cst.comp β) := by
      rw [← A.cst_over]
      have hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
      calc spMap (A.fn.comp a) = spMap A.fn ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd, Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨a', ha'⟩ := factor_of_epi β hepi a A.fn A.cst hfa
  have hsq : A.ξ₀ ≫ Y.s = spMap a' ≫ spMap β := by
    rw [← ha, ← ha']
    simp only [spMap, ← Spec.map_comp]; rfl
  let z : Sp A.Ω₀ ⟶ pullback Y.s (spMap β) := pullback.lift A.ξ₀ (spMap a') hsq
  have hz : z ≫ pullback.fst _ _ = A.ξ₀ := pullback.lift_fst _ _ _
  let y0 : ↥(pullback Y.s (spMap β)) := z (IsLocalRing.closedPoint A.Ω₀)
  have hfst : pullback.fst Y.s (spMap β) y0 = genPt A.ξ₀ := by
    show (pullback.fst Y.s (spMap β)) (z _) = A.ξ₀ _
    rw [← hz]
    rfl
  have hmax : ∀ y', y' ⤳ y0 → y' = y0 := by
    intro y' hy
    have h1 : pullback.fst Y.s (spMap β) y' ⤳ genPt A.ξ₀ := hfst ▸ hy.map (pullback.fst Y.s (spMap β)).continuous
    have h2 := eq_genPt_of_specializes A.ξ₀ A.gen₀ _ h1
    exact (pullback.fst Y.s (spMap β)).injective (h2.trans hfst.symm)
  have := noetherianSpace_baseChange Y.proj β
  have := Y.jQ_open
  have hy0 : y0 ∈ Set.range Y.jQ :=
    mem_of_dense_of_noGen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hmax
  have hrange : Set.range z ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint A.Ω₀ := Subsingleton.elim (α := PrimeSpectrum A.Ω₀) _ _
    rw [this]
    exact hy0
  refine ⟨IsOpenImmersion.lift Y.jQ z hrange, ?_⟩
  show A.ξ₀ = IsOpenImmersion.lift Y.jQ z hrange ≫ Y.jQ ≫ pullback.fst _ _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hz]

end GlobalTheory.CompanionTheory.Ar.GenOpen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_factor_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y), Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open | exact GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open | (intros; apply GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEval
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEval
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

section

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem antisymDegree_eq_dimFl' : GroundTheory.Heights₂.Heights.antisymDegree Ψ N = dimFl Ψ N := by
  simp [GroundTheory.Heights₂.Heights.antisymDegree, dimFl, Nat.choose_two_right]

theorem flMonoLines_eq (m : Ψ × Fin N →₀ ℕ) (d : ℕ) (hm : m.degree = d) :
    GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines Ψ N m d =
      monoLines (GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N) m d := by
  funext k
  have hl : (Finsupp.toMultiset m).toList.length = d := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hm]
    rfl
  have hk : (k : ℕ) < (Finsupp.toMultiset m).toList.length := by
    rw [hl]
    exact k.2
  simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines, monoLines, dif_pos hk]

theorem linRoot_pow_eq (lam : Wt Ψ N) (n : ℕ) :
    linRoot lam ^ n = ((-1 : ℝ) ^ n) •
      ∏ _k : Fin n, ∑ x : Ψ × Fin N, C (lam x.1 x.2) * X x := by
  rw [linRoot, neg_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_C_mul, map_pow, map_neg, map_one]

end

theorem hhFl_linRoot_pow : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) = eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := by
  intro II hII Ψ _ _ N _ lam _ hP
  have hword : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N,
      hhFl Ψ N II (monomial (∑ k, Finsupp.single (w k) 1) 1) = (-1 : ℝ) ^ (dimFl Ψ N + 1) *
        II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
          (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
          (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) := by
    intro w
    obtain ⟨hdeg, σ, -, hI⟩ := GlobalTheory.T.monomial_lines_permutation II hII.1 _ _ (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
      _ (GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N) w hP
      (fun j => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
    have hdeg' : (∑ k, Finsupp.single (w k) 1 : Ψ × Fin N →₀ ℕ).degree =
        GroundTheory.Heights₂.Heights.LowerBoundFree.dimFl Ψ N + 1 := hdeg
    have e1 : II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines Ψ N (∑ k, Finsupp.single (w k) 1) (dimFl Ψ N + 1)) =
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) := by
      rw [flMonoLines_eq _ _ hdeg]
      exact hI
    rw [HhModel.hhFl_monomial, GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono, if_pos hdeg', hdeg, one_mul]
    exact congrArg (fun t => (-1 : ℝ) ^ (dimFl Ψ N + 1) * t) e1
  have hpoly : PB.hFlPoly Ψ N II = PB.formPoly (dimFl Ψ N + 1) fun w =>
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) := by
    rw [PB.hFlPoly, antisymDegree_eq_dimFl']
  rw [linRoot_pow_eq, map_smul, GlobalTheory.T.functional_product_linear_forms _ _ (hhFl Ψ N II) (fun _ x => lam x.1 x.2), hpoly,
    (PB.formPoly_isHomogeneous_and_eval (Ψ × Fin N) (dimFl Ψ N + 1) _).2]
  simp only [hword, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : ((-1 : ℝ) ^ (dimFl Ψ N + 1)) * (-1 : ℝ) ^ (dimFl Ψ N + 1) = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (∏ k, lam (w k).1 (w k).2) *
    II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
      (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
      (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) * h2

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEvalStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_polynomial_eval : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) = eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow <;> assumption)
end
end
