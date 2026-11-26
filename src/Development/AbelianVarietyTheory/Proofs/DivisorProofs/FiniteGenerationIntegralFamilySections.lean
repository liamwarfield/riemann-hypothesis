module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTarget
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetPowSmulMem
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FinitePowerAnnihilation

theorem exists_finset_pow_smul_mem {R A Rf Af : Type} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Af]
    [IsNoetherianRing R] [Algebra R A] [Algebra R Rf] (f : R) [IsLocalization.Away f Rf]
    (ψ : Rf →+* Af) (ρ : A →+* Af) (hc : ∀ a, ρ (algebraMap R A a) = ψ (algebraMap R Rf a))
    (hk : ∀ x, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0) (T : Set Af) (hT : T.Finite)
    (hI : ∀ y ∈ T, ψ.IsIntegralElem y) (M : Set A)
    (hM : ∀ x ∈ M, ρ x ∈ Subring.closure (Set.range ψ ∪ T)) :
    ∃ s : Finset A, (s : Set A) ⊆ M ∧ ∀ x ∈ M, ∃ n : ℕ, f ^ n • x ∈ Submodule.span R (s : Set A) := by
  classical
  letI : Algebra Rf Af := ψ.toAlgebra
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers f) Rf inferInstance
  have hfg : (Algebra.adjoin Rf T).toSubmodule.FG := fg_adjoin_of_finite hT hI
  have hle : Submodule.span Rf (ρ '' M) ≤ (Algebra.adjoin Rf T).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h := hM x hx
    have : Subring.closure (Set.range ψ ∪ T) ≤ (Algebra.adjoin Rf T).toSubring := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact (Algebra.adjoin Rf T).algebraMap_mem a
      · exact Algebra.subset_adjoin hy
    exact this h
  have hfg2 : (Submodule.span Rf (ρ '' M)).FG := hfg.of_le hle
  obtain ⟨u, hu, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg2
  obtain ⟨s, hs, hsu⟩ := Finset.subset_set_image_iff.1 hu
  refine ⟨s, hs, fun x hx => ?_⟩
  have hx1 : ρ x ∈ Submodule.span Rf (u : Set Af) := hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩
  have key : ∀ z ∈ Submodule.span Rf (u : Set Af), ∃ n : ℕ, ∃ w ∈ Submodule.span R (s : Set A),
      ρ w = ρ (algebraMap R A f) ^ n * z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rw [← hsu, Finset.coe_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨0, w, Submodule.subset_span hw, by simp⟩
    | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨m, v, hv, e'⟩ := hb
      refine ⟨n + m, f ^ m • w + f ^ n • v,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hv), ?_⟩
      simp only [Algebra.smul_def, map_add (f := _), map_mul, map_pow, e, e']
      ring
    | smul c a _ ha =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers f) c
      refine ⟨n + k, b • w, Submodule.smul_mem _ _ hw, ?_⟩
      have hb' : ψ c * ρ (algebraMap R A f) ^ k = ρ (algebraMap R A b) := by
        rw [hc, hc, ← map_pow, ← map_mul, ← map_pow]
        exact congrArg ψ hb
      have hs' : c • a = ψ c * a := rfl
      rw [Algebra.smul_def, map_mul, e, ← hb', hs']
      ring
  obtain ⟨n, w, hw, e⟩ := key _ hx1
  obtain ⟨m, hm⟩ := hk (f ^ n • x - w) (by rw [map_sub, e, Algebra.smul_def, map_mul, map_pow, map_pow, sub_self])
  refine ⟨m + n, ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hm
  rw [hm]
  exact Submodule.smul_mem _ _ hw

theorem pow_mul_eq_zero_of_res {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (W : S.Opens) (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ W)) (hx : resK gp (S.basicOpen_le f) x = 0) :
    ∃ n : ℕ, (gp.app W).hom f ^ n * x = 0 := by
  have hc : IsCompact ((gp ⁻¹ᵁ W : (Sp K).Opens) : Set (Sp K)) :=
    (Set.subsingleton_of_subsingleton (α := PrimeSpectrum K)).isCompact
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (Sp K) hc x ((gp.app W).hom f) ?_
  have e : (Sp K).basicOpen ((gp.app W).hom f) ≤ gp ⁻¹ᵁ S.basicOpen f := (Scheme.preimage_basicOpen gp f).ge
  have h := congrArg ((Sp K).presheaf.map (homOfLE e).op).hom hx
  rw [map_zero, resK, ← CommRingCat.comp_apply, ← Functor.map_comp] at h
  exact h

theorem finFam_finite {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ}
    (V : Fin r → S.Opens) (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (hV : ⨆ i, V i = ⊤)
    (ht : ∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) (W : S.Opens) (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  classical
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra Γ(S, W) Γ(Sp K, gp ⁻¹ᵁ W) := (gp.app W).hom.toAlgebra
  have loc : ∀ f : Γ(S, W), (∃ i, S.basicOpen f ≤ V i) → ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W),
      (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) ⊆ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)) ∧
      ∀ x ∈ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)), ∃ n : ℕ,
        f ^ n • x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
    rintro f ⟨i, hi⟩
    haveI := hW.isLocalization_basicOpen f
    refine exists_finset_pow_smul_mem (Rf := Γ(S, S.basicOpen f)) f (gp.app (S.basicOpen f)).hom
      (resK gp (S.basicOpen_le f)) (fun a => resK_app gp _ a) ?_ (resK gp hi '' (t i : Set _))
      ((t i).finite_toSet.image _) ?_ _ ?_
    · intro x hx
      obtain ⟨n, hn⟩ := pow_mul_eq_zero_of_res gp W f x hx
      exact ⟨n, by rw [Algebra.smul_def, map_pow]; exact hn⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hp0⟩ := ht i y hy
      refine ⟨p.map (S.presheaf.map (homOfLE hi).op).hom, hp.map _, ?_⟩
      have e : (gp.app (S.basicOpen f)).hom.comp (S.presheaf.map (homOfLE hi).op).hom =
          (resK gp hi).comp (gp.app (V i)).hom := RingHom.ext fun a => (resK_app gp hi a).symm
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hp0, map_zero]
    · intro x hx
      have hii : S.basicOpen f ≤ W ⊓ V i := le_inf (S.basicOpen_le f) hi
      have h1 := (mem_finFam gp V t W x).1 hx i
      have hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii) :=
        ⟨_, h1, rfl⟩
      rw [RingHom.map_closure, resK_resK] at hm
      refine Subring.closure_mono ?_ hm
      rintro _ ⟨y, ⟨a, rfl⟩ | ⟨z, hz, rfl⟩, rfl⟩
      · exact Or.inl ⟨_, (resK_app gp hii a).symm⟩
      · exact Or.inr ⟨z, hz, by rw [resK_resK]⟩
  have hspan : Ideal.span {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i} = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    have hx2 : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx2
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩
  obtain ⟨F, hF, hFs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i}).1
    (IsNoetherian.noetherian (R := Γ(S, W)) _)
  have hF1 : Ideal.span (F : Set Γ(S, W)) = ⊤ := hFs.symm.trans hspan
  choose σ hσ using loc
  let s : Finset Γ(Sp K, gp ⁻¹ᵁ W) := F.attach.biUnion fun f => σ f.1 (hF f.2)
  refine ⟨s, fun y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.1 hy
    exact (hσ f.1 (hF f.2)).1 hf
  · have hxs : x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
      refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (F : Set Γ(S, W)) hF1 x fun f => ?_
      obtain ⟨n, hn⟩ := (hσ f.1 (hF f.2)).2 x hx
      refine ⟨n, Submodule.span_mono ?_ hn⟩
      intro y hy
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨f.1, f.2⟩, Finset.mem_attach _ _, hy⟩)
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset.1 hxs
    exact ⟨c, hc.2.symm⟩

end GlobalTheory.FinitePowerAnnihilation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem finFam_finite : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)), (⨆ i, V i) = ⊤ →
    (∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) → ∀ W : S.Opens, IsAffineOpen W →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  first
  | exact @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | (apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite ..)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_generation_integral_family_sections : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)), (⨆ i, V i) = ⊤ →
    (∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) → ∀ W : S.Opens, IsAffineOpen W →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  first | exact @GlobalTheory.Mum.finFam_finite | exact GlobalTheory.Mum.finFam_finite | (intros; apply GlobalTheory.Mum.finFam_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSigmaStableSummandFromLiftedEigenCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem eqLift_tensorModOf : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  intro C _ I A _ H _ _ σ hproj χ l₀ hl₀
  letI mH : Module (C ⊗[ℤ] A) H := GlobalTheory.HTSummand.tensorModOf σ
  let χt : C ⊗[ℤ] A →ₐ[ℤ] C := Algebra.TensorProduct.productMap (AlgHom.id ℤ C) χ.toIntAlgHom
  have hχt : ∀ (r : C) (a : A), χt (r ⊗ₜ[ℤ] a) = r * χ a := fun r a => by
    simp [χt, Algebra.TensorProduct.productMap_apply_tmul]
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hproj
  have hsx : ∀ x, (s x).sum (fun y c => c • y) = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [Finsupp.linearCombination_apply] using this
  let g : H → C := fun y => Function.surjInv Ideal.Quotient.mk_surjective (l₀ y)
  have hg : ∀ y, Ideal.Quotient.mk I (g y) = l₀ y := fun y =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (l₀ y)
  let F : H → C := fun x => (s x).sum (fun y c => χt c * g y)
  have hadd : ∀ x x', F (x + x') = F x + F x' := by
    intro x x'
    simp only [F, map_add (f := _)]
    exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])
  have hS : ∀ (t : C ⊗[ℤ] A) x, F (t • x) = χt t * F x := by
    intro t x
    simp only [F, map_smul]
    rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
    simp [_root_.mul_assoc]
  have hr : ∀ (r : C) (x : H), r • x = ((r ⊗ₜ[ℤ] (1 : A) : C ⊗[ℤ] A) • x) := by
    intro r x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, map_one]
    rfl
  have ha : ∀ (a : A) (x : H), σ a x = ((1 ⊗ₜ[ℤ] a : C ⊗[ℤ] A) • x) := by
    intro a x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, one_smul]
  let l : H →ₗ[C] C :=
    { toFun := F
      map_add' := hadd
      map_smul' := by
        intro r x
        show F (r • x) = r * F x
        rw [hr, hS, hχt, map_one, _root_.mul_one] }
  have hl₀t : ∀ (t : C ⊗[ℤ] A) y, l₀ (t • y) = Ideal.Quotient.mk I (χt t) * l₀ y := by
    intro t y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [GlobalTheory.HTSummand.tensorModOf_tmul, l₀.map_smul, hl₀, hχt, map_mul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, _root_.mul_assoc]
    | add t t' h h' => rw [add_smul, map_add (f := _), h, h', map_add (f := _), map_add (f := _), add_mul]
  refine ⟨l, ?_, ?_⟩
  · intro a x
    show F (σ a x) = χ a * F x
    rw [ha, hS, hχt, _root_.one_mul]
  · intro x
    show Ideal.Quotient.mk I (F x) = l₀ x
    conv_rhs => rw [← hsx x]
    simp only [F, map_finsuppSum, map_mul, hg, hl₀t]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantLift_functional_quotient_projective : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  first | exact @GlobalTheory.eqLift_tensorModOf | exact GlobalTheory.eqLift_tensorModOf | (intros; apply GlobalTheory.eqLift_tensorModOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSigmaStableSummandFromLiftedEigenCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory.HTSummand


set_option maxHeartbeats 800000 in
theorem summand_of_liftedCoords : ∀ {C : Type} [CommRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F →
  ∀ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) →
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) →
    (∀ k, y k ∈ LinearMap.range π) → (∀ j k, ℓ j (y k) = if j = k then 1 else 0) →
  ∃ G₀ M₀ : Submodule C H, G₀ ⊓ M₀ = ⊥ ∧ G₀ ⊔ M₀ = LinearMap.range π ∧ (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) ∧
    G₀ ⊔ I • LinearMap.range π = F ⊓ LinearMap.range π ∧
    ∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀ := by
  intro C _ I hI A _ H _ _ σ hproj a χ π hπ hσπ F hIF n κ ℓ y hℓ hF hy hδ
  have hl : ∀ k, ∃ l : H →ₗ[C] C, (∀ c x, l (σ c x) = χ (κ k) c * l x) ∧
      ∀ x, Ideal.Quotient.mk I (l x) = ℓ k x :=
    fun k => GlobalTheory.T.exists_equivariantLift_functional_quotient_projective I σ hproj (χ (κ k)) (ℓ k) (hℓ k)
  choose l hlσ hlℓ using hl
  have hII : ∀ u v : C, u ∈ I → v ∈ I → u * v = 0 := by
    intro u v hu hv
    have h := Ideal.mul_mem_mul hu hv
    rw [← sq, hI] at h
    simpa using h
  have hσQ : ∀ c, ∀ x ∈ LinearMap.range π, σ c x ∈ LinearMap.range π := by
    rintro c _ ⟨z, rfl⟩
    refine ⟨σ c z, ?_⟩
    show (π * σ c) z = (σ c * π) z
    rw [hσπ]
  let e : Fin n → Fin n → C := fun j m => l j (y m) - if j = m then 1 else 0
  have he : ∀ j m, e j m ∈ I := by
    intro j m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [e, map_sub, hlℓ, hδ]
    split_ifs <;> simp
  let x : Fin n → H := fun k => y k - ∑ m, e m k • y m
  have hxQ : ∀ k, x k ∈ LinearMap.range π := fun k =>
    Submodule.sub_mem _ (hy k) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hy m))
  have hlx : ∀ j k, l j (x k) = if j = k then 1 else 0 := by
    intro j k
    have h1 : ∀ m, e m k * l j (y m) = if j = m then e m k else 0 := by
      intro m
      have h0 := hII _ _ (he m k) (he j m)
      rw [show l j (y m) = e j m + (if j = m then 1 else 0) by simp [e], mul_add, h0]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_ite_eq]
    simp [e]
  let G₀ : Submodule C H := LinearMap.range π ⊓ ⨅ k, LinearMap.ker (l k)
  have hG : ∀ z, z ∈ G₀ ↔ z ∈ LinearMap.range π ∧ ∀ k, l k z = 0 := by
    intro z
    simp only [G₀, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  have key : ∀ q ∈ LinearMap.range π, q - ∑ k, l k q • x k ∈ G₀ := by
    intro q hq
    refine (hG _).2 ⟨Submodule.sub_mem _ hq (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (hxQ k)), fun j => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hlx]
  refine ⟨G₀, Submodule.span C (Set.range x), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro z ⟨hzG, hzM⟩
    rw [Submodule.mem_bot]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hzM
    have hc : ∀ j, c j = 0 := fun j => by
      have h := ((hG _).1 hzG).2 j
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hlx] using h
    simp [hc]
  · refine le_antisymm (sup_le inf_le_left
      (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hxQ k))) ?_
    intro q hq
    rw [← sub_add_cancel q (∑ k, l k q • x k)]
    exact Submodule.add_mem_sup (key q hq) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · intro c z hz
    rw [hG] at hz ⊢
    exact ⟨hσQ c z hz.1, fun k => by rw [hlσ, hz.2, mul_zero]⟩
  · apply le_antisymm
    · refine sup_le ?_ (le_inf ((Submodule.smul_mono le_rfl le_top).trans hIF)
        Submodule.smul_le_right)
      intro z hz
      rw [hG] at hz
      exact ⟨(hF z hz.1).2 (fun k => by rw [← hlℓ, hz.2 k, map_zero]), hz.1⟩
    · rintro z ⟨hzF, hzQ⟩
      have hlI : ∀ k, l k z ∈ I := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hlℓ]
        exact (hF z hzQ).1 hzF k
      rw [← sub_add_cancel z (∑ k, l k z • x k)]
      exact Submodule.add_mem_sup (key z hzQ) (Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem_smul (hlI k) (hxQ k))
  · intro d hd
    have hv : ∀ c k, σ c (x k) - χ (κ k) c • x k ∈ G₀ := by
      intro c k
      refine (hG _).2 ⟨Submodule.sub_mem _ (hσQ c _ (hxQ k)) (Submodule.smul_mem _ _ (hxQ k)),
        fun j => ?_⟩
      rw [map_sub, hlσ, map_smul, hlx, smul_eq_mul]
      split_ifs with h
      · subst h; ring
      · simp
    refine ⟨fun i => ∑ k ∈ Finset.univ.filter (fun k => κ k = i), l k d • x k, ?_, ?_⟩
    · intro i c
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Submodule.sum_mem
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [← hk.2, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ (hv c k)
    · rw [Finset.sum_fiberwise]
      exact key d hd

end GlobalTheory.HTSummand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSigmaStableSummandFromLiftedEigenCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sigmaStable_summand_from_lifted_eigenCoords : ∀ {C : Type} [CommRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F →
  ∀ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) →
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) →
    (∀ k, y k ∈ LinearMap.range π) → (∀ j k, ℓ j (y k) = if j = k then 1 else 0) →
  ∃ G₀ M₀ : Submodule C H, G₀ ⊓ M₀ = ⊥ ∧ G₀ ⊔ M₀ = LinearMap.range π ∧ (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) ∧
    G₀ ⊔ I • LinearMap.range π = F ⊓ LinearMap.range π ∧
    ∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀ := by
  first | exact @GlobalTheory.HTSummand.summand_of_liftedCoords | exact GlobalTheory.HTSummand.summand_of_liftedCoords | (intros; apply GlobalTheory.HTSummand.summand_of_liftedCoords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubscheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_opens_preimage_le_of_isClosedMap {F Y : Scheme.{0}} (φ : F ⟶ Y) (hφ : IsClosedMap φ) (y : Y)
    (T : F.Opens) (hT : ∀ p, φ p = y → p ∈ T) : ∃ N : Y.Opens, y ∈ N ∧ φ ⁻¹ᵁ N ≤ T := by
  refine ⟨⟨(φ '' (T : Set F)ᶜ)ᶜ, (hφ _ T.2.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, e⟩
    exact hp (hT p e)
  · intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩

theorem exists_basicOpen_le_of_finite {A : Type} [CommRing A] (s : Set (PrimeSpectrum A)) (hs : s.Finite)
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ b : A, s ⊆ PrimeSpectrum.basicOpen b ∧ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum A)) ⊆ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  by_cases hne : s = ∅
  · subst hne
    exact ⟨0, by simp, by simp⟩
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
  have key : ¬ ((I : Set A) ⊆ ⋃ i ∈ s, (i.asIdeal : Set A)) := by
    rw [Ideal.subset_union_prime_finite hs a a (fun i _ _ _ => i.2)]
    rintro ⟨i, hi, hle⟩
    have : i ∈ Uᶜ := by rw [hI]; exact hle
    exact this (hsU hi)
  obtain ⟨b, hb, hb'⟩ := Set.not_subset.1 key
  refine ⟨b, fun i hi h => hb' (Set.mem_iUnion₂.2 ⟨i, hi, h⟩), fun i hi => ?_⟩
  by_contra h
  have : i ∈ PrimeSpectrum.zeroLocus (I : Set A) := hI ▸ h
  exact hi (this hb)

theorem exists_basicOpen_le_of_finite' {G : Scheme.{0}} {W : G.Opens} (hW : IsAffineOpen W) (s : Set G) (hs : s.Finite)
    (hsW : s ⊆ W) (U : G.Opens) (hsU : s ⊆ U) : ∃ b : Γ(G, W), s ⊆ G.basicOpen b ∧ G.basicOpen b ≤ U := by
  obtain ⟨b, h₁, h₂⟩ := exists_basicOpen_le_of_finite (A := Γ(G, W)) (hW.fromSpec ⁻¹' s)
    (hs.preimage hW.fromSpec.isOpenEmbedding.injective.injOn) _
    (hW.fromSpec ⁻¹ᵁ U).2 (fun p hp => hsU hp)
  refine ⟨b, fun p hp => ?_, ?_⟩
  · have : p ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hsW hp
    obtain ⟨q, rfl⟩ := this
    rw [← hW.fromSpec_image_basicOpen]
    exact ⟨q, h₁ hp, rfl⟩
  · rw [← hW.fromSpec_image_basicOpen]
    rintro _ ⟨q, hq, rfl⟩
    exact h₂ hq

theorem exists_affine_preimage_eq_basicOpen {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {W : G.Opens} (hW : IsAffineOpen W) (y : Y) (hfin : (κ '' {p | φ p = y}).Finite)
    (hy : ∀ p, φ p = y → κ p ∈ W) :
    ∃ (O : Y.Opens) (b : Γ(G, W)), y ∈ O ∧ IsAffineOpen O ∧ φ ⁻¹ᵁ O = κ ⁻¹ᵁ G.basicOpen b := by
  obtain ⟨N, hyN, hN⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ W) hy
  obtain ⟨_, ⟨O₁, hO₁, rfl⟩, hyO₁, hO₁N⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyN N.2
  let U : G.Opens := ⟨(κ '' ((φ ⁻¹ᵁ O₁ : F.Opens) : Set F)ᶜ)ᶜ,
    (κ.isClosedEmbedding.isClosedMap _ (φ ⁻¹ᵁ O₁).2.isClosed_compl).isOpen_compl⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_basicOpen_le_of_finite' hW _ hfin (by rintro _ ⟨p, hp, rfl⟩; exact hy p hp) U (by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, e⟩
    obtain rfl := κ.isClosedEmbedding.injective e
    apply hq
    change φ q ∈ O₁
    rw [hp]; exact hyO₁)
  have hle : κ ⁻¹ᵁ G.basicOpen b₁ ≤ φ ⁻¹ᵁ O₁ := fun p hp => by
    by_contra h
    exact hb₁' hp ⟨p, h, rfl⟩
  obtain ⟨N₂, hyN₂, hN₂⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ G.basicOpen b₁)
    (fun p hp => hb₁ ⟨p, hp, rfl⟩)
  obtain ⟨g, hg, hyg⟩ := IsAffineOpen.exists_basicOpen_le hO₁ (V := N₂) ⟨y, hyN₂⟩ hyO₁
  have hS : IsAffineOpen (κ ⁻¹ᵁ W) := hW.preimage κ
  rw [Scheme.preimage_basicOpen] at hle hN₂
  obtain ⟨s, hs⟩ := hS.basicOpen_basicOpen_is_basicOpen (κ.app W b₁) (φ.appLE O₁ _ hle g)
  obtain ⟨b, rfl⟩ := κ.app_surjective W hW s
  refine ⟨Y.basicOpen g, b, hyg, hO₁.basicOpen g, ?_⟩
  rw [Scheme.preimage_basicOpen κ, hs, Scheme.basicOpen_appLE, eq_comm, inf_eq_right]
  exact fun p hp => hN₂ (hg hp)

theorem exists_affine_preimage_iff_not_mem {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {A : Type} [CommRing A] (J : Sp A ⟶ G) [IsOpenImmersion J] (y : Y)
    (hfin : (κ '' {p | φ p = y}).Finite) (hy : ∀ p, φ p = y → κ p ∈ Set.range J) :
    ∃ (O : Y.Opens) (b : A), y ∈ O ∧ IsAffineOpen O ∧
      ∀ p, φ p ∈ O ↔ ∃ q : PrimeSpectrum A, J q = κ p ∧ b ∉ q.asIdeal := by
  obtain ⟨O, b, h₁, h₂, h₃⟩ := exists_affine_preimage_eq_basicOpen κ φ hφ (isAffineOpen_opensRange J) y hfin hy
  have e : (⊤ : (Sp A).Opens) ≤ J ⁻¹ᵁ J.opensRange := fun q _ => ⟨q, rfl⟩
  refine ⟨O, (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b), h₁, h₂, fun p => ?_⟩
  have h₄ := basicOpen_eq_of_affine' (R := .of A) (J.appLE _ _ e b)
  rw [Scheme.basicOpen_appLE, top_inf_eq] at h₄
  have h₅ : ∀ q : PrimeSpectrum A, J q ∈ G.basicOpen b ↔
      (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b) ∉ q.asIdeal := fun q => by
    change q ∈ J ⁻¹ᵁ G.basicOpen b ↔ _
    rw [h₄]; rfl
  change p ∈ φ ⁻¹ᵁ O ↔ _
  rw [h₃]
  change κ p ∈ G.basicOpen b ↔ _
  constructor
  · intro h
    obtain ⟨q, hq⟩ := G.basicOpen_le b h
    exact ⟨q, hq, (h₅ q).1 (by rw [hq]; exact h)⟩
  · rintro ⟨q, hq, h⟩
    rw [← hq]; exact (h₅ q).2 h

theorem exists_act_eq_of_apply_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (hG : IsGal (algebraMap R R')) {F G T : Scheme.{0}} (t : T ⟶ Sp R')
    [IsClosedImmersion t] (κ : F ⟶ G) (gm : G ⟶ Sp R') (s : F ⟶ T) (hs : κ ≫ gm = s ≫ t)
    (act : Gal (algebraMap R R') → (G ⟶ G)) (hact : ∀ σ, act σ ≫ gm = gm ≫ spMap (Gal.hom σ)) (Y : Over (Sp R))
    (hY : Flat Y.hom) (φ : F ⟶ Y.left) (hφ : IsPullback φ s Y.hom (t ≫ spMap (algebraMap R R')))
    (hinv : ∀ σ, ∃ h : F ⟶ F, h ≫ κ = κ ≫ act σ ∧ h ≫ φ = φ) (p q : F) (e : φ p = φ q) :
    ∃ σ, act σ (κ p) = κ q := by
  let u : F ⟶ pullback Y.hom (spMap (algebraMap R R')) := pullback.lift φ (s ≫ t) (by rw [hφ.w, Category.assoc])
  have hu₁ : u ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd _ _ = s ≫ t := pullback.lift_snd _ _ _
  have hu : IsPullback s u t (pullback.snd Y.hom (spMap (algebraMap R R'))) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) ?_ hu₂.symm (IsPullback.of_hasPullback _ _).flip
    rw [hu₁]; exact hφ.flip
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hu inferInstance
  obtain ⟨σ, h, h₁, h₂, h₃⟩ := GlobalTheory.T.galois_transitive_on_fibres_flat_baseChange R R' hinj hG Y hY _ _ _ (IsPullback.of_hasPullback _ _) (u p) (u q) (by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hu₁, e])
  obtain ⟨k, k₁, k₂⟩ := hinv σ
  have hk : k ≫ u = u ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, hu₁, k₂]
    · rw [Category.assoc, Category.assoc, h₂, hu₂, ← Category.assoc u, hu₂, ← hs, ← Category.assoc k, k₁, Category.assoc,
        hact, Category.assoc]
  have hkp : k p = q := u.isClosedEmbedding.injective (by
    rw [← h₃, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk])
  exact ⟨σ, by rw [← hkp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, k₁]⟩

theorem mem_range_thick_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R')
    (hρ : ρ.Finite) (P : Sp R') (hP : spMap ρ P = closedPoint R) (e : ℕ) :
    P ∈ Set.range (thick R' (maximalIdeal R') e) := by
  have h₁ : (P.asIdeal.comap ρ).IsMaximal := by
    have : P.asIdeal.comap ρ = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hP
    rw [this]; infer_instance
  have := P.2
  have h₂ : P.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ h₁
  have h₃ : P.asIdeal = maximalIdeal R' := eq_maximalIdeal h₂
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R' ^ (e + 1))))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  intro a ha
  change a ∈ P.asIdeal
  rw [h₃]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e) ha

theorem exists_affine_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ x : H.toScheme, spMap (algebraMap R R') (G'.hom (H.ι x)) = closedPoint R → ∃ (V : X.left.Opens) (O : Y.left.Opens), π x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen O ∧ φ 0 ⁻¹ᵁ O = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ (H.ι ''ᵁ (π ⁻¹ᵁ V)) := by
  intro R _ _ _ R' _ _ _ _ hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec Y φ hY hφ _ hh x hx
  have := hG.1
  have := Fintype.ofFinite (Gal (algebraMap R R'))
  have hx₀ : H.ι x ∈ Set.range (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := by
    rw [Scheme.Pullback.range_fst]
    exact mem_range_thick_of_finite _ hF.2.2 _ hx 0
  obtain ⟨x₀, hx₀⟩ := hx₀
  have ht : IsClosedImmersion (thick R' (maximalIdeal R') 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hρ : IsFinite (spMap (algebraMap R R')) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hfin : IsFinite (φ 0) := MorphismProperty.of_isPullback (P := @IsFinite) (hφ 0).flip inferInstance
  have orb := exists_act_eq_of_apply_eq hF.2.1 hG (thick R' (maximalIdeal R') 0)
    (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) G'.hom _ pullback.condition act hact Y inferInstance (φ 0) (hφ 0) (hh 0)
  have hh₀ := hh 0
  have hκ : IsClosedImmersion (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := inferInstance
  generalize pullback.fst G'.hom (thick R' (maximalIdeal R') 0) = κ at *
  obtain ⟨_, ⟨V₁, hV₁, rfl⟩, hxV₁, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π x)) isOpen_univ
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlr, hpb, -, -, hcomm, -, hC⟩ :=
    GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants R R' hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec V₁ hV₁
  have lift : ∀ (z : H.toScheme) (w : Sp C), π z = l w → ∃ q : Sp C', j q = z ∧ spMap (algebraMap C C') q = w :=
    fun z w e => Scheme.exists_preimage_of_isPullback hpb z w e
  have hw : ∀ q, π (j q) = l (spMap (algebraMap C C') q) := fun q => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have hc : ∀ σ q, (j ≫ H.ι) (spMap (actC σ : C' →+* C') q) = act σ ((j ≫ H.ι) q) := fun σ q => by
    rw [← Scheme.Hom.comp_apply, hcomm, ← Scheme.Hom.comp_apply, Category.assoc]
  obtain ⟨w₀, hw₀⟩ : π x ∈ Set.range l := by rw [hlr]; exact hxV₁
  obtain ⟨q₀, hq₀, -⟩ := lift x w₀ hw₀.symm
  have hq₀' : (j ≫ H.ι) q₀ = κ x₀ := by rw [Scheme.Hom.comp_apply, hq₀, hx₀]
  obtain ⟨O, b, hyO, hO, hb⟩ := exists_affine_preimage_iff_not_mem κ (φ 0) (φ 0).isClosedMap (j ≫ H.ι) (φ 0 x₀)
    ((Set.finite_range fun σ => act σ (κ x₀)).subset (by
      rintro _ ⟨p, hp, rfl⟩
      exact orb x₀ p hp.symm))
    (fun p hp => by
      obtain ⟨σ, hσ⟩ := orb x₀ p hp.symm
      exact ⟨_, (hc σ q₀).trans (by rw [hq₀', hσ])⟩)
  let c : C := ⟨∏ σ, actC σ b, (hC _).2 fun τ => by
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => by simp⟩
  have key : ∀ p, φ 0 p ∈ O ↔ ∃ q : PrimeSpectrum C', (j ≫ H.ι) q = κ p ∧ (c : C') ∉ q.asIdeal := fun p => by
    constructor
    · intro hp
      obtain ⟨q, hq, -⟩ := (hb p).1 hp
      refine ⟨q, hq, fun hm => ?_⟩
      obtain ⟨σ, -, hσ⟩ := (q.2.prod_mem_iff).1 hm
      obtain ⟨k, k₁, k₂⟩ := hh₀ σ
      obtain ⟨q', hq', hb'⟩ := (hb (k p)).1 (by rw [← Scheme.Hom.comp_apply, k₂]; exact hp)
      have : q' = spMap (actC σ : C' →+* C') q := (j ≫ H.ι).isOpenEmbedding.injective
        ((hq'.trans (by rw [hq, ← Scheme.Hom.comp_apply k κ, k₁, Scheme.Hom.comp_apply])).trans (hc σ q).symm)
      rw [this] at hb'
      exact hb' hσ
    · rintro ⟨q, hq, hm⟩
      refine (hb p).2 ⟨q, hq, fun hm' => hm ?_⟩
      exact (q.2.prod_mem_iff).2 ⟨1, Finset.mem_univ _, by simpa using hm'⟩
  have key₂ : ∀ z : H.toScheme, π z ∈ l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens) ↔
      ∃ q : PrimeSpectrum C', j q = z ∧ (c : C') ∉ q.asIdeal := fun z => by
    constructor
    · rintro ⟨w, hw', e⟩
      obtain ⟨q, hq, rfl⟩ := lift z w e.symm
      exact ⟨q, hq, hw'⟩
    · rintro ⟨q, rfl, hq⟩
      exact ⟨_, hq, (hw q).symm⟩
  refine ⟨l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens), O, ?_, ?_, hO, ?_⟩
  · obtain ⟨q, hq, hm⟩ := (key x₀).1 hyO
    refine (key₂ x).2 ⟨q, H.ι.isOpenEmbedding.injective ?_, hm⟩
    rw [← hx₀, ← hq]; exact (Scheme.Hom.comp_apply _ _ _).symm
  · refine IsAffineOpen.image_of_isOpenImmersion ?_ l
    rw [← basicOpen_eq_of_affine (R := .of C)]
    exact (isAffineOpen_top _).basicOpen _
  · ext p
    refine (key p).trans ⟨?_, ?_⟩
    · rintro ⟨q, hq, hm⟩
      exact ⟨j q, (key₂ _).2 ⟨q, rfl, hm⟩, hq⟩
    · rintro ⟨z, hz, e⟩
      obtain ⟨q, rfl, hm⟩ := (key₂ z).1 hz
      exact ⟨q, e, hm⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubschemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_descent_open_invariant_subscheme : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ x : H.toScheme, spMap (algebraMap R R') (G'.hom (H.ι x)) = closedPoint R → ∃ (V : X.left.Opens) (O : Y.left.Opens), π x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen O ∧ φ 0 ⁻¹ᵁ O = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ (H.ι ''ᵁ (π ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Mum.exists_affine_chart | exact GlobalTheory.Mum.exists_affine_chart | (intros; apply GlobalTheory.Mum.exists_affine_chart <;> assumption)
end
end
