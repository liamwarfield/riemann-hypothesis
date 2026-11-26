module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
set_option autoImplicit false

namespace GlobalTheory.Published

theorem grothendieckDeformation_of_lifting (P : AbelianDeRham) (L : AbelianLifting) :
    GrothendieckDeformation :=
  fun R _ I κ hκ R₀ _ π hπ hI ↦
    ⟨GrothendieckMessing.canonical_of_abelianDeRham P hκ hπ hI, L R I κ hκ R₀ π hπ hI⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal

theorem IsHeckeL.ne_zero_nat {E : Type} [Field E] [NumberField E] {χ : HChar E} {Λ : ℂ → ℂ} (hu : IsUnitary χ)
    (hΛ : IsHeckeL χ Λ) {s : ℕ} (hs : 1 ≤ s) : Λ s ≠ 0 := by
  rcases hs.eq_or_lt with rfl | h
  · obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire E
    rw [Nat.cast_one]
    exact GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (GlobalTheory.HeckeOne.cf χ) GlobalTheory.HeckeOne.two_le_N
      (GlobalTheory.HeckeOne.norm_cf hu) GlobalTheory.HeckeOne.sumN GlobalTheory.HeckeOne.nonemptyN Z Λ hZd hΛ.1 hZ
      fun s hs => (hΛ.2 s hs).unique (GlobalTheory.HeckeOne.hasProd_exp hu hs)
  · have hs' : 1 < (s : ℂ).re := by
      rw [Complex.natCast_re]; exact_mod_cast h
    rw [(hΛ.2 _ hs').unique (GlobalTheory.HeckeOne.hasProd_exp hu hs')]
    exact Complex.exp_ne_zero _

theorem heckeL_ne_zero_nat : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℤ) (χ : HChar E) (Λ : ℂ → ℂ) (s : ℕ), IsUnitary χ → HasInf χ φ m → (∀ i, 0 < m i) → IsHeckeL χ Λ → 1 ≤ s → Λ s ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hu _ _ hΛ hs => hΛ.ne_zero_nat hu hs

end GlobalTheory.CMVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_real_isFor : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ K : Charts F, (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ r : Real K s σ, r.IsFor u ∧ ∀ k (U : X.Opens), IsAffineOpen U → (∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ⊤ ≤ r.x k ⁻¹ᵁ U := by
  intro I _ g Λ _ F B _ X s σ u hX K hK
  choose U hU hUE using hK
  have hx := fun k => exists_pt_of_affine u (K.W k) (K.base k) (U k) (hU k) (hUE k)
  choose x hxU hxE using hx
  have uniq : ∀ k (y : Sp (Hol (K.W k)) ⟶ X),
      (∀ p (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ y = u.E p) → y = x k := fun k y hy =>
    point_hol_ext_of_isSeparated (K.W k) hX y (x k) (fun p hp => (hy p hp).trans (hxE k p hp).symm)
  refine ⟨⟨x, ?_, ?_⟩, ?_, ?_⟩
  · intro k
    apply point_hol_ext_of_isSeparated (K.W k) inferInstance
    intro p hp
    rw [← Category.assoc, hxE k p hp, u.w p (K.base k p hp), ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    congr 1
  · intro l k k' h
    apply uniq k'
    intro p hp
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    have e : ((Hol.ev p hp).toRingHom.comp (Charts.sh h)) = (Hol.ev (F.shift l p) (K.maps h p hp)).toRingHom := by
      ext f
      simp [Hol.ev_apply, Charts.fn_sh h f hp]
    rw [e, hxE k _ (K.maps h p hp), u.per l p (K.base k' p hp)]
  · intro k p hp
    exact hxE k p hp
  · intro k V hV hVE
    obtain ⟨y, hyV, hyE⟩ := exists_pt_of_affine u (K.W k) (K.base k) V hV hVE
    have e := uniq k y hyE
    subst e
    exact hyV

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticChartsRealization_of_affine : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ K : Charts F, (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ r : Real K s σ, r.IsFor u ∧ ∀ k (U : X.Opens), IsAffineOpen U → (∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ⊤ ≤ r.x k ⁻¹ᵁ U := by
  first | exact @GlobalTheory.AnPer.exists_real_isFor | exact GlobalTheory.AnPer.exists_real_isFor | (intros; apply GlobalTheory.AnPer.exists_real_isFor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem map_fil_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C]
    {J' : Ideal C} (δ' : DividedPowers J') (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_properties : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J), fil δ 0 = ⊤ ∧ fil δ 1 = J ∧ (∀ m n, m ≤ n → fil δ n ≤ fil δ m) ∧ (∀ m n, fil δ m * fil δ n ≤ fil δ (m + n)) ∧ (∀ n, ∀ x ∈ J, δ.dpow n x ∈ fil δ n) ∧ (IsNilDP δ ↔ ∃ N, IsLev δ N) ∧ ∀ (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → ∀ N, (fil δ N).map f ≤ fil δ' N := by
  intro B _ J δ
  refine ⟨fil_zero_eq_top δ, fil_one_eq δ, fun m n h ↦ GlobalTheory.Cris.ExpBij.dpFil_anti δ h, fun m n ↦ ?_,
    fun n x hx ↦ GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hx n, isDPNilpotent_iff_exists_isLevel δ,
    fun C _ J' δ' f hf N ↦ map_fil_le δ δ' f hf N⟩
  rw [Ideal.mul_le]
  exact fun a ha b hb ↦ GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ ha hb

end GlobalTheory.PDA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_le_map_fil : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C]
    (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f →
    ∀ N, fil δ' N ≤ (fil δ N).map f := by
  intro B _ J δ C _ J' δ' f hf hJ N
  subst hJ
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_le.2 fun x hx y hy ↦ ExpBij.mul_mem_dpFil δ hx hy)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_eq_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (ExpBij.dpow_mem_dpFil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (ExpBij.dpFil_anti δ h2) (hprod l h1)

end GlobalTheory.PDA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphismStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerFiltrationIdeal_le_map_of_isDPMorphism : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f → ∀ N, fil δ' N ≤ (fil δ N).map f := by
  first | exact @GlobalTheory.PDA.fil_le_map_fil | exact GlobalTheory.PDA.fil_le_map_fil | (intros; apply GlobalTheory.PDA.fil_le_map_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilLift

theorem surjective_spMap_of_isNilpotent_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isProper_and_geometricallyConnected_of_smooth_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  intro R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc
  have hs : Surjective (spMap π) := surjective_spMap_of_isNilpotent_ker π hπ hn
  have hc : IsClosedImmersion (spMap π) := .spec_of_surjective _ hπ
  have : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs
  have : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc
  have : IsProper (i ≫ X.hom) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective i X.hom
  have : IsSeparated X.hom := GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom
  have : LocallyOfFiniteType X.hom := inferInstance
  refine ⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hφ : RingHom.ker π ≤ RingHom.ker φ.hom := by
    intro a ha
    obtain ⟨n, hn⟩ := hn
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    have h0 : IsNilpotent a := ⟨n, this⟩
    exact (h0.map φ.hom).eq_zero
  let ψ : R₀ →+* K := RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩
  have hψ : ∀ a, ψ (π a) = φ.hom a := fun a ↦
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a
  let y' : Spec (CommRingCat.of K) ⟶ Sp R₀ := Spec.map (CommRingCat.ofHom ψ)
  have hy : y' ≫ spMap π = Spec.map φ := by
    simp only [y', spMap, ← Spec.map_comp]
    congr 1
    ext a
    exact hψ a
  rw [← hy] at hz
  let p : Z ⟶ X₀.left := hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])
  refine hgc.geometrically_connectedSpace y' p snd ?_
  exact IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq

end GlobalTheory.NilLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLifStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_geometricallyConnected_smooth_nilpotent_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  first | exact @GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift | exact GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift | (intros; apply GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExponentLogLeOfCut
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem sum_exponent_log_le_of_cut :
    Formalism.CohomologicalDescent.E.ExCut → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → LargeParameterEstimates.Rows P X' A → LargeParameterEstimates.Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f → W.Sp.card ≤ 5 →
    ∀ T : ℕ, W.T2.card ≤ T → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
    ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b := by
  intro hC P X' A hH hL hR hB ι _ _ W hW hcard hSp T hT Q hQ
  have hs := Formalism.CohomologicalDescent.E.recursion_sum_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC Formalism.CohomologicalDescent.Top.prime_count_bound_rs
    P hH hL ι W hW hcard hSp Q hQ
  have hTf : W.T2.card ≤ P.f := by rw [← hcard]; exact Finset.card_le_univ _
  have ht := LargeParameterEstimates.tail_bound_holds P X' A _ hH hR hB hTf
  have F := LargeParameterEstimates.large_parameter_facts_of_hyp hH hR hB
  have hb : 0 ≤ P.b := F.b_pos.le
  have hm : (0 : ℝ) ≤ (P.m : ℝ) * P.b * P.L ^ 2 := by positivity
  have hTT : (W.T2.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have key : 30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 ≤ 30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 := by
    nlinarith
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfIsStd
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.isDPMorphism_of_isStd :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)),
      Q.IsStd δ η → ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (F : Q.P →+* C) (c : C),
        c ∈ J'' → IsDPMorphism δ δ'' (F.comp (algebraMap B Q.P)) → (∀ n, F (Q.e n) = δ''.dpow n c) →
          IsDPMorphism η δ'' F := by
  intro B _ J δ Q η hQ C _ J'' δ'' F c hc hF he
  have hS : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
    rw [Ideal.span_union, ← Ideal.map_span, Ideal.span_eq]; rfl
  refine IsDPMorphism.on_span η δ'' hS ?_ ?_
  · rintro s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · exact hF.1 (Ideal.mem_map_of_mem _ ha)
    · rw [he]; exact δ''.dpow_mem k.succ_ne_zero hc
  · rintro n s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · rw [hQ.dp.2 a ha]
      exact (hF.2 a ha).symm
    · have h1 := Q.e_one_mem_ext J
      show F (η.dpow n (Q.e (k + 1))) = δ''.dpow n (F (Q.e (k + 1)))
      have h2 : η.dpow n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
        rw [← hQ.var (k + 1), η.dpow_comp k.succ_ne_zero h1, hQ.var]
      rw [h2, map_mul, map_natCast, he, he, δ''.dpow_comp k.succ_ne_zero hc]

end GlobalTheory.PDA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientSubDPIdeal
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPQuot

theorem quotient_subDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J),
    (∀ 𝔟 : Ideal B, δ.IsSubDPIdeal 𝔟 → ∃ δ' : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)),
      IsDPMorphism δ δ' (Ideal.Quotient.mk 𝔟) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : B ⧸ 𝔟 →+* C),
        IsDPMorphism δ δ'' (g.comp (Ideal.Quotient.mk 𝔟)) → IsDPMorphism δ' δ'' g) ∧
    ∀ s : Set B, s ⊆ J →
      δ.IsSubDPIdeal (Ideal.span {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x}) := by
  intro B _ J δ
  refine ⟨fun 𝔟 h𝔟 ↦ ?_, fun s hs ↦ ?_⟩
  · have hinf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
      rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟
    refine ⟨Quotient.dividedPowers δ hinf, Quotient.isDPMorphism δ hinf, ?_⟩
    intro C _ J'' δ'' g hg
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_map]; exact hg.1
    · obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [Quotient.dpow_apply δ hinf ha]
      exact hg.2 a ha
  · have hset : {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x} =
        {y : B | ∃ (n : ℕ) (_ : n ≠ 0) (x : B) (_ : x ∈ s), y = δ.dpow n x} := by
      ext y; simp only [Set.mem_setOf_eq, exists_prop]
    rw [hset, ← SubDPIdeal.span_carrier_eq_dpow_span δ hs]
    exact (SubDPIdeal.span δ s).toIsSubDPIdeal

end GlobalTheory.DPQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularPrimitiveCharacters
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]


variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

end GlobalTheory.FinGL.LeviChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCompSectionOfProperSmoothNilpotentRigidity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCompSectionOfProperSmoothNilpotentRigidity
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Rigidity

theorem spMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hs : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) :
    Function.Surjective (spMap π) := by
  have h := _root_.range_comap_of_surjective R₀ π hs
  have h2 : PrimeSpectrum.zeroLocus (RingHom.ker π : Set R) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact (Submodule.mem_bot R).1 this
  rw [h2, Set.range_eq_univ] at h
  exact h

theorem eq_comp_section : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (P X : Over (Sp R)) (P₀ : Over (Sp R₀)) (l : P₀.left ⟶ P.left), IsPullback l P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f : P ⟶ X) (s₀ : Sp R₀ ⟶ X.left), l ≫ f.left = P₀.hom ≫ s₀ →
    f.left = P.hom ≫ ε ≫ f.left := by
  intro R R₀ _ _ π hs hn P X P₀ l hpb hsm hpr hgc ε hε f s₀ hf
  have := hsm
  have := hpr
  have : GeometricallyIntegral P.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.hom hsm hgc
  have hsurj : ∀ V : (Sp R).Opens, Function.Surjective (P.hom.app V).hom := fun V => by
    have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange
      exists_noetherian_model_of_smooth P.hom V
    exact (ConcreteCategory.bijective_of_isIso (P.hom.app V)).2
  have hloc : ∀ t : Sp R, ∃ V : (Sp R).Opens, t ∈ V ∧
      (P.hom ⁻¹ᵁ V).ι ≫ f.left = (P.hom ⁻¹ᵁ V).ι ≫ P.hom ≫ ε ≫ f.left := by
    intro t
    obtain ⟨t₀, ht₀⟩ := spMap_surjective π hs hn t
    refine local_rigidity _ _ _ P.hom ε f.left hε inferInstance hsurj t (s₀ t₀) ?_
    intro x hx
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := P.hom) (g := spMap π) x t₀
      (hx.trans ht₀.symm)
    have e₁ : l (hpb.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    have e₂ : P₀.hom (hpb.isoPullback.inv z) = t₀ := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
    rw [← e₁, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply, e₂]
  choose V hV hfg using hloc
  have hc : TopologicalSpace.IsOpenCover (fun t => P.hom ⁻¹ᵁ V t) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P.hom x, hV (P.hom x)⟩
  exact (P.left.openCoverOfIsOpenCover _ hc).hom_ext _ _ fun t => hfg t

end GlobalTheory.Rigidity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCompSectionOfProperSmoothNilpotentRigidityStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (P X : Over (Sp R)) (P₀ : Over (Sp R₀)) (l : P₀.left ⟶ P.left), IsPullback l P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f : P ⟶ X) (s₀ : Sp R₀ ⟶ X.left), l ≫ f.left = P₀.hom ≫ s₀ →
    f.left = P.hom ≫ ε ≫ f.left := by
  first | exact @GlobalTheory.Rigidity.eq_comp_section | exact GlobalTheory.Rigidity.eq_comp_section | (intros; apply GlobalTheory.Rigidity.eq_comp_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem PDPoly.liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    Q.liftAlg c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem PDPoly.exists_lift_and_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 →
      (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) →
      ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧
    ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  intro B _ Q
  refine ⟨fun C _ f c h0 hm ↦ ?_, ?_⟩
  · letI := f.toAlgebra
    exact ⟨(Q.liftAlg c h0 hm).toRingHom, fun b ↦ (Q.liftAlg c h0 hm).commutes b,
      fun n ↦ Q.liftAlg_e c h0 hm n⟩
  · let d : ℕ → B := fun n ↦ if n = 0 then 1 else 0
    have h0 : d 0 = 1 := by simp [d]
    have hm : ∀ m n, d m * d n = ((m + n).choose m : B) * d (m + n) := by
      intro m n
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [d, hm, hn]
    let ε := Q.liftAlg d h0 hm
    have hε : ∀ n, ε (Q.e n) = d n := Q.liftAlg_e d h0 hm
    have hmem : ∀ p, p - algebraMap B Q.P (ε p) ∈ Q.aug := by
      intro p
      have hp : p ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        rw [hε]
        rcases n with _ | n
        · simp [d, Q.e_zero]
        · simpa [d] using Q.e_succ_mem_aug n
      | zero => simp
      | add x y _ _ hx hy =>
        have : x + y - algebraMap B Q.P (ε (x + y)) =
            (x - algebraMap B Q.P (ε x)) + (y - algebraMap B Q.P (ε y)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this]; exact add_mem hx hy
      | smul b x _ hx =>
        have : b • x - algebraMap B Q.P (ε (b • x)) = algebraMap B Q.P b * (x - algebraMap B Q.P (ε x)) := by
          rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
        rw [this]; exact Q.aug.mul_mem_left _ hx
    refine ⟨ε, fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩⟩
    · have hle : Q.aug ≤ RingHom.ker ε := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨n, rfl⟩
        simp [RingHom.mem_ker, hε, d]
      exact RingHom.mem_ker.1 (hle hp)
    · have := hmem p
      rwa [hp, map_zero, sub_zero] at this

end GlobalTheory.PDA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMapStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_and_augmentation_map : ∀ (B : Type) [CommRing B] (Q : PDPoly B), (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 → (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) → ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧ ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_lift_and_aug | exact GlobalTheory.PDA.PDPoly.exists_lift_and_aug | (intros; apply GlobalTheory.PDA.PDPoly.exists_lift_and_aug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory.AnPer.SliceTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

theorem analyticAt_shift (q : (I ⊕ Fin g → ℂ) × (Fin g → ℂ)) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      (((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) q := by
  have h1 : ∀ j, AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦ y.1 j) q := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ⊕ Fin g ↦ ℂ) j).comp
      (ContinuousLinearMap.fst ℂ (I ⊕ Fin g → ℂ) (Fin g → ℂ))).analyticAt q
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ h1 _) ?_
  exact analyticAt_snd.add (analyticAt_pi_iff.2 fun i ↦ h1 _)

theorem analyticAt_joint {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      h.fn ((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b))) (0, w) := by
  refine AnalyticAt.comp_of_eq (h.analytic _ hw) (analyticAt_shift _) ?_
  ext <;> simp

theorem analyticAt_slice {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h.fn ((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b))) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ (x, w)) (analyticAt_joint h hw)
    (analyticAt_id.prod analyticAt_const) rfl

theorem eventually_mem {W : Opens ((I → ℂ) × (Fin g → ℂ))} {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0,
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ)) ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) := by
    fun_prop
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  have e : (((fun i ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inl i)), w + fun b ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inr b)) :
      (I → ℂ) × (Fin g → ℂ)) = (0, w) := by
    ext <;> simp
  change _ ∈ W
  simp only [e]
  exact hw

end GlobalTheory.AnPer.SliceTaylor


open GlobalTheory.AnPer.SliceTaylor in
theorem GlobalTheory.AnPer.exists_sliceTaylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  intro I _ _ g D _ _ N t ht E _ _ _ W W₀ a ha hW
  have key : ∀ h : Hol W, ∃ r : D ⊗[ℂ] Hol W₀, ∀ (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) r = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
    intro h
    have han : ∀ (k : ℕ) (v : Fin k → (I ⊕ Fin g → ℂ)), AnalyticOnNhd ℂ (fun p ↦ iteratedFDeriv ℂ k
        (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) 0 v) W₀ :=
      fun k v p hp ↦
        AnalyticAt.comp_of_eq (GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq _ (a p) k v (analyticAt_joint h (hW p hp))).1 (ha p hp) rfl
    unfold GlobalTheory.PeriodFamily.taylor
    refine ⟨∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I ⊕ Fin g,
      ((k.factorial : ℂ)⁻¹ • ∏ b, t (s b)) ⊗ₜ[ℂ] Hol.mk _ (han k fun b ↦ Pi.single (s b) 1), fun p hp ↦ ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, Hol.fn_mk _ _ hp,
      AlgHom.id_apply, Algebra.ofId_apply, mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]
  choose r hr using key
  obtain ⟨hadd, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ c : ℂ, r (algebraMap ℂ _ c) = algebraMap ℂ _ c := fun c ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [hr, AlgHom.commutes, ← hconst c]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_algebraMap c hx
  have hA : ∀ f h : Hol W, r (f + h) = r f + r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_add (f := _), hr, hr, hr, ← hadd _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_add f h hx
  have hM : ∀ f h : Hol W, r (f * h) = r f * r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_mul, hr, hr, hr,
      ← GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_mul f h hx
  exact ⟨{ toFun := r
           map_one' := by simpa only [map_one] using hc 1
           map_mul' := hM
           map_zero' := by simpa using hc 0
           map_add' := hA
           commutes' := hc }, hr⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHomStatement
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  first | exact @GlobalTheory.AnPer.exists_sliceTaylor_algHom | exact GlobalTheory.AnPer.exists_sliceTaylor_algHom | (intros; apply GlobalTheory.AnPer.exists_sliceTaylor_algHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReduction
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftDim

theorem surjective_spMap_of_nilpotent {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    intro x hx
    obtain ⟨n, hn⟩ := hnil
    refine (P : PrimeSpectrum R).2.mem_of_pow_mem n ?_
    have h : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    rw [h]; exact zero_mem _
  exact this

theorem smoothOfRelativeDimension_of_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (g : ℕ) (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    SmoothOfRelativeDimension g X₀.hom → SmoothOfRelativeDimension g X.hom := by
  intro R R₀ _ _ π hπ hnil g X X₀ i hpb hsm hg
  have hs : Surjective (spMap π) := surjective_spMap_of_nilpotent π hπ hnil
  have hi : Surjective i := MorphismProperty.of_isPullback hpb.flip hs
  have key : ∀ x : X.left, ∃ W : X.left.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ X.hom) := by
    intro x
    obtain ⟨n, W, hx, hW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom x
    obtain ⟨x₀, hx₀⟩ := hi.surj x
    have hn : n = g := ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hW hg x₀ (by rw [hx₀]; exact hx)
    subst hn
    exact ⟨W, hx, hW⟩
  choose W hW hd using key
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W ?_ hd
  exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩

end GlobalTheory.LiftDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReductionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (g : ℕ) (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    SmoothOfRelativeDimension g X₀.hom → SmoothOfRelativeDimension g X.hom := by
  first | exact @GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction | exact GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction | (intros; apply GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltration
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem crys_two_reductions : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg
  obtain ⟨-, -, -, PR, -⟩ := P
  have hπ : Function.Surjective π := by
    rw [← st.comp]; exact st.surj₁.comp st.surj
  have hb : spMap π₁ ≫ spMap ρ = spMap π ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id, ← st.comp, Cris.spMap_comp]
  let N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁ :=
    GrpMor.of_isGrpPullback st.dpJ hb h₁
  have key : ∀ c, N.pull ((liftMor (divided₂ hJ) h₂).pull c) = (liftMor κ h).pull c := fun c ↦
    GrpMor.pull_pull (liftMor (divided₂ hJ) h₂) N (liftMor κ h) (fun _ ↦ rfl) e c
  have b := PR R A g hA hg I κ st.nil R₀ π hπ st.ker A₀ i h
  have b₂ := PR R A g hA hg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) R₁ ρ st.surj st.kerJ A₁ i₂ h₂
  refine ⟨N, ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩, fun d ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := b₂.2 x
    obtain ⟨y, rfl⟩ := b₂.2 y
    have : (liftMor κ h).pull x = (liftMor κ h).pull y := by
      rw [← key, ← key]; exact hxy
    rw [b.1 this]
  · obtain ⟨c, rfl⟩ := b.2 y
    exact ⟨_, key c⟩
  · ext c
    show d ((liftMor κ h).pull c) = d (N.pull ((liftMor (divided₂ hJ) h₂).pull c))
    rw [key]

end GlobalTheory.SqLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltrationStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_crystal_two_reductions_agree : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  first | exact @GlobalTheory.SqLift.crys_two_reductions | exact GlobalTheory.SqLift.crys_two_reductions | (intros; apply GlobalTheory.SqLift.crys_two_reductions <;> assumption)
end
end
