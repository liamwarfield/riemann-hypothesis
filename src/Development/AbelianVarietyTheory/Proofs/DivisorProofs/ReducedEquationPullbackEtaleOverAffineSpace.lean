module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleReducedEq

theorem isRadical_map_of_etale {Q C : Type} [CommRing Q] [CommRing C] [Algebra Q C]
    [Algebra.Etale Q C] (I : Ideal Q) (hI : I.IsRadical) :
    (I.map (algebraMap Q C)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have : _root_.IsReduced (TensorProduct Q (Q ⧸ I) C) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (Q ⧸ I) _
  have : _root_.IsReduced (TensorProduct Q C (Q ⧸ I)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm Q C (Q ⧸ I)).toRingEquiv (RingEquiv.injective _)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingEquiv
    (RingEquiv.injective _)

theorem etale_eval₂Hom_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale) :
    (MvPolynomial.eval₂Hom ψ N).Etale := by
  have : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway g
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι A) := MvPolynomial.algebraMvPolynomial
  have : Algebra.Etale (MvPolynomial ι R) (MvPolynomial ι A) :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R (MvPolynomial ι R) A (MvPolynomial ι A))
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  letI : Algebra (MvPolynomial ι R) C :=
    (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).toAlgebra
  have : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι A) C :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [MvPolynomial.algebraMap_def, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  have : Algebra.Etale (MvPolynomial ι R) C := hE
  exact Algebra.Etale.of_restrictScalars (MvPolynomial ι R) (MvPolynomial ι A) C

theorem isRadical_span_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g δ : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale)
    (hδ : (Ideal.span {algebraMap R A δ}).IsRadical) :
    (Ideal.span {ψ (algebraMap R A δ)}).IsRadical := by
  have he := etale_eval₂Hom_of_away g ψ N hE
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  have : Algebra.Etale (MvPolynomial ι A) C := he
  have hI : (Ideal.map (MvPolynomial.C (σ := ι)) (Ideal.span {algebraMap R A δ})).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced] at hδ ⊢
    exact isReduced_of_injective
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (Ideal.span {algebraMap R A δ})).symm.toRingEquiv
      (RingEquiv.injective _)
  have h2 := isRadical_map_of_etale (C := C) _ hI
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply, MvPolynomial.eval₂Hom_C] at h2
  exact h2

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_ger_iff_not_mem {X : Scheme.{0}} (Z : Closeds X) (U' : X.affineOpens)
    (δ : Γ(X, U'.1)) (h : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U' = Ideal.span {δ})
    (x : X) (hx : x ∈ U'.1) : IsUnit (ger x hx δ) ↔ x ∉ Z := by
  obtain ⟨P, rfl⟩ : x ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hx
  have hS : IsClosed (X := PrimeSpectrum Γ(X, U'.1)) (U'.2.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage U'.2.fromSpec.continuous
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at h
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, U'.2.fromSpec_preimage_basicOpen]
  change δ ∉ P.asIdeal ↔ _
  rw [not_iff_not]
  have e := congrArg (P ∈ ·)
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U'.2.fromSpec ⁻¹' (Z : Set X)))
  rw [hS.closure_eq, h, PrimeSpectrum.zeroLocus_span] at e
  have e3 : (δ ∈ P.asIdeal) = (P ∈ PrimeSpectrum.zeroLocus {δ}) :=
    propext ((PrimeSpectrum.mem_zeroLocus (P : PrimeSpectrum Γ(X, U'.1)) {δ}).trans
      Set.singleton_subset_iff).symm
  exact (e3.trans e).to_iff

theorem mem_iff_not_isUnit_ger {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (P : Spec Γ(Y, W)) (hP : hW.fromSpec P ∈ W) (c : Γ(Y, W)) :
    c ∈ P.asIdeal ↔ ¬ IsUnit (ger (hW.fromSpec P) hP c) := by
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, hW.fromSpec_preimage_basicOpen]
  change _ ↔ ¬ ¬ c ∈ P.asIdeal
  rw [not_not]

theorem reducedEq_pullback_etale : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  intro X Y _ q ι _ Vo U U' hU' W hW hWU N hEt δ hδ
  have part1 : ∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 →
      (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo) := by
    intro z hz hzU'
    rw [ger_appLE q hWU z hz δ, isUnit_map_iff, ← ger_resG hU' (q z) hzU' δ,
      isUnit_ger_iff_not_mem _ U' _ hδ]
    exact not_not
  refine ⟨part1, ?_⟩
  intro W' hW' hW'U' f hf z hz
  obtain ⟨g, hgU', hzg⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨q z, hW'U' hz⟩ (hWU (hW' hz))
  set g' := resG X hU' g
  set V := X.basicOpen g'
  have hV' : V = X.basicOpen g := by
    simp only [V, g', resG, Scheme.basicOpen_res]
    exact inf_eq_right.2 hgU'
  have hVU' : V ≤ U'.1 := X.basicOpen_le g'
  have hVU : V ≤ U.1 := hVU'.trans hU'
  letI : Algebra Γ(X, U.1) Γ(X, V) := (resG X hVU).toAlgebra
  haveI : IsLocalization.Away g Γ(X, V) := U.2.isLocalization_of_eq_basicOpen g (homOfLE hVU) hV'
  have hδV : (Ideal.span {algebraMap Γ(X, U.1) Γ(X, V) δ}).IsRadical := by
    have e := (Scheme.IdealSheafData.vanishingIdeal Vo.compl).map_ideal_basicOpen U' g'
    rw [hδ, Ideal.map_span, Set.image_singleton] at e
    have hrad : ((Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal
        (X.affineBasicOpen g')).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    rw [← e] at hrad
    have e2 : algebraMap Γ(X, U.1) Γ(X, V) δ =
        (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom (resG X hU' δ) :=
      (resG_resG hU' hVU' δ).symm
    rw [e2]
    exact hrad
  have hzV : q z ∈ V := hV' ▸ hzg
  obtain ⟨h, hhle, hzh⟩ := hW.exists_basicOpen_le (V := W' ⊓ q ⁻¹ᵁ V) ⟨z, hz, hzV⟩ (hW' hz)
  set W1 := Y.basicOpen h
  have hW1W : W1 ≤ W := Y.basicOpen_le h
  have hW1V : W1 ≤ q ⁻¹ᵁ V := hhle.trans inf_le_right
  have hW1W' : W1 ≤ W' := hhle.trans inf_le_left
  have hW1 : IsAffineOpen W1 := hW.basicOpen h
  let ψ : Γ(X, V) →+* Γ(Y, W1) := (q.appLE V W1 hW1V).hom
  have hcomp : MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i)) =
      (resG Y hW1W).comp (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.algebraMap_toAlgebra, ψ, resG]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE_map]
    · intro i
      simp
  have hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i))).Etale := by
    rw [hcomp]
    have h2 : (resG Y hW1W).Etale := by
      letI : Algebra Γ(Y, W) Γ(Y, W1) := (resG Y hW1W).toAlgebra
      haveI : IsLocalization.Away h Γ(Y, W1) := hW.isLocalization_basicOpen h
      exact Algebra.Etale.of_isLocalizationAway h
    exact RingHom.Etale.stableUnderComposition _ _ hEt h2
  have rad := isRadical_span_of_away g δ ψ (fun i => resG Y hW1W (N i)) hE hδV
  have hd : ψ (algebraMap Γ(X, U.1) Γ(X, V) δ) = resG Y hW1W ((q.appLE U.1 W hWU).hom δ) := by
    have := congrArg (fun F => F (MvPolynomial.C δ)) hcomp
    simpa using this
  set d := ψ (algebraMap Γ(X, U.1) Γ(X, V) δ)
  set b := resG Y hW1W' f
  have hb : b ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hdP, hP⟩
    let P' : Spec Γ(Y, W1) := ⟨P, hP⟩
    have hz' : hW1.fromSpec P' ∈ W1 := by
      rw [← SetLike.mem_coe, ← hW1.range_fromSpec]; exact Set.mem_range_self _
    have hdP' : d ∈ P'.asIdeal := hdP (Ideal.mem_span_singleton_self d)
    rw [mem_iff_not_isUnit_ger hW1 P' hz', hd, ger_resG] at hdP'
    have hq : q (hW1.fromSpec P') ∉ Vo := by
      rw [← part1 _ (hW1W hz') (hVU' (hW1V hz'))]
      exact hdP'
    have hm := hf _ (hW1W' hz') hq
    change b ∈ P'.asIdeal
    rw [mem_iff_not_isUnit_ger hW1 P' hz', ger_resG]
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (rad hb)
  refine ⟨ger z hzh c, ?_⟩
  rw [← ger_resG hW1W' z hzh f, ← ger_resG hW1W z hzh, ← hd]
  change ger z hzh b = _
  rw [← hc, map_mul, mul_comm]

end GlobalTheory.EtaleReducedEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  first | exact @GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | exact GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | (intros; apply GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
open IsLocalRing GlobalTheory.FormalOrigin

noncomputable section
namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterOp_succ {A : Type} {n : ℕ} (ds : Fin (n+1) → A → A) (α : Fin (n+1) →₀ ℕ) (f : A) :
    iterOp ds α f = (ds 0)^[α 0] (iterOp (fun i => ds i.succ) α.tail f) := by
  unfold iterOp
  rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
  congr 1

def iterHom {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) : A →+ A where
  toFun := (⇑D)^[k]
  map_zero' := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  map_add' x y := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add (f := _), Function.iterate_succ_apply',
        Function.iterate_succ_apply']

theorem iterHom_apply {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) (x : A) :
    iterHom D k x = (⇑D)^[k] x := rfl

theorem exists_iterOpHom {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ),
    ∃ F : A →+ A, ∀ x, F x = iterOp (fun i => ⇑(ds i)) α x := by
  intro n
  induction n with
  | zero =>
      intro ds α
      refine ⟨AddMonoidHom.id A, fun x => ?_⟩
      have : α = 0 := Subsingleton.elim _ _
      subst this; rw [iterOp_zero]; rfl
  | succ n ih =>
      intro ds α
      obtain ⟨F, hF⟩ := ih (fun i => ds i.succ) α.tail
      exact ⟨(iterHom (ds 0) (α 0)).comp F, fun x => by
        rw [iterOp_succ, AddMonoidHom.comp_apply, iterHom_apply, hF]⟩

theorem sum_antidiagonal_succ {M : Type} [AddCommMonoid M] {n : ℕ} (α : Fin (n+1) →₀ ℕ)
    (F : (Fin (n+1) →₀ ℕ) → (Fin (n+1) →₀ ℕ) → M) :
    ∑ p ∈ antidiagonal α, F p.1 p.2 =
      ∑ q ∈ antidiagonal (α 0), ∑ r ∈ antidiagonal α.tail,
        F (Finsupp.cons q.1 r.1) (Finsupp.cons q.2 r.2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ((p.1 0, p.2 0), (p.1.tail, p.2.tail)))
    (fun x => (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p1, p2⟩ h
    simp only [mem_coe, HasAntidiagonal.mem_antidiagonal] at h
    simp only [mem_coe, mem_product, HasAntidiagonal.mem_antidiagonal]
    subst h
    refine ⟨by simp, ?_⟩
    ext i; simp [Finsupp.tail_apply]
  · rintro ⟨⟨j, k⟩, ⟨r1, r2⟩⟩ h
    simp only [mem_coe, mem_product, HasAntidiagonal.mem_antidiagonal] at h
    simp only [mem_coe, HasAntidiagonal.mem_antidiagonal]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h.1]
    · have := DFunLike.congr_fun h.2 i
      simpa [Finsupp.tail_apply] using this
  · rintro ⟨p1, p2⟩ _
    simp [Finsupp.cons_tail]
  · rintro ⟨⟨j, k⟩, ⟨r1, r2⟩⟩ _
    simp [Finsupp.tail_cons]
  · rintro ⟨p1, p2⟩ _
    simp [Finsupp.cons_tail]

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterOp_mul {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) (f g : A),
    iterOp (fun i => ⇑(ds i)) α (f * g) = ∑ p ∈ antidiagonal α,
      (∏ i, (α i).choose (p.1 i)) • (iterOp (fun i => ⇑(ds i)) p.1 f * iterOp (fun i => ⇑(ds i)) p.2 g)
  | 0, ds, α, f, g => by
      have : α = 0 := Subsingleton.elim _ _
      subst this
      simp [iterOp_zero]
  | n+1, ds, α, f, g => by
      have ih := iterOp_mul (fun i => ds i.succ) α.tail f g
      have hs : ∀ (β : Fin (n+1) →₀ ℕ) x, iterOp (fun i => ⇑(ds i)) β x =
          (⇑(ds 0))^[β 0] (iterOp (fun i => ⇑(ds i.succ)) β.tail x) := fun β x => iterOp_succ _ β x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, ih, ← iterHom_apply, map_sum, sum_antidiagonal_succ α (fun a b => (∏ i, (α i).choose (a i)) •
        (iterOp (fun i => ⇑(ds i)) a f * iterOp (fun i => ⇑(ds i)) b g))]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_nsmul, iterHom_apply, GlobalTheory.derivation_iterate_leibniz, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs, hs, Fin.prod_univ_succ]
      simp only [Finsupp.cons_zero, Finsupp.tail_cons, Finsupp.cons_succ, Finsupp.tail_apply]
      rw [← nsmul_eq_mul, smul_smul, mul_comm]

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterate_one {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) :
    (⇑D)^[k] 1 = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Function.iterate_succ_apply, D.map_one_eq_zero, ← iterHom_apply, map_zero]
    simp

theorem eq_zero_iff_succ {n : ℕ} (α : Fin (n+1) →₀ ℕ) : α = 0 ↔ α 0 = 0 ∧ α.tail = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, by ext i; simp [Finsupp.tail_apply]⟩
  · rintro ⟨h0, ht⟩
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0
    · have := DFunLike.congr_fun ht i
      simpa [Finsupp.tail_apply] using this

theorem iterOp_one {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ),
    iterOp (fun i => ⇑(ds i)) α 1 = if α = 0 then 1 else 0
  | 0, ds, α => by
      have : α = 0 := Subsingleton.elim _ _
      subst this
      simp [iterOp_zero]
  | n+1, ds, α => by
      have ih := iterOp_one (fun i => ds i.succ) α.tail
      have hs : ∀ (β : Fin (n+1) →₀ ℕ) x, iterOp (fun i => ⇑(ds i)) β x =
          (⇑(ds 0))^[β 0] (iterOp (fun i => ⇑(ds i.succ)) β.tail x) := fun β x => iterOp_succ _ β x
      rw [hs, ih]
      by_cases ht : α.tail = 0
      · rw [if_pos ht, iterate_one]
        simp [eq_zero_iff_succ α, ht]
      · rw [if_neg ht, ← iterHom_apply, map_zero]
        simp [eq_zero_iff_succ α, ht]

theorem iterOp_add {A : Type} [CommRing A] {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) (f g : A) :
    iterOp (fun i => ⇑(ds i)) α (f + g) = iterOp (fun i => ⇑(ds i)) α f + iterOp (fun i => ⇑(ds i)) α g := by
  obtain ⟨F, hF⟩ := exists_iterOpHom ds α
  rw [← hF, ← hF, ← hF, map_add (f := _)]

theorem iterOp_zero' {A : Type} [CommRing A] {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) :
    iterOp (fun i => ⇑(ds i)) α 0 = 0 := by
  obtain ⟨F, hF⟩ := exists_iterOpHom ds α
  rw [← hF, map_zero]

theorem factor_identity {n : ℕ} (α : Fin n →₀ ℕ) (p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ)) (hp : p.1 + p.2 = α) :
    (∏ i, ((α i).factorial : ℚ))⁻¹ * ((∏ i, (α i).choose (p.1 i) : ℕ) : ℚ) =
      (∏ i, ((p.1 i).factorial : ℚ))⁻¹ * (∏ i, ((p.2 i).factorial : ℚ))⁻¹ := by
  have hfac : ∀ i, ((α i).choose (p.1 i) : ℚ) * (((p.1 i).factorial : ℚ) * ((p.2 i).factorial : ℚ)) =
      ((α i).factorial : ℚ) := by
    intro i
    have e : α i = p.1 i + p.2 i := by rw [← hp]; rfl
    have h2 : p.2 i = α i - p.1 i := by omega
    have := Nat.choose_mul_factorial_mul_factorial (n := α i) (k := p.1 i) (by omega)
    rw [← h2] at this
    rw [← mul_assoc]
    exact_mod_cast this
  have hprod : (∏ i, ((α i).choose (p.1 i) : ℚ)) *
      ((∏ i, ((p.1 i).factorial : ℚ)) * ∏ i, ((p.2 i).factorial : ℚ)) = ∏ i, ((α i).factorial : ℚ) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hfac i
  have h1 : (∏ i, ((p.1 i).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (∏ i, ((p.2 i).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (∏ i, ((α i).choose (p.1 i) : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.choose_pos (by
      have e : α i = p.1 i + p.2 i := by rw [← hp]; rfl
      omega)).ne'
  push_cast
  rw [← hprod]
  field_simp

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin
open Finset TaylorRingHom

theorem taylor_isRingHom : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A), ∃ T : A →+* MvPowerSeries (Fin n) B, ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f := by
  intro A B _ _ _ n ev ds
  refine ⟨{ toFun := taylor ev (fun i => ⇑(ds i))
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun f => rfl⟩
  · ext α
    rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_one]
    unfold taylor
    rw [iterOp_one]
    split_ifs with h
    · subst h; simp
    · simp
  · intro f g
    ext α
    rw [MvPowerSeries.coeff_mul]
    simp only [MvPowerSeries.coeff_apply]
    unfold taylor
    set_option synthInstance.maxHeartbeats 100000 in
      rw [iterOp_mul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, map_mul, nsmul_eq_mul, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, ← map_natCast (algebraMap ℚ B), ← mul_assoc,
      ← map_mul, factor_identity α p hp, map_mul]
    ring
  · ext α
    rw [MvPowerSeries.coeff_apply, map_zero]
    unfold taylor
    rw [iterOp_zero', map_zero, smul_zero]
  · intro f g
    ext α
    rw [MvPowerSeries.coeff_apply, map_add (f := _), MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
    unfold taylor
    rw [iterOp_add, map_add (f := _), smul_add]

end GlobalTheory.FormalOrigin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHomStatement
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_eq_taylor : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), ∃ T : A →+* MvPowerSeries (Fin n) B, ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f := by
  first | exact @GlobalTheory.FormalOrigin.taylor_isRingHom | exact GlobalTheory.FormalOrigin.taylor_isRingHom | (intros; apply GlobalTheory.FormalOrigin.taylor_isRingHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false

namespace GlobalTheory.UPel.HT.ES.KerUPart

theorem exists_elt {O : Type} [CommRing O] (I J : Ideal O) (q : O) (h : IsCoprime I J)
    (hq : I * J ≤ Ideal.span {q}) (E : ℕ) :
    ∃ α : O, (∀ a ∈ I ^ E, ∃ u v, a = u * α + v * q ^ E) ∧ ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ v, α = a + v * q ^ E := by
  have hm : ∀ a ∈ I ^ E, ∀ b ∈ J ^ E, ∃ v, a * b = v * q ^ E := fun a ha b hb => by
    have h1 : a * b ∈ (I * J) ^ E := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    have h2 := Ideal.pow_right_mono hq E h1
    rw [Ideal.span_singleton_pow] at h2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨v, hv.symm⟩
  have hc : ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ b ∈ J ^ E, a + b = 1 := fun e =>
    Ideal.isCoprime_iff_exists.1 (h.pow (m := e) (n := E))
  obtain ⟨α, hα, β, hβ, hαβ⟩ := hc E
  refine ⟨α, fun a ha => ?_, fun e => ?_⟩
  · obtain ⟨v, hv⟩ := hm a ha β hβ
    exact ⟨a, v, by linear_combination hv - a * hαβ⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hc e
    obtain ⟨v, hv⟩ := hm α hα b hb
    exact ⟨α * a, Ideal.mul_mem_left _ _ ha, v, by linear_combination hv - α * hab⟩

theorem exists_conj {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤)
    (hu : uIdeal D r ≤ w) :
    ∃ J : Ideal (𝓞 D.F), IsCoprime (uIdeal D r) J ∧ uIdeal D r * J ≤ Ideal.span {(p : 𝓞 D.F)} := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hM : (D.ω - r) * (D.bar D.ω - r) = ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination hnm - r * htr
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hn
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hn
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, ← hM, Int.cast_one, Int.cast_natCast] at h
    refine hw ((Ideal.eq_top_iff_one w).2 (h ▸ w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r)))
      (w.mul_mem_left _ (w.mul_mem_right _ (hu (sub_mem_uIdeal D r))))))
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Int.cast_mul, Int.cast_natCast] at hM
  refine ⟨Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 D.disc_p
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    push_cast at h
    refine Ideal.isCoprime_iff_exists.2 ⟨x * p + y * (D.ω - D.bar D.ω) * (D.ω - r),
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ (p_mem_uIdeal D r)) (Ideal.mul_mem_left _ _ (sub_mem_uIdeal D r)),
      -(y * (D.ω - D.bar D.ω)) * (D.bar D.ω - r),
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
    linear_combination h + y * (D.ω + D.bar D.ω + D.tr) * htr - 4 * y * hnm
  · rw [uIdeal, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    rintro z (rfl | rfl | rfl | rfl)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    · exact Ideal.mem_span_singleton.2 (hM ▸ dvd_mul_right _ _)

section Grp

variable {S : Scheme.{0}}

theorem comp_mulN {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) : x ≫ mulN A n = x ^ n := by
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem exists_zeroLocus {B Z : Over S} [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (g : Z ⟶ B) (hg : g ^ n = 1) :
    ∃ (Y : Over S) (j : Y ⟶ Z), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ Z), (∃ z, z ≫ j = y) ↔ y ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B hn
  have hsec := GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion B n).hom _
    (Over.w (GlobalTheory.HTTorsRep.torsEta (A := B) n))
  have := GlobalTheory.HTTorsRep.mono_of_unit (GlobalTheory.HTTorsRep.torsEta (A := B) n)
  have := GlobalTheory.HTTorsRep.mono_ι (A := B) n
  have hEta : GlobalTheory.HTTorsRep.torsEta n ≫ torsion.ι B n = η[B] :=
    pullback.lift_fst _ _ _
  let g' : Z ⟶ torsion B n := pullback.lift g (toUnit Z) (by rw [comp_mulN, hg]; rfl)
  have hg' : g' ≫ torsion.ι B n = g := pullback.lift_fst _ _ _
  have hP := (IsPullback.of_hasPullback g' (GlobalTheory.HTTorsRep.torsEta n)).map (Over.forget S)
  refine ⟨pullback g' (GlobalTheory.HTTorsRep.torsEta n), pullback.fst _ _, inferInstance,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2, fun W y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [← hg', Category.assoc, ← Category.assoc (pullback.fst g' _), pullback.condition, Category.assoc,
      hEta, ← Category.assoc, toUnit_unique (z ≫ pullback.snd g' _) (toUnit W)]
    rfl
  · refine ⟨pullback.lift y (toUnit W) ?_, pullback.lift_fst _ _ _⟩
    rw [← cancel_mono (torsion.ι B n), Category.assoc, hg', h, Category.assoc, hEta]
    rfl

theorem exists_subgroup {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C]
    [IsCommMonObj C] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hC : IsAbelianScheme C) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (f : A ⟶ B) (g : A ⟶ C) [IsMonHom f] [IsMonHom g] :
    ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧
      ∀ (T : Over S) (x : T ⟶ A), InSub i x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  have := GlobalTheory.HTTorsRep.mono_ι (A := A) n
  have h0 : torsion.ι A n ^ n = 1 := by rw [← comp_mulN, GlobalTheory.HTTorsRep.ι_mulN]; rfl
  obtain ⟨Y, j, hj, hjo, hjc, hY⟩ := exists_zeroLocus hB hn (torsion.ι A n ≫ f)
    (by rw [← MonObj.pow_comp, h0, MonObj.one_comp])
  obtain ⟨K, k, hk, hko, hkc, hK⟩ := exists_zeroLocus hC hn (j ≫ torsion.ι A n ≫ g)
    (by rw [← MonObj.comp_pow, ← MonObj.pow_comp, h0, MonObj.one_comp, MonObj.comp_one])
  have hpts : ∀ (T : Over S) (x : T ⟶ A),
      InSub (k ≫ j ≫ torsion.ι A n) x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
    intro T x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← MonObj.comp_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, h0]
        simp only [MonObj.comp_one]
      · simpa only [Category.assoc] using (hY T (z ≫ k ≫ j)).1 ⟨z ≫ k, Category.assoc _ _ _⟩
      · simpa only [Category.assoc] using (hK T (z ≫ k)).1 ⟨z, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      let y : T ⟶ torsion A n := pullback.lift x (toUnit T) (by rw [comp_mulN, h1]; rfl)
      have hy : y ≫ torsion.ι A n = x := pullback.lift_fst _ _ _
      obtain ⟨z, hz⟩ := (hY T y).2 (by rw [← Category.assoc, hy, h2])
      obtain ⟨u, hu⟩ := (hK T z).2 (by rw [← Category.assoc, hz, ← Category.assoc, hy, h3])
      exact ⟨u, by rw [← Category.assoc, hu, ← Category.assoc, hz, hy]⟩
  have hm : Mono (k ≫ j ≫ torsion.ι A n) := inferInstance
  have hfin : IsFinite K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  have het : Etale K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  generalize k ≫ j ≫ torsion.ι A n = i at hpts hm
  obtain ⟨i1, i2, i3⟩ := (hpts K i).1 ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨G, hG⟩ := GlobalTheory.overScheme_grpObj_of_mono_factor S A K i hm
    (by
      have e : (i ⊗ₘ i) ≫ μ[A] = (fst K K ≫ i) * (snd K K ≫ i) := by
        rw [Hom.mul_def]; congr 1
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, i1]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i2]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i3]; simp)
    (by
      have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [e]
      exact (hpts _ _).2 ⟨one_pow _, MonObj.one_comp _, MonObj.one_comp _⟩)
    (by
      have e : i ≫ ι[A] = i⁻¹ := rfl
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [inv_pow, i1, inv_one]
      · rw [GrpObj.inv_comp, i2, inv_one]
      · rw [GrpObj.inv_comp, i3, inv_one])
  exact ⟨K, G, i, hG, hm, hfin, het, hpts⟩

end Grp

theorem charZero_of_isUnit {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : Γ(S, ⊤))) (k : Type) [Field k] (x : Sp k ⟶ S) :
    CharZero k := by
  have hpk : (p : k) ≠ 0 := by
    have := hp.map (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    rw [map_natCast] at this
    exact this.ne_zero
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    by_cases h : ringChar k = p
    · exact hpk (h ▸ h0)
    · have := (b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)).map β
      rw [map_natCast, h0] at this
      exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

theorem exists_kerUPart : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → IsTj r w j o o' ψ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) ∧ IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ b N _ _ hm r w j c hw hu _ _ S _ s hp o o' ψ hψ hT
  obtain ⟨⟨E, rfl⟩, hψh, hlin, -, -, ψ', hψ'h, hψψ', -⟩ := hψ
  obtain ⟨J, hJ, hJp⟩ := exists_conj D r w hw.ne_top hu
  obtain ⟨α, hα1, hα2⟩ := exists_elt _ _ _ hJ hJp E
  have hc : IsUnit ((p ^ E : ℕ) : Γ(S, ⊤)) := by rw [Nat.cast_pow]; exact hp.pow E
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : ∀ a, IsMonHom (o'.act.act a) := o'.act.hom
  obtain ⟨K, G, i, hG, hi, hfin, het, hpts⟩ :=
    exists_subgroup o.ab o'.ab o.ab hc ψ (o.act.act (algebraMap (𝓞 D.F) D.O α))
  have hnat : ∀ k : ℕ, o.act.act (k : D.O) = 𝟙 o.A ^ k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  have hcomb : ∀ {T : Over S} (x : T ⟶ o.A) (a u v : 𝓞 D.F), x ^ (p ^ E) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O (u * a + v * (p : 𝓞 D.F) ^ E)) = 1 := by
    intro T x a u v h1 h2
    rw [map_add (f := _), map_mul, map_mul, ← Nat.cast_pow, map_natCast, o.act.add, o.act.mul, o.act.mul, hnat,
      MonObj.comp_mul, ← Category.assoc, ← Category.assoc, h2, MonObj.comp_pow, Category.comp_id, h1,
      MonObj.one_comp, MonObj.one_comp, _root_.mul_one]
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      (x ≫ ψ = 1 ∧ ∃ e : ℕ, ES.KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
    intro T x
    rw [hpts]
    constructor
    · rintro ⟨h1, e, he⟩
      have h0 : x ^ (p ^ E) = 1 := by
        have : x ≫ ψ ≫ ψ' = 1 := by rw [← Category.assoc, h1, MonObj.one_comp]
        rwa [hψψ', MonObj.comp_pow, Category.comp_id] at this
      obtain ⟨a, ha, v, hv⟩ := hα2 e
      refine ⟨h0, h1, ?_⟩
      rw [hv, ← _root_.one_mul a]
      exact hcomb x a 1 v h0 (he a ha)
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h1, E, fun a ha => ?_⟩
      obtain ⟨u, v, rfl⟩ := hα1 a ha
      exact hcomb x α u v h0 h2
  refine ⟨K, G, i, hG, hi, hfin, het, fun a => ?_, ?_, key⟩
  · obtain ⟨h1, e, he⟩ := (key K i).2 ⟨𝟙 _, Category.id_comp _⟩
    refine (key K _).1 ⟨?_, e, fun z hz => ?_⟩
    · rw [Category.assoc, hlin, ← Category.assoc, h1, MonObj.one_comp]
    · rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, he z hz, MonObj.one_comp]
  · refine GlobalTheory.FinEtRank.isIsogDeg_of_card o.A K i hi hfin het _ ?_ fun k _ _ t => ?_
    · refine Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => ?_)
      have h := hu (p_mem_uIdeal D r)
      rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at h
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
    · haveI := charZero_of_isUnit b s hp k t
      obtain ⟨h1, h2⟩ := hT k t
      rw [hm, Nat.one_mul] at h2
      rw [← h2]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
      rw [← key]
      exact ⟨fun h => ⟨h.1, h1 g h.1 h.2⟩, fun h => ⟨h.1, 1, fun a ha => h.2 a (hu (by rwa [pow_one] at ha))⟩⟩

end GlobalTheory.UPel.HT.ES.KerUPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.AbTorsionGeomDescent

theorem finite_torsion_and_descent : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), (n : k) ≠ 0 → Finite {g : 𝟙_ (Over (Sp k)) ⟶ A // g ^ n = 1} ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ A), g ^ n = 1 → ∃ g₀ : 𝟙_ (Over (Sp k)) ⟶ A, g₀ ^ n = 1 ∧ g = toUnit (Over.mk x) ≫ g₀ := by
  intro k _ _ A _ _ hA n hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [h, Nat.cast_zero]) hn
    · exact h
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.TorusExtTorsion.finite_torsion_abelian_geomPoint A hA k (𝟙 _) n hn1
  · intro κ _ _ x g hg
    letI : Algebra k κ := (Spec.preimage x).hom.toAlgebra
    have hx : x = spMap (algebraMap k κ) := by
      show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨g₀, hg₀, hgl⟩ := GlobalTheory.AlgClosedDescent.torsion_descent (K := κ) A hA n hn hx g hg
    refine ⟨g₀, hg₀, ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hgl]
    congr 1

end GlobalTheory.AbTorsionGeomDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), (n : k) ≠ 0 → Finite {g : 𝟙_ (Over (Sp k)) ⟶ A // g ^ n = 1} ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ A), g ^ n = 1 → ∃ g₀ : 𝟙_ (Over (Sp k)) ⟶ A, g₀ ^ n = 1 ∧ g = toUnit (Over.mk x) ≫ g₀ := by
  first | (exact @GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent) | (exact GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent) | (intros; apply GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermConst

theorem germ_constFn_origin : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  intro R _ _ G _ O hO r
  have e := Scheme.Hom.appLE_map G.hom (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : O ≤ ⊤)).op
  have h : constFn G.hom O r = (G.left.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom (constFn G.hom ⊤ r) := by
    unfold constFn
    rw [← e]
    rfl
  rw [h, TopCat.Presheaf.germ_res_apply]
  rfl

end GlobalTheory.GermConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstantsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  first | exact @GlobalTheory.GermConst.germ_constFn_origin | exact GlobalTheory.GermConst.germ_constFn_origin | (intros; apply GlobalTheory.GermConst.germ_constFn_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolDeg

theorem idlAlong_vanishingIdeal_compl (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (f : R) (hf : (Ideal.span {f}).IsRadical) (hU : ∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal)
    (hrad : ∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical →
      (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) :
    idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  have hs := GlobalTheory.VanStalk.van_spec U.compl (ξ (closedPoint R))
  refine GlobalTheory.VanStalk.eq_of_forall_prime (hrad _ hs.1) hf fun q => ?_
  rw [idlAlong, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem]
  refine (hs.2 (PrimeSpectrum.comap (Scheme.stalkClosedPointTo ξ).hom q)).symm.trans ?_
  have e := congrArg (fun g => g q) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  change (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk (ξ (closedPoint R))) q ∈ (U.compl : Set S) ↔ _
  rw [e]
  change ξ q ∉ (U : Set S) ↔ _
  rw [hU q, not_not]

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span : ∀ (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (f : R), (Ideal.span {f}).IsRadical → (∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal) → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  first | exact @GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl | exact GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl | (intros; apply GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleDivIffIsAmpleLB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem presents_lbPow_toLB' {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) :
    Presents (k • D) (lbPow (toLB D) k) fun j => (j PUnit.unit).1.2 ^ k := by
  refine ⟨isLB_lbPow (isLB_toLB D) k, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB D) k).g i j = _ from lbPow_g _ k i j, Units.val_pow_eq_pow_val,
      LB.val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ k i).le hx)).nsmul k

theorem locus_rat {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) :
    locus D k ((presents_lbPow_toLB' D k).rat s) = (nonzeroLocus s : Set X) :=
  Set.ext fun _ => (presents_lbPow_toLB' D k).generatesAt_rat_iff s

theorem rat_mem_sec {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) : (presents_lbPow_toLB' D k).rat s ∈ Sec D k :=
  CartierDiv.mem_sections.1 ((presents_lbPow_toLB' D k).rat_mem s)

theorem ampleDiv_iff_isAmpleLB : ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] (D : CartierDiv X),
    AmpleDiv D ↔ IsAmpleLB (toLB D) := by
  intro X _ hc D
  constructor
  · intro h
    refine ⟨isLB_toLB D, hc, fun x => ?_⟩
    obtain ⟨k, hk, u, hu, U, hUa, hU, hx⟩ := h x
    obtain ⟨s, hs⟩ := (presents_lbPow_toLB' D k).exists_rat_eq (CartierDiv.mem_sections.2 hu)
    have e : nonzeroLocus s = U := SetLike.coe_injective (by rw [hU, ← locus_rat D k s, hs])
    exact ⟨k, hk, s, e ▸ hx, e ▸ hUa⟩
  · intro h x
    obtain ⟨k, hk, s, hx, ha⟩ := h.exists_affine x
    exact ⟨k, hk, _, rat_mem_sec D k s, nonzeroLocus s, ha, (locus_rat D k s).symm, hx⟩

end GlobalTheory.Desc
end
