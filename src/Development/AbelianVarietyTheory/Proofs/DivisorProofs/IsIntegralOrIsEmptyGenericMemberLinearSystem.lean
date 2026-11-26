module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.GenericMember

noncomputable def genVar (k : Type) [Field k] (N : ℕ) {X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (i : Fin N) : Γ(X', ⊤) :=
  f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv
    (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))

noncomputable def genSec (k : Type) [Field k] (N : ℕ) {X X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X)
    (b : Fin N → L.Sec) : (L.pull π).Sec :=
  ∑ i, genVar k N f' i • secPull (b i) π

end GlobalTheory.GenericMember
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericLinearFormPrime
open MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.GenericForm

variable (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ)

def polyEquiv : MvPolynomial (Fin N) k ⊗[k] A ≃+* MvPolynomial (Unit × Fin N) A :=
  ((Algebra.TensorProduct.comm k (MvPolynomial (Fin N) k) A).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k A).toRingEquiv).trans
    (renameEquiv A (Equiv.punitProd (Fin N)).symm).toRingEquiv

theorem polyEquiv_X_tmul (i : Fin N) (x : A) :
    polyEquiv k A N (X i ⊗ₜ x) = C x * X ((), i) := by
  simp [polyEquiv, smul_eq_C_mul]

theorem polyEquiv_one_tmul (x : A) : polyEquiv k A N (1 ⊗ₜ x) = C x := by
  simp [polyEquiv, smul_eq_C_mul]

variable {k A N}

def genForm (a : Fin N → A) : MvPolynomial (Fin N) k ⊗[k] A := ∑ i, X i ⊗ₜ a i

theorem polyEquiv_genForm (a : Fin N → A) :
    polyEquiv k A N (genForm (k := k) a) = linForm a () := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genForm, linForm, map_sum, polyEquiv_X_tmul]

theorem isDomain_tensor : IsDomain (MvPolynomial (Fin N) k ⊗[k] A) :=
  Function.Injective.isDomain (polyEquiv k A N).toRingHom
    (polyEquiv k A N).injective

theorem genForm_ne_zero (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    genForm (k := k) a ≠ 0 := by
  intro h
  have h1 := congrArg (polyEquiv k A N) h
  rw [polyEquiv_genForm, map_zero, ← linFormEquiv_X_of_mem (ι := Unit) a hu (Set.mem_univ ())] at h1
  exact X_ne_zero _ ((linFormEquiv a Set.univ j hu).injective (h1.trans (map_zero _).symm))

theorem map_span_genForm (a : Fin N → A) :
    (Ideal.span {genForm (k := k) a}).map (polyEquiv k A N) = Ideal.span {linForm a ()} := by
  rw [Ideal.map_span, Set.image_singleton, polyEquiv_genForm]

theorem isPrime_span_genForm (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    (Ideal.span {genForm (k := k) a}).IsPrime := by
  have hp : (Ideal.span {linForm a ()}).IsPrime := by
    have := isPrime_span_linForm (ι := Unit) a hu Set.univ
    rwa [Set.image_univ, Set.range_unique] at this
  have : Ideal.span {genForm (k := k) a} =
      (Ideal.span {linForm a ()}).map (polyEquiv k A N).symm := by
    rw [Ideal.map_span, Set.image_singleton, ← polyEquiv_genForm (k := k) a, RingEquiv.symm_apply_apply]
  rw [this]
  exact Ideal.map_isPrime_of_equiv _

theorem eq_zero_of_one_tmul_mem (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) {x : A}
    (hx : (1 : MvPolynomial (Fin N) k) ⊗ₜ[k] x ∈ Ideal.span {genForm (k := k) a}) : x = 0 := by
  have h1 := Ideal.mem_map_of_mem (polyEquiv k A N) hx
  rw [map_span_genForm, polyEquiv_one_tmul] at h1
  have h2 : C x ∈ RingHom.ker (linFormElim a hu (Set.univ : Set Unit)) := by
    rw [ker_linFormElim, Set.image_univ, Set.range_unique]
    exact h1
  rw [RingHom.mem_ker, algHom_C, algebraMap_eq, C_eq_zero] at h2
  exact h2

theorem span_genericForm_isPrime_or_eq_top :
    ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ) (a : Fin N → A)
      (j : Fin N), IsUnit (a j) → ∀ t : FractionRing (MvPolynomial (Fin N) k) ⊗[k] A,
      t = ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k))
        (MvPolynomial.X i) ⊗ₜ[k] a i →
      t ≠ 0 ∧ (Ideal.span {t} = ⊤ ∨ (Ideal.span {t}).IsPrime ∧
        ∀ x : A, (1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] x ∈ Ideal.span {t} → x = 0) := by
  intro k A _ _ _ _ N a j hu t ht
  let P := MvPolynomial (Fin N) k
  let K := FractionRing P
  let B := P ⊗[k] A
  haveI : IsDomain B := isDomain_tensor
  let φ : B →ₐ[k] K ⊗[k] A :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)
  letI : Algebra B (K ⊗[k] A) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap B (K ⊗[k] A) x = φ x := fun _ => rfl
  haveI : IsScalarTower P B (K ⊗[k] A) := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap B (K ⊗[k] A)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    change φ (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors P)
  haveI hL : IsLocalization M (K ⊗[k] A) :=
    IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K H
  have hkA : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨p, hp, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp ?_
    refine Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := P) (B := A) hkA ?_
    rw [map_zero]
    exact h
  have hinj : Function.Injective (algebraMap B (K ⊗[k] A)) := IsLocalization.injective _ hM
  have ht0 : t = algebraMap B (K ⊗[k] A) (genForm (k := k) a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, hφ, genForm, map_sum]
    rfl
  have hspan : Ideal.span {t} = (Ideal.span {genForm (k := k) a}).map (algebraMap B (K ⊗[k] A)) := by
    rw [Ideal.map_span, Set.image_singleton, ht0]
  refine ⟨?_, ?_⟩
  · rw [ht0]
    exact fun h => genForm_ne_zero (k := k) a hu (hinj (h.trans (map_zero _).symm))
  haveI hQ := isPrime_span_genForm (k := k) a hu
  by_cases hd : Disjoint (M : Set B) (Ideal.span {genForm (k := k) a} : Set B)
  · right
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hspan]
      exact IsLocalization.isPrime_of_isPrime_disjoint M (K ⊗[k] A) _ hQ hd
    · have h1 : (1 : K) ⊗ₜ[k] x = algebraMap B (K ⊗[k] A) ((1 : P) ⊗ₜ[k] x) := by
        rw [hφ, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rw [h1, hspan] at hx
      have h2 := IsLocalization.under_map_of_isPrime_disjoint M (K ⊗[k] A) hQ hd
      have h3 : (1 : P) ⊗ₜ[k] x ∈ ((Ideal.span {genForm (k := k) a}).map
          (algebraMap B (K ⊗[k] A))).under B := hx
      rw [h2] at h3
      exact eq_zero_of_one_tmul_mem a hu h3
  · left
    obtain ⟨m, hmM, hmQ⟩ := Set.not_disjoint_iff.1 hd
    rw [hspan]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmQ)
      (IsLocalization.map_units (K ⊗[k] A) (⟨m, hmM⟩ : M))

end GlobalTheory.GenericForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChart
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.GenericMember

theorem genSec_chart_ne_zero_and_isPrime : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  intro k _ N X X' _ f f' π L hL b V hne hW c hVc j hj
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  intro e he1 he2
  haveI : Nonempty V := hne.to_subtype
  set a : Fin N → Γ(X, V) := fun i => resG X hVc ((b i).f c) with ha
  set t₀ : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) :=
    ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i with ht
  obtain ⟨ht0, hI⟩ := GlobalTheory.GenericForm.span_genericForm_isPrime_or_eq_top k Γ(X, V) N a j hj t₀ rfl
  have hWU : π ⁻¹ᵁ V ≤ (L.pull π).U (fun _ => c) := fun x hx => Set.mem_iInter.2 fun _ => hVc hx
  have hsum : ∀ J, (genSec k N f' π L b).f J =
      ∑ i, resG X' le_top (genVar k N f' i) * (secPull (b i) π).f J := by
    intro J
    let F : (L.pull π).Sec →+ Γ(X', (L.pull π).U J) :=
      { toFun := fun s => s.f J, map_zero' := rfl, map_add' := fun _ _ => rfl }
    show F (∑ i, genVar k N f' i • secPull (b i) π) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  have key : resG X' hWU ((genSec k N f' π L b).f (fun _ => c)) = e t₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum (fun _ => c), map_sum, ht, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hq : algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i =
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] (1 : Γ(X, V))) *
          ((1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] a i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hq, map_mul, he1, he2]
    congr 1
    · have e2 : f'.appTop ≫ X'.presheaf.map (homOfLE (le_top : (L.pull π).U (fun _ => c) ≤ ⊤)).op ≫
          X'.presheaf.map (homOfLE hWU).op = f'.appLE ⊤ (π ⁻¹ᵁ V) le_top := by
        simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv.hom
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))) e2
    · have e1 : π.appLE (L.U c) ((L.pull π).U (fun _ => c)) ((GlobalTheory.chartPullPull L π).le (fun _ => c)) ≫
          X'.presheaf.map (homOfLE hWU).op = X.presheaf.map (homOfLE hVc).op ≫ π.app V := by
        rw [Scheme.Hom.naturality]
        simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((b i).f c)) e1
  have hid : (secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ =
      Ideal.span {e t₀} := by
    rw [ideal_secIdeal (LB.isLB_pull hL π) _ ⟨π ⁻¹ᵁ V, hW⟩ (fun _ => c) hWU]
    exact congrArg (fun x => Ideal.span {x}) key
  have hmap : Ideal.span {e t₀} = Ideal.map e (Ideal.span {t₀}) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine ⟨fun h0 => ht0 (e.injective ?_), ?_⟩
  · rw [map_zero, ← key, h0, map_zero]
  · rw [hid]
    rcases hI with h | ⟨hp, hx⟩
    · left
      rw [hmap, h, Ideal.map_top]
    · right
      refine ⟨?_, ?_⟩
      · haveI := hp
        rw [hmap]
        exact Ideal.map_isPrime_of_equiv e
      · rw [eq_bot_iff]
        intro x hx'
        rw [Ideal.mem_bot]
        apply hx x
        rw [Ideal.mem_comap, ← he1, Ideal.mem_span_singleton'] at hx'
        obtain ⟨d, hd⟩ := hx'
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm d, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, hd]

end GlobalTheory.GenericMember
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  first | exact @GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | exact GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | (intros; apply GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeCharts
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory.SubschemeIntegral

theorem isPreirreducible_univ_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hU : ∀ a, IsOpen (U a)) (hcov : ∀ x, ∃ a, x ∈ U a) (hirr : ∀ a, IsPreirreducible (U a))
    (hmeet : ∀ a b, (U a).Nonempty → (U b).Nonempty → (U a ∩ U b).Nonempty) :
    IsPreirreducible (Set.univ : Set X) := by
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨a, hxa⟩ := hcov x
  obtain ⟨b, hyb⟩ := hcov y
  obtain ⟨z, hza, hzu, hzb⟩ := hirr a u (U b) hu (hU b) ⟨x, hxa, hxu⟩
    (by obtain ⟨w, h1, h2⟩ := hmeet a b ⟨x, hxa⟩ ⟨y, hyb⟩; exact ⟨w, h1, h2⟩)
  obtain ⟨w, _, hw⟩ := hirr b u v hu hv ⟨z, hzb, hzu⟩ ⟨y, hyb, hyv⟩
  exact ⟨w, trivial, hw⟩

theorem fromSpec_mem_support {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (hU : IsAffineOpen U.1) (P : PrimeSpectrum Γ(Y, U.1)) (h : I.ideal U ≤ P.asIdeal) :
    hU.fromSpec P ∈ (I.support : Set Y) := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩
  change hU.fromSpec P ∈ I.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  have : hU.fromSpec P ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(Y, U.1)) :=
    ⟨P, (PrimeSpectrum.mem_zeroLocus _ _).mpr h, rfl⟩
  rw [hU.fromSpec_image_zeroLocus] at this
  exact this.1

theorem exists_cover {Y : Scheme.{0}} (I : Y.IdealSheafData) {ι : Type} (W : ι → Y.affineOpens)
    (hW : ⨆ a, (W a).1 = ⊤) (x : I.subscheme) :
    ∃ a y, (I.subschemeCover.f (W a)) y = x := by
  have hx : I.subschemeι x ∈ (⨆ a, (W a).1) := by rw [hW]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  haveI := I.subschemeCover.map_prop (W a)
  have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact ha
  obtain ⟨y, hy⟩ := this
  exact ⟨a, y, hy⟩

theorem isEmpty_spec_top {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (h : I.ideal U = ⊤) : IsEmpty (Spec (I.subschemeCover.X U)) := by
  haveI : Subsingleton (Γ(Y, U) ⧸ I.ideal U) := Ideal.Quotient.subsingleton_iff.mpr h
  refine ⟨fun y => ?_⟩
  have : Subsingleton (I.subschemeCover.X U) := this
  exact y.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by rw [Subsingleton.elim (1 : I.subschemeCover.X U) 0]; exact zero_mem _))

theorem isIntegral_or_isEmpty_subscheme : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  intro Y I ι W hW hI hm
  by_cases hex : ∃ a, (I.ideal (W a)).IsPrime
  · left
    obtain ⟨a₀, ha₀⟩ := hex
    haveI hred : ∀ a, _root_.IsReduced (I.subschemeCover.X (W a)) := by
      intro a
      rcases hI a with h | h
      · haveI : Subsingleton (Γ(Y, W a) ⧸ I.ideal (W a)) := Ideal.Quotient.subsingleton_iff.mpr h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
      · haveI := h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
    let 𝒰 : I.subscheme.OpenCover := Scheme.Cover.mkOfCovers ι (fun a => Spec (I.subschemeCover.X (W a)))
      (fun a => I.subschemeCover.f (W a)) (exists_cover I W hW) (fun a => I.subschemeCover.map_prop (W a))
    haveI : ∀ a : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X a) := fun a => by
      change AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X (W a))); haveI := hred a; infer_instance
    haveI : AlgebraicGeometry.IsReduced I.subscheme := IsReduced.of_openCover I.subscheme 𝒰
    have hpt : ∀ a (ha : (I.ideal (W a)).IsPrime), ∃ x : I.subscheme,
        I.subschemeι x = (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ := by
      intro a ha
      have := fromSpec_mem_support I (W a) (W a).2 ⟨I.ideal (W a), ha⟩ le_rfl
      rw [← I.range_subschemeι] at this
      exact this
    have hrange : ∀ a (x : I.subscheme), I.subschemeι x ∈ (W a).1 → x ∈ Set.range (I.subschemeCover.f (W a)) := by
      intro a x hx
      haveI := I.subschemeCover.map_prop (W a)
      have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
        rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact hx
      exact this
    have hp : ∀ a, (Set.range (I.subschemeCover.f (W a))).Nonempty → (I.ideal (W a)).IsPrime := by
      rintro a ⟨_, y, _⟩
      rcases hI a with h | h
      · exact ((isEmpty_spec_top I (W a) h).false y).elim
      · exact h
    haveI : IrreducibleSpace I.subscheme := by
      obtain ⟨x₀, -⟩ := hpt a₀ ha₀
      have hpre : IsPreirreducible (Set.univ : Set I.subscheme) := by
        refine isPreirreducible_univ_of_cover (fun a => Set.range (I.subschemeCover.f (W a))) (fun a => ?_)
          (fun x => ?_) (fun a => ?_) (fun a b ha hb => ?_)
        · haveI := I.subschemeCover.map_prop (W a); exact (I.subschemeCover.f (W a)).isOpenEmbedding.isOpenMap.isOpen_range
        · obtain ⟨a, y, hy⟩ := exists_cover I W hW x; exact ⟨a, y, hy⟩
        · rcases hI a with h | h
          · haveI := isEmpty_spec_top I (W a) h
            rw [Set.range_eq_empty]; exact isPreirreducible_empty
          · haveI : IsDomain (I.subschemeCover.X (W a)) := by
              change IsDomain (Γ(Y, W a) ⧸ I.ideal (W a)); haveI := h; infer_instance
            rw [← Set.image_univ]
            exact ((IrreducibleSpace.isIrreducible_univ _).image _
              (I.subschemeCover.f (W a)).continuous.continuousOn).isPreirreducible
        · obtain ⟨x, hx⟩ := hpt a (hp a ha)
          refine ⟨x, hrange a x ?_, hrange b x ?_⟩
          · rw [hx, ← SetLike.mem_coe, ← (W a).2.range_fromSpec]; exact ⟨_, rfl⟩
          · rw [hx]; exact hm a b (hp a ha) (hp b hb).ne_top
      haveI : PreirreducibleSpace I.subscheme := ⟨hpre⟩
      exact { toNonempty := ⟨x₀⟩ }
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · right
    refine ⟨fun x => ?_⟩
    obtain ⟨a, y, -⟩ := exists_cover I W hW x
    have h : I.ideal (W a) = ⊤ := (hI a).resolve_right (fun h => hex ⟨a, h⟩)
    exact (isEmpty_spec_top I (W a) h).false y

end GlobalTheory.SubschemeIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeChartsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  first | exact @GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme | exact GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme | (intros; apply GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtension
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem isAffineOpen_preimage_and_tensor_equiv_of_isPullback : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  intro k K _ _ _ X X' f f' π h V hV
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  refine ⟨hV.preimage π, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top)
      (CommRingCat.ofHom (algebraMap k K)) (π.app V)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  letI : Algebra K Γ(X', π ⁻¹ᵁ V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X', π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI : Algebra k Γ(X', π ⁻¹ᵁ V) :=
    ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom).comp
      (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k Γ(X, V) Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun r => by
    exact (congrArg (fun φ => φ.hom r) hpo'.w).symm
  haveI : Algebra.IsPushout k K Γ(X, V) Γ(X', π ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'.flip
  refine ⟨(Algebra.IsPushout.equiv k K Γ(X, V) Γ(X', π ⁻¹ᵁ V)).toRingEquiv, fun a => ?_, fun c => ?_⟩
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtensionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_base_change_over_field_extension : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  first | exact @GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback | exact GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback | (intros; apply GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_prime_comap_bot_lies_over_genericPoint :
    ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V →
      ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime),
        P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  intro X Y _ π V hV hW P hP h
  have e := IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl
  have e2 : π (hW.fromSpec ⟨P, hP⟩) =
      hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩) := by
    have := congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e
    exact this.symm
  set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef
  have hq : q.asIdeal = ⊥ := by
    rw [← h, Scheme.Hom.app_eq_appLE]
    rfl
  have hne : Nonempty V := ⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩
  have hgen : q = genericPoint (Spec Γ(X, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [e2, hgen, genericPoint_eq_of_isOpenImmersion]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime), P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  first | exact @GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | exact GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | (intros; apply GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystem
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory

theorem GenericMember.isIntegral_or_isEmpty_zeroScheme : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  intro k _ N X X' _ _ f f' π hP L hL b hb

  have loc : ∀ x : X, ∃ (V : X.Opens) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N),
      IsAffineOpen V ∧ x ∈ V ∧ IsUnit (resG X hVc ((b j).f c)) := by
    intro x
    have hx : x ∈ (⨆ i, nonzeroLocus (b i)) := hb.ge (Set.mem_univ x)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hj
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hc
    have hVc : V ≤ L.U c := hVle.trans (X.basicOpen_le _)
    refine ⟨V, c, hVc, j, hVa, hxV, ?_⟩
    have h1 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((b j).f c)
    have h2 := h1.map (X.presheaf.map (homOfLE hVle).op).hom
    convert h2 using 1
    simp only [resG]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  choose V c hVc j hVa hxV hu using loc
  have hW : ∀ x, IsAffineOpen (π ⁻¹ᵁ V x) := fun x => (GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)).1
  have key : ∀ x, (genSec k N f' π L b).f (fun _ => c x) ≠ 0 ∧
      ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩ = ⊤ ∨
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).IsPrime ∧
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).comap
          (π.app (V x)).hom = ⊥) := fun x => by
    obtain ⟨-, e, he1, he2⟩ := GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)
    exact GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart k N X X' f f' π L hL b (V x) ⟨x, hxV x⟩ (hW x) (c x) (hVc x) (j x) (hu x) e he1 he2
  refine ⟨genSec k N f' π L b, fun h0 => ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact (key x).1 (by rw [h0]; rfl)
  · refine GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts X' _ X (fun x => ⟨π ⁻¹ᵁ V x, hW x⟩) ?_ (fun x => ?_) (fun x y hx hy => ?_)
    · refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ⟨π z, hxV (π z)⟩
    · rcases (key x).2 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · rcases (key x).2 with h | h
      · exact absurd h hx.ne_top
      · have hg := GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint X X' π (V x) (hVa x) (hW x) _ hx h.2
        show π _ ∈ V y
        rw [hg]
        exact (genericPoint_spec X).mem_open_set_iff (V y).isOpen |>.2 ⟨y, trivial, hxV y⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystemStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isEmpty_generic_member_linearSystem : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  first | exact @GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme | exact GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme | (intros; apply GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme <;> assumption)
end
