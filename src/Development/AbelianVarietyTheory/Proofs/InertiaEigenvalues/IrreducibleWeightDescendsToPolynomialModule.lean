module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfield
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory

theorem matrix_intertwiner_descends : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  intro K _ e Γ m p _ _ A B ⟨X, hX, hXc⟩
  letI := e.toAlgebra
  obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (Matrix.ext h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual K ℂ, ℓ (X a b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hab ((Module.forall_dual_apply_eq_zero_iff K (X a b)).1 h)
  have h1 : ∀ (x : ℂ) (c : K), ℓ (x * e c) = ℓ x * c := by
    intro x c
    have : x * e c = c • x := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∀ (x : ℂ) (c : K), ℓ (e c * x) = c * ℓ x := by
    intro x c
    have : e c * x = c • x := by rw [Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul]
  refine ⟨X.map ℓ, ?_, fun γ => ?_⟩
  · intro h
    apply hℓ
    have := congrFun (congrFun h a) b
    simpa using this
  · ext i j
    have key := congrArg (fun M => ℓ (M i j)) (hXc γ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, h1, h2] at key ⊢
    exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  first | exact @GlobalTheory.matrix_intertwiner_descends | exact GlobalTheory.matrix_intertwiner_descends | (intros; apply GlobalTheory.matrix_intertwiner_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HwTransfer

open MvPolynomial

variable {L : Type} [Field L] {n : ℕ} {K : Type} [Field K]


open Classical in
noncomputable def evS {S : Type} [CommRing S] (c : L →+* L) (τ : L →+* K) (X Y : Matrix (Fin n) (Fin n) S) :
    (L →+* K) × Fin n × Fin n → S := fun p =>
  if p.1 = τ then X p.2.1 p.2.2
  else if p.1 = τ.comp c then Y p.2.2 p.2.1
  else if p.2.1 = p.2.2 then 1 else 0

theorem evS_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (c : L →+* L) (τ : L →+* K)
    (X Y : Matrix (Fin n) (Fin n) S) : ψ ∘ evS c τ X Y = evS c τ (X.map ψ) (Y.map ψ) := by
  funext p
  simp only [evS, Function.comp_apply, Matrix.map_apply]
  split_ifs <;> simp

noncomputable def defect {S : Type} [CommRing S] (φ : K →+* S) (c : L →+* L) (τ : L →+* K) {ι : Type} [Fintype ι]
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (X Y : Matrix (Fin n) (Fin n) S) (i : ι) : S :=
  (∏ a, X a a ^ (-lam a).toNat) * ∑ j, eval₂ φ (evS c τ X Y) (P i j) * φ (v j) -
    (∏ a, X a a ^ (lam a).toNat) * φ (v i)

theorem defect_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (φ : K →+* S) (c : L →+* L)
    (τ : L →+* K) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K)
    (lam : Fin n → ℤ) (X Y : Matrix (Fin n) (Fin n) S) (i : ι) :
    ψ (defect φ c τ P v lam X Y i) = defect (ψ.comp φ) c τ P v lam (X.map ψ) (Y.map ψ) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [defect, map_sub, map_mul, map_prod, map_pow, map_sum, hom_eval₂, Matrix.map_apply,
    RingHom.comp_apply]
  rw [← evS_map]
  rfl

theorem defect_eq_zero_iff {F : Type} [Field F] (φ : K →+* F) (c : L →+* L) (τ : L →+* K) {ι : Type}
    [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (X Y : Matrix (Fin n) (Fin n) F) (hX : ∀ a, X a a ≠ 0) (i : ι) :
    defect φ c τ P v lam X Y i = 0 ↔
      ∑ j, eval₂ φ (evS c τ X Y) (P i j) * φ (v j) = (∏ a, X a a ^ lam a) * φ (v i) := by
  have key : ∀ a, X a a ^ (lam a).toNat = X a a ^ (-lam a).toNat * X a a ^ lam a := by
    intro a
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hX a)]
    congr 1
    omega
  have hu : (∏ a, X a a ^ (-lam a).toNat) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hX a)
  simp only [defect, sub_eq_zero, key, Finset.prod_mul_distrib, mul_assoc]
  exact ⟨fun h => mul_left_cancel₀ hu h, fun h => by rw [h]⟩

end GlobalTheory.HwTransfer

namespace GlobalTheory.HwTransfer

open MvPolynomial

variable {L : Type} [Field L] {n : ℕ} {K : Type} [Field K]

theorem inv_map_of_mul {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) (G : Matrix (Fin n) (Fin n) A)
    (h : G⁻¹ * G = 1) : (G.map ψ)⁻¹ = G⁻¹.map ψ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero ψ) (map_one ψ)]

theorem defect_transfer (e : K →+* ℂ) (c : L →+* L) (τ : L →+* K) {ι : Type} [Fintype ι]
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (hK : ∀ B : GL (Fin n) K, B.val.BlockTriangular id → ∀ i, defect (RingHom.id K) c τ P v lam B.val (B⁻¹).val i = 0)
    (B : GL (Fin n) ℂ) (hB : B.val.BlockTriangular id) (i : ι) :
    defect e c τ P v lam B.val (B⁻¹).val i = 0 := by
  haveI : CharZero K := RingHom.charZero e
  haveI : Infinite K := inferInstance
  classical
  obtain ⟨D, hD⟩ : ∃ D : MvPolynomial (Fin n × Fin n) K, D = ∏ a, X (a, a) := ⟨_, rfl⟩
  let A := Localization.Away D
  let φA : K →+* A := (algebraMap (MvPolynomial (Fin n × Fin n) K) A).comp C
  let G : Matrix (Fin n) (Fin n) A := fun a b => if b < a then 0 else algebraMap (MvPolynomial (Fin n × Fin n) K) A (X (a, b))
  have hGtri : G.BlockTriangular id := fun a b h => by
    simp only [G]
    rw [if_pos (show b < a from h)]
  have hDA : algebraMap (MvPolynomial (Fin n × Fin n) K) A D =
      ∏ a, algebraMap (MvPolynomial (Fin n × Fin n) K) A (X (a, a)) := by
    rw [← map_prod]
    exact congrArg _ hD
  have hdet : G.det = algebraMap (MvPolynomial (Fin n × Fin n) K) A D := by
    rw [Matrix.det_of_upperTriangular hGtri, hDA]
    simp [G]
  have hunit : IsUnit G.det := hdet ▸ IsLocalization.Away.algebraMap_isUnit D
  have hGinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit

  have hy : defect φA c τ P v lam G G⁻¹ i = 0 := by
    obtain ⟨⟨f, s⟩, hfs⟩ := IsLocalization.surj (Submonoid.powers D) (defect φA c τ P v lam G G⁻¹ i)
    have hf : ∀ x : Fin n × Fin n → K, eval x D ≠ 0 → eval x f = 0 := by
      intro x hx
      let ψ : A →+* K := IsLocalization.Away.lift D (g := eval x) (Ne.isUnit hx)
      have hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin n × Fin n) K) A r) = eval x r := IsLocalization.Away.lift_eq D _
      set M : Matrix (Fin n) (Fin n) K := G.map ψ with hM
      have hMtri : M.BlockTriangular id := fun a b h => by
        show ψ (G a b) = 0
        rw [hGtri h, map_zero]
      have hMd : ∀ a, M a a = x (a, a) := fun a => by
        show ψ (G a a) = x (a, a)
        simp [G, hψ]
      have hMdet : M.det ≠ 0 := by
        rw [Matrix.det_of_upperTriangular hMtri, Finset.prod_congr rfl (fun a _ => hMd a)]
        simpa [hD] using hx
      let BK := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
      have h1 := hK BK hMtri i
      have h2 : ψ (defect φA c τ P v lam G G⁻¹ i) = 0 := by
        rw [defect_map, ← inv_map_of_mul ψ G hGinv]
        have hc : ψ.comp φA = RingHom.id K := RingHom.ext fun k => by simp [φA, hψ]
        rw [hc]
        simpa [BK, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.coe_units_inv] using h1
      have h3 := congrArg ψ hfs
      rw [map_mul, h2, zero_mul, hψ] at h3
      exact h3.symm
    have hfD : f * D = 0 := by
      apply MvPolynomial.funext
      intro x
      rw [map_mul, map_zero]
      by_cases hx : eval x D = 0
      · rw [hx, mul_zero]
      · rw [hf x hx, zero_mul]
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact Finset.prod_ne_zero_iff.2 fun a _ => X_ne_zero _
    have hf0 : f = 0 := (mul_eq_zero.1 hfD).resolve_right hD0
    rw [hf0, map_zero] at hfs
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units A s)).1 hfs

  have hBdiag : eval₂ e (fun p => B.val p.1 p.2) D ≠ 0 := by
    have : B.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit |>.ne_zero
    rw [Matrix.det_of_upperTriangular hB] at this
    simpa [hD] using this
  let ψ : A →+* ℂ := IsLocalization.Away.lift D (g := eval₂Hom e (fun p => B.val p.1 p.2)) (Ne.isUnit hBdiag)
  have hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin n × Fin n) K) A r) = eval₂ e (fun p => B.val p.1 p.2) r := IsLocalization.Away.lift_eq D _
  have hGB : G.map ψ = B.val := by
    ext a b
    by_cases h : b < a
    · show ψ (G a b) = B.val a b
      rw [hGtri h, map_zero, hB h]
    · show ψ (G a b) = B.val a b
      simp [G, h, hψ]
  have hc : ψ.comp φA = e := RingHom.ext fun k => by simp [φA, hψ]
  have := congrArg ψ hy
  rw [defect_map, ← inv_map_of_mul ψ G hGinv, hGB, hc, map_zero] at this
  simpa [Matrix.coe_units_inv] using this

end GlobalTheory.HwTransfer

namespace GlobalTheory.HwTransfer

open MvPolynomial

theorem diag_ne_zero {n : ℕ} {F : Type} [Field F] (B : GL (Fin n) F) (hB : B.val.BlockTriangular id) (a : Fin n) :
    B.val a a ≠ 0 := by
  have h : B.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  rw [Matrix.det_of_upperTriangular hB] at h
  exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)

end GlobalTheory.HwTransfer


open MvPolynomial GlobalTheory.HwTransfer in
theorem GlobalTheory.hwAt_of_hwAtF : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ)
    (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (a : NG.AlgWt L n) (ω : W →ₛₗ[e] a.W),
    (∀ (κ : Type) (v : κ → W), LinearIndependent K v → LinearIndependent ℂ fun x => ω (v x)) →
    Submodule.span ℂ (Set.range ω) = ⊤ → (∀ γ w, ω (ρ γ w) = a.ρ γ (ω w)) →
    ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ τ lam → a.HWAt (e.comp τ) lam := by
  intro L _ _ _ n K _ e c hc W _ _ ρ a ω hind hspan hint τ lam h
  classical
  obtain ⟨ι, hι, hdec, b, P, hP, v, hv0, hv⟩ := h
  have hcomp : ∀ σ σ' : L →+* K, e.comp σ = e.comp σ' ↔ σ = σ' := fun σ σ' =>
    ⟨fun h => RingHom.ext fun x => e.injective (RingHom.congr_fun h x), fun h => h ▸ rfl⟩
  have hconj : ComplexEmbedding.conjugate (e.comp τ) = e.comp (τ.comp c) := by
    ext x
    have h5 := IsCMField.complexEmbedding_complexConj L (e.comp τ) x
    rw [ComplexEmbedding.conjugate_coe_eq]
    simp only [RingHom.comp_apply, hc] at h5 ⊢
    exact h5.symm
  have hli : LinearIndependent ℂ (fun i => ω (b i)) := hind ι b b.linearIndependent
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => ω (b i)) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis ι ℂ a.W := Module.Basis.mk hli hsp
  let f : (L →+* K) × Fin n × Fin n → (L →+* ℂ) × Fin n × Fin n := fun p => (e.comp p.1, p.2)
  have hev : ∀ (g : (L →+* ℂ) × Fin n × Fin n → ℂ) (Q : MvPolynomial ((L →+* K) × Fin n × Fin n) K),
      eval g (rename f (map e Q)) = eval₂ e (g ∘ f) Q := fun g Q => by rw [eval_rename, eval_map]
  refine ⟨ι, hι, hdec, b', fun i j => rename f (map e (P i j)), ?_, fun i => e (v i), ?_, ?_⟩
  · intro γ γ₀ hγ
    have h1 := hP γ γ₀ hγ
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.toMatrix_apply, Module.Basis.mk_apply, ← hint, ← b.sum_repr (ρ γ (b j)), map_sum]
    simp only [LinearMap.map_smulₛₗ]
    have hb' : ∀ k, ω (b k) = b' k := fun k => (Module.Basis.mk_apply hli hsp k).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hb', map_sum, map_smul, Module.Basis.repr_self]
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hev]
    have h2 := congrFun (congrFun h1 i) j
    rw [LinearMap.toMatrix_apply] at h2
    rw [h2]
    change e (eval₂ (RingHom.id K) _ (P i j)) = _
    rw [hom_eval₂, RingHom.comp_id]
    rfl
  · intro h0
    apply hv0
    funext i
    exact e.injective (by simpa using congrFun h0 i)
  · intro B hB
    have hK : ∀ B : GL (Fin n) K, B.val.BlockTriangular id → ∀ i,
        defect (RingHom.id K) c τ P v lam B.val (B⁻¹).val i = 0 := by
      intro B hB i
      rw [defect_eq_zero_iff _ c τ P v lam _ _ (diag_ne_zero B hB)]
      have h3 := congrFun (hv B hB) i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h3
      have hF : NX.evPtF c τ B = evS c τ B.val (B⁻¹).val := by
        funext p
        unfold NX.evPtF evS
        split_ifs <;> rfl
      rw [hF] at h3
      simp only [RingHom.id_apply]
      exact h3
    have hC := fun i => defect_transfer e c τ P v lam hK B hB i
    have hevC : NG.evPt (e.comp τ) B ∘ f = evS c τ B.val (B⁻¹).val := by
      funext p
      simp only [NG.evPt, evS, Function.comp_apply, f, hconj, hcomp]
    funext i
    have h4 := (defect_eq_zero_iff e c τ P v lam _ _ (diag_ne_zero B hB) i).1 (hC i)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, hev, hevC]
    exact h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgWtDualRead

theorem isAlgWeight_of_hwAtF_dual : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  intro L _ _ _ n K _ e c hc W _ _ _ ρ κ _ _ b ρC hρC τ lam hw
  obtain ⟨ι, _, _, b', P, hP, -⟩ := hw
  classical
  let bd := b.dualBasis
  let A : Matrix κ ι K := bd.toMatrix b'
  let B : Matrix ι κ K := b'.toMatrix bd
  let f : (L →+* K) × Fin n × Fin n → (L →+* K) × Fin n × Fin n := fun p => (p.1.comp c, p.2.2, p.2.1)
  let Q : κ → κ → MvPolynomial ((L →+* K) × Fin n × Fin n) K := fun i j =>
    ∑ l, ∑ k, MvPolynomial.C (A j k) * MvPolynomial.rename f (P k l) * MvPolynomial.C (B l i)
  have key : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : Formalism.AUTREP.GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      ∀ i j, LinearMap.toMatrix b b (ρ γ) i j =
        MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (Q i j) := by
    intro γ γ₀ hm i j
    have hinv := hP γ⁻¹ γ₀⁻¹ (GlobalTheory.WtDual.match_inv γ γ₀ hm)
    have hγ := GlobalTheory.WtDual.mem_rationalUnitaryGroup_of_matrix_match γ γ₀ hm
    have e1 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = Matrix.transpose (LinearMap.toMatrix b b (ρ γ)) := by
      rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    have e2 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = A * LinearMap.toMatrix b' b' (ρ.dual γ⁻¹) * B :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bd b' bd b' _).symm
    have e3 : LinearMap.toMatrix b b (ρ γ) i j = LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) j i := by
      rw [e1]; rfl
    rw [e3, e2]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    simp only [hinv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    refine congrArg (fun g => MvPolynomial.eval g (P k l)) (funext fun p => ?_)
    simp only [Function.comp_apply, f, RingHom.comp_apply]
    rw [GlobalTheory.WtDual.inv_entry γ₀ hγ, hc]
    rfl
  refine ⟨inferInstance, κ, inferInstance, inferInstance, Pi.basisFun ℂ κ,
    fun i j => MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n => (e.comp p.1, p.2)) (MvPolynomial.map e (Q i j)), ?_⟩
  intro γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_eq_toMatrix', hρC γ, Matrix.map_apply, key γ γ₀ hm i j, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
  rfl

end GlobalTheory.AlgWtDualRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  first | exact @GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual | exact GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual | (intros; apply GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeigh
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeigh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

section Irr

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem pair_inv (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (γ : ReciprocityTheory.Aut.GQ L n) (x y : VV ℂ lam) :
    pairBK lam (mtRep emb lam γ x) (tenRep emb lam γ y) = pairBK lam x y :=
  (pairBK_apply lam _ _).trans ((pairingBInvariantK_holds ℂ ι n lam
    (mtwEmb emb (mtwRat (L := L) (n := n) γ)) (x : VV ℂ lam).1
    (y : VV ℂ lam).1).trans (pairBK_apply lam x y).symm)

theorem tenIrr_conj (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr emb lam) :
    TenIrr (mtwConj emb) lam := by
  unfold TenIrr
  rw [mtRep_eq_tenRep, mtwConj_conj]
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hd := GlobalTheory.WtDual.dual_isIrreducible (mtRep emb lam) h
  let Φ : VV ℂ lam →ₗ[ℂ] Module.Dual ℂ (VV ℂ lam) := (pairBK lam).flip
  have hΦ : ∀ x y, Φ y x = pairBK lam x y := fun x y => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact (pairingBNondegenerate_holds ℂ ι n lam).2 y fun x => by
      rw [← hΦ, hy]
      rfl
  have hdim : Module.finrank ℂ (VV ℂ lam) = Module.finrank ℂ (Module.Dual ℂ (VV ℂ lam)) :=
    (Subspace.dual_finrank_eq).symm
  let E := LinearMap.linearEquivOfInjective Φ hinj hdim
  have hE : ∀ y, E y = Φ y := fun y => rfl
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam).dual (tenRep emb lam) E.symm
    (fun g f => ?_) hd
  apply E.injective
  rw [LinearEquiv.apply_symm_apply, hE]
  obtain ⟨y, rfl⟩ := E.surjective f
  rw [LinearEquiv.symm_apply_apply, hE]
  ext x
  rw [hΦ, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hΦ]
  have := pair_inv emb lam g ((mtRep emb lam g⁻¹) x) y
  rw [Representation.self_inv_apply] at this
  exact this

end Irr
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

section Omega

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)

def bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
  Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge

theorem bC_apply (i : VVIdx lam) : bC e lam i = mapVV e lam (bVV K lam i) := by
  simp [bC]

variable {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def omegaV : Module.Dual K W →ₛₗ[e] Module.Dual ℂ (VV ℂ lam) where
  toFun f := (bC e lam).constr ℂ fun i => e (f (T.symm (bVV K lam i)))
  map_add' f g := by
    rw [← ((bC e lam).constr ℂ).map_add]
    congr 1
    funext i
    simp only [Pi.add_apply, LinearMap.add_apply, map_add]
  map_smul' c f := by
    rw [← ((bC e lam).constr ℂ).map_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_mul]

theorem omegaV_bC (f : Module.Dual K W) (i : VVIdx lam) :
    omegaV e lam T f (bC e lam i) = e (f (T.symm (bVV K lam i))) := by
  simp [omegaV, Module.Basis.constr_basis]

theorem omegaV_mapVV (f : Module.Dual K W) (x : VV K lam) :
    omegaV e lam T f (mapVV e lam x) = e (f (T.symm x)) := by
  conv_lhs => rw [← (bVV K lam).sum_repr x]
  conv_rhs => rw [← (bVV K lam).sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, ← bC_apply, LinearMap.map_smul, omegaV_bC, smul_eq_mul, map_mul, RingHom.id_apply, LinearEquiv.map_smul, LinearMap.map_smul]

end Omega
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

section Props

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)
  {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def coordK : Module.Dual K W →ₗ[K] VV K lam :=
  (bVV K lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval K W (T.symm (bVV K lam i))

def coordC : Module.Dual ℂ (VV ℂ lam) →ₗ[ℂ] VV ℂ lam :=
  (bC e lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval ℂ (VV ℂ lam) (bC e lam i)

theorem coordK_ker : LinearMap.ker (coordK lam T) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have h1 : ∀ i, f (T.symm (bVV K lam i)) = 0 := by
    intro i
    have h0 := congrArg (bVV K lam).equivFun hf
    simp only [coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero] at h0
    simpa using congrFun h0 i
  have h2 : f ∘ₗ T.symm.toLinearMap = 0 := (bVV K lam).ext fun i => by simpa using h1 i
  ext w
  have := LinearMap.congr_fun h2 (T w)
  simpa using this

theorem coordC_omegaV (f : Module.Dual K W) : coordC e lam (omegaV e lam T f) = mapVV e lam (coordK lam T f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordC, coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    LinearMap.pi_apply, Module.Dual.eval_apply, map_sum, LinearMap.map_smulₛₗ, omegaV_bC, bC_apply, omegaV_mapVV]

theorem omegaV_li (κ : Type) (v : κ → Module.Dual K W) (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun x => omegaV e lam T (v x) := by
  refine LinearIndependent.of_comp (coordC e lam) ?_
  refine LinearIndependent.of_comp (VV ℂ lam).subtype ?_
  have h1 : LinearIndependent K fun x => ((coordK lam T (v x) : VV K lam) : Pol K ι n) :=
    (hv.map' (coordK lam T) (coordK_ker lam T)).map' (VV K lam).subtype (Submodule.ker_subtype _)
  convert Formalism.L2.Col.linearIndependent_map e _ h1 using 1
  funext x
  simp [coordC_omegaV, mapVV_coe]

theorem omegaV_coord (i : VVIdx lam) :
    omegaV e lam T ((bVV K lam).coord i ∘ₗ T.toLinearMap) = (bC e lam).coord i := by
  refine (bC e lam).ext fun j => ?_
  rw [omegaV_bC]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem omegaV_span : Submodule.span ℂ (Set.range (omegaV e lam T)) = ⊤ := by
  classical
  rw [eq_top_iff, ← (bC e lam).dualBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨_, by rw [omegaV_coord, Module.Basis.coe_dualBasis]⟩

end Props
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

theorem omegaV_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type}
    [Field K] (e : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam)
    (hT : ∀ γ x, T (ρ γ x) = rhoVr emb lam (mtwRat (L := L) (n := n) γ) (T x)) (γ : ReciprocityTheory.Aut.GQ L n) (f : Module.Dual K W) :
    omegaV e lam T (ρ.dual γ f) = (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) := by
  refine (bC e lam).ext fun j => ?_
  have h1 : (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) (bC e lam j) =
      omegaV e lam T f (mapVV e lam (rhoVr emb lam (mtwRat (L := L) (n := n) γ⁻¹) (bVV K lam j))) := by
    rw [GlobalTheory.ConjTwist.mapVV_rhoVr, bC_apply]
    rfl
  rw [h1, bC_apply, omegaV_mapVV, omegaV_mapVV]
  show e (f (ρ γ⁻¹ (T.symm (bVV K lam j)))) = _
  congr 2
  apply T.injective
  rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.MtContraHw


open GlobalTheory.CoefModel _root_.Formalism.L2.Col in
theorem GlobalTheory.mtRatDual_hw : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm c hc lam hten W _ _ _ ρ T hT t lam0 hw
  have h' := GlobalTheory.MtContraHw.tenIrr_conj (fun t => e.comp (emb t)) lam hten
  have hwa := GlobalTheory.hwAt_of_hwAtF L n K e c hc (Module.Dual K W) ρ.dual
    (GlobalTheory.WtDual.dualWt (mtWt (fun t => e.comp (emb t)) lam hten)) (GlobalTheory.MtContraHw.omegaV e lam T)
    (GlobalTheory.MtContraHw.omegaV_li e lam T) (GlobalTheory.MtContraHw.omegaV_span e lam T)
    (GlobalTheory.MtContraHw.omegaV_comm e emb lam ρ T hT) (emb t) lam0 hw
  exact mtWt_hw_dual (fun t => e.comp (emb t)) hinj hcm lam hten h' t _ lam0 (GlobalTheory.WtDual.isDual_dualWt _) hwa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeighStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  first | exact @GlobalTheory.mtRatDual_hw | exact GlobalTheory.mtRatDual_hw | (intros; apply GlobalTheory.mtRatDual_hw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleAlgebraicWeightSubrep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleAlgebraicWeightSubrep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgSubrep

theorem toMatrix_sandwich {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (e : Module.Basis κ ℂ U) (π : V →ₗ[ℂ] U) (s : U →ₗ[ℂ] V)
    (f : V →ₗ[ℂ] V) :
    LinearMap.toMatrix e e (π ∘ₗ f ∘ₗ s) =
      LinearMap.toMatrix b e π * LinearMap.toMatrix b b f * LinearMap.toMatrix e b s := by
  rw [LinearMap.toMatrix_comp e b e, LinearMap.toMatrix_comp e b b, Matrix.mul_assoc]

theorem eval_sandwich {ι κ σ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (B : Matrix ι κ ℂ)
    (P : ι → ι → MvPolynomial σ ℂ) (x : σ → ℂ) (M : Matrix ι ι ℂ)
    (hM : M = fun k l => MvPolynomial.eval x (P k l)) :
    A * M * B =
      fun i j => MvPolynomial.eval x (∑ k, ∑ l, MvPolynomial.C (A i k) * P k l * MvPolynomial.C (B l j)) := by
  funext i j
  simp only [Matrix.mul_apply, Finset.sum_mul]
  subst hM
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [Finset.sum_comm]

end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem isAlgWeight_subrep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V)
    (hρ : Formalism.AUTREP.IsAlgWeight L n ρ) (S : Subrepresentation ρ) :
    Formalism.AUTREP.IsAlgWeight L n S.toRepresentation := by
  classical
  obtain ⟨hfin, ι, _, _, b, P, hP⟩ := hρ
  haveI := hfin
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S.toSubmodule
  let π : V →ₗ[ℂ] S.toSubmodule := Submodule.linearProjOfIsCompl S.toSubmodule C hC
  let e := Module.Free.chooseBasis ℂ S.toSubmodule
  refine ⟨inferInstance, Module.Free.ChooseBasisIndex ℂ S.toSubmodule, inferInstance, inferInstance, e,
    fun i j => ∑ k, ∑ l, MvPolynomial.C (LinearMap.toMatrix b e π i k) * P k l *
      MvPolynomial.C (LinearMap.toMatrix e b S.toSubmodule.subtype l j), ?_⟩
  intro γ γ₀ hγ
  have hres : S.toRepresentation γ = π ∘ₗ ρ γ ∘ₗ S.toSubmodule.subtype := by
    ext x : 1
    have hm : ρ γ x ∈ S.toSubmodule := S.apply_mem_toSubmodule γ x.2
    have h1 := Submodule.linearProjOfIsCompl_apply_left hC ⟨ρ γ x, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [show π (ρ γ ↑x) = _ from h1]
    apply Subtype.ext
    rfl
  have h4 := hP γ γ₀ hγ
  have h5 := toMatrix_sandwich b e π S.toSubmodule.subtype (ρ γ)
  exact (congrArg (LinearMap.toMatrix e e) hres).trans
    (h5.trans (eval_sandwich (LinearMap.toMatrix b e π) (LinearMap.toMatrix e b S.toSubmodule.subtype) P _ _ h4))
end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem exists_irreducible_algWt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V), Formalism.AUTREP.IsAlgWeight L n ρ → ∃ (a : NG.AlgWt L n) (j : a.W →ₗ[ℂ] V), Function.Injective j ∧ ∀ γ x, j (a.ρ γ x) = ρ γ (j x) := by
  intro L _ _ _ n V _ _ _ ρ hρ
  haveI := hρ.1
  obtain ⟨S, hS⟩ := GlobalTheory.PiIsotypic.exists_irreducible_subrep ρ
  exact ⟨⟨S.toSubmodule, S.toRepresentation, isAlgWeight_subrep L n ρ hρ S, hS⟩,
    S.toSubmodule.subtype, S.toSubmodule.injective_subtype, fun γ x => rfl⟩

end GlobalTheory.AlgSubrep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleAlgebraicWeightSubrepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_algebraicWeight_subrep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V), Formalism.AUTREP.IsAlgWeight L n ρ → ∃ (a : NG.AlgWt L n) (j : a.W →ₗ[ℂ] V), Function.Injective j ∧ ∀ γ x, j (a.ρ γ x) = ρ γ (j x) := by
  first | exact @GlobalTheory.AlgSubrep.exists_irreducible_algWt | exact GlobalTheory.AlgSubrep.exists_irreducible_algWt | (intros; apply GlobalTheory.AlgSubrep.exists_irreducible_algWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModule
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.WtDescent

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CoefModel

theorem weight_descends : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm hcov c hc W _ _ _ ρ hρ lam0 hw
  classical
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom⟩
  obtain ⟨t₀, -⟩ := hcov σ
  let N := Module.finrank K W
  let b : Module.Basis (Fin N) K W := Module.finBasis K W
  let A : ReciprocityTheory.Aut.GQ L n → Matrix (Fin N) (Fin N) K := fun γ => LinearMap.toMatrix b b (ρ γ)
  let ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (Fin N → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin N → ℂ)) :
        Matrix (Fin N) (Fin N) ℂ →* Module.End ℂ (Fin N → ℂ)).comp
      (((e.mapMatrix : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) K →* Matrix (Fin N) (Fin N) ℂ).comp
        (((LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin N) (Fin N) K) :
          Module.End K W →* Matrix (Fin N) (Fin N) K).comp ρ))
  have hρC : ∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e := by
    intro γ
    show LinearMap.toMatrix' (Matrix.toLin' ((LinearMap.toMatrix b b (ρ γ)).map e)) = _
    rw [LinearMap.toMatrix'_toLin']
  have halg : Formalism.AUTREP.IsAlgWeight L n ρC :=
    GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight L n K e c hc W ρ (Fin N) b ρC hρC (emb t₀) (lam0 t₀) (hw t₀)
  haveI : Nontrivial W := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible ρ hρ
  have hN : 0 < N := Module.finrank_pos
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, j, hj, hjρ⟩ := GlobalTheory.T.exists_irreducible_algebraicWeight_subrep L n (Fin N → ℂ) ρC halg
  obtain ⟨lam, Tc, hTc⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists L n ι (fun t => e.comp (emb t)) hinj hcm hcov a
  have hmatch : ∀ γ : ReciprocityTheory.Aut.GQ L n, (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
      Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
      ((mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
    intro γ
    exact (congrArg (fun g : GL (Fin n) (ReciprocityTheory.Aut.AL L) => (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)))
      (mtwInc_mtwRatFun γ)).symm
  let bK := bVV K lam
  let bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge
  have hbC : ∀ i, bC i = mapVV e lam (bK i) := fun i => Module.Basis.mk_apply _ _ _
  have hrepr : ∀ x i, bC.repr (mapVV e lam x) i = e (bK.repr x i) := by
    intro x i
    have hx : mapVV e lam x = bC.equivFun.symm (fun i => e (bK.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← bK.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, hbC]
    rw [hx, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let B : ReciprocityTheory.Aut.GQ L n → Matrix (VVIdx lam) (VVIdx lam) K :=
    fun γ => LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ))
  have hB : ∀ γ, LinearMap.toMatrix bC bC (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ)) = (B γ).map e := by
    intro γ
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    show _ = e (LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ)) i k)
    rw [LinearMap.toMatrix_apply, hbC, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hrepr]
  let M : VV ℂ lam →ₗ[ℂ] (Fin N → ℂ) := j ∘ₗ Tc.symm.toLinearMap
  have hM : ∀ γ y, M (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = ρC γ (M y) := by
    intro γ y
    have h1 : Tc.symm (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = a.ρ γ (Tc.symm y) := by
      apply Tc.injective
      rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [M, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hjρ]
  let X : Matrix (Fin N) (VVIdx lam) ℂ := LinearMap.toMatrix bC (Pi.basisFun ℂ (Fin N)) M
  have hX0 : X ≠ 0 := by
    intro h
    have hM0 : M = 0 := by
      have := congrArg (Matrix.toLin bC (Pi.basisFun ℂ (Fin N))) h
      simpa [X] using this
    haveI := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible a.ρ a.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    apply hx
    apply hj
    have : M (Tc x) = j x := by simp [M]
    rw [← this, hM0, LinearMap.zero_apply, map_zero]
  have hXrel : ∀ γ, X * (B γ).map e = (A γ).map e * X := by
    intro γ
    rw [← hB, show (A γ).map e = LinearMap.toMatrix' (ρC γ) from (hρC γ).symm,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext fun y => hM γ y
  obtain ⟨XK, hXK0, hXK⟩ := GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield K e (ReciprocityTheory.Aut.GQ L n) (VVIdx lam) (Fin N) B A ⟨X, hX0, hXrel⟩
  let Φ : VV K lam →ₗ[K] W := Matrix.toLin bK b XK
  have hΦ : ∀ γ x, Φ (rhoVr emb lam (mtwRat (L := L) (n := n) γ) x) = ρ γ (Φ x) := by
    intro γ x
    have h : Φ ∘ₗ rhoVr emb lam (mtwRat (L := L) (n := n) γ) = ρ γ ∘ₗ Φ := by
      apply (LinearMap.toMatrix bK b).injective
      rw [LinearMap.toMatrix_comp bK bK b, LinearMap.toMatrix_comp bK b b, LinearMap.toMatrix_toLin]
      exact hXK γ
    exact LinearMap.congr_fun h x
  have hsurj : Function.Surjective Φ := by
    let S : Subrepresentation ρ := ⟨LinearMap.range Φ, by
      rintro γ _ ⟨x, rfl⟩
      exact ⟨_, hΦ γ x⟩⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hXK0
      have hr : LinearMap.range Φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hΦ0 : Φ = 0 := LinearMap.range_eq_bot.1 hr
      have := congrArg (LinearMap.toMatrix bK b) hΦ0
      simpa [Φ] using this
    · have hr : LinearMap.range Φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  haveI : FiniteDimensional K (VV K lam) := Module.Finite.of_basis bK
  have hdimC : Module.finrank ℂ a.W ≤ N := by
    have := LinearMap.finrank_le_finrank_of_injective hj
    simpa using this
  have hdimA : Module.finrank ℂ a.W = Fintype.card (VVIdx lam) := by
    rw [Tc.finrank_eq, Module.finrank_eq_card_basis bC]
  have hdimK : Module.finrank K (VV K lam) = Fintype.card (VVIdx lam) := Module.finrank_eq_card_basis bK
  have hle : N ≤ Module.finrank K (VV K lam) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have heq : Module.finrank K (VV K lam) = Module.finrank K W := by
    show Module.finrank K (VV K lam) = N
    omega
  have hinjΦ : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj
  let Φb : VV K lam ≃ₗ[K] W := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩
  have h1 : ∀ y, Φb y = Φ y := fun y => rfl
  have hT : ∀ γ x, Φb.symm (ρ γ x) = rhoVr emb lam (mtwRat (L := L) (n := n) γ) (Φb.symm x) := by
    intro γ x
    apply Φb.injective
    rw [Φb.apply_symm_apply, h1, hΦ, ← h1, Φb.apply_symm_apply]
  have hten : Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam := by
    refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv a.ρ _ Tc (fun γ v => ?_) a.irr
    rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ)]
    rfl
  refine ⟨lam, fun t => (GlobalTheory.mtRatDual_hw L n ι K e emb hinj hcm c hc lam hten W ρ Φb.symm hT t (lam0 t) (hw t)).symm,
    Φb.symm, fun γ γ₀ hm x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hm
  exact hT γ x

end GlobalTheory.WtDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModuleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_weight_descends_to_polynomial_module : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  first | exact @GlobalTheory.WtDescent.weight_descends | exact GlobalTheory.WtDescent.weight_descends | (intros; apply GlobalTheory.WtDescent.weight_descends <;> assumption)
end
