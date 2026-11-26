module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKCentAf

theorem baseChange_centralizer_comm (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [Ring A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y ↔
      y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  let ad : B →ₗ[K] B := LinearMap.mulRight K γ - LinearMap.mulLeft K γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id k k) f y = LinearMap.lTensor k f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have had : ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) - ((1 : k) ⊗ₜ[K] γ) * y = LinearMap.lTensor k ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add (f := _), ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact k hex
  intro y
  rw [← sub_eq_zero, had, hex' y]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, hmap z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hmap z).symm⟩

theorem commute_of_centralizer (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [CommRing A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) (y z : k ⊗[K] B)
    (hy : y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y)
    (hz : z * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * z) : y * z = z * y := by
  obtain ⟨y', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent y).1 hy
  obtain ⟨z', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent z).1 hz
  rw [← map_mul, ← map_mul, mul_comm]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_iff_mem (P : Pair G) (y : G.C) :
    y * (P.γ : G.C) = (P.γ : G.C) * y ↔
      y ∈ Set.range ((Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro h
    have hy : y ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      simpa using h.symm
    rw [hcsa] at hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [hcsa]; exact w.2
    rw [Subalgebra.mem_centralizer_iff] at hw
    exact (hw _ rfl).symm

theorem conj_commute (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t)
    (a : G.GAf) (ha : a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self)) :
    (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
      ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) *
        (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom P.γ with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C) := rfl
  have hδ : ((P.toAf x t hx P.self : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
  simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
  rw [hδ] at h1
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
    calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
      _ = U * (x⁻¹ * A * x) := by group
  rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]

theorem twCent_comm : ∀ {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
    ∀ a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self),
    ∀ b ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self), a * b = b * a := by
  intro p _ G P x t hx a ha b hb
  have hc := commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _ (cent_iff_mem P) _ _
    (conj_commute P x t hx a ha) (conj_commute P x t hx b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

end GlobalTheory.LKCentAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory.HeightUnique


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_linSubst {R : Type} [CommRing R] {B N n m : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst P (_root_.GlobalTheory.ChowHt.linSubst M f) = _root_.GlobalTheory.ChowHt.linSubst (M * P) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_one {R : Type} [CommRing R] {B N : ℕ} (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst (1 : Matrix (Fin N) (Fin N) R) f = f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  have hX : (fun p : Fin B × Fin N => ∑ k, C ((1 : Matrix (Fin N) (Fin N) R) p.2 k) * X (p.1, k)) = X := by
    funext p
    simp [Matrix.one_apply, apply_ite C, ite_mul]
  rw [hX, aeval_X_left_apply]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_ne_zero {R : Type} [CommRing R] {B N n : ℕ} {M : Matrix (Fin N) (Fin n) R}
    {P : Matrix (Fin n) (Fin N) R} (h : M * P = 1) {f : MvPolynomial (Fin B × Fin N) R} (hf : f ≠ 0) :
    _root_.GlobalTheory.ChowHt.linSubst M f ≠ 0 := by
  intro h0
  apply hf
  have key := _root_.GlobalTheory.HeightUnique.linSubst_linSubst M P f
  rw [h0, h, _root_.GlobalTheory.HeightUnique.linSubst_one] at key
  rw [← key]
  simp [_root_.GlobalTheory.ChowHt.linSubst]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_C_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R) (c : R)
    (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst M (C c * f) = C c * _root_.GlobalTheory.ChowHt.linSubst M f := by
  simp [_root_.GlobalTheory.ChowHt.linSubst]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.exists_right_inv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective w.mulVecLin
    (by rw [Matrix.range_mulVecLin, hw])
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have key := congrArg LinearMap.toMatrix' hg
  have hw' : LinearMap.toMatrix' w.mulVecLin = w := (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hw'] at key

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma isWeightedHomogeneous_aeval_of_isWeightedHomogeneous {R M σ τ : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {w' : τ → M} {g : σ → MvPolynomial τ R} (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (aeval g f) m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [aeval_monomial, algebraMap_eq, ← hf (mem_support_iff.mp hd), Finsupp.weight_apply,
    ← zero_add (d.sum fun i c => c • w i)]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i))


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_homog {R : Type} [Field R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin N) R} (hf : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a (_root_.GlobalTheory.ChowHt.linSubst M f) := by
  rw [_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block] at hf ⊢
  unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hf ⊢
  unfold _root_.GlobalTheory.ChowHt.linSubst
  refine isWeightedHomogeneous_aeval_of_isWeightedHomogeneous (fun p => ?_) hf
  apply IsWeightedHomogeneous.sum
  intro k _
  have hw : _root_.GlobalTheory.Chow.blockWeight p = _root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n) := by
    simp [_root_.GlobalTheory.Chow.blockWeight]
  rw [hw, ← zero_add (_root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n))]
  exact (isWeightedHomogeneous_C _ _).mul (isWeightedHomogeneous_X _ _ _)


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.gaussAbs_C {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) (c : K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c : MvPolynomial σ K) = w c := by
  classical
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [C_apply, support_monomial, if_neg hc]
    simp [Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_C_mul_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) {c : K}
    (hc : c ≠ 0) (g : MvPolynomial σ K) : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c * g) = w c * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have hs : (C c * g).support = g.support := by
    ext s
    simp [coeff_C_mul, hc]
  rw [hs]
  simp_rw [coeff_C_mul, map_mul, Real.toNNReal_mul (apply_nonneg w c)]
  rw [← NNReal.mul_finset_sup, NNReal.coe_mul, Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_pos_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K)
    {g : MvPolynomial σ K} (hg : g ≠ 0) : 0 < _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hg
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have h1 : (w (AddMonoidAlgebra.coeff g s)).toNNReal ≤ g.support.sup fun t => (w (AddMonoidAlgebra.coeff g t)).toNNReal :=
    Finset.le_sup (f := fun t => (w (AddMonoidAlgebra.coeff g t)).toNNReal) (mem_support_iff.mpr hs)
  have h2 : 0 < w (AddMonoidAlgebra.coeff g s) := w.pos_iff.mpr hs
  exact_mod_cast lt_of_lt_of_le (Real.toNNReal_pos.mpr h2) h1

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma finsum_log_finitePlace_add_sum_log_norm_embedding {K : Type} [Field K] [NumberField K] {c : K}
    (hc : c ≠ 0) : ∑ᶠ v : FinitePlace K, Real.log (v c) + ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = 0 := by
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq c hc, ← Real.log_finprod (fun v => v.pos_iff.mpr hc), FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv]
  ring


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.formHeight_C_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (hN : 0 < N) (δ : ℕ)
    {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) {c : F} (hc : c ≠ 0) :
    _root_.GlobalTheory.ChowHt.formHeight δ w A (C c * f) = _root_.GlobalTheory.ChowHt.formHeight δ w A f := by
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.HeightUnique.exists_right_inv hw
  have hLf : _root_.GlobalTheory.ChowHt.linSubst w f ≠ 0 := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hfin : ∀ v : FinitePlace F, Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w (C c * f))) =
      Real.log (v c) + Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w f)) := by
    intro v
    rw [_root_.GlobalTheory.HeightUnique.linSubst_C_mul, gaussAbs_C_mul_of_ne_zero v hc,
      Real.log_mul (v.pos_iff.mpr hc).ne' (gaussAbs_pos_of_ne_zero v hLf).ne']
  have harch : ∀ σ : F →+* ℂ, _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ (C c * f))) =
      Real.log ‖σ c‖ + _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ f)) := by
    intro σ
    have hQ : A σ * (A σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hA σ))
    have hmf : map σ f ≠ 0 := fun h0 => hf (map_injective σ σ.injective (by rw [h0, map_zero]))
    have hg := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hQ hmf
    have hgh := _root_.GlobalTheory.HeightUnique.linSubst_homog (A σ) (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring a f ha σ)
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
    have hC : (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) ≠ 0 := by simpa using hσc
    have hCh : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => 0) (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) :=
      (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt _ _).mpr fun _ => isWeightedHomogeneous_C _ _
    rw [map_mul, map_C, _root_.GlobalTheory.HeightUnique.linSubst_C_mul,
      _root_.ReciprocityTheory.MultiplicativeHeights.sphere_mean_mul_multihomogeneous _root_.ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B N (fun _ => 0) a _ _ hC hg hCh hgh]
    congr 1
    haveI := _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := B) hN
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [eval_C]
  have hsuppc : (Function.support fun v : FinitePlace F => Real.log (v c)).Finite := by
    simpa [_root_.GlobalTheory.HeightUnique.gaussAbs_C] using _root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite (C c : MvPolynomial Unit F) (by simpa using hc)
  unfold _root_.GlobalTheory.ChowHt.formHeight
  congr 1
  simp_rw [hfin, harch]
  rw [finsum_add_distrib hsuppc (_root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hLf)]
  simp only [Finset.sum_add_distrib]
  linarith [finsum_log_finitePlace_add_sum_log_norm_embedding hc]

end GlobalTheory.HeightUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem herm_negDef_of_sigPosH_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro hdet hsig y hy
  have hneg : ∀ i, hA.eigenvalues i < 0 := by
    intro i
    have hnp : ¬ 0 < hA.eigenvalues i := by
      intro h
      have : IsEmpty {i : Fin n // 0 < hA.eigenvalues i} := Fintype.card_eq_zero_iff.mp hsig
      exact this.false ⟨i, h⟩
    have hne : hA.eigenvalues i ≠ 0 := by
      intro h0
      apply hdet
      rw [hA.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
    exact lt_of_le_of_ne (not_lt.mp hnp) hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set z : Fin n → ℂ := star U *ᵥ y with hz
  have hyz : y = U *ᵥ z := by rw [hz, mulVec_mulVec, hUU', one_mulVec]
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [hyz, h, mulVec_zero]
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have key : star y ⬝ᵥ A *ᵥ y = star z ⬝ᵥ diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ z := by
    conv_lhs => rw [hspec]
    rw [hz, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Complex.re_sum]
  have hterm : ∀ i, (star z i * ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * z i)).re =
      hA.eigenvalues i * Complex.normSq (z i) := by
    intro i
    rw [show (RCLike.ofReal (hA.eigenvalues i) : ℂ) = (hA.eigenvalues i : ℂ) from rfl,Pi.star_apply, mul_left_comm, Complex.re_ofReal_mul]
    congr 1
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin n)))]
  refine Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hneg i).le (Complex.normSq_nonneg _))
    ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos (hneg j) (Complex.normSq_pos.mpr hj)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZeroStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negDef_of_hermitianMatrixPositiveIndex_eq_zero : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | (exact @GlobalTheory.herm_negDef_of_sigPosH_eq_zero) | (exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero) | (intros; apply GlobalTheory.herm_negDef_of_sigPosH_eq_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf ToricRatioConjugates)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem exists_toricSum_ne_zero [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ∃ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ ∧ T₀ ≠ 0 := by
  obtain ⟨i₀, -⟩ := hφ (Classical.arbitrary _)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ _ χ hφ hχ.1 hχ.2.2.1 ⟨i₀, by omega⟩
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ hU hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  exact ⟨Λ s, t1, hΛ.ne_zero_nat hχ.1 hs⟩

theorem condQ_ne_bot {𝔣 : Ideal (OF E)} (hb : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ :=
  mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem exists_twistedSum [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ)
    (Q : Finset (HeightOneSpectrum (OF E))) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) : ∃ T, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T := by
  have h0 := OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 _ χ hU hs hb (dvd_mul_right _ _)
      (condQ_ne_bot hb Q) hχ.1 hχ.2.2.1 (fun y hy => h0 y (hatOUnits_mono hle hy)) q.out
  exact ⟨_, PicFin.finite_picO E _ (condQ_ne_bot hb Q), S, hS, rfl⟩

theorem isTwistedSum_one {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} (T : ℂ) :
    IsTwistedSum φ s κ c χ 1 T ↔ IsToricSum φ s κ c χ T := by
  simp [IsTwistedSum, IsToricSum, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF]

theorem conjChar_one {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) : conjChar g (1 : PicO c →* ℂˣ) = 1 :=
  MonoidHom.ext fun _ => Units.ext (map_one g)

theorem toricRatioConjugates_of_transport (hT : TwistedTransport) : ToricRatioConjugates := by
  intro E _ _ _ K _ _ _ d δ ι I _ φ s κ 𝔣 Q χ hU hK hd hδ hφ hι hs hκ hb hQ hχ
  obtain ⟨Ω₀, hΩ₀, halg, hconj⟩ := hT K d δ ι hK hd hδ
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hU hφ hs hb hχ
  choose T hTw using exists_twistedSum hU hφ hs hb hχ Q
  have hD : IsDatum ι φ s κ 𝔣 Q χ := ⟨hU, hφ, hι, hs, hκ, hb, hQ, hχ⟩
  have hD₀ : IsDatum ι φ s κ 𝔣 ∅ χ := ⟨hU, hφ, hι, hs, hκ, hb, fun _ h => absurd h (Finset.notMem_empty _), hχ⟩
  have hT₀' := (isTwistedSum_one T₀).2 hT₀
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  refine ⟨T₀, T, e ▸ hT₀, h0, hTw, fun ψ => ?_, fun Ω _ _ _ j art hj ha g σ t hgE hgl hσ ht ψ => ⟨?_, ?_⟩⟩
  · rw [← coordIn_div E hd hs κ hΩ₀, div_eq_mul_inv]
    exact (halg E I φ s κ 𝔣 Q χ hD ψ _ (hTw ψ)).mul (halg E I φ s κ 𝔣 ∅ χ hD₀ 1 _ hT₀').inv
  · obtain ⟨Ω₁, hΩ₁, h⟩ := hconj Ω j art hj ha g σ t hσ ht
    have hw : IsConjWt φ g κ κ := fun i i' hi => by
      have : φ i = φ i' := RingHom.ext fun x => (hgE i x).symm.trans (hi x)
      rw [(hφ (φ i)).unique (Or.inl rfl) (Or.inl this)]
    have hc : IsConjChar φ s κ g χ χ := ⟨fun y => (hgl y).symm, hχ.2.2.1⟩
    have h1 := h E I φ s κ 𝔣 Q χ hD κ χ hw hc ψ _ _ (hTw ψ) (hTw _)
    have h2 := h E I φ s κ 𝔣 ∅ χ hD₀ κ χ hw hc 1 T₀ T₀ hT₀' (by rw [conjChar_one]; exact hT₀')
    have hl := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ (upIdele K E t)
    have hm : ((modF t : ℝ) : ℂ) ≠ 0 := by
      have := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero 1 (1 : HChar K) t
      rw [lamF, pow_one] at this
      exact right_ne_zero_of_mul this
    rw [← coordIn_div E hd hs κ hΩ₀, map_div₀, h1, h2, coordIn_div E hd hs κ hΩ₁, conjChar_one]
    simp only [MonoidHom.one_apply, Units.val_one, mul_one]
    have := (conjChar g ψ (classOf K (condQ 𝔣 Q) t)).ne_zero
    field_simp
  · have := PicFin.finite_picO E _ (condQ_ne_bot hb Q)
    exact (conjChar g ψ).isOfFinOrder (isOfFinOrder_of_finite _)

end GlobalTheory.ToricTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbOverSumInjective
open NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.RealRepBij

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

theorem span_range_eq_top {F B : Type} [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B]
    [IsSimpleRing B] [FiniteDimensional F B] {n : ℕ} (σ : F →+* ℂ)
    (f : B →+* Matrix (Fin n) (Fin n) ℂ) (hdim : Module.finrank F B = n ^ 2)
    (hf : ∀ a, f (algebraMap F B a) = Matrix.scalar (Fin n) (σ a)) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a := fun a => by
    rw [hf, Matrix.algebraMap_eq_diagonal]; rfl
  let g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ := { f with commutes' := hg }
  let L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)
  have hn : 0 < n := by
    have := Module.finrank_pos (R := F) (M := B)
    rw [hdim] at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right
      (not_subsingleton _)
  have hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective L.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj
  refine eq_top_iff.2 fun m _ => ?_
  clear ‹m ∈ ⊤›
  obtain ⟨x, rfl⟩ := hsurj m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have : L.toLinearMap (c ⊗ₜ b) = c • f b := by
      dsimp only [L]
      rw [AlgHom.toLinearMap_apply]
      erw [Algebra.TensorProduct.lift_tmul]
      rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

variable {K F : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
  [Field F] [NumberField F] [NumberField.IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

end GlobalTheory.UPel.HT.RealRepBij
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeEmbeddingEqTop
namespace GlobalTheory.EmbeddingRangeSpanTop

open NumberField

theorem span_range_embedding_eq_top (F : Type) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : NumberField.InfinitePlace F) ↦
      (NumberField.InfinitePlace.embedding v : F → ℂ) a) = ⊤ := by
  classical
  let L : NumberField.mixedEmbedding.mixedSpace F →ₗ[ℝ] (NumberField.InfinitePlace F → ℂ) :=
    { toFun := fun x v => x.2 ⟨v, NumberField.IsTotallyComplex.isComplex v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Surjective L := fun z => ⟨(0, fun w => z w.1), rfl⟩
  have hcomp : (fun (a : F) (v : NumberField.InfinitePlace F) ↦
      (NumberField.InfinitePlace.embedding v : F → ℂ) a) = L ∘ (NumberField.mixedEmbedding F) := by
    funext a v
    simp [L, NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hspan : Submodule.span ℝ (Set.range (NumberField.mixedEmbedding F)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.mixedEmbedding.latticeBasis F).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (NumberField.mixedEmbedding.latticeBasis_apply F i).symm⟩
  rw [hcomp, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact hL

end GlobalTheory.EmbeddingRangeSpanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
noncomputable section

open Matrix NumberField
open scoped TensorProduct Classical

namespace GlobalTheory.LKTrip.HTGroup

theorem span_real_embedding_places (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | (apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top ..)

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  simp only [psiR, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
  rfl

theorem psiR_pi_bijective (G : HTGroup p) :
    Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : ∀ x, Ψ x = fun v => G.psiR v x := fun x => rfl
  set S := Ψ.range with hS
  have hsc : ∀ a : G.F, Ψ (1 ⊗ₜ algebraMap G.F G.C a) =
      fun v : InfinitePlace G.F => Matrix.scalar (Fin G.n) (v.embedding a) := by
    intro a; funext v; rw [hΨ]; dsimp only; rw [psiR_tmul, one_smul, G.psi_F]
  let sc : (InfinitePlace G.F → ℂ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    { toFun := fun c v => Matrix.scalar (Fin G.n) (c v)
      map_add' := fun c d => by funext v; simp
      map_smul' := fun r c => by
        funext v
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Matrix.scalar_apply, Matrix.scalar_apply]
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, h] }
  have hscS : ∀ c : InfinitePlace G.F → ℂ, sc c ∈ S := by
    have htop := span_real_embedding_places G.F
    have hle : Submodule.span ℝ (Set.range fun (a : G.F) (v : InfinitePlace G.F) => v.embedding a) ≤
        (Subalgebra.toSubmodule S).comap sc := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_comap.2 ((AlgHom.mem_range _).2 ⟨_, hsc a⟩)
    intro c
    exact hle (htop ▸ Submodule.mem_top)
  have hsingle : ∀ (v₁ : InfinitePlace G.F) (m : Matrix (Fin G.n) (Fin G.n) ℂ), Pi.single v₁ m ∈ S := by
    intro v₁ m
    have hspan := GlobalTheory.UPel.HT.RealRepBij.span_range_eq_top v₁.embedding (G.psi v₁) G.rankC (G.psi_F v₁)
    have hm : m ∈ Submodule.span ℂ (Set.range (G.psi v₁)) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have : (Pi.single v₁ (G.psi v₁ b) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ 1) * Ψ (1 ⊗ₜ b) := by
        funext v
        rw [hΨ]
        by_cases h : v = v₁
        · subst h; simp [sc, psiR_tmul]
        · simp [sc, h, psiR_tmul]
      rw [this]; exact S.mul_mem (hscS _) ((AlgHom.mem_range _).2 ⟨_, rfl⟩)
    | zero => simpa using S.zero_mem
    | add x y _ _ hx hy => rw [Pi.single_add]; exact S.add_mem hx hy
    | smul z x _ hx =>
      have : (Pi.single v₁ (z • x) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ z) * Pi.single v₁ x := by
        funext v
        by_cases h : v = v₁
        · subst h; simp [sc, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
        · simp [sc, h]
      rw [this]; exact S.mul_mem (hscS _) hx
  have hsurj : Function.Surjective Ψ := by
    intro y
    have : y ∈ S := by
      rw [← Finset.univ_sum_single y]
      exact Subalgebra.sum_mem _ fun v _ => hsingle v (y v)
    exact (AlgHom.mem_range _).1 this
  have hc : 2 * Fintype.card (InfinitePlace G.F) = Module.finrank ℚ G.F := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero G.F]
    ring
  have hfin : Module.finrank ℝ (ℝ ⊗[ℚ] G.C) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    rw [← hc]; ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Ψ.toLinearMap)).2 hsurj, hsurj⟩

end GlobalTheory.LKTrip.HTGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlacesStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (exact GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (intros; apply GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEquiv

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Datum.InfFam D} {M : DSModel V S}
  {J : Set (GA D V)} {χ : GA D V → ℂ}


open Classical in
theorem list_equiv {U : MMap M} (hU : IsMultMap θ M J χ U)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (v w : M.Vec) (h : ∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) (l : List D.what₂.Tau) (hl : l.Nodup) :
    U (fun ρ => if ρ ∈ l then w ρ else v ρ) = rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v) := by
  induction l with
  | nil =>
    funext x
    simp [rTr]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have e := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
      simp only [if_neg hl.1]; exact h a)
    rw [ih hl.2] at e
    have e2 : rTr V ((a :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
        rTr V (atTau θ V a (g a)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
      funext x
      simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
    rw [e2, ← e]
    congr 1
    funext ρ
    by_cases hρ : ρ = a
    · subst hρ
      simp
    · rw [Function.update_of_ne hρ]
      simp [hρ]

theorem mult_realElt : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : Datum.InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) → ∀ v w : M.Vec, (∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) → U w = rTr V (realElt θ V g) (U v) := by
  intro D V S θ M J χ U hU g hg v w h
  classical
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have e := list_equiv hU g hg v w h (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [realElt, ← e]
    congr 1
    funext ρ
    simp
  | zero => funext x; simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have a := congrFun h1 x
    have b := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at a b ⊢
    rw [a, b]
  | smul c U _ h1 =>
    funext x
    have a := congrFun h1 x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at a ⊢
    rw [a]

end GlobalTheory.RealEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

def unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ) (hσ : ∀ a, σ' (incF c c' hle a) = σ a)
    (U : Unf Xo c σ r) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := σ.toAlgebra
  { Comp := U.Comp
    fin := U.fin
    X := U.X
    un := fun k x => FrPt.ext hle (S := CAt σ') hσ (U.un k x) }

def covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) : DeltaDat Xo c' n :=
  { ddBC hle d with cδ := ((show (covCoeff hle d).F from u) • rulBC (le_covCoeff hle d) d.cδ : Rul d.Xo₂ (covCoeff hle d)) }

def covUnf (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) :
    Unf (covBC hle d u).Xo₂ (covBC hle d u).c₂
      (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) r :=
  unfExt (le_covCoeff hle d) _ (fun _ => rfl) U₂

end Gen

section Val

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}

def CXiAt {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) : Prop :=
  IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif d.Xo₂ ((σ0.comp (d.eF.symm : d.c₂.F →+* c.F)).comp
          (IntermediateField.inclusion d.c₂.le).toRingHom)
        (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
      (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
      (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
        rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2 =
          c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

theorem cXiVal_iff {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) :
    CXiVal V hr σ0 dδ U₂ dict₂ ι x₀ xi ↔ ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧
      ∀ t, CXiAt V hr σ0 (dδ t) (U₂ t) (dict₂ t) ι x₀ (xi t) c0 := Iff.rfl

end Val

end GlobalTheory.OneMapAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquiv
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ Γ' G₁ G₂ _ _ _ _ e ι₁ ι₂ θ K₁ K₂ γ δ f φ
  have hprod : (ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom) = (ι₁.prod ι₂).comp e.toMonoidHom := by
    ext x <;> rfl
  have hR : ((ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom)).range = (ι₁.prod ι₂).range := by
    rw [hprod, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
  have hS : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
    intro x
    have h : stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁ ι₂ K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [h]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun a => by simp [Subgroup.mem_comap]))
  unfold pointSum
  simp only [hS]
  rw [hR]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquivStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.pointSum_comp_mulEquiv) | (exact GlobalTheory.pointSum_comp_mulEquiv) | (intros; apply GlobalTheory.pointSum_comp_mulEquiv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem mul_triv_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b h x : S) (t d : A)
    (hx : x * b * (σ x).unop = algebraMap A S t) (hh : h * (σ h).unop = algebraMap A S d) :
    h * x * b * (σ (h * x)).unop = algebraMap A S (t * d) := by
  calc h * x * b * (σ (h * x)).unop = h * (x * b * (σ x).unop) * (σ h).unop := by
        simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S t * (h * (σ h).unop) := by rw [hx, ← Algebra.commutes, mul_assoc]
    _ = _ := by rw [hh, map_mul]

end GlobalTheory.LKMid
end
