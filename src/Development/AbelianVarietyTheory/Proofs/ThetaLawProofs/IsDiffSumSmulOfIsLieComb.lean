module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding JetR zR

noncomputable section

namespace GlobalTheory

namespace DiffLin

open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)

variable {R : Type} [CommRing R] {n : ℕ}

theorem fst_dualLift (t : Fin n → R) (y : JetR R (Fin n) 1) :
    (dualLift t y).fst = jetAug R (Fin n) 1 y :=
  AlgHom.congr_fun (fstD_comp_dualLift t) y

theorem snd_dualLift_sum {k : ℕ} (c : Fin k → R) (t : Fin k → Fin n → R) (y : JetR R (Fin n) 1) :
    (dualLift (∑ i, c i • t i) y).snd = ∑ i, c i * (dualLift (t i) y).snd := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (MvPolynomial.C a))).snd = 0 := fun s => by
      have := (dualLift s).commutes a
      exact (congrArg TrivSqZeroExt.snd this).trans rfl
    simp only [h, mul_zero, Finset.sum_const_zero]
  | add p q hp hq =>
    simp only [map_add (f := _), TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (p * MvPolynomial.X j))).snd =
          jetAug R (Fin n) 1 (Ideal.Quotient.mk _ p) * s j := fun s => by
      rw [map_mul, map_mul, dualLift_zR, DualNumber.snd_mul, fst_dualLift]
      simp
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem spMap_dualLift_surjective (t : Fin n → R) :
    Function.Surjective (spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R)) := by
  intro p
  have hs : Function.Surjective (jetAug R (Fin n) 1 : JetR R (Fin n) 1 →+* R) := fun a =>
    ⟨algebraMap R _ a, (jetAug R (Fin n) 1).commutes a⟩
  have hp : (p : PrimeSpectrum (JetR R (Fin n) 1)) ∈
      Set.range (PrimeSpectrum.comap (jetAug R (Fin n) 1 : JetR R (Fin n) 1 →+* R)) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    apply (PrimeSpectrum.isPrime p).mem_of_pow_mem (1 + 1)
    have : a ^ (1 + 1) ∈ (RingHom.ker (jetAug R (Fin n) 1)) ^ (1 + 1) := Ideal.pow_mem_pow ha _
    rw [ker_jetAug_pow, Ideal.mem_bot] at this
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨q, rfl⟩ := hp
  refine ⟨PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun y => ?_)
  change (dualLift t y).fst ∈ q.asIdeal ↔ jetAug R (Fin n) 1 y ∈ q.asIdeal
  rw [fst_dualLift]

theorem top_le_preimage_of_dualLift {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (t : Fin n → R)
    (h : ⊤ ≤ (spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_dualLift_surjective t p
  exact h (Set.mem_univ q)

open GlobalTheory.TangentOrigin in
theorem evalPt_of_eq {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (t : Fin n → R) (v : Sp (DualNumber R) ⟶ X)
    (e : v = spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) (f : Γ(X, U)) :
    ∃ h : ⊤ ≤ v ⁻¹ᵁ U, evalPt v U h f = dualLift t (evalPt x U hx f) := by
  subst e
  exact ⟨fun p _ => hx (Set.mem_univ _), evalPt_spMap_comp _ x U hx _ f⟩

end DiffLin


open GlobalTheory.TangentOrigin DiffLin in
theorem isDiff_sum_smul_of_isLieComb :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ hA L g n u v W c w hv hd hc U h f
  have : Smooth A.hom := hA.smooth
  obtain ⟨m, x, hx⟩ := Chart.univChartLoc A
  have htan : ∀ i, Chart.IsTan (v i) := fun i => (Chart.isTan_iff _).mpr (hv i)
  obtain ⟨hw, e⟩ := Chart.prodPts_tan hx c v htan
  have ew : w.left = spMap (Chart.dualLift (∑ i, c i • Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := by
    rw [← e, (Chart.isLieComb_iff c v w).1 hc]
    exact congrArg CommaMorphism.left (Chart.tcoord_spec hx _ hw)
  have ev : ∀ i, (v i).left = spMap (Chart.dualLift (Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := fun i =>
    congrArg CommaMorphism.left (Chart.tcoord_spec hx _ (htan i))
  have hU : ⊤ ≤ (x 1).left ⁻¹ᵁ U := top_le_preimage_of_dualLift _ U _ (ew ▸ h)
  obtain ⟨h', e'⟩ := evalPt_of_eq (x 1).left U hU _ w.left ew f
  change (evalPt (R := DualNumber ℂ) w.left U h' f).snd = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e', snd_dualLift_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hi, ei⟩ := evalPt_of_eq (x 1).left U hU _ (v i).left (ev i) f
  rw [← ei, map_smul, smul_eq_mul]
  exact congrArg (c i * ·) (hd i U hi f)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpMove

section
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem thetaChar_half {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    thetaChar τ (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) z = theta (halfVec n) (halfVec n') z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + fun i => (n i : ℂ) / 2) = shiftVec (halfVec n) l := by
    funext i; simp [shiftVec, halfVec]
  have e' : (fun i => (n' i : ℂ) / 2) = ofRealVec (halfVec n') := by
    funext i; simp [ofRealVec, halfVec]
  rw [e, e', thetaTerm, eC]
  congr 1
  ring

theorem jAut_transpose_mulVec_period {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (w : Fin g ⊕ Fin g → ℤ) :
    (jAut δ τ)ᵀ *ᵥ ((fun i => (w (Sum.inr i) : ℂ)) + spAct δ τ *ᵥ (fun i => (w (Sum.inl i) : ℂ))) =
      (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) + τ *ᵥ (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  have hs := spAct_isSymm hδ hτ.1 hj
  have h1 : (jAut δ τ)ᵀ * spAct δ τ = (nAut δ τ)ᵀ := by
    rw [← hs.eq, ← Matrix.transpose_mul, spAct_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj,
      Matrix.mul_one]
  have h2 : (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) =
      (cMat δ).toBlocks₁₂ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₂ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Fintype.sum_sum_type]
  have h3 : (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) =
      (cMat δ).toBlocks₁₁ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₁ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Fintype.sum_sum_type]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, h2, h3, jAut_eq, nAut_eq]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hτ.1.eq, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

theorem jAut_transpose_mulVec_mem_iff {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (z : Fin g → ℂ) :
    (∃ m n : Fin g → ℤ, (jAut δ τ)ᵀ *ᵥ z = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ↔
      ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + spAct δ τ *ᵥ (fun i => (n i : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  constructor
  · rintro ⟨m, n, h⟩
    have hu : IsUnit δᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact SymplecticGroup.symplectic_det hδ
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu (Sum.elim n m)
    have h1 := jAut_transpose_mulVec_period hδ hτ w
    rw [hw] at h1
    refine ⟨fun i => w (Sum.inr i), fun i => w (Sum.inl i), ?_⟩
    have hinj : Function.Injective (jAut δ τ)ᵀ.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact hj
    apply hinj
    rw [h, h1]
    rfl
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, _, jAut_transpose_mulVec_period hδ hτ (Sum.elim n m)⟩

theorem exists_theta_law {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {n n' k k' : Fin g → ℤ}
    (h : KeyPow.ThetaLaw g δ n n' k k') {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ r : ℂ, r ^ 8 = (jAut δ τ).det ^ 4 ∧ ∀ z,
      theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ) =
        r * Complex.exp (Real.pi * Complex.I * expArg δ τ z) * theta (halfVec n) (halfVec n') z τ := by
  obtain ⟨c, hc, h⟩ := h
  have hz : Differentiable ℂ (zAct δ τ) :=
    (Matrix.mulVecLin ((jAut δ τ)⁻¹)ᵀ).toContinuousLinearMap.differentiable
  have hq : Differentiable ℂ fun z => Real.pi * Complex.I * expArg δ τ z := by
    simp only [expArg, dotProduct, mulVec]
    fun_prop
  obtain ⟨r, hr, H⟩ := entire_eq_mul_of_sq_eq_mul_sq g
    (fun z => theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ))
    (fun z => theta (halfVec n) (halfVec n') z τ) _ (c * (jAut δ τ).det)
    ((differentiable_theta (spAct_mem hδ hτ) _ _).comp hz) (differentiable_theta hτ _ _) hq
    (fun z => by
      rw [h τ hτ z, eC]
      congr 3
      ring)
  refine ⟨r, ?_, H⟩
  calc r ^ 8 = (r ^ 2) ^ 4 := by ring
    _ = _ := by rw [hr, mul_pow, hc, _root_.one_mul]

end

theorem normalAt_spAct : ∀ (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ) (sp : Matrix (Fin x.P.g ⊕ Fin x.P.g) (Fin x.P.g ⊕ Fin x.P.g) ℤ) (n n' k k' : Fin x.P.g → ℤ), sp ∈ Matrix.symplecticGroup (Fin x.P.g) ℤ → GlobalTheory.KeyPow.ThetaLaw x.P.g sp n n' k k' → c ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) c → ∃ (M' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c' : ℂ), c' ≠ 0 ∧ M'.det ^ 4 / c' ^ 8 = M.det ^ 4 / c ^ 8 ∧ GlobalTheory.KeyPow.NormalAt x (Key.Chi.spAct sp τ) M' (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) c' := by
  intro x τ M c sp n n' k k' hsp hlaw hc hN
  have hτ := hN.mem_siegelH
  obtain ⟨u, -, -, hΛ, hrig, hfn, hv⟩ := hN
  have hj := Key.Chi.jAut_isUnit hsp hτ
  have hτ' := Key.Chi.spAct_mem hsp hτ
  obtain ⟨r, hr, H⟩ := exists_theta_law hsp hlaw hτ
  set j := Key.Chi.jAut sp τ with hjdef
  have hj0 : j.det ≠ 0 := hj.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact pow_ne_zero 4 hj0 (by rw [← hr]; simp)
  have e1 : j.transpose * (j⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hj, Matrix.transpose_one]
  have e2 : (j⁻¹).transpose * j.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hj, Matrix.transpose_one]
  let φ : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := Matrix.toLin'OfInv e2 e1
  have hφ : ∀ z, φ z = j.transpose.mulVec z := fun _ => rfl
  have hE : Differentiable ℂ fun z => Complex.exp (Real.pi * Complex.I * Key.Chi.expArg sp τ (φ z)) := by
    simp only [hφ, Key.Chi.expArg, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨u', -, hΛ', hrig', hfn', hv'⟩ := exists_holUnif_reparam x.P.A x.P.L x.P.g u φ _ hE
    (fun _ => Complex.exp_ne_zero _) (by simp [Key.Chi.expArg])
  refine ⟨M * j⁻¹, c / r, div_ne_zero hc hr0, ?_, u', hτ'.1, hτ'.2, fun z => ?_, hrig' _ hrig, ?_,
    fun i => hv' _ _ ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_pow, hr]
    field_simp
  · rw [hΛ', hΛ, hφ]
    exact jAut_transpose_mulVec_mem_iff hsp hτ z
  · convert hfn' _ _ hfn using 2 with z
    have h1 := H (φ z)
    have h2 : Key.Chi.zAct sp τ (φ z) = z := by
      rw [Key.Chi.zAct, hφ, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
    rw [h2] at h1
    rw [thetaChar_half, thetaChar_half, h1]
    field_simp
  · have h3 : φ ((M * j⁻¹) i) = M i := by
      rw [hφ, Matrix.mulVec_transpose]
      change ((M * j⁻¹) * j) i = M i
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj, Matrix.mul_one]
    rw [map_smul, h3]
    exact hv i

end GlobalTheory.SpMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsThetaFnAndNeZeroOfIsFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SectionFn

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem differentiable_of_isFn (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) :
    Differentiable ℂ θ := by
  intro z
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hn := (u.hol (L.U i) (s.f i)).1.mem_nhds hi
  have d : DifferentiableOn ℂ (fun w => valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹)
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U i} :=
    (u.hol (L.U i) (s.f i)).2.mul ((u.fr_hol i).inv fun w hw => u.fr_ne i w hw)
  refine (d.differentiableAt hn).congr_of_eventuallyEq (Filter.mem_of_superset hn fun w hw => ?_)
  have := u.fr_ne i w hw
  change θ w = valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹
  rw [h i w hw]
  field_simp

theorem isThetaFn_of_isFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsThetaFn Hm χ 1 θ := by
  refine ⟨differentiable_of_isFn u hL h, fun l z => ?_⟩
  have hper : u.ex (z + l) = u.ex z := by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h i z hi
  have h2 := h i (z + l) hi'
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  refine mul_right_cancel₀ (u.fr_ne i _ hi') ?_
  rw [← h2, pow_one]
  unfold hermForm
  ring

theorem ne_zero_of_isFn [LocallyOfFiniteType A.hom] {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    {p : A.left} (hp : p ∈ Out.nonzeroLocus s) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  have hle : A.left.basicOpen (s.f i) ≤ ⊥ := by
    refine ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun y hy hyb => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y hy)
    have hzy : (u.ex z).left = y := by rw [hz]; rfl
    subst hzy
    have hne := (top_le_preimage_basicOpen_iff _ _ _).1 hyb
    have hU := top_le_preimage_of_valAt'_ne_zero _ hne
    exact absurd (by simpa using h i z hU) hne
  exact hle hi

end SectionFn

theorem isThetaFn_and_ne_zero_of_isFn :
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  intro x u Hm χ θ hAH h
  refine ⟨SectionFn.isThetaFn_of_isFn u x.P.isLB hAH h, ?_⟩
  obtain ⟨p, -, hp⟩ := x.th_ne (default : PrimeSpectrum ℂ)
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  exact SectionFn.ne_zero_of_isFn u h hp

end GlobalTheory
end
