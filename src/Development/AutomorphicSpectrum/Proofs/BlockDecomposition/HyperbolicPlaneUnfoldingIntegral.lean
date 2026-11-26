module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitExtensionFundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrame
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (y z : Fin M → E) : σ (hE σ J y z) = hE σ J z y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem exists_partner [CharZero E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {N : ℕ}
    (K : Matrix (Fin N) (Fin N) E) (hK : IsHermND σ K) (x : Fin N → E) (hx0 : x ≠ 0)
    (hxx : hE σ K x x = 0) : ∃ y, hE σ K x y = 1 ∧ hE σ K y y = 0 := by
  have hherm := hE_herm σ hσ K hK.1
  have hex : ∃ y₀, hE σ K x y₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hv : Matrix.vecMul (fun i => σ (x i)) K = 0 := by
      funext j
      have := hall (Pi.single j 1)
      simpa [hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hz : (fun i => σ (x i)) = 0 := by
      have hu : IsUnit K := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hK.2)
      exact (Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)
    apply hx0
    funext i
    have h := congrArg σ (congrFun hz i)
    simpa [hσ] using h
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨y₁, hxy₁⟩ : ∃ y₁, hE σ K x y₁ = 1 :=
    ⟨(hE σ K x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩
  have hy₁x : hE σ K y₁ x = 1 := by rw [← hherm, hxy₁, map_one]
  obtain ⟨q, hq⟩ : ∃ q, q = hE σ K y₁ y₁ := ⟨_, rfl⟩
  have hqs : σ q = q := by rw [hq]; exact hherm _ _
  obtain ⟨y, hy⟩ : ∃ y : Fin N → E, y = y₁ + (-(q / 2)) • x := ⟨_, rfl⟩
  have hxy : hE σ K x y = 1 := by
    rw [hy, hE_add_right, hE_smul_right, hxy₁, hxx]; simp
  have hyy : hE σ K y y = 0 := by
    have hs2 : σ (-(q / 2)) = -(q / 2) := by
      rw [map_neg, map_div₀, hqs, map_ofNat]
    rw [hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left,
      hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]
    field_simp
    ring
  exact ⟨y, hxy, hyy⟩

theorem gramE_pair (σ : E →ₐ[F] E) {N : ℕ} (K : Matrix (Fin N) (Fin N) E) (u v : Fin N → E)
    (h1 : hE σ K u u = 0) (h2 : hE σ K u v = 1) (h3 : hE σ K v u = 1) (h4 : hE σ K v v = 0) :
    gramE σ K ![u, v] = !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gramE, h1, h2, h3, h4]

theorem hE_hypOne_basis (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 1 fun _ => 0) = 0 ∧
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 1 fun _ => 0) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [hE, hform, Fin.sum_univ_succ, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one]

end Alg

theorem exists_unitary_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  intro F E _ _ _ _ _ σ hCM M J hJ q hq
  obtain ⟨hσ, -⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hK := isHermND_hypOne σ hJ
  obtain ⟨hli, hg⟩ := hq
  have hx0 : q 0 ≠ 0 := hli.ne_zero 0
  have hxx : hE σ (hypOne J) (q 0) (q 0) = 0 := congrFun (congrFun hg 0) 0
  obtain ⟨y, hxy, hyy⟩ := exists_partner σ hσ (hypOne J) hK (q 0) hx0 hxx
  have hyx : hE σ (hypOne J) y (q 0) = 1 := by
    rw [← hE_herm σ hσ _ hK.1, hxy, map_one]
  obtain ⟨b1, b2, b3, b4⟩ := hE_hypOne_basis σ J
  have hX := gramE_pair σ (hypOne J) (q 0) y hxx hxy hyx hyy
  have hY := gramE_pair σ (hypOne J) _ _ b1 b2 b3 b4
  obtain ⟨g, hgU, hgX⟩ := GlobalTheory.T.witt_extension_global F E σ hCM (M + 2) (hypOne J) hK 2 _ _ (hX.trans hY.symm)
    (by rw [hX]; simp [Matrix.det_fin_two_of])
  refine ⟨⟨g, hgU⟩, ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  exact hgX 0

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrameStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_unitary_moves_isotropic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliser
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliser
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

theorem linearIndependent_mulVec_unit {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact_unitary {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec_unit (g : GL (Fin M) E) hX

theorem gact_inv_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : gact σ w⁻¹ (e0 E M) = e0 E M := by
  conv_lhs => rw [← hw]
  exact gact_inv_gact σ w _

theorem gact_zero_of_first {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (w : UJ (σ : E →+* E) (hypOne J))
    {X : Fin (n + 1) → Fin (M + 2) → E} (hX : X 0 = e0 E M 0) :
    gact σ w X 0 = gact σ w (e0 E M) 0 := by
  change ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X 0 =
    ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ e0 E M 0
  rw [hX]

theorem gact_mem_framesOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) {X : Fin (n + 1) → Fin (M + 2) → E}
    (hX : X ∈ framesOne σ J n) : gact σ w X ∈ framesOne σ J n := by
  refine ⟨⟨linearIndependent_gact_unitary σ w hX.1.1, ?_⟩, ?_⟩
  · rw [gramE_gact]; exact hX.1.2
  · rw [gact_zero_of_first σ w hX.2, hw]

def framesOneEquiv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (n : ℕ) {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : framesOne σ J n ≃ framesOne σ J n where
  toFun X := ⟨gact σ w X.1, gact_mem_framesOne σ hw X.2⟩
  invFun X := ⟨gact σ w⁻¹ X.1, gact_mem_framesOne σ (gact_inv_e0 σ hw) X.2⟩
  left_inv X := Subtype.ext (gact_inv_gact σ w X.1)
  right_inv X := Subtype.ext (gact_gact_inv σ w X.1)

theorem tsum_gact_framesOne (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J))
    (hw : gact σ w (e0 E M) = e0 E M) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞) :
    ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 :=
  (framesOneEquiv σ n hw).tsum_eq (fun X => f X.1)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliserStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_sum_invariant_under_stabiliser : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J)), gact σ w (e0 E M) = e0 E M → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbit
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_gact {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent E (gact σ g X) := by
  have hker : LinearMap.ker
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y h => ?_
    have h1 : gact σ g (fun _ : Fin 1 => x) = gact σ g (fun _ : Fin 1 => y) :=
      funext fun _ => h
    have h2 := congrArg (gact σ g⁻¹) h1
    rw [gact_inv_gact, gact_inv_gact] at h2
    exact congrFun h2 0
  have h3 : gact σ g X =
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) ∘ X := by
    funext a
    rfl
  rw [h3]
  exact hX.map' (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) hker

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J)
    {T : Matrix (Fin n) (Fin n) E} {X : Fin n → Fin M → E} (hX : X ∈ framesE σ J T) :
    gact σ g X ∈ framesE σ J T :=
  ⟨linearIndependent_gact σ g hX.1, (gramE_gact σ g X).trans hX.2⟩

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  intro F E _ _ _ σ M J n rr hrr f
  have hrow : ∀ (q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))
      (X : framesOne σ J n), gact σ (rr q)⁻¹ X.1 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    have h0 := congrFun h 0
    have hX : X.1 0 = e0 E M 0 := X.2.2
    change ((((rr q)⁻¹ : UJ (σ : E →+* E) (hypOne J)) : GL (Fin (M + 2)) E) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X.1 0 = q.1 0
    rw [hX, h0]
    rfl
  let m : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) × framesOne σ J n →
      framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :=
    fun p => ⟨gact σ (rr p.1)⁻¹ p.2.1, gact_mem_framesE σ _ p.2.2.1⟩
  have hinj : Function.Injective m := by
    rintro ⟨q, X⟩ ⟨q', X'⟩ h
    have h1 : gact σ (rr q)⁻¹ X.1 = gact σ (rr q')⁻¹ X'.1 := congrArg Subtype.val h
    have hq : q = q' := by
      apply Subtype.ext
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      rw [← hrow q X, ← hrow q' X', h1]
    subst hq
    have h2 := congrArg (gact σ (rr q)) h1
    rw [gact_gact_inv, gact_gact_inv] at h2
    exact Prod.ext rfl (Subtype.ext h2)
  have hsurj : Function.Surjective m := by
    rintro ⟨Y, hY⟩
    have hq : (fun _ : Fin 1 => Y 0) ∈
        framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
      refine ⟨hY.1.comp (fun _ : Fin 1 => (0 : Fin (n + 1)))
        (Function.injective_of_subsingleton _), ?_⟩
      funext a b
      exact congrFun (congrFun hY.2 0) 0
    let q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := ⟨_, hq⟩
    have hX : gact σ (rr q) Y ∈ framesOne σ J n :=
      ⟨gact_mem_framesE σ _ hY, congrFun (hrr q) 0⟩
    exact ⟨(q, ⟨_, hX⟩), Subtype.ext (gact_inv_gact σ (rr q) Y)⟩
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbitStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_frames_sum_by_orbit : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumByFirstVector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumByFirstVector
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b c d : E)
    (x y : Fin M → E) :
    hE σ (hypOne J) (Fin.cons a (Fin.cons b x) : Fin (M + 2) → E)
        (Fin.cons c (Fin.cons d y) : Fin (M + 2) → E) = σ a * d + σ b * c + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have e00 : hypOne J 0 0 = 0 := rfl
  have e01 : hypOne J 0 (Fin.succ 0) = 1 := rfl
  have e10 : hypOne J (Fin.succ 0) 0 = 1 := rfl
  have e11 : hypOne J (Fin.succ 0) (Fin.succ 0) = 0 := rfl
  have e0r : ∀ j : Fin M, hypOne J 0 j.succ.succ = 0 := fun _ => rfl
  have e1r : ∀ j : Fin M, hypOne J (Fin.succ 0) j.succ.succ = 0 := fun _ => rfl
  have er0 : ∀ i : Fin M, hypOne J i.succ.succ 0 = 0 := fun _ => rfl
  have er1 : ∀ i : Fin M, hypOne J i.succ.succ (Fin.succ 0) = 0 := fun _ => rfl
  have err : ∀ i j : Fin M, hypOne J i.succ.succ j.succ.succ = J i j := fun _ _ => rfl
  simp only [e00, e01, e10, e11, e0r, e1r, er0, er1, err]
  simp
  ring

theorem e0_cons (M : ℕ) : e0 E M 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i

theorem consA_zero {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) :
    consA a Y 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
  rw [← e0_cons]; rfl

theorem consA_succ {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) (j : Fin n) :
    consA a Y j.succ = Fin.cons (a 0 j) (Fin.cons 0 (Y j)) := rfl

theorem consA_mem (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) (hY : Y ∈ framesE σ J (0 : Matrix (Fin n) (Fin n) E)) :
    consA a Y ∈ framesOne σ J n := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hg : ∀ i j, hE σ J (Y i) (Y j) = 0 := fun i j => congrFun (congrFun hY.2 i) j
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    rw [Fin.sum_univ_succ] at hc
    have htail : ∀ k : Fin n, c k.succ = 0 := by
      refine Fintype.linearIndependent_iff.1 hY.1 (fun k => c k.succ) ?_
      funext i
      have := congrFun hc i.succ.succ
      simpa [Finset.sum_apply, consA_zero, consA_succ] using this
    have h0 : c 0 = 0 := by
      have := congrFun hc 0
      simpa [Finset.sum_apply, consA_zero, consA_succ, htail] using this
    intro k
    exact Fin.cases h0 htail k
  · ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gramE, consA_zero, hE_cons, hz, BlockAlg.hE_zero_left]
    · simp [gramE, consA_zero, consA_succ, hE_cons, hz, BlockAlg.hE_zero_left]
    · simp [gramE, consA_zero, consA_succ, hE_cons, hz, BlockAlg.hE_zero_right]
    · simp [gramE, consA_succ, hE_cons, hg]
  · rfl

theorem sec_zero (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesOne σ J n) (a : Fin n) :
    X a.succ (Fin.succ 0) = 0 := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hc : X a.succ = Fin.cons (X a.succ 0) (Fin.cons (X a.succ (Fin.succ 0)) (fun i => X a.succ i.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have h : hE σ (hypOne J) (X 0) (X a.succ) = 0 := congrFun (congrFun hX.1.2 0) a.succ
  rw [hX.2, e0_cons, hc, hE_cons, hz, BlockAlg.hE_zero_left] at h
  simpa using h

theorem tail_mem (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesOne σ J n) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ.succ) ∈ framesE σ J (0 : Matrix (Fin n) (Fin n) E) := by
  have hgr : ∀ a b, hE σ (hypOne J) (X a) (X b) = 0 := fun a b =>
    congrFun (congrFun hX.1.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (Fin.cons (X a (Fin.succ 0)) (fun i => X a i.succ.succ)) :=
    fun a => by
      funext i
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have hsec := sec_zero σ J X hX
  have h0 := hX.2.trans (e0_cons M)
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1.1
      (Fin.cons (-∑ k, c k * X k.succ 0) c) (by
      rw [Fin.sum_univ_succ, h0]
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Finset.sum_apply]
      · have hsec' : ∀ a : Fin n, X a.succ 1 = 0 := hsec
        simp [Finset.sum_apply, hsec']
      · have := congrFun hc' k
        simpa [Finset.sum_apply] using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, hE_cons, hsec, hsec] at h
    simpa [gramE] using h

def framesOneEquiv (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    framesE σ J (0 : Matrix (Fin n) (Fin n) E) × (Fin 1 → Fin n → E) ≃ framesOne σ J n where
  toFun p := ⟨consA p.2 p.1.1, consA_mem σ J p.2 p.1.1 p.1.2⟩
  invFun X := (⟨fun a i => X.1 a.succ i.succ.succ, tail_mem σ J X.1 X.2⟩, fun _ a => X.1 a.succ 0)
  left_inv p := by
    obtain ⟨⟨Y, hY⟩, a⟩ := p
    refine Prod.ext (Subtype.ext ?_) ?_
    · rfl
    · funext i j
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    refine Subtype.ext ?_
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact hX.2.symm
    · funext i
      refine Fin.cases rfl (fun i => Fin.cases ?_ (fun l => rfl) i) i
      exact (sec_zero σ J X hX k).symm

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞), ∑' X : framesOne σ J n, f X.1 = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : Fin 1 → Fin n → E, f (consA a Y.1) := by
  intro F E _ _ _ σ M J n f
  rw [← (framesOneEquiv σ J n).tsum_eq (fun X : framesOne σ J n => f X.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumByFirstVectorStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_sum_by_first_vector : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞), ∑' X : framesOne σ J n, f X.1 = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : Fin 1 → Fin n → E, f (consA a Y.1) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFibrationVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFibrationVolume
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PeriodisedMean

theorem setLIntegral_tsum_comp_inv_eq : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ _ 𝓕N h𝓕 hfin V _ _ _ _ _ _ _ _ dA _ Λ _ D hD hD1 l hlc hlmul hlsurj hlΓ f hf
  obtain ⟨-, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain N Γ ν 𝓕N h𝓕 hfin
  have hlm : Measurable l := hlc.measurable

  set Ft : V → ℝ≥0∞ := fun x => ∑' a : Λ, f ((a : V) + x) with hFt
  have hFtm : Measurable Ft :=
    Measurable.tsum fun a => hf.comp (measurable_const.add measurable_id)
  have hper : ∀ b ∈ Λ, ∀ x, Ft (x + b) = Ft x := by
    intro b hb x
    simp only [hFt]
    rw [← (Equiv.addRight (⟨b, hb⟩ : Λ)).tsum_eq (fun a : Λ => f ((a : V) + x))]
    refine tsum_congr fun a => ?_
    simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
    congr 1
    abel
  set h : N → ℝ≥0∞ := fun m => Ft (l m⁻¹) with hh
  have hinv : ∀ γ ∈ Γ, ∀ m, h (γ * m) = h m := by
    intro γ hγ m
    simp only [hh]
    rw [mul_inv_rev, hlmul]
    exact hper _ (hlΓ _ (Γ.inv_mem hγ)) _

  have hshift : ∀ n₀ : N, ∫⁻ m in 𝓕N, h (m * n₀) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro n₀
    have hF : IsFundamentalDomain Γ ((· * n₀⁻¹) ⁻¹' 𝓕N) ν :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right ν n₀⁻¹) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hmp : MeasurePreserving (· * n₀) ν ν := measurePreserving_mul_right ν n₀
    have hemb : MeasurableEmbedding (· * n₀ : N → N) :=
      (MeasurableEquiv.mulRight n₀).measurableEmbedding
    have e1 := hmp.setLIntegral_comp_preimage_emb hemb h ((· * n₀⁻¹) ⁻¹' 𝓕N)
    have e2 : (· * n₀ : N → N) ⁻¹' ((· * n₀⁻¹) ⁻¹' 𝓕N) = 𝓕N := by
      ext x; simp
    rw [e2] at e1
    rw [e1]
    exact hF.setLIntegral_eq h𝓕 h (fun γ x => hinv γ γ.2 x)

  have hT : ∀ x, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := hlsurj x
    rw [← hshift y⁻¹]
    refine lintegral_congr fun m => ?_
    simp only [hh]
    rw [mul_inv_rev, inv_inv, hlmul]

  have hfold : ∀ c : V, ∫⁻ x in D, Ft (x + c) ∂dA = ∫⁻ x, f x ∂dA := by
    intro c
    have e0 : ∫⁻ x, f (x + c) ∂dA = ∫⁻ x, f x ∂dA := lintegral_add_right_eq_self f c
    have e3 : ∫⁻ x in D, ∑' a : Λ, f ((a +ᵥ x) + c) ∂dA
        = ∑' a : Λ, ∫⁻ x in D, f ((a +ᵥ x) + c) ∂dA :=
      lintegral_tsum fun a => (hf.comp ((measurable_const_vadd a).add_const c)).aemeasurable
    rw [← e0, hD.lintegral_eq_tsum'' (fun x => f (x + c)), ← e3]
    refine lintegral_congr fun x => ?_
    simp only [hFt]
    refine tsum_congr fun a => ?_
    simp [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  have hswapm : Measurable (Function.uncurry fun (x : V) (m : N) => Ft (x + l m⁻¹)) :=
    hFtm.comp (measurable_fst.add (hlm.comp measurable_snd.inv))
  calc ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν
      = ∫⁻ m in 𝓕N, h m ∂ν := rfl
    _ = ∫⁻ _x in D, (∫⁻ m in 𝓕N, h m ∂ν) ∂dA := by
        rw [setLIntegral_const, hD1, mul_one]
    _ = ∫⁻ x in D, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν ∂dA :=
        lintegral_congr fun x => (hT x).symm
    _ = ∫⁻ m in 𝓕N, ∫⁻ x in D, Ft (x + l m⁻¹) ∂dA ∂ν :=
        lintegral_lintegral_swap hswapm.aemeasurable
    _ = ∫⁻ _m in 𝓕N, (∫⁻ x, f x ∂dA) ∂ν := lintegral_congr fun m => hfold _
    _ = ν 𝓕N * ∫⁻ x, f x ∂dA := by
        rw [setLIntegral_const, mul_comm]

end GlobalTheory.CompanionTheory.SW.PeriodisedMean
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFibrationVolumeStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_fibration_volume : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  first | exact @GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | exact GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | (intros; apply GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegral
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
open GlobalTheory.CompanionTheory.SW.ThetaStage

section Tup

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem ratTup_consA {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) :
    ratTup (F := F) R (consA a Y) = consA (ratTup (F := F) R a) (ratTup (F := F) R Y) := by
  funext j i
  refine Fin.cases ?_ (fun j => ?_) j <;> refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    simp [ratTup, consA]

theorem ratTup_e0 {M : ℕ} : ratTup (F := F) R (e0 E M) = e0 (R ⊗[F] E) M := by
  funext j i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [ratTup, e0]

theorem continuous_consA {K : Type} [Zero K] [One K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (fun p : (Fin 1 → Fin n → K) × (Fin n → Fin M → K) => consA p.1 p.2) := by
  refine continuous_pi fun j => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) j
  · exact continuous_const
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact (continuous_apply j).comp ((continuous_apply (0 : Fin 1)).comp continuous_fst)
    · exact continuous_const
    · exact (continuous_apply i).comp ((continuous_apply j).comp continuous_snd)

end Tup

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def phiA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ)
    (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (g : HA (AF F) σ (hypOne J)) : ℝ≥0∞ :=
  ∑' X : framesOne σ J n, Φ (actW (AF F) σ (hypOne J) g⁻¹ (ratTup (AF F) X.1))

end Glob


set_option maxHeartbeats 2000000 in
theorem meanP : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∃ (μP : Measure (stabilizer₂ (AF F) σ J)) (𝓕P : Set (stabilizer₂ (AF F) σ J)), μP.IsHaarMeasure ∧ IsFundamentalDomain (ratP (AF F) σ J) 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ g : HA (AF F) σ (hypOne J), (μP 𝓕P)⁻¹ * ∫⁻ u in 𝓕P, phiA σ J n Φ ((u : HA (AF F) σ (hypOne J)) * g) ∂μP = Ψ (actW (AF F) σ (hypOne J) g⁻¹ (e0 _ M)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hyp
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨hJb, -, -⟩ := GlobalTheory.T.hyperbolic_frames_unitary_stable F E σ hσ M J hJ
  obtain ⟨tg, lc, sc, t2, bs, act⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 2) _ hJb (AF F)
  obtain ⟨tg₁, lc₁, sc₁, t2₁, bs₁, act₁⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  haveI := tg₁
  haveI := lc₁
  haveI := sc₁
  haveI := t2₁
  haveI := bs₁
  obtain ⟨c1, c2, c3, c4, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hσ (AF F)
  haveI := c1
  haveI := c2
  haveI := c3
  haveI := c4
  haveI := hB (n + 1) (M + 2)
  haveI := hB 1 (M + 2)
  haveI := hB n M
  haveI := hB 1 n
  haveI : μ₁.IsHaarMeasure := hμ₁
  haveI : dA.IsAddHaarMeasure := hdA.1
  obtain ⟨D, hD, hD1⟩ := hdA.2
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  have hPc : IsClosed ((stabilizer₂ (AF F) σ J : Subgroup (HA (AF F) σ (hypOne J))) : Set (HA (AF F) σ (hypOne J))) :=
    isClosed_eq ((act 1).1.comp (continuous_id.prodMk continuous_const)) continuous_const
  haveI : LocallyCompactSpace (stabilizer₂ (AF F) σ J) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (stabilizer₂ (AF F) σ J) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (stabilizer₂ (AF F) σ J) := Subtype.borelSpace _
  obtain ⟨ι, π, hιc, hπc, hπι, hι1, hπ1, hK, hιact, hl⟩ := GlobalTheory.T.stabiliser_splitting_adelic F E σ hσ M J hJ
  obtain ⟨hc0, U, hU, hU1⟩ := rational_countable_discrete F E σ hσ (M + 2) _ hJb
  haveI hc₁ : Countable (HFinIn (AF F) σ J) := (rational_countable_discrete F E σ hσ M J hJ).1
  let Γ₁ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI hc₁' : Countable Γ₁ := hc₁
  haveI hcP : Countable (ratP (AF F) σ J) := by
    haveI := hc0
    have hinj : Function.Injective fun γ : ratP (AF F) σ J =>
        (⟨((γ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)), γ.2⟩ : HFinIn (AF F) σ (hypOne J)) := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : HFinIn (AF F) σ (hypOne J) => (x : HR (AF F) σ (hypOne J))) h))
    exact hinj.countable
  have hfin : μ₁ 𝓕₁ < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ₁ hμ₁).2 𝓕₁ h𝓕₁
  have hUP : ∃ U' ∈ 𝓝 (1 : stabilizer₂ (AF F) σ J), ∀ γ ∈ ratP (AF F) σ J, γ ∈ U' → γ = 1 := by
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
    intro γ hγ hγU
    refine Subtype.ext (hU1 _ hγU ?_)
    exact (mem_HFinIn_iff _ σ _ _).1 hγ
  obtain ⟨ν, 𝓕N, μP, 𝓕P, hν, h𝓕N, hν0, hνf, hμP, h𝓕P, hPf, hform⟩ :=
    GlobalTheory.T.split_extension_fundamental_domain (stabilizer₂ (AF F) σ J) (HA (AF F) σ J) ι π hιc hπc hπι (ratP (AF F) σ J) Γ₁
      hUP hι1 hπ1 μ₁ 𝓕₁ h𝓕₁ hfin hK
  refine ⟨μP, 𝓕P, hμP, h𝓕P, hPf, fun g => ?_⟩
  haveI := hν
  have hNc : IsClosed ((π.ker : Subgroup (stabilizer₂ (AF F) σ J)) : Set (stabilizer₂ (AF F) σ J)) := by
    have : ((π.ker : Subgroup (stabilizer₂ (AF F) σ J)) : Set (stabilizer₂ (AF F) σ J)) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπc
  haveI : LocallyCompactSpace π.ker := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI hcN : Countable ((ratP (AF F) σ J).subgroupOf π.ker) := by
    have hinj : Function.Injective fun γ : (ratP (AF F) σ J).subgroupOf π.ker =>
        (⟨(γ : π.ker), Subgroup.mem_subgroupOf.1 γ.2⟩ : ratP (AF F) σ J) := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : ratP (AF F) σ J => (x : stabilizer₂ (AF F) σ J)) h))
    exact hinj.countable
  haveI hcΛ : Countable (ratA (F := F) (E := E) n) := by
    have hs : Function.Surjective fun a : Fin 1 → Fin n → E =>
        (⟨ratTup (AF F) a, ⟨a, rfl⟩⟩ : ratA (F := F) (E := E) n) := by
      rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩
    exact hs.countable
  have hl' : ∀ Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∃ l : π.ker → Fin 1 → Fin n → AF F ⊗[F] E,
      Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧
      (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) n) ∧
      ∀ (m : π.ker) (a : Fin 1 → Fin n → AF F ⊗[F] E),
        actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y.1)) =
          consA (a + l m) (ratTup (AF F) Y.1) := fun Y => hl n Y.1 Y.2.1
  choose ll hlc hladd hlsurj hlrat hlact using hl'

  let eA : (Fin 1 → Fin n → E) ≃ ratA (F := F) (E := E) n := Equiv.ofBijective
    (fun a => ⟨ratTup (AF F) a, ⟨a, rfl⟩⟩)
    ⟨fun a b h => ratTup_adele_injective (F := F) (congrArg Subtype.val h), by
      rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩⟩
  have hact : ∀ k : ℕ, Continuous fun X : Fin k → Fin (M + 2) → AF F ⊗[F] E =>
      actW (AF F) σ (hypOne J) g⁻¹ X := fun k =>
    (act k).1.comp (continuous_const.prodMk continuous_id)
  let K : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞ := fun Y' =>
    ∫⁻ x, Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA x Y')) ∂dA
  have hjoint : Measurable fun p : (Fin n → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin n → AF F ⊗[F] E) =>
      Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA p.2 p.1)) :=
    hΦ.comp ((hact (n + 1)).comp (continuous_consA.comp continuous_swap)).measurable
  have hKm : Measurable K := hjoint.lintegral_prod_right'
  have hslice : ∀ Y' : Fin n → Fin M → AF F ⊗[F] E, Measurable fun x : Fin 1 → Fin n → AF F ⊗[F] E =>
      Φ (actW (AF F) σ (hypOne J) g⁻¹ (consA x Y')) := fun Y' =>
    hΦ.comp ((hact (n + 1)).comp (continuous_consA.comp (continuous_id.prodMk continuous_const))).measurable

  have hterm : ∀ (u : HA (AF F) σ J) (m : π.ker),
      phiA σ J n Φ ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g) =
      ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : ratA (F := F) (E := E) n,
        Φ (actW (AF F) σ (hypOne J) g⁻¹
          (consA ((a : Fin 1 → Fin n → AF F ⊗[F] E) + ll Y m⁻¹)
            (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)))) := by
    intro u m
    rw [phiA, GlobalTheory.T.frames_sum_by_first_vector F E σ M J n (fun X => Φ (actW (AF F) σ (hypOne J)
      ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g)⁻¹ (ratTup (AF F) X)))]
    refine tsum_congr fun Y => ?_
    rw [← eA.tsum_eq]
    refine tsum_congr fun a => ?_
    congr 1
    have e1 : ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g)⁻¹ =
        g⁻¹ * (((ι u⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) *
          (((m⁻¹ : π.ker) : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J))) := by
      rw [map_inv]
      simp [mul_assoc]
    rw [e1, actW_mul_apply, actW_mul_apply, ratTup_consA, hlact, hιact]
    rfl
  have hinner : ∀ u : HA (AF F) σ J,
      ∫⁻ m in 𝓕N, phiA σ J n Φ ((((m : stabilizer₂ (AF F) σ J) * ι u : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) * g) ∂ν =
      ν 𝓕N * ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E),
        K (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)) := by
    intro u
    rw [lintegral_congr (hterm u), lintegral_tsum, ← ENNReal.tsum_mul_left]
    · refine tsum_congr fun Y => ?_
      exact GlobalTheory.T.fundamental_domain_fibration_volume π.ker ν ((ratP (AF F) σ J).subgroupOf π.ker) 𝓕N h𝓕N hνf
        (Fin 1 → Fin n → AF F ⊗[F] E) dA (ratA (F := F) (E := E) n) D hD hD1 (ll Y) (hlc Y) (hladd Y)
        (hlsurj Y) (fun γ hγ => hlrat Y γ (Subgroup.mem_subgroupOf.1 hγ)) _ (hslice _)
    · intro Y
      refine Measurable.aemeasurable (Measurable.tsum fun a => ?_)
      refine (hslice _).comp ?_
      exact (measurable_const.add ((hlc Y).measurable.comp measurable_inv))
  have hfm : Measurable fun p : stabilizer₂ (AF F) σ J =>
      phiA σ J n Φ ((p : HA (AF F) σ (hypOne J)) * g) := by
    refine Measurable.tsum fun X => hΦ.comp ?_
    have : Continuous fun p : stabilizer₂ (AF F) σ J =>
        actW (AF F) σ (hypOne J) ((p : HA (AF F) σ (hypOne J)) * g)⁻¹ (ratTup (AF F) X.1) :=
      (act (n + 1)).1.comp (((continuous_subtype_val.mul continuous_const).inv).prodMk continuous_const)
    exact this.measurable
  have hvol : μP 𝓕P = ν 𝓕N * μ₁ 𝓕₁ := by
    have := hform (fun _ => 1) measurable_const
    simpa [mul_comm] using this
  rw [hform _ hfm, lintegral_congr hinner, lintegral_const_mul' _ _ hνf.ne, hvol, hyp g⁻¹,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ₁ 𝓕₁ hμ₁ h𝓕₁ n _ K hKm, ENNReal.mul_inv (Or.inl hν0) (Or.inl hνf.ne)]
  calc _ = (ν 𝓕N)⁻¹ * ν 𝓕N * ((μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), K (actW (AF F) σ J u⁻¹ (ratTup (AF F) Y.1)) ∂μ₁) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hν0 hνf.ne, one_mul]


set_option maxHeartbeats 2000000 in
theorem unfold_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (μ : Measure (HA (AF F) σ (hypOne J))) 𝓕, IsHaarH F E σ (M + 2) (hypOne J) μ → IsFDH F E σ (M + 2) (hypOne J) μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∫⁻ X, Φ X ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E))) = ∫⁻ y, Ψ y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n hn hM μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hΨ hyp
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨hJb, he0, hgq⟩ := GlobalTheory.T.hyperbolic_frames_unitary_stable F E σ hσ M J hJ
  obtain ⟨tg, lc, sc, t2, bs, act⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 2) _ hJb (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  obtain ⟨c1, c2, c3, c4, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hσ (AF F)
  haveI := c1
  haveI := c2
  haveI := c3
  haveI := c4
  haveI := hB (n + 1) (M + 2)
  haveI := hB 1 (M + 2)
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  obtain ⟨μP, 𝓕P, hμP, h𝓕P, hPf, hmean⟩ := meanP F E σ hσ M J hJ n μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA Φ Ψ hΦ hyp
  haveI := hμP
  have hPc : IsClosed ((stabilizer₂ (AF F) σ J : Subgroup (HA (AF F) σ (hypOne J))) : Set (HA (AF F) σ (hypOne J))) :=
    isClosed_eq ((act 1).1.comp (continuous_id.prodMk continuous_const)) continuous_const
  haveI : LocallyCompactSpace (stabilizer₂ (AF F) σ J) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (stabilizer₂ (AF F) σ J) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (stabilizer₂ (AF F) σ J) := Subtype.borelSpace _
  haveI hc : Countable (HFinIn (AF F) σ (hypOne J)) := (rational_countable_discrete F E σ hσ (M + 2) _ hJb).1
  let Γ : Subgroup (HA (AF F) σ (hypOne J)) := HFinIn (AF F) σ (hypOne J)
  haveI hc' : Countable Γ := hc
  haveI hcP : Countable (ratP (AF F) σ J) := by
    have hinj : Function.Injective fun γ : ratP (AF F) σ J =>
        (⟨((γ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)), γ.2⟩ : HFinIn (AF F) σ (hypOne J)) := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : HFinIn (AF F) σ (hypOne J) => (x : HR (AF F) σ (hypOne J))) h))
    exact hinj.countable
  have hW : ∀ q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E),
      ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q.1 = e0 E M :=
    fun q => GlobalTheory.T.global_unitary_moves_isotropic_frame F E σ hσ M J hJ q.1 q.2
  choose rr hrr using hW
  let r := fun q => ratH (AF F) σ (hypOne J) (rr q)
  have hφ : Measurable (phiA σ J n Φ) := by
    refine Measurable.tsum fun X => hΦ.comp ?_
    have : Continuous fun g : HA (AF F) σ (hypOne J) =>
        actW (AF F) σ (hypOne J) g⁻¹ (ratTup (AF F) X.1) :=
      (act (n + 1)).1.comp (continuous_inv.prodMk continuous_const)
    exact this.measurable
  have hmul : ∀ (g h : HA (AF F) σ (hypOne J)) {k : ℕ} (X : Fin k → Fin (M + 2) → AF F ⊗[F] E),
      actW (AF F) σ _ (g * h) X = actW (AF F) σ _ g (actW (AF F) σ _ h X) :=
    fun g h {k} X => actW_mul_apply _ σ _ g h X
  have hfix : ∀ g : UJ (σ : E →+* E) (hypOne J),
      actW (AF F) σ _ (ratH (AF F) σ _ g) (e0 _ M) = ratTup (AF F) (gact σ g (e0 E M)) := by
    intro g
    rw [← ratTup_e0, actW_ratH']
  have hinv : ∀ u ∈ ratP (AF F) σ J, ∀ g, phiA σ J n Φ ((stabilizer₂ (AF F) σ J).subtype u * g) = phiA σ J n Φ g := by
    intro u hu g
    obtain ⟨w, hw⟩ := exists_ratH (AF F) σ _ (u : HA (AF F) σ (hypOne J)) hu
    have hw0 : gact σ w (e0 E M) = e0 E M := by
      have h1 : actW (AF F) σ (hypOne J) (u : HA (AF F) σ (hypOne J)) (e0 _ M) = e0 _ M := u.2
      rw [hw, hfix, ← ratTup_e0] at h1
      exact ratTup_adele_injective (F := F) h1
    have hw1 : gact σ w⁻¹ (e0 E M) = e0 E M := by
      conv_lhs => rw [← hw0]
      exact gact_inv_gact σ w _
    have e : ∀ X : Fin (n + 1) → Fin (M + 2) → E,
        actW (AF F) σ _ ((stabilizer₂ (AF F) σ J).subtype u * g)⁻¹ (ratTup (AF F) X) =
          actW (AF F) σ _ g⁻¹ (ratTup (AF F) (gact σ w⁻¹ X)) := by
      intro X
      rw [mul_inv_rev, hmul]
      change actW (AF F) σ _ g⁻¹ (actW (AF F) σ _ (u : HA (AF F) σ (hypOne J))⁻¹ (ratTup (AF F) X)) = _
      rw [hw, ratH_inv, actW_ratH']
    simp only [phiA, e]
    exact GlobalTheory.T.frames_sum_invariant_under_stabiliser F E σ M J n w⁻¹ hw1 (fun X => Φ (actW (AF F) σ _ g⁻¹ (ratTup (AF F) X)))
  have hΓ : ∀ u ∈ ratP (AF F) σ J, (stabilizer₂ (AF F) σ J).subtype u ∈ Γ := fun u hu => hu
  have hrinv : ∀ q, gact σ (rr q)⁻¹ (e0 E M) = q.1 := by
    intro q
    rw [← hrr q, gact_inv_gact]
  have huniq : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ ratP (AF F) σ J, γ = (stabilizer₂ (AF F) σ J).subtype u * r q := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := exists_ratH (AF F) σ _ γ hγ
    have hy := hgq g⁻¹ _ he0
    let q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := ⟨_, hy⟩
    have hst : ratH (AF F) σ _ g * (r q)⁻¹ ∈ stabilizer₂ (AF F) σ J := by
      change actW (AF F) σ _ (ratH (AF F) σ _ g * (r q)⁻¹) (e0 _ M) = e0 _ M
      have e1 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      rw [hmul, e1, hfix, hrinv, actW_ratH']
      change ratTup (AF F) (gact σ g (gact σ g⁻¹ _)) = _
      rw [gact_gact_inv, ratTup_e0]
    have hmemu : (⟨_, hst⟩ : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J :=
      Subgroup.mul_mem Γ (ratH_mem _ σ _ g) (Subgroup.inv_mem Γ (ratH_mem _ σ _ (rr q)))
    refine ⟨q, ⟨⟨_, hst⟩, hmemu, ?_⟩, ?_⟩
    · change ratH (AF F) σ _ g = ratH (AF F) σ _ g * (r q)⁻¹ * r q
      rw [inv_mul_cancel_right]
    rintro q' ⟨u', -, he⟩
    apply Subtype.ext
    apply ratTup_adele_injective (F := F)
    have e1 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹ (e0 _ M) = ratTup (AF F) q.1 := by
      rw [ratH_inv, hfix]
    have e2 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹ (e0 _ M) = ratTup (AF F) q'.1 := by
      have e3 : (r q')⁻¹ = ratH (AF F) σ _ (rr q')⁻¹ := ratH_inv _ σ _ _
      have h6 : (ratH (AF F) σ _ g)⁻¹ = (r q')⁻¹ * ((u'⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) := by
        rw [he, mul_inv_rev]
        rfl
      have h7 : actW (AF F) σ (hypOne J) ((u'⁻¹ : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (e0 _ M) = e0 _ M :=
        (u'⁻¹).2
      rw [h6, hmul, h7, e3, hfix, hrinv]
    rw [← e1, ← e2]
  have key := GlobalTheory.T.quotient_measure_tower _ _ (stabilizer₂ (AF F) σ J).subtype hPc.isClosedEmbedding_subtypeVal μ μP Γ
    (ratP (AF F) σ J) 𝓕 𝓕P h𝓕 h𝓕P hPf hΓ _ r (fun q => ratH_mem _ σ _ _) huniq (phiA σ J n Φ) hφ hinv
  have hA : ∀ h : HA (AF F) σ (hypOne J),
      ∑' Y : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E),
        Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y.1)) = ∑' q, phiA σ J n Φ (r q * h) := by
    intro h
    rw [GlobalTheory.T.isotropic_frames_sum_by_orbit F E σ M J n rr hrr (fun Y => Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y)))]
    refine tsum_congr fun q => tsum_congr fun X => ?_
    have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
    rw [mul_inv_rev, hmul, e3, actW_ratH']
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 2) _ hJb μ 𝓕 hμ h𝓕 (n + 1) _ Φ hΦ,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 2) _ hJb μ 𝓕 hμ h𝓕 1 _ Ψ hΨ]
  congr 1
  calc _ = ∫⁻ h in 𝓕, ∑' q, phiA σ J n Φ (r q * h) ∂μ := lintegral_congr hA
    _ = _ := key
    _ = _ := by
      refine lintegral_congr fun h => tsum_congr fun q => ?_
      have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      refine (hmean (r q * h)).trans ?_
      rw [mul_inv_rev, hmul, e3, hfix, hrinv]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegralStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_unfolding_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (μ : Measure (HA (AF F) σ (hypOne J))) 𝓕, IsHaarH F E σ (M + 2) (hypOne J) μ → IsFDH F E σ (M + 2) (hypOne J) μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∫⁻ X, Φ X ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E))) = ∫⁻ y, Ψ y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames <;> assumption)
end
