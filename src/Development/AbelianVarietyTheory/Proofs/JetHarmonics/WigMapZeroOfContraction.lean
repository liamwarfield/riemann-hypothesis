module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
public import Formalism.HermitianCurvature.StatementTBB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₂ →L[ℂ] V₂)) (φ : V₂ →L[ℂ] V₁), (∀ v, ‖φ v‖ ≤ ‖v‖) → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, ∀ v, φ (π₂ h v) = π₁ h (φ v)) → _root_.GlobalTheory.WigSh.WigMap k r z π₂ π₁ 0 (fun _ => φ) := by
  intro V₁ _ _ V₂ _ _ k r z π₁ π₂ φ hφ heqv
  refine ⟨⟨1, fun _ => 1, fun _ => φ, fun _ => by simp, fun ω => by simp⟩,
    fun h hh ω => ?_, fun t ω => by simp, fun ω _ _ => ?_⟩
  · ext v
    exact heqv h hh v
  · have hle : ‖φ‖ ≤ 1 := φ.opNorm_le_bound zero_le_one (fun v => by simpa using hφ v)
    rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) hle

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationOfForallGeometricPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EigenAll

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split <;> simp

theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  rw [gs_eq f y U h, gs_eq f y U h, gs_eq f y U h, map_sub, map_sub]

theorem exists_defect {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H) (V : G.Opens) (t : Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        gs (g ≫ m) z V t - gs (g ≫ p) z ⊤ u * gs (g ≫ s) z V t := by
  have hp : m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V ≤ p ⁻¹ᵁ (⊤ : H.Opens) := fun _ _ => trivial
  refine ⟨(Y.presheaf.map (homOfLE inf_le_left).op).hom ((m.app V).hom t) -
    (Y.presheaf.map (homOfLE hp).op).hom ((p.app ⊤).hom u) *
      (Y.presheaf.map (homOfLE inf_le_right).op).hom ((s.app V).hom t), ?_⟩
  intro Z g z hz
  rw [gs_sub g z _ hz, gs_mul g z _ hz, gs_res g z _ hz, gs_res g z _ hz, gs_res g z _ hz,
    gs_pull g m z V hz.1, gs_pull g p z ⊤ trivial, gs_pull g s z V hz.2]

end GlobalTheory.EigenAll

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyThroughDiscreteSeries
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem family_through_discreteSeries : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep k r), Num k r lam u b bv ga h q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 k r) lam →
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R 0 = R0 := by
  intro hH k r lam u b bv ga h q0 R0 hN hR0
  classical
  have hex : DSExist := hH.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have hfam := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = 0 → R = R0) := by
    intro ν
    by_cases h0 : ν = 0
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      simpa using hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR 0).2 rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem wigMap_comp : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (V₃ : Type) [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (π₃ : Mx k r → (V₃ →L[ℂ] V₃)) (d e : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) (A' : (Fin (2 * r + k + 1) → ℂ) → (V₃ →L[ℂ] V₂)), GlobalTheory.WigSh.WigMap k r z π₂ π₁ d A → GlobalTheory.WigSh.WigMap k r z π₃ π₂ e A' → GlobalTheory.WigSh.WigMap k r z π₃ π₁ (d + e) (fun ω => (A ω).comp (A' ω)) := by
  intro V₁ _ _ V₂ _ _ V₃ _ _ k r z π₁ π₂ π₃ d e A A' hA hA'
  obtain ⟨⟨t, q, L, hq, hL⟩, h2, h3, h4⟩ := hA
  obtain ⟨⟨t', q', L', hq', hL'⟩, h2', h3', h4'⟩ := hA'
  refine ⟨⟨t * t', fun i => q (finProdFinEquiv.symm i).1 * q' (finProdFinEquiv.symm i).2,
    fun i => (L (finProdFinEquiv.symm i).1).comp (L' (finProdFinEquiv.symm i).2), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hq _) (hq' _))
  · intro ω
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin t × Fin t' =>
      MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q p.1 * q' p.2) • (L p.1).comp (L' p.2)),
      Fintype.sum_prod_type]
    show (A ω).comp (A' ω) = _
    rw [hL ω, hL' ω]
    ext x
    simp only [ContinuousLinearMap.comp_apply, sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, smul_smul]
  · intro h hh ω
    show ((A (h *ᵥ ω)).comp (A' (h *ᵥ ω))).comp (π₃ h) = (π₁ h).comp ((A ω).comp (A' ω))
    rw [ContinuousLinearMap.comp_assoc, h2' h hh, ← ContinuousLinearMap.comp_assoc, h2 h hh,
      ContinuousLinearMap.comp_assoc]
  · intro s ω
    show (A ((s : ℂ) • ω)).comp (A' ((s : ℂ) • ω)) = ((s : ℂ) ^ (d + e)) • (A ω).comp (A' ω)
    rw [h3, h3', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_add]
  · intro ω hω hz
    show ‖(A ω).comp (A' ω)‖ ^ 2 ≤ _
    have a := h4 ω hω hz
    have b := h4' ω hω hz
    calc ‖(A ω).comp (A' ω)‖ ^ 2 ≤ (‖A ω‖ * ‖A' ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
      _ = ‖A ω‖ ^ 2 * ‖A' ω‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := by
          rw [pow_add]
          exact mul_le_mul a b (sq_nonneg _) ((sq_nonneg _).trans a)

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieUnitaryElementSimpleRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieUnitaryElementSimpleRoot
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnipotentElement

open Formalism.HermitianLatticeCounting.ExpansionTerms

theorem exp_of_cube_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A * A * A = 0) (t : ℂ) :
    NormedSpace.exp (t • A) = 1 + t • A + (t ^ 2 / 2) • (A * A) := by
  have h3 : A ^ 3 = 0 := by rw [pow_three']; exact h
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_pow, smul_smul, pow_two A]
    simp [Nat.factorial, div_eq_inv_mul]
  · intro b hb
    have hb3 : 3 ≤ b := by simpa using hb
    rw [smul_pow, pow_eq_zero_of_le hb3 h3, smul_zero, smul_zero]

theorem ymat_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (e v : Fin n → ℂ) :
    rankTwoSkewMatrix H e v = vecMulVec e (star v) * H - vecMulVec v (star e) * H := by
  ext i j
  simp [rankTwoSkewMatrix, Formalism.QuantumDeterminants.herm, Matrix.mul_apply, vecMulVec_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

theorem ymat_skew {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (e v : Fin n → ℂ) :
    (rankTwoSkewMatrix H e v)ᴴ * H + H * rankTwoSkewMatrix H e v = 0 := by
  rw [ymat_eq, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH, conjTranspose_vecMulVec,
    conjTranspose_vecMulVec, star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Matrix.mul_assoc]
  abel

theorem form_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (x y : EuclideanSpace ℂ (Fin n)) :
    majorantHermitianForm (Matrix.toEuclideanLin H) x y = Formalism.QuantumDeterminants.herm H x.ofLp y.ofLp := by
  unfold majorantHermitianForm Formalism.QuantumDeterminants.herm
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  show star (H *ᵥ y.ofLp) ⬝ᵥ x.ofLp = _
  rw [star_mulVec, hH, dotProduct_mulVec]

theorem isTheta {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) :
    IsSelfAdjointInvolution (Matrix.toEuclideanLin H) := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · apply WithLp.ofLp_injective
    show H *ᵥ (H *ᵥ x.ofLp) = x.ofLp
    rw [mulVec_mulVec, hHH, one_mulVec]
  · exact (Matrix.isSymmetric_toEuclideanLin_iff.2 hH) x y

theorem ymat_hs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (e v : EuclideanSpace ℂ (Fin n)) :
    ∑ i, ∑ j, ‖rankTwoSkewMatrix H e.ofLp v.ofLp i j‖ ^ 2 ≤ 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_hilbert_schmidt_bound _ _ (isTheta H hH hHH) n (EuclideanSpace.basisFun (Fin n) ℂ) e v
  refine le_of_eq_of_le ?_ h
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [form_eq H hH, form_eq H hH, EuclideanSpace.basisFun_inner]
  simp [rankTwoSkewMatrix]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

theorem exists_element : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, ∀ a : Fin r, ∃ X : Mx k r, PI.UpqRep.InLieHpk k r X ∧ (∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ 4 * lenA k r z g a.castSucc ^ 2) ∧ ∀ t : ℝ, ∃ m ∈ Formalism.QuantumDeterminants.Nset k r, g * NormedSpace.exp ((t : ℂ) • X) = m * g ∧ Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m = Complex.exp (-(2 * (lenA k r z g a.succ : ℂ) * (t : ℂ)) * Complex.I) := by
  intro k r z hz hT g hg a
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := GlobalTheory.TensLen.isUnit_det_of_unitary hHH hg
  have hHu : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := Matrix.isUnit_det_of_left_inverse hHH
  have hpos := (GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1 a.succ
  obtain ⟨e', v', he, hen, hvn, hv0, hv1⟩ := Formalism.HermitianLatticeCounting.P.majorant_parameter_choice_holds _ _ (isTheta _ hH hHH) r
    (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a hpos.ne'
  have hgg : ∀ x : Fin (2 * r + k + 1) → ℂ, g *ᵥ (g⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hgg' : ∀ x : Fin (2 * r + k + 1) → ℂ, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hform : ∀ b, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) (g *ᵥ v'.ofLp) =
      majorantHermitianForm (Matrix.toEuclideanLin (Formalism.QuantumDeterminants.Hpk k r))
        (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b)) v' := fun b => by
    rw [form_eq _ hH, ← herm_mulVec hg (WithLp.ofLp _) v'.ofLp, WithLp.ofLp_toLp, hgg]
  have hE : g *ᵥ e'.ofLp - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
      Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) := by
    have h1 := Submodule.mem_map_of_mem
      (f := (Matrix.mulVecLin g).comp (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap) he
    rw [Submodule.map_span, Set.image_image] at h1
    simpa [mulVec_sub, hgg, -mulVec_mulVec] using h1
  have hV0 : ∀ b, b ≤ a.castSucc →
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) (g *ᵥ v'.ofLp) = 0 := fun b hb => by
    rw [hform]; exact hv0 b hb
  have hV1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) (g *ᵥ v'.ofLp) =
      -Complex.I * (lenA k r z g a.succ : ℂ) := by
    rw [hform]; exact hv1
  obtain ⟨h3, -, hN⟩ := Formalism.HermitianLatticeCounting.P.nilpotent_model_computation_holds k r z hz a _ _ hE hV0
  have hpsi := Formalism.HermitianLatticeCounting.P.derivative_of_psi_holds k r z hz a _ _ 1 _ hE hV0 hV1
  have hAd := Formalism.HermitianLatticeCounting.P.matrix_adjoint_action_holds _ _ hHu g hg (g *ᵥ e'.ofLp) (g *ᵥ v'.ofLp)
  rw [hgg', hgg'] at hAd
  refine ⟨rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e'.ofLp v'.ofLp, ymat_skew _ hH _ _, ?_, fun t => ⟨_, (hN t).1, ?_, ?_⟩⟩
  · have h := ymat_hs _ hH hHH e' v'
    rw [hvn, hen, one_pow, mul_one] at h
    exact h
  · rw [← hAd, ← Matrix.smul_mul, ← Matrix.mul_smul,
      Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hu), exp_of_cube_eq_zero _ h3,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    rfl
  · simpa using hpsi t

end GlobalTheory.UnipotentElement
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieUnitaryElementSimpleRootStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_unitary_element_simple_root : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, ∀ a : Fin r, ∃ X : Mx k r, PI.UpqRep.InLieHpk k r X ∧ (∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ 4 * lenA k r z g a.castSucc ^ 2) ∧ ∀ t : ℝ, ∃ m ∈ Formalism.QuantumDeterminants.Nset k r, g * NormedSpace.exp ((t : ℂ) • X) = m * g ∧ Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m = Complex.exp (-(2 * (lenA k r z g a.succ : ℂ) * (t : ℂ)) * Complex.I) := by
  first | exact @GlobalTheory.UnipotentElement.exists_element | exact GlobalTheory.UnipotentElement.exists_element | (intros; apply GlobalTheory.UnipotentElement.exists_element <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerDOpOfStabiliser
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory

theorem intertwiner_dOp_of_stabiliser {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁]
    [FiniteDimensional ℂ V₁] {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂]
    [FiniteDimensional ℂ V₂] {k r : ℕ} {z e : Fin (2 * r + k + 1) → ℂ}
    {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →L[ℂ] V₂)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂)
    (hT : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v))
    {X : Mx k r} (hX : InLieW k r z X) (he : X *ᵥ e = 0) (v : V₁) :
    T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have d₁ := dOp_hasDeriv h₁.1 h₁.2 hX
  have d₂ := dOp_hasDeriv h₂.1 h₂.2 hX
  have e₁ := ((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₁
  have e₂ := ((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₂
  have hf : (((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • X))) =
      (((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact hT _ (exp_uw hX t) (Qx8.exp_fix he t) v
  rw [hf] at e₁
  exact e₁.unique e₂

theorem intertwiner_EB_of_stabiliser : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r m : ℕ) (z e : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →L[ℂ] V₂) (B : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z, e] B → (∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v)) → ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r m z e π₁ π₂ T B h₁ h₂ hB hT a b v
  have hz : IsFrameOf k r [z] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have he : IsFrameOf k r [e] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have lz := frame_lie hz a b
  have le := frame_lie he a b
  have p1 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.1 le.1.2 v
  have p2 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.2 le.2.2 v
  show T (ecOp π₁ (unitB (Hpk k r) B a b) v) = ecOp π₂ (unitB (Hpk k r) B a b) (T v)
  unfold ecOp
  simp only [_root_.add_apply, _root_.smul_apply, map_add (f := _), map_smul, p1, p2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.FrameExpansion

private lemma herm_mulVec_invariant {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w := by
  simp only [_root_.Formalism.QuantumDeterminants.herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hH]

private lemma inWb_of_coords_eq_zero {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ}
    (h1 : ∀ a, v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0) (h2 : ∀ a, v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0) : _root_.Formalism.QuantumDeterminants.inWb k r v := by
  intro i hi
  rcases hi with hi | hi
  · have e : _root_.Formalism.QuantumDeterminants.eI k r ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← e]; exact h1 _
  · have e : _root_.Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i, by omega⟩ = i :=
      Fin.ext (show 2 * r + k - (2 * r + k - (i : ℕ)) = i by omega)
    rw [← e]; exact h2 _

private lemma herm_bvec_esI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.esI k r a)) = v (_root_.Formalism.QuantumDeterminants.eI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma coord_eI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0 :=
  hv _ (Or.inl (show (a : ℕ) < r from a.2))

private lemma herm_bvec_eI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) = v (_root_.Formalism.QuantumDeterminants.esI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma coord_esI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0 :=
  hv _ (Or.inr (show r + k < 2 * r + k - (a : ℕ) by have := a.2; omega))

theorem _root_.GlobalTheory.FrameExpansion.frame_expansion_uw_group :
    ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B → (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → w = ∑ c, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w (B c) • B c) ∧ ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → _root_.Formalism.QuantumDeterminants.inWb k r (h *ᵥ w) ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ w) z = 0) ∧ (∀ v w, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w) ∧ h⁻¹ ∈ _root_.Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1 ∧ h⁻¹ * h = 1 ∧ ∀ h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, h * h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  intro k r z B hz hT hB
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  refine ⟨fun w hw hwz => _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz, ?_⟩
  intro h hh
  have hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r := hh.1
  have hinv := herm_mulVec_invariant hH
  have hfz : h *ᵥ z = z := hh.2.2
  have hdet : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  refine ⟨fun w hw hwz => ⟨?_, ?_⟩, hinv, _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh, mul_nonsing_inv h hdet,
    nonsing_inv_mul h hdet, fun h' hh' => _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh hh'⟩
  · apply inWb_of_coords_eq_zero
    · intro a
      rw [← herm_bvec_esI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).2, hinv, herm_bvec_esI_jet_harmonics]
      exact coord_eI_eq_zero_of_inWb hw a
    · intro a
      rw [← herm_bvec_eI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).1, hinv, herm_bvec_eI_jet_harmonics]
      exact coord_esI_eq_zero_of_inWb hw a
  · rw [← hfz, hinv, hwz]

end GlobalTheory.FrameExpansion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LoweringBound
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PieriBound

theorem bound_cast (k M n : ℕ) (hn : n = k + M) (lam mu : Fin n → ℝ) (u : ℕ → ℝ) (b bv ga q0 : ℝ) (s : Fin n)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (h1 : StrictAnti lam) (h2 : ∀ a c, ∃ z : ℤ, lam a - lam c = (z : ℝ))
    (h3 : ∀ a, ∀ i ∈ Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2)
    (h4 : ∀ a : Fin n, a.val < k → lam a < u (a.val + 1))
    (h5 : ∀ a : Fin n, a.val + 1 < k → u (a.val + 2) < lam a)
    (h6 : ∀ a : Fin n, a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8)
    (h7 : ∀ a : Fin n, k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv)
    (h8 : ∀ a, |lam a| ≤ b) (h9 : ∀ i ∈ Icc 1 k, |u i| ≤ b)
    (h10 : ∀ a c : Fin n, a < c → c.val + 1 < k → ga ≤ lam a - lam c) (h11 : 4 ≤ ga)
    (h12 : ∀ a, ∃ z : ℤ, mu a - lam a = (z : ℝ)) (h13 : StrictAnti mu)
    (h14 : ∑ a, |mu a - lam a| ≤ q0) (h15 : q0 ≤ ga / 8) (h16 : q0 ≤ bv / 4) (h17 : q0 ≤ b)
    (h18 : ∀ s', s' ≠ s → mu s - 1 ≠ mu s') :
    (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2 := by
  subst hn
  have hmem : ∀ i : Fin k, (i : ℕ) + 1 ∈ Icc 1 k := fun i => by
    rw [Finset.mem_Icc]; have := i.2; omega
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.sup_l2_ratio_majorant k M lam mu (fun i => u (i.val + 1)) b bv ga q0 s hk hM
    ⟨h1, h2, fun a i => h3 a _ (hmem i), fun i => h4 (Fin.castAdd M i) i.2,
      fun i j hij => by
        have := h5 (Fin.castAdd M i) (by have := j.2; simp only [Fin.val_castAdd]; omega)
        simp only [Fin.val_castAdd] at this
        show u (j.val + 1) < _
        rw [← hij]; exact this,
      h6, h7, h8, fun i => h9 _ (hmem i), h10, h11, h12, h13, h14, h15, h16, h17⟩ h18
  have e : (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) = ∏ i : Fin k, |mu s - 1 / 2 - u (i.val + 1)| := by
    rw [Fin.prod_univ_eq_prod_range (fun i => |mu s - 1 / 2 - u (i + 1)|) k, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun i => |mu s - 1 / 2 - u i|) 0 k 1]
    rfl
  rw [e]; exact key

theorem lowering_bound : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → ∀ s, (∏ i ∈ Icc 1 k, |lam s + (ν s : ℝ) - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| ≤ b ^ 4 := by
  intro k r lam u b bv ga h q0 hN ν hν s
  obtain ⟨⟨hb, hbv, -, hq, -⟩, hf⟩ := GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN
  obtain ⟨-, -, -, hgap⟩ := hf ν hν
  obtain ⟨hk, hHC, h3, h4, h5, h6, h7, h8, h9, h10, -, -, hga, -, hbig⟩ := hN
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have key := bound_cast k (2 * r + 1) (2 * r + k + 1) (by omega) lam (fun a => lam a + (ν a : ℝ)) u b bv ga q0 s hk
    (by omega) hHC.1
    (fun a c => by
      obtain ⟨m, hm⟩ := hHC.2 a
      obtain ⟨m', hm'⟩ := hHC.2 c
      exact ⟨m - m', by push_cast at hm hm' ⊢; linarith⟩) h3 h4 h5 h6 h7 h8 h9 h10 (by linarith)
    (fun a => ⟨ν a, by ring⟩) (fun a c hac => by have := hgap a c hac; show _ < _; linarith)
    (by
      have : ((n1 ν : ℕ) : ℝ) ≤ q0 := by exact_mod_cast hν
      refine le_trans (le_of_eq ?_) this
      unfold n1
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      simp)
    (by linarith) (by linarith) (by linarith)
    (fun t ht => by
      rcases lt_or_gt_of_ne ht with hlt | hlt
      · have := hgap t s hlt
        intro e; linarith
      · have := hgap s t hlt
        intro e; linarith)
  refine key.trans ?_
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hb0 : (0 : ℝ) ≤ b := by linarith
  split_ifs
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hkn : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hp : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 :=
      le_self_pow₀ (by linarith) (by norm_num)
    have h64 : 64 * Real.exp 1 * Real.sqrt k ≤ b := by
      have : Real.exp 1 * Real.sqrt k ≤ 3 * k := mul_le_mul he hs (Real.sqrt_nonneg _) (by norm_num)
      norm_num at hbig hp hkn ⊢
      nlinarith
    calc _ ≤ b * b ^ 3 := mul_le_mul_of_nonneg_right h64 (by positivity)
      _ = b ^ 4 := by ring
  · have h16 : 16 * Real.exp 1 ≤ b ^ 2 := by nlinarith
    calc _ ≤ b ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = b ^ 4 := by ring

end GlobalTheory.PieriBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedCutoff
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory
namespace QuotCutoff

def mulM {m : ℕ} (a b : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a * Matrix.of b) i j

lemma continuous_mulM {m : ℕ} : Continuous (fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma mulM_assoc {m : ℕ} (a b c : PI.MtM m) : mulM (mulM a b) c = mulM a (mulM b c) :=
  Matrix.mul_assoc (Matrix.of a) (Matrix.of b) (Matrix.of c)

lemma continuous_mulM_left {m : ℕ} (x : PI.MtM m) : Continuous (fun s => mulM s x) :=
  continuous_mulM.comp (continuous_id.prodMk continuous_const)

def invM {m : ℕ} (a : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a)⁻¹ i j

lemma continuousAt_invM {m : ℕ} (a : PI.MtM m) (h : Matrix.of a * (Matrix.of a)⁻¹ = 1) :
    ContinuousAt invM a := by
  have hu : IsUnit (Matrix.of a).det := Matrix.isUnit_det_of_right_inverse h
  have h1 : ContinuousAt Ring.inverse (Matrix.of a).det := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact continuousAt_matrix_inv (Matrix.of a) h1

def piece {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (j : ℕ) : Set (PI.MtM m) :=
  {x | Matrix.of x ∈ G} ∩ Metric.closedBall 0 (j : ℝ)

lemma isClosed_of {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) :
    IsClosed {x : PI.MtM m | Matrix.of x ∈ G} := hG

lemma isCompact_piece {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) (j : ℕ) :
    IsCompact (piece G j) :=
  (isCompact_closedBall _ _).inter_left (isClosed_of hG)

lemma exists_bound {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) (j : ℕ) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ x : PI.MtM m, μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ c := by
  have hC := isCompact_piece hG.1 j
  set K : Set (PI.MtM m) :=
    (fun p : PI.MtM m × PI.MtM m => mulM p.1 (invM p.2)) '' (piece G j ×ˢ piece G j) with hK
  have hKc : IsCompact K := by
    refine (hC.prod hC).image_of_continuousOn ?_
    rintro ⟨a, b⟩ ⟨-, hb⟩
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun p : PI.MtM m × PI.MtM m => invM p.2) (a, b) :=
      ContinuousAt.comp (g := invM) (f := fun p : PI.MtM m × PI.MtM m => p.2) (x := (a, b))
        (continuousAt_invM b (hG.2.2.2 (Matrix.of b) hb.1).2) continuousAt_snd
    exact ContinuousAt.comp (g := fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2)
      (f := fun p : PI.MtM m × PI.MtM m => (p.1, invM p.2))
      continuous_mulM.continuousAt (continuousAt_fst.prodMk h1)
  have hKS : IsCompact (K ∩ {x | Matrix.of x ∈ S}) := hKc.inter_right (isClosed_of hS.1)
  refine ⟨μ (K ∩ {x | Matrix.of x ∈ S}),
    (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.1 _ hKS (fun x hx => hx.2), fun x => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hA : MeasurableSet ((fun s => mulM s x) ⁻¹' piece G j) :=
    (hC.isClosed.preimage (continuous_mulM_left x)).measurableSet
  by_cases h : ∃ s₀ : PI.MtM m, Matrix.of s₀ ∈ S ∧ mulM s₀ x ∈ piece G j
  · obtain ⟨s₀, hs₀, hx⟩ := h
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    rw [← h1, Measure.map_apply (continuous_mulM_left s₀).measurable hA, h1]
    refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    refine ⟨⟨(mulM t (mulM s₀ x), mulM s₀ x), ⟨?_, hx⟩, ?_⟩, ht⟩
    · rw [← mulM_assoc]; exact hti
    · have h2 := (hG.2.2.2 (Matrix.of (mulM s₀ x)) hx.1).2
      change Matrix.of t * Matrix.of (mulM s₀ x) * (Matrix.of (mulM s₀ x))⁻¹ = Matrix.of t
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  · refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    exact absurd ⟨t, ht, hti⟩ h

lemma exists_pos {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (x : PI.MtM m) (hx : Matrix.of x ∈ G) :
    ∃ j : ℕ, 0 < μ ((fun s => mulM s x) ⁻¹' piece G j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
  refine ⟨j, ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hU : IsOpen ((fun s => mulM s x) ⁻¹' Metric.ball 0 (j : ℝ)) :=
    Metric.isOpen_ball.preimage (continuous_mulM_left x)
  have h1 : mulM (Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)) x = x :=
    Matrix.one_mul (Matrix.of x)
  have := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.2 _ hU
    ⟨Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ), by
      rw [Set.mem_preimage, h1]; simpa using hj, hS.2.1⟩
  refine this.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with t ht hti
  exact ⟨hG.2.2.1 _ (hSG ht) _ hx, Metric.ball_subset_closedBall hti⟩

lemma exists_precutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) :
    ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (mulM s x) ∂μ ≠ 0 ∧ ∫⁻ s, φ (mulM s x) ∂μ ≠ ⊤ := by
  choose c hc hb using exists_bound hG hS hμ hR
  have hP : ∀ j, MeasurableSet (piece G j) := fun j => (isCompact_piece hG.1 j).measurableSet
  set w : ℕ → ℝ≥0∞ := fun j => (2⁻¹ : ℝ≥0∞) ^ j * (1 + c j)⁻¹ with hw
  have hmeas : ∀ j, Measurable ((piece G j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hP j)
  have hI : ∀ x : PI.MtM m, ∫⁻ s, (∑' j, (piece G j).indicator (fun _ => w j) (mulM s x)) ∂μ
      = ∑' j, w j * μ ((fun s => mulM s x) ⁻¹' piece G j) := by
    intro x
    rw [lintegral_tsum (f := fun j s => (piece G j).indicator (fun _ => w j) (mulM s x))
      (fun j => ((hmeas j).comp (continuous_mulM_left x).measurable).aemeasurable)]
    congr 1
    ext j
    rw [← lintegral_indicator_const ((continuous_mulM_left x).measurable (hP j))]
    rfl
  refine ⟨fun y => ∑' j, (piece G j).indicator (fun _ => w j) y,
    Measurable.tsum hmeas, fun x hx => ?_⟩
  rw [hI x]
  constructor
  · obtain ⟨j, hj⟩ := exists_pos hG hS hSG hμ x hx
    intro h
    rw [ENNReal.tsum_eq_zero] at h
    have hwj : w j ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (by simp)) ?_
      rw [ENNReal.inv_ne_zero]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, (hc j).ne⟩
    exact mul_ne_zero hwj hj.ne' (h j)
  · refine ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) ?_
      (ENNReal.tsum_le_tsum fun j => ?_)
    · rw [ENNReal.tsum_geometric]
      simp
    · have h1 : (1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ 1 := by
        calc _ ≤ (1 + c j)⁻¹ * (1 + c j) := by
              gcongr
              exact (hb j x).trans le_add_self
          _ ≤ 1 := ENNReal.inv_mul_le_one _
      calc w j * _ = (2⁻¹ : ℝ≥0∞) ^ j * ((1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j)) :=
            mul_assoc _ _ _
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ j * 1 := by gcongr
        _ = _ := mul_one _

end QuotCutoff

open QuotCutoff in
theorem exists_normalised_cutoff : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G → ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
  intro m G S μ hG hS hSG hμ hR
  obtain ⟨φ, hφ, hI⟩ := exists_precutoff hG hS hSG hμ hR
  haveI := hμ.1
  set I : PI.MtM m → ℝ≥0∞ := fun x => ∫⁻ s, φ (mulM s x) ∂μ with hIdef
  have hIm : Measurable I :=
    Measurable.lintegral_prod_left' (f := fun p : PI.MtM m × PI.MtM m => φ (mulM p.1 p.2))
      (hφ.comp continuous_mulM.measurable)
  have hinv : ∀ s₀ x : PI.MtM m, Matrix.of s₀ ∈ S → I (mulM s₀ x) = I x := by
    intro s₀ x hs₀
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    have h2 := lintegral_map (μ := μ) (f := fun s => φ (mulM s x))
      (hφ.comp (continuous_mulM_left x).measurable) (continuous_mulM_left s₀).measurable
    rw [h1] at h2
    simp only [hIdef]
    rw [h2]
    simp only [mulM_assoc]
  refine ⟨fun y => φ y * (I y)⁻¹, hφ.mul hIm.inv, fun x hx => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  calc ∫⁻ s, φ (mulM s x) * (I (mulM s x))⁻¹ ∂μ = ∫⁻ s, φ (mulM s x) * (I x)⁻¹ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        rw [hinv s x hs]
    _ = I x * (I x)⁻¹ := lintegral_mul_const _ (hφ.comp (continuous_mulM_left x).measurable)
    _ = 1 := ENNReal.mul_inv_cancel (hI x hx).1 (hI x hx).2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopNum
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopNum

theorem hsq_le (r : ℕ) (T b C : ℝ) (hC : 0 ≤ C) (hb : 2 ≤ b)
    (hT : T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ))) :
    Hsq r T b ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h1 : (1 : ℝ) ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hb1 (mul_nonneg hC (Nat.cast_nonneg _))
  have h2 : max 1 T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) := max_le h1 hT
  have h3 : (C + 10) * ((2 * r + 2 : ℕ) : ℝ)
      = C * ((2 * r + 2 : ℕ) : ℝ) + ((20 * (r + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3, Real.rpow_add hb0, Real.rpow_natCast]
  unfold Hsq
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hb0.le _)

theorem top_num : ∀ (r : ℕ) (T T' b C : ℝ), 0 ≤ C → 2 ≤ b → T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → T' ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → Real.sqrt (Hsq r T b * Hsq r T' b) ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  intro r T T' b C hC hb hT hT'
  have hb0 : 0 < b := by linarith
  have h1 := hsq_le r T b C hC hb hT
  have h2 := hsq_le r T' b C hC hb hT'
  have hp : 0 ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hb0.le _
  have h0 : 0 ≤ Hsq r T' b := by
    unfold Hsq
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (pow_nonneg hb0.le _)
  rw [Real.sqrt_le_left hp, sq]
  exact mul_le_mul h1 h2 h0 hp

end GlobalTheory.TopNum
end
