module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLogStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodular
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory

theorem coverUnitary_unimodular :
    ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧
      LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G :=
  fun p q T => ⟨(GlobalTheory.HolDS.haar_unimodular p q T).1, (GlobalTheory.HolDS.haar_unimodular p q T).2,
    GlobalTheory.HolDS.instLocallyCompact T, GlobalTheory.HolDS.instSecondCountable T, GlobalTheory.HolDS.t2Space_cuspAdeles T⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodularStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPQCover_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧ LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G := by
  first | exact @GlobalTheory.coverUnitary_unimodular | exact GlobalTheory.coverUnitary_unimodular | (intros; apply GlobalTheory.coverUnitary_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompact
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem isClosed_Kset {p q : ℕ} (T : GrpData p q) : IsClosed T.Kset := by
  have h : T.Kset = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : T.G | matG T x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_eq ((continuous_matG T).matrix_elem a b) continuous_const

theorem isCompact_Kset : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  intro p q T
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Ix p q) (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const) (fun M hM => hM)
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hc.prod hS)).of_isClosed_subset
    (isClosed_Kset T) fun x hx => ⟨matG_star_mul T hx, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompactStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_detSqrtCover_maxCompact : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  first | exact @GlobalTheory.PolarU.isCompact_Kset | exact GlobalTheory.PolarU.isCompact_Kset | (intros; apply GlobalTheory.PolarU.isCompact_Kset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnP
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnP
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

private theorem jpq_eq_diagonal' (p q : ℕ) : Formalism.UG.Jpq p q =
    Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

private theorem mul_jpq_comm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) :
    X * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * X := by
  rw [jpq_eq_diagonal']
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (Sum.inl a) (Sum.inr b) (by simp [sameBlock])]
  · simp [hX (Sum.inr a) (Sum.inl b) (by simp [sameBlock])]
  · simp

private theorem Jpq_mul_Jpq_mul (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [jpq_eq_diagonal', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

private theorem exists_UJ_umat_eq_of_inUJ {p q : ℕ} (g : Mat p q) (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q)
    (hK : IsKC g) : gᴴ * g = 1 := by
  calc gᴴ * g = gᴴ * g * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) := by rw [Jpq_mul_Jpq_mul, Matrix.mul_one]
    _ = gᴴ * (g * Formalism.UG.Jpq p q) * Formalism.UG.Jpq p q := by simp only [Matrix.mul_assoc]
    _ = gᴴ * Formalism.UG.Jpq p q * g * Formalism.UG.Jpq p q := by rw [mul_jpq_comm_of_isKC g hK]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jpq_mul_Jpq_mul]

private theorem unitary_inv_of_unitary {n : Type} [Fintype n] [DecidableEq n] (u : GL n ℂ)
    (hu : (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) = 1) :
    ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 := by
  have h1 : ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = (u : Matrix n n ℂ)ᴴ := by
    calc ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)
        = (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          rw [hu, Matrix.one_mul]
      _ = (u : Matrix n n ℂ)ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h1, Matrix.conjTranspose_conjTranspose, ← h1]
  exact Units.mul_inv u

private theorem conjTranspose_mul_self_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) : (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul, hB]

private theorem pY_mem_upq {p q : ℕ} (B : Fin p → Fin q → ℂ) : pY B ∈ upq p q := by
  show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
  rw [show Jm p q = Formalism.UG.Jpq p q from rfl, jpq_eq_diagonal']
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [pY, pOf, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem eq_pY_of_mem_pR {p q : ℕ} (Y : Mat p q) (hYm : Y ∈ pR p q) :
    Y = pY (fun i j => Y (Sum.inl i) (Sum.inr j)) := by
  have h2 : Y ∈ upq p q ∧ IsPC Y := hYm
  have hY : Yᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * Y = 0 := h2.1
  have hP : ∀ a b, sameBlock a b → Y a b = 0 := h2.2
  rw [jpq_eq_diagonal'] at hY
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]
  · simp [pY, pOf]
  · have h := congrArg (fun M : Mat p q => M (Sum.inr i) (Sum.inl j)) hY
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply] at h
    simp only [pY, pOf, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Matrix.of_apply]
    linear_combination -h
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]

theorem exists_action_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  intro p q T L hLc hL hdec g
  have hexp : ∀ X ∈ upq p q, ((T.cov (T.expt X) : GL _ ℂ) : Mat p q) = NormedSpace.exp X := T.16
  have hec : ContinuousOn T.expt (upq p q) := T.17
  have hcov : Continuous fun x : T.G => ((T.cov x : GL _ ℂ) : Mat p q) :=
    Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)
  have hKu : ∀ k ∈ T.Kset, ((T.cov k : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    exact exists_UJ_umat_eq_of_inUJ ((T.cov k : GL _ ℂ) : Mat p q) (T.cov_mem k) hk
  have hKinv : ∀ k ∈ T.Kset,
      ((T.cov k⁻¹ : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k⁻¹ : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    rw [map_inv]
    exact unitary_inv_of_unitary _ (hKu k hk)
  have hev : ∀ u : T.G, ((T.cov u : GL _ ℂ) : Mat p q)ᴴ * ((T.cov u : GL _ ℂ) : Mat p q) = 1 →
      ∀ C, L ((T.cov (u * T.expt (pY C)) : GL _ ℂ) : Mat p q) = C := by
    intro u hu C
    rw [map_mul, Units.val_mul, hexp _ (pY_mem_upq C)]
    exact hL _ C hu
  have hkey : ∀ h : T.G, ∃ k ∈ T.Kset,
      h = k * T.expt (pY (L ((T.cov h : GL _ ℂ) : Mat p q))) := by
    intro h
    obtain ⟨k, hk, Y, hY, rfl⟩ := hdec h
    obtain ⟨C, hC⟩ : ∃ C, Y = pY C := ⟨_, eq_pY_of_mem_pR Y hY⟩
    subst hC
    exact ⟨k, hk, by rw [hev k (hKu k hk) C]⟩
  refine ⟨fun B => L ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q), ?_, ?_, ?_⟩
  · have hof : Continuous fun B : Fin p → Fin q → ℂ => (Matrix.of B : Matrix (Fin p) (Fin q) ℂ) :=
      continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop
    have hpY : Continuous fun B : Fin p → Fin q → ℂ => pY B := by
      simp only [pY, pOf]
      exact Continuous.matrix_fromBlocks continuous_const hof hof.matrix_conjTranspose continuous_const
    have hE : Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) :=
      hec.comp_continuous hpY pY_mem_upq
    have hM : Continuous fun B : Fin p → Fin q → ℂ =>
        ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q) :=
      hcov.comp (hE.mul continuous_const)
    exact hLc.comp_continuous hM (fun B => (T.cov _).isUnit)
  · constructor
    · intro B1 B2 h12
      dsimp only at h12
      obtain ⟨k1, hk1, e1⟩ := hkey (T.expt (pY B1) * g)
      obtain ⟨k2, hk2, e2⟩ := hkey (T.expt (pY B2) * g)
      rw [← h12] at e2
      generalize L ((T.cov (T.expt (pY B1) * g) : GL _ ℂ) : Mat p q) = C at e1 e2
      have f1 := eq_mul_inv_of_mul_eq e1
      have f2 := eq_mul_inv_of_mul_eq e2
      have e3 : T.expt (pY B1) = (k1 * k2⁻¹) * T.expt (pY B2) := by
        rw [f1, f2]
        group
      have hB1 : L ((T.cov (1 * T.expt (pY B1)) : GL _ ℂ) : Mat p q) = B1 := hev 1 (by simp) B1
      have hB2 : L ((T.cov ((k1 * k2⁻¹) * T.expt (pY B2)) : GL _ ℂ) : Mat p q) = B2 :=
        hev _ (by rw [map_mul, Units.val_mul]; exact conjTranspose_mul_self_mul_eq_one _ _ (hKu k1 hk1) (hKinv k2 hk2)) B2
      rw [one_mul, e3] at hB1
      exact hB1.symm.trans hB2
    · intro C
      obtain ⟨k, hk, e⟩ := hkey (T.expt (pY C) * g⁻¹)
      refine ⟨L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q), ?_⟩
      dsimp only
      generalize L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q) = B at e ⊢
      have f := eq_inv_mul_of_mul_eq e.symm
      have e' : T.expt (pY B) * g = k⁻¹ * T.expt (pY C) := by
        rw [f]
        group
      rw [e']
      exact hev _ (hKinv k hk) C
  · intro B
    exact hkey (T.expt (pY B) * g)

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnPStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  first | exact @GlobalTheory.PolarU.exists_action_on_p | exact GlobalTheory.PolarU.exists_action_on_p | (intros; apply GlobalTheory.PolarU.exists_action_on_p <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem exists_lift_blocks (p q : ℕ) (T : GrpData p q) :
    ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  intro U hU V hV
  have hU1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hU2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hV2 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [star_eq_conjTranspose] at hU1 hU2 hV1 hV2
  let g : GL (Ix p q) ℂ :=
    ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
      by simp [Matrix.fromBlocks_multiply, hU1, hV1],
      by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V
      = Formalism.UG.Jpq p q
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det
    (show 0 < 2 by norm_num)
  have hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by
    unfold matG; rw [hk]
  refine ⟨k, ?_, hm⟩
  show IsKC (matG T k)
  rw [hm]
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonalStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal : ∀ (p q : ℕ) (T : GrpData p q), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  first | exact @GlobalTheory.PolarU.exists_lift_blocks | exact GlobalTheory.PolarU.exists_lift_blocks | (intros; apply GlobalTheory.PolarU.exists_lift_blocks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversalStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal : ∀ (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G), Measurable e → mK Kᶜ = 0 → (∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) → lam ≠ 0 → (∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤) → (∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧ ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) → ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f → ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  first | exact @GlobalTheory.Twist.lintegral_haar_eq_transversal | exact GlobalTheory.Twist.lintegral_haar_eq_transversal | (intros; apply GlobalTheory.Twist.lintegral_haar_eq_transversal <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCover
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

theorem polJ_aOf_eq_prod (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (GlobalTheory.T.sinhcAd_mulVec_of_adSq_eigen p q _ _ _ (GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (GlobalTheory.T.det_adSqEigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem shc_pos (x : ℝ) : 0 < shc x := by
  unfold shc
  split_ifs with hx
  · exact one_pos
  · rcases lt_or_gt_of_ne hx with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

theorem polJ_conj {p q : ℕ} (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) (Y : Mat p q) :
    polJ (matG T k * Y * matG T k⁻¹) = polJ Y :=
  GlobalTheory.T.polarJacobian_blockDiag_conj_invariant p q _ _ Y (by rw [← matG_mul, mul_inv_cancel, matG_one]) hk ((Ksub T).inv_mem hk)

theorem exists_conj_aOf {p q : ℕ} (T : GrpData p q) {Y : Mat p q} (hY : Y ∈ pR p q) :
    ∃ k ∈ T.Kset, ∃ h : ℕ → ℝ, Y = matG T k * aOf p q h * matG T k⁻¹ := by
  obtain ⟨B, rfl⟩ := exists_pY hY
  obtain ⟨U, hU, V, hV, h, hB⟩ := GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose p q (Matrix.of B)
  obtain ⟨k, hk, hkm⟩ := GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal p q T U hU V hV
  refine ⟨k, hk, h, ?_⟩
  rw [matG_inv_of_mem T hk, hkm, pY, hB]
  simp [aOf, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

theorem polJ_pos {p q : ℕ} (T : GrpData p q) (B : Fin p → Fin q → ℂ) : 0 < polJ (pY B) := by
  obtain ⟨k, hk, h, hB⟩ := exists_conj_aOf T (pY_mem B)
  rw [hB, polJ_conj T hk, polJ_aOf_eq_prod]
  exact Finset.prod_pos fun _ _ => shc_pos _

theorem cartan {p q : ℕ} (T : GrpData p q) (g : T.G) : ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  by_cases h : 1 ≤ p + q
  · exact (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q h T).2 g
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    refine ⟨g * (T.expt (pY 0))⁻¹, ?_, pY 0, pY_mem 0, by simp⟩
    intro a
    rcases a with a | a <;> exact a.elim0

theorem isAddHaar_volume (p q : ℕ) : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem haar_polar {p q : ℕ} (T : GrpData p q) :
    ∃ (c : ℝ) (mK : Measure T.G), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (T.Kset)ᶜ = 0 ∧
    (∀ k ∈ T.Kset, Measure.map (fun x => k * x) mK = mK) ∧
    ∀ f : T.G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂T.haar = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ,
          (∫⁻ k, f (k * T.expt (pY B)) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  obtain ⟨-, hinv, hlc, hsc, ht2⟩ := GlobalTheory.T.unitaryPQCover_unimodular p q T
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ := GlobalTheory.T.exists_biinvariant_probability_on_compact_subgroup' T.G (Ksub T) (GlobalTheory.T.isCompact_detSqrtCover_maxCompact p q T)
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.T.exists_continuousOn_polar_log' p q
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (GlobalTheory.T.continuous_polarCoordinatesJacobian p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ p q _ (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q B)
  have hem : Measurable fun B : Fin p → Fin q → ℂ => T.expt (pY B) := (continuous_expt_pY T).measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal T.G (Fin p → Fin q → ℂ) T.haar mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) T.Kset (fun B => T.expt (pY B)) hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI := isAddHaar_volume p q
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ)) Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using polJ_pos T B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (matG T '' C)) :=
        (hC.image (continuous_matG T)).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact Units.isUnit _))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [matG_mul, matG_expt]
      exact hL _ B (matG_star_mul T hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p p q T L hLc hL (cartan T) g
      refine ⟨ψ, hψc.measurable, GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := GlobalTheory.T.jacobian_action_upperRightBlock_exp_coords p q (matG T g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := exists_blocks T hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg (matG T) h
          rwa [matG_mul, matG_mul, matG_expt, matG_expt, hm] at this)
        (fun B => by rw [hdet]; exact polJ_pos T B) (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q)
        (fun B => GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP p q B (GlobalTheory.T.hasDerivAt_exp_two_add_smul_sinhcAdjoint p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × T.G => f (z.2 * T.expt (pY z.1)))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

theorem polar_coordinates : ∀ X : ProvA, CoverHaarIntegration X := by
  intro X p q
  refine ⟨haar_polar (X.grp p q), fun k hk Y _ => ?_, fun Y hY => ?_, fun h => ?_⟩
  · rw [← matG_inv]; exact polJ_conj _ hk Y
  · obtain ⟨k, hk, h, hY⟩ := exists_conj_aOf (X.grp p q) hY
    exact ⟨k, hk, h, by rw [← matG_inv]; exact hY⟩
  · rw [polJ_aOf_eq_prod, GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP]

end GlobalTheory.PolarU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCoverStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover : ∀ X : ProvA, CoverHaarIntegration X := by
  first | exact @GlobalTheory.PolarU.polar_coordinates | exact GlobalTheory.PolarU.polar_coordinates | (intros; apply GlobalTheory.PolarU.polar_coordinates <;> assumption)
end
