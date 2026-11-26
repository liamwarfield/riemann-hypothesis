module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrixStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.GelfandKazhdanHerm

open scoped InnerProductSpace

theorem exists_invariant_hermitian : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  intro hB E _ _ _ a π hπ
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hc : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
    ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level
  have hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hB.of_invariant (π.cusp φ hφ) (hπ φ hφ)
    exact (memL2_iff_isSqInt (hc φ hφ) (π.cusp φ hφ).1.left (hπ φ hφ)).2
      (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC)
  let T := toL2ₗ μ π.V hm
  have hinj : Function.Injective T := toL2ₗ_injective hm hc
  have hR : ∀ (g : GA E a) (x y : L2 (latticeGL E a) μ),
      ⟪R (latticeGL E a) μ g x, R (latticeGL E a) μ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y => by
    let U : L2 (latticeGL E a) μ →ₗᵢ[ℂ] L2 (latticeGL E a) μ :=
      ⟨(R (latticeGL E a) μ g).toLinearMap, fun v => norm_R _ v⟩
    exact U.inner_map_map x y
  refine ⟨((innerₛₗ ℂ).comp T).compl₂ T, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ
    exact inner_conj_symm (T ψ) (T φ)
  · intro φ h0
    have hT : T φ ≠ 0 := fun e => h0 (hinj (e.trans (map_zero T).symm))
    change 0 < (⟪T φ, T φ⟫_ℂ).re
    first
      | exact (re_inner_self_pos (𝕜 := ℂ)).2 hT
      | exact inner_self_pos.2 hT
      | exact (RCLike.inner_self_pos).2 hT
      | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using hT)
  · intro k φ ψ
    change ⟪T (π.op (.fin k) φ), T (π.op (.fin k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (finGL E a k) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.fin k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.fin k) _ ψ.2)).symm
  · intro k φ ψ
    change ⟪T (π.op (.cpt k) φ), T (π.op (.cpt k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (infGL E a (Unitary.toUnits k)) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.cpt k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.cpt k) _ ψ.2)).symm
  · intro X φ ψ
    change ⟪T (π.op (.lie X) φ), T ψ⟫_ℂ + ⟪T φ, T (π.op (.lie X) ψ)⟫_ℂ = 0
    have := GlobalTheory.T.lie_skew_adjoint_matrix E a μ π.V hm π.stable (fun θ hθ => (π.cusp θ hθ).1) X φ ψ
    rw [eq_neg_iff_add_eq_zero] at this
    exact this

end GlobalTheory.GelfandKazhdanHerm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRepStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  first | exact @GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | exact GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | (intros; apply GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrame
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Dbl

theorem dblM_gram {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : Cᵀ * N * C.map star = Jm R S) :
    (dblM C)ᵀ * Matrix.fromBlocks N 0 0 (-N) * (dblM C).map star = Jm (R + S) (S + R) := by
  have hG : ∀ a a', ∑ x, (∑ y, C y a * N y x) * (starRingEnd ℂ) (C x a') = Jm R S a a' := by
    intro a a'
    have := congrFun (congrFun h a) a'
    simpa [Matrix.mul_apply] using this
  ext j k
  rcases j with p | p <;> rcases k with q | q <;>
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective p
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective q
    rcases x with r | s <;> rcases y with r' | s' <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, hG, Jm, Formalism.UG.Jpq, Matrix.one_apply,
        Finset.sum_neg_distrib, Matrix.neg_apply, Fin.ext_iff, Function.swap] <;> omega

theorem dblM_rinv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (h : ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1) :
    ∃ D : Matrix (Ix (R + S) (S + R)) (β ⊕ β) ℂ, dblM C * D = 1 := by
  obtain ⟨C', hC'⟩ := h
  refine ⟨(dblM C'ᵀ)ᵀ, ?_⟩
  have hI : ∀ i i', ∑ r, C i (Sum.inl r) * C' (Sum.inl r) i' + ∑ s, C i (Sum.inr s) * C' (Sum.inr s) i' =
      (1 : Matrix β β ℂ) i i' := by
    intro i i'
    rw [← hC', Matrix.mul_apply, Fintype.sum_sum_type]
  ext i i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_add, dblM, dblCol, Matrix.one_apply, hI, add_comm, Function.swap]

theorem dblM_isFrame {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : IsFrame N C) : IsFrame (Matrix.fromBlocks N 0 0 (-N)) (dblM C) :=
  ⟨dblM_gram N C h.1, dblM_rinv C h.2⟩

theorem framed_dbl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  rintro ⟨hab, hA, hC⟩
  refine ⟨hab, hA, fun w => ?_⟩
  have key : b • (dbl JB).map (piInf (τ w)) =
      Matrix.fromBlocks (b • JB.map (piInf (τ w))) 0 0 (-(b • JB.map (piInf (τ w)))) := by
    simp [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_neg]
  rw [key]
  exact dblM_isFrame _ _ (hC w)

end GlobalTheory.RealLift.Dbl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrameStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_hermitian_space_frame_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ),
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  first | exact @GlobalTheory.RealLift.Dbl.framed_dbl | exact GlobalTheory.RealLift.Dbl.framed_dbl | (intros; apply GlobalTheory.RealLift.Dbl.framed_dbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOfMulEqSmul
noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SelfDualFil

theorem isRegular_of_mul_eq_smul {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) : IsRegular M ∧ IsRegular N := by
  have hd : M.det * N.det ≠ 0 := by
    rw [← Matrix.det_mul, H, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (left_ne_zero_of_mul hd)).1,
    Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (right_ne_zero_of_mul hd)).1⟩

theorem mul_eq_smul_comm {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) :
    N * M = c • (1 : Matrix (Fin h) (Fin h) A) := by
  apply (isRegular_of_mul_eq_smul hc H).1.1
  show M * (N * M) = M * (c • 1)
  rw [← Matrix.mul_assoc, H]
  simp

section

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ]
  [Algebra ℤ_[p] Γ]

theorem G_eq [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply (isRegular_of_mul_eq_smul hμ D.G_mul_F).2.2
  show D.G * D.F = D.G.map (phiInv p O) * D.Ψ' * D.F
  have e1 : D.G.map (phiInv p O) * D.F.map (phiInv p O) = nu ε • 1 := by
    rw [← Matrix.map_mul, D.G_mul_F]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, phiInv_mu]
  have e2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, mul_eq_smul_comm hξ D.Ψ_mul]
    simp
  rw [Matrix.mul_assoc, e2, Matrix.mul_smul, e1, smul_smul, xi_mul_nu, D.G_mul_F]

def dualDatum [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    Datum ε h ℤ_[p] where
  F := D.Gᵀ
  G := D.Fᵀ
  Ψ := D.Ψ'ᵀ
  Ψ' := D.Ψᵀ
  ρT := (etale ε h).ρT
  ρM := (etale ε h).ρM
  G_mul_F := by rw [← Matrix.transpose_mul, D.G_mul_F]; simp
  F_eq := by
    rw [Matrix.transpose_map, ← Matrix.transpose_mul, ← G_eq hμ hξ D]
  Ψ_mul := by rw [← Matrix.transpose_mul, D.Ψ_mul]; simp
  F_act := by
    intro a
    have e : ((etale ε h).ρT a).map (ofPadic p O) = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, hij]
    have e' : (etale ε h).ρM a = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Matrix.algebraMap_matrix_apply, hij]
    rw [e, e']
    simp

variable (C : Type) [Field C] [Algebra O C]

end

end GlobalTheory.SelfDualFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZero
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.GhostKer

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_frobenius (b : Ainf p O) : phiInv p O (WittVector.frobenius b) = b := by
  rw [WittVector.frobenius_eq_map_frobenius]
  unfold phiInv
  ext n
  simp only [WittVector.map_coeff]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

theorem frobenius_iterate_teichmuller (k : ℕ) (x : PreTilt O p) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[k] (WittVector.teichmuller p x) =
      WittVector.teichmuller p (x ^ p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]


variable (p O) in
def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by rw [ghost, iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghost_succ_xi {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (k : ℕ) :
    ghost p O (k + 1) (xi ε) = p := by
  have h : ghost p O (k + 1) (WittVector.teichmuller p (root ε)) = 1 := by
    rw [ghost, frobenius_iterate_teichmuller, WittVector.fontaineTheta_teichmuller, pow_succ',
      pow_mul, root, frobeniusEquiv_symm_pow_p, map_pow]
    have h0 := hε.zeta_zero
    simp only [zeta, Function.iterate_zero, id] at h0
    rw [h0, one_pow]
  change ghostHom p O (k + 1) (xi ε) = p
  unfold xi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_pow]
  change ∑ i ∈ Finset.range p, (ghost p O (k + 1) (WittVector.teichmuller p (root ε))) ^ i = p
  simp [h]

theorem nu_eq_mu_root (x : PreTilt O p) : nu x = mu (root x) := rfl

end SlopeTestRemainingChoices

theorem mu_dvd_of_ghost : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
  have key : ∀ n, ∀ a : Ainf p O, (∀ m, ghost p O m a = 0) → mu ε ∣ mu (root^[n] ε) * a := by
    intro n
    induction n with
    | zero => intro a _; exact dvd_mul_right _ _
    | succ n ih =>
      intro a ha
      have ha0 : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
        rw [RingHom.mem_ker]; exact ha 0
      rw [GlobalTheory.AinfXi.ker_theta hv ε h1, Ideal.mem_span_singleton] at ha0
      obtain ⟨b, rfl⟩ := ha0
      have hb : ∀ m, ghost p O m (WittVector.frobenius b) = 0 := by
        intro m
        rw [ghost_frobenius]
        have h3 := ha (m + 1)
        rw [ghost_mul, ghost_succ_xi hε] at h3
        exact (mul_eq_zero.1 h3).resolve_left hp0
      obtain ⟨c, hc⟩ := ih _ hb
      have hc' := congrArg (phiInv p O) hc
      have e : root (root^[n] ε) = root^[n + 1] ε := (Function.iterate_succ_apply' root n ε).symm
      rw [map_mul, map_mul, phiInv_frobenius, phiInv_mu, phiInv_mu, nu_eq_mu_root, e] at hc'
      refine ⟨phiInv p O c, ?_⟩
      linear_combination xi ε * hc' + phiInv p O c * xi_mul_nu ε
  exact GlobalTheory.MuDivides.mu_dvd_of_forall_dvd p C v O hv ε h1 a (fun n => key n a ha)

end GlobalTheory.GhostKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZeroStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  first | exact @GlobalTheory.GhostKer.mu_dvd_of_ghost | exact GlobalTheory.GhostKer.mu_dvd_of_ghost | (intros; apply GlobalTheory.GhostKer.mu_dvd_of_ghost <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelle
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TameTieOfGood

variable {D : D7}

theorem exists_div (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) : ∃ w, P.Div k w := by
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) (P.pb k).asIdeal (by
    have : RingHom.ker (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective _ _)
    rw [this]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, ?_⟩
  · rintro rfl
    apply (P.pb k).ne_bot
    rw [← hQ']
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  · exact HeightOneSpectrum.ext hQ'

theorem tameTie_of_given {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hG : Given R F) : GlobalTheory.DimPartsCompare.TameTie D R.C.W.om := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hL := hG.core.lev
  obtain ⟨L, h1, h2, h3⟩ := hG.types k
  refine ⟨L, h1, h2, fun v j => ?_⟩
  obtain ⟨PP, hPP⟩ := exists_div R.C.P k
  obtain ⟨u0, hu0, -⟩ := GlobalTheory.GLp.Model.exists_gen L
  have hp := D.host.g_prime k
  set a : ℕ := (u0 : ZMod (D.host.g k)).val with ha_def
  have haz : ((a : ℕ) : ZMod (D.host.g k)) = u0 := ZMod.natCast_zmod_val _
  have ha : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 := by
    rw [← hu0, ← haz, map_natCast]
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha, ← hu0]; simp
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro h; rw [h] at ha0; exact ha0 (by simp)
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have hgPP := Formalism.IndefR.Fin.g_mem_of_div R.C hPP
  have hk0 : IsUnit ((a : ℕ) : kP PP) := by
    have hc : IsCoprime ((a : ℕ) : kP PP) ((D.host.g k : ℕ) : kP PP) := by
      have := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (kP PP))
      simpa using this
    have hg0 : ((D.host.g k : ℕ) : kP PP) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hgPP
    rw [hg0] at hc
    exact isCoprime_zero_right.1 hc
  set u : (kP PP)ˣ := hk0.unit with hu_def
  have key := h3 v j PP hPP a u ha hk0.unit_spec
  have h2' := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3' := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu_def, hk0.unit_spec, map_natCast])
  rw [h2', MonoidHom.inv_apply, _root_.inv_inj] at h3'
  have hw : ZMod.unitOfCoprime a hcop = u0 := Units.ext (by rw [ZMod.coe_unitOfCoprime, haz])
  have hχ : (R.chi ((j : ℕ) + 1) PP u : ℂˣ) = GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.chiTame R.C.W.om k j u0 := by
    rw [h3', ← hw]; rfl
  have hgen : ∀ w : (ZMod (D.host.g k))ˣ, algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) w = L.gen 1 → w = u0 :=
    fun w hw' => Units.ext ((algebraMap _ _).injective (hw'.trans hu0.symm))
  rcases key with e | e
  · refine ⟨_, Or.inl rfl, fun b => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab L ⟨(D.nd.chiT k v j).ne_zero, fun w hw' => ?_⟩ b⟩
    rw [hgen w hw', e, hχ]
  · refine ⟨_, Or.inr rfl, fun b => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab L ⟨(D.nd.chiT k v j).ne_zero, fun w hw' => ?_⟩ b⟩
    rw [hgen w hw', e, hχ, MonoidHom.inv_apply]

theorem exists_tameTie_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∃ om, GlobalTheory.DimPartsCompare.TameTie D om :=
  fun R F hG => ⟨_, tameTie_of_given R F hG⟩

end GlobalTheory.TameTieOfGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelleStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∃ om, GlobalTheory.DimPartsCompare.TameTie D om := by
  first | exact @GlobalTheory.TameTieOfGood.exists_tameTie_of_given | exact GlobalTheory.TameTieOfGood.exists_tameTie_of_given | (intros; apply GlobalTheory.TameTieOfGood.exists_tameTie_of_given <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdeal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RegSeqKer

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (s : L.Sec)

theorem map_cutHom {l m : ℤ} (h : l + 1 = m) (h' : -1 + m = l) :
    Twist.map (lbZPow L m) (GlobalTheory.cutHom F hL s) =
      (twistZAddIso F hL h').hom ≫ mulSecOfEq F (zofSec s) h :=
  zhom_ext fun V u i => by
    change _ = zcoord ((mulSecOfEq F (zofSec s) h).app V ((twistZAddIso F hL h').hom.app V u)) i
    rw [zcoord_map_app, cutHom_app F hL s i inf_le_right, zcoord_mulSecOfEq_app, zcoord_twistZAddIso_hom_app,
      zchartEquiv_apply, zfun_zofSec]

theorem mul_comp_π {l m : ℤ} (h : l + 1 = m) :
    mulSecOfEq F (zofSec s) h ≫ Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s) = 0 := by
  have h' : -1 + m = l := by omega
  rw [← cancel_epi (twistZAddIso F hL h').hom, ← Category.assoc, ← map_cutHom hL F s h h', Limits.comp_zero]
  exact ((cutComplex F hL s).map (twistFunctor (lbZPow L m))).zero

def twistComplex {l m : ℤ} (h : l + 1 = m) : ShortComplex Y.Modules :=
  .mk (mulSecOfEq F (zofSec s) h) (Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s)) (mul_comp_π hL F s h)

theorem shortExact_twistComplex [Mono (GlobalTheory.cutHom F hL s)] {l m : ℤ} (h : l + 1 = m) :
    (twistComplex hL F s h).ShortExact := by
  have h' : -1 + m = l := by omega
  have hS : (cutComplex F hL s).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (cutHom F hL s))
      (inferInstanceAs (Mono (cutHom F hL s))) (epi_cutπ F hL s)
  refine ShortComplex.shortExact_of_iso ?_
    (Twist.shortExact_map (isLB_lbZPow hL m) hS)
  refine ShortComplex.isoMk (twistZAddIso F hL h') (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (map_cutHom hL F s h h').symm.trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem vanishFrom_cut [Mono (GlobalTheory.cutHom F hL s)] {j₀ : ℤ} (hv : VanishFrom L F j₀) :
    VanishFrom L (GlobalTheory.cut F hL s) (j₀ + 1) := fun j hj q hq =>
  cohOn.subsingleton₃ (shortExact_twistComplex hL F s (l := j - 1) (m := j) (by omega)) ⊤ q
    (hv j (by omega) q hq) (hv (j - 1) (by omega) (q + 1) (by omega))

theorem exists_global (n : ℕ) : ∀ (t : Fin n → L.Sec) (F : Y.Modules) (j₀ l : ℤ), RegSeq hL F (List.ofFn t) →
    VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤),
    (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)),
      (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f =
        ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app W (m i)) →
    ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app ⊤ (m i) := by
  induction n with
  | zero =>
    intro t F j₀ l _ _ _ f hf
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    obtain ⟨W, hW, m, hm⟩ := hf x
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hW, hm, map_zero]
  | succ n ih =>
    intro t F j₀ l hr hv hj f hf
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have nat : ∀ (a : L.Sec) (W : Y.Opens) (u : Γ(GlobalTheory.twistZ F L l, W)),
        (Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W ((mulSecOfEq F (zofSec a) rfl).app W u) =
          (mulSecOfEq (cut F hL (t 0)) (zofSec a) rfl).app W
            ((Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W u) := fun a W u => by
      apply zsec_ext fun i => ?_
      rw [zcoord_map_app, zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, zcoord_map_app,
        Scheme.Modules.Hom.app_smul]
    have hS := shortExact_twistComplex hL F (t 0) (l := l) rfl
    have := hS.mono_f
    have hex : ∀ W : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) (rfl : l + 1 = l + 1)).app W)
        ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W) := exact_app_of_exact_of_mono hS.exact
    obtain ⟨m', hm'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l hr (vanishFrom_cut hL F (t 0) hv)
      (by push_cast at hj; omega) ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app ⊤ f) fun y => by
        obtain ⟨W, hW, m, hm⟩ := hf y
        refine ⟨W, hW, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W (m i.succ), ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← app_res, hm, Fin.sum_univ_succ, map_add (f := _), (hex W).apply_apply_eq_zero, zero_add, map_sum]
        exact Finset.sum_congr rfl fun i _ => nat _ _ _
    have hlift : ∀ i, ∃ u : Γ(GlobalTheory.twistZ F L l, ⊤),
        (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app ⊤ u = m' i := fun i => by
      have hi := i.pos
      exact cohOn.app_surjective (shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)) ⊤
        (hv (l - 1) (by push_cast at hj; omega) 1 one_pos) (m' i)
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex ⊤ (f - ∑ i, (mulSecOfEq F (zofSec (t i.succ)) rfl).app ⊤ (u i))).1 (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hm', map_sum, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [nat, hu])
    refine ⟨Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqKer

theorem GlobalTheory.HSCore.exists_global_of_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) :=
  fun _ _ _ _ _ _ hL n t F _ j₀ l => RegSeqKer.exists_global hL n t F j₀ l
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdealStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_combination_of_local_regular_ideal : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) := by
  first | exact @GlobalTheory.HSCore.exists_global_of_regSeq | exact GlobalTheory.HSCore.exists_global_of_regSeq | (intros; apply GlobalTheory.HSCore.exists_global_of_regSeq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRegularSequenceOfCommonZeros
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRegularSequenceOfCommonZeros
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.QCoh RingTheory.Sequence

namespace GlobalTheory.RegBasis

section General

variable {X : Scheme.{0}} {L : LB X} {k : Type} [Field k] [Algebra k Γ(X, ⊤)] {V : Type} [AddCommGroup V]
  [Module k V] (φ : V →ₛₗ[algebraMap k Γ(X, ⊤)] L.Sec)

def vanishAt (x : X) : Submodule k V where
  carrier := {w | x ∉ nonzeroLocus (φ w)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add (f := _)] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [φ.map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem vanishAt_eq_top {ι : Type} {v : ι → V} (hv : Submodule.span k (Set.range v) = ⊤) {x : X}
    (hx : ∀ i, x ∉ nonzeroLocus (φ (v i))) : vanishAt φ x = ⊤ :=
  top_le_iff.1 (hv.ge.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx i)))

theorem exists_regSeq [Infinite k] [Module.Finite k V] [AlgebraicGeometry.IsNoetherian X] (hL : L.IsLB)
    (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x)) (m : ℕ) (F : X.Modules) [IsFiniteQC F] (W : Submodule k V)
    (hW : Module.finrank k W + m = Module.finrank k V)
    (h : ∀ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ → ∀ x, vanishAt φ x = ⊤ →
      IsWeaklyRegular (F.presheaf.stalk x :) (List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x)))) :
    ∃ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ ∧ RegSeq hL F (List.ofFn fun i => φ (v i)) := by
  induction m generalizing F W with
  | zero =>
    refine ⟨Fin.elim0, ?_, by rw [List.ofFn_zero]; trivial⟩
    rw [Submodule.eq_top_of_finrank_eq hW, top_sup_eq]
  | succ m ih =>
    have hne : W ≠ ⊤ := fun e => by
      rw [e, finrank_top] at hW
      omega
    have : Finite {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} :=
      ((finite_assPoints F).subset (t := {x : X | x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤})
        (fun _ hx => hx.1)).to_subtype
    obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
      (fun o : Option {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} => o.elim W fun x => vanishAt φ x.1)
      (by
        rintro (_ | x)
        exacts [hne, x.2.2])
    have hsup : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) =
        W ⊔ Submodule.span k (Set.range (Fin.cons w v : Fin (m + 1) → V)) := fun v => by
      rw [Fin.range_cons, Submodule.span_insert, sup_assoc]
    have key : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) = ⊤ →
        ∀ x, vanishAt φ x = ⊤ → IsWeaklyRegular (F.presheaf.stalk x :)
          (X.presheaf.germ _ x (hc x) ((φ w).f (c x)) ::
            List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x))) := fun v hv x hx => by
      have := h (Fin.cons w v) ((hsup v).symm.trans hv) x hx
      rwa [List.ofFn_succ] at this
    obtain ⟨v, hv, hr⟩ := ih (cut F hL (φ w)) (W ⊔ Submodule.span k {w})
      (by rw [Submodule.finrank_sup_span_singleton (p := W) (hw none)]; omega) fun v hv x hx => by
        obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv F hL (φ w) (c x) (hc x)
        exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x hx)).2
    refine ⟨Fin.cons w v, (hsup v).symm.trans hv, ?_⟩
    rw [List.ofFn_succ]
    refine (regSeq_cons hL F _ _).2 ⟨(mono_cutHom_iff F hL _).2 fun x hx => ?_, hr⟩
    by_cases e : vanishAt φ x = ⊤
    · have hreg := ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x e)).1
      obtain ⟨t, ht⟩ := mem_assPoints_iff_exists.1 hx
      refine (Cartier.mem_nonzeroLocus_iff (φ w) (c x) (hc x)).2 ((X.mem_basicOpen _ x (hc x)).2 ?_)
      by_contra hu
      have h0 : t = 0 := hreg (((ht _).2 hu).trans (smul_zero _).symm)
      exact (ht 1).1 (by rw [h0, smul_zero]) isUnit_one
    · exact not_not.1 (hw (some ⟨x, hx, e⟩))

theorem nonempty_stalk_toMod {B : LB X} (hB : B.IsLB) (x : X) :
    Nonempty (((LB.toMod B).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨e⟩ := Twist.nonempty_stalkEquiv (F := structureModule X) hB x
  let i : twist (structureModule X) B ≅ LB.toMod B := Twist.unitTwistIso B
  exact ⟨(LinearEquiv.ofBijective (stalkLinear i.hom x)
    ⟨stalkLinear_injective _ x, stalkLinear_surjective _ x⟩).symm ≪≫ₗ e ≪≫ₗ structureModuleStalkEquiv x⟩

end General

def combMap {k : Type} [Field k] (S : LinSys k) {D : ℕ} (s : Fin D → Fin S.N → k) :
    (Fin D → k) →ₛₗ[algebraMap k Γ(S.Y, ⊤)] S.L.Sec where
  toFun c := S.comb (∑ j, c j • s j)
  map_add' a b := by
    simp only [LinSys.comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' a b := by
    simp only [LinSys.comb, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_mul]

theorem exists_regular_basis : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K),
    G.IsGood s → ∀ B : LB G.Y, B.IsLB → ∃ g : Matrix (Fin G.D) (Fin G.D) K, IsUnit g.det ∧
      RegSeq G.isLB (GlobalTheory.LB.toMod B) (List.ofFn fun i => G.comb (∑ j, g i j • s j)) := by
  intro K _ _ G s hs B hB
  have hp := G.geom.alg.variety.proj
  have := isNoetherian_of_isProjOver hp
  have : IsFiniteQC (LB.toMod B) := isFiniteQC_iff_isFiniteType.2 ⟨LB.isQuasicoherent_toMod hB, LB.isFiniteType_toMod hB⟩
  have hfin : ((G.ideal s).support : Set G.Y).Finite := by
    have := hs.finite
    have h := ((G.ideal s).subschemeι ≫ G.str).finite_preimage_singleton (IsLocalRing.closedPoint K)
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (h.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum K) _ _).image _
  obtain ⟨v, hv, hr⟩ := exists_regSeq (combMap G.toLinSys s) G.isLB G.chartAt G.mem_chartAt G.D (LB.toMod B) ⊥
    (by simp) fun v hv x hx => by
      rw [bot_sup_eq] at hv
      obtain ⟨q⟩ := nonempty_stalk_toMod hB x
      refine (q.isWeaklyRegular_congr _).2 ((ProperCut.topSelf_eq_length_of_smooth G.str G.smooth hp G.isLB
        (fun i => combMap G.toLinSys s (v i)) (hfin.subset fun y hy => ?_)).2.1 x ?_ _ _).toIsWeaklyRegular
      · have e := vanishAt_eq_top _ hv ((mem_support_cutIdeal _ _ y).1 hy)
        refine (mem_support_cutIdeal _ _ y).2 fun i => ?_
        have h : y ∉ nonzeroLocus (G.comb (∑ j, (Pi.single i 1 : Fin G.D → K) j • s j)) :=
          e.ge (Submodule.mem_top (x := Pi.single i 1))
        simpa [Pi.single_apply] using h
      · exact (mem_support_cutIdeal _ _ x).2 fun i => hx.ge (Submodule.mem_top (x := v i))
  rw [bot_sup_eq] at hv
  refine ⟨Matrix.of v, (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
    (linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp))), hr⟩

end GlobalTheory.RegBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRegularSequenceOfCommonZerosStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ B : LB G.Y, B.IsLB → ∃ g : Matrix (Fin G.D) (Fin G.D) K, IsUnit g.det ∧ RegSeq G.isLB (GlobalTheory.LB.toMod B) (List.ofFn fun i => G.comb (∑ j, g i j • s j)) := by
  first | exact @GlobalTheory.RegBasis.exists_regular_basis | exact GlobalTheory.RegBasis.exists_regular_basis | (intros; apply GlobalTheory.RegBasis.exists_regular_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
noncomputable section

namespace GlobalTheory.TypeBase

def piCongrLeftMul {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) : (∀ a, P (e a)) ≃* ∀ b, P b :=
  { Equiv.piCongrLeft P e with
    map_mul' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.mul_apply, Equiv.piCongrLeft_apply_apply] }

theorem piCongrLeftMul_apply {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) (f : ∀ a, P (e a)) (a : α) :
    piCongrLeftMul P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

def bcEquiv {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A ≃+* B) :
    GL n A ≃* GL n B :=
  MonoidHom.toMulEquiv (Formalism.UG.bc (f : A →+* B)) (Formalism.UG.bc (f.symm : B →+* A))
    (by ext g i j; simp [Formalism.UG.bc]) (by ext g i j; simp [Formalism.UG.bc])

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A →+* B)
    (g : GL n A) (i j : n) : ((Formalism.UG.bc f g : GL n B) : Matrix n n B) i j = f ((g : Matrix n n A) i j) := rfl

theorem bc_mem_unip_iff {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A ≃+* B) (g : GL (Fin r) A) :
    Formalism.UG.bc (f : A →+* B) g ∈ unip B r ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.unitri r A := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := h1 (show j.val < i.val from hij)
      rw [bc_apply] at h
      exact f.injective (h.trans (map_zero f).symm)
    · have h := h2 i
      rw [bc_apply] at h
      exact f.injective (h.trans (map_one f).symm)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [bc_apply, h1 (show id j < id i from hij), map_zero]
    · rw [bc_apply, h2 i, map_one]

theorem edgeSum_bc {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A →+* B) (g : GL (Fin r) A) :
    edgeSum supEdge (Formalism.UG.bc f g) = f (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag (g : Matrix (Fin r) (Fin r) A)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [edgeSum, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag, supEdge, bc_apply, map_sum, apply_ite f, map_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr

theorem det_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

theorem exists_char {Ks : Type} [Field Ks] (σ : Ks →+* ℂ) (p : ℕ) [Fact p.Prime] {ζ : Ks} (hζ : IsPrimitiveRoot ζ p)
    {k : Type} [CommRing k] (f : ZMod p ≃+* k) (χ : AddChar k ℂ) :
    ∃ ψ : AddChar (ZMod p) Ks, ∀ x, σ (ψ x) = χ (f x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz : χ (f 1) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero,
      AddChar.map_zero_eq_one]
  obtain ⟨k, -, hk⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz
  have hc : (ζ ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨AddChar.zmodChar p hc, fun x => ?_⟩
  rw [AddChar.zmodChar_apply, map_pow, map_pow, hk, ← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_zmod_val]

theorem baseLevelCharacter_eq_prod_superdiagonalSum {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) (g) (hg : g ∈ (P0 Pg r ψ).H) :
    (((P0 Pg r ψ).chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : Pg, ψ PP.1 (edgeSum supEdge (g PP)) := by
  unfold P0 LevelP.ofLocal
  dsimp only
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, Units.coe_prod]
  rfl

theorem mem_lastZeroOrthImageSubspace_iff {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (g : G0 Pg r) :
    g ∈ (P0 Pg r ψ).H ↔ ∀ PP, g PP ∈ unip (kP PP.1) r := by
  simp [P0, LevelP.ofLocal, Subgroup.mem_pi]

end GlobalTheory.TypeBase

namespace GlobalTheory.TypeBase

theorem base_level_unip_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.grp_chiW → (∀ k, ∃ ζ : Ks, IsPrimitiveRoot ζ (D.host.g k)) → ∀ (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), ∃ (t : LevelGroup D.host ≃* G) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Ks), (∀ u v, R.eG (t u) (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) ∧ (∀ v, ψ v ≠ 1) ∧ (∀ u, t u ∈ (F.lvl false).P ↔ u ∈ levelU D.host) ∧ ∀ u (h : t u ∈ (F.lvl false).P), algebraMap Ks D.what₂.LL (psiU ψ u) = ((F.lvl false).ψ ⟨t u, h⟩ : D.what₂.LLˣ) ∧ ∀ i, (R.FW i).chi (t u) = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hlevels hchiW hζ e iso
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let φ : LevelGroup D.host ≃* G0 R.Pg D.R.r :=
    (MulEquiv.piCongrRight fun v : Sq D.host => (bcEquiv (n := Fin D.R.r) (iso v))).trans
      (piCongrLeftMul (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e)
  have hφ : ∀ u v, φ u (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v) := fun u v =>
    piCongrLeftMul_apply (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e
      (fun v => Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) v
  have hex : ∀ v : Sq D.host, ∃ ψ : AddChar (ZMod (D.host.g v.1)) Ks,
      ∀ x, D.what₂.embLL (algebraMap Ks D.what₂.LL (ψ x)) = ψ0 (e v).1 (iso v x) := by
    intro v
    obtain ⟨ζ, hz⟩ := hζ v.1
    exact exists_char (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)) _ hz (iso v) (ψ0 (e v).1)
  choose ψ hψ using hex
  refine ⟨φ.trans R.eG.symm, ψ, fun u v => ?_, fun v h1 => ?_, fun u => ?_, fun u h => ?_⟩
  · show R.eG (R.eG.symm (φ u)) (e v) = _
    rw [MulEquiv.apply_symm_apply, hφ]
  · apply hgen (e v).1 (e v).2
    ext y
    obtain ⟨x, rfl⟩ := (iso v).surjective y
    rw [← hψ v x, h1, AddChar.one_apply, map_one, map_one, AddChar.one_apply]
  · show φ u ∈ (R.levR F false).H ↔ _
    rw [hlev, mem_lastZeroOrthImageSubspace_iff, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.levelU, Subgroup.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact (e.forall_congr fun v => by rw [hφ, bc_mem_unip_iff]).symm
  · have hm : φ u ∈ (P0 R.Pg D.R.r ψ0).H := by rw [← hlev]; exact h
    have hun : ∀ PP, φ u PP ∈ unip (kP PP.1) D.R.r := (mem_lastZeroOrthImageSubspace_iff _ _ _ _).1 hm
    refine ⟨?_, fun i => ?_⟩
    · apply D.what₂.embLL.injective
      have e1 : (R.levR F false).chi ⟨φ u, h⟩ =
          Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩) := rfl
      have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
          ((X.chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (g PP)) := by
        rintro X rfl g hg
        exact baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ g hg
      have h2 := key _ hlev (φ u) h
      rw [e1, Units.coe_map] at h2
      rw [show D.what₂.embLL (((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (φ u PP)) from h2]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.psiU, map_prod]
      refine Finset.prod_equiv e (by simp) fun v _ => ?_
      rw [hψ, hφ, edgeSum_bc, RingEquiv.coe_toRingHom]
    · apply Units.ext
      apply D.what₂.embLL.injective
      have hg : R.eG ((φ.trans R.eG.symm) u) = φ u := R.eG.apply_symm_apply _
      rw [hchiW i, hg, Finset.prod_eq_one (fun PP _ => by rw [det_unip (hun PP), map_one, Units.val_one]),
        Units.val_one, map_one]

end GlobalTheory.TypeBase
end
end
