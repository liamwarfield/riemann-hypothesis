module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinDual

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) → ∀ v : H, IsKFin ε ρ v → v ∈ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
  classical
  intro n ε H _ _ ρ hU hirr
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} :=
        (le_sSup (s := {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) hΛ).trans (le_iSup (fun Λ => sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K)
      exact hle
  intro v ⟨F, hF, hvF, hFK⟩
  exact key _ F hF le_rfl hFK hvF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S | IsKTypeOf ε ρ Λ S}

theorem kIso_le (Λ : Fin n → ℝ) : kIso ε ρ Λ ≤ kFinVec ε ρ :=
  sSup_le fun S hS v hv => ⟨S, hS.1, hv, hS.2.1⟩

theorem kIso_orth (hU : IsURepOn (Kset ε) ρ) {Λ μ : Fin n → ℝ} (hne : μ ≠ Λ) :
    ∀ x ∈ kIso ε ρ Λ, ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq]
  refine Submodule.isOrtho_sSup_left.2 fun S hS => Submodule.isOrtho_sSup_right.2 fun T hT => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (GlobalTheory.Jet.MultGap.orth_of_ne hU hS hT hne)

theorem finset_orth (hU : IsURepOn (Kset ε) ρ) (s : Finset (Fin n → ℝ)) {μ : Fin n → ℝ} (hμ : μ ∉ s) :
    ∀ x ∈ s.sup (kIso ε ρ), ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq, Finset.sup_eq_iSup]
  refine Submodule.isOrtho_iSup_left.2 fun Λ => Submodule.isOrtho_iSup_left.2 fun hΛ => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (kIso_orth hU (fun e => hμ (e ▸ hΛ)))

theorem exists_finset (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) (v : H) (hv : IsKFin ε ρ v) :
    ∃ s : Finset (Fin n → ℝ), v ∈ s.sup (kIso ε ρ) := by
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hd v hv)
  exact ⟨s, by rwa [Finset.sup_eq_iSup]⟩

end

section
variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem map_kIso_le {T : H →ₗ[ℂ] V} (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y))
    (Λ : Fin n → ℝ) : (kIso ε ρ Λ).map T ≤ kIso ε π Λ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sSup_le fun S hS => ?_
  rw [← Submodule.map_le_iff_le_comap]
  haveI := hS.1
  set Q : S →L[ℂ] V := LinearMap.toContinuousLinearMap (T ∘ₗ S.subtype) with hQdef
  have hR : S.map T = LinearMap.range (Q : S →ₗ[ℂ] V) := by
    rw [hQdef, LinearMap.coe_toContinuousLinearMap, LinearMap.range_comp, Submodule.range_subtype]
  by_cases hQ : Q = 0
  · rw [hR, hQ]; simp
  · rw [hR]
    refine le_sSup (GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S V π Q hS (fun k hk x y hxy => ?_) hQ)
    change T y = π k (T x)
    rw [hxy]
    exact hT k hk x ⟨S, hS.1, x.2, hS.2.1⟩

end

end GlobalTheory.KFinDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem recursive_matrixPower_eq_matrix_pow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) :
    Matrix.of (Formalism.REAL.epow E k) = (Matrix.of E) ^ k := by
  induction k with
  | zero =>
    ext a b
    simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    ext a b
    rw [pow_succ, ← ih]
    simp [Formalism.REAL.epow, Matrix.mul_apply]

theorem scalarMatrix_mul_algebraMatrix_mul_apply {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((algebraMap ℂ A).mapMatrix P.transpose * M * (algebraMap ℂ A).mapMatrix Q.transpose) a b
      = ∑ c, ∑ d, (P c a * Q b d) • M c d := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]

theorem etr_conj_scalar_matrix {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL
  set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR
  have hLR : L * R = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]
  have hRL : R * L = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]
  have hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R := by
    ext a b
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]
    rfl
  have hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R := by
    intro m
    induction m with
    | zero => simp [hLR]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc L * Matrix.of E ^ m * R * (L * Matrix.of E * R)
          = L * Matrix.of E ^ m * (R * L) * Matrix.of E * R := by simp only [mul_assoc]
        _ = L * (Matrix.of E ^ m * Matrix.of E) * R := by rw [hRL]; simp only [mul_assoc, one_mul]
  have hk := recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k
  rw [hE, hpow, ← recursive_matrixPower_eq_matrix_pow] at hk
  have hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a
      = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d := by
    intro a
    have := congrFun (congrFun hk a) a
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply] at this
    exact this
  unfold Formalism.REAL.etr
  simp only [hent]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrixStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  first | exact @GlobalTheory.etr_conj_scalar_matrix | exact GlobalTheory.etr_conj_scalar_matrix | (intros; apply GlobalTheory.etr_conj_scalar_matrix <;> assumption)
end
end

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.GKLie

theorem epow_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) : ∀ k a b, R * epow E k a b = epow E' k a b * R := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [Formalism.REAL.epow]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    simp only [Formalism.REAL.epow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem etr_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) (k : ℕ) : R * etr E k = etr E' k * R := by
  simp only [etr, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => epow_intertwine E E' R h k a a

theorem single_mul_single' {n : ℕ} (a b c d : Fin n) :
    (single a b (1 : ℂ)) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem conj_single {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * single a b 1 * P⁻¹ = ∑ c, ∑ d, (P c a * P⁻¹ b d) • single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section Main

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end Main

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section KPart

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kset_facts {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) :
    κᴴ * κ = 1 ∧ κ⁻¹ = κᴴ ∧ κ * Jm ε = Jm ε * κ ∧ κᴴ * Jm ε = Jm ε * κᴴ := by
  obtain ⟨hu, hc⟩ := hκ
  have h1 : κᴴ * κ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hu
    simpa [Matrix.star_eq_conjTranspose] using hu
  refine ⟨h1, Matrix.inv_eq_left_inv h1, hc, ?_⟩
  have := congrArg conjTranspose hc
  simpa [conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem theta_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.thetaJ ε (κ * Y * κ⁻¹) = κ * PI.DSInfCharCap.thetaJ ε Y * κ⁻¹ := by
  obtain ⟨_, hinv, hc, hc'⟩ := kset_facts hκ
  rw [hinv]
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, conjTranspose_conjTranspose, mul_neg, neg_mul, mul_assoc]
  rw [hc', ← mul_assoc (Jm ε) κ, ← hc, mul_assoc]

theorem cre_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cre ε (κ * Y * κ⁻¹) = κ * cre ε Y * κ⁻¹ := by
  unfold cre
  rw [theta_kconj hκ]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

theorem cim_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cim ε (κ * Y * κ⁻¹) = κ * cim ε Y * κ⁻¹ := by
  unfold cim
  rw [theta_kconj hκ]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]

end KPart

end GlobalTheory.GKLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCUnitary

variable {n : ℕ} {ε : Fin n → Bool}

theorem maxCpt_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.maxCpt (UJset ε) = Kset ε := by
  ext g
  refine ⟨fun hg => ⟨hg.2, ?_⟩, fun hg => ⟨mem_UJset_of_mem_Kset hg, hg.1⟩⟩
  have h1 : g * gᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hg.2
  have h2 : gᴴ * Jm ε * g = Jm ε := hg.1
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h2]
    _ = Jm ε * g := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, h1, Matrix.one_mul]

theorem isLinRed_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.IsLinRed (UJset ε) := by
  have hW : IsIsoFlag ε (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => (⊥ : Submodule ℂ (Fin n → ℂ))) :=
    ⟨rfl, monotone_const, fun i => i.elim0, fun x hx y _ => by
      rw [(Submodule.mem_bot ℂ).1 hx]; simp⟩
  have h := (GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε 0 _ _ hW (fun i => i.elim0)).1
  rwa [leviOne_zero hW, mats_top] at h

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isKStable_iff {S : Submodule ℂ H} : GlobalTheory.LinRed.IsKStable (UJset ε) π S ↔ IsKStableOn ε π S := by
  unfold GlobalTheory.LinRed.IsKStable IsKStableOn
  rw [maxCpt_UJset]

theorem isKTypeOf_map {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε π Λ S) (T : H →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ w ∈ S, T (π k w) = π k (T w)) : S.map T = ⊥ ∨ IsKTypeOf ε π Λ (S.map T) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hv⟩, hdom⟩ := hS
  have hpre : ∀ S' : Submodule ℂ H, IsKStableOn ε π S' → IsKStableOn ε π (S ⊓ S'.comap T) :=
    fun S' h k hk w hw => ⟨hst k hk w hw.1, by
      have : T (π k w) ∈ S' := by rw [hT k hk w hw.1]; exact h k hk _ hw.2
      exact this⟩
  have hbot : IsKStableOn ε π ⊥ := fun k _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _
  rcases hirr _ inf_le_left (hpre ⊥ hbot) with h0 | h1
  · right
    have hinj : ∀ w ∈ S, T w = 0 → w = 0 := fun w hw h => by
      have : w ∈ S ⊓ (⊥ : Submodule ℂ H).comap T := ⟨hw, h⟩
      rwa [h0, Submodule.mem_bot] at this
    refine ⟨inferInstance, ?_, fun S' hle hS' => ?_, ⟨T v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h),
      fun θ hθ => ?_⟩, ?_⟩
    · rintro k hk _ ⟨w, hw, rfl⟩
      exact ⟨π k w, hst k hk w hw, hT k hk w hw⟩
    · rcases hirr _ inf_le_left (hpre S' hS') with h | h
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := hle hx
        have : w ∈ S ⊓ S'.comap T := ⟨hw, hx⟩
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]; exact Submodule.zero_mem _
      · exact Or.inr (le_antisymm hle (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h)))
    · rw [← hT _ hθ v hvS, hv θ hθ, map_smul]
    · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
      refine hdom μ w hw (fun h => hw0 (by rw [h, map_zero])) fun θ hθ => ?_
      refine sub_eq_zero.1 (hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw)) ?_)
      rw [map_sub, map_smul, hT _ hθ w hw, hwt θ hθ, sub_self]
  · exact Or.inl (eq_bot_iff.2 (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h1)))

theorem isAdmOn_iff [CompleteSpace H] : GlobalTheory.LinRed.IsAdmOn (UJset ε) π ↔ IsAdmRep ε π := by
  unfold GlobalTheory.LinRed.IsAdmOn IsAdmRep
  simp only [isKStable_iff]
  rw [maxCpt_UJset]
  refine and_congr_right fun h1 => and_congr_right fun h2 => and_congr_right fun h3 => ?_
  obtain ⟨hA, hB⟩ := GlobalTheory.KTypeHighest.ktype_highest_weight n ε H π h1 h2 h3
  refine ⟨fun h Λ => ?_, fun h S hfin hst hirr => ?_⟩
  · by_cases he : ∃ S₀, IsKTypeOf ε π Λ S₀
    · obtain ⟨S₀, hS₀⟩ := he
      haveI := h S₀ hS₀.1 hS₀.2.1 hS₀.2.2.1
      refine Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S' | ∃ T : H →ₗ[ℂ] H, S' = S₀.map T ∧
        ∀ k ∈ Kset ε, ∀ w ∈ S₀, T (π k w) = π k (T w)}) fun S hS => ?_)
      obtain ⟨B, hB1, hB2⟩ := hB Λ S₀ S hS₀ hS.2
      exact ⟨B, hB2.symm, fun k hk w _ => hB1 k hk w⟩
    · exact Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le fun S hS => absurd ⟨S, hS.2⟩ he)
  · by_cases h0 : S = ⊥
    · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le ?_)
      rintro _ ⟨T, rfl, -⟩
      rw [h0, Submodule.map_bot]
    · obtain ⟨Λ, hΛ⟩ := hA S hfin h0 hst hirr
      haveI := h Λ
      refine Submodule.finiteDimensional_of_le (S₂ := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S}) (sSup_le ?_)
      rintro _ ⟨T, rfl, hT⟩
      rcases isKTypeOf_map hΛ T hT with hb | hk
      · rw [hb]; exact bot_le
      · exact le_sSup ⟨le_top, hk⟩

end GlobalTheory.HCUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinCuspApprox

variable {D : D7}

abbrev avgN (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e φ

def KStab (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (s : Set D.what₂.Tau) (W : Submodule ℂ (GA D N.V → ℂ)) : Prop :=
  ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), N.M.fr τ * g * (N.M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (N.M.ε τ) →
    ∀ f ∈ W, rTr N.V (atTau θ N.V τ g) f ∈ W

theorem kStab_empty (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (W : Submodule ℂ (GA D N.V → ℂ)) : KStab θ N ∅ W := fun _ h => h.elim

end GlobalTheory.KFinCuspApprox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem sqrt_intCast_eq_sqrt_toNat (x : ℤ) : Real.sqrt (x : ℝ) = Real.sqrt ((x.toNat : ℕ) : ℝ) := by
  rcases le_or_gt 0 x with h | h
  · rw [show ((x.toNat : ℕ) : ℝ) = (x : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]
  · rw [Real.sqrt_eq_zero'.2 (by exact_mod_cast h.le), Int.toNat_eq_zero.2 h.le]; simp

theorem gap_eq_chiGap : ∀ D : D7, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 := by
  intro D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hv : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v = (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v := fun _ => rfl
  have hk : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v 2 - (GlobalTheory.Grid.gridOf D 0 0 τ).v D.R.k =
      (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k := fun τ => by rw [hv]
  have hN : (GlobalTheory.Grid.bigN D : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := rfl
  have hN' : GlobalTheory.Grid.bigN D = GlobalTheory.ChiGrid.bigN D := rfl
  have hs : GlobalTheory.Grid.sLen D = GlobalTheory.ChiGrid.sLen D := rfl
  have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = (D.R.r : ℝ) + 1 := by simp [GlobalTheory.ChiGrid.nRk]
  set f : D.what₂.Tau → ℤ := fun τ => (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k with hf
  have hc : GlobalTheory.ChiGrid.cloudLen D = Finset.univ.sup fun τ => (f τ).toNat := rfl
  have key : ∀ γ : ℕ, GlobalTheory.Grid.GapCond D γ ↔ GlobalTheory.ChiGrid.GapBound D 1 γ := by
    intro γ
    unfold GlobalTheory.Grid.GapCond GlobalTheory.ChiGrid.GapBound
    simp only [one_mul, hk, hn, hN, hN', hs, hc]
    refine and_congr ?_ Iff.rfl
    have hB : (0 : ℝ) ≤ ((D.R.r : ℝ) + 1) ^ 3 := by positivity
    constructor
    · intro h
      obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun τ => (f τ).toNat
      have := h τ
      rw [sqrt_intCast_eq_sqrt_toNat] at this
      rw [hτ]; exact this
    · intro h τ
      rw [sqrt_intCast_eq_sqrt_toNat]
      refine le_trans ?_ h
      have h1 : (f τ).toNat ≤ Finset.univ.sup fun τ => (f τ).toNat := Finset.le_sup (f := fun τ => (f τ).toNat) (Finset.mem_univ τ)
      have h2 : Real.sqrt (((f τ).toNat : ℕ) : ℝ) ≤ Real.sqrt (((Finset.univ.sup fun τ => (f τ).toNat : ℕ)) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast h1)
      nlinarith
  have e : {γ | GlobalTheory.Grid.GapCond D γ} = {g | GlobalTheory.ChiGrid.GapBound D 1 g} := Set.ext fun γ => key γ
  have h1 := GlobalTheory.Grid.isLeast_gap D
  rw [e] at h1
  exact h1.unique (GlobalTheory.ChiGrid.isLeast_gap D 1)

end GlobalTheory.GridJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridMinimalGap_eq_chiGridGapGamma_one : ∀ D : D7, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 := by
  first | exact @GlobalTheory.GridJoin.gap_eq_chiGap | exact GlobalTheory.GridJoin.gap_eq_chiGap | (intros; apply GlobalTheory.GridJoin.gap_eq_chiGap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem spMap_epsMul_comp (a b : ℂ) {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) :
    spMap (epsMul a) ≫ spMap (epsMul b) ≫ v = spMap (epsMul (b * a)) ≫ v := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply RingHom.ext
  intro x
  ext <;> simp [epsMul] <;> ring

theorem exists_lift_deriv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') {p : ℕ} (hp : p.Prime)
    {y y'' : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy'' : y'' = F.u j P') (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hI : IsHkIsog p y y'' C ψ ψp) :
    ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
  subst hy hy''
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  refine ⟨gam, h, h1, h2, h3, fun w v hvs hd => ?_⟩
  have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
    pullback.lift_fst _ _ _
  have d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
    refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
      (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
    · convert ExpChain.isHolTo_ex F i P hP using 2 with z
      exact hfst z
    · convert hd using 2 with z
      exact hfst z
  have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
  have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left := fun z => by
    rw [← Category.assoc, hI.2.2.1, h4]
    exact pullback.lift_fst _ _ _
  simp only [e1] at d1
  exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1


set_option maxHeartbeats 1000000 in
theorem exists_similitude_tri_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ m < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) m = p * ∑ j ∈ Finset.range (Dw.mult τ), A τ m j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (m : Fin (Dw.mult τ)), A τ m m = Formalism.L2.PjFree.toC (t (some ⟨τ, m⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU P p i k k' x x' C z t hA hK hH hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨Pm, hP, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨Pm', hP', per', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hH
  have hpp : p.Prime := hA.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha
  obtain ⟨gam, h, hiso, hh, honto, hder⟩ := exists_lift_deriv F (ik k) (ik k') Pm Pm' per per' hpp hPx
    (hB.1.trans hPx') C ψ ψp hC hI
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hcol : ∀ τ m, h.toLinearMap (Pi.single (e.symm ⟨τ, m⟩) 1) =
      (∑ j, ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ m
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ m
    have d2 := hder (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' per' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ m)
      (z.u τ m)).1 (hPx' ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
      have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
        apply RingHom.ext
        intro a
        ext <;> simp [epsMul]
      rw [e0]
      first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ m = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' per'
    show h (Pi.single (e.symm ⟨τ, m⟩) 1) = _
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (Formalism.L2.PjFree.toC (cf τ m j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  refine ⟨(φ k').toLinearMap ∘ₗ gam ∘ₗ (φ k).symm.toLinearMap,
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun w => ?_, fun τ i j hji => ?_,
    fun τ m hm v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
    push_cast
    ring
  · obtain ⟨a, ha⟩ := honto ((φ k').symm w)
    refine ⟨φ k a, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ha, map_nsmul, LinearEquiv.apply_symm_apply]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨m, hm⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range, Finset.mul_sum]
    refine (GlobalTheory.LevelCusp.apply_of_cols e h.toLinearMap
      (fun τ i j => (p : ℂ) * Formalism.L2.PjFree.toC (cf τ i j)) hcol (Pm v) τ ⟨m, hm⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dite_eq_left ⟨hm, j.2⟩, _root_.mul_assoc]
  · beta_reduce
    rw [dite_eq_left ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePointStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_similitude_triangular_periods_of_heckePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ m < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) m = p * ∑ j ∈ Finset.range (Dw.mult τ), A τ m j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (m : Fin (Dw.mult τ)), A τ m m = Formalism.L2.PjFree.toC (t (some ⟨τ, m⟩) : CAt σ) := by
  first | exact @GlobalTheory.HeckeEx.exists_similitude_tri_of_hkPt | exact GlobalTheory.HeckeEx.exists_similitude_tri_of_hkPt | (intros; apply GlobalTheory.HeckeEx.exists_similitude_tri_of_hkPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCarta
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCarta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jm_mul_self {n : ℕ} (e : Fin n → Bool) : Formalism.REAL.Jm e * Formalism.REAL.Jm e = 1 := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem jm_injective {n : ℕ} {e e' : Fin n → Bool} (h : Formalism.REAL.Jm e = Formalism.REAL.Jm e') : e = e' := by
  funext a
  have := congrFun (congrFun h a) a
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at this
  cases he : e a <;> cases he' : e' a <;> simp_all <;> norm_num at this

theorem dsModel_of_onb_cart : ∀ (D : D7), GlobalTheory.Published.DiscreteSeriesUpqExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε) → (∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) → ∃ M : DSModel V S, cart M = C ∧ onb M = O := by
  intro D hDS V S O C h1 h2
  choose lam ε hE hP hG using h1
  choose H i1 i2 σ hσ using fun τ =>
    (GlobalTheory.Published.discreteSeriesExists_iff.1 hDS) V.rank (ε τ) (lam τ) (hP τ)
  have hdet : ∀ τ, IsUnit (O τ).det := fun τ => by
    refine Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm (ε τ) * ((O τ)ᴴ * gramAt D V τ)) ?_
    rw [Matrix.mul_assoc, hG τ, jm_mul_self]
  have hr : ∀ τ, O τ * (O τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (hdet τ)
  have hl : ∀ τ, (O τ)⁻¹ * O τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
  have hii : ∀ τ, ((O τ)⁻¹)⁻¹ = O τ := fun τ => Matrix.nonsing_inv_nonsing_inv _ (hdet τ)
  let M : DSModel V S :=
    { H := H, nacg := i1, ips := i2, σ := σ, lam := lam, ε := ε, fr := fun τ => (O τ)⁻¹,
      enum := hE, ds := hσ,
      fr_unit := fun τ => (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet τ))
      fr_gram := fun τ => by
        rw [← hG τ]
        calc ((O τ)⁻¹)ᴴ * ((O τ)ᴴ * gramAt D V τ * O τ) * (O τ)⁻¹
            = (O τ * (O τ)⁻¹)ᴴ * gramAt D V τ * (O τ * (O τ)⁻¹) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = gramAt D V τ := by rw [hr τ]; simp }
  refine ⟨M, ?_, ?_⟩
  · funext τ
    obtain ⟨e', hG', hC⟩ := h2 τ
    have he : e' = ε τ := jm_injective (by rw [← hG', hG τ])
    rw [he] at hC
    show ((O τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (O τ)⁻¹ = C τ
    rw [hii, ← hC, Matrix.mul_assoc, hr, Matrix.mul_one]
  · funext τ
    exact hii τ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCartaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan : ∀ (D : D7), GlobalTheory.Published.DiscreteSeriesUpqExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε) → (∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) → ∃ M : DSModel V S, cart M = C ∧ onb M = O := by
  first | exact @GlobalTheory.dsModel_of_onb_cart | exact GlobalTheory.dsModel_of_onb_cart | (intros; apply GlobalTheory.dsModel_of_onb_cart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PureTensorExists

theorem existsUnique_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC x hx
  classical
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.PlaceTensor.base_std hB
  have hf0 : IsThetaFunO ψ S T f₀ := GlobalTheory.PlaceTensor.base_theta hB

  have build : ∀ (s : Finset (Place D)) (y : Place D → WO S T → ℂ),
      IsRestricted ψ θ S T sS sT ΛS ΛT f₀ y → (∀ p, y p ≠ f₀ → p ∈ s) →
        ∃ f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro y _ hy
      have hconst : y = fun _ => f₀ := by
        funext p
        by_contra hne
        exact absurd (hy p hne) (by simp)
      subst hconst
      exact ⟨f₀, (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1⟩
    · intro q s _ ih y hyR hy

      have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update y q f₀) := by
        refine ⟨fun p => ?_, ?_⟩
        · by_cases hpq : p = q
          · subst hpq
            simpa using GlobalTheory.PlaceTensor.base_isLocal hB p
          · simpa [Function.update_apply, hpq] using hyR.1 p
        · refine hyR.2.subset fun p hp => ?_
          by_cases hpq : p = q
          · subst hpq
            simp at hp
          · simpa [Function.update_apply, hpq] using hp
      have hsub : ∀ p, Function.update y q f₀ p ≠ f₀ → p ∈ s := by
        intro p hp
        by_cases hpq : p = q
        · subst hpq
          simp at hp
        · have hp' : y p ≠ f₀ := by simpa [Function.update_apply, hpq] using hp
          rcases Finset.mem_insert.1 (hy p hp') with h | h
          · exact absurd h hpq
          · exact h
      obtain ⟨f, hf⟩ := ih (Function.update y q f₀) hres hsub
      obtain ⟨f', hf', -⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC
        (Function.update y q f₀) y f q hf (by simp)
        (fun p hp => (Function.update_of_ne hp f₀ y).symm) (hyR.1 q)
      exact ⟨f', hf'⟩
  obtain ⟨f, hf⟩ := build hx.2.toFinset x hx (fun p hp => by simpa using hp)
  refine ⟨f, hf, fun g hg => ?_⟩

  obtain ⟨hHaar, hFD, -⟩ := id hC
  have hfT : IsThetaFunO ψ S T f := hf.2.1
  have hgT : IsThetaFunO ψ S T g := hg.2.1
  have hIP := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hstd hC
  have hd : IsThetaFunO ψ S T (g - f) := GlobalTheory.WeilVacMove.isTheta_sub hgT hfT
  have hz : g - f = 0 := by
    refine GlobalTheory.HeisTotal.eq_zero_of_orthogonal_translates D ψ hstd S T f₀ (g - f) hf0
      (GlobalTheory.PlaceTensor.base_ne_zero hB) hd μ 𝓕 hHaar hFD fun w => ?_
    have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₀ hf0
    have e1 : ipO μ 𝓕 g (heisO ψ S T w f₀) = ipO μ 𝓕 f (heisO ψ S T w f₀) := by
      rw [(hg.2.2 w).2, (hf.2.2 w).2]
    have e2 : ipO μ 𝓕 (heisO ψ S T w f₀) g = ipO μ 𝓕 (heisO ψ S T w f₀) f := by
      rw [(hIP g _ hgT hw).2.1, (hIP f _ hfT hw).2.1, e1]
    have e3 := ((hIP (g - f) _ hd hw).2.2.2.1 f hfT).2
    rw [sub_add_cancel] at e3
    have e4 : ipO μ 𝓕 (heisO ψ S T w f₀) (g - f) = 0 := by
      linear_combination e2 - e3
    exact e4
  exact sub_eq_zero.1 hz

end GlobalTheory.PureTensorExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_pureTensor_restrictedFamily : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  first | exact @GlobalTheory.PureTensorExists.existsUnique_isPure | exact GlobalTheory.PureTensorExists.existsUnique_isPure | (intros; apply GlobalTheory.PureTensorExists.existsUnique_isPure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridNodeSignatureSelfDual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.Grid.Vertex

theorem negIdx_of_sig {D : D7} (V : HSp D) (q : ℕ) (h : V.SigOK) (hs : ∀ τ : D.host.E →+* ℂ, V.sig τ = (V.rank - q, q)) :
    NegIdx V q := fun τ => by
  have := h (tauE D τ)
  rw [hs] at this
  exact this

end GlobalTheory.Grid.Vertex

end
end
