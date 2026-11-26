module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBound
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem unip_mul_diag_cone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  intro E _ _ _ a t ht i j hij
  obtain ⟨C0, hC0, hb⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  refine ⟨C0 * C0 + C0, by positivity, ?_⟩
  intro r d hr hcone hd
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hji : r j / r i ≤ C0 := hb r hr hcone i j hij'
  have hji0 : 0 ≤ r j / r i := (div_pos (hr j) (hr i)).le
  refine ⟨by nlinarith, fun z => ?_⟩
  refine ⟨fun p => (r p.1.2 / r p.1.1) • z p, ?_, ?_⟩
  · have hX : 0 ≤ (C0 * C0 + C0) * (r j / r i) := by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    have hk : p.1.1 ≤ i := by rw [Fin.le_def]; have := p.2.1; omega
    have hl : j ≤ p.1.2 := by rw [Fin.le_def]; exact p.2.2
    have h1 : r p.1.2 / r j ≤ C0 := hb r hr hcone j p.1.2 hl
    have h3 : r i / r p.1.1 ≤ C0 := hb r hr hcone p.1.1 i hk
    have hpos : 0 < r p.1.2 / r p.1.1 := div_pos (hr _) (hr _)
    have heq : r p.1.2 / r p.1.1 = (r p.1.2 / r j) * (r j / r i) * (r i / r p.1.1) := by
      have := hr j; have := hr i; have := hr p.1.1
      field_simp
    have hbd : r p.1.2 / r p.1.1 ≤ (C0 * C0 + C0) * (r j / r i) := by
      rw [heq]
      have e1 : 0 ≤ r p.1.2 / r j := (div_pos (hr _) (hr _)).le
      have e3 : 0 ≤ r i / r p.1.1 := (div_pos (hr _) (hr _)).le
      calc r p.1.2 / r j * (r j / r i) * (r i / r p.1.1) ≤ C0 * (r j / r i) * C0 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hji0) h3 e3 (by positivity)
        _ ≤ (C0 * C0 + C0) * (r j / r i) := by nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact mul_le_mul hbd (norm_le_pi_norm z p) (norm_nonneg _) hX
  · intro τ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hd]
    change (1 + nilM (τ • z)) * _ = _ * (1 + nilM (τ • fun p => (r p.1.2 / r p.1.1) • z p))
    ext k l w
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    congr 1
    simp only [nilM, Matrix.of_apply]
    split_ifs with h
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, add_right_inj]
      have := hr k
      have hk0 : (r k : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast
      field_simp
    · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBoundStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUnipotent_conj_coneDiagonal_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  first | exact @GlobalTheory.unip_mul_diag_cone | exact GlobalTheory.unip_mul_diag_cone | (intros; apply GlobalTheory.unip_mul_diag_cone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirections
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem exists_finset_clm_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (B : Finset V) (C : ℝ), 0 ≤ C ∧ ∀ (L : V →L[ℝ] ℂ) (X : V) (M : ℝ),
      (∀ Y ∈ B, ‖L Y‖ ≤ M) → 0 ≤ M → ‖L X‖ ≤ C * ‖X‖ * M := by
  classical
  obtain ⟨C, hC, h⟩ := (Module.finBasis ℝ V).exists_opNorm_le (F := ℂ)
  refine ⟨Finset.univ.image (Module.finBasis ℝ V), C, hC.le, fun L X M hB hM => ?_⟩
  have h1 : ‖L‖ ≤ C * M := h hM fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  calc ‖L X‖ ≤ ‖L‖ * ‖X‖ := L.le_opNorm X
    _ ≤ C * M * ‖X‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C * ‖X‖ * M := by ring

theorem lieD_le_of_basis : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  intro E _ _ _ a
  obtain ⟨B, C, hC, h⟩ := exists_finset_clm_bound (Lie E a)
  exact ⟨B, C, hC, fun ψ g X M hB hM => h (fderiv ℝ (chart ψ g) (oneL E a)) X M hB hM⟩

end GlobalTheory.CuspRapid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirectionsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  first | exact @GlobalTheory.CuspRapid.lieD_le_of_basis | exact GlobalTheory.CuspRapid.lieD_le_of_basis | (intros; apply GlobalTheory.CuspRapid.lieD_le_of_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegment
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegment
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem norm_sub_le_of_lieD_unipotent_segment (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ)
    (hn : n * n = 0) (hu : ∀ τ : ℝ, (u τ).val = 1 + τ • n)
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) :
    ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  have h0 : u 0 = 1 := Units.ext (by rw [hu]; simp)
  have hadd : ∀ τ s : ℝ, u (τ + s) = u τ * u s := by
    intro τ s
    refine Units.ext ?_
    rw [Units.val_mul, hu, hu, hu]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hn, smul_zero, add_zero, add_smul]
    abel
  have hc : HasDerivAt (fun t => toL (u t).val) (toL n) 0 := by
    have e : (fun t : ℝ => toL (u t).val) = fun t : ℝ => oneL E a + t • toL n := by
      funext t; rw [hu]; rfl
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL n)).const_add (oneL E a)
  have hd : ∀ τ : ℝ, HasDerivAt (fun t => ψ.1 (g * infGL E a (u t)))
      (lieD (toL n) ψ.1 (g * infGL E a (u τ))) τ := by
    intro τ
    have h1 := hasDerivAt_curve ψ (g * infGL E a (u τ)) u (toL n) h0 hc
    have h2 : HasDerivAt (fun s => ψ.1 (g * infGL E a (u τ) * infGL E a (u s)))
        (lieD (toL n) ψ.1 (g * infGL E a (u τ))) (τ - τ) := by rwa [sub_self]
    have h3 := h2.comp_sub_const τ τ
    have e : (fun t => ψ.1 (g * infGL E a (u τ) * infGL E a (u (t - τ)))) =
        fun t => ψ.1 (g * infGL E a (u t)) := by
      funext t
      rw [mul_assoc, ← map_mul, ← hadd, add_sub_cancel]
    rwa [e] at h3
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t => ψ.1 (g * infGL E a (u t)))
    (fun τ _ => (hd τ).hasDerivWithinAt) (fun τ hτ => hM τ (Set.Ico_subset_Icc_self hτ))
  simpa [h0] using h

end GlobalTheory.CuspRapid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegmentStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ), n * n = 0 → (∀ τ : ℝ, (u τ).val = 1 + τ • n) → (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) → ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  first | exact @GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | exact GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | (intros; apply GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotent
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapVari

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem nilM_smul {r : ℕ} (τ : ℝ) (x : BlockIx a r → Cinf E) :
    (nilM (τ • x) : Matrix (Fin a) (Fin a) (Cinf E)) = τ • nilM x := by
  ext i j
  simp only [nilM, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem norm_toL_nilM_le {r : ℕ} (x : BlockIx a r → Cinf E) :
    ‖toL (nilM x : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  change ‖(nilM x : Matrix (Fin a) (Fin a) (Cinf E)) i j‖ ≤ ‖x‖
  simp only [nilM, Matrix.of_apply]
  split_ifs with h
  · exact norm_le_pi_norm x _
  · simp

theorem continuous_unip_inf {r : ℕ} :
    Continuous (fun x : BlockIx a r → Cinf E => (unip x : GL (Fin a) (Cinf E))) := by
  have hN : Continuous (fun x : BlockIx a r → Cinf E => (nilM x : Matrix (Fin a) (Fin a) (Cinf E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hN, continuous_const.sub hN⟩

theorem exists_bound_compact {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Ω, ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A ∧
      ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A := by
  have h1 : Continuous (fun c : GL (Fin a) (Cinf E) => toL (c : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  have h2 : Continuous (fun c : GL (Fin a) (Cinf E) =>
      toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  obtain ⟨A1, hA1⟩ := hΩ.exists_bound_of_continuousOn h1.continuousOn
  obtain ⟨A2, hA2⟩ := hΩ.exists_bound_of_continuousOn h2.continuousOn
  exact ⟨max (max A1 A2) 0, le_max_right _ _, fun c hc =>
    ⟨(hA1 c hc).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hA2 c hc).trans ((le_max_right _ _).trans (le_max_left _ _))⟩⟩

theorem norm_conj_le (A : ℝ) (c : GL (Fin a) (Cinf E)) (N : Matrix (Fin a) (Fin a) (Cinf E))
    (h1 : ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A)
    (h2 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A) :
    ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N * c.val)‖ ≤ a * a * A * A * ‖toL N‖ := by
  have hA : 0 ≤ A := (norm_nonneg _).trans h1
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have p1 := norm_toL_mul_le ((c⁻¹ : GL (Fin a) (Cinf E)).val * N) c.val
  have p2 := norm_toL_mul_le (c⁻¹ : GL (Fin a) (Cinf E)).val N
  have p2' : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ ≤ a * (A * ‖toL N‖) :=
    p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) ha)
  have p3 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ * ‖toL c.val‖ ≤ (a * (A * ‖toL N‖)) * A :=
    mul_le_mul p2' h1 (norm_nonneg _) (mul_nonneg ha (mul_nonneg hA (norm_nonneg _)))
  exact (p1.trans (mul_le_mul_of_nonneg_left p3 ha)).trans (le_of_eq (by ring))

end GlobalTheory.RapVari


open GlobalTheory.RapVari in
theorem GlobalTheory.rap_vari : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t →
    ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ R : ℝ, 0 ≤ R →
    ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧
    ∀ ψ : Sm E a, ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
    (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
    ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω,
    ∀ z : BlockIx a j → Cinf E, ‖z‖ ≤ R →
    ‖ψ.1 (infGL E a (unip z * (d * c))) - ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a t ht i j hij Ω hΩ R hR
  obtain ⟨C0, hC0, hconj⟩ := GlobalTheory.T.blockUnipotent_conj_coneDiagonal_bound E a t ht i j hij
  obtain ⟨B, Cb, hCb, hbasis⟩ := GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections E a
  obtain ⟨A, hA, hAc⟩ := exists_bound_compact hΩ
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have haA : (0 : ℝ) ≤ a * a * A * A := mul_nonneg (mul_nonneg (mul_nonneg ha ha) hA) hA
  refine ⟨(fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
      (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω), B, Cb * (a * a * A * A) * (C0 * R), ?_, ?_, ?_⟩
  · exact ((isCompact_closedBall 0 (C0 * C0 * R)).prod hΩ).image
      ((continuous_unip_inf.comp continuous_fst).mul continuous_snd)
  · exact mul_nonneg (mul_nonneg hCb haA) (mul_nonneg hC0 hR)
  intro ψ r d hr hrat hd M hM hB c hc z hz
  obtain ⟨hq, hz'⟩ := hconj r d hr hrat hd
  obtain ⟨z', hz'n, hcomm⟩ := hz' z
  have hq0 : 0 ≤ r j / r i := div_nonneg (hr j).le (hr i).le
  have hz'R : ‖z'‖ ≤ C0 * (r j / r i) * R := hz'n.trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hC0 hq0))
  have hz'R' : ‖z'‖ ≤ C0 * C0 * R :=
    hz'R.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC0) hR)
  have hu : ∀ τ : ℝ, ((c⁻¹ * unip (τ • z') * c : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      1 + τ • ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) := by
    intro τ
    rw [Units.val_mul, Units.val_mul]
    change (c⁻¹ : GL (Fin a) (Cinf E)).val * (1 + nilM (τ • z')) * c.val = _
    rw [nilM_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hNN : ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) *
      ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) = 0 := by
    calc _ = (c⁻¹ : GL (Fin a) (Cinf E)).val *
          (nilM z' * (c.val * (c⁻¹ : GL (Fin a) (Cinf E)).val) * nilM z') * c.val := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Units.mul_inv, Matrix.mul_one, nilM_mul, Matrix.mul_zero, Matrix.zero_mul]
  have hNnorm : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val)‖ ≤
      a * a * A * A * (C0 * (r j / r i) * R) :=
    (norm_conj_le A c _ (hAc c hc).1 (hAc c hc).2).trans
      (mul_le_mul_of_nonneg_left ((norm_toL_nilM_le z').trans hz'R) haA)
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, unip (τ • z') * c ∈
      (fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
        (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω) := by
    intro τ hτ
    refine ⟨(τ • z', c), ⟨?_, hc⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hτ.2).trans hz'R'
  have key := GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment E a ψ (infGL E a (d * c)) _ (fun τ => c⁻¹ * unip (τ • z') * c)
    (Cb * (a * a * A * A * (C0 * (r j / r i) * R)) * M) hNN hu (by
      intro τ hτ
      have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip (τ • z') * c) =
          infGL E a (d * (unip (τ • z') * c)) := by
        rw [← map_mul]; congr 1; group
      rw [e]
      refine (hbasis ψ.1 _ _ M (fun Y hY => hB Y hY _ (hmem τ hτ)) hM).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNnorm hCb) hM)
  have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip ((1 : ℝ) • z') * c) = infGL E a (unip z * (d * c)) := by
    rw [← map_mul]; congr 1
    have h1 := hcomm 1
    rw [one_smul, one_smul] at h1
    rw [one_smul, ← mul_assoc (unip z) d c, h1]
    group
  rw [e] at key
  exact key.trans (le_of_eq (by ring))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotentStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelCone_smooth_variation_along_bounded_unipotent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ R : ℝ, 0 ≤ R → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ ψ : Sm E a, ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ∀ z : BlockIx a j → Cinf E, ‖z‖ ≤ R → ‖ψ.1 (infGL E a (unip z * (d * c))) - ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  first | exact @GlobalTheory.rap_vari | exact GlobalTheory.rap_vari | (intros; apply GlobalTheory.rap_vari <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariation
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.CuspRep

theorem norm_le_of_unip_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a),
    IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ),
      (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  intro E _ _ _ a ψ hψ s hs0 hsa g e he
  letI : MeasurableSpace (BlockIx a s → Ad E) := borel _
  haveI : BorelSpace (BlockIx a s → Ad E) := ⟨rfl⟩
  set μ : Measure (BlockIx a s → Ad E) := Measure.addHaar with hμ
  obtain ⟨𝓕, h𝓕, h0, htop⟩ := GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL E a s μ
  have hc := ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  have hI := CuspidalL2GL.integrableOn_unip hc hψ.1.left μ h𝓕 g
  have hz : ∫ x in 𝓕, ψ.1 (unip x * g) ∂μ = 0 := hψ.2 s hs0 hsa μ 𝓕 inferInstance h𝓕 g
  have key : ∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ = μ.real 𝓕 • ψ.1 g := by
    have h1 : IntegrableOn (fun _ => ψ.1 g) 𝓕 μ := integrableOn_const htop.ne
    rw [integral_sub h1 hI, hz, setIntegral_const, sub_zero]
  have hb : ‖∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ‖ ≤ e * μ.real 𝓕 :=
    norm_setIntegral_le_of_norm_le_const htop fun x _ => by rw [norm_sub_rev]; exact he x
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, mul_comm] at hb
  have hpos : 0 < μ.real 𝓕 := ENNReal.toReal_pos h0 htop.ne
  exact le_of_mul_le_mul_right hb hpos

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariationStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ), (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  first | exact @GlobalTheory.CuspRep.norm_le_of_unip_variation | exact GlobalTheory.CuspRep.norm_le_of_unip_variation | (intros; apply GlobalTheory.CuspRep.norm_le_of_unip_variation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFinite
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AdeleApprox

theorem exists_compact_integral (E : Type) [Field E] [NumberField E] :
    ∃ C : Set (InfiniteAdeleRing E), IsCompact C ∧
      ∀ x : Ad E, ∃ a : E, (x - algebraMap E (Ad E) a).1 ∈ C ∧
        ∀ v, (x - algebraMap E (Ad E) a).2 v ∈ v.adicCompletionIntegers E := by
  obtain ⟨C, hC, hCy⟩ := Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap E _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap E (Af E) (u + r) =
        (x.2 - algebraMap E _ u) - algebraMap E _ (r : E) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

theorem exists_rat_sub_bounded_small :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧
        pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  intro E _ _ _ U hU
  obtain ⟨C, hC, hcov⟩ := exists_compact_integral E
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU
  have hc : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded
  refine ⟨N * max B 0, by positivity, fun x => ?_⟩
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, h1, h2⟩ := hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)
  set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk
  have e : x - algebraMap E (Ad E) ((N : E) * a) = N • k := by
    rw [hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hN', map_one, one_mul, map_mul]
  refine ⟨(N : E) * a, ?_, ?_⟩
  · rw [e, map_nsmul]
    have hb : ‖pInf E k‖ ≤ max B 0 := (hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · rw [e, map_nsmul]
    exact hNU _ h2

end GlobalTheory.AdeleApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFiniteStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧ pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  first | exact @GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | exact GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | (intros; apply GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeve
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapCover

theorem unip_eq_rat_mul_inf_mul_fin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ)
    (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E,
    ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧
    unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  intro E _ _ _ a s L hL
  have h0 : (unip (0 : BlockIx a s → Af E)) = 1 := by
    have h := unip_add (0 : BlockIx a s → Af E) 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hpre : (fun y : BlockIx a s → Af E => unip y) ⁻¹' L ∈ nhds (0 : BlockIx a s → Af E) := by
    apply JointCont.continuous_unip.continuousAt.preimage_mem_nhds
    rw [h0]; exact hL
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hU : (⋂ p, t p) ∈ nhds (0 : Af E) := Filter.iInter_mem.2 fun p => by simpa using ht p
  obtain ⟨R, hR, hx⟩ := GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite E (⋂ p, t p) hU
  refine ⟨R, hR, fun x => ?_⟩
  choose ξ hξ1 hξ2 using fun p => hx (x p)
  refine ⟨ξ, fun p => pInf E (x p - algebraMap E (Ad E) (ξ p)),
    unip (fun p => pFin E (x p - algebraMap E (Ad E) (ξ p))), ?_, ?_, ?_⟩
  · apply hsub
    intro p _
    exact Set.mem_iInter.1 (hξ2 p) p
  · exact (pi_norm_le_iff_of_nonneg hR).2 hξ1
  · have hsplit : x = (fun p => algebraMap E (Ad E) (ξ p)) + (fun p => x p - algebraMap E (Ad E) (ξ p)) := by
      funext p; simp
    conv_lhs => rw [hsplit, unip_add, unip_algebraMap,
      ← infGL_mul_finGL (unip (fun p => x p - algebraMap E (Ad E) (ξ p))), JointCont.map_unip, JointCont.map_unip]
    rw [mul_assoc]

end GlobalTheory.RapCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeveStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E, ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧ unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  first | exact @GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | exact GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | (intros; apply GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStep
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_decay_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a ψ hψ t ht i j hij Ω hΩ
  have hL : {k | finRep E a k ψ = ψ} ∈ nhds (1 : GL (Fin a) (Af E)) :=
    hψ.1.level.mem_nhds (by simp)
  obtain ⟨R, hR0, hcov⟩ := GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level E a (j : ℕ) _ hL
  obtain ⟨Ω', B, C, hΩ', hC, hvar⟩ := GlobalTheory.T.siegelCone_smooth_variation_along_bounded_unipotent E a t ht i j hij Ω hΩ R hR0
  refine ⟨Ω', B, C, hΩ', hC, fun r d hr hrt hd M hM hY c hc => ?_⟩
  refine GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation E a ψ hψ (j : ℕ) (by omega) j.2 (infGL E a (d * c)) (C * (r j / r i) * M) fun x => ?_
  obtain ⟨ξ, z, k, hk, hz, hx⟩ := hcov x
  have hk' : finRep E a k ψ = ψ := hk
  have e : ψ.1 (unip x * infGL E a (d * c)) = ψ.1 (infGL E a (unip z * (d * c))) := by
    rw [hx, mul_assoc, mul_assoc, ← infGL_comm, ← mul_assoc (infGL E a (unip z)), ← map_mul, hψ.1.left]
    have := congrArg (fun φ : Sm E a => φ.1 (infGL E a (unip z * (d * c)))) hk'
    exact this
  rw [e]
  exact hvar ψ r d hr hrt hd M hM hY c hc z hz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStepStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  first | exact @GlobalTheory.cuspForm_decay_step | exact GlobalTheory.cuspForm_decay_step | (intros; apply GlobalTheory.cuspForm_decay_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowth
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem iterated_decay : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  intro hfin E _ _ _ a N t ht i j hij m
  induction m with
  | zero =>
    intro ψ _ htame Ω hΩ
    obtain ⟨C0, hC0⟩ := htame []
    obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
    refine ⟨|C0| * B ^ N, by positivity, ?_⟩
    intro r d _ _ _ c hc
    have h1 := hC0 (d * c)
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h1
    have hh0 : 0 ≤ height (d * c) := le_trans zero_le_one (one_le_height _)
    have hh : height (d * c) ^ N ≤ (B * height d) ^ N := pow_le_pow_left₀ hh0 (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C0 * height (d * c) ^ N := h1
      _ ≤ |C0| * height (d * c) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hh0 N)
      _ ≤ |C0| * (B * height d) ^ N := mul_le_mul_of_nonneg_left hh (abs_nonneg C0)
      _ = |C0| * B ^ N * (r j / r i) ^ 0 * height d ^ N := by rw [mul_pow]; ring
  | succ m ih =>
    intro ψ hψ htame Ω hΩ
    obtain ⟨Ω', B, C, hΩ', hC, hstep⟩ := GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step E a ψ hψ t ht i j hij Ω hΩ
    have hY : ∀ Y ∈ B, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
        ∀ c ∈ Ω', ‖(lie E a Y ψ).1 (infGL E a (d * c))‖ ≤ C' * (r j / r i) ^ m * height d ^ N := by
      intro Y _
      have hcusp : IsCuspForm (lie E a Y ψ) := GlobalTheory.T.isCuspForm_operator_act hfin E a (.lie Y) ψ hψ
      refine ih (lie E a Y ψ) hcusp ?_ Ω' hΩ'
      intro l
      obtain ⟨C1, hC1⟩ := htame (l ++ [Y])
      refine ⟨C1, fun y => ?_⟩
      have e : (l.map (lie E a)).prod (lie E a Y ψ) = ((l ++ [Y]).map (lie E a)).prod ψ := by
        simp [List.map_append, List.prod_append, Module.End.mul_apply]
      rw [e]
      exact hC1 y
    choose! CY hCY0 hCY using hY
    refine ⟨C * ∑ Y ∈ B, CY Y, mul_nonneg hC (Finset.sum_nonneg hCY0), ?_⟩
    intro r d hr hrt hd c hc
    have hq : 0 ≤ (r j / r i) ^ m * height d ^ N :=
      mul_nonneg (pow_nonneg (div_nonneg (hr j).le (hr i).le) m)
        (pow_nonneg (le_trans zero_le_one (one_le_height d)) N)
    have hM0 : 0 ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
      mul_nonneg (Finset.sum_nonneg hCY0) hq
    have h := hstep r d hr hrt hd _ hM0 (fun Y hYB c' hc' => by
      have h2 : lieD Y ψ.1 = (lie E a Y ψ).1 := rfl
      rw [h2]
      calc ‖(lie E a Y ψ).1 (infGL E a (d * c'))‖ ≤ CY Y * (r j / r i) ^ m * height d ^ N := hCY Y hYB r d hr hrt hd c' hc'
        _ = CY Y * ((r j / r i) ^ m * height d ^ N) := by ring
        _ ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun Y hY => hCY0 Y hY) hYB) hq) c hc
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * ((∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N)) := h
      _ = (C * ∑ Y ∈ B, CY Y) * (r j / r i) ^ (m + 1) * height d ^ N := by ring

end GlobalTheory.CuspRapid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowthStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_GL_iterated_decay_moderateGrowth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  first | exact @GlobalTheory.CuspRapid.iterated_decay | exact GlobalTheory.CuspRapid.iterated_decay | (intros; apply GlobalTheory.CuspRapid.iterated_decay <;> assumption)
end
