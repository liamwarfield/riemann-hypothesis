module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVec_add {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (u + v) := by
  obtain ⟨F, hF, hF'⟩ := hu
  obtain ⟨K, hK, hK'⟩ := hv
  exact ⟨fun z => F z + K z, hF.add hK, fun z hz => by rw [map_add (f := _), hF' z hz, hK' z hz]⟩

theorem isSmoothVec_smul (c : ℂ) {v : H} (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (c • v) := by
  obtain ⟨F, hF, hF'⟩ := hv
  exact ⟨fun z => c • F z, hF.const_smul c, fun z hz => by rw [map_smul, hF' z hz]⟩

theorem isSmoothVec_zero : IsSmoothVec G π (0 : H) :=
  ⟨fun _ => 0, contDiff_const, fun z _ => map_zero _⟩

theorem isSmoothVec_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → H)
    (hf : ∀ i, IsSmoothVec G π (f i)) : IsSmoothVec G π (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothVec_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSmoothVec_add (isSmoothVec_smul _ (hf a)) ih

variable {d : ℕ} {b : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem word_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {w : H} (hw : IsSmoothVec G π w) :
    IsSmoothVec G π (p.foldr (fun i w => dRep π (b i) w) w) := by
  induction p with
  | nil => exact hw
  | cons i p ih => exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih (hb i)).2

theorem list_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) {v : H}
    (hv : IsSmoothVec G π v) : IsSmoothVec G π (l.foldr (dRep π) v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep
      (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) (hl X List.mem_cons_self)).2

theorem word_add (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {u v : H} (hu : IsSmoothVec G π u)
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (u + v) =
      p.foldr (fun i w => dRep π (b i) w) u + p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hu)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.1

theorem word_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) (c : ℂ) {v : H}
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (c • v) =
      c • p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hv)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.2 c

theorem word_sum (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → H) (hf : ∀ i, IsSmoothVec G π (f i)) :
    p.foldr (fun i w => dRep π (b i) w) (∑ j ∈ s, c j • f j) =
      ∑ j ∈ s, c j • p.foldr (fun i w => dRep π (b i) w) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := word_smul hG hrep hb p (0 : ℂ) (isSmoothVec_zero (G := G) (π := π) (H := H))
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      word_add hG hrep hb p (isSmoothVec_smul _ (hf a)) (isSmoothVec_sum s c f hf),
      word_smul hG hrep hb p _ (hf a), ih]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem prod_mnorm_nonneg (l : List (Matrix (Fin n) (Fin n) ℂ)) : 0 ≤ (l.map mnorm).prod := by
  induction l with
  | nil => simp
  | cons X l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (mnorm_nonneg X) ih

theorem mixed_bound (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) (p : List (Fin d)) :
    ‖p.foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
      C ^ (p.length + l.length + 1) * (p.length + l.length).factorial * D ^ l.length *
        (l.map mnorm).prod := by
  induction l generalizing p with
  | nil => simpa using hbound p
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ HCSS.lieOf G := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX : X ∈ HCSS.lieOf G := hl X List.mem_cons_self
    have hw : IsSmoothVec G π (l.foldr (dRep π) v) := list_smooth hG hrep l hl' hv
    obtain ⟨r, hr⟩ := hsp X hX
    have e1 : dRep π X (l.foldr (dRep π) v) =
        ∑ i, (r i : ℂ) • dRep π (b i) (l.foldr (dRep π) v) := by
      rw [hr]
      exact hexp r _ hw
    have hsm : ∀ i, IsSmoothVec G π (dRep π (b i) (l.foldr (dRep π) v)) := fun i =>
      (hasDerivAt_dRep_and_isSmoothVec hG hrep hw (hb i)).2
    have e2 : p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v)) =
        ∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v) := by
      rw [e1, word_sum hG hrep hb p _ _ _ hsm]
      simp [List.foldr_append]
    have hih : ∀ i, ‖(p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
        C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
          D ^ l.length * (l.map mnorm).prod := by
      intro i
      have h := ih hl' (p ++ [i])
      rw [List.length_append, List.length_singleton,
        show p.length + 1 + l.length = p.length + (l.length + 1) by omega] at h
      exact h
    have hK : 0 ≤ C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
        D ^ l.length * (l.map mnorm).prod :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC.le _) (Nat.cast_nonneg _))
        (pow_nonneg hD0 _)) (prod_mnorm_nonneg l)
    have hsum : ∑ i, |r i| ≤ D * mnorm X := by
      rw [hr]
      exact hD r
    show ‖p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v))‖ ≤ _
    rw [e2]
    calc ‖∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖
        ≤ ∑ i, |r i| * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) := by
          refine norm_sum_le_of_le _ fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hih i) (abs_nonneg _)
      _ = (∑ i, |r i|) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (D * mnorm X) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          mul_le_mul_of_nonneg_right hsum hK
      _ = _ := by
          simp only [List.length_cons, List.map_cons, List.prod_cons]
          ring

theorem wordBound_of_basis {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ}
    (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial) :
    WordBound G π v := by
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
  refine ⟨C * (D + 1), by positivity, fun l hl => ?_⟩
  have h := mixed_bound hG hrep hb hsp D hD0 hD hexp hv C hC hbound l hl []
  simp only [List.foldr_nil, List.length_nil, Nat.zero_add] at h
  refine h.trans ?_
  have hP := prod_mnorm_nonneg l
  have hpow : D ^ l.length ≤ (D + 1) ^ (l.length + 1) :=
    (pow_le_pow_left₀ hD0 (by linarith) _).trans (pow_le_pow_right₀ hD1 (Nat.le_succ _))
  have hCk : 0 ≤ C ^ (l.length + 1) := pow_nonneg hC.le _
  have hf : (0 : ℝ) ≤ l.length.factorial := Nat.cast_nonneg _
  rw [mul_pow]
  calc C ^ (l.length + 1) * l.length.factorial * D ^ l.length * (l.map mnorm).prod
      = (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) * D ^ l.length := by ring
    _ ≤ (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) *
          (D + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hCk hf) hP)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBoundStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_basis_coordinate_growth_bound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i)) (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w → dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w) {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C) (hbound : ∀ l : List (Fin d), ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial), WordBound G π v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rightMul (Y : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Matrix.of.symm (Matrix.of z * Y)
      map_add' := fun x y => by
        ext a b
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext a b
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

theorem rightMul_apply (Y : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → Fin n → ℂ) :
    rightMul Y z = Matrix.of.symm (Matrix.of z * Y) := rfl

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_curve (z : Fin n → Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (rightMul X z) 0 := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [rightMul_apply, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_entry X c b).const_mul (z a c))

def one : Fin n → Fin n → ℂ := Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)

theorem of_one : Matrix.of (one (n := n)) = 1 := by exact Matrix.of.apply_symm_apply _

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
  {F : (Fin n → Fin n → ℂ) → H}

theorem hasDerivAt_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    HasDerivAt (fun t : ℝ => π (Matrix.of z * NormedSpace.exp (t • X)) v)
      (fderiv ℝ F z (rightMul X z)) 0 := by
  have hd : HasFDerivAt F (fderiv ℝ F z) (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X))) := by
    have : (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = z := by
      simp
    rw [this]
    exact (hF.differentiable (by simp) z).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve z X)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm : Matrix.of z * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hz _ (hX t)
  have := hFv (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X))) (by simpa only [Matrix.of.apply_symm_apply] using hm)
  simpa only [Matrix.of.apply_symm_apply, Function.comp_def] using this

theorem hasDerivAt_exp_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (fderiv ℝ F one (rightMul X one)) 0 := by
  have h := hasDerivAt_along hG hF hFv hX (z := one) (by rw [of_one]; exact hG.one_mem)
  simpa [of_one] using h

theorem dRep_eq (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : dRep π X v = fderiv ℝ F one (rightMul X one) :=
  (hasDerivAt_exp_along hG hF hFv hX).deriv

theorem rep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    π (Matrix.of z) (dRep π X v) = fderiv ℝ F z (rightMul X z) := by
  have h1 := hasDerivAt_exp_along hG hF hFv hX
  have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := hasDerivAt_along hG hF hFv hX hz
  rw [dRep_eq hG hF hFv hX]
  refine HasDerivAt.unique ?_ h3
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 _ hz _ (hX t)
  simp [this]

theorem dRep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π X (dRep π Y v) =
      fderiv ℝ (fderiv ℝ F) one (rightMul X one) (rightMul Y one) +
        fderiv ℝ F one (rightMul Y (rightMul X one)) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) one) one :=
    (hF1.differentiable (by simp) one).hasFDerivAt
  have hG1 := hdF.clm_apply (rightMul Y).hasFDerivAt
  have hc := hasDerivAt_curve (one (n := n)) X
  have h0 : (Matrix.of.symm (Matrix.of (one (n := n)) * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = one := by
    simp [one]
  have h := hG1.comp_hasDerivAt_of_eq (0 : ℝ) hc h0.symm
  have h' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (dRep π Y v)) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have := rep_dRep hG hrep hF hFv hY (z := Matrix.of.symm (NormedSpace.exp (t • X)))
        (by simpa only [Matrix.of.apply_symm_apply] using hX t)
      simpa only [Matrix.of.apply_symm_apply, of_one, one_mul, Function.comp_def] using this)
  refine h'.deriv.trans ?_
  simp [add_comm]

end Smooth

theorem dRep_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hZ : X * Y - Y * X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.2.1 X Y hX hY
  have hsymm : IsSymmSndFDerivAt ℝ F one :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  rw [dRep_dRep hG hrep hF hFv hX hY, dRep_dRep hG hrep hF hFv hY hX, dRep_eq hG hF hFv hZ,
    hsymm.eq (rightMul X one) (rightMul Y one), add_sub_add_left_eq_sub, ← map_sub]
  congr 1
  simp only [rightMul_apply, Matrix.of.apply_symm_apply, of_one, one_mul]
  ext a b
  rfl

theorem smooth_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) :=
  fun hG hrep _ hv _ _ hX hY => dRep_bracket hG hrep hv hX hY

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutatorStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_commutator : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem deriv_nonneg_of_nonneg_right {e : ℝ → ℝ} {e' : ℝ} (h : HasDerivAt e e' 0) (h0 : e 0 = 0)
    (hpos : ∀ t, 0 < t → 0 ≤ e t) : 0 ≤ e' := by
  refine ge_of_tendsto h.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hpos t ht)

theorem isBoundedBilinearMap_re_form {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q : H → H → ℂ) (Mb : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y))
    (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) :
    IsBoundedBilinearMap ℝ (fun p : H × H => (Q p.1 p.2).re) := by
  have hsmulR : ∀ (c : ℝ) (x y : H), Q x (c • y) = (c : ℂ) * Q x y := fun c x y => by
    rw [← hsmul, Complex.coe_smul]
  have haddL : ∀ x₁ x₂ y, Q (x₁ + x₂) y = Q x₁ y + Q x₂ y := fun x₁ x₂ y => by
    rw [hconj, hadd, star_add, ← hconj, ← hconj]
  have hsmulL : ∀ (c : ℝ) (x y : H), Q (c • x) y = (c : ℂ) * Q x y := fun c x y => by
    rw [hconj, hsmulR, star_mul', ← hconj, show star (c : ℂ) = c from Complex.conj_ofReal c]
  refine ⟨fun x₁ x₂ y => ?_, fun c x y => ?_, fun x y₁ y₂ => ?_, fun c x y => ?_, ?_⟩
  · simp only [haddL, Complex.add_re]
  · simp only [hsmulL, Complex.re_ofReal_mul, smul_eq_mul]
  · simp only [hadd, Complex.add_re]
  · simp only [hsmulR, Complex.re_ofReal_mul, smul_eq_mul]
  · refine ⟨max Mb 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x y => ?_⟩
    rw [Real.norm_eq_abs]
    calc |(Q x y).re| ≤ ‖Q x y‖ := Complex.abs_re_le_norm _
      _ ≤ Mb * ‖x‖ * ‖y‖ := hbd x y
      _ ≤ max Mb 1 * ‖x‖ * ‖y‖ := by gcongr; exact le_max_left _ _

theorem abs_two_re_form_dRep_le : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  intro n G H _ _ π hG hrep Q Mb a hadd hsmul hconj hbd hgrow X hX x hx
  have hB := isBoundedBilinearMap_re_form Q Mb hadd hsmul hconj hbd
  have hv : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 :=
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hx hX).1
  have hv0 : π (NormedSpace.exp ((0 : ℝ) • X)) x = x := by
    rw [zero_smul, NormedSpace.exp_zero, hrep.1]
    rfl
  set d := dRep π X x with hd
  set f : ℝ → ℝ := fun t => (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re with hf_def
  have hf : HasDerivAt f (2 * (Q d x).re) 0 := by
    have h1 := (hB.hasFDerivAt (π (NormedSpace.exp ((0 : ℝ) • X)) x, π (NormedSpace.exp ((0 : ℝ) • X)) x)).comp_hasDerivAt
      (0 : ℝ) (hv.prodMk hv)
    rw [hB.deriv_apply] at h1
    simp only [hv0] at h1
    have e : (Q x d).re + (Q d x).re = 2 * (Q d x).re := by
      rw [hconj d x, Complex.star_def, Complex.conj_re]
      ring
    rw [e] at h1
    exact h1
  have hf0 : f 0 = (Q x x).re := by
    simp only [hf_def, hv0]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (a * t * mnorm X) * (Q x x).re) (a * mnorm X * (Q x x).re) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => a * t * mnorm X) (a * 1 * mnorm X) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul a).mul_const (mnorm X)
    have h3 := (h2.exp).mul_const (Q x x).re
    simpa using h3
  have up : 2 * (Q d x).re ≤ a * mnorm X * (Q x x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hf) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX t x
      rw [abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  have hfn : HasDerivAt (fun t : ℝ => f (-t)) (2 * (Q d x).re * -1) 0 := by
    have hf' : HasDerivAt f (2 * (Q d x).re) (-(0 : ℝ)) := by rwa [neg_zero]
    exact hf'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have low : -(a * mnorm X * (Q x x).re) ≤ 2 * (Q d x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hfn) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX (-t) x
      rw [abs_neg, abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  rw [abs_le]
  exact ⟨low, up⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowthStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_hermitian_form_growth : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord

theorem sum_abs_coord_le_mnorm {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hli : LinearIndependent ℝ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun r a c => ∑ i, r i • b i a c
      map_add' := fun r s => by
        funext a c
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t r => by
        funext a c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hL : ∀ r a c, L r a c = (∑ i, r i • b i) a c := by
    intro r a c
    simp [L, Matrix.sum_apply, Matrix.smul_apply]
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun r hr => ?_
    have hsum : ∑ i, r i • b i = 0 := by
      ext a c
      have h := congrFun (congrFun hr a) c
      rw [hL] at h
      simpa using h
    funext i
    exact Fintype.linearIndependent_iff.mp hli r hsum i
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨(d : ℝ) * K, by positivity, fun r => ?_⟩
  have h1 : ‖r‖ ≤ K * ‖L r‖ := by
    have h := hK.le_mul_dist r 0
    simpa [dist_zero_right] using h
  have hN : 0 ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ‖L r‖ ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun c => ?_
    rw [hL]
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    calc ‖(∑ i, r i • b i) a c‖ ≤ ∑ c', ‖(∑ i, r i • b i) a c'‖ :=
          Finset.single_le_sum (f := fun c' => ‖(∑ i, r i • b i) a c'‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
      _ ≤ ∑ a', ∑ c', ‖(∑ i, r i • b i) a' c'‖ :=
          Finset.single_le_sum (f := fun a' => ∑ c', ‖(∑ i, r i • b i) a' c'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h3 : ∑ i, |r i| ≤ d * ‖r‖ := by
    calc ∑ i, |r i| ≤ ∑ _i : Fin d, ‖r‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm r i
      _ = d * ‖r‖ := by simp
  calc ∑ i, |r i| ≤ d * ‖r‖ := h3
    _ ≤ d * (K * ‖L r‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ ≤ d * (K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 K.coe_nonneg) (Nat.cast_nonneg _)
    _ = d * K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBoundStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_coefficient_norm_bound : ∀ {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hli : LinearIndependent ℝ b), ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm <;> assumption)
end
end

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

theorem dRep_real_smul {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (r : ℝ) :
    dRep π (r • X) v = (r : ℂ) • dRep π X v := by
  have hrX : r • X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 r X hX
  have h1 := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hX).1
  have h2 := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hrX).1
  have h3 : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have h4 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v) (r • dRep π X v) 0 := by
    have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) (r * 0) := by
      simpa using h1
    exact HasDerivAt.scomp (0 : ℝ) h1' h3
  have h5 : (fun t : ℝ => π (NormedSpace.exp (t • (r • X))) v) = fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v := by
    funext t
    rw [smul_smul, mul_comm]
  rw [h5] at h2
  rw [h2.unique h4]
  exact (Complex.coe_smul r _).symm

theorem dRep_sum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (r : Fin d → ℝ) {w : H} (hw : IsSmoothVec G π w) :
    dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w := by
  have hl := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  have key : ∀ s : Finset (Fin d), (∑ i ∈ s, r i • b i ∈ HCSS.lieOf G) ∧
      dRep π (∑ i ∈ s, r i • b i) w = ∑ i ∈ s, (r i : ℂ) • dRep π (b i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · intro t
        simpa using hG.one_mem
      · simp [dRep]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hri := hl.2.1 (r i) _ (hb i)
      refine ⟨hl.1 _ _ hri ih.1, ?_⟩
      rw [(GlobalTheory.T.derived_action_additive hG hrep hw hw hri ih.1).1, ih.2, dRep_real_smul hG hrep hw (hb i)]
  exact (key Finset.univ).2

theorem word_bound_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v := by
  intro n G H _ _ _ π hG hrep _ hQ d b hb hli hsp Y _ hYs hYd v hv
  obtain ⟨Q, m, Mb, a, hm, hMb, ha, hadd, hsmul, hconj, hpos, hbd, hgrow⟩ := hQ
  obtain ⟨hsadd, hssmul, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  have hvs := hYs v hv
  let S : Submodule ℂ H :=
    { carrier := {x | IsSmoothVec G π x}
      add_mem' := fun {x y} hx hy => hsadd x y hx hy
      zero_mem' := by simpa using hssmul 0 v hvs
      smul_mem' := fun c x hx => hssmul c x hx }
  let Xf : Fin d → Module.End ℂ S := fun i =>
    { toFun := fun x => ⟨dRep π (b i) x, (GlobalTheory.T.derived_action_of_smooth_vector hG hrep x.2 (hb i)).2⟩
      map_add' := fun x y => Subtype.ext (GlobalTheory.T.derived_action_additive hG hrep x.2 y.2 (hb i) (hb i)).2.1
      map_smul' := fun c x => Subtype.ext ((GlobalTheory.T.derived_action_additive hG hrep x.2 x.2 (hb i) (hb i)).2.2 c) }
  have hXc : ∀ i (x : S), ((Xf i x : S) : H) = dRep π (b i) x := fun _ _ => rfl
  have hlie := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  choose r hr using fun (p : Fin d × Fin d) => hsp _ (hlie.2.2.1 (b p.1) (b p.2) (hb p.1) (hb p.2))
  have hcomm : ∀ i j, Xf i * Xf j - Xf j * Xf i = ∑ l, ((r (i, j) l : ℝ) : ℂ) • Xf l := by
    intro i j
    ext u
    have h1 := GlobalTheory.T.derived_action_commutator hG hrep u.2 (hb i) (hb j)
    rw [show b i * b j - b j * b i = _ from hr (i, j), dRep_sum hG hrep b hb _ u.2] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, hXc]
    exact h1.symm
  have hQnn : ∀ x : H, 0 ≤ (Q x x).re := fun x =>
    le_trans (by positivity) (hpos x)
  let A : ℝ := a * ∑ i, mnorm (b i)
  have hmn : ∀ X : Matrix (Fin n) (Fin n) ℂ, 0 ≤ mnorm X := fun X =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg ha (Finset.sum_nonneg fun i _ => hmn _)
  have hs : ∀ i (x : S), |2 * (Q (Xf i x) x).re| ≤ A * (Q x x).re := by
    intro i x
    refine (GlobalTheory.T.smooth_vector_hermitian_form_growth hG hrep Q Mb a hadd hsmul hconj hbd hgrow (hb i) x.2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hQnn x)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => mnorm (b i)) (fun i _ => hmn _) (Finset.mem_univ i)) ha
  let V : Submodule ℂ S := Y.comap S.subtype
  have hinj : Function.Injective (fun u : V => (⟨(u : S), u.2⟩ : Y)) := by
    intro u w h
    exact Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : H)) h))
  let f : V →ₗ[ℂ] Y :=
    { toFun := fun u => ⟨(u : S), u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ V := FiniteDimensional.of_injective f hinj
  have hV : ∀ u ∈ V, (∑ i, Xf i * Xf i) u ∈ V := by
    intro u hu
    have h1 := hYd (u : H) hu
    change (((∑ i, Xf i * Xf i) u : S) : H) ∈ Y
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, hXc] using h1
  obtain ⟨C, hC, hN⟩ := GlobalTheory.T.hermitian_form_lie_word_growth (fun x y : S => Q x y)
    (fun x y z => hadd x y z) (fun c x y => hsmul c x y) (fun x y => hconj x y)
    (fun x hx => lt_of_lt_of_le (by
      have : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
      positivity) (hpos x))
    Xf (fun i j l => ((r (i, j) l : ℝ) : ℂ)) hcomm A hA hs V hV
  have hword : ∀ (l : List (Fin d)) (u : S),
      (((l.map Xf).prod u : S) : H) = l.foldr (fun i w => dRep π (b i) w) (u : H) := by
    intro l u
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hXc, List.foldr_cons, ih]
  let vS : S := ⟨v, hvs⟩
  have hvV : vS ∈ V := hv
  let K : ℝ := Real.sqrt (Q v v).re / Real.sqrt m
  have hK : 0 ≤ K := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine GlobalTheory.T.lie_basis_coordinate_growth_bound hG hrep b hb hsp _ (GlobalTheory.T.linearIndependent_coefficient_norm_bound b hli).choose_spec.1 (GlobalTheory.T.linearIndependent_coefficient_norm_bound b hli).choose_spec.2
    (fun r w hw => dRep_sum hG hrep b hb r hw) hvs (C * (K + 1)) (by positivity) ?_
  intro l
  have h1 := hN l vS hvV
  rw [show ((l.map Xf).prod vS : S) = ((l.map Xf).prod vS : S) from rfl] at h1
  set w : S := (l.map Xf).prod vS with hw
  have hwv : (w : H) = l.foldr (fun i w => dRep π (b i) w) v := hword l vS
  rw [← hwv]
  have h2 : Real.sqrt m * ‖(w : H)‖ ≤ Real.sqrt (Q w w).re := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hm.le]
    exact hpos w
  have h3 : ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * K := by
    have h4 : Real.sqrt m * ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re := h2.trans h1
    have h5 : C ^ (l.length + 1) * l.length.factorial * K = (C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re) / Real.sqrt m := by
      simp only [K]; ring
    rw [h5, le_div_iff₀ hsm]
    linarith
  refine h3.trans ?_
  have h6 : K ≤ (K + 1) ^ (l.length + 1) := by
    have h7 : (K + 1) ^ 1 ≤ (K + 1) ^ (l.length + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  rw [mul_pow]
  have h8 : 0 ≤ C ^ (l.length + 1) * (l.length.factorial : ℝ) := by positivity
  calc C ^ (l.length + 1) * l.length.factorial * K ≤ C ^ (l.length + 1) * l.length.factorial * (K + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left h6 h8
    _ = C ^ (l.length + 1) * (K + 1) ^ (l.length + 1) * l.length.factorial := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

end
