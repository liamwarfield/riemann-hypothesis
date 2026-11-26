module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.RatExtend

variable {D : D7}

section Theta

variable {T : Tor D} {N N' : ℕ}

theorem Hf_add_left (x y w : VC D N N') : Hf D T (x + y) w = Hf D T x w + Hf D T y w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_smul_left (c : ℂ) (x w : VC D N N') : Hf D T (c • x) w = c * Hf D T x w := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_conj (x w : VC D N N') : Hf D T w x = (starRingEnd ℂ) (Hf D T x w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem Hf_nsmul_left (n : ℕ) (x w : VC D N N') : Hf D T (n • x) w = n * Hf D T x w := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]

theorem Hf_nsmul_right (n : ℕ) (x w : VC D N N') : Hf D T x (n • w) = n * Hf D T x w := by
  rw [Hf_conj, Hf_nsmul_left, map_mul, ← Hf_conj, map_natCast]

theorem Hf_diff (x : VC D N N') : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem Wd_diff (x : VC D N N') {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (Wd D T x F) := by
  have h := Hf_diff (T := T) x
  unfold Wd U
  fun_prop

theorem Wd_comm (a x : VC D N N') (m : ℤ) (h : (Hf D T a x).im = m) (F : VC D N N' → ℂ) :
    Wd D T a (Wd D T x F) = Wd D T x (Wd D T a F) := by
  funext z
  have h1 : Hf D T x a = Hf D T a x - 2 * m * Complex.I := by
    rw [Hf_conj a x]
    apply Complex.ext <;> simp [h]
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) a - (Real.pi : ℂ) * Hf D T a a / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + a) x - (Real.pi : ℂ) * Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    rw [Hf_add_left, Hf_add_left, h1]
    ring
  simp only [Wd, U]
  rw [add_right_comm z a x]
  linear_combination (-(wdPh D T a * wdPh D T x * F (z + x + a))) * h2

theorem Wd_add (x : VC D N N') (F G : VC D N N' → ℂ) : Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) : Wd D T x (c • F) = c • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem TT_add {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') : F + G ∈ TT D T N N' := by
  obtain ⟨d, m, hm, h⟩ := hF
  obtain ⟨d', m', hm', h'⟩ := hG
  refine ⟨d.add d', m * m', by positivity, fun x hx => ?_⟩
  rw [Wd_add]
  congr 1
  · rw [mul_nsmul']; exact h _ (nsmul_mem hx _)
  · rw [mul_nsmul]; exact h' _ (nsmul_mem hx _)

theorem TT_smul (c : ℂ) {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') : c • F ∈ TT D T N N' := by
  obtain ⟨d, m, hm, h⟩ := hF
  exact ⟨d.const_smul c, m, hm, fun x hx => by rw [Wd_smul, h x hx]⟩

theorem TT_zero : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

end Theta

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {κ : Type} (s : Finset κ) (r : κ → ℂ) (F : κ → VC D N N' → ℂ)
    (hF : ∀ i, F i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, r i • F i) ∈ TT D (tor0 D cc δ) N N' ∧
      W.Om g g' (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • W.Om g g' (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using TT_zero, ?_⟩
    have := W.smul g g' 0 0 TT_zero
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨TT_add (TT_smul _ (hF a)) ih.1, ?_⟩
    rw [W.add g g' _ (TT_smul _ (hF a)) _ ih.1, W.smul g g' _ _ (hF a), ih.2]

theorem exists_nsmul_mem {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) (δ : ℂ) {N N' : ℕ}
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ n : ℕ, 0 < n ∧ n • pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N' := by
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (MovedLattice.inverseHalfDifferent_ne_zero D)
  set b : D.host.E := algebraMap (𝓞 D.host.E) D.host.E a with hb
  have hb0 : b ≠ 0 := by
    rw [hb]; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ha0
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E)
    (Finset.univ.image fun p : Fin N' × Fin N => z p.1 p.2 / b)
  have hA : ∀ i j, IsIntegral ℤ (((y.natAbs * y.natAbs : ℕ) : D.host.E) * (z i j / b)) := by
    intro i j
    have h1 := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    have h2 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (y : D.host.E) * (y : D.host.E) := by
      rw [← Int.cast_natCast, Int.natAbs_mul_self, Int.cast_mul]
    rw [h2, mul_assoc]
    rw [zsmul_eq_mul] at h1
    exact (isIntegral_algebraMap (R := ℤ) (x := y)).mul h1
  set m : ℕ := y.natAbs * y.natAbs with hm
  have hm0 : 0 < m := by positivity
  have hn0 : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨Ideal.absNorm cc * m, by positivity, AddSubgroup.subset_closure
    ⟨δ * D.host.φ₀ ((((Ideal.absNorm cc : 𝓞 D.host.K) : D.host.K) : D.host.E)),
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, rfl⟩,
      b • Matrix.of (fun i j => (m : D.host.E) * (z i j / b)),
      Submodule.subset_span ⟨b, ha, _, Submodule.subset_span ?_, rfl⟩, ?_⟩⟩
  · intro x hx i _
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨_, hA i j⟩ : 𝓞 D.host.E) (hx j trivial)
  · funext τ i j
    have h1 : b * ((m : D.host.E) * (z i j / b)) = m * z i j := by field_simp
    simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, h1, map_mul,
      map_natCast, nsmul_eq_mul]
    simp
    ring

theorem emb_conj {a b : ℕ} (γ : Matrix (Fin a) (Fin b) D.host.E) (τ : D.what₂.Tau) :
    ((γ.map D.host.conj).transpose).map (embT D τ) = (γ.map (embT D τ)).conjTranspose := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  exact D.host.conjE_apply (embT D τ) (γ j i)

theorem Hf_eq_trace {T : Tor D} {N N' : ℕ} (z w : VC D N N') :
    Hf D T z w = (∑ τ, (Matrix.of (z τ) * (Matrix.of (w τ)).conjTranspose).trace) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

def subst {N N' : ℕ} (u : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (u' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ)
    (z : VC D N N') : VC D N N' :=
  fun τ => ((u' τ).conjTranspose * Matrix.of (z τ) * u τ : Matrix _ _ ℂ)

theorem Hf_subst {T : Tor D} {N N' : ℕ} {u : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ}
    {u' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ} (hu : ∀ τ, u τ * (u τ).conjTranspose = 1)
    (hu' : ∀ τ, u' τ * (u' τ).conjTranspose = 1) (z w : VC D N N') :
    Hf D T (subst u u' z) (subst u u' w) = Hf D T z w := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change (((u' τ).conjTranspose * Matrix.of (z τ) * u τ) *
    ((u' τ).conjTranspose * Matrix.of (w τ) * u τ).conjTranspose).trace = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (u τ), hu, Matrix.one_mul, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hu', Matrix.mul_one]

theorem subst_add {N N' : ℕ} (u : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (u' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (z w : VC D N N') :
    subst u u' (z + w) = subst u u' z + subst u u' w := by
  funext τ
  change ((u' τ).conjTranspose * (Matrix.of (z τ) + Matrix.of (w τ)) * u τ : Matrix _ _ ℂ) =
    (u' τ).conjTranspose * Matrix.of (z τ) * u τ + (u' τ).conjTranspose * Matrix.of (w τ) * u τ
  rw [Matrix.mul_add, Matrix.add_mul]

theorem pull_Wd {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {γ : Matrix (Fin N) (Fin N) D.host.E}
    {γ' : Matrix (Fin N') (Fin N') D.host.E} (h : γ * (γ.map D.host.conj).transpose = 1)
    (h' : γ' * (γ'.map D.host.conj).transpose = 1) (z : Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) =
      Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (γ' * z * (γ.map D.host.conj).transpose))
        (pull D (tor0 D cc δ) γ γ' G) := by
  have hu : ∀ τ, γ.map (embT D τ) * (γ.map (embT D τ)).conjTranspose = 1 := fun τ => by
    rw [← emb_conj, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hu' : ∀ τ, γ'.map (embT D τ) * (γ'.map (embT D τ)).conjTranspose = 1 := fun τ => by
    rw [← emb_conj, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : pt D (tor0 D cc δ) δ z = subst (fun τ => γ.map (embT D τ)) (fun τ => γ'.map (embT D τ))
      (pt D (tor0 D cc δ) δ (γ' * z * (γ.map D.host.conj).transpose)) := by
    funext τ
    change (δ • z.map (embT D τ) : Matrix _ _ ℂ) = (γ'.map (embT D τ)).conjTranspose *
      (δ • (γ' * z * (γ.map D.host.conj).transpose).map (embT D τ)) * γ.map (embT D τ)
    rw [Matrix.map_mul, Matrix.map_mul, emb_conj, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.1 (hu τ), Matrix.mul_one, ← Matrix.mul_assoc, mul_eq_one_comm.1 (hu' τ), Matrix.one_mul]
  generalize pt D (tor0 D cc δ) δ (γ' * z * (γ.map D.host.conj).transpose) = x at hx
  rw [hx]
  funext w
  change Wd D (tor0 D cc δ) _ G (subst (fun τ => γ.map (embT D τ)) (fun τ => γ'.map (embT D τ)) w) =
    wdPh D (tor0 D cc δ) x * (G (subst (fun τ => γ.map (embT D τ)) (fun τ => γ'.map (embT D τ)) (w + x)) * _)
  simp only [Wd, U, wdPh, qH, Hf_subst hu hu', subst_add]

theorem om_eq_pull_of_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), (∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) → ∀ (W : WeilO D cc δ N N' e0) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → (W.Om γA γA' e0 = fun z => a * pull D (tor0 D cc δ) γ γ' e0 z) → ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om γA γA' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z := by
  intro D cc δ hC N N' e0 he0 hspan W γA γA' γ γ' a hγ hγ' h0 F hF
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (La0 D (tor0 D cc δ) N N') (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) x e0 = e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  have hT : ∀ z, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 ∈ TT D (tor0 D cc δ) N N' := by
    intro z
    obtain ⟨Q, hQ, hz⟩ := exists_nsmul_mem hC.1.1 δ z
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ hz
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hu := (GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 γA γ hγ
  have hu' := (GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 γA' γ' hγ'
  have hinv : (((γA : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      ((γ.map D.host.conj).transpose).map (inc D) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [show ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = γ.map (inc D) from hγ,
      ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ z, W.Om γA γA' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0) =
      a • pull D (tor0 D cc δ) γ γ' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0) := by
    intro z
    obtain ⟨m, -, hl⟩ := W.lift γA γA' z e0 heT
    rw [hl (γ' * z * (γ.map D.host.conj).transpose), pull_Wd hu hu', ← Wd_smul, h0]
    · rfl
    · intro i j
      refine ⟨0, zero_mem _, ?_⟩
      rw [hinv, show ((γA' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) = γ'.map (inc D) from hγ',
        Matrix.map_mul, Matrix.map_mul, sub_self, mul_zero]
      rfl
  obtain ⟨k, r, z, rfl⟩ := hspan F hF
  rw [(Om_sum W γA γA' Finset.univ _ _ fun i => hT (z i)).2]
  funext w
  simp only [key, pull, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  erw [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

end GlobalTheory.NormSum.RatExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuumStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), (∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) → ∀ (W : WeilO D cc δ N N' e0) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → (W.Om γA γA' e0 = fun z => a * pull D (tor0 D cc δ) γ γ' e0 z) → ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om γA γA' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z := by
  first | exact @GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum | exact GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum | (intros; apply GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.WeilEquiv

theorem exists_common_den {R : Type} [CommRing R] (O : Subring R)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : R) * A i j ∈ O := by
  choose f hf hfO using hO
  refine ⟨∏ p : Fin a × Fin b, f (A p.1 p.2), Finset.prod_pos fun p _ => hf _, fun i j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
  exact O.mul_mem (natCast_mem O _) (hfO _)

theorem exists_close {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R)
    (hX : ∀ i j, (P * X * Q) i j ∈ I) (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      ∀ i j, (P * z.map ι * Q) i j ∈ I := by
  obtain ⟨n, hn, hP⟩ := exists_common_den O hO P
  obtain ⟨n', hn', hQ⟩ := exists_common_den O hO Q
  choose e t ht he using fun i j => hA (X i j) (m * n * n') (by positivity)
  refine ⟨Matrix.of e, fun i j => ⟨((n * n' : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩, fun i j => ?_⟩
  · simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
    push_cast; ring
  · have h1 : (Matrix.of e).map ι = X + Matrix.of fun i j => ((m * n * n' : ℕ) : R) * t i j := by
      ext i j
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, ← he]
      ring
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    refine I.add_mem (hX i j) ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((m * n * n' : ℕ) : R) * t r l) * Q l j =
        ((m : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)

theorem om_wd_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (k : GL (Fin N) (AE D)) L₁ → Moves D (k' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ x' ∈ La D (tor0 D cc δ) L₂ L₂', W.Om h h' (Wd D (tor0 D cc δ) x F) = Wd D (tor0 D cc δ) x' (W.Om h h' F) := by
  intro D hD cc δ hcc N N' e0 W h k h' k' L₁ L₂ L₁' L₂' h1 h1' h2 h2' x hx F hF
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hD cc δ hcc N N' k k' L₁ L₁' h1 h1' x hx
  obtain ⟨m, hm, hl⟩ := W.lift h h' z F hF
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  obtain ⟨z', hc, hz'⟩ := exists_close (inc D) (OhE D) (IhE D cc) hA hO hI
    (((h' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
    (((((h' * k' : GA D N') : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)))
    (((h * k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    (by
      intro i j
      refine Set.mem_of_eq_of_mem (congrFun (congrFun ?_ i) j) (hz i j)
      simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((h' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
        ← Matrix.mul_assoc (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
        Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]) m hm
  exact ⟨_, GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hD cc δ hcc N N' (h * k) (h' * k') L₂ L₂' h2 h2' z' hz', hl z' hc⟩

end GlobalTheory.WeilEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (k : GL (Fin N) (AE D)) L₁ → Moves D (k' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ x' ∈ La D (tor0 D cc δ) L₂ L₂', W.Om h h' (Wd D (tor0 D cc δ) x F) = Wd D (tor0 D cc δ) x' (W.Om h h' F) := by
  first | exact @GlobalTheory.WeilEquiv.om_wd_moved | exact GlobalTheory.WeilEquiv.om_wd_moved | (intros; apply GlobalTheory.WeilEquiv.om_wd_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.KerSum

theorem exists_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => H u v)
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, LinearMap.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul])
  let B' : V →L[ℝ] V →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ B)
  exact ⟨‖B'‖, norm_nonneg _, fun u v => B'.le_opNorm₂ u v⟩

theorem norm_kerTerm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : Sesq V) {M R : ℝ} (hM : 0 ≤ M) (hB : ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖) (x w z : V)
    (hw : ‖w‖ ≤ R) :
    ‖kerTerm H x w z‖ ≤ Real.exp (π * (M * R * ‖z‖)) *
      Real.exp (-(π / 2) * (H x x).re + (π * (M * ‖z‖ + M * R)) * ‖x‖) := by
  rw [kerTerm, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have h1 : (H w z).re ≤ M * R * ‖z‖ :=
    ((Complex.re_le_norm _).trans (hB w z)).trans (by gcongr)
  have h2 : (H x z).re ≤ M * ‖x‖ * ‖z‖ := (Complex.re_le_norm _).trans (hB x z)
  have h3 : -(H w x).re ≤ M * R * ‖x‖ :=
    (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hB w x)).trans (by gcongr)
  have e : ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2).re
      = π * ((H w z).re + (H x z).re + -(H w x).re) - π / 2 * (H x x).re := by
    simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) Real.pi_pos.le
  linarith

theorem differentiable_kerTerm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (H : Sesq V) (x z : V) :
    Differentiable ℂ (fun w => kerTerm H x w z) := by
  have h : ∀ v, Differentiable ℂ (fun w => H w v) := fun v =>
    (LinearMap.toContinuousLinearMap (H.flip v)).differentiable
  have e : (fun w => kerTerm H x w z) = fun w =>
      cexp ((π : ℂ) * (H w z + H x z) - (π : ℂ) * H w x - (π : ℂ) * H x x / 2) := by
    funext w; simp [kerTerm]
  rw [e]
  exact (((((h z).add_const _).const_mul _).sub ((h x).const_mul _)).sub_const _).cexp

theorem kerTerm_shift {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ z w, H z w = conj (H w z)) (x y w z : V) :
    kerTerm H x (w + y) z * cexp (-(π : ℂ) * H w y - (π : ℂ) * H y y / 2)
      = cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) * kerTerm H (y + x) w z := by
  have h : I * ((H y x).im : ℂ) = (H y x - H x y) / 2 := by
    rw [hH x y, Complex.sub_conj]; push_cast; ring
  rw [kerTerm, kerTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add (f := _), LinearMap.add_apply]
  linear_combination (π : ℂ) * h

theorem kerSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  intro V _ _ _ H hH Λ _ α hα
  obtain ⟨M, hM, hB⟩ := exists_bound H
  have hn : ∀ x : Λ, ‖α x‖ = 1 := fun x => by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have key : ∀ (z : V) (R : ℝ), ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (w : V), ‖w‖ ≤ R → ‖α x * kerTerm H x w z‖ ≤ u x := fun z R =>
    ⟨_, (GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * (M * ‖z‖ + M * R))).mul_left (Real.exp (π * (M * R * ‖z‖))),
      fun x w hw => by
        rw [norm_mul, hn, one_mul]
        exact norm_kerTerm_le H hM hB x w z hw⟩
  refine ⟨fun w z => ?_, fun z => ?_, fun z y hy w => ?_⟩
  · obtain ⟨u, hu, h⟩ := key z ‖w‖
    exact Summable.of_norm_bounded hu fun x => h x w le_rfl
  · refine differentiableOn_univ.1 (GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal isOpen_univ
      (F := fun (x : Λ) w => α x * kerTerm H x w z)
      (fun x => ((differentiable_kerTerm H x z).const_mul _).differentiableOn) fun w _ => ?_)
    obtain ⟨u, hu, h⟩ := key z (‖w‖ + 1)
    refine ⟨Metric.ball w 1, Metric.ball_mem_nhds w one_pos, u, hu, fun x v hv => h x v ?_⟩
    have := norm_le_norm_add_norm_sub' v w
    rw [mem_ball_iff_norm] at hv
    linarith
  · simp only [Heisenberg₂, kerSum]
    rw [← tsum_mul_right, ← tsum_mul_left,
      ← (Equiv.addLeft (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α x * kerTerm H x w z)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addLeft, AddSubgroup.coe_add]
    rw [hα.2.2 y hy x x.2, mul_assoc (α x), kerTerm_shift H hH.1]
    ring

end GlobalTheory.UnitaryTheta.KerSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpecStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergReproducingKernelSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  first | exact @GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | exact GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | (intros; apply GlobalTheory.UnitaryTheta.KerSum.kerSum_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLattices
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaStab

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  exact h2 ▸ (h1 1).1

theorem mem_standardThetaLattice_iff_adelicIdeal (hcc : cc ≠ ⊥) (x : VC D N N') : x ∈ La0 D (tor0 D cc δ) N N' ↔
    ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, inc D (z i j) ∈ IhE D cc := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hx
    obtain ⟨z, hz, h⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') x hx
    exact ⟨z, hz, fun i j => by simpa using h i j⟩
  · rintro ⟨z, rfl, h⟩
    exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') z (fun i j => by simpa using h i j)

theorem inc_mem_of_isIntegral {e : D.host.E} (he : IsIntegral ℤ e) : inc D e ∈ OhE D :=
  GlobalTheory.NormSum.MovedTheta.inc_int (⟨e, he⟩ : 𝓞 D.host.E)

theorem mulV_mem (hcc : cc ≠ ⊥) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (h' : ∀ i j, IsIntegral ℤ (M' i j)) (h : ∀ i j, IsIntegral ℤ (M i j)) (x : VC D N N')
    (hx : x ∈ La0 D (tor0 D cc δ) N N') : mulV D M' M x ∈ La0 D (tor0 D cc δ) N N' := by
  obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
  refine (mem_standardThetaLattice_iff_adelicIdeal hcc _).2 ⟨_, mulV_pt D cc δ M' M z, fun i j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun k _ => ?_
  rw [mul_comm]
  refine MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h k j)) (sum_mem fun l _ => ?_)
  exact MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h' i l)) (hz l k)

theorem exists_denom {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, IsIntegral ℤ ((m • M) i j) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin n × Fin n => M p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
  have h1 := h (M i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, ← natCast_zsmul]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h1
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', neg_smul]; exact h1.neg

theorem mulV_nsmul (m' m : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (x : VC D N N') : mulV D (m' • M') (m • M) x = (m' * m) • mulV D M' M x := by
  funext τ
  have e : ∀ {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) D.host.E),
      (k • A).map (embT D τ) = k • A.map (embT D τ) := by
    intro n k A
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]
  change (m' • M').map (embT D τ) * Matrix.of (x τ) * (m • M).map (embT D τ) =
    (m' * m) • (M'.map (embT D τ) * Matrix.of (x τ) * M.map (embT D τ))
  rw [e, e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, mul_smul]

theorem inv_eq_adj {n : ℕ} {g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    (((g : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = (adj D γ).map (inc D) := by
  have h1 : γ * adj D γ = 1 := (GlobalTheory.NormSum.mem_ratG_intG D n).2.2.2.1 g γ h
  apply Units.inv_eq_of_mul_eq_one_right
  unfold IsRat at h
  rw [h, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_iff_moved (hcc : cc ≠ ⊥) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : IsRat D (γA : GL (Fin N) (AE D)) γ)
    (h' : IsRat D (γA' : GL (Fin N') (AE D)) γ') (hL : Moves D (γA : GL (Fin N) (AE D)) L₁)
    (hL' : Moves D (γA' : GL (Fin N') (AE D)) L₁') (x : VC D N N') :
    x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have h1 : adj D γ * γ = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 γA γ h)
  have h1' : adj D γ' * γ' = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 γA' γ' h')
  have key : ∀ z : Matrix (Fin N') (Fin N) D.host.E,
      (((γA' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = (adj D γ' * z * γ).map (inc D) := by
    intro z
    have h2 := h
    unfold IsRat at h2
    rw [inv_eq_adj h', h2, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro hx
    obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
    rw [mulV_pt]
    refine GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' γA γA' _ _ hL hL' _ fun i j => ?_
    have e : adj D γ' * (γ' * z * adj D γ) * γ = z := by
      rw [Matrix.mul_assoc γ', ← Matrix.mul_assoc (adj D γ'), h1', Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rw [key, e]
    exact hz i j
  · intro hx
    obtain ⟨w, hw, hz⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' γA γA' _ _ hL hL' _ hx
    refine (mem_standardThetaLattice_iff_adelicIdeal hcc x).2 ⟨adj D γ' * w * γ, ?_, fun i j => ?_⟩
    · rw [← mulV_pt, ← hw, mulV_mulV, h1, h1', mulV_one]
    · have := hz i j
      rw [key] at this
      exact this

end GlobalTheory.ThetaStab


open GlobalTheory.ThetaStab in
theorem GlobalTheory.ThetaStab.mulV_theta_lattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  refine ⟨fun M' M h' h x hx => mulV_mem hcc M' M h' h x hx, fun M' M => ?_,
    fun γA γA' γ γ' L₁ L₁' h h' hL hL' x => mem_iff_moved hcc γA γA' γ γ' L₁ L₁' h h' hL hL' x⟩
  obtain ⟨m', hm', h'⟩ := exists_denom M'
  obtain ⟨m, hm, h⟩ := exists_denom M
  refine ⟨m' * m, Nat.mul_pos hm' hm, fun x hx => ?_⟩
  rw [← mulV_nsmul]
  exact mulV_mem hcc _ _ h' h x hx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLatticesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrixMul_thetaLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.ThetaStab.mulV_theta_lattices | exact GlobalTheory.ThetaStab.mulV_theta_lattices | (intros; apply GlobalTheory.ThetaStab.mulV_theta_lattices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaled
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.IdealGenerator

theorem coe_ideal_mul {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (I : FractionalIdeal R⁰ K) :
    (((P : FractionalIdeal R⁰ K) * I : FractionalIdeal R⁰ K) : Submodule R K) = P • (I : Submodule R K) := by
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨p, hp, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hm
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hp hn
  · rw [Submodule.smul_le]
    intro p hp n hn
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ((IsLocalization.mem_coeSubmodule _ _).2 ⟨p, hp, rfl⟩) hn

theorem exists_gen {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), ∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K) := by
  have hle : (P : FractionalIdeal R⁰ K) * I ≤ I := by
    calc (P : FractionalIdeal R⁰ K) * I ≤ 1 * I := by
          gcongr; exact FractionalIdeal.coeIdeal_le_one
      _ = I := one_mul I
  have hne : (P : FractionalIdeal R⁰ K) * I ≠ I := by
    intro h
    have h1 : (P : FractionalIdeal R⁰ K) = 1 := mul_right_cancel₀ hI (by rw [h, one_mul])
    exact hP.ne_top (by simpa using (FractionalIdeal.coeIdeal_eq_one.1 h1))
  obtain ⟨t₀, ht₀, ht₀'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  refine ⟨t₀, ht₀, ?_⟩
  set S : FractionalIdeal R⁰ K := FractionalIdeal.spanSingleton R⁰ t₀ + (P : FractionalIdeal R⁰ K) * I with hS
  have hSle : S ≤ I := by
    rw [hS, ← FractionalIdeal.sup_eq_add]
    exact sup_le (FractionalIdeal.spanSingleton_le_iff_mem.2 ht₀) hle
  have hPS : (P : FractionalIdeal R⁰ K) * I ≤ S := by
    rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
  have hJ : S * I⁻¹ ≤ 1 := by
    calc S * I⁻¹ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  obtain ⟨J, hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ
  have hSJ : S = (J : FractionalIdeal R⁰ K) * I := by
    rw [hJ', mul_assoc, inv_mul_cancel₀ hI, mul_one]
  have hPJ : P ≤ J := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K, hJ']
    calc (P : FractionalIdeal R⁰ K) = (P * I) * I⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ S * I⁻¹ := by gcongr
  have hJt : J = ⊤ := by
    by_contra h
    have hPJ' := hP.eq_of_le h hPJ
    apply ht₀'
    rw [hPJ', ← hSJ]
    have : FractionalIdeal.spanSingleton R⁰ t₀ ≤ S := by
      rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact this (FractionalIdeal.mem_spanSingleton_self _ _)
  have hSI : S = I := by rw [hSJ, hJt, FractionalIdeal.coeIdeal_top, one_mul]
  intro t ht
  have ht' : t ∈ (S : Submodule R K) := by rw [hSI]; exact ht
  rw [hS, FractionalIdeal.coe_add, coe_ideal_mul, FractionalIdeal.coe_spanSingleton, Submodule.add_eq_sup,
    Submodule.mem_sup] at ht'
  obtain ⟨y, hy, z, hz, rfl⟩ := ht'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact ⟨a, by simpa using hz⟩

theorem mem_range_of_mul_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : K)
    (h : ∀ t ∈ (I : Submodule R K), x * t ∈ (I : Submodule R K)) : x ∈ (algebraMap R K).range := by
  have h1 : FractionalIdeal.spanSingleton R⁰ x * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.2 h
  have h2 : FractionalIdeal.spanSingleton R⁰ x ≤ 1 := by
    calc FractionalIdeal.spanSingleton R⁰ x = (FractionalIdeal.spanSingleton R⁰ x * I) * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.spanSingleton_le_iff_mem.1 h2)

theorem exists_gen_and {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), (∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K)) ∧
      ∀ θ : K, θ ∉ (algebraMap R K).range → (∀ p ∈ P, p • θ ∈ (algebraMap R K).range) →
        ∀ a : R, a • (t₀ * θ) ∈ (I : Submodule R K) → a ∈ P := by
  obtain ⟨t₀, ht₀, hgen⟩ := exists_gen P hP I hI
  refine ⟨t₀, ht₀, hgen, fun θ hθ hPθ a ha => ?_⟩
  by_contra haP
  have hθP : ∀ z ∈ P • (I : Submodule R K), θ * z ∈ (I : Submodule R K) := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun p hp n hn => ?_) (fun x y hx hy => ?_)
    · obtain ⟨q, hq⟩ := hPθ p hp
      have : θ * p • n = q • n := by
        rw [Algebra.smul_def q, hq, smul_mul_assoc, mul_smul_comm]
      rw [this]; exact Submodule.smul_mem _ _ hn
    · rw [mul_add]; exact add_mem hx hy
  have haθ : a • θ ∈ (algebraMap R K).range := by
    refine mem_range_of_mul_mem I hI _ fun t ht => ?_
    obtain ⟨b, hb⟩ := hgen t ht
    have : a • θ * t = a • (θ * (t - b • t₀)) + b • (a • (t₀ * θ)) := by
      simp only [Algebra.smul_def]; ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (hθP _ hb)) (Submodule.smul_mem _ _ ha)
  obtain ⟨u, p, hp, hup⟩ := hP.exists_inv haP
  apply hθ
  have : θ = algebraMap R K u * (a • θ) + p • θ := by
    rw [← Algebra.smul_def, smul_smul, ← add_smul, hup, one_smul]
  rw [this]
  exact add_mem (mul_mem ⟨u, rfl⟩ haθ) (hPθ p hp)

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  unfold Formalism.BasicNotions.Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)

theorem isFractional_Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : IsFractional (𝓞 D.host.E)⁰ (Iid D cc) := by
  obtain ⟨d, hd, hd'⟩ := D.host.AA0.isFractional
  refine (FractionalIdeal.isFractional_span_iff).2 ⟨d, hd, ?_⟩
  rintro _ ⟨c, -, a, ha, rfl⟩
  rw [← mul_smul_comm]
  refine IsLocalization.isInteger_mul ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩ (hd' a ha)

theorem Iid_ne_bot (D : D7) (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) : Iid D cc ≠ ⊥ := by
  obtain ⟨c, hcc, hc0⟩ := (Submodule.ne_bot_iff _).1 hc
  have hA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    inverseHalfDifferent_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hA
  refine (Submodule.ne_bot_iff _).2 ⟨_, Submodule.subset_span ⟨c, hcc, a, ha, rfl⟩, mul_ne_zero ?_ ha0⟩
  intro h
  apply hc0
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem exists_generator_Iid : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t₀ ∈ Iid D cc, (∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) ∧ ∀ θ : D.host.E, ¬ IntE D θ → (∀ p ∈ P, IntE D (p • θ)) → ∀ a : 𝓞 D.host.E, a • (t₀ * θ) ∈ Iid D cc → a ∈ P := by
  intro D cc hc P hP
  exact exists_gen_and P hP ⟨Iid D cc, isFractional_Iid D cc⟩
    (fun h => Iid_ne_bot D cc hc (FractionalIdeal.coeToSubmodule_eq_bot.2 h))

end GlobalTheory.IdealGenerator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaledStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_cmDifferentIdealScaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t₀ ∈ Iid D cc, (∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) ∧ ∀ θ : D.host.E, ¬ IntE D θ → (∀ p ∈ P, IntE D (p • θ)) → ∀ a : 𝓞 D.host.E, a • (t₀ * θ) ∈ Iid D cc → a ∈ P := by
  first | exact @GlobalTheory.IdealGenerator.exists_generator_Iid | exact GlobalTheory.IdealGenerator.exists_generator_Iid | (intros; apply GlobalTheory.IdealGenerator.exists_generator_Iid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulByIntegralIsClosed
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory


open Formalism.MainNotions.GL3Theta in
theorem mulBy_integral_isClosed : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsClosed {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} := by
  intro p _ g
  set L : MvPowerSeries Unit ℂ_[p] := g.lg (GL3Theta.Xv ()) with hLdef
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by
    rw [hLdef, GL3Theta.G1.lg]
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _
      (GlobalTheory.GenusOneDatum.constantCoeff_flog _ _)
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have key : ∀ e : Unit →₀ ℕ, ∃ S : Finset ℕ, ∀ c : ℂ_[p],
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
        ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
    intro e
    have hfin := PowerSeries.coeff_subst_finite hL (PowerSeries.mk fun _ => (1 : ℂ_[p])) e
    have hfin' : (Function.support fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.mk fun _ => (1 : ℂ_[p])) • MvPowerSeries.coeff e (L ^ d)).Finite := hfin
    refine ⟨hfin'.toFinset, fun c => ?_⟩
    have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * L) = 0 := by
      simp [hL0]
    have ha : PowerSeries.HasSubst (MvPowerSeries.C c * L) :=
      PowerSeries.HasSubst.of_constantCoeff_zero ha0
    show MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.C c * L) g.ex) = _
    rw [PowerSeries.coeff_subst ha]
    have hterm : ∀ d : ℕ, PowerSeries.coeff d g.ex • MvPowerSeries.coeff e ((MvPowerSeries.C c * L) ^ d) =
        PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
      intro d
      rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, smul_eq_mul]
    simp_rw [hterm]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hd
    simp only [PowerSeries.coeff_mk, one_smul] at h0
    rw [h0, mul_zero, mul_zero]
  have hset : {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} =
      ⋂ e : Unit →₀ ℕ, {c : ℂ_[p] |
        ‖MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])‖ ≤ 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [hset]
  refine isClosed_iInter fun e => ?_
  obtain ⟨S, hS⟩ := key e
  have hfun : (fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])) =
      fun c => ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) :=
    funext hS
  have hcont : Continuous fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    rw [hfun]
    fun_prop
  exact isClosed_le (continuous_norm.comp hcont) continuous_const

end GlobalTheory
end
