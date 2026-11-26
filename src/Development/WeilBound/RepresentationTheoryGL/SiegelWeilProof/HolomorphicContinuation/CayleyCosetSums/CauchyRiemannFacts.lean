module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveGR

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicSectionLoweringInvariant
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DifferentiableAtFirstCayleyBlock
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_function_eq_weighted (m : ℕ) (e : ℤ) (y : GR n) : F0 m 0 e y = holomorphicScalarSection m e (mR y) := by
  simp [F0, f0, holomorphicScalarSection]

def Nm (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂

def Nm' (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂

private theorem Cm_mul_Cmi_eq_one : Cm n * Cmi n = 1 := by
  simp only [Cm, Cmi, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

private theorem Cm_inv_eq_Cmi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi_eq_one

private theorem Cmi_mul_Cm_eq_one : Cmi n * Cm n = 1 := by
  rw [← Cm_inv_eq_Cmi]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse Cm_mul_Cmi_eq_one)

private theorem u1_eq_mul_Cm_toBlocks₂₁ (g : M2 n) : u1 g = (g * Cm n).toBlocks₂₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u1, Cm, Matrix.fromBlocks_multiply]

private theorem u2_eq_mul_Cm_toBlocks₂₂ (g : M2 n) : u2 g = (g * Cm n).toBlocks₂₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u2, Cm, Matrix.fromBlocks_multiply]

private theorem Nm_eq_mul_Cm_toBlocks₁₁ (g : M2 n) : Nm g = (g * Cm n).toBlocks₁₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm, Cm, Matrix.fromBlocks_multiply]

private theorem Nm'_eq_mul_Cm_toBlocks₁₂ (g : M2 n) : Nm' g = (g * Cm n).toBlocks₁₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm', Cm, Matrix.fromBlocks_multiply]

private theorem toBlocks11_mul_fromBlocks (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₁₁ = A.toBlocks₁₁ * P + A.toBlocks₁₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_fromBlocks_toBlocks₂₁ (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₂₁ = A.toBlocks₂₁ * P + A.toBlocks₂₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    x * mX P Q R S * Cm n = x * Cm n * fromBlocks P Q R S := by
  simp only [mX, Cm_inv_eq_Cmi, Matrix.mul_assoc, Cmi_mul_Cm_eq_one, Matrix.mul_one]

theorem zOfE_eq (x : M2 n) : zOfE x = Nm x * (u1 x)⁻¹ := rfl

theorem first_cayley_block_mul_block (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX P Q R S) = u1 x * P + u2 x * R := by
  rw [u1_eq_mul_Cm_toBlocks₂₁, u1_eq_mul_Cm_toBlocks₂₁, u2_eq_mul_Cm_toBlocks₂₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, mul_fromBlocks_toBlocks₂₁]

theorem Nm_mX (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    Nm (x * mX P Q R S) = Nm x * P + Nm' x * R := by
  rw [Nm_eq_mul_Cm_toBlocks₁₁, Nm_eq_mul_Cm_toBlocks₁₁, Nm'_eq_mul_Cm_toBlocks₁₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, toBlocks11_mul_fromBlocks]

theorem da_entry (i j : Fin n ⊕ Fin n) (x : M2 n) : DifferentiableAt ℂ (fun y : M2 n => y i j) x := by
  exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_id (x := x)) i) j

theorem da_matrix {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n}
    (h : ∀ i j, DifferentiableAt ℂ (fun y => f y i j) x) : DifferentiableAt ℂ f x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j
  exact h1

theorem da_apply {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (h : DifferentiableAt ℂ f x) (i j : Fin n) :
    DifferentiableAt ℂ (fun y => f y i j) x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x := h
  exact differentiableAt_pi.1 (differentiableAt_pi.1 h1 i) j

theorem da_mul {f g : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) : DifferentiableAt ℂ (fun y => f y * g y) x := by
  refine da_matrix fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (da_apply hf i k).mul (da_apply hg k j)

theorem differentiableAt_first_cayley_block (x : M2 n) : DifferentiableAt ℂ u1 x := by
  refine da_matrix fun i j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

theorem da_Nm (x : M2 n) : DifferentiableAt ℂ Nm x := by
  refine da_matrix fun i j => ?_
  simp only [Nm, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

private theorem differentiableAt_det_of_differentiableAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] {f : M2 n → Matrix ι ι ℂ}
    {x : M2 n} (hf : ∀ a b, DifferentiableAt ℂ (fun y => f y a b) x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  have hp : ∀ (s : Finset ι) (σ : Equiv.Perm ι),
      DifferentiableAt ℂ (fun y => ∏ i ∈ s, f y (σ i) i) x := by
    intro s σ
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (hf _ _).mul ih
  have e : (fun y => (f y).det) =
      fun y => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  exact DifferentiableAt.fun_sum fun σ _ => (hp _ σ).const_mul _

theorem da_det {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  exact differentiableAt_det_of_differentiableAt_entries (da_apply hf)

theorem da_inv {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) (h : (f x).det ≠ 0) :
    DifferentiableAt ℂ (fun y => (f y)⁻¹) x := by
  have hadj : ∀ i j, DifferentiableAt ℂ (fun y => (f y).adjugate i j) x := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det_of_differentiableAt_entries fun a b => ?_
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp only [hab, if_true]
      exact differentiableAt_const _
    · simp only [hab, if_false]
      exact da_apply hf a b
  have hd : DifferentiableAt ℂ (fun y => ((f y).det)⁻¹) x := (differentiableAt_det_of_differentiableAt_entries (da_apply hf)).inv h
  refine da_matrix fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (hadj i j)

theorem da_zOfE (x : M2 n) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ zOfE x := by
  have e : zOfE = fun y : M2 n => Nm y * (u1 y)⁻¹ := funext zOfE_eq
  rw [e]
  exact da_mul (da_Nm x) (da_inv (differentiableAt_first_cayley_block x) h)

theorem da_F0E (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ (holomorphicScalarSection m e) x := by
  show DifferentiableAt ℂ (fun y : M2 n => y.det ^ e * (u1 y).det ^ (-(m : ℤ))) x
  exact ((differentiableAt_det_of_differentiableAt_entries (f := fun y => y) fun a b => da_entry a b x).zpow (Or.inl h0)).mul
    ((da_det (differentiableAt_first_cayley_block x)).zpow (Or.inl h))

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Cm n * fromBlocks 0 Q 0 0 * Cmi n := by
  have h1 : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q 0 1 : M2 n) = 1 + fromBlocks 0 Q 0 0 := by
    rw [← fromBlocks_one, fromBlocks_add]; simp
  rw [lowQ, mX, h1, cm_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, add_sub_cancel_left]

theorem lowQ_smul (c : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ (c • Q) = c • lowQ Q := by
  rw [lowQ_eq, lowQ_eq, show (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) 0 0 : M2 n) = c • fromBlocks 0 Q 0 0 by
    rw [fromBlocks_smul]; simp]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q 0 1 = 1 + lowQ Q := by
  rw [lowQ]; abel

theorem det_mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : (mX 1 Q 0 1 : M2 n).det = 1 := by
  simp only [mX, Cm_inv_eq_Cmi]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, mul_one]
  rw [← Matrix.det_mul, Cm_mul_Cmi_eq_one, Matrix.det_one]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fderiv_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : M2 n → E} {x : M2 n}
    (hf : DifferentiableAt ℂ f x) (v : M2 n) (hc : ∀ τ : ℂ, f (x + τ • v) = f x) : fderiv ℂ f x v = 0 := by
  have hl : HasDerivAt (fun τ : ℂ => x + τ • v) v 0 :=
    (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x).congr_deriv (one_smul ℂ v)
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hl (by simp)
  have h2 : HasDerivAt (f ∘ fun τ : ℂ => x + τ • v) 0 0 := by
    have e : (f ∘ fun τ : ℂ => x + τ • v) = fun _ => f x := funext fun τ => hc τ
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem line_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * lowQ Q) = x * mX 1 (τ • Q) 0 1 := by
  rw [mX_low, lowQ_smul, mul_add, mul_one, Matrix.mul_smul]

theorem zOfE_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : zOfE (x * mX 1 Q 0 1) = zOfE x := by
  rw [zOfE_eq, zOfE_eq, first_cayley_block_mul_block, Nm_mX]; simp

theorem holomorphic_section_lowering_invariant (m : ℕ) (e : ℤ) (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : holomorphicScalarSection m e (x * mX 1 Q 0 1) = holomorphicScalarSection m e x := by
  unfold holomorphicScalarSection
  simp only [Matrix.det_mul, det_mX_low, first_cayley_block_mul_block, mul_one, mul_zero, add_zero]

theorem fderiv_zOfE_low (x : M2 n) (h : (u1 x).det ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_zOfE x h) _ fun τ => by rw [line_low, zOfE_low]

theorem fderiv_F0E_low (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0)
    (Q : Matrix (Fin n) (Fin n) ℂ) : fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_F0E m e x h0 h) _ fun τ => by rw [line_low, holomorphic_section_lowering_invariant]

theorem low_blocks (R : Matrix (Fin n) (Fin n) ℂ) :
    lowQ R = fromBlocks ((-1 / 2 : ℂ) • R) ((Complex.I / 2) • R) ((Complex.I / 2) • R) ((1 / 2 : ℂ) • R) := by
  rw [lowQ_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

def raiseR (S : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 0 S 1 - 1

private theorem Cm_mul_Cmi : Cm n * Cmi n = 1 := by
  unfold Cm Cmi
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem raise_eq (S : Matrix (Fin n) (Fin n) ℂ) : raiseR S = Cm n * fromBlocks 0 0 S 0 * Cmi n := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi
  have hb : (fromBlocks 1 0 S 1 : M2 n) = fromBlocks 0 0 S 0 + 1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp
  unfold raiseR mX
  rw [hinv, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Cm_mul_Cmi, add_sub_cancel_right]

theorem raise_blocks (S : Matrix (Fin n) (Fin n) ℂ) :
    raiseR S = fromBlocks ((-1 / 2 : ℂ) • S) ((-Complex.I / 2) • S) ((-Complex.I / 2) • S) ((1 / 2 : ℂ) • S) := by
  rw [raise_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem sig_fromBlocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    sig (fromBlocks A B C D) = fromBlocks (-Dᴴ) Bᴴ Cᴴ (-Aᴴ) := by
  rw [sig_eq]
  unfold JJ
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem sig_low (R : Matrix (Fin n) (Fin n) ℂ) : sig (lowQ R) = raiseR Rᴴ := by
  rw [low_blocks, raise_blocks, sig_fromBlocks]
  simp only [Matrix.conjTranspose_smul]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply] <;> ring_nf <;> simp [Complex.conj_I] <;> ring_nf

theorem raiseR_smul (c : ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : raiseR (c • S) = c • raiseR S := by
  rw [raise_blocks, raise_blocks, Matrix.fromBlocks_smul]
  congr 1 <;> exact smul_comm _ _ _

theorem line_raise (x : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * raiseR S) = x * mX 1 0 (τ • S) 1 := by
  have : mX 1 0 (τ • S) 1 = 1 + raiseR (τ • S) := by rw [raiseR]; abel
  rw [this, raiseR_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_matrix_mul {A B : ℂ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  have hA' : HasDerivAt (fun τ => (A τ : Fin n → Fin n → ℂ)) (A' : Fin n → Fin n → ℂ) 0 := hA
  have hB' : HasDerivAt (fun τ => (B τ : Fin n → Fin n → ℂ)) (B' : Fin n → Fin n → ℂ) 0 := hB
  have h : HasDerivAt (fun τ => ((A τ * B τ : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ))
      ((A' * B 0 + A 0 * B' : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.mul_apply, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun k _ => ?_
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA' i) k).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB' k) j)
  exact h

theorem fderiv_zOfE_raise (x : M2 n) (h : (u1 x).det ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * raiseR S) = WM x * S * (u1 x)⁻¹ := by
  let v := x * raiseR S
  have hl := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hg := (da_zOfE x h).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  simp only [id_eq, one_smul, Function.comp_def] at hg
  have hu : ∀ τ : ℂ, u1 (x + τ • v) = u1 x + τ • (u2 x * S) := fun τ => by
    rw [line_raise, first_cayley_block_mul_block, Matrix.mul_one, Matrix.mul_smul]
  have hN : ∀ τ : ℂ, Nm (x + τ • v) = Nm x + τ • (Nm' x * S) := fun τ => by
    rw [line_raise, Nm_mX, Matrix.mul_one, Matrix.mul_smul]
  have hc : Continuous fun τ : ℂ => (u1 x + τ • (u2 x * S)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), (u1 x + τ • (u2 x * S)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using h)
  have hB := ((hasDerivAt_id (0 : ℂ)).smul_const (u2 x * S)).const_add (u1 x)
  simp only [id_eq, one_smul] at hB
  have hL := hasDerivAt_matrix_mul hg hB
  have hR := ((hasDerivAt_id (0 : ℂ)).smul_const (Nm' x * S)).const_add (Nm x)
  simp only [id_eq, one_smul] at hR
  have heq : (fun τ : ℂ => zOfE (x + τ • v) * (u1 x + τ • (u2 x * S))) =ᶠ[𝓝 0]
      fun τ => Nm x + τ • (Nm' x * S) := by
    filter_upwards [hev] with τ hτ
    rw [← hu, zOfE_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (by rwa [hu])), Matrix.mul_one, hN]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero] at hfin
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have key : fderiv ℂ zOfE x v * u1 x = WM x * S := by
    refine (eq_sub_of_add_eq hfin).trans ?_
    rw [WM, show (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) = Nm' x from rfl, Matrix.sub_mul, Matrix.mul_assoc (zOfE x)]
  calc fderiv ℂ zOfE x v = fderiv ℂ zOfE x v * u1 x * (u1 x)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
    _ = WM x * S * (u1 x)⁻¹ := congrArg (fun M => M * (u1 x)⁻¹) key

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₁₂_mul' (A B : M2 n) :
    (A * B).toBlocks₁₂ = A.toBlocks₁₁ * B.toBlocks₁₂ + A.toBlocks₁₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Nm x := by
  simp [toBlocks₁₁_mul', Cm, Nm, Matrix.mul_smul]

theorem mul_cm₁₂ (x : M2 n) : (x * Cm n).toBlocks₁₂ = Nm' x := by
  simp [toBlocks₁₂_mul', Cm, Nm', Matrix.mul_smul, Matrix.mul_neg]

theorem det_ne_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    intro h3
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, h3, zero_mul, Matrix.det_neg] at this
    simp at this
  exact h2 h1.symm

theorem det_cm_ne : (Cm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (cm_mul_cmi (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem wm_det (x : M2 n) (hx : InG x) (h : (u1 x).det ≠ 0) : (WM x).det ≠ 0 := by
  intro hW
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hW
  set w := -(((u1 x)⁻¹ * u2 x) *ᵥ v)
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have hM : (x * Cm n) *ᵥ Sum.elim w v = 0 := by
    rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_mulVec, mul_cm₁₁, mul_cm₁₂, mul_cm₂₁, mul_cm₂₂]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have e1 : Nm x *ᵥ w + Nm' x *ᵥ v = WM x *ᵥ v := by
      simp only [w, WM, Matrix.mulVec_neg, Matrix.mulVec_mulVec, zOfE_eq, Matrix.sub_mulVec, Matrix.mul_assoc]
      rw [show -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂ = Nm' x from rfl]; abel
    have e2 : u1 x *ᵥ w + u2 x *ᵥ v = 0 := by
      simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1,
        Matrix.one_mul, neg_add_cancel]
    rw [e1, e2, hv]
    funext i; cases i <;> simp
  have hdet : (x * Cm n).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero (det_ne_of_inG hx) det_cm_ne
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
  exact hv0 (funext fun i => by simpa using congrFun h0 (Sum.inr i))

theorem cra2 : CauchyRiemannFacts := by
  refine ⟨fun n m e y => orbital_function_eq_weighted m e y, fun n x h0 h => ⟨da_zOfE x h, fun m e => da_F0E m e x h0 h, fun Q =>
    ⟨fderiv_zOfE_low x h Q, fun m e => fderiv_F0E_low m e x h0 h Q⟩, fun R => ?_, fun hx => wm_det x hx h⟩⟩
  rw [sig_low]
  exact fderiv_zOfE_raise x h Rᴴ

end PositivityTheory.Rg.Sw.HSt.CR
