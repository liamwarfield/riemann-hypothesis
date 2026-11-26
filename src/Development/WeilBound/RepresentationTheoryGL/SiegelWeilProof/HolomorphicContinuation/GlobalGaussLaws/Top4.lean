module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop2
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvac
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCell
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellTop

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstTop
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVac
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacD
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacA
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacB
noncomputable section

open Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem inG_mR (g : GR n) : InG (mR g) := g.2

theorem neg_one_blocks : (-1 : M2 n) = fromBlocks (-1) 0 0 (-1) := by
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem JJ_sq : JJ n * JJ n = -1 := by
  rw [neg_one_blocks]; simp [JJ, fromBlocks_multiply]

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  simp [JJ, fromBlocks_conjTranspose, fromBlocks_neg]

theorem flip_of_inG {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have h1 : (Mᴴ * JJ n) * (-(M * JJ n)) = 1 := by
    rw [mul_neg, ← mul_assoc, h', JJ_sq, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have h3 : M * JJ n * (Mᴴ * JJ n) = -1 := by
    rw [neg_mul] at h2
    exact neg_eq_iff_eq_neg.mp h2
  calc M * JJ n * Mᴴ = -(M * JJ n * (Mᴴ * JJ n) * JJ n) := by
        simp only [mul_assoc, JJ_sq, mul_neg, mul_one, neg_neg]
    _ = JJ n := by rw [h3]; simp

theorem lagr (g : GR n) :
    (mR g).toBlocks₂₁ * ((mR g).toBlocks₂₂)ᴴ = (mR g).toBlocks₂₂ * ((mR g).toBlocks₂₁)ᴴ := by
  have h := flip_of_inG (inG_mR g)
  have h22 := congrArg Matrix.toBlocks₂₂ h
  rw [← Matrix.fromBlocks_toBlocks (mR g)] at h22
  simp only [JJ, fromBlocks_multiply, fromBlocks_conjTranspose, toBlocks_fromBlocks₂₂, mul_zero, zero_add,
    add_zero, mul_one, mul_neg, neg_mul] at h22
  exact (neg_add_eq_zero.mp h22).symm

theorem vec_zero (g : GR n) (z : ℂ) (hz : z.im ≠ 0) (v : Fin n → ℂ)
    (hv : v ᵥ* (z • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂) = 0) : v = 0 := by
  have hl := lagr g
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hv
  have hW : v ᵥ* (mR g).toBlocks₂₂ = -(z • (v ᵥ* (mR g).toBlocks₂₁)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hv
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (v ᵥ* A) ⬝ᵥ star (v ᵥ* B) = (v ᵥ* (A * Bᴴ)) ⬝ᵥ star v := by
    intro A B
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hsym : (v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₂) =
      (v ᵥ* (mR g).toBlocks₂₂) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁) := by
    rw [key, key, hl]
  rw [hW] at hsym
  simp only [star_neg, star_smul, dotProduct_neg, neg_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hsym
  have hz' : z - star z ≠ 0 := by
    intro h0
    apply hz
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hY0 : (v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁) = 0 := by
    have : (z - star z) * ((v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁)) = 0 := by
      linear_combination hsym
    exact (mul_eq_zero.mp this).resolve_left hz'
  have hY : v ᵥ* (mR g).toBlocks₂₁ = 0 := dotProduct_self_star_eq_zero.mp hY0
  have hD : v ᵥ* (mR g).toBlocks₂₂ = 0 := by
    rw [hW, hY, smul_zero, neg_zero]
  have hu : (Sum.elim 0 v : Fin n ⊕ Fin n → ℂ) ᵥ* mR g = 0 := by
    ext j
    cases j with
    | inl k =>
      have := congrFun hY k
      simpa [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₂₁] using this
    | inr k =>
      have := congrFun hD k
      simpa [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₂₂] using this
  have hinv : mR g * ((g : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val = 1 := by
    simp [mR]
  have hu0 : (Sum.elim 0 v : Fin n ⊕ Fin n → ℂ) = 0 := by
    have := congrArg (fun w => w ᵥ* ((g : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val) hu
    simp only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact this
  ext i
  simpa using congrFun hu0 (Sum.inr i)

theorem automorphy_first_det_ne_zero (g : GR n) : (u1 (mR g)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_vecMul_eq_zero_iff).mpr h
  exact hv0 (vec_zero g Complex.I (by simp) v (by simpa [u1] using hv))

theorem automorphy_second_det_ne_zero (g : GR n) : (u2 (mR g)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_vecMul_eq_zero_iff).mpr h
  exact hv0 (vec_zero g (-Complex.I) (by simp) v (by simpa [u2, neg_smul] using hv))

theorem det_ne (g : GR n) : (mR g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem cont_mR : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_vacuum_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inr i)).comp cont_mR)

theorem continuous_vacuum_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inr j)).comp ((continuous_apply (Sum.inr i)).comp cont_mR)

theorem continuous_vacuum_section (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous fun g : GR n => (mR g).det := cont_mR.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := by
    refine Continuous.matrix_det ?_
    unfold u1; exact (continuous_vacuum_lower_left_block.const_smul Complex.I).add continuous_vacuum_lower_right_block
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := by
    refine Continuous.matrix_det ?_
    unfold u2; exact (continuous_vacuum_lower_left_block.const_smul Complex.I).neg.add continuous_vacuum_lower_right_block
  have : F0 (n := n) p q e = fun g => (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))) := rfl
  rw [this]
  exact (hdet.zpow₀ e fun g => Or.inl (det_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (automorphy_first_det_ne_zero g)).mul (h2.zpow₀ _ fun g => Or.inl (automorphy_second_det_ne_zero g)))

theorem lower_left_block_mul {Y G : M2 n} (hY : Y.toBlocks₂₁ = 0) : (Y * G).toBlocks₂₁ = Y.toBlocks₂₂ * G.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁, hY, zero_mul, zero_add]

theorem lower_right_block_mul {Y G : M2 n} (hY : Y.toBlocks₂₁ = 0) : (Y * G).toBlocks₂₂ = Y.toBlocks₂₂ * G.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂, hY, zero_mul, zero_add]

theorem vacuum_section_mul_parabolic (p q : ℕ) (e : ℤ) (y g : GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    F0 p q e (y * g) = F0 p q e y * F0 p q e g := by
  have e1 : u1 (mR y * mR g) = (mR y).toBlocks₂₂ * u1 (mR g) := by
    simp only [u1, lower_left_block_mul hy, lower_right_block_mul hy, Matrix.mul_add, Matrix.mul_smul]
  have e2 : u2 (mR y * mR g) = (mR y).toBlocks₂₂ * u2 (mR g) := by
    simp only [u2, lower_left_block_mul hy, lower_right_block_mul hy, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
  have e1' : u1 (mR y) = (mR y).toBlocks₂₂ := by
    simp [u1, hy]
  have e2' : u2 (mR y) = (mR y).toBlocks₂₂ := by
    simp [u2, hy]
  simp only [F0, f0, mR_mul, e1, e2, e1', e2', det_mul, mul_zpow]
  ring

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h21 : (1 : M2 n).toBlocks₂₁ = 0 := by rw [← fromBlocks_one, toBlocks_fromBlocks₂₁]
  have h22 : (1 : M2 n).toBlocks₂₂ = 1 := by rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]
  simp [F0, f0, u1, u2, mR_one, h21, h22]

theorem JJ_nU (b : Matrix (Fin n) (Fin n) ℂ) : JJ n * nU b = fromBlocks 0 1 (-1) (-b) := by
  simp [JJ, nU, fromBlocks_multiply]

theorem det_JJ : (JJ n).det = 1 := by
  have : JJ n = fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 := by
    simp [JJ, fromBlocks_multiply]
  rw [this, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  rw [nU, det_fromBlocks_zero₂₁]; simp

theorem vacuum_section_big_cell (p q : ℕ) (e : ℤ) (h : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hh : mR h = JJ n * nU b) :
    F0 p q e h = ((-Complex.I) ^ n * (1 - Complex.I • b).det) ^ (-(p : ℤ)) *
      (Complex.I ^ n * (1 + Complex.I • b).det) ^ (-(q : ℤ)) := by
  have e1 : u1 (JJ n * nU b) = (-Complex.I) • (1 - Complex.I • b) := by
    rw [JJ_nU]
    ext i j
    simp [u1, Matrix.one_apply]
    split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have e2 : u2 (JJ n * nU b) = Complex.I • (1 + Complex.I • b) := by
    rw [JJ_nU]
    ext i j
    simp [u2, Matrix.one_apply]
    split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  simp only [F0, f0, hh, det_mul, det_JJ, det_nU, one_mul, _root_.one_zpow, e1, e2, det_smul,
    Fintype.card_fin]

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

noncomputable section

open Matrix Filter Topology Polynomial
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem inG_JJ : InG (JJ n) := by
  unfold InG
  rw [JJ_conjTranspose, Matrix.mul_assoc, JJ_sq, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem nU_mul (b c : Matrix (Fin n) (Fin n) ℂ) : nU b * nU c = nU (b + c) := by
  simp [nU, fromBlocks_multiply, add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, fromBlocks_one]

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG; simp [nU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, hb.eq]

def jjE : GR n := ⟨⟨JJ n, -JJ n, by rw [Matrix.mul_neg, JJ_sq, neg_neg], by rw [Matrix.neg_mul, JJ_sq, neg_neg]⟩, inG_JJ⟩

def nuE (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : GR n :=
  ⟨⟨nU b, nU (-b), by rw [nU_mul, add_neg_cancel, nU_zero], by rw [nU_mul, neg_add_cancel, nU_zero]⟩, inG_nU hb⟩

def nbar (s : ℝ) : M2 n := fromBlocks 1 0 ((s : ℂ) • 1) 1

theorem nbar_mul (s t : ℝ) : nbar (n := n) s * nbar t = nbar (s + t) := by
  simp [nbar, fromBlocks_multiply, add_smul, add_comm]

theorem nbar_zero : nbar (n := n) 0 = 1 := by simp [nbar, fromBlocks_one]

theorem inG_nbar (s : ℝ) : InG (nbar (n := n) s) := by
  unfold InG
  simp [nbar, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_smul, Complex.conj_ofReal]

def nbE (s : ℝ) : GR n :=
  ⟨⟨nbar s, nbar (-s), by rw [nbar_mul, add_neg_cancel, nbar_zero], by rw [nbar_mul, neg_add_cancel, nbar_zero]⟩, inG_nbar s⟩

theorem nbE_zero : nbE (n := n) 0 = 1 := Subtype.ext (Units.ext nbar_zero)

theorem cont_nbar : Continuous (nbar (n := n)) := by
  unfold nbar
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem cont_nbE : Continuous (nbE (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨cont_nbar, ?_⟩
  exact cont_nbar.comp continuous_neg

theorem lower_left_block_mul_lowering (g : GR n) (s : ℝ) :
    (mR (g * nbE s)).toBlocks₂₁ = (mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂ := by
  rw [mR_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
  show (fromBlocks _ _ _ _ * nbar s).toBlocks₂₁ = _
  simp [nbar, fromBlocks_multiply]

theorem finite_bad (g : GR n) :
    {s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0}.Finite := by
  set C := (mR g).toBlocks₂₁
  set D := (mR g).toBlocks₂₂
  set P : Polynomial ℂ := det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C) with hP
  have hev : ∀ z : ℂ, P.eval z = (C + z • D).det := by
    intro z
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hz := hev Complex.I
    rw [h0, Polynomial.eval_zero] at hz
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz.symm
    apply hv
    apply vec_zero g (-Complex.I) (by simp) v
    have hm : (-Complex.I) • C + D = (-Complex.I) • (C + Complex.I • D) := by
      rw [smul_add, smul_smul]
      simp
    rw [hm, Matrix.vecMul_smul, hv0, smul_zero]
  apply ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot, hev]
  exact hs

theorem dense_cell : Dense {g : GR n | ((mR g).toBlocks₂₁).det ≠ 0} := by
  intro g
  have hT : Tendsto (fun s : ℝ => g * nbE s) (𝓝[≠] 0) (𝓝 g) := by
    have hc : Continuous fun s : ℝ => g * nbE s := continuous_const.mul cont_nbE
    have h := hc.tendsto 0
    rw [nbE_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hfin := finite_bad g
  have hZ : IsClosed ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  have h0 : (0 : ℝ) ∉ ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hZ.isOpen_compl.mem_nhds h0), self_mem_nhdsWithin] with s hs hs0
  show ((mR (g * nbE s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_mul_lowering]
  intro hdet
  exact hs ⟨hdet, hs0⟩

theorem bigcell (g : GR n) (hγ : ((mR g).toBlocks₂₁).det ≠ 0) :
    ∃ (y h : GR n) (b : Matrix (Fin n) (Fin n) ℂ), (mR y).toBlocks₂₁ = 0 ∧ b.IsHermitian ∧ mR h = JJ n * nU b ∧
      g = y * h := by
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hγ
  have huH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hγ)
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * Cᴴ⁻¹ = C⁻¹ * (C * Dᴴ) * Cᴴ⁻¹ := by rw [nonsing_inv_mul_cancel_left C _ hu]
      _ = C⁻¹ * (D * Cᴴ) * Cᴴ⁻¹ := by rw [hC, hD, lagr g]
      _ = C⁻¹ * D := by rw [← Matrix.mul_assoc, mul_nonsing_inv_cancel_right Cᴴ _ huH]
  refine ⟨g * (jjE * nuE (C⁻¹ * D) hb)⁻¹, jjE * nuE (C⁻¹ * D) hb, C⁻¹ * D, ?_, hb, ?_, by group⟩
  · have hinv : mR (jjE * nuE (C⁻¹ * D) hb)⁻¹ = nU (-(C⁻¹ * D)) * (-JJ n) := by
      rw [_root_.mul_inv_rev, mR_mul]
      rfl
    rw [mR_mul, hinv]
    conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
    simp [nU, JJ, fromBlocks_multiply, fromBlocks_neg, ← hC, ← hD]
    rw [mul_nonsing_inv_cancel_left C D hu, neg_add_cancel]
  · rw [mR_mul]
    rfl

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem map_star_eq (U : Matrix (Fin n) (Fin n) ℂ) : U.map star = (Uᴴ)ᵀ := by
  ext i j; simp [conjTranspose_apply]

theorem normSq_det_unitary {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    Complex.normSq U.det = 1 := by
  have h := congrArg Matrix.det (mem_unitaryGroup_iff'.mp hU)
  rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose] at h
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  simpa using h

theorem mp_cU {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun w : Fin n → ℂ => (U.map star) *ᵥ w) volume volume := by
  set L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' (U.map star)).restrictScalars ℝ with hLdef
  have hdet : LinearMap.det L = 1 := by
    rw [hLdef, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, map_star_eq,
      det_transpose, det_conjTranspose]
    show Complex.normSq (star U.det) = 1
    rw [Complex.star_def, Complex.normSq_conj, normSq_det_unitary hU]
  have hmeas : Measurable (fun w : Fin n → ℂ => (U.map star) *ᵥ w) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  refine ⟨hmeas, ?_⟩
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

def rowF (c κ : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ :=
  Complex.exp (-(c * ∑ i, ‖v i‖ ^ 2 : ℝ)) * Complex.exp (Complex.I * κ * ∑ i, ∑ j, b i j * star (v j) * v i)

theorem sumsq_eq (v : Fin n → ℂ) : (((∑ i, ‖v i‖ ^ 2 : ℝ)) : ℂ) = star v ⬝ᵥ v := by
  push_cast
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem quad_eq (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ∑ i, ∑ j, b i j * star (v j) * v i = v ⬝ᵥ (b *ᵥ star v) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rowF_comp (c κ : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) (w : Fin n → ℂ) :
    rowF c κ b ((hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).map star *ᵥ w) =
      ∏ k, Complex.exp (-((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) * (‖w k‖ : ℂ) ^ 2) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hUU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem hb.eigenvectorUnitary.2
  have hT : Uᵀ * U.map star = 1 := by
    rw [map_star_eq, ← transpose_mul, hUU, transpose_one]
  have key : ∀ x : Fin n → ℂ, (U *ᵥ x) ⬝ᵥ (U.map star *ᵥ w) = x ⬝ᵥ w := by
    intro x
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hT, vecMul_one]
  have hstar : star (U.map star *ᵥ w) = U *ᵥ star w := by
    ext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  have hbU : b * U = U * diagonal (RCLike.ofReal ∘ hb.eigenvalues) := by
    conv_lhs => rw [hb.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_assoc, star_eq_conjTranspose, hUU, Matrix.mul_one]
  have hS : ∑ i, ‖(U.map star *ᵥ w) i‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
    have h := sumsq_eq (U.map star *ᵥ w)
    rw [hstar, key, ← sumsq_eq] at h
    exact_mod_cast h
  have hQ : ∑ i, ∑ j, b i j * star ((U.map star *ᵥ w) j) * (U.map star *ᵥ w) i =
      ∑ k, (hb.eigenvalues k : ℂ) * (‖w k‖ : ℂ) ^ 2 := by
    rw [quad_eq, dotProduct_comm, hstar, mulVec_mulVec, hbU, ← mulVec_mulVec, key]
    simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.star_def, Complex.conj_mul']
    rfl
  rw [rowF, hS, hQ, ← Complex.exp_add, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem det_shift (c κ : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    ((c : ℂ) • 1 - (Complex.I * κ) • b).det = ∏ k, ((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) := by
  have hX : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * κ) • diagonal (RCLike.ofReal ∘ hb.eigenvalues) =
      diagonal (fun k => (c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [one_apply, h]
  have hD : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * κ) • b =
      Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary
        ((c : ℂ) • 1 - (Complex.I * κ) • diagonal (RCLike.ofReal ∘ hb.eigenvalues)) := by
    conv_lhs => rw [hb.spectral_theorem]
    rw [map_sub, map_smul, map_smul, map_one]
  have hu : (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).det *
      (star (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [← det_mul, Unitary.mul_star_self_of_mem hb.eigenvectorUnitary.2, det_one]
  rw [hD, Unitary.conjStarAlgAut_apply, hX, det_mul, det_mul, det_diagonal, mul_right_comm, hu, one_mul]

theorem row_int (c κ : ℝ) (hc : 0 < c) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    ∫ v : Fin n → ℂ, rowF c κ b v = (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * κ) • b).det := by
  have mp := mp_cU hb.eigenvectorUnitary.2
  have hcont : Continuous (rowF c κ b) := by
    unfold rowF
    fun_prop
  have hg : ∀ k, ∫ z : ℂ, Complex.exp (-((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) * (‖z‖ : ℂ) ^ 2) =
      (Real.pi : ℂ) / ((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) := by
    intro k
    have ha : 0 < ((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)).re := by simp [hc]
    have h := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) ha
    rw [Complex.finrank_real_complex] at h
    simpa using h
  rw [← mp.map_eq, integral_map mp.measurable.aemeasurable hcont.aestronglyMeasurable]
  simp_rw [rowF_comp c κ b hb]
  have hprod := integral_fintype_prod_eq_prod
    (f := fun k (z : ℂ) => Complex.exp (-((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) * (‖z‖ : ℂ) ^ 2))
    (μ := fun _ : Fin n => (volume : Measure ℂ))
  rw [← volume_pi] at hprod
  rw [hprod, Finset.prod_congr rfl (fun k _ => hg k), Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, det_shift c κ b hb]

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {m n : ℕ}

def sR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem gramX_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX ε x j i = ∑ a, (sR ε a : ℂ) * (star (x a j) * x a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, sR, map_sub, map_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem trace_eq (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
  have h1 : (b * gramX ε x).trace = ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h1]
  calc ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i)
      = ∑ i, ∑ a, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := Finset.sum_comm
    _ = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
        simp only [Finset.mul_sum]

theorem secN_one (ε : Fin m → Bool) (c t : ℝ) (hc : 0 < c) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b =
      ∏ a : Fin m, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det := by
  have hpt : ∀ x : Fin m → Fin n → ℂ,
      evX (1 : PX m n) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
        = ∏ a, rowF c (t * sR ε a) b (x a) := by
    intro x
    simp only [evX, map_one, one_mul, gs, rowF, trace_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    · congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · congr 1
      rw [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
  unfold secN
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a v => rowF c (t * sR ε a) b v)]
  exact Finset.prod_congr rfl fun a _ => row_int c _ hc b hb

theorem detpm (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b = (c : ℂ) • (1 - (Complex.I * (s : ℂ)) • b) := by
  rw [smul_sub, smul_smul]; push_cast; congr 2; ring

theorem fac_eq (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b).det =
      ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) * ((1 - (Complex.I * (s : ℂ)) • b).det)⁻¹ := by
  rw [detpm, det_smul, Fintype.card_fin, div_mul_eq_div_div, div_eq_mul_inv]

theorem one_sub_neg (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((-1 : ℝ) : ℂ)) • b) = 1 + Complex.I • b := by
  push_cast; rw [mul_neg_one, neg_smul, sub_neg_eq_add]

theorem one_sub_pos (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((1 : ℝ) : ℂ)) • b) = 1 - Complex.I • b := by
  push_cast; rw [mul_one]

private theorem prod_bool_fun_eq_pow_cnt_mul_pow_cnt (ε : Fin m → Bool) (F : Bool → ℂ) :
    ∏ a, F (ε a) = F true ^ cnt ε true * F false ^ cnt ε false := by
  have h : ∀ a, F (ε a) = if ε a = true then F true else F false := by
    intro a
    cases ε a <;> simp
  rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp [cnt]

theorem secN_eval (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (hc : 0 < c)
    (hsign : (t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true))
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b = ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) *
      (1 - Complex.I • b).det ^ (-(p : ℤ)) * (1 + Complex.I • b).det ^ (-(q : ℤ)) := by
  rw [secN_one ε c t hc b hb]
  rcases hsign with ⟨ht, hp, hq⟩ | ⟨ht, hp, hq⟩
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then 1 else -1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      rw [ht, fac_eq]
      rfl
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then -1 else 1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      have hs : t * sR ε a = c * (if ε a = true then -1 else 1) := by
        rw [ht]
        unfold sR
        split_ifs <;> ring
      rw [hs, fac_eq]
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open Vac

theorem lIvac : LIvac := by
  intro m n ε c t p q e hc hpq S C hS h1 hy hcell
  have hα : ((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)) ≠ 0 := by
    apply mul_ne_zero <;> apply zpow_ne_zero <;> apply pow_ne_zero <;> simp
  have key : ∀ g : GR n, (toBlocks₂₁ (mR g)).det ≠ 0 →
      S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g hg
    obtain ⟨y, h, b, hy0, hb, hh, rfl⟩ := bigcell g hg
    rw [hy y h hy0, hcell h b hb hh, secN_eval ε c t p q hc hpq b hb, vacuum_section_mul_parabolic p q e y h hy0,
      vacuum_section_big_cell p q e h b hh, mul_zpow, mul_zpow]
    field_simp
  have hall : ∀ g, S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g
    exact congrFun (Continuous.ext_on dense_cell hS (continuous_const.mul (continuous_vacuum_section p q e)) key) g
  have hlam := hall 1
  rw [h1, weight_factor_one, mul_one] at hlam
  intro g
  rw [hall g, ← hlam, one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInst
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstA
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (reP p) m = (AddMonoidAlgebra.coeff p m).re := by
  classical
  unfold reP
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem coeff_imP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (imaginary p) m = (AddMonoidAlgebra.coeff p m).im := by
  classical
  unfold imaginary
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = map (algebraMap ℝ ℂ) (reP p) + C Complex.I * map (algebraMap ℝ ℂ) (imaginary p) := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, eval (fun i => (y i : ℂ)) p = 0) : p = 0 := by
  have hev : ∀ (y : σ → ℝ) (q : MvPolynomial σ ℝ),
      eval (fun i => (y i : ℂ)) (map (algebraMap ℝ ℂ) q) = ((eval y q : ℝ) : ℂ) := by
    intro y q
    rw [eval_map]
    change _ = (algebraMap ℝ ℂ) (eval₂ (RingHom.id ℝ) y q)
    rw [hom_eval₂]
    rfl
  have key : ∀ y : σ → ℝ, eval y (reP p) = 0 ∧ eval y (imaginary p) = 0 := by
    intro y
    have hy := h y
    rw [eq_map_re_add_im p, eval_add, eval_mul, eval_C, hev, hev] at hy
    have hre := congrArg Complex.re hy
    have him := congrArg Complex.im hy
    simp at hre him
    exact ⟨hre, him⟩
  have hr : reP p = 0 := MvPolynomial.funext fun y => by simpa using (key y).1
  have hi : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (key y).2
  rw [eq_map_re_add_im p, hr, hi]
  simp

end PositivityTheory.Rg.Sw.Glob.LocInstH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

open MvPolynomial

def toRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
    else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def ofRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
    else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem ofRe_toRe {m n : ℕ} (P : PX m n) : ofRe m n (toRe m n P) = P := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : (C Complex.I : PX m n) * C (1 / (2 * Complex.I)) = C (1 / 2) := by
    rw [← C_mul]; congr 1; field_simp
  have hC2 : (C (1 / 2) : PX m n) + C (1 / 2) = 1 := by
    rw [← C_add, ← C_1]; congr 1; norm_num
  have : (ofRe m n).comp (toRe m n) = AlgHom.id ℂ (PX m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_add (f := _), map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination (X (a, i, false) - X (a, i, true)) * hC + X (a, i, false) * hC2
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_sub, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hC + X (a, i, true) * hC2
  exact congrArg (fun f => f P) this

theorem evX_eq_eval_toRe {m n : ℕ} (P : PX m n) (y : Fin m × Fin n × Bool → ℝ) :
    evX P (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ)) =
      eval (fun k => (y k : ℂ)) (toRe m n P) := by
  have key : (aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ))
      else (y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ)) = (aeval fun k => (y k : ℂ)).comp (toRe m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp [toRe]
    · simp [toRe, Complex.conj_ofReal, sub_eq_add_neg]
  unfold evX
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact congrArg (fun f => f P) key

theorem evX_injective {m n : ℕ} {P Q : PX m n} (h : ∀ u, evX P u = evX Q u) : P = Q := by
  have h0 : toRe m n (P - Q) = 0 := by
    apply eq_zero_of_eval_real
    intro y
    rw [← evX_eq_eval_toRe]
    have := h (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ))
    unfold evX at this ⊢
    rw [map_sub, this, sub_self]
  rw [← sub_eq_zero, ← ofRe_toRe (P - Q), h0, map_zero]

theorem fP_injective {m n : ℕ} {c : ℝ} {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  apply evX_injective
  intro u
  have := congrFun h u
  simp only [fP] at this
  have hg : gs c u ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hg this

theorem fP_smul_add {m n : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add (f := _), smul_eq_C_mul, map_mul, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.LocInstH

namespace PositivityTheory.Rg.Sw.Glob

open LocInstH

theorem locInst_of (hT : TensMem) (hl : LIl) (hlin : LIlin) (hlaw : LIlaw) (hcell : LIcell) (hcont : LIcont)
    (hrho : LIrho) (hk : LIkact) (hvac : LIvac) (hkv : LIkvac) : LocInst := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hl0 := hl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨hlinL, hid⟩ := hlin D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨e, he⟩ := hlaw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨C0, hC0, hCc⟩ := hcell D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨ρ, hρ, hfin⟩ := hrho D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  have hzero : ∀ y : GR n, L y (fP (cLoc l τ) (0 : PX V.rank n)) = 0 := by
    intro y
    have h2 := hlinL y 1 0 0
    simp only [one_smul, add_zero] at h2
    have : L y (fP (cLoc l τ) (0 : PX V.rank n)) + L y (fP (cLoc l τ) (0 : PX V.rank n)) =
        L y (fP (cLoc l τ) (0 : PX V.rank n)) + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel this
  let sL : PX V.rank n →ₗ[ℂ] (GR n → ℂ) :=
    { toFun := fun P => sLd L (cLoc l τ) P
      map_add' := fun P Q => by
        funext y
        have h2 := hlinL y 1 P Q
        rw [one_smul, one_smul] at h2
        simp only [sLd, Pi.add_apply, h2]
      map_smul' := fun a P => by
        funext y
        have h2 := hlinL y a P 0
        rw [add_zero, hzero y, add_zero] at h2
        simp only [sLd, Pi.smul_apply, RingHom.id_apply, h2, smul_eq_mul] }
  have hsign : ((tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true)) := by
    unfold tLoc cLoc pqOf
    split_ifs with h
    · exact Or.inl ⟨by rw [abs_of_pos h], rfl, rfl⟩
    · have hneg : l τ < 0 := lt_of_le_of_ne (not_lt.mp h) hl0
      exact Or.inr ⟨by rw [abs_of_neg hneg]; ring, rfl, rfl⟩
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.mpr hl0
    positivity
  have h11 : sLd L (cLoc l τ) 1 1 = 1 := by
    simp [sLd, hid, fP, evX, gs]
  have hvac' : ∀ g, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g :=
    hvac V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign (sLd L (cLoc l τ) 1) C0
      (hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL 1) h11 (fun y g hy => he 1 y g hy) (fun g b hb hg => hCc 1 g b hb hg)
  refine ⟨sL, ρ, (pqOf ε l τ).1, (pqOf ε l τ).2, e, ?_, ?_, fun P y => rfl, hρ⟩
  · have hs := hC.hsig
    unfold pqOf GoodSig at *
    split_ifs <;> omega
  · refine ⟨hcpos, hsign, fun P => hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P, hvac', fun P y g hy => he P y g hy,
      ⟨C0, hC0, fun P g b hb hg => hCc P g b hb hg⟩,
      fun P g k hk' => hk D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk', ?_, hfin⟩
    intro k hkK
    have h1 := hkv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac' k hkK
    rw [hρ k 1 hkK] at h1
    apply fP_injective (c := cLoc l τ)
    rw [h1]
    have := fP_smul_add (cLoc l τ) (F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k) (1 : PX V.rank n) 0
    simp only [add_zero] at this
    rw [this]
    funext u
    simp [fP, evX]

end PositivityTheory.Rg.Sw.Glob
end
end

namespace PositivityTheory.Rg.Sw.Glob

theorem locInst_of_cell_kvac (hc : LIcell) (hk : LIkvac) (hT : TensMem) : LocInst :=
  locInst_of hT lIl lIlin lIlaw hc lIcont lIrho lIkact lIvac hk

theorem locInst_of_cell (hc : LIcell) (hT : TensMem) : LocInst := locInst_of_cell_kvac hc lIkvac hT

theorem locInst_of_away (hA : AwayAct) (hT : TensMem) : LocInst :=
  locInst_of_cell (lIcell_of' hA lIcont lIlaw lIvac) hT

end PositivityTheory.Rg.Sw.Glob
end

namespace PositivityTheory.Rg.Sw.Glob

theorem top5 (hLF : LocFact) (hAA : AwayAct) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top3 hLF hAA (locInst_of_away hAA tensMem) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
