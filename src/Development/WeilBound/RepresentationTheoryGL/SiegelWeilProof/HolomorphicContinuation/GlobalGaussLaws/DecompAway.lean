module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAwayA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DA

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply GlobalTheory.AdelicU.matHom_injective
  exact Units.ext e

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (A B : Mx D k k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  unfold compAt
  exact Matrix.map_one _ (by simp) (by simp)

theorem finMap_mul {k : ℕ} (A B : Mx D k k) : (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) :=
  Matrix.map_mul (f := finPart D)

theorem compAt_conjT (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {k : ℕ} (A : Mx D k k) :
    compAt θ τ (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) A) = (compAt θ τ A)ᴴ := by
  ext i j
  simp only [compAt, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_Jst (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    compAt θ τ ((Jst D n).map (incA D)) = reidx (JJ n) := by
  ext i j
  simp only [compAt, Matrix.map_apply]
  rw [(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1]
  simp only [Jst, blk4, reidx, JJ, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with a | a <;> rcases h2 : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite]

end PositivityTheory.Rg.Sw.Glob.DA
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

theorem decompAway : DecompAway := by
  intro D n θ τ ι hθ hι g
  obtain ⟨-, hιy⟩ := hι
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * (Jst D n).map (incA D) * mat g =
      (Jst D n).map (incA D) := g.2
  set Y := compAt θ τ (mat g) with hYdef
  have hY : Yᴴ * reidx (JJ n) * Y = reidx (JJ n) := by
    have := congrArg (compAt θ τ) hg
    rwa [DA.compAt_mul, DA.compAt_mul, DA.compAt_conjT θ hθ, DA.compAt_Jst θ hθ] at this
  have hinv : compAt θ τ (mat g⁻¹) * Y = 1 := by
    rw [hYdef, ← DA.compAt_mul, ← DA.mat_mul, inv_mul_cancel, DA.mat_one, DA.compAt_one]
  have hYu : IsUnit Y.det := Matrix.isUnit_det_of_left_inverse hinv
  set M : M2 n := Y.submatrix finSumFinEquiv finSumFinEquiv with hMdef
  have hMY : reidx M = Y := by ext i j; simp [reidx, hMdef]
  have hMG : InG M := by
    have h2 : JJ n = (reidx (JJ n)).submatrix finSumFinEquiv finSumFinEquiv := by ext i j; simp [reidx]
    unfold InG
    rw [h2, hMdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hY]
  have hMu : IsUnit M.det := by rw [hMdef, det_submatrix_equiv_self]; exact hYu
  set y := mkGR M hMu hMG with hydef
  have hιY : compAt θ τ (mat (ι y)) = Y := by rw [(hιy y).1, hydef, mR_mkGR, hMY]
  have htriv : compAt θ τ (mat (g * (ι y)⁻¹)) = 1 := by
    have h3 : compAt θ τ (mat (g * (ι y)⁻¹)) * Y = Y := by
      calc compAt θ τ (mat (g * (ι y)⁻¹)) * Y = compAt θ τ (mat (g * (ι y)⁻¹)) * compAt θ τ (mat (ι y)) := by rw [hιY]
        _ = compAt θ τ (mat (g * (ι y)⁻¹ * ι y)) := by rw [DA.mat_mul (g * (ι y)⁻¹) (ι y), DA.compAt_mul]
        _ = Y := by rw [inv_mul_cancel_right]
    calc compAt θ τ (mat (g * (ι y)⁻¹)) = compAt θ τ (mat (g * (ι y)⁻¹)) * Y * Y⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
      _ = 1 := by rw [h3, Matrix.mul_nonsing_inv _ hYu]
  refine ⟨g * (ι y)⁻¹, y, htriv, by group, ?_⟩
  generalize g * (ι y)⁻¹ = x at htriv ⊢
  intro y'
  apply DA.mat_inj
  rw [DA.mat_mul, DA.mat_mul]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [DA.finMap_mul, DA.finMap_mul, (hιy y').2.2, Matrix.mul_one, Matrix.one_mul]
  · intro τ'
    rw [DA.compAt_mul, DA.compAt_mul]
    by_cases h : τ' = τ
    · subst h
      rw [htriv, Matrix.mul_one, Matrix.one_mul]
    · rw [(hιy y').2.1 τ' h, Matrix.mul_one, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SmulOneConj
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DRealH

variable {n : ℕ}

theorem blocks_of_inG {g : M2 n} (hg : InG g) :
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₁ = (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁ ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₂ = (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂ ∧
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₂ - (g.toBlocks₂₁)ᴴ * g.toBlocks₁₂ = 1 ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₁ - (g.toBlocks₂₂)ᴴ * g.toBlocks₁₁ = -1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero,
    Matrix.fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (· + (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁) h11
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · have := congrArg (· + (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂) h22
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h12
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h21

variable {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem smul_one_conj (w : ℂ) : ((w • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (star w) • 1 := by
  rw [conjTranspose_smul, conjTranspose_one]

theorem cross_self (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B) = (star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h3]; abel
  have e4 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h4]; abel
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e3, e4, h1, h2]
  module

theorem cross_conj (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * ((star w) • C + D) = (w • C + D)ᴴ * ((star w) • A + B) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := eq_add_of_sub_eq h3
  have e4 : Bᴴ * C = -1 + Dᴴ * A := eq_add_of_sub_eq h4
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [h1, h2, e3, e4]
  module

theorem det_ne_zero (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) : (w • C + D).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have key := cross_self h1 h2 h3 h4 w
  have e := congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) key
  have l1 : ((w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B)) *ᵥ v
      = -((w • C + D)ᴴ *ᵥ ((w • A + B) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub]
  have l2 : ((star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = (star w - w) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  simp only [l1, l2] at e
  rw [dotProduct_neg, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv, star_zero, zero_dotProduct, neg_zero,
    dotProduct_smul, smul_eq_mul] at e
  have hne : star w - w ≠ 0 := sub_ne_zero.mpr hw
  have : star v ⬝ᵥ v = 0 := (mul_eq_zero.mp e.symm).resolve_left hne
  exact hv0 (dotProduct_star_self_eq_zero.mp this)

theorem conj_frac (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) :
    ((w • A + B) * (w • C + D)⁻¹)ᴴ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
  have hw' : star (star w) ≠ star w := by
    rw [star_star]
    exact fun h => hw h.symm
  have d1 := det_ne_zero h1 h2 h3 h4 w hw
  have d2 := det_ne_zero h1 h2 h3 h4 (star w) hw'
  have u1 : IsUnit (w • C + D)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact (star_ne_zero.mpr d1).isUnit
  have u2 : IsUnit ((star w) • C + D).det := d2.isUnit
  have cc := cross_conj h1 h2 h3 h4 w
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc ((w • C + D)ᴴ)⁻¹ * (w • A + B)ᴴ
      = ((w • C + D)ᴴ)⁻¹ * ((w • A + B)ᴴ * ((star w) • C + D)) * ((star w) • C + D)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u2]
    _ = ((w • C + D)ᴴ)⁻¹ * ((w • C + D)ᴴ * ((star w) • A + B)) * ((star w) • C + D)⁻¹ := by rw [cc]
    _ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]

end DRealH

open DRealH in
theorem dReal : DReal := by
  intro m n ε t c e y X a ha s
  funext u
  have hA : aC X (s : ℂ) = mR (a s) := by
    rw [ha s]
    unfold aC
    congr 1
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  have hmul : mR y * aC X (s : ℂ) = mR (y * a s) := by
    rw [hA]
    rfl
  have hG : InG (mR (y * a s)) := (y * a s).2
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG hG
  have hIs : star Complex.I ≠ Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    norm_num at this
  have key := conj_frac h1 h2 h3 h4 Complex.I hIs
  have sI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [sI] at key
  have cI : ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (-Complex.I) • 1 := by
    rw [smul_one_conj, sI]
  unfold famC jF gZf gC jC ptZ actZ
  simp only [hmul, cI, Matrix.mul_smul, Matrix.mul_one]
  rw [key]

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {m n : ℕ}

theorem evX_Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) (u : Fin m → Fin n → ℂ) :
    evX (Qb ε b i j) u = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evX, Qb, map_sum]

theorem gramB_apply (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramB ε b u i j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := evX_Qb ε b i j u

theorem gramB_not (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB (fun a => !ε a) b u = gramB ε (!b) u := by
  ext i j
  simp only [gramB_apply]
  refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
  cases ε a <;> cases b <;> simp

theorem gramX_eq (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) :
    gramX ε u = gramB ε true u - gramB ε false u := by
  ext i j
  simp [gramX, gramB, Qp, evX, map_sub]

private theorem gramB_eq_conjTranspose_diagonal_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB ε b u = (Matrix.of u)ᴴ * diagonal (fun a => if ε a = b then (1 : ℂ) else 0) * Matrix.of u := by
  ext i j
  simp [gramB_apply, Matrix.mul_apply, diagonal_apply, Finset.sum_filter, conjTranspose_apply]

theorem gramB_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    gramB ε b (Matrix.of u * a) = aᴴ * gramB ε b u * a := by
  rw [gramB_eq_conjTranspose_diagonal_mul ε b u]
  refine (gramB_eq_conjTranspose_diagonal_mul ε b (Matrix.of u * a)).trans ?_
  change (Matrix.of u * a)ᴴ * _ * (Matrix.of u * a) = _
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem epsT_pos {t : ℝ} (ht : 0 < t) (ε : Fin m → Bool) : epsT t ε = ε := by
  funext a; simp [epsT, ht]

theorem epsT_nonpos {t : ℝ} (ht : ¬ 0 < t) (ε : Fin m → Bool) : epsT t ε = fun a => !ε a := by
  funext a; simp [epsT, ht]

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  simp only [cnt]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simpa using this

theorem chN_mul_gZf (ε : Fin m → Bool) {t c : ℝ} (htc : |t| = c) (b Z : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : chN ε t b u * gZf ε t c Z u = gZf ε t c (Z + b) u := by
  unfold chN gZf
  rw [← Complex.exp_add]
  congr 1
  rw [gramX_eq, conjTranspose_add, hb]
  by_cases ht : 0 < t
  · rw [epsT_pos ht]
    have htc' : t = c := by rw [← htc, abs_of_pos ht]
    subst htc'
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  · rw [epsT_nonpos ht, gramB_not, gramB_not]
    have htc' : t = -c := by rw [← htc, abs_of_nonpos (not_lt.mp ht), neg_neg]
    subst htc'
    simp only [Bool.not_true, Bool.not_false, Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.ofReal_neg]
    ring

theorem trace_cyc (Z a G : Matrix (Fin n) (Fin n) ℂ) : (Z * (aᴴ * G * a)).trace = (a * Z * aᴴ * G).trace := by
  rw [show Z * (aᴴ * G * a) = (Z * aᴴ * G) * a by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem gZf_mul (ε : Fin m → Bool) (t c : ℝ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZf ε t c Z (Matrix.of u * a) = gZf ε t c (a * Z * aᴴ) u := by
  unfold gZf
  rw [gramB_mul, gramB_mul, trace_cyc, trace_cyc, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchange
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

namespace SchwartzDifferenceQuotient

variable {m n : ℕ}

instance haarInner (n : ℕ) : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance haarOuter (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

theorem isSch_sub {f g : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (f - g) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨S', rfl⟩ := hg
  exact ⟨S - S', by ext u; simp⟩

theorem isSch_smul (a : ℂ) {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : IsSch (fun u => a * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨a • S, by ext u; simp [smul_eq_mul]⟩

theorem isSch_continuous {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : Continuous f := by
  obtain ⟨S, rfl⟩ := hf
  exact S.continuous

theorem isSch_sq_integrable {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) :
    Integrable (fun u => ‖f u‖ ^ 2) := by
  obtain ⟨S, rfl⟩ := hf
  exact (S.memLp ((2 : ℕ) : ENNReal) volume).integrable_norm_pow two_ne_zero

end SchwartzDifferenceQuotient

open SchwartzDifferenceQuotient in
theorem dL2 : DifferenceQuotientIsometryExchange := by
  intro m n T κ hκ hTS hTsub hTsmul hTiso G G' E' s hG hG' hE' hL2 hpt
  have hD : ∀ h : ℝ, IsSch (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) := by
    intro h
    have h3 := isSch_sub (isSch_smul ((h : ℂ)⁻¹) (isSch_sub (hG (s + h)) (hG s))) hG'
    convert h3 using 1
    funext u
    simp only [Pi.sub_apply, div_eq_mul_inv]
    ring
  have hTD : ∀ h : ℝ, T (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
      fun u => (T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u := by
    intro h
    have e1 : (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
        (fun u => (h : ℂ)⁻¹ * (G (s + h) - G s) u) - G' := by
      funext u
      simp only [Pi.sub_apply]
      try ring
    rw [e1, hTsub _ _ (isSch_smul _ (isSch_sub (hG _) (hG _))) hG',
      hTsmul _ _ (isSch_sub (hG _) (hG _)), hTsub _ _ (hG _) (hG _)]
    funext u
    simp only [Pi.sub_apply]
    try ring
  obtain ⟨F, hF⟩ : ∃ F : ℝ → (Fin m → Fin n → ℂ) → ENNReal,
      F = fun h u => ENNReal.ofReal (‖(T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u‖ ^ 2) := ⟨_, rfl⟩
  have hmeas : ∀ h, Measurable (F h) := by
    intro h
    have hc := isSch_continuous (hTS _ (hD h))
    rw [hTD] at hc
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (hc.norm.pow 2).measurable
  have hlim_pt : ∀ u, Tendsto (fun h => F h u) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (‖E' u - T G' u‖ ^ 2))) := by
    intro u
    rw [hF]
    have h1 := ((hpt u).sub_const (T G' u)).norm.pow 2
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have hint : ∀ h, ∫⁻ u, F h u = ENNReal.ofReal (κ * ∫ u, ‖(G (s + h) u - G s u) / (h : ℂ) - G' u‖ ^ 2) := by
    intro h
    rw [← hTiso _ (hD h), hTD, ofReal_integral_eq_lintegral_ofReal, hF]
    · have hi := isSch_sq_integrable (hTS _ (hD h))
      rw [hTD] at hi
      exact hi
    · exact Filter.Eventually.of_forall fun u => sq_nonneg _
  have hlim_int : Tendsto (fun h => ∫⁻ u, F h u) (𝓝[≠] 0) (𝓝 0) := by
    simp_rw [hint]
    have h1 := hL2.const_mul κ
    rw [mul_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have hfatou := lintegral_liminf_le (μ := (volume : Measure (Fin m → Fin n → ℂ))) (u := 𝓝[≠] (0 : ℝ)) hmeas
  rw [hlim_int.liminf_eq] at hfatou
  have hz : ∫⁻ u, ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) = 0 := by
    refine le_antisymm ?_ (by simp)
    calc _ = ∫⁻ u, liminf (fun h => F h u) (𝓝[≠] (0 : ℝ)) := by
          congr 1
          funext u
          exact ((hlim_pt u).liminf_eq).symm
      _ ≤ 0 := hfatou
  have hcT := isSch_continuous (hTS _ hG')
  have hcE : Continuous fun u => E' u - T G' u := hE'.sub hcT
  have hm : Measurable fun u => ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hcE.norm.pow 2).measurable
  rw [lintegral_eq_zero_iff hm] at hz
  have hae : E' =ᵐ[volume] T G' := by
    filter_upwards [hz] with u hu
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hu
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hu (sq_nonneg _))))
  exact ((Continuous.ae_eq_iff_eq volume hE' hcT).mp hae).symm

end PositivityTheory.Rg.Sw.Glob
end
end
