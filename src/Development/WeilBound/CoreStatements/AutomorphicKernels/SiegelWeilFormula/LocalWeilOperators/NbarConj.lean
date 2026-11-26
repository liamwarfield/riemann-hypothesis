module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.NbarConj
noncomputable section

open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem w_four {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := w_four_pf h

theorem nbar_conj' {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ :=
  R.nbar_conj_pf w h

end RD

end PositivityTheory.SiegelWeilFormula

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocJJA
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eps_of_unit {n : ℕ} (hn : 1 ≤ n) (ε ε' : ℤˣ)
    (h : (wM n ((ε : ℤ) : ℂ))ᵀ * Krd.Qc n ε' * (wM n ((ε : ℤ) : ℂ)).map star = Krd.Qc n ε') : ε = ε' := by
  have h2 := congrArg Matrix.toBlocks₂₁ h
  simp [wM, Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at h2
  have h3 := congrFun (congrFun h2 ⟨0, hn⟩) ⟨0, hn⟩
  simp at h3
  exact Units.ext (by exact_mod_cast h3)

namespace RD

variable {d : SD σ} (R : RD d)

theorem isW_eps (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε := by
  have hmem : (mat2 w₀)ᵀ * dbl (incM F d.Y.J) * (mat2 w₀).map (cA σ) = dbl (incM F d.Y.J) := w₀.2
  have hmat : mat2 w₀ = incM F d.b.1 * inFrame d.b w₀ * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc]
    rw [Krd.bb d, Matrix.one_mul, Matrix.mul_assoc, Krd.bb d, Matrix.mul_one]
  have hc := congrArg (d.cw w) hmem
  rw [Krd.cw_mul d, Krd.cw_mul d, Place.cw_cA d, Krd.cw_transpose d, Krd.dbl_incM d, Krd.cw_incM d, hmat,
    Krd.cw_mul d, Krd.cw_mul d, Krd.cw_incM d, Krd.cw_incM d, RD.cw_wM h w] at hc
  set P := d.b.1.map (d.B.emb w).1
  set Pi := (d.b⁻¹).1.map (d.B.emb w).1
  set D := (dbl d.Y.J).map (d.B.emb w).1
  set Wc := wM d.n ((ε : ℤ) : ℂ)
  have hPiP : Pi * P = 1 := by
    simp only [Pi, P]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ := Krd.hQ_w d R.hε w
  apply eps_of_unit d.ok.hn ε R.ε
  calc Wcᵀ * Krd.Qc d.n R.ε * Wc.map star
      = (Pi * P)ᵀ * Wcᵀ * (Pᵀ * D * P.map star) * Wc.map star * (Pi * P).map star := by
        rw [hPiP, hQ, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    _ = Pᵀ * ((P * Wc * Pi)ᵀ * D * (P * Wc * Pi).map star) * P.map star := by
        simp only [Matrix.transpose_mul, Krd.mapStar_mul, Matrix.mul_assoc]
    _ = Krd.Qc d.n R.ε := by rw [hc, hQ]

end RD

end PositivityTheory.SiegelWeilFormula

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNB
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNA
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Alg

theorem gram_loc {m n : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (J : Matrix (Fin m) (Fin m) ℂ) (ζ s : ℂ) (hζ : ζ ≠ 0)
    (hfr : ζ • (frᵀ * J * fr.map star) = s • 1) (u : Matrix (Fin m) (Fin n) ℂ) :
    (fr * u.map star)ᵀ * J * (fr * u.map star).map star = (ζ⁻¹ * s) • (uᴴ * u) := by
  have h1 : frᵀ * J * fr.map star = (ζ⁻¹ * s) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [mul_smul, ← hfr, smul_smul, inv_mul_cancel₀ hζ, one_smul]
  have hmap : (fr * u.map star).map star = fr.map star * u := by
    ext i j
    simp [Matrix.mul_apply, star_sum]
  rw [hmap, Matrix.transpose_mul]
  calc (u.map star)ᵀ * frᵀ * J * (fr.map star * u)
        = (u.map star)ᵀ * (frᵀ * J * fr.map star) * u := by simp only [Matrix.mul_assoc]
    _ = (ζ⁻¹ * s) • (uᴴ * u) := by
        rw [h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        rfl

theorem trace_herm_real {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB, Matrix.trace_mul_comm]
  have him : (A * B).trace.im = 0 := by
    have h' := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at h'
    linarith
  exact Complex.ext (by simp) (by simp [him])

end Alg

end PositivityTheory.SiegelWeilFormula

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem cw_mulR {p q r : Type} [Fintype q] (w' : InfinitePlace F) (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w' (A * B) = d.cw w' A * d.cw w' B :=
  Matrix.map_mul (f := piInf (d.B.emb w'))

theorem cw_loc (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have e : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [e, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem cw_gram (X : Mx F E d.m d.n) :
    d.cw w (d.gram X X) = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  simp only [SD.gram]
  rw [cw_mulR, cw_mulR, Krd.cw_transpose d, Krd.cw_incM d, Place.cw_cA d, R.cw_loc w X]
  exact gram_loc _ _ _ _ hζ0 (R.hfr w) _

theorem piInf_half (τ : EmbOver E w) : piInf τ (algebraMap (AF F) (AE F E) (⅟(2 : AF F))) = 1 / 2 := by
  have h := congrArg (fun a => piInf τ (algebraMap (AF F) (AE F E) a)) (invOf_mul_self (2 : AF F))
  simp only [map_mul, map_one, map_ofNat] at h
  rw [eq_div_iff two_ne_zero]
  exact h

theorem psi_nU (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hb : bᴴ = b) (β : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hβw : d.cw w β = R.ζ • b) (hβo : ∀ w', w' ≠ w → d.cw w' β = 0) (hβf : finOne F • β = 0) (X : Mx F E d.m d.n) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) = Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)))) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set z : AE F E := (-(⅟(2 : AF F))) • (β * d.gram X X).trace with hz
  have e1 : -(⅟(2 : AF F) * d.tt (β * d.gram X X)) = Algebra.trace (AF F) (AE F E) z := by
    rw [hz, LinearMap.map_smul, smul_eq_mul, neg_mul]
    rfl
  have hpi : ∀ w', piInf (d.B.emb w') z = -(1 / 2) * (d.cw w' β * d.cw w' (d.gram X X)).trace := by
    intro w'
    rw [hz, Algebra.smul_def, map_mul, map_neg, map_neg, piInf_half, ← cw_mulR]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, SD.cw, Matrix.map_apply, Matrix.diag, map_sum]
  have hf : finOne F • z = 0 := by
    rw [hz, smul_comm, ← Matrix.trace_smul, ← Matrix.smul_mul, hβf, Matrix.zero_mul, Matrix.trace_zero, smul_zero]
  have ho : ∀ u, u ≠ w → piInf (d.B.emb u) z = 0 := by
    intro u hu
    rw [hpi, hβo u hu, Matrix.zero_mul, Matrix.trace_zero, mul_zero]
  rw [e1, Place.psi_trace_at d.std d.cm d.B.emb w z hf ho, hpi, hβw, R.cw_gram w X]
  set T := (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace with hT
  have hreal : ((T.re : ℝ) : ℂ) = T := trace_herm_real _ _ hb (by rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose])
  have e2 : (R.ζ • b * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace = ((R.sg w : ℤ) : ℂ) * T := by
    rw [smul_mul_smul_comm, Matrix.trace_smul, hT, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  rw [e2]
  rw [← hreal]
  congr 1
  push_cast
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, zero_mul]
  push_cast
  ring

end RD

end PositivityTheory.SiegelWeilFormula

end
end
