module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CharacterQuadraticDerivativeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.IsCompactK

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FrameBlockPairingSign
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Matrix

section Place

variable {m n : ℕ}

def T1 (A : Matrix (Fin m) (Fin m) ℂ) (C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : Matrix (Fin m) (Fin n) ℂ)
    (V : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  trace ((x * (bw.toCols₂)ᵀ)ᵀ * A * (V * (bw.toCols₁)ᵀ).map star * Cᵀ)

def T2 (fi : Matrix (Fin m) (Fin m) ℂ) (x V : Matrix (Fin m) (Fin n) ℂ) : ℂ := trace ((fi * x)ᴴ * (fi * V))

def Sw (A fi : Matrix (Fin m) (Fin m) ℂ) (C bw biw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ) : ℂ :=
  (4 * Real.pi * Complex.I) * ((T1 A C bw x (U * biwᵀ).toCols₁).re : ℂ) -
    (4 * Real.pi) * ((T2 fi x (U * biwᵀ).toCols₂).re : ℂ)

theorem frame_block_pairing_sign {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε : ℤˣ} (hJ : bwᵀ * C * bw.map star = jE n ε) :
    (bw.toCols₂)ᵀ * C * (bw.toCols₁).map star = ((ε : ℤ) : ℂ) • 1 := by
  ext i j
  have h := congrFun (congrFun hJ (Sum.inr i)) (Sum.inl j)
  simp only [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.fromBlocks_apply₂₁] at h
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.toCols₁_apply,
    Matrix.toCols₂_apply]

theorem mapStar_mul {a b c : Type} [Fintype b] (M : Matrix a b ℂ) (N : Matrix b c ℂ) :
    (M * N).map star = M.map star * N.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

theorem trace_form_sign_eq {A : Matrix (Fin m) (Fin m) ℂ} {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε : ℤˣ}
    (hJ : bwᵀ * C * bw.map star = jE n ε) (x V : Matrix (Fin m) (Fin n) ℂ) :
    T1 A C bw x V = ((ε : ℤ) : ℂ) * trace (xᵀ * A * V.map star) := by
  have h1 := PositivityTheory.SiegelWeilFormula.KK.frame_block_pairing_sign hJ
  have h2 : ((bw.toCols₁).map star)ᵀ * Cᵀ * bw.toCols₂ = ((ε : ℤ) : ℂ) • 1 := by
    have h := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.transpose_one, ← Matrix.mul_assoc] at h
    exact h
  unfold PositivityTheory.SiegelWeilFormula.KK.T1
  calc trace ((x * (bw.toCols₂)ᵀ)ᵀ * A * (V * (bw.toCols₁)ᵀ).map star * Cᵀ)
      = trace (bw.toCols₂ * (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ))) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, PositivityTheory.SiegelWeilFormula.KK.mapStar_mul,
          Matrix.transpose_map, Matrix.mul_assoc]
    _ = trace (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ) * bw.toCols₂) :=
        Matrix.trace_mul_comm _ _
    _ = trace (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ * bw.toCols₂)) := by
        simp only [Matrix.mul_assoc]
    _ = trace (xᵀ * A * V.map star * (((ε : ℤ) : ℂ) • 1)) := by rw [h2]
    _ = ((ε : ℤ) : ℂ) * trace (xᵀ * A * V.map star) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

theorem trace_transpose_star {a b : Type} [Fintype a] [Fintype b] (M N : Matrix a b ℂ) :
    trace (Mᵀ * N.map star) = star (trace (Mᴴ * N)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, star_sum, star_mul', star_star]

theorem A_eq {A fr fi : Matrix (Fin m) (Fin m) ℂ} {sg : ℤˣ} {ζ : ℂ} (hfi' : fr * fi = 1) (hz : star ζ * ζ = 1)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) :
    A = (((sg : ℤ) : ℂ) * star ζ) • (fiᵀ * fi.map star) := by
  have h1 : frᵀ * A * fr.map star = (((sg : ℤ) : ℂ) * star ζ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have h := congrArg (fun M => star ζ • M) hfr
    simp only [smul_smul, hz, one_smul] at h
    rw [h, mul_comm]
  have hfi : fiᵀ * frᵀ = 1 := by rw [← Matrix.transpose_mul, hfi', Matrix.transpose_one]
  have hfi2 : fr.map star * fi.map star = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.KK.mapStar_mul, hfi']
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  calc A = fiᵀ * frᵀ * A * (fr.map star * fi.map star) := by
        rw [hfi, hfi2, Matrix.one_mul, Matrix.mul_one]
    _ = fiᵀ * (frᵀ * A * fr.map star) * fi.map star := by simp only [Matrix.mul_assoc]
    _ = fiᵀ * ((((sg : ℤ) : ℂ) * star ζ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * fi.map star := by rw [h1]
    _ = (((sg : ℤ) : ℂ) * star ζ) • (fiᵀ * fi.map star) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem trace_form_dual_eq {A fr fi : Matrix (Fin m) (Fin m) ℂ} {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε sg : ℤˣ} {ζ : ℂ} (hfi' : fr * fi = 1) (hz : star ζ * ζ = 1)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) (hJ : bwᵀ * C * bw.map star = jE n ε)
    (x V : Matrix (Fin m) (Fin n) ℂ) :
    T1 A C bw x V = ((ε : ℤ) : ℂ) * ((((sg : ℤ) : ℂ) * star ζ) * star (T2 fi x V)) := by
  rw [PositivityTheory.SiegelWeilFormula.KK.trace_form_sign_eq hJ,
    PositivityTheory.SiegelWeilFormula.KK.A_eq hfi' hz hfr]
  congr 1
  unfold PositivityTheory.SiegelWeilFormula.KK.T2
  rw [← PositivityTheory.SiegelWeilFormula.KK.trace_transpose_star, Matrix.transpose_mul, PositivityTheory.SiegelWeilFormula.KK.mapStar_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem Sw_rel {A fr fi : Matrix (Fin m) (Fin m) ℂ} {C bw biw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε sg : ℤˣ}
    {ζ : ℂ} (e2 : biw * bw = 1) (hfi' : fr * fi = 1) (hJ : bwᵀ * C * bw.map star = jE n ε)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I)
    (x : Matrix (Fin m) (Fin n) ℂ) (U U' : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ)
    (hU : U' = (((((1 : ℤˣ) : ℤ) : ℂ) * Complex.I) • ((-(Complex.I * ((((ε : ℤ) : ℂ) * ((sg : ℤ) : ℂ)) * ζ))) •
      (1 : Matrix (Fin m) (Fin m) ℂ) * U * (bw * (jE n ε)ᵀ * biw)ᵀ))) :
    Sw A fi C bw biw x U' = Complex.I * Sw A fi C bw biw x U := by
  have hz : star ζ * ζ = 1 := by
    rcases hζ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have hW : (bw * (PositivityTheory.SiegelWeilFormula.KK.jE n ε)ᵀ * biw)ᵀ * biwᵀ = biwᵀ * PositivityTheory.SiegelWeilFormula.KK.jE n ε := by
    rw [← Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have hUb : U' * biwᵀ = (((((1 : ℤˣ) : ℤ) : ℂ) * Complex.I) * (-(Complex.I * ((((ε : ℤ) : ℂ) * ((sg : ℤ) : ℂ)) * ζ)))) •
      (U * biwᵀ * PositivityTheory.SiegelWeilFormula.KK.jE n ε) := by
    rw [hU, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc U _ biwᵀ, hW, ← Matrix.mul_assoc]
  have hYS1 : ∀ Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ,
      (Y * PositivityTheory.SiegelWeilFormula.KK.jE n ε).toCols₁ = ((ε : ℤ) : ℂ) • Y.toCols₂ := by
    intro Y
    ext i j
    simp [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    try ring
  have hYS2 : ∀ Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ,
      (Y * PositivityTheory.SiegelWeilFormula.KK.jE n ε).toCols₂ = Y.toCols₁ := by
    intro Y
    ext i j
    simp [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    try ring
  have hts1 : ∀ (c : ℂ) (M : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ), (c • M).toCols₁ = c • M.toCols₁ :=
    fun _ _ => Matrix.ext fun _ _ => rfl
  have hts2 : ∀ (c : ℂ) (M : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ), (c • M).toCols₂ = c • M.toCols₂ :=
    fun _ _ => Matrix.ext fun _ _ => rfl
  have hT : ∀ V, PositivityTheory.SiegelWeilFormula.KK.T1 A C bw x V =
      ((ε : ℤ) : ℂ) * ((((sg : ℤ) : ℂ) * star ζ) * star (PositivityTheory.SiegelWeilFormula.KK.T2 fi x V)) :=
    PositivityTheory.SiegelWeilFormula.KK.trace_form_dual_eq hfi' hz hfr hJ x
  have hN : ∀ (c : ℂ) (V : Matrix (Fin m) (Fin n) ℂ),
      PositivityTheory.SiegelWeilFormula.KK.T2 fi x (c • V) = c * PositivityTheory.SiegelWeilFormula.KK.T2 fi x V := by
    intro c V
    unfold PositivityTheory.SiegelWeilFormula.KK.T2
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  unfold PositivityTheory.SiegelWeilFormula.KK.Sw
  rw [hUb, hts1, hts2, hYS1, hYS2, smul_smul, hT, hT, hN, hN]
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases Int.units_eq_one_or sg with rfl | rfl <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end Place

end PositivityTheory.SiegelWeilFormula.KK

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem T_add (Φ Ψ : d.Fn) (X : Mx F E d.m d.n) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := by
  simp only [SD.T, ← map_add (f := _)]
  congr 1
  funext z
  exact mul_add _ _ _


variable (d) in
abbrev b1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₁

theorem incM_mul {ι ι' ι'' : Type} [Fintype ι'] (x : Matrix ι ι' E) (y : Matrix ι' ι'' E) :
    incM F (x * y) = incM F x * incM F y := Matrix.map_mul

theorem incM_one {ι : Type} [DecidableEq ι] : incM F (1 : Matrix ι ι E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem split (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    u = (u * (incM F (d.b⁻¹).1)ᵀ).toCols₁ * (b1 d)ᵀ + (u * (incM F (d.b⁻¹).1)ᵀ).toCols₂ * (b2 d)ᵀ := by
  have e : incM F d.b.1 = Matrix.fromCols (b1 d) (b2 d) := by
    rw [b1, b2, ← Matrix.fromCols_toCols d.b.1]; ext i (j | j) <;> rfl
  have e1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one,
      Matrix.transpose_one]
  calc u = u * (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
    _ = _ := by
      rw [e, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (u * (incM F (d.b⁻¹).1)ᵀ), Matrix.fromCols_mul_fromRows,
        Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]

theorem at_mul {α β γ : Type} [Fintype β] {u : Matrix α β (AE F E)} (hu : At (evI F) u) (M : Matrix β γ (AE F E)) :
    At (evI F) (u * M) := fun c hc => by rw [← Matrix.smul_mul, hu c hc, Matrix.zero_mul]

theorem at_toCols₁ {α β γ : Type} {u : Matrix α (β ⊕ γ) (AE F E)} (hu : At (evI F) u) : At (evI F) u.toCols₁ :=
  fun c hc => by ext i j; exact congrFun₂ (hu c hc) i (.inl j)

theorem at_toCols₂ {α β γ : Type} {u : Matrix α (β ⊕ γ) (AE F E)} (hu : At (evI F) u) : At (evI F) u.toCols₂ :=
  fun c hc => by ext i j; exact congrFun₂ (hu c hc) i (.inr j)

theorem first_frame_half_eq_mul : ∃ t : Matrix (Fin d.n) (Fin d.n) (AE F E), b1 d = dg d * t := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  refine ⟨incM F t.1, ?_⟩
  have h2 : ∀ i j, d.b.1 i (Sum.inl j) = ∑ k, (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) i k * t.1 k j :=
    fun i j => congrFun₂ ht i j
  ext i j
  rw [Matrix.mul_apply]
  change inclR (AF F) (d.b.1 i (Sum.inl j)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1
  rcases i with i | i <;>
  · change inclR (AF F) ((1 : Matrix (Fin d.n) (Fin d.n) E) i k) = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k
    by_cases h : i = k <;> simp [Matrix.one_apply, h]

def vacF (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, gs (2 * Real.pi) (R.loc w X)) * g fun k => (d.crd X k).2

theorem hasDerivAt_normSq (y v : ℂ) :
    HasDerivAt (fun t : ℝ => ‖y + (t : ℂ) * v‖ ^ 2) (2 * (star y * v).re) 0 := by
  have e : (fun t : ℝ => ‖y + (t : ℂ) * v‖ ^ 2) = fun t => (y.re + t * v.re) ^ 2 + (y.im + t * v.im) ^ 2 := by
    funext t
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => y.re + t * v.re) v.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.re).const_add y.re
  have h2 : HasDerivAt (fun t : ℝ => y.im + t * v.im) v.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add y.im
  refine ((h1.pow 2).add (h2.pow 2)).congr_deriv ?_
  rw [show (star y * v).re = y.re * v.re + y.im * v.im by simp [Complex.mul_re]]
  simp only [zero_mul, add_zero, pow_one, Nat.cast_ofNat]
  ring

theorem cw_add_smul (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    d.cw w (X + realAd F t • Z) = d.cw w X + (t : ℂ) • d.cw w Z := by
  ext i j
  show piInf (d.B.emb w) ((X + realAd F t • Z) i j) = piInf (d.B.emb w) (X i j) + (t : ℂ) * piInf (d.B.emb w) (Z i j)
  rw [Matrix.add_apply, Matrix.smul_apply, map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul]

theorem snd_add_realAd (t : ℝ) (a b : AF F) : (a + realAd F t * b).2 = a.2 := by
  show a.2 + (realAd F t).2 * b.2 = a.2
  rw [show (realAd F t).2 = 0 from rfl, zero_mul, add_zero]

theorem crd_add_smul_snd (X Z : Mx F E d.m d.n) (t : ℝ) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (X + realAd F t • Z) k).2 = (d.crd X k).2 := by
  have e : d.crd (X + realAd F t • Z) k = d.crd X k + realAd F t * d.crd Z k := by
    simp only [SD.crd, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
  rw [e, snd_add_realAd]

theorem realAd_zero : realAd F 0 = 0 := by
  unfold realAd
  rw [map_zero, map_zero, map_zero]

def qL (R : RD d) (X Z : Mx F E d.m d.n) (t : ℝ) : ℝ :=
  ∑ w, ∑ a, ∑ i, ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2

theorem gs_loc (R : RD d) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    gs (2 * Real.pi) (R.loc w (X + realAd F t • Z)) = Complex.exp ((-(2 * Real.pi * ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) : ℝ) : ℂ) := by
  simp only [gs, RD.loc, cw_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.map_apply, norm_star, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg]

theorem vacF_line (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) (t : ℝ) :
    vacF R g (X + realAd F t • Z) = Complex.exp ((-(2 * Real.pi) * qL R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
  simp only [vacF, crd_add_smul_snd, gs_loc]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [qL]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem trace_re {p q : ℕ} (y v : Matrix (Fin p) (Fin q) ℂ) :
    (Matrix.trace (yᴴ * v)).re = ∑ a, ∑ i, (star (y a i) * v a i).re := by
  rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  rfl

theorem vacF_deriv (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => vacF R g (X + realAd F t • Z))
      (((-(4 * Real.pi) * ∑ w, (Matrix.trace ((((R.fr w)⁻¹).1 * d.cw w X)ᴴ * (((R.fr w)⁻¹).1 * d.cw w Z))).re : ℝ) : ℂ) *
        vacF R g X) 0 := by
  have hf : (fun t : ℝ => vacF R g (X + realAd F t • Z)) =
      fun t => Complex.exp ((-(2 * Real.pi) * qL R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 :=
    funext (vacF_line R g X Z)
  rw [hf]
  have hq : HasDerivAt (qL R X Z)
      (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) 0 := by
    unfold qL
    refine HasDerivAt.fun_sum (A := fun w (t : ℝ) => ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun w _ => ?_
    refine HasDerivAt.fun_sum (A := fun a (t : ℝ) => ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun a _ => ?_
    exact HasDerivAt.fun_sum (A := fun i (t : ℝ) =>
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun i _ =>
      hasDerivAt_normSq _ _
  have he := ((hq.const_mul (-(2 * Real.pi))).ofReal_comp.cexp).mul_const (g fun k => (d.crd X k).2)
  refine he.congr_deriv ?_
  have e0 : vacF R g X = Complex.exp ((-(2 * Real.pi) * qL R X Z 0 : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
    have := vacF_line R g X Z 0
    rwa [realAd_zero, zero_smul, add_zero] at this
  rw [e0]
  have e2 : (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) =
      2 * ∑ w, ∑ a, ∑ i, (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re := by
    simp only [Finset.mul_sum]
  simp only [trace_re, e2]
  push_cast
  ring

theorem frame_form (R : RD d) (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * dbl (d.Y.J.map (d.B.emb w).1) * (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
  have h := d.ok.good.cm
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have hd : (dbl d.Y.J).map (d.B.emb w).1 = dbl (d.Y.J.map (d.B.emb w).1) := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks]
  have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map, cst, hd] at this
  rw [this]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]

theorem map_mul_incM_transpose_eq {p q r : Type} [Fintype q] (w : InfinitePlace F) (x : Matrix p q (AE F E)) (y : Matrix r q E) :
    (x * (incM F y)ᵀ).map (piInf (d.B.emb w)) = x.map (piInf (d.B.emb w)) * (y.map (d.B.emb w).1)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_map, map_incM']

theorem T_D_vac (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = vacF R g) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u) Φ) X = (∑ w, Sw (d.A.J.map (d.B.emb w).1) ((R.fr w)⁻¹).1 (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) ((d.b⁻¹).1.map (d.B.emb w).1) (d.cw w X) (d.cw w u)) * vacF R g X := by
  obtain ⟨tA, htA⟩ := first_frame_half_eq_mul (d := d)
  set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := at_mul hu _
  have h1 : At (evI F) (W.toCols₁ * tAᵀ) := at_mul (at_toCols₁ hWa) _
  have h2 : At (evI F) W.toCols₂ := at_toCols₂ hWa
  have e1 : W.toCols₁ * (b1 d)ᵀ = (W.toCols₁ * tAᵀ) * (dg d)ᵀ := by
    rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  have hs := split u
  rw [← hW, e1] at hs
  have hsplitD : Box.D (d.dd.e u) Φ = Box.D (d.dd.e ((W.toCols₁ * tAᵀ) * (dg d)ᵀ)) Φ +
      Box.D (d.dd.e (W.toCols₂ * (b2 d)ᵀ)) Φ := by
    conv_lhs => rw [hs]
    rw [map_add (f := _), Box.D_add_left]
  rw [hsplitD, T_add, T_D_dg hΦ h1, hT]
  have hder := theta_derivative_second_frame hΦ h2 X
  rw [hT] at hder
  rw [(vacF_deriv R g X W.toCols₂).unique hder |>.symm]

  have hmX : ∀ w, (X * (b2 d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := fun w => by
    rw [map_mul_incM_transpose_eq]; rfl
  have hmW : ∀ w, W.map (piInf (d.B.emb w)) = d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ := fun w => by
    rw [hW, map_mul_incM_transpose_eq]; rfl
  have hmW1 : ∀ w, (W.toCols₁ * (b1 d)ᵀ).map (piInf (d.B.emb w)) =
      (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁ * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := fun w => by
    rw [map_mul_incM_transpose_eq, ← hmW]; rfl
  have hmW2 : ∀ w, d.cw w W.toCols₂ = (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₂ := fun w => by
    rw [← hmW]; rfl
  have hm : mZ d (W.toCols₁ * tAᵀ) X = ∑ w, -(2 * (T1 (d.A.J.map (d.B.emb w).1) (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) (d.cw w X) ((d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁)).re) := by
    rw [mZ, ← e1, trace_sp]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmX w, hmW1 w]
    rfl
  rw [hm]
  simp only [hmW2, Sw, T2]
  rw [Finset.sum_mul]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem vac_rel (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = vacF R g) {u u' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (hu' : At (evI F) u') (hr : Box.Rel d.B.emb (fun _ => 1) (thA R) (thB d R.ε) u u') (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u') Φ) X = Complex.I * d.T (Box.D (d.dd.e u) Φ) X := by
  rw [T_D_vac R g hΦ hT hu' X, T_D_vac R g hΦ hT hu X, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfi : (R.fr w).1 * ((R.fr w)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Sw_rel e2 hfi (frame_form R w) (R.hfr w) R.hζ (d.cw w X) (d.cw w u) (d.cw w u') (hr w)

end PositivityTheory.SiegelWeilFormula.KK

end
