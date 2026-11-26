module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DilExPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem nbw1 (d : SD σ) (R : RD d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb)
    (xN : GR d.n) (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hxN : mR xN = nU h) :
    ∃ β₁ : nA σ d.Y d.b, R.ι w xN = nb β₁ ∧ d.cw w β₁.1 = R.ζ • h ∧ (∀ u, u ≠ w → d.cw u β₁.1 = 0) ∧
      finOne F • β₁.1 = 0 := by
  have hP : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w xN)).toBlocks₁₂ 0 1 := by
    apply Place.cw_ext d
    · intro u
      rw [KSing.UnitaryGroupBasics.cw_fromBlocks, KSing.UnitaryGroupBasics.cw_toBlocks₁₂]
      by_cases hu : u = w
      · subst hu
        rw [KSing.UnitaryGroupBasics.cw_unip d R u xN _ hxN, Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u xN hu, KSing.UnitaryGroupBasics.toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, KSing.UnitaryGroupBasics.fin_toBlocks₁₂, R.off_f w xN, ← KSing.UnitaryGroupBasics.fin_toBlocks₁₂, KSing.UnitaryGroupBasics.toBlocks₁₂_one,
        smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  let β₁ : nA σ d.Y d.b := ⟨(inFrame d.b (R.ι w xN)).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w xN, hP⟩⟩
  have hB : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 β₁.1 0 1 := hP
  refine ⟨β₁, KSing.UnitaryGroupBasics.inFrame_inj d (by rw [hN]; exact hB), ?_, fun u hu => ?_, ?_⟩
  · have e := KSing.UnitaryGroupBasics.cw_unip d R w xN _ hxN
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_w w u xN hu
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_f w xN
    rw [hB, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)

def betaW (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • d.cw w T.1.1))

theorem character_w1_trace_exp (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b)
    (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hh : h.IsHermitian) (hBw : d.cw w β₁.1 = R.ζ • h)
    (hBu : ∀ u, u ≠ w → d.cw u β₁.1 = 0) (hBf : finOne F • β₁.1 = 0) :
    d.B.ψ (d.tt (T.1.1 * β₁.1)) = Complex.exp (Complex.I * (betaW d R w T * h).trace) := by
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := KSing.UnitaryGroupBasics.form_w d R w x
      rw [hx, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [SD.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [SD.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [SD.cw] at ea ⊢
      linear_combination -ea
  unfold betaW
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT ⊢
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  have hf : finOne F • (T.1.1 * β₁.1).trace = 0 := by
    rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf, Matrix.mul_zero, Matrix.trace_zero]
  have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * β₁.1).trace = 0 := fun u hu => by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBu u hu, Matrix.mul_zero, Matrix.trace_zero]
  have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * β₁.1).trace hf hw
  have hw' : piInf (d.B.emb w) (T.1.1 * β₁.1).trace = ((R.ζ • Tw) * h).trace := by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBw, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
  have hreal : ((((R.ζ • Tw) * h).trace).re : ℂ) = ((R.ζ • Tw) * h).trace := by
    have hs : star (((R.ζ • Tw) * h).trace) = ((R.ζ • Tw) * h).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, hh.eq, Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.1 hs
  have eR : ((((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • Tw))) * h).trace =
      ((2 * Real.pi : ℝ) : ℂ) * (-2 * (R.ζ • Tw * h).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  unfold SD.tt
  rw [hz, hw', eR]
  generalize (R.ζ • Tw * h).trace = c at hreal ⊢
  congr 1
  push_cast
  rw [hreal]
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionDilationExp
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dilV_off (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (k : Fin n ⊕ Fin n)
    (hk : k ∉ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))) : dilV h w i₀ τ k = 1 := by
  haveI := h.1
  rcases k with j | j
  · have hj : j ≠ i₀ := fun hj => hk (by subst hj; simp)
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [if_neg hj]
  · have hj : j ≠ i₀ := fun hj => hk (by subst hj; simp)
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [if_neg hj]

theorem j_comm_dil {d : SD σ} (R : RD d) (L : LD d) (w : InfinitePlace F) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single L.i₀ 1) τ y) (g : L.sd.G) : L.j g * R.ι w y = R.ι w y * L.j g := by
  have hPQ := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv (F := F) d.b
  have hQP := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul (F := F) d.b
  have key : ∀ x : d.G, mat2 x = incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x * incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
    intro x
    show mat2 x = incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * mat2 x * incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) * incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)
    simp only [Matrix.mul_assoc, hPQ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hM := L.j_out g
  have hcomm : inFrame d.b (L.j g) * inFrame d.b (R.ι w y) = inFrame d.b (R.ι w y) * inFrame d.b (L.j g) := by
    rw [inFrame_dil R w L.i₀ τ y hy]
    ext u v
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hS : u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) ∨ v ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
    · have h1 : inFrame d.b (L.j g) u v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) u v := by
        rcases hS with hu | hv
        · exact (hM u hu v).1
        · exact (hM v hv u).2
      rw [h1]
      by_cases huv : u = v
      · subst huv
        exact mul_comm _ _
      · rw [Matrix.one_apply_ne huv, zero_mul, mul_zero]
    · obtain ⟨hu, hv⟩ := not_or.mp hS
      rw [dilV_off _ w L.i₀ τ u hu, dilV_off _ w L.i₀ τ v hv, mul_one, one_mul]
  apply Subtype.ext
  apply Units.ext
  show mat2 (L.j g) * mat2 (R.ι w y) = mat2 (R.ι w y) * mat2 (L.j g)
  rw [key (L.j g), key (R.ι w y)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) (incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), hQP, Matrix.one_mul,
    ← Matrix.mul_assoc (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) (incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), hQP, Matrix.one_mul,
    ← Matrix.mul_assoc (inFrame d.b (L.j g)), hcomm, Matrix.mul_assoc]

theorem l_eq_T_zero (d : SD σ) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) : d.l Ψ = d.T Ψ 0 := by
  have hk := d.ok.dbl.kill 0 Ψ hΨ
  show d.l Ψ = d.l (d.dd.rho d.B.ψ (0 * (incM F (↑d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E).toCols₂).transpose) Ψ)
  convert hk.symm using 3
  exact (Matrix.zero_mul _).trans (Matrix.zero_mul _).symm

theorem dilV_mul (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (j : Fin n) :
    dilV h w i₀ τ (Sum.inl j) * dilV h w i₀ τ (Sum.inr j) = 1 := by
  haveI := h.1
  show (if j = i₀ then _ else (1 : AE F E)) * (if j = i₀ then _ else (1 : AE F E)) = 1
  by_cases hj : j = i₀
  · rw [if_pos hj, if_pos hj, ← map_mul, adr_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      adr_one, map_one]
  · rw [if_neg hj, if_neg hj, mul_one]

theorem dilV_mul' (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (j : Fin n) :
    dilV h w i₀ τ (Sum.inr j) * dilV h w i₀ τ (Sum.inl j) = 1 := by
  rw [mul_comm]
  exact dilV_mul h w i₀ τ j

def dilT (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) : GL (Fin n) (AE F E) :=
  ⟨Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inl j), Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inr j), by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j; exact dilV_mul h w i₀ τ j, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j; exact dilV_mul' h w i₀ τ j⟩

theorem det_dilT (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) :
    haveI := h.1
    Matrix.GeneralLinearGroup.det (dilT h w i₀ τ) = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
  haveI := h.1
  apply Units.ext
  show (Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inl j)).det =
    algebraMap (AF F) (AE F E) (adr w (Real.exp τ))
  rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
  · show (if i₀ = i₀ then _ else (1 : AE F E)) = _
    rw [if_pos rfl]
  · intro j _ hj
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [if_neg hj]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem inFrame_dil' {d : SD σ} (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (dilT d.cm w i₀ τ).1 0 0 (dilT d.cm w i₀ (-τ)).1 := by
  rw [inFrame_dil R w i₀ τ y hy]
  show _ = Matrix.fromBlocks (Matrix.diagonal fun j => dilV d.cm w i₀ τ (Sum.inl j)) 0 0
    (Matrix.diagonal fun j => dilV d.cm w i₀ (-τ) (Sum.inl j))
  rw [Matrix.fromBlocks_diagonal]
  congr 1

theorem section_dilation_exp (H : Hyps) {d : SD σ} (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (h : d.G) :
    d.sec0 Φ (R.ι w y * h) = Complex.exp (τ * d.m) * d.sec0 Φ h := by
  haveI := d.cm.1
  have hφ : d.om h Φ ∈ d.sch := d.ok.dbl.weil.2.1.toIsSplitting.pres h Φ hΦ
  have hφ' : d.om (R.ι w y) (d.om h Φ) ∈ d.sch := d.ok.dbl.weil.2.1.toIsSplitting.pres _ _ hφ
  have hT := (H.tAll.2.1 F E σ d (d.om h Φ) hφ).2.1 (R.ι w y) (dilT d.cm w i₀ τ) (dilT d.cm w i₀ (-τ))
    (inFrame_dil' R w i₀ τ y hy) 0
  show d.l (d.om (R.ι w y * h) Φ) = Complex.exp (↑τ * ↑d.m) * d.l (d.om h Φ)
  rw [map_mul, Module.End.mul_apply, l_eq_T_zero d _ hφ', hT, Matrix.zero_mul, ← l_eq_T_zero d _ hφ, det_dilT]
  erw [chi_adrU d w τ]
  erw [absE_adrU d.cm w τ]
  rw [one_mul, ← Real.exp_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
end
