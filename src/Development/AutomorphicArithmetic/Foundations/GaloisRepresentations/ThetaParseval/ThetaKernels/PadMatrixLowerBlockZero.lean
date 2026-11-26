module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.NbarConj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaEps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsClosedSiegelParabolic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def emS_k : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em
def padM_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c
theorem emS_inj_k : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
theorem padM_emS_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = M a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_left h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padM_out_row_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padM_out_col_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem mem_out_k {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
theorem em_ne_k (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩
theorem not_inl_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inl, Sum.inl.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
theorem not_inr_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.inr.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
theorem inFrame_j_k (g : G2 σ L.Y) : inFrame d.b (L.j g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ h1]
      exact (L.j_out g r (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) c).1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ r h1]
      exact (L.j_out g c (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) r).2
theorem sub_mem_nA_k (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 : β.1 ∈ kfour.nCond σ d.n ε := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond (σ := σ) L.em β.1 h1
def prj_k : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.sub_mem_nA_k L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl
theorem prj_val_k (β : nA σ d.Y d.b) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1 = β.1.submatrix L.em L.em := rfl
theorem continuous_prj_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.matrix_submatrix L.em L.em
theorem pad_matrix_lower_block_zero (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ = 0) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
    simp
  · by_cases hk : k = L.i₀
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L M _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
      simp
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L M (Sum.inr a) (Sum.inl a')
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2
theorem embedding_lower_block_zero {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_matrix_lower_block_zero L _ ((kunf.isPar_frame ht₀ x t).1 ht).1
theorem j_par_k {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t⁻¹, ht.inv⟩
  have hPQ : P * Q = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hQP : Q * P = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have e1 := upper_block_mul_of_lower_zero hQ hPQ
  have e2 := upper_block_mul_of_lower_zero hP hQP
  set T0 := incM F t₁.1
  set Ti := incM F (t₁⁻¹).1
  have hT : T0 * Ti = 1 := by
    show incM F t₁.1 * incM F (t₁⁻¹).1 = 1
    rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₁⁻¹).1 * incM F t₁.1 = 1
    rw [← kunf.incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  let t' : GL (Fin d.n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * Q.toBlocks₁₁ * Ti, by
      calc T0 * P.toBlocks₁₁ * Ti * (T0 * Q.toBlocks₁₁ * Ti) = T0 * (P.toBlocks₁₁ * (Ti * T0) * Q.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e1, Matrix.mul_one, hT], by
      calc T0 * Q.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti) = T0 * (Q.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e2, Matrix.mul_one, hT]⟩
  exact mem_parabolic_GL2_iff.2 ⟨t', (kunf.isPar_frame ht₁ (L.j g) t').2 ⟨hP, rfl⟩⟩
def padE_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c
theorem padM_incM_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (incM F N) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N) := by
  ext r c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
theorem j_rat_k {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hf, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k]
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := by
  apply d.inFrame_inj
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_iota_pf (y : GR d.n) : d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  calc d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by rw [R.at_w w y, Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b w₀) = wM d.n ((ε : ℤ) : ℂ) := by
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [hW]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, wM, Matrix.one_apply] <;> split_ifs <;> simp
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt (x : Matrix (Fin d.n) (Fin d.n) ℂ) (hx : xᴴ = x) : GR d.n :=
  ⟨⟨nU x, nU (-x), by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one],
    by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩,
    by
      show InG (nU x)
      simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hx]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.nbar_conj_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, x, hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.oppositeUnipotent_weylConj {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ y' : GR d.n, mR y' = nU ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
def sM_k (b : Fin L.n → AE F E) : d.G := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.elt_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b))
def pb_k (β : nA σ d.Y d.b) : Fin L.n → AE F E := fun j => β.1 L.i₀ (L.em j)
def pa_k (δ : E) (β : nA σ d.Y d.b) : AF F := ellA δ (β.1 L.i₀ L.i₀)
def eisensteinSecondTerm (Φ : d.G → ℂ) (g : d.G) : ℂ := ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, Φ (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fockMem_k : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.fock_le_k d R, fun w Ψ hΨ => ⟨fun P => _root_.PositivityTheory.SiegelWeilFormula.KFock.away_tens_k R w Ψ hΨ P, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ⟩, fun w f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.fock_dec_k R w f hf⟩
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d (Φ - Φ') Φ'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_sub_k, e, sub_self]))
theorem linLift_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {V : Type} [AddCommGroup V] [Module ℂ V] (t : V →ₗ[ℂ] (Mx F E d.m d.n → ℂ))
    (ht : ∀ v, t v ∈ d.schM) : ∃ φ : V →ₗ[ℂ] d.Fn, ∀ v, φ v ∈ d.sch ∧ d.T (φ v) = t v := by
  choose φ0 hφ0 using fun v => (hB F E σ d).2.1 (t v) (ht v)
  refine ⟨{ toFun := φ0, map_add' := fun v v' => ?_, map_smul' := fun a v => ?_ }, fun v => hφ0 v⟩
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (v + v')).1 (d.sch.add_mem (hφ0 v).1 (hφ0 v').1) ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add (f := _)]
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1) ?_
    rw [RingHom.id_apply, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k, (hφ0 _).2, (hφ0 _).2, map_smul]
def tensP_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : PX d.m d.n →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun P := R.tens w (fP P) Ψ
  map_add' P Q := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
theorem liftEx_of_k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := by
  intro hB hF F E _ _ _ _ _ σ d R w Ψ hΨ
  obtain ⟨φ, hφ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.linLift_k hB d (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensP_k R w Ψ) fun P => (hF F E σ d R).1 (((hF F E σ d R).2.1 w Ψ hΨ).1 P)
  exact ⟨φ, hφ⟩
theorem liftEx_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_of_k hB _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
theorem liftSw1_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (_root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.om_sch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch := fun x Φ hΦ =>
  d.ok.dbl.weil.2.1.pres x Φ hΦ
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_zero : d.T 0 = 0 := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (0 : d.Fn) = 0 := fun p => by
    funext x
    simp [schr]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, h, map_zero, Pi.zero_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_inj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0 := fun Φ hΦ h => (hT.1 F E σ d).2.2 Φ hΦ h
end SD
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc_surj (w : InfinitePlace F) : ∀ (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ), ∃ Z : Mx F E d.m d.n,
    (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0 ∧ R.loc w (X + Z) = u := by
  intro X u
  obtain ⟨ins, h1, h2, h3⟩ := d.exists_insW w
  set M : Matrix (Fin d.m) (Fin d.n) ℂ := (R.fr w).1 * (Matrix.of u).map star - d.cw w X with hM
  refine ⟨M.map ins, fun w' hw' => ?_, ?_, ?_⟩
  · ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h2 w' hw']
  · ext i j
    simp [h3]
  · have hc : d.cw w (X + M.map ins) = (R.fr w).1 * (Matrix.of u).map star := by
      have : d.cw w (M.map ins) = M := by
        ext i j
        simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h1]
      rw [show d.cw w (X + M.map ins) = d.cw w X + d.cw w (M.map ins) from by
        ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw], this, hM]
      abel
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, hc, ← Matrix.mul_assoc]
    rw [show ((R.fr w)⁻¹).1 * (R.fr w).1 = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], Matrix.one_mul]
    ext i j
    simp
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR {p q r : Type} [Fintype q] (w' : InfinitePlace F) (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w' (A * B) = d.cw w' A * d.cw w' B :=
  Matrix.map_mul (f := piInf (d.B.emb w'))
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_loc (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have e : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [e, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_gram (X : Mx F E d.m d.n) :
    d.cw w (d.gram X X) = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, R.cw_loc w X]
  exact gram_loc _ _ _ _ hζ0 (R.hfr w) _
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.psi_nU (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hb : bᴴ = b) (β : Matrix (Fin d.n) (Fin d.n) (AE F E))
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
    rw [hz, Algebra.smul_def, map_mul, map_neg, map_neg, piInf_half, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.diag, map_sum]
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
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Mat
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Semiring R]
end Mat
theorem inFrame_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k]
theorem quasiCharacter_conj_embed {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : L.sd.G) : IdentityOnLastRowsCols L.i₀ (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v
theorem q_conj'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (g : L.sd.G) :
    IsQ F E L.i₀ (inFrame d.b (L.j g * q * (L.j g)⁻¹)) lam := by
  have hH : inFrame d.b (L.j g) * inFrame d.b (L.j g)⁻¹ = 1 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k]
  refine isQ_conj hq hH (_root_.PositivityTheory.SiegelWeilFormula.Avac.quasiCharacter_conj_embed L g) ?_
  rw [← map_inv]
  exact _root_.PositivityTheory.SiegelWeilFormula.Avac.quasiCharacter_conj_embed L g⁻¹
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd.DC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem dblJ_det_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε) : (dbl d.Y.J).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
  exact QR_det_ne E ε this.symm
def bX_k (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  d.b.1 * X * (d.b⁻¹).1
theorem bX_unitary_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    {X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E} (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)ᵀ * dbl d.Y.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X).map σ = dbl d.Y.J :=
  conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n ε) (Units.mul_inv d.b) hε hX
def ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) : d.G :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.dblJ_det_k d hε)))),
    by
      show (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X))ᵀ * dbl (incM F d.Y.J) * (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)).map (cA σ) = dbl (incM F d.Y.J)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, incM_cA, incM_alt_bis, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX]⟩
theorem ratG_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX ∈ rat2 σ d.Y :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
theorem inFrame_ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX) = incM F X := by
  show incM F (d.b⁻¹).1 * incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) * incM F d.b.1 = incM F X
  rw [← incM_mul, ← incM_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
theorem inFrame_mul_k (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := by
  show incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
    (incM F (d.b⁻¹).1 * mat2 x * incM F d.b.1) * (incM F (d.b⁻¹).1 * mat2 z * incM F d.b.1)
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
      incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 z * incM F d.b.1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem inFrame_inj_k {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := by
  have e : ∀ u : d.G, mat2 u = incM F d.b.1 * inFrame d.b u * incM F (d.b⁻¹).1 := fun u => by
    simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show mat2 x = mat2 z
  rw [e x, e z, h]
end PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DM PositivityTheory.SiegelWeilFormula.Krd.DC in
theorem PositivityTheory.SiegelWeilFormula.Krd.denseW_k : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_mem_k d hε X hX, _, hXO, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩ with hy'
  set A := inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by
    rw [hA, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k, inv_mul_cancel_right, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_ratG_k]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, Matrix.mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, Matrix.mul_one] at e
    have := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
    simpa only [← Matrix.mul_assoc, dZ_inv_mul h0, Matrix.one_mul] using this
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hC, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d _ (R.ι w y''), _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d (R.ι w y''), ← hA]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases hw : w' = w
    · subst hw; rw [hAw, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y'' hw, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GramSuppCmpK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def insW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : ℂ) : AE F E := (Place.exists_sec d.cm d.B.emb).choose (Pi.single w z)
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F)
theorem insW_self_k (z : ℂ) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = z := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_same]
theorem insW_ne_k {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) : piInf (d.B.emb w') (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_of_ne hw]
theorem insW_fin_k (z : ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.2.1]
theorem insW_add_k (z z' : ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w (z + z') = _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z + _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z' := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, Pi.single_add, h.2.2.2.1]
end
def insL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : Mx F E d.m d.n :=
  ((R.fr w).1 * (Matrix.of v).map star).map (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w)
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def Supp_k (Z : Mx F E d.m d.n) : Prop := (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0
theorem cw_insL_k (v : Fin d.m → Fin d.n → ℂ) : d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_self_k]
theorem insL_supp_k (v : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_ne_k d w hw', Matrix.zero_apply]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.smul_apply, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_fin_k, Matrix.zero_apply]
theorem insL_add_k (v v' : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (v + v') = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp
  unfold _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k
  rw [e]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_add_k]
theorem insL_zero_k : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = 0 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k R w 0 0
  rw [add_zero] at h
  calc _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by abel
    _ = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by rw [← h]
    _ = 0 := sub_self _
theorem insL_loc_k {Z : Mx F E d.m d.n} (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z) = Z := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · by_cases hw : w' = w
    · rw [hw]
      change d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w Z
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k]
      have h2 : (Matrix.of (R.loc w Z)).map star = ((R.fr w)⁻¹).1 * d.cw w Z := by
        ext i j
        exact star_star _
      rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · change d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w' Z
      rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).1 w' hw, hZ.1 w' hw]
  · rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).2, hZ.2]
theorem rest_inv_k (X Z : Mx F E d.m d.n) (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) :
    (X + Z) - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w (X + Z)) = X - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w X) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k d R w X Z, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_loc_k R w hZ]
  abel
end
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem psi_add_right_k (ε : ℤˣ) (X Z Z' : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  have e : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem psi_add_left_k (ε : ℤˣ) (X X' Z : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  have e : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem cw_gram_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  have hJ : (incM F d.A.J).map (piInf (d.B.emb w)) = d.A.J.map (d.B.emb w).1 := by
    ext i j
    simp [incM, PositivityTheory.ThKG.Tow.Levi.piInf_incl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Place.map_cA d.cm (d.B.emb w) Z, hJ]
theorem gram_supp_cmp_k (w : InfinitePlace F) {Z' Z : Mx F E d.m d.n} (hZ' : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z') (hZ : d.cw w Z = 0) :
    d.gram Z' Z = 0 := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · change d.cw w' (d.gram Z' Z) = d.cw w' 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k]
    by_cases hw : w' = w
    · subst hw
      rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  · unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]
    simp
theorem psi_zero_gram_k (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : Mx F E d.n d.n)) = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
end
theorem zeta_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ ≠ 0 := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_loc_k (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have h2 : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
theorem frJ_k : (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  have h := R.hfr w
  calc (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star
      = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R), one_smul]
    _ = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by rw [h, smul_smul]
end
theorem psi_at_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (ε : ℤˣ) (M : Mx F E d.n d.n)
    (hM1 : ∀ w', w' ≠ w → d.cw w' M = 0) (hM2 : finOne F • M = 0) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have ptr : ∀ u, piInf (d.B.emb u) M.trace = (d.cw u M).trace := fun u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
  rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _ ?_ ?_, map_zsmul, ptr, zsmul_eq_mul]
  · rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero]
  · intro u hu
    rw [map_zsmul, ptr, hM1 u hu, Matrix.trace_zero, smul_zero]
theorem kernel_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ε : ℤˣ) (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  have hM1 : ∀ w', w' ≠ w → d.cw w' (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) = 0 := by
    intro w' hw
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u) = 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.mul_smul]
    have : finOne F • (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) = (finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) := by
      ext i j
      simp [map_smul]
    rw [this, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).2]
    simp
  have e1 : d.cw w (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) =
      (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w X, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k, Matrix.transpose_mul]
    have h3 : ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u := by
      ext i j
      simp [Matrix.mul_apply]
    have h4 : ((Matrix.of (R.loc w X)).map star)ᵀ = (Matrix.of (R.loc w X))ᴴ := rfl
    rw [h3, h4]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.KW.frJ_k, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_at_w_k d w ε _ hM1 hM2, e1, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have e2 : -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) := by
    push_cast
    ring
  rw [e2, Complex.re_ofReal_mul]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousPhzK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem continuous_phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  have ha := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_a'_k d
  have e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) := by
    funext x; rw [_root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [e]
    exact (Complex.continuous_ofReal.comp ha).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d x))
  exact h1.mul hf
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
end
