module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.AddFDOfCover

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def nilpotentFrameMatrix {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne {d : SD σ} (L : LD d) (j : Fin L.n) : L.em j ≠ L.i₀ := ((L.rng (L.em j)).2 ⟨j, rfl⟩)

theorem nilpotent_frame_mul_zero {d : SD σ} (L : LD d) (u v : Fin L.n → AE F E) : nilpotentFrameMatrix L u * nilpotentFrameMatrix L v = 0 := by
  simp only [nilpotentFrameMatrix, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  exact em_ne L _

theorem continuous_nilpotentFramePart {d : SD σ} (L : LD d) : Continuous (nilpotentFrameMatrix L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have : (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact (continuous_apply j).smul continuous_const

def muF {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 (((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ))

def muF' {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 - nilpotentFrameMatrix L u) 0 0 (((1 + nilpotentFrameMatrix L u)ᵀ).map (cA σ))

theorem one_add_mul_one_sub {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) :
    (1 + nilpotentFrameMatrix L u) * (1 - nilpotentFrameMatrix L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, nilpotent_frame_mul_zero, add_zero, add_sub_cancel_right]

theorem muF_mul {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : muF L u * muF' L u = 1 := by
  have e1 := one_add_mul_one_sub L u
  simp only [muF, muF', Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]

theorem inFrame_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = muF L u := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 a' at ha
  have hf := kunf.frame_eq hε (uM u)
  rw [ha] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - nilpotentFrameMatrix L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - nilpotentFrameMatrix L u)ᵀ * (1 + nilpotentFrameMatrix L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, one_add_mul_one_sub, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - nilpotentFrameMatrix L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  have e3 : a' = ((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ) := by
    rw [← e2]
    ext i j
    simp [Matrix.map_apply, kfour.cA_cA' σ hσ]
  rw [ha, e3]
  rfl

theorem continuous_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := continuous_nilpotentFramePart L
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hc : Continuous (muF (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const
      (hcA.comp (continuous_const.sub hN).matrix_transpose)
  have hc' : Continuous (muF' (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const
      (hcA.comp (continuous_const.add hN).matrix_transpose)
  have h1 : Continuous fun u => incM F d.b.1 * muF L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun u => incM F d.b.1 * muF' L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun u => ?_
    show _ = mat2 (uM u)
    rw [kunf.matrix_eq_inFrame_conj d.b, inFrame_uM L h]
  · refine h2.congr fun u => ?_
    show _ = mat2 (uM u)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, inFrame_uM L h,
      Matrix.inv_eq_right_inv (muF_mul L u)]

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.BMat
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

def eA : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)

def elt (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1

def uA (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)

def uMat (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (uA L u) 0 0 ((uA L (-u))ᵀ.map (cA σ))

def bMat (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 β 0 1

def sB (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(eA R * cA σ (b j))))

def aB (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E := E) (AF F) δ)

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_add {k : ℕ} (x y : Fin k → E) :
    GlobalTheory.ThK.incV F (x + y) = GlobalTheory.ThK.incV F x + GlobalTheory.ThK.incV F y := by
  funext i
  simp [GlobalTheory.ThK.incV, map_add (f := _)]

theorem incV_zero {k : ℕ} : GlobalTheory.ThK.incV F (0 : Fin k → E) = 0 := by
  funext i
  simp [GlobalTheory.ThK.incV]

theorem incV_neg {k : ℕ} (x : Fin k → E) : GlobalTheory.ThK.incV F (-x) = -GlobalTheory.ThK.incV F x := by
  funext i
  simp [GlobalTheory.ThK.incV, map_neg]

theorem mem_ratVec {k : ℕ} {v : Fin k → AE F E} :
    v ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)) ↔ ∃ x, GlobalTheory.ThK.incV F x = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, incV_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, incV_add X Z⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, incV_neg X⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩

theorem ratVec_cocompact (k : ℕ) : ∃ K : Set (Fin k → AE F E), IsCompact K ∧
    ∀ v, ∃ γ ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)), γ + v ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => C, isCompact_univ_pi fun _ => hC, fun v => ?_⟩
  choose X hX using fun i => hCx (v i)
  exact ⟨GlobalTheory.ThK.incV F X, mem_ratVec.2 ⟨X, rfl⟩, fun i _ => hX i⟩

theorem ratVec_discrete (k : ℕ) :
    DiscreteTopology (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  obtain ⟨V, hV, hV0⟩ := kfour.exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, (fun v : Fin k → AE F E => v i) ⁻¹' V) ∈ 𝓝 (0 : Fin k → AE F E) := by
    refine Filter.iInter_mem.2 fun i => ?_
    exact (continuous_apply i).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage continuous_subtype_val using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hx
    have h2 : X = 0 := by
      funext i
      exact hV0 _ (Set.mem_iInter.1 (hOW h) i)
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext incV_zero)

theorem ratVec_countable (k : ℕ) :
    Countable (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  haveI := kfour.countable_E (E := E)
  have h : (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))) :
      Set (Fin k → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))).mono fun v hv => ?_
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hv
    exact ⟨X, rfl⟩
  exact h.to_subtype

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end
