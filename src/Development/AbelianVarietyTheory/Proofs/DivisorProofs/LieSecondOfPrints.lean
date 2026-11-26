module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledFockVacuumEqSmulVacuumMulConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceSplittingConstantHalfRealPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousDblIncl
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Compare

section Emb

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {β : Type} [Fintype β] [DecidableEq β]

def blkGL : GL β E →* GL (β ⊕ β) E where
  toFun g := ⟨Matrix.fromBlocks (g : Matrix β β E) 0 0 1, Matrix.fromBlocks ((g⁻¹ : GL β E) : Matrix β β E) 0 0 1,
    by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one], by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩
  map_one' := by ext : 1; simp [Matrix.fromBlocks_one]
  map_mul' a b := by ext : 1; simp [Matrix.fromBlocks_multiply]

def dblIncl (JB : Matrix β β E) : UG c JB →* UG c (dbl JB) :=
  ((blkGL (β := β) (E := E)).comp (UG c JB).subtype).codRestrict (UG c (dbl JB)) fun g => by
    have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
    show (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl JB *
      (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl JB
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, dbl, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hg, Matrix.map_one _ (map_zero c) (map_one c)]

theorem dblIncl_val (JB : Matrix β β E) (g : UG c JB) :
    (((dblIncl c JB g : UG c (dbl JB)) : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) =
      Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := rfl

theorem continuous_blkGL [TopologicalSpace E] : Continuous (blkGL (β := β) (E := E)) := by
  rw [Units.continuous_iff]
  constructor
  · exact Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const continuous_const
  · exact Continuous.matrix_fromBlocks Units.continuous_coe_inv continuous_const continuous_const continuous_const

theorem continuous_dblIncl [TopologicalSpace E] (JB : Matrix β β E) : Continuous (dblIncl c JB) :=
  Continuous.subtype_mk (continuous_blkGL.comp continuous_subtype_val) _

end Emb

end GlobalTheory.RealLift.Compare

namespace GlobalTheory.RealLift.Compare

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sumPl_tprod (L : ι → Module.End ℂ V) (v : V) (μ : ι → ℂ) (h : ∀ w, L w v = μ w • v) :
    sumPl (V := fun _ => V) L (PiTensorProduct.tprod ℂ fun _ => v) = (∑ w, μ w) • PiTensorProduct.tprod ℂ fun _ => v := by
  rw [sumPl, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [atPl, PiTensorProduct.map_tprod]
  have e : (fun i => (Function.update (fun i => (LinearMap.id : V →ₗ[ℂ] V)) w (L w) i) v) =
      Function.update (fun _ => v) w (μ w • v) := by
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  rw [e, MultilinearMap.map_update_smul, Function.update_eq_self]
  rfl

end Tensor

end GlobalTheory.RealLift.Compare

namespace GlobalTheory.RealLift.Compare

section Lines

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ}

def firstCopy (R S : ℕ) : Ix (R + S) (S + R) → ℂ :=
  Sum.elim (fun p => Sum.elim (fun _ => Complex.I) (fun _ => 0) (finSumFinEquiv.symm p))
    (fun q => Sum.elim (fun _ => Complex.I) (fun _ => 0) (finSumFinEquiv.symm q))

def genDbl (R S : ℕ) (w₀ : InfinitePlace F) (w : InfinitePlace F) : Mat (R + S) (S + R) :=
  Matrix.diagonal fun j => if w = w₀ then firstCopy R S j else 0

theorem lines_dbl {JB : Matrix β β (AE F E)} {γ : Multiplicative ℝ →* UG (cA σ) JB} (hγ : γ ∈ RLines (σ := σ) JB) :
    (dblIncl (cA σ) JB).comp γ ∈ RLines (σ := σ) (dbl JB) := by
  refine ⟨(continuous_dblIncl (cA σ) JB).comp hγ.1, fun t => ?_⟩
  have h := hγ.2 t
  have e : ((((dblIncl (cA σ) JB).comp γ) t : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)).1 - 1 =
      Matrix.fromBlocks (((γ t : UG (cA σ) JB) : GL β (AE F E)).1 - 1) 0 0 0 := by
    rw [MonoidHom.comp_apply, dblIncl_val]
    ext i j
    rcases i with a | a <;> rcases j with b | b <;> simp [Matrix.one_apply]
  intro u hu
  change u • (((((dblIncl (cA σ) JB).comp γ) t : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)).1 - 1) = 0
  have h' : u • (((γ t : UG (cA σ) JB) : GL β (AE F E)).1 - 1) = 0 := h u hu
  rw [e, Matrix.fromBlocks_smul, h']
  simp

theorem gen_dbl (τ : ∀ w : InfinitePlace F, EmbOver E w) {JB : Matrix β β (AE F E)} (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (w₀ : InfinitePlace F) (γ : Multiplicative ℝ →* UG (cA σ) JB) (z : ℝ → (AE F E)ˣ)
    (hz : ∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) = (z t : AE F E) • (1 : Matrix β β (AE F E)))
    (hpi : ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : AE F E) = if w = w₀ then Complex.exp (t * Complex.I) else 1) :
    IsGen τ (fun w => dblM (C w)) ((dblIncl (cA σ) JB).comp γ) (genDbl R S w₀) := by
  intro t w
  have e1 : ((((dblIncl (cA σ) JB).comp γ) (Multiplicative.ofAdd t) : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)).1 =
      Matrix.fromBlocks ((z t : AE F E) • (1 : Matrix β β (AE F E))) 0 0 1 := by
    rw [MonoidHom.comp_apply, dblIncl_val, ← hz t]
  change ((((((dblIncl (cA σ) JB).comp γ) (Multiplicative.ofAdd t) : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)).1).map (piInf (τ w))) * dblM (C w) = dblM (C w) * NormedSpace.exp (t • genDbl R S w₀ w)
  rw [e1, genDbl, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  have e2 : (Matrix.fromBlocks ((z t : AE F E) • (1 : Matrix β β (AE F E))) (0 : Matrix β β (AE F E)) 0
      (1 : Matrix β β (AE F E))).map (piInf (τ w)) =
      Matrix.fromBlocks ((piInf (τ w) (z t : AE F E)) • (1 : Matrix β β ℂ)) (0 : Matrix β β ℂ) 0 (1 : Matrix β β ℂ) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  rw [e2, hpi t w]
  ext i j
  rw [Matrix.mul_diagonal]
  rcases i with b | b <;> rcases j with p | q
  · rcases h : finSumFinEquiv.symm p with r | s <;> by_cases hw : w = w₀ <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, firstCopy, h, hw, Matrix.one_apply,
        ← Complex.exp_eq_exp_ℂ, Pi.coe_exp, mul_comm]
  · rcases h : finSumFinEquiv.symm q with s | r <;> by_cases hw : w = w₀ <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, firstCopy, h, hw, Matrix.one_apply,
        ← Complex.exp_eq_exp_ℂ, Pi.coe_exp, mul_comm]
  · rcases h : finSumFinEquiv.symm p with r | s <;> by_cases hw : w = w₀ <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, firstCopy, h, hw, Matrix.one_apply,
        ← Complex.exp_eq_exp_ℂ, Pi.coe_exp, mul_comm]
  · rcases h : finSumFinEquiv.symm q with s | r <;> by_cases hw : w = w₀ <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, firstCopy, h, hw, Matrix.one_apply,
        ← Complex.exp_eq_exp_ℂ, Pi.coe_exp, mul_comm]

end Lines

end GlobalTheory.RealLift.Compare

namespace GlobalTheory.RealLift.Compare

section Weights

variable {F : Type} [Field F] [NumberField F]

theorem sum_signed_scalar (R S : ℕ) :
    ∑ c : Ix R S, Complex.I * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c = Complex.I * R - Complex.I * S := by
  simp [Fintype.sum_sum_type]; ring

theorem sum_signed_first (R S : ℕ) :
    ∑ c : Ix (R + S) (S + R), firstCopy R S c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c =
      Complex.I * R - Complex.I * S := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_one, mul_neg_one, Finset.sum_neg_distrib, firstCopy]
  rw [(finSumFinEquiv.symm).sum_comp (fun x => Sum.elim (fun _ => Complex.I) (fun _ => (0 : ℂ)) x),
    (finSumFinEquiv.symm).sum_comp (fun x => Sum.elim (fun _ => Complex.I) (fun _ => (0 : ℂ)) x)]
  simp [Fintype.sum_sum_type]; ring

theorem trace_first (R S : ℕ) : ∑ c : Ix (R + S) (S + R), firstCopy R S c = Complex.I * ((R : ℂ) + S) := by
  rw [Fintype.sum_sum_type]
  simp only [firstCopy, Sum.elim_inl, Sum.elim_inr]
  rw [(finSumFinEquiv.symm).sum_comp (fun x => Sum.elim (fun _ => Complex.I) (fun _ => (0 : ℂ)) x),
    (finSumFinEquiv.symm).sum_comp (fun x => Sum.elim (fun _ => Complex.I) (fun _ => (0 : ℂ)) x)]
  simp [Fintype.sum_sum_type]; ring

variable (hvac : ∀ (p q r s : ℕ) (D : Ix r s → ℂ), fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s))
include hvac

theorem weight_single (P Q R S : ℕ) (c : InfinitePlace F → ℂ) (w₀ w : InfinitePlace F) :
    (fockAct2 P Q R S (if w = w₀ then Complex.I • (1 : Mat R S) else 0) +
      (c w * (if w = w₀ then Complex.I • (1 : Mat R S) else 0).trace) • 1) (1 : Formalism.BasicNotions.TH.Pol P Q R S) =
    (if w = w₀ then (((P : ℂ) - Q) / 2) * (Complex.I * R - Complex.I * S) + c w₀ * (Complex.I * ((R : ℂ) + S)) else 0) •
      (1 : Formalism.BasicNotions.TH.Pol P Q R S) := by
  by_cases hw : w = w₀
  · subst hw
    simp only [if_true, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [Matrix.smul_one_eq_diagonal, hvac, sum_signed_scalar, Matrix.trace_diagonal, add_smul]
    congr 2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  · simp [hw]

theorem weight_dbl (P Q R S : ℕ) (cd : InfinitePlace F → ℂ) (w₀ w : InfinitePlace F) :
    (fockAct2 P Q (R + S) (S + R) (genDbl R S w₀ w) + (cd w * (genDbl R S w₀ w).trace) • 1)
        (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) =
    (if w = w₀ then (((P : ℂ) - Q) / 2) * (Complex.I * R - Complex.I * S) + cd w₀ * (Complex.I * ((R : ℂ) + S)) else 0) •
      (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, genDbl]
  rw [hvac, Matrix.trace_diagonal, ← add_smul]
  congr 1
  by_cases hw : w = w₀
  · subst hw
    simp only [if_true]
    rw [sum_signed_first, trace_first]
  · simp [hw]

end Weights

end GlobalTheory.RealLift.Compare

namespace GlobalTheory.RealLift.Compare

def conjS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f : V → ℂ) x n
    have e : (fun x => star (f x)) = (Complex.conjLIE : ℂ → ℂ) ∘ (f : V → ℂ) := rfl
    show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => star (f x)) x‖ ≤ C
    rw [e, h]
    exact hC x

theorem conjS_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjS f x = star (f x) := rfl

theorem compare_of (hcen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type)
    [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (w₀ : InfinitePlace F), IsCMExt F E σ →
    ∃ z : ℝ → (AE F E)ˣ, ∃ γ ∈ RLines (σ := σ) J,
      IsGen τ C γ (fun w => if w = w₀ then Complex.I • (1 : Mat R S) else 0) ∧
      (∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) = (z t : AE F E) • (1 : Matrix β β (AE F E))) ∧
      (∀ t : ℝ, At (evI F) ((z t : AE F E) - 1)) ∧
      ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : AE F E) = if w = w₀ then Complex.exp (t * Complex.I) else 1) (hvac : ∀ (p q r s : ℕ) (D : Ix r s → ℂ), fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s)) (htp : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) =
        Matrix.fromBlocks ((g : GL β (AE F E)) : Matrix β β (AE F E)) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hcm hstd hfock hres hact hactd hvb hRS w₀
  obtain ⟨z, γ, hγ, hgen, hzγ, -, hpi⟩ := hcen F E σ β R S τ JB C w₀ hcm
  have hγd := lines_dbl hγ
  have hgd := gen_dbl τ C w₀ γ z hzγ hpi
  set lam : ℂ := (((P : ℂ) - Q) / 2) * (Complex.I * R - Complex.I * S) + c w₀ * (Complex.I * ((R : ℂ) + S)) with hlam
  set lamd : ℂ := (((P : ℂ) - Q) / 2) * (Complex.I * R - Complex.I * S) + cd w₀ * (Complex.I * ((R : ℂ) + S)) with hlamd
  have hsum := sumPl_tprod (fun w => fockAct2 P Q R S (if w = w₀ then Complex.I • (1 : Mat R S) else 0) +
      (c w * (if w = w₀ then Complex.I • (1 : Mat R S) else 0).trace) • 1) 1 _
    (fun w => weight_single hvac P Q R S c w₀ w)
  have hsumd := sumPl_tprod (fun w => fockAct2 P Q (R + S) (S + R) (genDbl R S w₀ w) +
      (cd w * (genDbl R S w₀ w).trace) • 1) 1 _ (fun w => weight_dbl hvac P Q R S cd w₀ w)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum hsumd
  have hA := hact γ hγ _ hgen (PiTensorProduct.tprod ℂ fun _ => 1)
  rw [hsum, map_smul] at hA
  have hB := hactd _ hγd _ hgd (PiTensorProduct.tprod ℂ fun _ => 1)
  rw [hsumd, map_smul] at hB

  have hf₁ : Φ (PiTensorProduct.tprod ℂ fun _ => 1) ≠ 0 := fun h =>
    htp F P Q R S (hfock.1 (by rw [h, map_zero]))
  obtain ⟨y, hy⟩ : ∃ y, Φ (PiTensorProduct.tprod ℂ fun _ => 1) y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf₁ (SchwartzMap.ext hcon)
  obtain ⟨z0, hz0, hfd⟩ := hvb
  set f₁ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hf₁def
  set fd := Φd (PiTensorProduct.tprod ℂ fun _ => 1) with hfddef
  set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl
  set G : (κ ⊕ κ → Af F) → ℂ := fun u => g₀ (u ∘ Sum.inl) * g₀ (u ∘ Sum.inr) with hGdef
  have hG : G ∈ SB (κ ⊕ κ → Af F) := GlobalTheory.SchwartzBox.sb_box hg₀ hg₀
  set φ₁ : (κ → AF F) → ℂ := pureA F f₁ g₀ with hφ₁def
  set φ₂ : (κ → AF F) → ℂ := pureA F (conjS f₁) g₀ with hφ₂def
  have hφ₁ : φ₁ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f₁, g₀, hg₀, rfl⟩
  have hφ₂ : φ₂ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨conjS f₁, g₀, hg₀, rfl⟩
  have hbox : pureA F fd G = z0 • boxFun φ₁ φ₂ := by
    funext u
    simp only [pureA, boxFun, hGdef, hφ₁def, hφ₂def, Pi.smul_apply, smul_eq_mul, conjS_apply]
    rw [hfd]
    simp only [Function.comp_def]
    ring
  set x₁ : κ → AF F := ptAt y 0 with hx₁
  set xd : κ ⊕ κ → AF F := ptAt (Sum.elim y y) 0 with hxd
  have hxl : xd ∘ Sum.inl = x₁ := rfl
  have hxr : xd ∘ Sum.inr = x₁ := rfl
  have hA' := hA g₀ hg₀ (LinearMap.proj x₁) (eval_mem_adm x₁)
  have hB' := hB G hG (LinearMap.proj xd) (eval_mem_adm xd)
  simp only [LinearMap.coe_proj, Function.eval] at hA' hB'
  have hfun : (fun t : ℝ => omd (((dblIncl (cA σ) JB).comp γ) (Multiplicative.ofAdd t)) (pureA F fd G) xd) =
      fun t => z0 * (om (γ (Multiplicative.ofAdd t)) φ₁ x₁ * φ₂ x₁) := by
    funext t
    rw [hbox, map_smul, hres (γ (Multiplicative.ofAdd t)) (((dblIncl (cA σ) JB).comp γ) (Multiplicative.ofAdd t)) rfl
      φ₁ hφ₁ φ₂ hφ₂]
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, hxl, hxr]
  change HasDerivAt (fun t : ℝ => omd (((dblIncl (cA σ) JB).comp γ) (Multiplicative.ofAdd t)) (pureA F fd G) xd) (pureA F (lamd • fd) G xd) 0 at hB'
  rw [hfun] at hB'
  have hB'' := (hA'.mul_const (φ₂ x₁)).const_mul z0
  have heq := hB''.unique hB'
  have v1 : pureA F (⇑(lam • f₁)) g₀ x₁ = lam * f₁ y := by
    rw [hx₁, pureA_ptAt, hg₀0, SchwartzMap.smul_apply, smul_eq_mul, mul_one]
  have v2 : φ₂ x₁ = star (f₁ y) := by
    rw [hφ₂def, hx₁, pureA_ptAt, hg₀0, conjS_apply, mul_one]
  have v3 : pureA F (⇑(lamd • fd)) G xd = lamd * (z0 * f₁ y * star (f₁ y)) := by
    rw [hxd, pureA_ptAt, SchwartzMap.smul_apply, smul_eq_mul, hfddef, hfd]
    have hG0 : G 0 = 1 := by
      simp only [hGdef]
      rw [show ((0 : κ ⊕ κ → Af F) ∘ Sum.inl) = 0 from rfl, show ((0 : κ ⊕ κ → Af F) ∘ Sum.inr) = 0 from rfl, hg₀0, mul_one]
    rw [hG0, mul_one]
    rfl
  rw [v1, v2, v3] at heq
  have hK : z0 * f₁ y * star (f₁ y) ≠ 0 := mul_ne_zero (mul_ne_zero hz0 hy) (star_ne_zero.mpr hy)
  have hll : lam = lamd := by
    apply mul_right_cancel₀ hK
    linear_combination heq
  have hI : Complex.I * ((R : ℂ) + S) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast hRS.ne'
  rw [hlam, hlamd] at hll
  exact mul_right_cancel₀ hI (by linear_combination hll)

end GlobalTheory.RealLift.Compare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpace
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Compare

theorem constant_eq_dbl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (β ⊕ β) (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((g : GL β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w :=
  compare_of GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace GlobalTheory.VacuumWeight.fockAct2_diagonal_one GlobalTheory.tprod_one_pol_ne_zero

end GlobalTheory.RealLift.Compare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpaceStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (β ⊕ β) (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((g : GL β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w := by
  first | exact @GlobalTheory.RealLift.Compare.constant_eq_dbl | exact GlobalTheory.RealLift.Compare.constant_eq_dbl | (intros; apply GlobalTheory.RealLift.Compare.constant_eq_dbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZero
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.L2InnerProductNonvanishing

theorem integral_mul_star_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (f : SInf F κ) (hf : f ≠ 0) :
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI hH : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : FiniteDimensional ℝ (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).HasTemperateGrowth :=
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hL2 : MeasureTheory.MemLp (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) 2 MeasureTheory.volume := f.memLp 2 MeasureTheory.volume
  have hint : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := hL2.integrable_norm_pow (by norm_num)
  have h1 : ∀ x, f x * star (f x) = (((‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    intro x
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast; rfl
  simp_rw [h1]
  rw [integral_complex_ofReal]
  rw [Complex.ofReal_ne_zero]
  apply ne_of_gt
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]
  have hopen : IsOpen (Function.support fun x => ‖f x‖ ^ 2) := by
    exact (continuous_norm.comp f.continuous).pow 2 |>.isOpen_support
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  exact IsOpen.measure_pos (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)) hopen
    ⟨x, by simpa using hx⟩

end GlobalTheory.L2InnerProductNonvanishing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZeroStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f : SInf F κ), f ≠ 0 →
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  first | exact @GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | exact GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | (intros; apply GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangian
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagLagrNorm
open MeasureTheory GlobalTheory.DiagForm IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem map_eI_eq : ∃ k : NNReal, k ≠ 0 ∧
    Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) := by
  have : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  have : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  have : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have : (Measure.map (eI F κ) (volume : Measure (Vi F κ))).IsAddHaarMeasure :=
    (eI F κ).isAddHaarMeasure_map volume
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem integral_compD {k : NNReal}
    (hk : Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)))
    (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) =
      (k : ℂ) * ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  rw [SchwartzMap.integralCLM_apply]
  have e : ∀ u, compD F κ f u = (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x)) (eI F κ u) :=
    fun u => rfl
  simp only [e]
  have h1 := integral_map_equiv (μ := (volume : Measure (Vi F κ))) (eI F κ).toHomeomorph.toMeasurableEquiv
    (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x))
  change ∫ y, f (Sum.elim y y) ∂(Measure.map (eI F κ) volume) = ∫ x, f (Sum.elim (eI F κ x) (eI F κ x)) at h1
  rw [hk, integral_smul_nnreal_measure] at h1
  rw [← h1, NNReal.smul_def, Complex.real_smul]

theorem exists_SB_ne : ∃ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
    (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) ≠ 0 := by
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
  set U : Set (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => O
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
  set g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ := U.indicator fun _ => 1
  have hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
      HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
  set V : Set (Vf F κ) := Set.univ.pi fun _ => O
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
  have hgV : (fun v : Vf F κ => g (Sum.elim v v)) = V.indicator fun _ => (1 : ℂ) := by
    funext v
    simp only [g, U, V, Set.indicator_apply, Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, and_self]
  refine ⟨g, hg, ?_⟩
  rw [hgV, integral_indicator_const _ hVo.measurableSet]
  have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0⟩
  have hfin : (Measure.addHaar : Measure (Vf F κ)) V < ⊤ := hVc.measure_lt_top
  have : 0 < (Measure.addHaar : Measure (Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
  simpa using this.ne'

end GlobalTheory.DiagLagrNorm

namespace GlobalTheory.RealLift

open MeasureTheory GlobalTheory.DiagForm GlobalTheory.DiagLagrNorm

theorem diagLagr_invForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd _ hdd
  obtain ⟨k, hk0, hk⟩ := map_eI_eq (F := F) (κ := κ)
  obtain ⟨g, hg, hc⟩ := exists_SB_ne (F := F) (κ := κ)
  set c : ℂ := (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) * (k : ℂ) with hcdef
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hc0 : c ≠ 0 := mul_ne_zero hc hk'
  refine ⟨c⁻¹ • lDiag F κ, ?_, ?_, g, hg, ?_⟩
  · intro g' hg'
    obtain ⟨T, hT⟩ := lDiag_adm (F := F) (κ := κ) g' hg'
    exact ⟨c⁻¹ • T, fun f => by simp [hT f]⟩
  · intro z φ hφ
    have hz : z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    have hr : dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ =
        schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) φ := by
      rw [hz, Darboux.rho, hdd z z]
    simp only [LinearMap.smul_apply]
    rw [hr, lDiag_schr ψ _ _ hφ]
  · intro f
    simp only [LinearMap.smul_apply]
    rw [lDiag_pureA f hg, integral_compD hk, smul_eq_mul, hcdef]
    field_simp

end GlobalTheory.RealLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangianStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  first | exact @GlobalTheory.RealLift.diagLagr_invForm | exact GlobalTheory.RealLift.diagLagr_invForm | (intros; apply GlobalTheory.RealLift.diagLagr_invForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.LieSecondPf

theorem lieSecond_of_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → DerEx → FockEx → VacLine → LieScalar → LieSecond := by
  intro _ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ
  obtain ⟨hU, dd, omd, hdd, hWS, hres⟩ := hW
  obtain ⟨c, hc⟩ := hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  obtain ⟨Φd, hΦd⟩ := hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) hCM hψ hFrd
  obtain ⟨cd, hcd⟩ := hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1
  have key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace := by
    intro w Y
    rcases Nat.eq_zero_or_pos (R + S) with h0 | hpos
    · have hR : R = 0 := by omega
      have hS : S = 0 := by omega
      subst hR hS
      have : Y.trace = 0 := by simp [Matrix.trace]
      rw [this, mul_zero, mul_zero]
    · have hbox := GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
      have hl := GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd
      have hne : (∫ x : κ → mixedEmbedding.mixedSpace F,
          Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 := by
        obtain ⟨z, hz, hzx⟩ := hbox
        have h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) =
            z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x)) := by
          intro x
          rw [hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]
        simp_rw [h1]
        rw [MeasureTheory.integral_const_mul]
        refine mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)
        intro h0
        exact GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))
      have h1 := GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w
      have h2 := GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w
      rw [h2, h1]
  intro γ hγ Y hY T
  have e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) =
      fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1 := by
    funext w
    rw [key w (Y w)]
  have := hc γ hγ Y hY T
  rw [← e] at this
  exact this

end GlobalTheory.RealLift.LieSecondPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | exact GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | (intros; apply GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar <;> assumption)
end
