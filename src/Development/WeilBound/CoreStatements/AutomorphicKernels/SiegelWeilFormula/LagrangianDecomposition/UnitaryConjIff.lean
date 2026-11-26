module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
public import Development.WeilBound.ThetaLifts.LatticeBasics.BotAsm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem unitary_conj_iff {S ι : Type*} [CommRing S] [Fintype ι] [DecidableEq ι] (c : S →+* S) (D J P Q X : Matrix ι ι S)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hG : Pᵀ * D * P.map c = J) :
    Xᵀ * D * X.map c = D ↔ (Q * X * P)ᵀ * J * (Q * X * P).map c = J := by
  have t1 : Qᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  have t2 : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  have m1 : P.map c * Q.map c = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero c) (map_one c)]
  have m2 : Q.map c * P.map c = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero c) (map_one c)]
  have hD : D = Qᵀ * J * Q.map c := by
    rw [← hG]
    calc D = (Qᵀ * Pᵀ) * D * (P.map c * Q.map c) := by rw [t1, m1, Matrix.one_mul, Matrix.mul_one]
      _ = Qᵀ * (Pᵀ * D * P.map c) * Q.map c := by simp only [Matrix.mul_assoc]
  constructor
  · intro hX
    rw [← hG]
    calc (Q * X * P)ᵀ * (Pᵀ * D * P.map c) * (Q * X * P).map c
        = Pᵀ * (Xᵀ * ((Qᵀ * Pᵀ) * D * (P.map c * Q.map c)) * X.map c) * P.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = Pᵀ * D * P.map c := by rw [t1, m1, Matrix.one_mul, Matrix.mul_one, hX]
  · intro hY
    have hX : X = P * (Q * X * P) * Q := by
      calc X = (P * Q) * X * (P * Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
        _ = P * (Q * X * P) * Q := by simp only [Matrix.mul_assoc]
    generalize Q * X * P = Y at hX hY
    rw [hX, hD]
    calc (P * Y * Q)ᵀ * (Qᵀ * J * Q.map c) * (P * Y * Q).map c
        = Qᵀ * (Yᵀ * ((Pᵀ * Qᵀ) * J * (Q.map c * P.map c)) * Y.map c) * Q.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = Qᵀ * J * Q.map c := by rw [t2, m2, Matrix.one_mul, Matrix.mul_one, hY]

theorem blk_out {R : Type*} [Semiring R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin N ⊕ Fin N)), ∀ v,
      blk h M 1 u v = (1 : Matrix _ _ R) u v ∧ blk h M 1 v u = (1 : Matrix _ _ R) v u := by
  intro u hu v
  obtain ⟨p, hp⟩ := eB_out h u hu
  have e1 : (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R) = blk h 1 1 := (blk_one h).symm
  rw [e1, blk_apply, blk_apply, blk_apply, blk_apply, hp]
  generalize eB h v = x
  rcases x with x | x <;> simp

def blkHom {S : Type*} [Semiring S] {N n : ℕ} (h : n + 1 = N) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) S →* Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) S where
  toFun M := blk h M 1
  map_one' := blk_one h
  map_mul' M M' := by rw [blk_mul, Matrix.one_mul]

def blkGL {S : Type*} [Semiring S] {N n : ℕ} (h : n + 1 = N) :
    GL (Fin n ⊕ Fin n) S →* GL (Fin N ⊕ Fin N) S := Units.map (blkHom h)

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def bA {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : GL ι (AE F E) :=
  Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) b

theorem bA_val {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : (bA (F := F) b).1 = incM F b.1 := rfl

theorem bA_inv_val {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : ((bA (F := F) b)⁻¹).1 = incM F (b⁻¹).1 := by
  rw [bA, ← map_inv]
  rfl

theorem incM_mul_inv {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  rw [← bA_inv_val b, ← bA_val (F := F) b, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem incM_inv_mul {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← bA_inv_val b, ← bA_val (F := F) b, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem cA_incl (z : E) : cA σ (inclR (F := F) (AF F) z) = inclR (F := F) (AF F) (σ z) := by
  simp [cA, inclR]

theorem incM_gram {ι : Type} [Fintype ι] [DecidableEq ι] (P D : Matrix ι ι E) :
    (incM F P)ᵀ * incM F D * (incM F P).map (cA σ) = incM F (Pᵀ * D * P.map σ) := by
  have e : (incM F P).map (cA σ) = incM F (P.map σ) := by
    ext i j
    simp [incM, cA_incl]
  rw [e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem incM_dbl {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : incM F (dbl J) = dbl (incM F J) := by
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> simp [incM, dbl]

theorem incM_jeps (k : ℕ) (ε : ℤˣ) : incM F (jeps k ε : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) =
    Matrix.fromBlocks 0 1 ((inclR (F := F) (AF F) ((ε : ℤ) : E)) • 1) 0 := by
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> simp [incM, jeps, Matrix.one_apply] <;> split_ifs <;> simp

def jHom (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))

theorem inFrame_eq {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    inFrame b g = incM F (b⁻¹).1 * g.1.1 * incM F b.1 := rfl

theorem jHom_val (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (jHom d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [jHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]

theorem jHom_mem (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    jHom d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (jHom d h b g).1ᵀ * dbl (incM F d.Y.J) * (jHom d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, jHom_val]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInv
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def BigT : Prop := PositivityTheory.SiegelWeilFormula.TAll → PositivityTheory.SiegelWeilFormula.AuxiliaryPrimeFunction →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : PositivityTheory.SiegelWeilFormula.SD σ)
  (dd0 : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))) (Fin d.m × Fin d.n × Fin 2)),
  IsAdapted d.bs d.A d.Y d.b dd0 →
  (∀ x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E, ∃ y z : Fin d.m × Fin d.n × Fin 2 → F,
      dd0.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∃ (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ))
    (S0' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ), C ≠ 0 ∧
    GlobalTheory.TowU.IsOp2 d.B.ψ (fun w => dd0.e (d.dd.e.symm w)) S0 S0' ∧ ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (crdB d.bs X)

def PartCharInv : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (l : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ℂ),
    l ∈ (adeleClass F).adm (κ' ⊕ κ'') →
    (∀ (y : κ'' → AF F), ∀ Ψ ∈ schA F (κ' ⊕ κ''), l (fun x => ψ ((x ∘ Sum.inr) ⬝ᵥ y) * Ψ x) = l Ψ) →
    ∀ Ψ ∈ schA F (κ' ⊕ κ''), (∀ x' : κ' → AF F, Ψ (Sum.elim x' 0) = 0) → l Ψ = 0

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FrameOf
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SigSig
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig' (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])


variable (F) in
def spcOf {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Spc F E n := ⟨J, ⊤, fun _ => 1, fun _ => 1⟩

theorem toCols₁_wit {n : ℕ} (T : GL (Fin n) E) (a : E) :
    ∃ t : GL (Fin n) E, (GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit a T).1.toCols₁ = diagCols (Fin n) * t.1 := by
  have hd := GlobalTheory.ThK.Dbl.Frame.frame_diag (1 : GL (Fin n) E) T a
  refine ⟨1, ?_⟩
  ext i j
  have := congrFun (congrFun hd i) j
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at this
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  simpa [Matrix.toCols₁] using this

omit [NumberField F] [NumberField E] in
theorem dbl_sym {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (hJ : ∀ i j, σ (J j i) = e₀ * J i j) :
    ((dbl J).map (σ : E →+* E))ᵀ = e₀ • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]

theorem eps_eq {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E}
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {e : E}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (e • 1) 0) (he : σ e = e) : e = e₀ := by
  have h := GlobalTheory.ThK.Dbl.Frame.gram_sym (σ : E →+* E) hc (dbl_sym hJ) b
  have hb' : bᵀ * dbl J * b.map (σ : E →+* E) = Matrix.fromBlocks 0 1 (e • 1) 0 := hb
  rw [hb'] at h
  have := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simpa [Matrix.fromBlocks, he] using this

end PositivityTheory.SiegelWeilFormula.Ald.YFA

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

open PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


omit [NumberField F] in
theorem frame_of {n : ℕ} (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (he : e₀ * e₀ = 1)
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) (T : GL (Fin n) E) (hT : J * T.1.map σ = 1) :
    ∃ b : GL (Fin n ⊕ Fin n) E, b.1ᵀ * dbl J * b.1.map σ = Matrix.fromBlocks 0 1 (e₀ • 1) 0 ∧
      ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1 := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (2 : E)⁻¹ + (σ : E →+* E) (2 : E)⁻¹ = 1 := by
    rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]
  have hJ' : (J.map (σ : E →+* E))ᵀ = e₀ • J := by
    ext i j
    simpa using hJ i j
  have hT' : (1 : GL (Fin n) E).1ᵀ * J * (1 : GL (Fin n) E).1.map (σ : E →+* E) * T.1.map (σ : E →+* E) = 1 := by
    have : (1 : Matrix (Fin n) (Fin n) E).map (σ : E →+* E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    simpa [this] using hT
  refine ⟨GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit (2 : E)⁻¹ T,
    GlobalTheory.ThK.Dbl.Frame.frame_gram (σ : E →+* E) hc he ha hJ' 1 T hT', toCols₁_wit T _⟩

theorem yFrame : YFrame := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb

end PositivityTheory.SiegelWeilFormula.Ald

end
end
