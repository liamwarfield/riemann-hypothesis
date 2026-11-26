module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ParabolicUnipotents

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (f : d.G → ℂ) (s₁ z : ℂ) (x : d.G) : ℂ := ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x
abbrev Cs_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y)
def rep_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : d.G := ((Quot.out q : rat2 σ d.Y) : d.G)
def FirstOrbit {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ : d.G) : Prop := ∀ i, inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) = 0
def kq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (T : nF σ d.Y d.b)
    (uM : (Fin L.n → AE F E) → d.G) (γ x : d.G) (p : (Fin L.n → AE F E) × nA σ d.Y d.b) : ℂ :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (γ * (nb p.2 * (uM p.1 * x))) *
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * p.2.1))))
def tm_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (γ x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (γ * g)) T (uM u * x) ∂ν
def secondOrbitSection {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (x : d.G) : ℂ :=
  ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
def first_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → G2 σ L.Y) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
abbrev SD_k.LF (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := (Fin d.m → Fin d.n → ℂ) → ℂ
abbrev SD_k.MF (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Mx F E d.m d.n → ℂ
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.StepOK (x : d.G) (A : d.LF → d.LF) (B : d.MF → d.MF) : Prop :=
  (∀ f, IsSw f → IsSw (A f)) ∧ ∀ Ψ, d.IsAwayW w Ψ → d.IsAwayW w (B Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w (A f) (B Ψ)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.Good (y : GR d.n) (g f : d.LF) : Prop :=
  ∀ Ψ, d.IsAwayW w Ψ → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w g Ψ
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.OkY (y : GR d.n) : Prop := ∀ f, IsSw f → ∃ g, IsSw g ∧ R.Good w y g f
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.Lc (y : GR d.n) (f : d.LF) : d.LF := if h : ∃ g, IsSw g ∧ R.Good w y g f then h.choose else 0
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isLocOp_of_ok (h : ∀ y, R.OkY w y) : R.IsLocOp w (R.Lc w) := by
  intro y f hf
  have hx := h y f hf
  have e : R.Lc w y f = hx.choose := by simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.Lc, dif_pos hx]
  rw [e]
  exact ⟨hx.choose_spec.1, fun Ψ hΨ Φ hΦ hT => hx.choose_spec.2 Ψ hΨ Φ hΦ hT⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_of_step {y : GR d.n} {A : d.LF → d.LF} (h : R.StepOK w (R.ι w y) A id) : R.OkY w y := by
  intro f hf
  exact ⟨A f, h.1 f hf, fun Ψ hΨ Φ hΦ hT => (h.2 Ψ hΨ).2 f hf Φ hΦ hT⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.step_comp (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {x x' : d.G} {A A' : d.LF → d.LF}
    {B B' : d.MF → d.MF} (h : R.StepOK w x A B) (h' : R.StepOK w x' A' B') :
    R.StepOK w (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun Ψ hΨ => ⟨(h.2 _ (h'.2 Ψ hΨ).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 Ψ hΨ).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' Ψ) (h'.2 Ψ hΨ).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (hsch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_mul (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {y y' : GR d.n} (h : R.OkY w y)
    (h' : R.OkY w y') : R.OkY w (y * y') := by
  intro f hf
  obtain ⟨g', hg', hG'⟩ := h' f hf
  obtain ⟨g, hg, hG⟩ := h g' hg'
  refine ⟨g, hg, fun Ψ hΨ Φ hΦ hT => ?_⟩
  rw [map_mul, map_mul, Module.End.mul_apply]
  exact hG Ψ hΨ _ (hsch _ Φ hΦ) (hG' Ψ hΨ Φ hΦ hT)
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Glue
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sc_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sc_cont_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d) := (Place.exists_sec d.cm d.B.emb).choose_spec.1
theorem sc_pi_k (x : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x) = x w :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.1 x w
theorem sc_fin_k (x : InfinitePlace F → ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x = 0 := (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.1 x
variable {p : Type} [Fintype p] [DecidableEq p]
def atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : Matrix p p (AE F E) :=
  Matrix.of fun i j => _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d (fun w' => fam w Z w' i j) + finOne F • (1 : Matrix p p (AE F E)) i j
theorem cw_mul_k {q : Type} [Fintype q] (w : InfinitePlace F) (A B : Matrix q q (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_one_k {q : Type} [DecidableEq q] (w : InfinitePlace F) : d.cw w (1 : Matrix q q (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_atM_k (w w' : InfinitePlace F) (Z : Matrix p p ℂ) : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z) = fam w Z w' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_pi_k, Place.piInf_finOne, add_zero]
theorem fin_atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z = finOne F • (1 : Matrix p p (AE F E)) := by
  ext i j
  simp only [Matrix.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, smul_add, _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_fin_k, zero_add, smul_smul, fin_idem]
theorem atM_mul_k (w : InfinitePlace F) (Z Z' : Matrix p p ℂ) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (Z * Z') = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z' := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    unfold fam
    split_ifs <;> simp
  · rw [fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, Matrix.mul_one]
theorem atM_one_k (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (1 : Matrix p p ℂ) = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
    unfold fam
    split_ifs <;> rfl
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
theorem continuous_atM_k (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k (p := p) d w) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.add ((_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_cont_k d).comp (continuous_pi fun w' => ?_)) continuous_const
  unfold fam
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  · exact continuous_const
end Glue
section Iota
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem bb_k : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]
theorem bb'_k : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]
def Zm_k (ζ : ℂ) (y : GR d.n) : M2 d.n := dZ d.n ζ⁻¹ * mR y * dZ d.n ζ
theorem Zm_mul_k {ζ : ℂ} (h : ζ ≠ 0) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (y * y') = mR y * mR y' from rfl]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dZ d.n ζ) (dZ d.n ζ⁻¹), dZ_mul_inv h, Matrix.one_mul]
theorem Zm_one_k {ζ : ℂ} (h : ζ ≠ 0) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ 1 = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (1 : GR d.n) = 1 from rfl, Matrix.mul_one, dZ_inv_mul h]
def MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) * incM F (d.b⁻¹).1
theorem MxI_mul_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_mul_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem MxI_one_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ 1 = 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_one_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem inFrame_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) :
    incM F (d.b⁻¹).1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * incM F d.b.1 = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp
theorem cw_transpose_k {p q : Type} (w : InfinitePlace F) (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ :=
  Matrix.transpose_map
theorem cw_incM_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) : d.cw w (incM F M) = M.map (d.B.emb w).1 :=
  Matrix.ext fun i j => PositivityTheory.ThKG.Tow.Levi.piInf_incl (d.B.emb w) (M i j)
theorem map_sig_emb_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    (M.map σ).map (d.B.emb w).1 = (M.map (d.B.emb w).1).map star := by
  ext i j
  exact d.cm.2.2.2 _ _
theorem hQ_w_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 * (d.b.1.map (d.B.emb w).1).map star = Qc d.n ε := by
  have h := congrArg (fun M => M.map (d.B.emb w).1) hε
  simp only [Matrix.map_mul (f := (d.B.emb w).1), _root_.PositivityTheory.SiegelWeilFormula.Krd.map_sig_emb_k] at h
  rw [Matrix.transpose_map] at h
  rw [h]
  simp only [Qc, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
theorem fin_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y = finOne F • 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, fin_mul, fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, ← fin_mul, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem MxI_unitary_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y).map (cA σ) = dbl (incM F d.Y.J) := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k]
    have hM : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y) = d.b.1.map (d.B.emb w').1 * fam w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) w' * (d.b⁻¹).1.map (d.B.emb w').1 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    rw [hM]
    refine conj_unit _ _ _ _ _ ?_ (_root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d hε w') ?_
    · rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · unfold fam
      split_ifs
      · exact (unitary_iff hζ (mR y)).2 y.2
      · rw [Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : (finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))).map (cA σ) = finOne F • 1 := by
      rw [map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [fin_mul, fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, ← map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, e1, Matrix.transpose_smul,
      Matrix.transpose_one, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
def iotaF_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) : d.G :=
  ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y⁻¹, by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)]⟩, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_unitary_k d hε hζ w y⟩
def iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : GR d.n →* d.G where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Krd.iotaF_k d hε hζ w
  map_one' := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ) w))
  map_mul' a b := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ) w a b))
theorem inFrame_iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w y) = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) :=
  _root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_MxI_k d w ζ y
theorem continuous_iota_k {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w) := by
  have hm : Continuous fun y : GR d.n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hz : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y := (continuous_const.matrix_mul hm).matrix_mul continuous_const
  have hM : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y :=
    (continuous_const.matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_atM_k d w).comp hz)).matrix_mul continuous_const
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨hM, ?_⟩
  exact hM.comp continuous_inv
theorem iotaEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k := by
  intro F E _ _ _ _ _ σ d ε ζ hε hζ
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ, _root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_iota_k d hε hζ, fun w y => ?_, fun w w' y hw => ?_, fun w y => ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_true, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dZ_mul_inv (zeta_ne hζ), Matrix.one_mul]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_neg hw]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
end Iota
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
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
def eA_k : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)
def elt_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1
def uA_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
def bMat_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 β 0 1
def sB_k (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j))))
def aB_k (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E := E) (AF F) δ)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem incM_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem incM_inv_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.inv_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem inFrame_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem matrixRep_eq_frameConj_inFrame (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.mul_one]
theorem inFrame_injective_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Function.Injective (inFrame (σ := σ) (Y := d.Y) d.b) := by
  intro x y h
  have : mat2 x = mat2 y := by rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d y, h]
  exact Subtype.ext (Units.ext this)
theorem om_mem_sch_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om g Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres g Φ h
theorem constantTerm_mul_right (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (g k : d.G) : d.sec0 Φ (g * k) = d.sec0 (d.om k Φ) g := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul, Module.End.mul_apply]
theorem a_mul_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g k : d.G) (hk : k ∈ d.K) : d.a (g * k) = d.a g := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := d.ok.hgt.iwa g
  rw [mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']
theorem kfin_om_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) : d.KFin (d.om k Φ) := by
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d k hΦ.1, ?_⟩
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩
  simp [map_mul, Module.End.mul_apply]
section Forms
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
end Forms
theorem frame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  simp [incM, Matrix.fromBlocks_map]
theorem parabolic_lowerLeft_block_zero (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    (inFrame d.b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hp' : mat2 p * DC = DC * t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M * E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p * E1 = E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 := rfl
    calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((mat2 p * DC) * incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inr i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type] using this
theorem par_decomp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ (n0 m0 : d.G) (β₀ : Mx F E d.n d.n), inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1 ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d m0 ∧ p = n0 * m0 := by
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t hp
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
theorem gram_mat_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : UA σ d.A.J) (X : Mx F E d.m d.n) :
    d.gram (mat g⁻¹ * X) (mat g⁻¹ * X) = d.gram X X := by
  have hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J := (g⁻¹).2
  have hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_mul, hm]
  calc Xᵀ * (mat g⁻¹)ᵀ * incM F d.A.J * ((mat g⁻¹).map (cA σ) * X.map (cA σ))
      = Xᵀ * ((mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ)) * X.map (cA σ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg]
theorem phase_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T β₀ : Mx F E d.n d.n) :
    -(⅟(2 : AF F) * d.tt (β₀ * ((-2 : ℤ) • T))) = d.tt (T * β₀) := by
  have h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀) := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]
theorem orb_n_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) (n0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) :
    d.orb T (d.om n0 Ψ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T Ψ := by
  have hP := (hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn
  have hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E),
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 →
      d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X) := by
    intro g X hX
    rw [hP, _root_.PositivityTheory.SiegelWeilFormula.KWhit.gram_mat_inv_k, hX, _root_.PositivityTheory.SiegelWeilFormula.KWhit.phase_k]
  have hs : ∀ g : UA σ d.A.J,
      (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T Ψ (mat g⁻¹ * incM F X.1) := by
    intro g
    rw [← tsum_mul_left]
    exact tsum_congr fun X => hpt g X.1 X.2
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb]
  simp_rw [hs]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
theorem int_n_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b))
    (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (w n0 m0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) (f : d.G → ℂ) :
    ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
      d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, f (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
  have := hcd.2.1
  have hβ₀ : β₀ ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨n0, hn⟩
  let b₀ : nA σ d.Y d.b := ⟨β₀, hβ₀⟩
  have hnb : ∀ β, nb β * n0 = nb (b₀ + β) := by
    intro β
    apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_injective_k d
    rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hcd.1 β, hn, hcd.1 (b₀ + β)]
    simp [Matrix.fromBlocks_multiply, add_comm, b₀]
  have htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1) := by
    intro β
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_add, Matrix.trace_add, map_add (f := _), b₀]
  calc ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
      = ∫ β, (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) *
          d.B.ψ (d.tt (T.1.1 * β₀)))) (b₀ + β) ∂lam := by
        congr 1
        funext β
        dsimp only
        rw [← hnb β, htt β, ← AddChar.map_add_eq_mul,
          show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]
        simp only [mul_assoc]
    _ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam :=
        integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) *
          (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))
    _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext β
        ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def unipotentNilpotentPart {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := ((L.rng (L.em j)).2 ⟨j, rfl⟩)
theorem unipotent_nilpotent_mul_eq_zero {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L v = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L _
theorem continuous_unipotent_nilpotent {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have : (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact (continuous_apply j).smul continuous_const
def muF_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) 0 0 (((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ))
def muF'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) 0 0 (((1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ))
theorem one_add_mul_one_sub_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) :
    (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) * (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero, add_zero, add_sub_cancel_right]
theorem muF_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k L u = 1 := by
  have e1 := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.one_add_mul_one_sub_k L u
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]
theorem inFrame_uM_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) 0 0 a' at ha
  have hf := kunf.frame_eq hε (uM u)
  rw [ha] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.one_add_mul_one_sub_k, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  have e3 : a' = ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ) := by
    rw [← e2]
    ext i j
    simp [Matrix.map_apply, kfour.cA_cA' σ hσ]
  rw [ha, e3]
  rfl
theorem continuous_uM_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const
      (hcA.comp (continuous_const.sub hN).matrix_transpose)
  have hc' : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const
      (hcA.comp (continuous_const.add hN).matrix_transpose)
  have h1 : Continuous fun u => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun u => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF'_k L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun u => ?_
    show _ = mat2 (uM u)
    rw [kunf.matrix_eq_inFrame_conj d.b, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L h]
  · refine h2.congr fun u => ?_
    show _ = mat2 (uM u)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L h,
      Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_mul_k L u)]
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EpsEqK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {ε ε' : ℤˣ} (hε : FrameEq σ d.Y d.b ε) (hε' : FrameEq σ L.Y L.b ε') : ε = ε' := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hnL : 1 ≤ L.n := L.ok.hn
  have key : ∀ (s : ℤ), (∀ i j, σ (d.Y.J j i) = (s : E) * d.Y.J i j) → (∀ i j, σ (L.Y.J j i) = (s : E) * L.Y.J i j) →
      ε = ε' := fun s h1 h2 =>
    Units.ext ((eps_of_sign hσ d.ok.hn hε s h1).trans (eps_of_sign hσ hnL hε' s h2).symm)
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · exact key (-1) (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · exact key 1 (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix : Type := Fin d.m × Fin d.n × Fin 2
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) : d.crd (d.cmb c) = c := by
  funext ⟨i, j, k⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb]
  have h : ∑ k', c (i, j, k') ⊗ₜ[F] d.bs k' = ∑ k', c (i, j, k') • (Algebra.TensorProduct.basis (AF F) d.bs) k' := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact congrFun (Module.Basis.repr_sum_self _ (fun k' => c (i, j, k'))) k
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add (X X' : Mx F E d.m d.n) : d.crd (X + X') = d.crd X + d.crd X' := by
  funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_smul (a : AF F) (X : Mx F E d.m d.n) : d.crd (a • X) = a • d.crd X := by
  funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) →ₗ[AF F] Mx F E d.m d.n where
  toFun := d.cmb
  map_add' c c' := by ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' a c := by ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Finset.smul_sum, TensorProduct.smul_tmul']
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Mx F E d.m d.n := d.cmb fun j => if k = j then 1 else 0
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) : d.cmb c = ∑ k, c k • _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d k :=
  LinearMap.pi_apply_eq_sum_univ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL d) c
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek_rat (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : ∃ M : Matrix (Fin d.m) (Fin d.n) E, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d k = incM F M := by
  refine ⟨Matrix.of fun i j => (∑ k', (if k = (i, j, k') then (1 : F) else 0) • d.bs k' : E), ?_⟩
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, incM, Matrix.map_apply, Matrix.of_apply, map_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  show _ = (1 : AF F) ⊗ₜ[F] _
  split_ifs <;> simp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM (M : Matrix (Fin d.m) (Fin d.n) E) (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) :
    d.crd (incM F M) k = algebraMap F (AF F) (d.bs.repr (M k.1 k.2.1) k.2.2) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, incM, Matrix.map_apply]
  rw [show inclR (F := F) (AF F) (M k.1 k.2.1) = (1 : AF F) ⊗ₜ[F] M k.1 k.2.1 from rfl,
    Algebra.TensorProduct.basis_repr_tmul]
  simp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_incM (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (incM F x) = incM F ((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, ← incM_transpose, ← incM_mul]
  rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n)
    (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (fun k => d.crd X (τ k)) ⬝ᵥ (fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w) = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w := by
  rw [dotProduct, Equiv.sum_comp τ (fun i => d.crd X i * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d i * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w), ← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_sum_left]
  congr 1
  conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d X, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum, Matrix.sum_mul]
  simp only [Matrix.smul_mul]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) :
    Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F) where
  toFun w := (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) (τ k), fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w)
  map_add' w w' := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_add, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right]
  map_smul' a w := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_smul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_smul]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_smul_right]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) (τ k), fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w) := rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    om (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w') = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, om, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv]
  exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_split d w w').symm
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = (fun k => d.crd X (τ k), 0) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_frame]
  refine Prod.ext rfl (funext fun k => ?_)
  exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame d _ _
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w).1 = 0) : ∃ Z : Mx F E d.m d.n, w = Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ := by
  have h1 : d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) = 0 := by
    funext i
    have := congrFun h (τ.symm i)
    simpa [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply] using this
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w = 0 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w), h1]
    exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL d).map_zero
  obtain ⟨Z, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w
  exact ⟨Z, by rw [hZ, h2, Matrix.zero_mul, add_zero]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    ∃ y z : κ → F, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (incM F x) = ratV y z := by
  have hs : ∀ k, ∃ r : F, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (incM F x) = algebraMap F (AF F) r := by
    intro k
    obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek_rat d (τ k)
    rw [hM, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, ← incM_transpose, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]
    obtain ⟨y, z, h⟩ := d.ok.dbl.rat (M * (d.b.1.toCols₂)ᵀ)
    obtain ⟨y', z', h'⟩ := d.ok.dbl.rat x
    exact ⟨om (y, z) (y', z'), by rw [h, h']; exact om_ratV y z y' z'⟩
  choose r hr using hs
  refine ⟨fun k => d.bs.repr (((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) (τ k).1 (τ k).2.1) (τ k).2.2, r, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_incM]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ (τ k)
  · exact hr k
end Adp
end PositivityTheory.SiegelWeilFormula.TBij
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopChiW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.uW (w : InfinitePlace F) (z : ℂ) : AE F E :=
  (Place.exists_sec d.cm d.B.emb).choose (Function.update (fun _ => 1) w z) + finOne F • 1
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW (w : InfinitePlace F) (z : ℂ) : ℂ := if h : IsUnit (d.uW w z) then ((d.χ h.unit : Circle) : ℂ) else 1
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CAInjectiveK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def Au_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := fun h => (L.rng (L.em j)).2 ⟨j, rfl⟩ h
theorem Au_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L v = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (u + v) := by
  have h0 : (∑ j, Matrix.single L.i₀ (L.em j) (u j)) * (∑ k, Matrix.single L.i₀ (L.em k) (v k)) = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => Matrix.single_mul_single_of_ne _ _ _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.em_ne_k L j) _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, add_mul, mul_add, one_mul, mul_one, h0, add_zero, Pi.add_apply, Matrix.single_add,
    Finset.sum_add_distrib, add_assoc]
theorem Au_zero_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L 0 = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k]
theorem cA_injective_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Function.Injective (cA σ) := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  have hb : Function.Bijective σ := AlgHom.bijective σ
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective σ hb)).injective
theorem frame_blk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x : d.G} {A A' : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks A 0 0 A') : Aᵀ * A'.map (cA σ) = 1 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h2 := kunf.frame_eq hε x
  rw [h] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  exact (Matrix.fromBlocks_inj.1 h2).2.1
theorem blk_unique_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x y : d.G} {A A₁ A₂ : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (hx : inFrame d.b x = Matrix.fromBlocks A 0 0 A₁) (hy : inFrame d.b y = Matrix.fromBlocks A 0 0 A₂) : x = y := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d hx
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d hy
  have h1' : A₁.map (cA σ) * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have e : A₁.map (cA σ) = A₂.map (cA σ) := by
    calc A₁.map (cA σ) = A₁.map (cA σ) * (Aᵀ * A₂.map (cA σ)) := by rw [h2, Matrix.mul_one]
      _ = A₂.map (cA σ) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A₁ = A₂ := Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) e
  apply kunf.inFrame_injective d.b
  rw [hx, hy, e2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlace
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
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.ae_ext (z z' : AE F E) (h : ∀ w, piInf (d.B.emb w) z = piInf (d.B.emb w) z') (hf : finOne F • z = finOne F • z') :
    z = z' :=
  Place.ad_ext d.cm d.B.emb h hf
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.exists_insW (w : InfinitePlace F) : ∃ ins : ℂ →+ AE F E, (∀ z, piInf (d.B.emb w) (ins z) = z) ∧
    (∀ w', w' ≠ w → ∀ z, piInf (d.B.emb w') (ins z) = 0) ∧ ∀ z, finOne F • ins z = 0 := by
  obtain ⟨s, -, h1, h2, h3, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨AddMonoidHom.mk' (fun z => s (Pi.single w z)) (fun a b => by rw [Pi.single_add, h3]), fun z => ?_,
    fun w' hw' z => ?_, fun z => h2 _⟩
  · simp [h1]
  · simp [h1, Pi.single_eq_of_ne hw']
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end
