module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNM
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNC
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
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.frame_nU (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hy : mR y = nU b) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w y)).toBlocks₁₂ 0 1 ∧
    d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₂ = R.ζ • b ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₂ = 0) ∧ finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₂ = 0 := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set M := inFrame d.b (R.ι w y) with hM
  have hw : d.cw w M = nU (R.ζ • b) := by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_nU hζ0]
  have ho : ∀ w', w' ≠ w → d.cw w' M = 1 := fun w' h => R.off_w w w' y h
  have hf : finOne F • M = finOne F • 1 := R.off_f w y
  have o1 := one_blocks (n := d.n) (1 : ℂ)
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  simp only [one_smul] at o1
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
    rw [hf, smul_one_smul]
  have e11 : M.toBlocks₁₁ = 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k d]
      show (d.cw w' M).toBlocks₁₁ = 1
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.1
    · show (finOne F • M).toBlocks₁₁ = _
      rw [hf', of.1, smul_one_smul]
  have e21 : M.toBlocks₂₁ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [show d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0 from Matrix.map_zero _ (map_zero _)]
      show (d.cw w' M).toBlocks₂₁ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.2.2.1
    · show (finOne F • M).toBlocks₂₁ = _
      rw [hf', of.2.2.1, smul_zero]
  have e22 : M.toBlocks₂₂ = 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k d]
      show (d.cw w' M).toBlocks₂₂ = 1
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.2.2.2
    · show (finOne F • M).toBlocks₂₂ = _
      rw [hf', of.2.2.2, smul_one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [e11, e21, e22]
  · show (d.cw w M).toBlocks₁₂ = _
    rw [hw]; simp [nU]
  · intro w' h
    show (d.cw w' M).toBlocks₁₂ = _
    rw [ho w' h]; exact o1.2.1
  · show (finOne F • M).toBlocks₁₂ = _
    rw [hf', of.2.1]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepN_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b →
    R.StepOK w (R.ι w y) (fun f u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) id := by
  intro y b hb hy
  obtain ⟨hM, hβw, hβo, hβf⟩ := R.frame_nU w y b hy
  refine ⟨fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_quadratic_phase_multiplication d.m d.n (((R.sg w : ℤ) : ℝ)) b hb φ
    refine ⟨ψ, ?_⟩
    rw [hψ]
    funext u
    push_cast
    rfl
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).1 (R.ι w y) _ hM X, R.psi_nU w b hb _ hβw hβo hβf X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepN (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b →
    R.StepOK w (R.ι w y) (fun f u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) id :=
  R.stepN_pf w hT
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ c : ℂ, c ≠ 0 ∧ R.StepOK w (R.ι w y) (fun f u => c * f (Matrix.of u * a)) id :=
  R.stepM_pf w hT
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def rot_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) : d.G :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => R.ι w (yrot d.n (R.sg w) t)).prod
theorem rot_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t ∈ d.K := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k
  refine d.K.list_prod_mem fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)
theorem exists_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) :
    ∃ W' : Mx F E d.m d.n, finOne F • W' = 0 ∧ ∀ w, d.cw w W' = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W := by
  obtain ⟨s, -, hs1, hs2, -, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← smul_mul_assoc, hs2, zero_mul]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]
def tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) : Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_tw_k R W).choose
def vline_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (z : ℂ) : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (realAd F z.re • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F z.im • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ
theorem fin_eq_zero_iff_k (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X = 0 ↔ finOne F • X = 0 := by
  set bas := Algebra.TensorProduct.basis (AF F) d.bs
  have key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0 := by
    intro z
    rw [← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]
    simp only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      finOne_mul_eq_zero_iff]
  constructor
  · intro h
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    refine (key _).2 fun l => ?_
    exact congrFun h (i, j, l)
  · intro h
    funext ⟨i, j, l⟩
    exact (key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCos
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem surj_k {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hS : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ g ∈ rat2 σ L.Y, γ = p * L.j g := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  obtain ⟨G0', hG0'⟩ := Afc.rat_frame (b := d.b) γ⁻¹ (inv_mem hγ)
  have hGG : G0' * G0 = 1 := kfour.incM_injective (F := F) (by
    rw [kfour.incM_mul', ← hG0, ← hG0', ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one,
      Afc.incM_one'])
  have hS0 : ∀ i, G0 (Sum.inr i) (Sum.inl L.i₀) = 0 := fun i => by
    have h1 := hS i
    rw [hG0] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  set v : Fin d.n → E := fun k => G0 (Sum.inl k) (Sum.inl L.i₀) with hv_def
  have hv : v ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hGG (Sum.inl L.i₀)) (Sum.inl L.i₀)
    have h2 : ∀ k, G0 (Sum.inl k) (Sum.inl L.i₀) = 0 := fun k => congrFun h0 k
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h1
    simp only [h2, hS0, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨a, ha⟩ := exists_gl_col L.i₀ v hv
  obtain ⟨p1, hp1r, hp1⟩ := Afc.levi_ex hσ d.ok.frame a⁻¹
  have hp1P : p1 ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p1).2 (by rw [hp1, Matrix.toBlocks_fromBlocks₂₁])
  set P1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
    Matrix.fromBlocks (a⁻¹).1 0 0 ((((a⁻¹)⁻¹).1)ᵀ.map σ) with hP1_def
  have hP1 : inFrame d.b p1 = incM F P1 := by
    rw [hp1, hP1_def, Afc.incM_fromBlocks, show incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 from kfour.incM_zero]
  set M1 := P1 * G0 with hM1_def
  have hM1 : inFrame d.b (p1 * γ) = incM F M1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, hM1_def, kfour.incM_mul']
  have hγ1 : p1 * γ ∈ rat2 σ d.Y := mul_mem hp1r hγ
  have hx : ∀ r, M1 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    rw [hM1_def, Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | i
    · simp only [hP1_def, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero]
      have e1 : ∀ j, G0 (Sum.inl j) (Sum.inl L.i₀) = a.1 j L.i₀ := fun j => (ha j).symm
      simp only [e1]
      rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [Matrix.one_apply]
    · simp [hP1_def, hS0, Matrix.one_apply]
  have hform := form_E hε (p1 * γ) hM1
  have hy := yrow_zero hform hx
  set H := M1.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) with hH_def
  have hH := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.blockH_form_k L hform hx hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨h, hh⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hhr : h ∈ rat2 σ L.Y := kunf.rat_of_inFrame hh
  have hh' : inFrame L.b h⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hh]
    exact Matrix.inv_eq_right_inv hIA
  have hnF : inFrame d.b (p1 * γ * L.j h⁻¹) = incM F (M1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hh', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k, hM1_def,
      kfour.incM_mul', kfour.incM_mul']
  have hnq : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (p1 * γ * L.j h⁻¹)) := by
    rw [hnF]
    exact NQ.map _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_E_k L hx hy hHH')
  have hnP : p1 * γ * L.j h⁻¹ ∈ par2 σ d.Y := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 hnq.projected_block_lower_sum
  have hnR : p1 * γ * L.j h⁻¹ ∈ rat2 σ d.Y := mul_mem hγ1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hhr))
  refine ⟨p1⁻¹ * (p1 * γ * L.j h⁻¹), mul_mem (inv_mem hp1P) hnP, mul_mem (inv_mem hp1r) hnR, h, hhr, ?_⟩
  rw [map_inv]
  group
theorem rep_mk_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (x : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x) = p * x := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
    (Quotient.out_eq (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)).symm
  refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
  show (((Quotient.out (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)) : rat2 σ d.Y) : d.G) = _
  rw [← hγ]
  rfl
end Bq
theorem cos_bij_pf_k : ∃ e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 = p * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') := by
  set H := (par2 σ d.Y).subgroupOf (rat2 σ d.Y) with hH
  set H' := (par2 σ L.Y).subgroupOf (rat2 σ L.Y) with hH'
  let jr : rat2 σ L.Y → rat2 σ d.Y := fun γ => ⟨L.j γ, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L γ.2⟩
  let e0 : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d := Quotient.lift (fun γ => GlobalTheory.AutomorphicL2Unitary.mk H (jr γ)) (by
    intro a b hab
    have hab' : b * a⁻¹ ∈ H' := QuotientGroup.rightRel_apply.1 hab
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨jr (b * a⁻¹), ?_⟩, ?_⟩
    · rw [hH', Subgroup.mem_subgroupOf] at hab'
      rw [hH, Subgroup.mem_subgroupOf]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hab'
    · apply Subtype.ext
      show L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) * L.j a = L.j b
      rw [map_mul, map_inv, inv_mul_cancel_right])
  have he0 : ∀ γ, e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ) = GlobalTheory.AutomorphicL2Unitary.mk H (jr γ) := fun γ => rfl
  have hS : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q')) := by
    intro q'
    induction q' using Quotient.inductionOn with
    | h γ =>
      obtain ⟨p, hp, -, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
      have e1 : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = p * L.j γ := by rw [he0]; exact hrep
      show _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)))
      rw [e1]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L hp (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_smallerGroupEmbed L γ)
  let e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun q' => ⟨e0 q', hS q'⟩
  have hinj : Function.Injective e := by
    intro q1 q2 h12
    have h0 : e0 q1 = e0 q2 := congrArg Subtype.val h12
    induction q1 using Quotient.inductionOn with
    | h a =>
      induction q2 using Quotient.inductionOn with
      | h b =>
        change GlobalTheory.AutomorphicL2Unitary.mk H (jr a) = GlobalTheory.AutomorphicL2Unitary.mk H (jr b) at h0
        obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h0
        have hγv : ((γ : rat2 σ d.Y) : d.G) = L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) := by
          have := congrArg Subtype.val hγ
          simp only [Subgroup.coe_mul, jr] at this
          rw [map_mul, map_inv, ← this, mul_inv_cancel_right]
        have hP : (b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹ ∈ par2 σ L.Y := by
          apply _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.par_of_j_k L
          rw [← hγv]
          exact Subgroup.mem_subgroupOf.1 γ.2
        change GlobalTheory.AutomorphicL2Unitary.mk H' a = GlobalTheory.AutomorphicL2Unitary.mk H' b
        rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
        refine ⟨⟨b * a⁻¹, Subgroup.mem_subgroupOf.2 hP⟩, ?_⟩
        simp
  have hsurj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hpP, hpR, g, hg, hγ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.surj_k L (Quotient.out q).2 hq
    refine ⟨GlobalTheory.AutomorphicL2Unitary.mk H' ⟨g, hg⟩, Subtype.ext ?_⟩
    show GlobalTheory.AutomorphicL2Unitary.mk H (jr ⟨g, hg⟩) = q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨⟨p, hpR⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
    exact hγ.symm
  refine ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, fun q' => ?_⟩
  induction q' using Quotient.inductionOn with
  | h γ =>
    obtain ⟨p, hpP, hpR, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
    obtain ⟨p', hp'P, hp'R, hrep'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (d := L.sd) γ
    refine ⟨p * L.j p'⁻¹, mul_mem hpP (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L (inv_mem hp'P)), mul_mem hpR (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hp'R)), ?_⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = _
    rw [he0, hrep, hrep', map_mul, map_inv]
    simp only [jr]
    group
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMVal
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMB
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
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_gen (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ t : GL (Fin d.n) (AE F E), d.cw w t.1 = a ∧ (∀ w', w' ≠ w → d.cw w' t.1 = 1) ∧ finOne F • t.1 = finOne F • 1 ∧
      R.StepOK w (R.ι w y) (fun f u => ((d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ)) * f (Matrix.of u * a)) id := by
  intro y a ha hy
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1
      rw [mul_inv_cancel]; rfl
    have h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]
    calc mR y⁻¹ = (Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y) * mR y⁻¹ := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨hM, hA1, -, hO1, hF1, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y) with hMdef
  set M' := inFrame d.b (R.ι w y⁻¹) with hM'def
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)},
      P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ →
      P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    intro P Q hP hQ hPQ
    rw [hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hPQ
    exact ⟨h1, h4⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM
  obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩
  let u : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  have hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1 := hM
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  refine ⟨t, hA1, fun w' h => (hO1 w' h).1, hF1, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ
    exact ⟨ψ, hψ⟩
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]
    have hui : (u⁻¹).1 = M'.toBlocks₂₂ := rfl
    rw [hui]
    set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ
    have hZo : ∀ w', w' ≠ w → d.cw w' Z = 0 := by
      intro w' h
      rw [hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by
        rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]; exact Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,
        Matrix.mul_one, sub_self]
    have hZf : finOne F • Z = 0 := by
      rw [hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, sub_self]
    have hX : X * (M'.toBlocks₂₂)ᵀ = X + Z := by rw [hZ]; abel
    have hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a := by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
      rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, hD', ← Matrix.mul_assoc, mapStar_mulR]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    rw [hloc, hX, hΨ X Z hZo hZf]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

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
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.compFin_det (t : GL (Fin d.n) (AE F E)) (hf : finOne F • t.1 = finOne F • 1) (v : Pl F) :
    compFin F E v (t.1.det) = 1 := by
  have hm : t.1.map (compFin F E v) = 1 := by
    ext i j
    rw [Matrix.map_apply, ← Place.compFin_finOne v (t.1 i j)]
    change compFin F E v ((finOne F • t.1) i j) = _
    rw [hf, Matrix.smul_apply, Place.compFin_finOne, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.piInf_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (w' : InfinitePlace F) :
    piInf (d.B.emb w') (t.1.det) = Function.update (fun _ => (1 : ℂ)) w a.det w' := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  by_cases h : w' = w
  · subst h
    rw [Function.update_self]
    exact congrArg Matrix.det ht
  · rw [Function.update_of_ne h]
    have := congrArg Matrix.det (ho w' h)
    rw [Matrix.det_one] at this
    exact this
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.det_uW (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    t.1.det = d.uW w a.det := by
  obtain ⟨-, hs2, hs3, -, -⟩ := (Place.exists_sec d.cm d.B.emb).choose_spec
  apply PositivityTheory.ThKG.Tow.Levi.ad_ext d.cm d.B.emb
  · intro w'
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.piInf_det (d := d) w t a ht ho w', _root_.PositivityTheory.SiegelWeilFormula.SD_k.uW, map_add (f := _), hs2, Place.piInf_finOne, add_zero]
  · intro v
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.compFin_det (d := d) t hf v, _root_.PositivityTheory.SiegelWeilFormula.SD_k.uW, map_add (f := _), ← Place.compFin_finOne v, hs3, map_zero, zero_add,
      Place.compFin_finOne, map_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = d.chiW w a.det := by
  have e := _root_.PositivityTheory.SiegelWeilFormula.RD_k.det_uW (d := d) w t a ht ho hf
  have hu : IsUnit (d.uW w a.det) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.det t).isUnit.map (RingHom.id _) |>.map (RingHom.id _) |> fun h => by
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW, dite_eq_left hu]
  have : hu.unit = Matrix.GeneralLinearGroup.det t :=
    Units.ext (by rw [IsUnit.unit_spec, Matrix.GeneralLinearGroup.val_det_apply, e])
  rw [this]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.absE_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖a.det‖ ^ 2 := by
  rw [GlobalTheory.Doubling.absE_apply]
  have hinf : ∀ w', GlobalTheory.Doubling.absEw F E w' (GlobalTheory.Doubling.unitInf F E w' (Matrix.GeneralLinearGroup.det t)) =
      ‖Function.update (fun _ => (1 : ℂ)) w a.det w'‖₊ ^ 2 := by
    intro w'
    rw [GlobalTheory.Doubling.absEw_eq_sq d.cm (d.B.emb w'), ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.piInf_det (d := d) w t a ht ho w',
      ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) = 1 := by
    intro v
    have : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = 1 := by
      apply Units.ext
      show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = 1
      rw [Matrix.GeneralLinearGroup.val_det_apply, _root_.PositivityTheory.SiegelWeilFormula.RD_k.compFin_det (d := d) t hf v]
    rw [this, map_one]
  simp only [hinf, hfin, finprod_one, mul_one]
  rw [Finset.prod_eq_single w (fun w' _ h => by rw [Function.update_of_ne h]; simp) (fun h => absurd (Finset.mem_univ w) h),
    Function.update_self]
  push_cast
  rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_val_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id := by
  intro y a ha hy
  obtain ⟨t, ht, ho, hf, hS⟩ := R.stepM_gen w hT y a ha hy
  have hc : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) =
      d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (d := d) w t a ht ho hf, _root_.PositivityTheory.SiegelWeilFormula.RD_k.absE_det (d := d) w t a ht ho hf, ← Real.rpow_natCast ‖a.det‖ 2,
      ← Real.rpow_mul (norm_nonneg _), show ((2 : ℕ) : ℝ) * ((d.m : ℝ) / 2) = (d.m : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    rfl
  simp only [hc] at hS
  exact hS
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem commW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x hx y
theorem iota_mem_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w y hy
theorem kSplit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.kSplit_k d R w k hk
theorem iota_isPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w q hq
theorem siegel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.siegel_k d hp
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.T_zero_k d Φ
theorem loc_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.loc_zero_k d R w
theorem gSplit_of_k (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  obtain ⟨y, hk'K, hk'w⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.kSplit_k d R w k hk
  set k' := (R.ι w y)⁻¹ * k with hk'
  have hcomm := _root_.PositivityTheory.SiegelWeilFormula.KSplit.commW_k d R w k' hk'w
  obtain ⟨A, hA⟩ := hAw F E σ d R w k' hk'w
  have hΨi : d.Indep w Ψ := ((hF F E σ d R).2.1 w Ψ hΨ).2
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.siegel_k d hp
  refine ⟨p * k', y, C * A Ψ 0, (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ), absE_pos _, ?_,
    fun y' => ⟨?_, fun P => ?_⟩⟩
  · rw [mul_assoc, hcomm y, hk', mul_inv_cancel_left]
  · obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := Glob.locIwasawa y'
    obtain ⟨tq, hPq, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.iota_isPar_k d R w q hq
    have e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k') := by
      rw [map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]
      simp only [mul_assoc]
    have hval := d.ok.hgt.val _ _ (isPar_mul hp hPq) _ ((d.K).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplit.iota_mem_K_k d R w k₀ hk₀) hk'K)
    have h0 : 0 ≤ d.a ((p * R.ι w q) * (R.ι w k₀ * k')) := by rw [hval]; exact NNReal.coe_nonneg _
    show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _
    rw [e, Real.coe_toNNReal _ h0, hval, map_mul, map_mul, NNReal.coe_mul, habs, hloc]
  · have hsw := fP_sw P
    have hΞ := (hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2
    have hΞs : d.om (R.ι w y') (φ P) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ (hφ P).1
    have h2 := (hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ
    have hs2 : d.om k' (d.om (R.ι w y') (φ P)) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ hΞs
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hs2, ← _root_.PositivityTheory.SiegelWeilFormula.KSplit.T_zero_k, h2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KSplit.loc_zero_k]
    ring
end PositivityTheory.SiegelWeilFormula.KSplit
end
end
end
