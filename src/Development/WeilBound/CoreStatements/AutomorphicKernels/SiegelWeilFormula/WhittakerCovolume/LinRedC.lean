module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IwaRedOfC

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.LinRedC
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem linRedC : LinRedC := by
  unfold LinRedC
  intro hT hTC hL hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW
  have hTT : TTheta := hT.2.2.2.1
  have hTA : ThetaAuto := hT.2.2.2.2
  have hsch : ∀ i, Φs i ∈ d.sch := fun i => (hK i).1
  have hΦ : (∑ i : Fin k, cs i • Φs i) ∈ d.sch :=
    lin_sum_mem d Finset.univ cs Φs (fun i _ => hsch i)
  have hunf := fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  choose t ht using hunf
  have hpsi : ∀ a, ‖d.B.ψ a‖ = 1 := fun a => GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std a
  unfold WhitAtC
  intro nb lam 𝓖 hcd ε w hw T hT'
  have hval : c * d.orb T ((d.om x) (∑ i : Fin k, cs i • Φs i)) =
      ∑ i : Fin k, cs i * (c * d.orb T ((d.om x) (Φs i))) := by
    have hI : d.I (∑ i : Fin k, cs i • Φs i) = ∑ i : Fin k, cs i • d.I (Φs i) := by
      funext y
      rw [lin_I_sum d hTT hTA Finset.univ cs Φs (fun i _ => hsch i) y]
      simp [Finset.sum_apply]
    have h1 := hTC F E σ d _ hΦ nb lam 𝓖 hcd T x
    rw [← h1, hI, lin_fc_sum hL d hcd T hT' x Finset.univ cs (fun i => d.I (Φs i))
      (fun i => ((hTA F E σ d).2.2 (Φs i) (hsch i)).2.1)
      (fun i => ((hTA F E σ d).2.2 (Φs i) (hsch i)).2.2), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hTC F E σ d _ (hsch i) nb lam 𝓖 hcd T x]
    ring
  rw [hval]
  have hsum := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (↑↑T * ↑β)) ∂lam)
    (fun i => c * d.orb T ((d.om x) (Φs i))) (s0 d.m d.n)
    (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hT')
  refine HolValueAt.congr hsum ⟨∑ i : Fin k, |t i|, fun z hz => ?_⟩
  have hz' : ∀ i, t i < z.re := fun i =>
    lt_of_le_of_lt ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) hz
  have hint : ∀ i, MeasureTheory.Integrable (fun β => GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (↑↑T * ↑β))) lam := fun i =>
    ((ht i z (hz' i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd
      (lin_psi_meas d _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun β => (hpsi _).le))
  simp only
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
    simp only [GlobalTheory.ThK.Dbl.flat, section_linear_finset_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · exact fun i _ => (hint i).const_mul (cs i)

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.DictAsm
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option linter.unusedSectionVars false

theorem asm_incl (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) e = HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) e := rfl

theorem asm_cA (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z := rfl

theorem asm_half : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

theorem asm_scalar_mul {n : ℕ} (η : E) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    incM F (Matrix.scalar (Fin n) η) * M = (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • M := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite,
    map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.smul_apply, smul_eq_mul]
  rfl

theorem asm_gramR (d : SD σ) (η : E) (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (Jd d η) Y =
      (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • (d.gram (toMx Y) (toMx Y))ᵀ := by
  ext c a
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, HeckeCharacterZeroLocus.SiegelWeilU.hform, HeckeCharacterZeroLocus.SiegelWeilU.JR, Jd,
    Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, SD.gram, Matrix.mul_apply, toMx,
    Matrix.of_apply, incM, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [asm_incl, asm_cA]
  ring

theorem asm_phase_cell {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : Rel d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b)
    (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    -(⅟(2 : AF F) * d.tt (β.1 * d.gram (toMx Y) (toMx Y))) =
      PositivityTheory.PfSWUS.Loc.trPair (AF F) ((hOf β).1) (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (Jd d η) Y) := by
  rw [PositivityTheory.PfSWUS.Loc.trPair, asm_gramR, hr.hof β, SD.tt, asm_half, Matrix.neg_mul, asm_scalar_mul,
    Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg, mul_neg, neg_neg]
  congr 1
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem asm_phase_whit {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : Rel d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b) :
    -d.tt (T.1.1 * β.1) =
      -PositivityTheory.PfSWUS.Loc.trPair (AF F) ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) ((hOf β).1) := by
  rw [neg_inj, PositivityTheory.PfSWUS.Loc.trPair, hr.hof β, hr.rat, SD.tt, asm_scalar_mul, Matrix.mul_neg, Matrix.mul_smul,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg]
  have h2 : ∑ a, ∑ c, ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F))) a c * ((hOf β).1 : Mx F E d.n d.n) c a =
      algebraMap (AF F) (AE F E) (-2) * (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η *
        (incM F T₀ * ((hOf β).1 : Mx F E d.n d.n)ᵀ).trace) := by
    simp only [Td, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_neg,
      map_ofNat, Matrix.trace, Matrix.diag, Matrix.mul_apply, incM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [asm_incl]
    ring
  rw [h2, ← Algebra.smul_def (-2 : AF F) _, LinearMap.map_smul, smul_eq_mul, ← mul_assoc]
  have h5 : algebraMap F (AF F) (1 / 2) * (-2 : AF F) = -1 := by
    rw [show (-2 : AF F) = algebraMap F (AF F) (-2) by rw [map_neg, map_ofNat], ← map_mul]
    norm_num
  rw [h5]
  ring

theorem asm_cpow_split {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) (w : ℂ) :
    ((C * ν⁻¹ : ℝ) : ℂ) ^ w = (C : ℂ) ^ w * (ν : ℂ) ^ (-w) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hC.le (inv_nonneg.2 hν.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hν.le]; exact Real.pi_pos.ne), Complex.cpow_neg]

theorem asm_c_ne (d : SD σ) (t : GL (Fin d.n) (AE F E)) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
    have h : absE F E (Matrix.GeneralLinearGroup.det t) * absE F E (Matrix.GeneralLinearGroup.det t)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 h0
  exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hpos _).ne')

theorem asm_meanC_smul {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μH : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J))
    (𝓕 : Set (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J)) (c : ℂ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (S : Set (Fin n → Fin M → E)) :
    HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ M J (fun Y => c * Φ Y) S) =
      c * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ M J Φ S) := by
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.meanC, HeckeCharacterZeroLocus.SiegelWeilU.thetaS, tsum_mul_left, integral_const_mul, Complex.real_smul]
  ring

theorem dictAsmX : DictAsmX := by
  intro hCell hRel hH hM hTh hT hA F E _ _ _ _ _ σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t, u, hxtu⟩ := hx
  obtain ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, hr, hΦg, hani, hεs, hcm, hherm, hTT, hdet, hchr, hpl, hfr,
    hpure, hprod, hsdW, hsdH⟩ := hRel hT hA F E σ d R Φ hΦ P gf hpg x t u hxtu T hTnd
  obtain ⟨lv, L₁, L₂, C, hC, hlv, hco, hstd, hht⟩ := hH F E σ d R x t u T η T₀ hOf θ fr g hr nb lam 𝓖 hcd ε w hw
  obtain ⟨hMβ, hMZ⟩ := hM F E σ d R x t u T η T₀ hOf θ fr g hr
  obtain ⟨hembβ, hpresβ⟩ := hMβ nb lam 𝓖 hcd ν hsdH
  obtain ⟨νc, hνc⟩ := (hA F E σ d).1
  obtain ⟨hembZ, hpresZ⟩ := hMZ μ νc hsdW hνc
  obtain ⟨μH, 𝓕, hμH, h𝓕, horb⟩ := hTh F E σ d η hr.ne hr.herm
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := asm_c_ne d t
  have hTx : ∀ Y, d.T (d.om x Φ) (toMx Y) = c * Φg Y := by
    intro Y
    rw [hΦg Y]
    exact (hT.2.1 F E σ d Φ hΦ.1).2.1 x t u hxtu (toMx Y)
  have hint : ∀ z : ℂ, ∀ β : nA σ d.Y d.b,
      GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) =
        c * (C : ℂ) ^ (z - s0 d.m d.n) * Gen.whI (AF F) σ (Jd d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
          ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β) := by
    intro z β
    obtain ⟨hνpos, ha⟩ := hht β
    have hcell := hCell hT F E σ d νc hνc ε w hw Φ hΦ.1 (nb β) x β.1 (hcd.1 β)
    have hZ : ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram Z Z))) * d.T (d.om x Φ) Z ∂νc =
        c * PositivityTheory.PfSWUS.Loc.jtR (AF F) σ (Jd d η) d.B.ψ μ Φg (hOf β) := by
      rw [← hpresZ.integral_comp hembZ]
      simp only [PositivityTheory.PfSWUS.Loc.jtR, hTx, asm_phase_cell hr β]
      rw [← integral_const_mul]
      congr 1
      funext Y
      ring
    have hs : s0 d.m d.n = ((d.m : ℂ) - d.n) / 2 := rfl
    simp only [GlobalTheory.ThK.Dbl.flat]
    rw [hcell, hZ, ha, asm_phase_whit hr β, asm_cpow_split hC hνpos]
    simp only [Gen.whI, hs]
    ring
  refine ⟨2, Jd d η, Td η T₀, d.bs, d.B.ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C,
    ⟨hcm, hherm, hTT, hdet, hchr, hpl, hfr, hlv, hco, hstd, hpure, hprod, hsdW, hsdH⟩, hani, hεs, hC,
    ⟨0, fun z _ => ⟨fun hI => ?_, ?_⟩⟩, μH, 𝓕, hμH, h𝓕, ?_⟩
  · have hk : c * (C : ℂ) ^ (z - s0 d.m d.n) ≠ 0 :=
      mul_ne_zero hc0 (Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hC.ne')))
    have h1 : Integrable (fun β => GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) *
        d.B.ψ (-d.tt (T.1.1 * β.1))) lam :=
      hI.mul_bdd (lin_psi_meas d T.1.1).aestronglyMeasurable
        (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
    have h2 := h1.const_mul (c * (C : ℂ) ^ (z - s0 d.m d.n))⁻¹
    have hcomp : Integrable (fun β => Gen.whI (AF F) σ (Jd d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
        ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β)) lam := by
      refine h2.congr (Eventually.of_forall fun β => ?_)
      simp only [hint z β]
      exact inv_mul_cancel_left₀ hk _
    exact (hpresβ.integrable_comp_emb hembβ).1 hcomp
  · simp_rw [hint z]
    rw [integral_const_mul, hpresβ.integral_comp hembβ]
  · rw [horb T T₀ hr.rat (d.om x Φ) (om_mem_sch d x hΦ.1)]
    have : (fun Y => d.T (d.om x Φ) (toMx Y)) = fun Y => c * Φg Y := funext hTx
    rw [this, asm_meanC_smul]

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem th_cA_incl (x : E) : cA σ (inclR (F := F) (E := E) (AF F) x) = inclR (F := F) (E := E) (AF F) (σ x) := by
  rw [← th_sigR_eq]; exact th_sigR_incl x

theorem th_gram_incM (d : SD σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact th_cA_incl _
  rw [SD.gram, h1]
  simp only [incM, Matrix.transpose_map, Matrix.map_mul]

theorem th_gramE (d : SD σ) (η : E) (X : Matrix (Fin d.m) (Fin d.n) E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) Xᵀ = η • (Xᵀ * d.A.J * X.map σ)ᵀ := by
  ext a b
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem th_gram_iff (d : SD σ) {η : E} (hη : η ≠ 0) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • incM F T₀ ↔ HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) Xᵀ = Td η T₀ := by
  have hs : ((-2 : ℤ) • incM F T₀ : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F ((-2 : ℤ) • T₀) := by
    ext i j; simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]
  rw [th_gram_incM, th_gramE, Td, hs]
  constructor
  · intro h
    rw [th_incM_injective h]
    ext i j
    simp only [Matrix.smul_apply, Matrix.transpose_apply]
    simp only [zsmul_eq_mul, smul_eq_mul]; push_cast; ring
  · intro h
    congr 1
    ext i j
    have := congrFun (congrFun h j) i
    simp only [Matrix.smul_apply, Matrix.transpose_apply] at this ⊢
    simp only [zsmul_eq_mul, smul_eq_mul] at this ⊢
    push_cast at this ⊢
    apply mul_left_cancel₀ hη
    rw [this]; ring

theorem th_toMx_act (d : SD σ) (M : GL (Fin d.m) (AE F E)) (X : Matrix (Fin d.m) (Fin d.n) E) :
    toMx (HeckeCharacterZeroLocus.SiegelWeilU.actTup (AF F) M (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF F) Xᵀ)) =
      (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) * incM F X := by
  ext a j
  simp only [toMx, HeckeCharacterZeroLocus.SiegelWeilU.actTup, HeckeCharacterZeroLocus.SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]

theorem thetaDict : ThetaDict := by
  intro F E _ _ _ _ _ σ d η hη _
  refine ⟨d.μ.map (thM d hη), thM d hη '' d.D, th_haar d hη, th_fd d hη, ?_⟩
  intro T T₀ hT Φ _
  rw [SD.orb, setAverage_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, MeasurableEquiv.map_apply, (thM d hη).preimage_image,
    (thM d hη).restrict_map, (thM d hη).preimage_image, integral_map_equiv, measureReal_def]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.thetaS]
  let e : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Fin d.n → Fin d.m → E | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) X = Td η T₀} :=
    { toFun := fun X => ⟨X.1ᵀ, (th_gram_iff d hη T₀ X.1).1 (hT ▸ X.2)⟩
      invFun := fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by
        rw [hT]; exact (th_gram_iff d hη T₀ _).2 Y.2⟩
      left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E)) }
  rw [← e.tsum_eq]
  refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [th_toMx_act]
  rfl

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
