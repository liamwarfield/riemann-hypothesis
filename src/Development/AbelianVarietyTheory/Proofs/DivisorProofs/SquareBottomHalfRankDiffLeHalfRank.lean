module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem completed_eq {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L) {s : ℂ}
    (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) : Λ s = archFactor n s * L s := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  let g : ℂ → ℂ := fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹)
  have key : ∀ z : ℂ, (∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) → archFactor n z *
      ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := fun z hz => by
    unfold archFactor
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (hz i), one_mul]
  have hg : Differentiable ℂ g := by
    refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hgL : g = L := entire_eq_of_halfPlane hg hL.1 1 fun z hz => by
    have hz' : ∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => Complex.Gamma_ne_zero_of_re_pos (by
      have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
      norm_num
      have := abs_nonneg (n i)
      have h2 : (0:ℝ) ≤ |(n i : ℝ)| := abs_nonneg _
      linarith)
    show Λ z * _ = L z
    rw [h.eq_mul hL hz, mul_comm (archFactor n z), mul_assoc, key z hz', mul_one]
  calc Λ s = Λ s * (archFactor n s * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))⁻¹)) := by rw [key s hs, mul_one]
    _ = archFactor n s * g s := by ring
    _ = archFactor n s * L s := by rw [hgL]

end GlobalTheory.LValNe

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem nonempty_of_isCMType {φ : I → E →+* ℂ} (hφ : IsCMType φ) : Nonempty I := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  obtain ⟨i, -⟩ := hφ w.embedding
  exact ⟨i⟩

theorem exists_heckeL [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ)
    (hm : HasInf χ φ m) (hpos : ∀ i, 0 < m i) : ∃ Λ, IsHeckeL χ Λ := by
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  exact GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ m χ hφ hu hm ⟨i₀, (hpos i₀).ne'⟩

theorem gamma_int_ne_zero {k : ℤ} (hk : 0 < k) : Complex.Gamma (k : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.intCast_re]; exact_mod_cast hk)

theorem half_abs_two_mul (a : ℤ) (ha : 0 < a) : ((|2 * a| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_of_pos (by omega)]; push_cast; ring

theorem half_abs_neg_two_mul (a : ℤ) (ha : 0 < a) : ((|-(2 * a)| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_neg, half_abs_two_mul a ha]

theorem archFactor_ne_zero {n : I → ℤ} {s : ℂ} (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) :
    archFactor n s ≠ 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (hs i)
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto

theorem heckeL_ne_zero_int (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) [IsCMField E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ) (hm : HasInf χ φ m)
    (hpos : ∀ i, 0 < m i) {L : ℂ → ℂ} (hL : IsHeckeL χ L) (s : ℤ) (hs : ∀ i, 0 < s + m i) : L s ≠ 0 := by
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  have hn : ∃ i, 2 * m i ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hn' : ∃ i, -(2 * m i) ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hm' : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -(2 * m i)) := GlobalTheory.Published.HeckeFEModel.hasInf_inv hm
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hmi : HasInf χ⁻¹ φ (fun i => -m i) := by
    have e : (fun i => 2 * -m i) = fun i => -(2 * m i) := funext fun i => by ring
    show Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => 2 * -m i)
    rw [e]; exact hm'
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ (fun i => 2 * m i) hu hm hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -(2 * m i)) hu' hm' hn'
  obtain ⟨L', hL'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ (fun i => -m i) χ⁻¹ hφ hu' hmi
    ⟨i₀, by have := hpos i₀; omega⟩

  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-(2 * m i)| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_neg_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (k := 1 - s + m i) (by have := hpos i; omega)
    push_cast at this; exact this
  have e1 := completed_eq hΛ' hL' g1
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [e1]; exact mul_ne_zero (archFactor_ne_zero g1) hL1
  have hΛs : Λ s ≠ 0 := fun h0 =>
    hΛ'1 ((GlobalTheory.Published.HeckeFEModel.zero_iff hFE hφ hu hm hn hΛ hΛ' s).1 h0)

  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|2 * m i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (hs i)
    push_cast at this; exact this
  rw [completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

end GlobalTheory.LValNe

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem squareBottomHalfRankDiff_le_halfRank (D : D7) (i j : ℕ) : e0 D i j ≤ halfRank D i j := by
  unfold e0 halfRank botBig botSmall
  omega

theorem lNe_square (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) {D : D7} {T : Type}
    {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (i j : Fin D.R.m) :
    (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
      ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := by
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  have hpos : ∀ τ, 0 < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := fun τ => by
    have := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).2
    omega
  have fam_ok : ∀ χ : HChar D.host.E, IsValChar (cmPhi D) 0 (kap D sc.cGap i j 0) (condF G.pl) ∅ χ →
      ∃ Λ, IsHeckeL χ Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := fun χ h => by
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ h.1 h.2.2.1 hpos
    exact ⟨Λ, hΛ, fun s hs => hΛ.ne_zero_nat h.1 hs⟩
  refine ⟨fun t => ?_, fun c => ?_⟩
  · have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
      simp only [nuH, hL.xi_base, mul_one]
      exact mul_div_right_comm _ _ _
    obtain ⟨n, hn, hf⟩ := hL.xi_fin t
    have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
    have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
      intro k
      rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (Lc.xiH t) hn hf k, mul_one]
      exact hv.1.2.2.1 k
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ hu hm hpos
    refine ⟨Λ, hΛ, fun s hs1 hs2 => GlobalTheory.LValNe.heckeL_ne_zero_int hFE hB hφ hu hm hpos hΛ s fun τ => ?_⟩
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 := squareBottomHalfRankDiff_le_halfRank D i j
    omega
  · cases c with
    | none => exact fam_ok _ hv.1
    | some c => exact fam_ok _ (hv.2 c)

theorem lNe_of_functionalEquation :
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LNe := by
  intro hFE hB hFD
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, -, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  exact fun i j => lNe_square hFE hB hφ hL G i j

end GlobalTheory.SqTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVW
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVW
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityW

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hTr : IsTriple B G X om om') (v : Pl (F := F)) (h : UA σ G.W.J) (hh : h ∈ UAt σ G.W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin a × Fin (a + a') → AF F)
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) :
      om (1, h) (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (om (1, h) Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := G.M.co.e.symm (p, q) with hw
  have he : G.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat h - 1) = 0 := hh u hu
  have hact : GlobalTheory.WeilM.actAB (cA σ) ((1, h) : UA σ G.V.J × UA σ G.W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1
  have h2 := hW.impl (1, h) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v h hh φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (1, h) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have hcomm := comm_off B G X om om' hTr v h hh
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (1, h) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h' := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h'
    exact h'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  refine ⟨fun t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp

end GlobalTheory.WeilLocalityW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityW.locality | exact GlobalTheory.WeilLocalityW.locality | (intros; apply GlobalTheory.WeilLocalityW.locality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingNormAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.NormScaleHaar
open Formalism.UG GlobalTheory.AdelicU

theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

end GlobalTheory.NormScaleHaar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModMat

theorem addEquivAddHaarChar_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  intro F E _ _ _ _ _ σ _ j m _ _ _ _ g a
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE F E j m g a
  rw [hchar, GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele]
  have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det g ^ m * Matrix.GeneralLinearGroup.det a ^ j) := by
    ext
    simp [hdet]
  rw [hu]
  apply NNReal.eq
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.NormScaleHaar.ideleModule_norm, map_mul, map_pow, map_pow]

end GlobalTheory.ResidueEisenstein.ModMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensorStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  first | exact @GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE | exact GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE | (intros; apply GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.LieScal

theorem sumPl_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (L : ∀ w, Module.End ℂ (V w)) (a : ι → ℂ) :
    sumPl (fun w => L w + a w • (1 : Module.End ℂ (V w))) = sumPl L + (∑ w, a w) • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
  have h : ∀ w, atPl w (L w + a w • (1 : Module.End ℂ (V w))) = atPl w (L w) + a w • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro w
    have e := (PiTensorProduct.mapMultilinear ℂ V V).map_update_add (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w)
      (a w • LinearMap.id)
    have e2 := (PiTensorProduct.mapMultilinear ℂ V V).map_update_smul (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (a w)
      LinearMap.id
    simp only [PiTensorProduct.mapMultilinear_apply, Function.update_eq_self, PiTensorProduct.map_id] at e e2
    simp only [atPl]
    rw [Module.End.one_eq_id, Module.End.one_eq_id, e, e2]
    rfl
  simp only [sumPl, h, Finset.sum_add_distrib, Finset.sum_smul]


open scoped Classical in
theorem lieScalar : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine → LieScalar := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := GlobalTheory.T.darboux_schrodinger_compatibility hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := GlobalTheory.T.weil_representation_unitary_standard_character hP F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := GlobalTheory.T.archimedean_frame_character_factorization hP F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  unfold cA at *
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  rw [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 P Q R S (Y w) + (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (Tens F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact sumPl_add_smul (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add (f := _), map_smul, smul_eq_mul]

end GlobalTheory.LieScal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieScalar_of_prints_derEx_vacLine : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @GlobalTheory.LieScal.lieScalar | exact GlobalTheory.LieScal.lieScalar | (intros; apply GlobalTheory.LieScal.lieScalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.BaseKernelUniq

variable {D : D7}

theorem res_unique {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P)
    (h' : IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP => (GlobalTheory.HeckeParts.idem_unique V (hes PP hP) (hes' PP hP)).symm

theorem omegaQ_congr {a b : ℕ} {Q : Finset (Pl D.host.E)} {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) (r : ℕ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ Q r ξ k y = omegaQ Q r ξ' k y := by
  unfold omegaQ
  split_ifs with hy
  · exact Finset.prod_congr rfl fun PP _ => by rw [hξ PP.1 PP.2]
  · rfl

theorem thPVec_unique {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) (h' : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f')
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) : f = f' := by
  obtain ⟨-, e, he, hT⟩ := h
  obtain ⟨-, e', he', hT'⟩ := h'
  obtain rfl := idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hT
  rw [hall Tm hTm, hT'.2 Tm hTm]
  congr 1
  funext x
  rw [omegaQ_congr hξ]

theorem baseKernelUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → BaseKernelUnique R i v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i v _ _ ω φ ω' φ' hk hk'
  obtain ⟨χ, ξR, hχ, hres, hω, hv⟩ := hk
  obtain ⟨χ', ξR', hχ', hres', hω', hv'⟩ := hk'
  obtain rfl : χ = χ' := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 χ χ' _ hχ hχ'
  obtain rfl : φ = φ' := thPVec_unique hv hv' fun PP hP => res_unique (hres PP hP) (hres' PP hP)
  have hθφ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  have hinf : IsInfFam R.θ := hv.1.2.inf
  funext h w u g
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D R.ψ hω.std _ _ _ _ ω ω' hω hω' (h, g) _
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hinf _ _ _ _ hθφ _)) 0

end GlobalTheory.BaseKernelUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUniqueStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseThetaKernel_series_unique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → BaseKernelUnique R i v (ownAt D v) := by
  first | exact @GlobalTheory.BaseKernelUniq.baseKernelUnique | exact GlobalTheory.BaseKernelUniq.baseKernelUnique | (intros; apply GlobalTheory.BaseKernelUniq.baseKernelUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped Matrix TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassSumIdentity

theorem sub_orthProj_perp_mem {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hH : (H.map v0.embedding).PosDef) (N : Submodule K (Fin n → K)) (x : Fin n → K) :
    x - orthProj H (perpOf H N) x ∈ N := by
  have hd : ∀ Z : Submodule K (Fin n → K), Hᴴ = H ∧ IsUnit ((subE Z)ᴴ * H * subE Z).det := fun Z =>
    have k := orthogonal_projection_exists K v0 h0 _ _ H hH (subE Z) (subspace_image_spec K n Z).1
    ⟨k.1, k.2.2.1⟩
  have h1 : ∀ u y : Fin n → K, hform H u y = star u ⬝ᵥ H.mulVec y := fun u y => by
    simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_assoc,
      mul_comm, mul_left_comm]
  have hs : ∀ u y : Fin n → K, hform H u y = 0 → hform H y u = 0 := fun u y e => by
    rw [h1] at e ⊢
    have := congrArg star e
    rwa [star_zero, ← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, (hd N).1, ← Matrix.dotProduct_mulVec] at this
  set y := x - orthProj H (perpOf H N) x
  have hy : y ∈ perpOf H (perpOf H N) := sub_orthProj_mem_perpOf H _ (hd _).2 x
  have hq : orthProj H N y ∈ N := orthProj_mem H N y
  have hw : y - orthProj H N y ∈ perpOf H N := sub_orthProj_mem_perpOf H _ (hd _).2 y
  have hw' : y - orthProj H N y ∈ perpOf H (perpOf H N) :=
    Submodule.sub_mem _ hy fun z hz => hs _ _ (hz _ hq)
  obtain ⟨a, ha⟩ := (subspace_image_spec K n (perpOf H N)).2.ge hw
  have h2 : ((subE (perpOf H N))ᴴ * H * subE (perpOf H N)).mulVec a = 0 := by
    funext i
    have := hw' _ ((subspace_image_spec K n (perpOf H N)).2.le ⟨Pi.single i 1, rfl⟩)
    rw [← ha, h1, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [← Pi.single_star] using this
  have h3 : a = 0 := by
    rw [← Matrix.one_mulVec a, ← Matrix.nonsing_inv_mul _ (hd (perpOf H N)).2, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  rw [h3, map_zero] at ha
  exact sub_eq_zero.1 ha.symm ▸ hq

theorem lvlE_lvlOp {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) (S : CSD K)
    (hH : (S.H.map v0.embedding).PosDef) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (hr : S.ActGood r)
    (U : Subgroup G) (ψ : U →* Kˣ) (a : MonoidAlgebra K G) (ha : ∀ b, b * a = a * b) (x : Fin (S.lvlDim r U ψ) → K) :
    S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec ((S.lvlOp r U ψ a).mulVec x)) =
      ∑ g, a.coeff g • r g (S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec x)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec_mulVec, (level_operator_spec K v0 h0 S hH G r hr U ψ a (ha _).symm).1, ← Matrix.mulVec_mulVec, CSD.gaMat,
    Matrix.sum_mulVec, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec K S G r g _))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open GlobalTheory.TraceIncl in
theorem classSum_eOp {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} (h : HidaSetting R i t) {θ} (hθ : OnTies.IsClassSum R i t U ψ ph θ)
    (c : G → D.what₂.LL) {x y : Fin (OnTies.srcDim A i t U ψ) → D.what₂.LL}
    (e : srcForm A i t U ψ y = ∑ g, c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) : θ y = (R.FW i).eOp c (θ x) := by
  rcases subsingleton_or_nontrivial (Fin (R.nW i) → D.what₂.LL) with hs | hs
  · exact Subsingleton.elim _ _
  refine h.eq_of_adForm fun v => ?_
  have e0 : adForm R i ((R.FW i).eOp c (θ x)) = ∑ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) := by
    unfold adForm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  have e4 : ∀ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) (fun ρ => v ρ) =
      ph • (clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x))) v := fun g => by
    have e1 : adForm R i ((R.FW i).ρ g (θ x)) (fun ρ => v ρ) = sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (adForm R i (θ x) fun ρ => v ρ) :=
      DFunLike.congr_fun ((h.unif i _).2.2 g (θ x)) _
    have e2 : clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
          (clSum (presV R i t) (kern R i t) (srcForm A i t U ψ x) v) :=
      congrFun (h.clSum_equiv g (srcForm A i t U ψ x)) v
    have e3 : sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) = D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) :=
      congrArg (fun s : D.what₂.LL →+* ℂ => s _) (sign_at_base_place_eq_embedding R)
    have e5 : clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        D.what₂.embLL (c g) • clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
      congrFun (LinearMap.map_smulₛₗ _ _ _) v
    have e6 : D.what₂.embLL (c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) * D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) =
        D.what₂.embLL (c g) := by rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [e5, e2, adForm_smul, MultilinearMap.smul_apply, e1, e3, h.adForm_theta hθ, smul_smul, e6, LinearMap.map_smul, smul_comm]
  have e7 : clSum (presV R i t) (kern R i t) (srcForm A i t U ψ y) v =
      ∑ g, clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
    (congrArg (fun f => clSum (presV R i t) (kern R i t) f v) e).trans
      ((congrFun (map_sum (clSum (presV R i t) (kern R i t)) _ _) v).trans (Finset.sum_apply _ _ _))
  refine (h.adForm_theta hθ y v).trans (((congrArg (fun F => ph • F) e7).trans Finset.smul_sum).trans (Eq.symm ?_))
  exact (DFunLike.congr_fun e0 _).trans ((MultilinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun g _ => e4 g))

section Comparison₂

attribute [local instance 2000] Submodule.module

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem identity_of_tie (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y)
    (hS : GlobalTheory.TraceIncl.HidaSetting R ι (R.mu v)) {s : ℕ} (hOk : A.fam.Ok s) (hr : ClassSumRational R ι (R.mu v) U ψ ph) :
    O.θ' v i ∘ₗ O.eX v i = O.e i ∘ₗ O.θ' v i ∧
      ∀ x ∈ LinearMap.range (O.eX v i), x - O.pr v i x ∈ LinearMap.ker (O.θ' v i) := by
  have hθy : ∀ x, (toForms h fw ι z ∘ₗ O.θ' v i ∘ₗ y.symm.toLinearMap) (y x) = toForms h fw ι z (O.θ' v i x) := fun x =>
    congrArg (fun a => toForms h fw ι z (O.θ' v i a)) (y.symm_apply_apply x)
  refine ⟨LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_, fun x _ => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, t.e_eOp, ← hθy, ← hθy]
    refine classSum_eOp hS (t.θ'_eq hr) _ ?_
    refine (congrArg (srcForm A ι (R.mu v) U ψ) (LinearMap.congr_fun t.eX_eq x)).trans ?_
    exact lvlE_lvlOp hOk.conj (A.MtCSD ι (R.mu v)) ((hOk.lifts ι (R.mu v)).hpos _) (A.leftGroupActionLift ι (R.mu v)) hS.act U ψ _
      (idempotent_central _ _ A.X hOk.irr).2 (y x)
  · have hpos : (((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ).map A.v0.embedding).PosDef :=
      BlockDat.lf_lvlH_pos (B := A.fam.L ι (R.mu v)) (ℓ := ⟨A.X, U, ψ⟩) ⟨hOk.conj, hOk.irr, hOk.lifts ι (R.mu v)⟩ A.v0
    obtain ⟨a, ha, e⟩ := sub_orthProj_perp_mem hOk.conj hpos ((LinearMap.ker (O.θ' v i)).map y.toLinearMap) (y x)
    have e' : y a = y (x - O.pr v i x) :=
      e.trans ((congrArg (fun b => y x - b) (LinearMap.congr_fun t.pr_eq x).symm).trans (y.map_sub _ _).symm)
    exact y.injective e' ▸ ha

end Comparison₂


attribute [local instance] GlobalTheory.BigOn.runAlg' in
theorem leafIdentity_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → TwistedRational R F (fun _ => 1) → LeafIdentity O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO s hOk hC hU hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1 →
      O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j) := fun v j hr =>
    identity_of_tie (T := (r.used v).full) (inst := inst) (R := R) (ht v j).1
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩ hOk hr
  exact fun w hw => ⟨fun j => key w j (hrat w hw j), fun j => key _ j (by rw [hC.tup.mu_conj w]; exact hrat w hw j)⟩

end GlobalTheory.ClassSumIdentity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBaseP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBaseP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaGridRamifiedOverBasePlace

theorem thetaGridCharacterQuotient_not_unramified_over_basePlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hv
  rw [show alpha G t i j / beta G i j = G.nu t i (j + 1) from mul_div_mul_right_eq_div _ _ _,
    GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) w]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi : ¬ (G.ch.chiH (D.R.m - i)).UnrAt w := (G.ch.lev0 _ hm.1 hm.2 _ hv).2
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    rw [hv] at h
    refine (S1_mem_OmF D).2 ?_
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : (L.xiH t).UnrAt w := by
    by_contra hc
    rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
    · exact G.pl.levelPlace_ne_basePlace t _ h hv
    · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
  intro hn
  apply hchi
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t / SqNum.nuH G t i j := by
    rw [SqNum.nuH, div_div_cancel]
  rw [e, div_eq_mul_inv]
  exact (hmu.mul hxi).mul hn.inv

end GlobalTheory.ThetaGridRamifiedOverBasePlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_unrAt_of_under_eq_v0 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | (intros; apply GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_compFin_mem_intLoc_adele (z : AE F E) :
    ∀ᶠ v : Pl F in cofinite, compFin F E v z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h h'
    rw [map_add]
    exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := evFin F v a) h (1 : 𝓞 E)) h'
    change evFin F v a ⊗ₜ[F] e ∈ _
    simpa using this


omit [NumberField E] in
theorem compFin_unitAt_self (v : Pl F) (l : (AE F E)ˣ) :
    compFin F E v (unitAt E v l : AE F E) = compFin F E v l := by
  change compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _
  have h : evFin F v (eFin v) = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  rw [map_add (f := _), compFin_smul, compFin_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]

theorem eventually_unitAt_mem_unitsAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ) : ∀ᶠ v in cofinite, unitAt E v l ∈ unitsAt E v := by
  filter_upwards [eventually_compFin_mem_intLoc_adele (l : AE F E),
    eventually_compFin_mem_intLoc_adele ((l⁻¹ : (AE F E)ˣ) : AE F E)] with v h h'
  refine mem_unitsAt.2 ⟨unitAt_mem v l, ?_, ?_⟩
  · rwa [compFin_unitAt_self]
  · rwa [← map_inv, compFin_unitAt_self]

end GlobalTheory.ThK.ConeEuler

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationTowerCompatible
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BCChar

open scoped GroundTheory.Global.AdicLiesOver

theorem adicCompletionMap_comp_adicCompletionMap {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (GroundTheory.Global.adicCompletionMap u w).comp (GroundTheory.Global.adicCompletionMap v u) =
      GroundTheory.Global.adicCompletionMap v w := by
  have h := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((GroundTheory.Global.continuous_adicCompletionMap u w).comp
      (GroundTheory.Global.continuous_adicCompletionMap v u))
    (GroundTheory.Global.continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [GroundTheory.Global.adicCompletionMap_algebraMap, GroundTheory.Global.adicCompletionMap_algebraMap,
      GroundTheory.Global.adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply K M L]

theorem normU_comp_normU {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (normU v u).comp (normU u w) = normU v w := by
  haveI : IsScalarTower (v.adicCompletion K) (u.adicCompletion M) (w.adicCompletion L) :=
    .of_algebraMap_eq' (adicCompletionMap_comp_adicCompletionMap v u w).symm
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [normU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.norm_norm (R := v.adicCompletion K) (S := u.adicCompletion M) (a := (x : w.adicCompletion L))

end GlobalTheory.BCChar

end
end
