module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPoints
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.TieAlgValues

theorem mem_Qbar_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact IsIntegral.of_pow hn h

theorem emb_mem_Qbar {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (k : L) : φ k ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) k).map φ.toRatAlgHom

theorem conj_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : (starRingEnd ℂ) z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact h.map (starRingEnd ℂ).toRatAlgHom

theorem norm_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : ((‖z‖ : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  refine mem_Qbar_of_pow (n := 2) (by norm_num) ?_
  have e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e]
  exact mul_mem h (conj_mem_Qbar h)

theorem inf_mem_Qbar {L : Type} [Field L] [NumberField L] {χ : HChar L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (h : χ.HasInf φ n) (k : Lˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [h k]
  exact prod_mem fun i _ => zpow_mem (div_mem (emb_mem_Qbar _ _) (norm_mem_Qbar (emb_mem_Qbar _ _))) _

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem loc_pow_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ∃ n : ℕ, 0 < n ∧ χ.loc v x ^ n = 1 := by
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hN
  have hN2 : 1 < N := Fintype.one_lt_card
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  refine ⟨N - 1, by omega, ?_⟩
  rw [← map_pow]
  refine hv _ ?_ ?_
  · show Valued.v (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  · have e : (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) - 1 =
        (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) := by
      push_cast; rfl
    rw [e]
    exact le_exp_neg_one hlt

theorem loc_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ((χ.loc v x : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  obtain ⟨n, hn, h⟩ := loc_pow_eq_one χ v hv x hx
  refine mem_Qbar_of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact one_mem _

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open PI.HeckeProdW

theorem fin_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (htame : ∀ v, χ.TameAt v)
    (hinf : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (b : Ideles L) (hb : IsFinIdele b) :
    ((χ.1 b : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  classical
  obtain ⟨h, hh, hx⟩ := CharEx.classExp L
  obtain ⟨k, hk⟩ := hx b
  set u : Ideles L := b ^ h * diagUnits L k with hu
  set w : Ideles L := (infDiag k)⁻¹ * u with hw
  have hwInf : (w : AdeleRing (𝓞 L) L).1 = 1 := by
    funext pl
    show pw pl w = 1
    refine f_inv_mul (pw pl) _ _ ?_
    rw [pw_infDiag, hu, map_mul, map_pow, pw_diag]
    have : pw pl b = 1 := hb pl
    rw [this, one_pow, one_mul]
  have hwFin : ∀ v, Valued.v ((w : AdeleRing (𝓞 L) L).2 v) = 1 := by
    intro v
    show Valued.v (pv v w) = 1
    rw [hw, f_inv_mul' (pv v) _ _ (pv_infDiag v k)]
    exact hk v
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (w : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (hwFin v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (hwFin v)
  let y : Pu L := fun v => (hunit v).unit
  have hwy : w = Phi L y := Units.ext (Prod.ext (hwInf.trans rfl) (Subtype.ext (funext fun v => rfl)))
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  have hwQ : ((χ.1 w : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    rw [hwy, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod, Units.coe_prod]
    refine prod_mem fun v _ => ?_
    rw [Phi_single]
    refine loc_mem_Qbar χ v (htame v) _ ?_
    show Valued.v (((y v : v.adicCompletionIntegers L) : v.adicCompletion L)) = 1
    exact hwFin v
  have hue : u = infDiag k * w := by rw [hw, mul_inv_cancel_left]
  have hχu : χ.1 u = χ.1 b ^ h := by rw [hu, map_mul, χ.2.2 k, mul_one, map_pow]
  refine mem_Qbar_of_pow hh ?_
  rw [← Units.val_pow_eq_pow_val, ← hχu, hue, map_mul, Units.val_mul]
  exact mul_mem (hinf k) hwQ

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

def finIdele {L : Type} [Field L] [NumberField L] (z : (FiniteAdeleRing (𝓞 L) L)ˣ) : Ideles L :=
  MulEquiv.prodUnits.symm (1, z)

theorem mt_mem_Qbar : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m,
    ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  intro D _ _ _ _ _ _ _ _ t u μ _ A dtU _ hP _ i hi y
  obtain ⟨x, hx⟩ := hP.q_read.1 (dtU y)
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Ideles t.X.E := finIdele (Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : IsFinIdele b := fun _ => rfl
  have hbx : ι (x : AfE t.X.F t.X.E) = (b : AdeleRing (𝓞 t.X.E) t.X.E).2 := rfl
  have key : ((D.muTil (i + 1) (A.q x) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
    rw [hP.muTil ι hι ⟨i, hi⟩ b x hb hbx]
    obtain ⟨n, -, hn⟩ := (hP.mu0 ⟨i, hi⟩).inf
    exact fin_mem_Qbar _ (hP.mu0 ⟨i, hi⟩).tame (inf_mem_Qbar hn) b hb
  by_cases hμ : μ = D.what₂.mu0
  · rw [(hP.ref hμ).2, ← hx]
    exact key
  · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ hμ rfl
    have e : (t.O u μ).mt (i + 1) = D.muTil (i + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m)
    rw [e, MonoidHom.mul_apply, Units.val_mul, ← hx]
    refine mul_mem key ?_
    rw [hξ x, Units.coe_map]
    exact emb_mem_Qbar _ _

end GlobalTheory.TieAlgValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  first | exact @GlobalTheory.TieAlgValues.mt_mem_Qbar | exact GlobalTheory.TieAlgValues.mt_mem_Qbar | (intros; apply GlobalTheory.TieAlgValues.mt_mem_Qbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityType
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityType
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mt_ratId : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi
  choose e he using fun τ => (D.hc τ).e_int ⟨i, hi⟩
  refine ⟨e, fun τ => (he τ).symm, fun z hz y hy => ?_⟩
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hz' : (z : D.host.E) ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host ⟨z, hz'⟩
  simp only at hk
  let k' : t.X.Eˣ := Units.map t.seam.iE.symm.toRingHom.toMonoidHom k
  have hik : t.seam.iE (k' : t.X.E) = k := t.seam.iE.apply_symm_apply _
  have hq : A.q (ratId t.X.F t.X.E k') = dtU y := by
    apply hP.q_dt
    rw [hy]
    have hx : Units.map A.iA.toRingHom.toMonoidHom (ratId t.X.F t.X.E k') = ratId D.host.F D.host.E k := by
      apply Units.ext
      show A.iA ((k' : t.X.E) ⊗ₜ[t.X.F] 1) = (k : D.host.E) ⊗ₜ[D.host.F] 1
      rw [hP.iA_rat, hik]
    rw [hx, h90, MonoidHom.div_apply, MonoidHom.id_apply, eq_div_iff_mul_eq']
    apply Units.ext
    show ((z : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) _ ((k : D.host.E) ⊗ₜ[D.host.F] 1)) = (k : D.host.E) ⊗ₜ[D.host.F] 1
    rw [Formalism.UG.sigR]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hs : Formalism.L2.Forms.sigD D (k : D.host.E) = D.host.conj k := bridge_star_holds D.R D.host _
    rw [hs, hk]
  have hmu : ((D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ := by
    obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
    rw [hP.muTil ι hι ⟨i, hi⟩ (GlobalTheory.Mem.Chr.finPartI _ (GlobalTheory.Mem.Chr.diagUnits _ k')) _ (GlobalTheory.KerJ.RatPts.isFin_finPart _)
      ((hι.1 (k' : t.X.E)).trans rfl), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag, Units.val_inv_eq_inv_val]
    obtain ⟨n, hn, hinf⟩ := (hP.mu0 ⟨i, hi⟩).inf
    rw [hinf k', ← Finset.prod_inv_distrib, ← t.seam.iT.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : n τ = 2 * -e (t.seam.iT τ) := by
      have h1 := hn τ
      simp only [he] at h1
      exact_mod_cast h1
    have hka : Formalism.L2.Col.Fields.embC t.X t.seam.σ₀ τ (k' : t.X.E) = TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) := by
      rw [← hik]; exact t.seam_ok.1 τ _
    have h1 := congrArg (TaylorLogMetric.embT D (t.seam.iT τ)) hk
    rw [map_mul] at h1
    rw [GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    rw [hka]
    have h0 : TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) ≠ 0 := by simp
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) = a at *
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (z : D.host.E) = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]
  have htw : (t.O u μ).mt (i + 1) (A.q (ratId t.X.F t.X.E k')) = D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) := by
    by_cases h0 : μ = D.what₂.mu0
    · rw [(hP.ref h0).2]
    · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ h0 rfl
      rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hξ]
      have h1 : ((t.tup μ : Chr t.X.F t.X.E t.X.K)) (ratId t.X.F t.X.E k') = 1 := by
        have hm := (t.tup μ).2
        exact hm.1.1.1.1.1 ⟨k', rfl⟩
      rw [h1, map_one, mul_one]
  rw [← hq, htw, hmu]

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityTypeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  first | exact @GlobalTheory.TwV.mt_ratId | exact GlobalTheory.TwV.mt_ratId | (intros; apply GlobalTheory.TwV.mt_ratId <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TwV.MuLawPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem generalLinearGroupOne_eq_of_det_eq {R : Type} [CommRing R] {g h : GL (Fin 1) R}
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det h : Rˣ) : R) := by rw [e]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at e'
  ext a b
  fin_cases a; fin_cases b
  exact e'

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def gl1 (x : (AfE F E)ˣ) : GL (Fin 1) (AfE F E) :=
  Units.map (Matrix.scalar (Fin 1) : AfE F E →+* Matrix (Fin 1) (Fin 1) (AfE F E)).toMonoidHom x

theorem det_ideleAsGL1 (x : (AfE F E)ˣ) : Matrix.GeneralLinearGroup.det (gl1 x) = x := by
  ext
  simp [gl1, Matrix.GeneralLinearGroup.val_det_apply]

theorem ideleAsGL1_mem_unitary_of_normOne (σ : E →ₐ[F] E) {x : (AfE F E)ˣ} (hx : x ∈ U1 σ) :
    gl1 x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) := by
  have h1 : (x : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) (MonoidHom.mem_ker.1 hx)
    simpa [conjId] using this
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, gl1, Matrix.mul_apply, inclE]
  rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]; exact h1

end Gen

section D
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)

theorem muOf_det (j : ℕ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt j (dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold muOf
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]

theorem exists_unitaryOne_det_eq_normOneIdele {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x :=
  ⟨⟨gl1 x, ideleAsGL1_mem_unitary_of_normOne _ hx⟩, det_ideleAsGL1 x⟩

end D

section D2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)


set_option maxHeartbeats 4000000 in
theorem muOf_det_mul (j : ℕ) (x y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1) =
      muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1) * muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) := by
  have e : Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1 =
      Matrix.GeneralLinearGroup.det (x * y).1 := by
    rw [Subgroup.coe_mul, map_mul]
  have h2 : dtU (x * y) = dtU x * dtU y := dtU.map_mul x y
  have h3 : (t.O u μ).mt j (dtU x * dtU y) = (t.O u μ).mt j (dtU x) * (t.O u μ).mt j (dtU y) :=
    ((t.O u μ).mt j).map_mul _ _
  have k1 := muOf_det (t := t) (u := u) (μ := μ) dtU j (x * y)
  rw [h2, h3, Units.val_mul, ← e] at k1
  rw [k1, muOf_det, muOf_det]

end D2

theorem rationalIdele_mem_normOne_of_norm_eq_one {D : D7} (z : D.host.Eˣ) (hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1) :
    ratId D.host.F D.host.E z ∈ U1 (sigD D) := by
  have hs : (sigD D : D.host.E →+* D.host.E) (z : D.host.E) = D.host.conj (z : D.host.E) := Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  rw [U1, MonoidHom.mem_ker]
  ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, conjId, ratId, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
  show inclE _ (z : D.host.E) * sigR (sigD D) _ (inclE _ (z : D.host.E)) = 1
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [show (sigD D) (z : D.host.E) = D.host.conj (z : D.host.E) from hs, hz, Algebra.TensorProduct.one_def]

theorem muLaw_underTie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT'
  have hA := GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints A dtU a hP hT'
  have hU := GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary A dtU a hP hT'
  have hR := GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType A dtU a hP hT'
  intro i hi
  refine ⟨fun y => muOf_det dtU (i + 1) y, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 := muOf_det (t := t) (u := u) (μ := μ) dtU (i + 1) 1
    simp only [OneMemClass.coe_one, map_one, Units.val_one] at h1
    exact h1
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hy
    exact muOf_det_mul dtU (i + 1) x' y'
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det]
    exact hA i hi y
  · intro x hx hint hv
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det, hU i hi y hint hv, Units.val_one]
  · obtain ⟨e, he, hz⟩ := hR i hi
    refine ⟨e, he, fun z hz1 => ?_⟩
    obtain ⟨y, hy⟩ := exists_unitaryOne_det_eq_normOneIdele (rationalIdele_mem_normOne_of_norm_eq_one z hz1)
    rw [← hy, muOf_det]
    exact hz z hz1 y hy

end GlobalTheory.TwV.MuLawPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChainStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  first | exact @GlobalTheory.TwV.MuLawPf.muLaw_underTie | exact GlobalTheory.TwV.MuLawPf.muLaw_underTie | (intros; apply GlobalTheory.TwV.MuLawPf.muLaw_underTie <;> assumption)
end
