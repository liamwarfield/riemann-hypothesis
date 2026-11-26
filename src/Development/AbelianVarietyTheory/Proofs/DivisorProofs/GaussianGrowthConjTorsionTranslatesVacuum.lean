module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaChangeOfRepRootOfUnityOfChartIndependence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum
namespace GlobalTheory.ConjGrowth

section SlopeTestRemainingChoices

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem fnConj_sum (D : D7) {N N' n : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (c : Fin n → M)
    (F : Fin n → VC D N N' → ℂ) (hF : ∀ i, Differentiable ℂ (F i)) (hM : ∀ i, CoefIn D (F i) M)
    (hd : ∀ i, Differentiable ℂ (fnConj D M ρ (F i))) (h0 : ∀ i, fnConj D M ρ (F i) ≠ 0) :
    fnConj D M ρ (fun z => ∑ i, (c i : ℂ) * F i z) = fun z => ∑ i, ρ (c i) * fnConj D M ρ (F i) z := by
  funext z
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => ∑ i, (c i : ℂ) * F i z) α =
      ((∑ i, c i * ⟨_, hM i α⟩ : M) : ℂ) := by
    intro α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.ConjSeries.taylor_eq_coeff, taylorDir_sum _ _ fun i _ =>
      GlobalTheory.ProdThetaConj.an0 ((hF i).const_mul (c i : ℂ)), map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← GlobalTheory.ConjSeries.taylor_eq_coeff, GlobalTheory.ProdThetaConj.taylor_const_mul (hF i)]
  have hcj : ∀ x : M, cj M ρ x = ρ x := fun x => by simp [cj, TaylorLogMetric.liftM]
  have hs : HasSum (fun α => ∑ i, ρ (c i) * (TaylorLogMetric.taylor D (fnConj D M ρ (F i)) α * mono D α z))
      (∑ i, ρ (c i) * fnConj D M ρ (F i) z) :=
    hasSum_sum fun i _ => (GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' _ (hd i) z).mul_left _
  rw [← hs.tsum_eq]
  refine tsum_congr fun α => ?_
  change cj M ρ _ * _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht, hcj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(GlobalTheory.ConjSeries.taylor_fnConj D N N' M ρ (F i) (hd i) (h0 i)).1 α, map_mul, mul_assoc, ← hcj ⟨_, hM i α⟩]

theorem vBar_vBar (D : D7) {N N' : ℕ} (z : VC D N N') : vBar D (vBar D z) = z := by
  funext τ i j
  simp [vBar]

theorem cBar_cBar (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : cBar D (cBar D G) = G := by
  funext z
  simp [cBar, vBar_vBar]

def Facts (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (G : VC D a d → ℂ) (ρ : Qbar →ₐ[ℚ] ℂ) : Prop :=
  0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧ fnConj D Qbar ρ G ≠ 0 ∧
    (∀ y, LaQ D (tor0 D cc δ) L L' y → ∃ y', fnConj D Qbar ρ (U D (tor0 D cc δ) y G) =
      U D (torConj D (tor0 D cc δ) Qbar ρ) y' (fnConj D Qbar ρ G)) ∧
    ∀ x z, ‖U D (torConj D (tor0 D cc δ) Qbar ρ) x (fnConj D Qbar ρ G) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
        normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
          (fnConj D Qbar ρ G) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))

theorem facts_fix (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Facts D cc δ L L' G ρ := by
  have hGT := vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (hI.t0Ex cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := hI.curve cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hI.perm Qbar ρ hρ hdata.1
  refine ⟨by rw [hΛ]; exact area_pos D hI.g1 cc' δ' hc', ?_, fun y hy => ?_, fun x z => ?_⟩
  · intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hI.g1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  · obtain ⟨m, hm, hmy⟩ := id hy
    obtain ⟨y', hy', -⟩ := hI.galEx cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
      (by omega)
    have hgal := (hI.gal cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
      hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
      (by rw [comb_one]; exact hAU y hy)).1
    rw [comb_one] at hgal
    exact ⟨y', hgal⟩
  · have := sup_perm D hI.g1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh x z
    rw [Hf_re, ← mul_div_assoc] at this
    exact this

theorem facts_all (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) :
    Facts D cc δ L L' G ρ := by
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := hI.bar cc δ hc Qbar ρ hdata
  · exact facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG ρ hfix
  obtain ⟨k1, k2, k3, k4⟩ := facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG _ hfix
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
  rw [U_zero] at hn2
  have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
      (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
    congrArg Tor.abelian₂ htor
  rw [hL, area_conj] at k1 k4
  rw [(hbar a d L L' G).1] at k2 k3 k4
  rw [htor] at k3 k4
  rw [hn2] at k4
  have hU := (hbar a d L L' (fnConj D Qbar ρ G)).2.1
  refine ⟨k1, fun h => k2 ?_, fun y hy => ?_, fun x z => ?_⟩
  · rw [h]
    funext z
    simp [cBar]
  · obtain ⟨y', hy'⟩ := k3 y hy
    refine ⟨vBar D y', ?_⟩
    rw [(hbar a d L L' _).1, ← vBar_vBar D y', ← hU] at hy'
    have := congrArg (cBar D) hy'
    rwa [cBar_cBar, cBar_cBar] at this
  · have := k4 (vBar D x) (vBar D z)
    rw [← hU] at this
    simpa only [cBar, vBar_vBar, vBar, RCLike.norm_conj, Complex.conj_conj] using this

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem conj_growth : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  intro D hI cc δ t0 hc ht a b e0 hev he Ls Lt h1 h2 κ hκ k n r s hk hs hr ρ t' ht'
  have hsd : ∀ N, SD D (stdL D N) := fun N => by
    obtain ⟨Lt, h, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    exact h1 ▸ (h 1).2
  have hG := GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual D hI cc δ t0 hc ht a b _ _ Ls Lt (hsd a) (hsd b) h1 h2 e0 he.2.2.2.1
  change ThetaVectorUpToUnits D (tor0 D cc δ) t0 Ls Lt
    (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) at hG
  generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0 = G at hG ⊢
  have hGT := GlobalTheory.ConjJet.vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a b Ls Lt h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, hAC, -⟩ := hI.alg cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨k1, k2, k3, k4⟩ := facts_all D hI cc δ t0 hc ht a b Ls Lt h1 h2 hev G hG ρ
  rw [hN] at k4
  obtain ⟨hκ1, hκ2⟩ := hκ
  have hq : ∀ i, LaQ D (tor0 D cc δ) Ls Lt (s i) := fun i => ⟨k, hk, hs i⟩
  choose y hy using fun i => k3 (s i) (hq i)
  have he' : (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i) G z) =
      fun z => ∑ i, ((⟨κ, hκ1⟩ * r i : Qbar) : ℂ) * U D (tor0 D cc δ) (s i) G z := by
    funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    rfl
  have hd : ∀ i, Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G)) := fun i => by
    rw [hy]; exact GlobalTheory.ConjJet.U_diff D _ _ _ hTh.1
  rw [he', fnConj_sum D Qbar ρ _ _ (fun i => GlobalTheory.ConjJet.U_diff D _ _ _ hGT.1) (fun i => hAU _ (hq i)) hd
    (fun i => by rw [hy]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ k2)]
  refine ⟨k1, hAC n _ s (fun i => (⟨κ, hκ1⟩ * r i : Qbar).2) hq,
    Differentiable.fun_sum fun i _ => (hd i).const_mul _, fun z => ?_⟩
  have hb := fun i => k4 (y i) z
  have h0 := (sq_nonneg _).trans (k4 0 z)
  generalize (3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) * _ * _ : ℝ) = B at hb h0 ⊢
  have hb' : ∀ i, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G) z‖ ≤ √B := fun i => by
    rw [hy]; exact Real.le_sqrt_of_sq_le (hb i)
  rw [← Real.le_sqrt (norm_nonneg _) h0]
  calc _ ≤ ∑ i, ‖ρ (r i)‖ * √B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have h3 : ‖ρ ⟨κ, hκ1⟩‖ = 1 := hκ2 ρ.toRingHom
        rw [norm_mul, map_mul, norm_mul, h3, one_mul]
        exact mul_le_mul_of_nonneg_left (hb' i) (norm_nonneg _)
    _ ≤ 1 * √B := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hr ρ.toRingHom) (Real.sqrt_nonneg _)
    _ = √B := one_mul _

end GlobalTheory.ConjGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianGrowth_conj_torsionTranslates_vacuum : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  first | exact @GlobalTheory.ConjGrowth.conj_growth | exact GlobalTheory.ConjGrowth.conj_growth | (intros; apply GlobalTheory.ConjGrowth.conj_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryStabilizerTransitionSelfDualFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameChange

open Formalism.L2.DIV
open scoped Matrix TensorProduct

set_option synthInstance.maxHeartbeats 160000

private theorem int_of_parts {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n]
    (G Gi : Matrix n n R) (hGG : G * Gi = 1) (ε ε' : R) (hε : ε ∈ O) (hε' : ε' ∈ O)
    (hs : (ε + ε') • (G - 1) = G - 1) (h1 : ∀ i j, ε * G i j ∈ O) (h2 : ∀ i j, ε' * G i j ∈ O)
    (h3 : ∀ i j, ε * Gi i j ∈ O) (h4 : ∀ i j, ε' * Gi i j ∈ O) :
    (∀ i j, G i j ∈ O) ∧ ∀ i j, Gi i j ∈ O := by
  have hone : ∀ i j, (1 : Matrix n n R) i j ∈ O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hs1 : (1 - ε - ε') ∈ O := O.sub_mem (O.sub_mem O.one_mem hε) hε'
  have hA : (1 - (ε + ε')) • G = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    have : (1 - (ε + ε')) • (G - 1) = 0 := by rw [sub_smul, one_smul, hs, sub_self]
    rw [smul_sub, sub_eq_zero] at this
    exact this
  have hB : (1 - (ε + ε')) • Gi = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    calc (1 - (ε + ε')) • Gi = ((1 - (ε + ε')) • (1 : Matrix n n R)) * Gi := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((1 - (ε + ε')) • G) * Gi := by rw [hA]
      _ = (1 - (ε + ε')) • (1 : Matrix n n R) := by rw [Matrix.smul_mul, hGG]
  constructor
  · intro i j
    have e1 := congrFun (congrFun hA i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : G i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * G i j + ε' * G i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h1 i j)) (h2 i j)
  · intro i j
    have e1 := congrFun (congrFun hB i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : Gi i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * Gi i j + ε' * Gi i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h3 i j)) (h4 i j)

private theorem smul_conj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b b' X : GL n R) (ε : R)
    (h : ε • X.1 = ε • (b' * b⁻¹ : GL n R).1) :
    ε • (b⁻¹ * X * b : GL n R).1 = ε • (b⁻¹ * b' : GL n R).1 ∧
      ε • ((b⁻¹ * X * b)⁻¹ : GL n R).1 = ε • (b'⁻¹ * b : GL n R).1 := by
  have key : ∀ u v : GL n R, ε • (u * X * v : GL n R).1 = ε • (u * (b' * b⁻¹) * v : GL n R).1 := by
    intro u v
    simp only [Units.val_mul] at h ⊢
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rw [key, show b⁻¹ * (b' * b⁻¹) * b = b⁻¹ * b' by group]
  · have := key (b⁻¹ * X⁻¹) (b * b'⁻¹ * b)
    rw [show b⁻¹ * X⁻¹ * X * (b * b'⁻¹ * b) = b'⁻¹ * b by group,
      show b⁻¹ * X⁻¹ * (b' * b⁻¹) * (b * b'⁻¹ * b) = (b⁻¹ * X * b)⁻¹ by group] at this
    exact this.symm

private theorem smul_conj_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b X : GL n R) (s : R)
    (h : s • (X.1 - 1) = X.1 - 1) :
    s • ((b⁻¹ * X * b : GL n R).1 - 1) = (b⁻¹ * X * b : GL n R).1 - 1 := by
  have e : (b⁻¹ * X * b : GL n R).1 - 1 = (b⁻¹).1 * (X.1 - 1) * b.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h]

private theorem exists_int_GL {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] (γ : GL n R)
    (h1 : ∀ i j, γ.1 i j ∈ O) (h2 : ∀ i j, (γ⁻¹).1 i j ∈ O) : ∃ y : GL n O, y.1.map O.subtype = γ.1 := by
  let A : Matrix n n O := Matrix.of fun i j => ⟨γ.1 i j, h1 i j⟩
  let B : Matrix n n O := Matrix.of fun i j => ⟨(γ⁻¹).1 i j, h2 i j⟩
  have hA : A.map O.subtype = γ.1 := rfl
  have hB : B.map O.subtype = (γ⁻¹).1 := rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective O.subtype_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, hA⟩
  · show (A * B).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · show (B * A).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem frame_inv_mul_int {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {b b' : GL (Fin n) (EAf D)} (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (i j : Fin n) :
    (b⁻¹ * b' : GL (Fin n) (EAf D)).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : b'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [hb']
    intro k
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h2 := (hb _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2


set_option maxHeartbeats 800000 in
private theorem mem_St_of_comp {D : D7} (e : AE D) (he : e * e = e) (V : HSp D)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (b b' : GL (Fin V.rank) (EAf D)) (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (k : GA D V) (hk : SuppAt e V k)
    (hc : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) :
    Formalism.IndefR.Lev.finE V k ∈ St b := by
  have hidem : ∀ a : AE D, a * a = a → toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha =>
    Formalism.IndefR.Fin.LevelGroupLemmas.toEAf_mem_intAf (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, ha]))
  have hε := hidem e he
  have hε' := hidem (cA D e) (by rw [← map_mul, he])
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin V.rank) (EAf D), X = Formalism.IndefR.Lev.finE V k := ⟨_, rfl⟩
  have hXv : X.1 = (mt V k).map (toEAf D) := by rw [hX]; rfl
  have hc' : toEAf D e • X.1 = toEAf D e • (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1 := by
    rw [hX]; exact Matrix.ext fun i j => hc i j
  obtain ⟨c1, c2⟩ := smul_conj b b' X (toEAf D e) hc'
  have hs : (toEAf D e + toEAf D (cA D e)) • (X.1 - 1) = X.1 - 1 := by
    refine Matrix.ext fun i j => ?_
    have h0 := congrArg (toEAf D) (hk i j)
    have h1 : toEAf D ((mt V k - 1) i j) = (X.1 - 1) i j := by
      rw [hXv, Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
    rw [map_mul, RingHom.map_add (f := _), h1] at h0
    exact h0
  have i1 : ∀ i j, (toEAf D e • (b⁻¹ * X * b : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c1]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb hb' i j)
  have i2 : ∀ i j, (toEAf D e • ((b⁻¹ * X * b)⁻¹ : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c2]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb' hb i j)
  obtain ⟨j1, j2⟩ := GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ b hΛ hb X (hX ▸ GlobalTheory.LevSplit.finE_mem_UA V k)
    (b⁻¹ * X * b) rfl e i1 i2
  obtain ⟨g1, g2⟩ := int_of_parts (Formalism.L2.Herm.intAf D.host.F D.host.E) _ _ (Units.mul_inv (b⁻¹ * X * b)) _ _ hε hε'
    (smul_conj_sub_one b X _ hs) i1 j1 i2 j2
  obtain ⟨y, hy⟩ := exists_int_GL _ _ g1 g2
  refine ⟨y, ?_⟩
  have hy' : intGL D.host.F D.host.E V.rank y = b⁻¹ * X * b := Units.ext hy
  rw [← hX]
  show b * intGL D.host.F D.host.E V.rank y * b⁻¹ = X
  rw [hy']; group


set_option maxHeartbeats 800000 in
private theorem exists_unitary_frame_change : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y := by
  intro D e S hS V Λ hΛ b b' hb hb'
  have he : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hS
  have he' : e * cA D e = 0 := hS.2
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  let inv : EAf D →+* (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toRingEquiv.toRingHom
  have hinv : ∀ x, Lev.swapAE D (inv x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a c => rfl
    | add a c ha hc => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hc]
  let P : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1
  let Q : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b * b'⁻¹ : GL (Fin V.rank) (EAf D)).1
  have hPQ : P * Q = 1 := by
    show (b' * b⁻¹ * (b * b'⁻¹) : GL (Fin V.rank) (EAf D)).1 = 1
    rw [show b' * b⁻¹ * (b * b'⁻¹) = 1 by group]
    rfl
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf (P.map inv) (Q.map inv)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
  let k : GA D V := ⟨g, hg⟩
  have hval : ∀ i j, (Lev.finE V k).1 i j = Lev.swapAE D (finPart D (g.1 i j)) := fun i j => rfl
  have hcomp : ∀ i j, toEAf D e * (Lev.finE V k).1 i j = toEAf D e * P i j := by
    intro i j
    have h3 : finPart D e * finPart D (g.1 i j) = finPart D e * inv (P i j) := congrFun (congrFun h2 i) j
    rw [hval, show toEAf D e = Lev.swapAE D (finPart D e) from rfl, ← map_mul, h3, map_mul, hinv]
  have hk : SuppAt e V k := h1
  have hSt := mem_St_of_comp e he V Λ hΛ b b' hb hb' k hk hcomp
  refine ⟨k, hk, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.stabLat_of_mem_St V Λ b hb k hSt, hcomp, ?_⟩
  intro y hy
  have hyv : (y : AE D) = e * (mt V k).det + (1 - e) := hy
  have hyd : y = Formalism.IndefR.Fin.LevelGroupLemmas.detAt e V k :=
    Units.ext (hyv.trans (Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he V k).symm)
  have hint : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])
  refine ⟨?_, ?_, ?_⟩
  · rw [hyv, RingHom.map_add (f := _), map_mul, RingHom.map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_int he hint V hSt
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_inv_int he hint V hSt

end GlobalTheory.FrameChange

end

theorem _root_.GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y :=
  GlobalTheory.FrameChange.exists_unitary_frame_change
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RawSeriesMoveDatum
section Point

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

theorem move_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → ∀ (wq wq' : (Fin n → LevQ Dw l) → c.F), (∀ q q', LevMoves h q q' → wq' q' = wq q) → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq' (actLat h Λ) b' N' (pushLet c h P) y v' → ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) ≠ 0 ∧ v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  intro wq wq' hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq' b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq' q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  refine ⟨?_, ?_⟩
  · rw [index_Ln, ← hrr]
    exact (Nat.pos_of_mul_pos_left (lt_of_lt_of_eq hz2 (zCard_eq _ hN' r))).ne'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt

namespace GlobalTheory.DatumMove

theorem move_complex (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : ℂ, ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ 1 N P y v →
        ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' → v = z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, ht1, ht⟩ := GlobalTheory.Phase.ChangePt.move_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL
    hrow nab hnab Λ h hU hh hT hT'
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht1
  refine ⟨((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)), fun y v v' hv hv' => ?_⟩
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa
    w 1).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1).1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ 1 N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 hP w' _ 1 N' u' hu')
  obtain ⟨hA', k3⟩ := ht x L y₀ F hx hSD w w' hw N N' hN hN' a P hPa 1 1 u u' one_ne_zero one_ne_zero hu hu'
  have hsq : ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA'))).ne'
  have k4 : u = ((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)) * u' := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hsq)]
    simp only [map_one, _root_.mul_one] at k3
    linear_combination -k3
  rw [k1, k2, k4]; ring

theorem exists_move_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
    [StarRing (𝓞 E)] (nab : NabV Xo c) (h1 : 1 ≤ Dw.p + Dw.q) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : c.F, ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S),
      ShortValAt Xo c nab w Λ 1 N P y v →
        ∃ v', ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' ∧ v = algebraMap c.F S z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c h1 n hn
  obtain ⟨z, hid⟩ := @move_complex E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h hU hh hT hT' w w' hw N N' hN hN' a P hPa
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  have ex1 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w 1
  have ex2 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1
  choose u hu using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex1.1 S y).exists
  choose u' hu' using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex2.1 S y).exists
  have n1 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u S y) = u T y' :=
    fun S T _ _ _ _ φ y y' hy => ex1.2 S T φ y y' hy _ _ (hu S y) (hu T y')
  have n2 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u' S y) = u' T y' :=
    fun S T _ _ _ _ φ y y' hy => ex2.2 S T φ y y' hy _ _ (hu' S y) (hu' T y')
  have h : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = z * @u' ℂ _ s.toAlgebra y :=
    fun y => hid y _ _ (@hu ℂ _ s.toAlgebra y) (@hu' ℂ _ s.toAlgebra y)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : c.F, ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = s z₀ * @u' ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u' ℂ _ s.toAlgebra y = 0
    · refine ⟨1, fun y => ?_⟩
      rw [h y, h0 y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @GlobalTheory.ConstRatio.ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u' ℂ _ s.toAlgebra) (@u ℂ _ s.toAlgebra)
        (@n2 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@n1 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z h y hy
      have hz₀' : s z₀ = z := hz₀
      exact ⟨z₀, fun y => by rw [hz₀', h y]⟩
  have hfin := GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s u (fun S _ _ y => algebraMap c.F S z₀ * u' S y) n1
    (fun S T _ _ _ _ φ y y' hyy => by rw [map_mul, φ.commutes, n2 S T φ y y' hyy]) hz₀
  refine ⟨z₀, fun S _ _ y v hv => ⟨u' S y, hu' S y, ?_⟩⟩
  rw [(ex1.1 S y).unique hv (hu S y)]
  exact hfin S y

end GlobalTheory.DatumMove

end Point

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumMove


set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem rawSeries_move_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → ∀ x0 x1 : Fin n → LevQc Dw l, Submodule.span (𝓞 E) (Set.range x0) = ⊤ → Submodule.span (𝓞 E) (Set.range x1) = ⊤ → {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)} ⊆ (Submodule.span c.F {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x1)) La N P y (f p y)} : Set (Formalism.L2.Pj.Rul Xo c)) := by
  intro E _ _ _ H Dw l Xo c _ nab h1 _ hnab bad n a hbad hdom x0 x1 hx0 hx1 f ⟨hf, Λ, N, P, hU, hT, hM, hN, hP, hv⟩
  obtain ⟨γ, hγ, hb, hm, hw⟩ := exists_unitary_moving c (bad := 2 * bad) (by omega) x0 x1 hx0 hx1
  have triv : ∀ d, d ∣ 2 * bad → (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ ⟨stdLat E n⟩).TrivAt d := fun d hd => by
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk.coprime_dvd_right hd, h⟩
  obtain ⟨N', hN'⟩ := exists_levOK (triv 2 (Dvd.intro _ rfl)) hN
  have hM' := trivAt_act hm hM
  obtain ⟨z, hz⟩ := exists_move_const E H Dw l Xo c nab h1 hnab n hdom.2 Λ γ hU hγ hM hM' _ _ hw N N' hN hN' a P hP.1
  obtain ⟨k1, -, -, k2⟩ := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a γ hγ).2 Λ
  by_cases hz0 : z = 0
  · have : f = 0 := by
      funext p y
      obtain ⟨v', -, e⟩ := hz p.R y _ (hv p y)
      rw [e, hz0, map_zero, zero_mul]
      rfl
    rw [this]
    exact Submodule.zero_mem _
  · have e : f = z • z⁻¹ • f := by
      funext p y
      change f p y = z • z⁻¹ • f p y
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hz0, map_one, one_mul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Submodule.smul_mem _ _ hf, _, N', _, k1 hU,
      trivAt_act (triv bad (Dvd.intro_left _ rfl)) hT, hM', hN', k2 P hP, fun p y => ?_⟩)
    obtain ⟨v', hv', e⟩ := hz p.R y _ (hv p y)
    have e2 : (z⁻¹ • f) p y = v' := by
      change z⁻¹ • f p y = v'
      rw [e, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul]
    rw [e2]
    exact hv'

end GlobalTheory.DatumMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory GlobalTheory.TriMove GlobalTheory.Mem.Isom

namespace GlobalTheory.TriMoveConst

variable {D : D7}

def kapME {V V' : HSp D} (I : IsoMat V V') : GA D V ≃ᵐ GA D V' :=
  (Homeomorph.mk I.kap.toEquiv I.continuous_kap I.continuous_kap_symm).toMeasurableEquiv

theorem kapME_apply {V V' : HSp D} (I : IsoMat V V') (g : GA D V) : kapME I g = I.kap g := rfl

theorem preimage_kapME {V V' : HSp D} (I : IsoMat V V') (s : Set (GA D V)) : kapME I ⁻¹' (I.kap.symm ⁻¹' s) = s := by
  ext g
  simp only [Set.mem_preimage, kapME_apply, MulEquiv.symm_apply_apply]

theorem trH_symm_trH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (F : WO S T → ℂ) :
    trH IS.symm IT.symm (trH IS IT F) = F := by
  funext w
  show F ((homMap IS IT).symm (homMap IS IT w)) = F w
  rw [AddEquiv.symm_apply_apply]

theorem thetaKO_omH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T')
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) (F : WO S T → ℂ) :
    thetaKO (omH IS IT om) (IS.kap g) (IT.kap h) (trH IS IT F) = thetaKO om g h F := by
  unfold thetaKO
  rw [omH_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, trH_symm_trH]
  show (om (g, h) F) ((homMap IS IT).symm 0) = _
  rw [map_zero]

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

theorem ker_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) (g : GA D B) :
    (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) (IA.kap g) = Y.ker ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ true IA IW Y.rA.s Y.rA.B Y.rW.s Y.rW.B (Y.f t) P
  have hs : ∀ {k : ℕ} (s : Matrix (Fin k) (Fin k) ℂ), GlobalTheory.Grid.sgnM true s = -s := fun _ => rfl
  simp only [hs] at hF
  exact (congrArg (thetaKO (omH IA IW (Y.ω t)) (IA.kap g) (IW.kap h)) hF).trans (thetaKO_omH IA IW (Y.ω t) g h _)

theorem ker'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) (g : GA D B') :
    (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) (IA'.kap g) = Y.ker' ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ false IA' IW Y.rA'.s Y.rA'.B Y.rW.s Y.rW.B (Y.f' t) P
  show thetaKO (omH IA' IW (Y.ω' t)) (IA'.kap g) (IW.kap h) (pureTensorO ψ θ (GlobalTheory.Grid.sgn false A') WW
      (fun τ => GlobalTheory.Grid.sgnM false (cartMove IA' τ (Y.rA'.s τ))) (fun τ => cartMove IW τ (Y.rW.s τ))
      (fun τ => basMove IA' τ (Y.rA'.B τ)) (fun τ => basMove IW τ (Y.rW.B τ)) (trH IA' IW (Y.f' t))
      (polMove IW.rank_eq IA'.rank_eq P)) =
    thetaKO (Y.ω' t) g h (pureTensorO ψ θ (GlobalTheory.Grid.sgn false B') WW₁ (fun τ => GlobalTheory.Grid.sgnM false (Y.rA'.s τ)) Y.rW.s Y.rA'.B
      Y.rW.B (Y.f' t) P)
  rw [hF, thetaKO_omH]

theorem I_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) = Y.I ψ θ t P h := by
  show ∫ g in IA.kap.symm ⁻¹' Y.fd, (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) g
      ∂(Y.m.map (kapME IA)) = _
  rw [setIntegral_map_equiv (kapME IA), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd, F g ∂Y.m) (funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g)

theorem I'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) = Y.I' ψ θ t P h := by
  show ∫ g in IA'.kap.symm ⁻¹' Y.fd', (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) g
      ∂(Y.m'.map (kapME IA')) = _
  rw [setIntegral_map_equiv (kapME IA'), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd', F g ∂Y.m') (funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g)

theorem integrableOn_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd
      (triMove IA IA' IW Y).m ↔ IntegrableOn (Y.ker ψ θ t P h) Y.fd Y.m := by
  show IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (IA.kap.symm ⁻¹' Y.fd)
      (Y.m.map (kapME IA)) ↔ _
  rw [IntegrableOn, (kapME IA).restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) ∘ kapME IA = Y.ker ψ θ t P h :=
    funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem integrableOn'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd'
      (triMove IA IA' IW Y).m' ↔ IntegrableOn (Y.ker' ψ θ t P h) Y.fd' Y.m' := by
  show IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (IA'.kap.symm ⁻¹' Y.fd')
      (Y.m'.map (kapME IA')) ↔ _
  rw [IntegrableOn, (kapME IA').restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) ∘ kapME IA' = Y.ker' ψ θ t P h :=
    funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem isConst_triMove : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  intro D T₀ A A' WW B B' WW₁ IA IA' IW Y ψ θ hθ c hY
  obtain ⟨hc, P, P', H⟩ := hY
  refine ⟨hc, polMove IW.rank_eq IA.rank_eq P, polMove IW.rank_eq IA'.rank_eq P', fun t => ?_⟩
  obtain ⟨hint, ⟨h0, hne⟩, heq⟩ := H t
  refine ⟨fun h' => ?_, ⟨IW.kap h0, ?_⟩, fun h' => ?_⟩
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    exact ⟨(integrableOn_move IA IA' IW Y ψ θ hθ t P h).2 (hint h).1,
      (integrableOn'_move IA IA' IW Y ψ θ hθ t P' h).2 (hint h).2⟩
  · rw [I'_move IA IA' IW Y ψ θ hθ t P' h0]
    exact hne
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    rw [I_move IA IA' IW Y ψ θ hθ t P h, I'_move IA IA' IW Y ψ θ hθ t P' h]
    exact heq h

end GlobalTheory.TriMoveConst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConst_seesawTriple_transport_isometries : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  first | exact @GlobalTheory.TriMoveConst.isConst_triMove | exact GlobalTheory.TriMoveConst.isConst_triMove | (intros; apply GlobalTheory.TriMoveConst.isConst_triMove <;> assumption)
end
end
