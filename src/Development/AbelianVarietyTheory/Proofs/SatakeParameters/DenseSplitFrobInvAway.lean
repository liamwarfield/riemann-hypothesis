module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelSharpWeights
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitAttUniq

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem repIso_of_dense {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
    (r r' : G E Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (D : Set (G E Ω)) (hD : Dense D)
    (he : ∀ g ∈ D, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    UpperTheory.V.Af.RepIso r r' := by
  have hcp : ∀ g : G E Ω, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc)
    have h2 : Continuous fun g : G E Ω => (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc')
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    intro σ hσ
    simp only [he σ hσ]
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' hcp
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.SplitAttUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PolarizedSat

theorem hasSat_conjPlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  intro hF E _ _ _ a π χ hpol
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (compNorm E χ).UnrAt w :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) B :=
    (conjSrc_injective _).tendsto_cofinite.eventually (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π)
  filter_upwards [hu, hs] with w hw hB'e B hB
  obtain ⟨B', hB'⟩ := hB'e
  have e := UpperTheory.V.Br.satOfPol E a π _ hpol.dual w hw B B' hB hB'
  have e2 : B' = B.map fun α => α⁻¹ * (compNorm E χ).val w := by
    have e3 := congrArg (Multiset.map fun z : ℂˣ => z⁻¹) e
    rw [Multiset.map_map, Multiset.map_map] at e3
    simp only [Function.comp_def, inv_inv, Multiset.map_id'] at e3
    rw [e3]
    exact Multiset.map_congr rfl fun α _ => by rw [mul_inv_rev, inv_inv, mul_comm]
  rw [← e2]
  exact hB'

end GlobalTheory.PolarizedSat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlaceStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  first | exact @GlobalTheory.PolarizedSat.hasSat_conjPlace | exact GlobalTheory.PolarizedSat.hasSat_conjPlace | (intros; apply GlobalTheory.PolarizedSat.hasSat_conjPlace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.posTie_at : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; PosTie (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) ∧ ∀ r : D.what₂.LL, ι (D.what₂.embLL r) = algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w] (ex.cmp.embW u w hg r)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  refine ⟨fun v s x => ?_, fun r => ?_⟩
  · have h := hS v s x
    have hz : (embT D (hT.gat_pos u w hg ⟨v, s⟩)) x ∈ TaylorLogMetric.Qbar := by
      rw [← tEL_emb]
      exact Formalism.L2.G.embLL_mem_alg D _
    have he : TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x = embT D (hT.gat_pos u w hg ⟨v, s⟩) x := rfl
    have hL : TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) = ι ((embT D (hT.gat_pos u w hg ⟨v, s⟩)) x) := by
      unfold TaylorLogMetric.lamC
      rw [dite_eq_left (he ▸ hz)]
      rw [hι ⟨_, hz⟩]
      rfl
    rw [← hL, h, Formalism.L2.Herm.star_conj]
    rfl
  · have hz := Formalism.L2.G.embLL_mem_alg D r
    rw [hι ⟨_, hz⟩, ← S.hK r hz]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeights
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem liftWt_of_lt (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) (r : ℕ) (hr : r < m + j * (t + 1) + 1) (h : r < m + 1) :
    liftWt t m lam w j ⟨r, hr⟩ = lam ⟨r, h⟩ := by
  simp [liftWt, h]

theorem liftWt_blk (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j b : ℕ) (hr : m + 1 + b * (t + 1) < m + j * (t + 1) + 1) :
    liftWt t m lam w j ⟨m + 1 + b * (t + 1), hr⟩ = -w (b + 1) := by
  have hd : b * (t + 1) / (t + 1) = b := Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [liftWt]
  rw [dite_eq_right (show ¬ (m + 1 + b * (t + 1) < m + 1) by omega)]
  simp only [Nat.add_sub_cancel_left, hd]


set_option maxHeartbeats 1000000 in
theorem wtOK_sites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → WtOK (sysS H X std) D (hT.gat_pos u w hg) u μ j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj ⟨a⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hw0 := ((H.core j hj1) (((I.at' j hj1).st.eC.symm a).1)).wt
  have hrk := ((I.at' j hj1).st.loc (((I.at' j hj1).st.eC.symm a).1)).rk
  unfold WtTie at hw0
  rw [J.pos j hj1] at hw0
  have ht : (sysS H X std).t = D.R.t := X.fl_t
  have hk : (sysS H X std).G.P.m + 1 = D.R.k := by
    have := (lev0At J.Gd u w hg).A.rk
    simpa [Ranks.N] using this
  set pos := hT.gat_pos u w hg with hpos
  have hA : ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)) (r : ℕ) (hr : r < (sysS H X std).G.P.m + 1),
      (((sysS H X std).G.P.lam0 v s ⟨r, hr⟩ : ℤ) : ℚ) = hcToWeightQ (D.hcW u (pos ⟨v, s⟩)).u ⟨r, by omega⟩ := by
    intro v s r hr
    have hr' : r < (sysS H X std).G.P.m + (j + 1) * ((sysS H X std).t + 1) + 1 := by omega
    have h1 := hw0 v s ⟨r, hr'⟩
    have h3 : (gatJ Lv (j + 1)).P.lam0 v s ⟨r, hr'⟩ = (sysS H X std).G.P.lam0 v s ⟨r, hr⟩ :=
      liftWt_of_lt (sysS H X std).t (sysS H X std).G.P.m ((sysS H X std).G.P.lam0 v s) (fun i => (sysS H X std).w v i s) (j + 1) r hr' hr
    rw [h3] at h1
    rw [h1]
    have h2 := (I.at' j hj1).M.lam_eq (j + 1) hj1 (pos ⟨v, s⟩) ((finCongr hrk) ⟨r, hr'⟩)
    rw [dite_eq_left (show ((finCongr hrk) ⟨r, hr'⟩ : ℕ) < D.R.k from (by simp; omega))] at h2
    exact h2
  have hB : ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)) (b : ℕ) (hb : b ≤ j),
      (((sysS H X std).w v (b + 1) s : ℤ) : ℚ) = wG D.R ((D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩) (b + 1) := by
    intro v s b hb
    have hlt : b * ((sysS H X std).t + 1) < (j + 1) * ((sysS H X std).t + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.succ_pos _)
    have hr' : (sysS H X std).G.P.m + 1 + b * ((sysS H X std).t + 1) < (sysS H X std).G.P.m + (j + 1) * ((sysS H X std).t + 1) + 1 := by
      omega
    have h1 := hw0 v s ⟨_, hr'⟩
    have h3 : (gatJ Lv (j + 1)).P.lam0 v s ⟨_, hr'⟩ = -((sysS H X std).w v (b + 1) s) :=
      liftWt_blk (sysS H X std).t (sysS H X std).G.P.m ((sysS H X std).G.P.lam0 v s) (fun i => (sysS H X std).w v i s) (j + 1) b hr'
    rw [h3] at h1
    have h2 := (I.at' j hj1).M.lam_eq (j + 1) hj1 (pos ⟨v, s⟩) ((finCongr hrk) ⟨_, hr'⟩)
    have hv : ((finCongr hrk) ⟨_, hr'⟩ : ℕ) = D.R.k + b * (D.R.t + 1) := by
      simp only [finCongr_apply, Fin.coe_cast]
      rw [← hk, ← ht]
    have hd : (D.R.k + b * (D.R.t + 1) - D.R.k) / (D.R.t + 1) = b := by
      rw [Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
    have he : ∀ (b' : ℕ) (hb' : b' < D.R.m), b' = b → (D.hcW u (pos ⟨v, s⟩)).e ⟨b', hb'⟩ = (D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩ := by
      rintro b' hb' rfl; rfl
    rw [dite_eq_right (show ¬ (((finCongr hrk) ⟨_, hr'⟩ : Fin _) : ℕ) < D.R.k by rw [hv]; omega)] at h2
    rw [he _ _ (by rw [hv, hd]), hv, hd] at h2
    have h4 : ((-((sysS H X std).w v (b + 1) s) : ℤ) : ℚ) = -wG D.R ((D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩) (b + 1) := by
      rw [h1]; exact h2
    push_cast at h4
    linarith
  have hcT : ∀ i, ((CmpJ.cTw D i : ℤ) : ℚ) = (i : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
    intro i
    obtain ⟨c, hc⟩ := D.R.t_odd
    have h2 : i * (D.R.t + 1) / 2 = i * (c + 1) := by
      rw [hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, ← mul_assoc, mul_comm i 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    simp only [CmpJ.cTw, h2]
    push_cast
    rw [hc]
    push_cast
    ring
  refine ⟨(GlobalTheory.TwV.DelB.sysS_ranks S).2.2.2 j, ?_, ?_, ?_⟩
  · intro τ i
    generalize hvs : pos.symm τ = vs
    obtain ⟨v, s⟩ := vs
    have hτ : τ = pos ⟨v, s⟩ := by rw [← hvs]; simp
    subst hτ
    have hS := Formalism.L2.KerInert.SecondKernelSharpWeights.sharp_weight_formula D ex.tw u μ j hj (pos ⟨v, s⟩) i
    have hL := (ex.tw.fm u μ).lam_eq j hj.le (pos ⟨v, s⟩) i
    have hSs := (D.chTw u μ).sSharp_eq j hj (pos ⟨v, s⟩)
    have hwj := hB v s j le_rfl
    have hk' : (D.gat u w hg).P.m + 1 = D.R.k := hk
    have hcomm := Nat.mul_comm j (D.R.t + 1)
    have hiN : i.1 < D.R.k + j * (D.R.t + 1) := by have := i.2; simp only [Ranks.N] at this; exact this
    apply Int.cast_injective (α := ℚ)
    simp only [hvs, Sys.nuv, nu]
    by_cases hr : i.1 < D.R.k
    · rw [if_pos (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1 by omega)]
      simp only [lamI]
      rw [dite_eq_left (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1 by omega)]
      have hl0 := hA v s i.1 (by omega)
      rw [dite_eq_left hr] at hL
      simp only [Nat.add_sub_cancel]
      push_cast
      simp only [Formalism.BasicNotions.wG, sExp', Ranks.N] at hwj hSs
      push_cast at hS hSs hwj
      rw [hl0]
      linarith
    · have hjt : (j + 1) * (D.R.t + 1) = j * (D.R.t + 1) + (D.R.t + 1) := by ring
      rw [if_neg (show ¬ (1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1) by omega)]
      rw [if_pos (show (sysS H X std).G.P.m + 1 < i.1 + 1 ∧ i.1 + 1 ≤ NN (sysS H X std).G.P.m (sysS H X std).t (j + 1) by
        simp only [NN]; rw [ht]; omega)]
      have hidx : (i.1 + 1 - ((sysS H X std).G.P.m + 2)) / ((sysS H X std).t + 1) = (i.1 - D.R.k) / (D.R.t + 1) := by
        rw [ht]; congr 1; omega
      have hb : (i.1 - D.R.k) / (D.R.t + 1) < j := by
        apply Nat.div_lt_of_lt_mul; omega
      have hwb := hB v s ((i.1 - D.R.k) / (D.R.t + 1)) hb.le
      rw [dite_eq_right hr] at hL
      rw [hidx]
      push_cast
      simp only [Formalism.BasicNotions.wG, sExp', Ranks.N] at hwj hSs hwb hL
      push_cast at hS hSs hwj hwb hL
      linarith
  · intro τ
    have hwj := hB (pos.symm τ).1 (pos.symm τ).2 j le_rfl
    have hp : pos ⟨(pos.symm τ).1, (pos.symm τ).2⟩ = τ := by simp
    rw [hp] at hwj
    simp only [wT]
    have hSs := (D.chTw u μ).sSharp_eq j hj τ
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hwj, hSs, hcT]
    simp only [Formalism.BasicNotions.wG, sExp', Ranks.N]
    push_cast
    ring
  · intro τ
    have hwj := hB (pos.symm τ).1 (pos.symm τ).2 j le_rfl
    have hp : pos ⟨(pos.symm τ).1, (pos.symm τ).2⟩ = τ := by simp
    rw [hp] at hwj
    simp only [wT]
    have hSd := (D.chTw u μ).sDiv_eq j hj τ
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hwj, hSd, hcT]
    simp only [Formalism.BasicNotions.wG, sExp, Ranks.N]
    push_cast
    ring

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → WtOK (sysS H X std) D (hT.gat_pos u w hg) u μ j) := by
  first | exact @GlobalTheory.TwV.DelA.wtOK_sites | exact GlobalTheory.TwV.DelA.wtOK_sites | (intros; apply GlobalTheory.TwV.DelA.wtOK_sites <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem bAt_orth_lev : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj a
  cases j with
  | zero =>
    refine ⟨?_, fun a' => rfl⟩
    exact J.Gd.cmp.B_std.1
  | succ j =>
    refine ⟨(H.core j hj _).std, fun a' => J.oneB j hj _ _⟩

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependentStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_chartBasis_orthonormal_levelIndependent : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  first | exact @GlobalTheory.TwV.DelA.bAt_orth_lev | exact GlobalTheory.TwV.DelA.bAt_orth_lev | (intros; apply GlobalTheory.TwV.DelA.bAt_orth_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometry
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.muT_det_ratA : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) ∧ ∀ k (hk : k ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) = ∏ τ, TaylorLogMetric.embT D τ γ.1.det ^ e τ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj
  obtain ⟨e, he, hz⟩ := S.law.mu_rat j hj
  refine ⟨e, he, fun k hk γ hγ => ?_⟩
  have hu := ((GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S) k hk).2 γ hγ
  have key : Matrix.GeneralLinearGroup.det (ratA D.host.F γ) =
      Formalism.L2.DIV.ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det γ) := by
    ext
    simp [ratA, Formalism.UG.bc, Formalism.L2.DIV.ratId, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [key]
  have h2 := hz (Matrix.GeneralLinearGroup.det γ) (by simpa using hu.2)
  simpa using h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometryStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacter_det_rationalIsometry : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) ∧ ∀ k (hk : k ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) = ∏ τ, TaylorLogMetric.embT D τ γ.1.det ^ e τ) := by
  first | exact @GlobalTheory.TwV.muT_det_ratA | exact GlobalTheory.TwV.muT_det_ratA | (intros; apply GlobalTheory.TwV.muT_det_ratA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertible
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertible
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem det_map_ringHom {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem frInv_fdOfCharts {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) : FrInv (fdOfCharts cp a bad) := by
  intro j La v
  simp only [fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self, det_map_ringHom]
  apply IsUnit.map
  rw [Matrix.det_mul, LinearMap.det_toMatrix']
  exact IsUnit.mul (LinearEquiv.isUnit_det' _) (Matrix.isUnits_det_units _)

theorem frames_invertible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    FrInv (J.fd std) ∧ ∀ d : Dec J std, FrInv d.fd2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have h1 : FrInv (J.fd std) := frInv_fdOfCharts _ _ _
  refine ⟨h1, fun d j La v => ?_⟩
  show IsUnit (((star (d.eM j La)).map (J.rho std v)) * (J.fd std).frM j La v).det
  rw [Matrix.det_mul, det_map_ringHom]
  exact IsUnit.mul (IsUnit.map _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d j La))) (h1 j La v)

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertibleStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siteFrames_and_changedFrames_invertible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => FrInv (J.fd std) ∧ ∀ d : Dec J std, FrInv d.fd2) := by
  first | exact @GlobalTheory.TwV.DelB.frames_invertible | exact GlobalTheory.TwV.DelB.frames_invertible | (intros; apply GlobalTheory.TwV.DelB.frames_invertible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAt
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAt
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.QuadCharUnr

theorem quadChar_unrAt_of_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hw : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))
    · exact GlobalTheory.LFun.isUnram_of_isSplit h2 hs
    · refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
      obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl
      haveI := u.isPrime
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw
  intro x hx
  have hn := GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (localIdele _ _ x)) = 1
  rw [GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]

end GlobalTheory.QuadCharUnr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAtStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | (intros; apply GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInChar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInChar
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem reGL_finCongr_twice {R : Type} [CommRing R] {a b : ℕ} (h1 : a = b) (h2 : b = a) (x : GL (Fin a) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h2) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h1) x) = x := by
  subst h1
  apply Units.ext
  ext r s
  rfl


set_option maxHeartbeats 1000000 in
theorem ptS_isPt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj La hLa
  obtain ⟨⟨hr, hx⟩, -⟩ := hD (j + 1) hj La hLa
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  refine ⟨Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2, fun v => ?_, ?_⟩
  · obtain ⟨g, hg'⟩ := (Formalism.L2.G.Cmp.isLattice_iff _ (La.2 v)).1 (hLa v)
    exact Classical.epsilon_spec (p := fun g0 : GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v) =>
      La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g0 : Matrix _ _ _)) ⟨g, by rw [hg', Formalism.L2.G.Cmp.colSpan_eq]⟩
  · have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      show (dite (j + 1 ≤ D.R.m) _ _ : PtCh _ _).y = _
      rw [dite_eq_left hj]
    rw [hx, hy, reGL_finCongr_twice]
    exact (Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩).1

end GlobalTheory.TwV.DelA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInCharStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  first | exact @GlobalTheory.TwV.DelA.ptS_isPt | exact GlobalTheory.TwV.DelA.ptS_isPt | (intros; apply GlobalTheory.TwV.DelA.ptS_isPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramified
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem ideleNorm_eq_found (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      have hm : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap
          (maximalRealSubfield E) E = GroundTheory.Global.AdeleBaseChange.adeleMap
          (maximalRealSubfield E) E := by
        ext a : 1
        apply Prod.ext
        · funext w
          open scoped NumberField.LiesOver in
          change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
          rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
        · apply FiniteAdeleRing.ext
          intro w
          change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap _ _ w _ =
            GroundTheory.Global.SemiLocal.completionMap _ w _
          rfl
      rw [hm, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem ideleNorm_localIdele (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (y : (w.adicCompletion E)ˣ) :
    ideleNorm E (localIdele E w y) = localIdele (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))
      (GroundTheory.LocalField.normUnits _ (w.adicCompletion E) y) := by
  rw [ideleNorm_eq_found]
  exact GroundTheory.Global.ideleNorm_finiteEmbedding (K := maximalRealSubfield E) w y

end GlobalTheory.NormBelow

namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem unrAt_under_of_compNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w →
    χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  intro E _ _ _ χ w _ hur hχ x hx
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 :=
    Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 (maximalRealSubfield E))
  haveI : w.asIdeal.LiesOver (w.under (𝓞 (maximalRealSubfield E))).asIdeal := ⟨rfl⟩
  have hxm : x ∈ (Submonoid.ofClass ((w.under (𝓞 (maximalRealSubfield E))).adicCompletionIntegers
      (maximalRealSubfield E))).units := by
    unfold IsUnitAt at hx
    refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  obtain ⟨y, hy, hyn⟩ := GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one _ w he hxm
  have hyu : IsUnitAt w y := by
    obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 hy
    have h1' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
    have h2' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
    unfold IsUnitAt
    refine le_antisymm h1' ?_
    have e : Valued.v (y : w.adicCompletion E) * Valued.v ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : _) = _ := e.symm
      _ ≤ Valued.v (y : w.adicCompletion E) := mul_le_of_le_one_right' h2'
  have key : χ.loc (w.under (𝓞 (maximalRealSubfield E))) x = (compNorm E χ).loc w y := by
    show χ.1 (localIdele _ _ x) = χ.1 (ideleNorm E (localIdele E w y))
    rw [ideleNorm_localIdele]
    congr 2
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    exact hyn.symm
  rw [key]
  exact hχ y hyu

end GlobalTheory.NormBelow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramifiedStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w → χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.NormBelow.unrAt_under_of_compNorm | exact GlobalTheory.NormBelow.unrAt_under_of_compNorm | (intros; apply GlobalTheory.NormBelow.unrAt_under_of_compNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealAtSuccIffDecompositionValues
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepTwistAtClassRepEqCharPowDet
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepTwistAtClassRepEqCharPowDet
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem castSt_y_castCls {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) : (castSt h S).y (castCls h i c) = S.y c := by
  subst h; rfl

theorem exists_isDetOf_uPts (D : D7) (i : ℕ) (hi : i ≤ D.R.m)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 := by
  have hd := det_unitary_adelic_point_gram_step_norm_one D i hi x
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1)).toMonoidHom (Matrix.GeneralLinearGroup.det x.1), ?_⟩, ?_⟩
  · simp only [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, Formalism.L2.DIV.conjId] at hd
    have hd' := congrArg Units.val hd
    simp only [Units.val_mul, Units.coe_map, Units.val_one, MonoidHom.coe_coe] at hd'
    show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, Matrix.scalar_apply, inclE]
    rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]
    exact hd'
  · ext
    simp [Formalism.L2.Herm.IsDetOf, Matrix.GeneralLinearGroup.det]

theorem tw_at_rep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β c
  obtain ⟨y, hy⟩ := exists_isDetOf_uPts D (j + 1) hj (((I.at' j hj).st.K β).y c)
  rw [J.tw j hj β _ y hy]
  have hrep : (J.St (j + 1) hj).y (castCls (X.onCh j hj) (j + 1) c.1) = ((I.at' j hj).st.K β).y c := by
    have e := J.st j hj
    revert e
    generalize J.St (j + 1) hj = St'
    intro e
    subst e
    rw [castSt_y_castCls]
    exact (GlobalTheory.TwU.StepCharts.y_eq (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) c).symm
  rw [J.tie.dt (j + 1) hj _ y (by rw [hy, hrep])]

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepTwistAtClassRepEqCharPowDetStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepTwist_at_classRep_eq_charPow_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  first | exact @GlobalTheory.TwV.tw_at_rep | exact GlobalTheory.TwV.tw_at_rep | (intros; apply GlobalTheory.TwV.tw_at_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealAtSuccIffDecompositionValues
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_ofStepIn_read {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (β : S.Ch) (c : {c // S.chOf c = β}) (c' : C'.cls i) (hc' : c' = castCls h i c.1) :
    (St.y c').1 = ((S.K β).y c).1 ∧
    (∀ κ' : (St.K (St.chOf c')).lev.U, ∃ κ : (S.K β).lev.U, κ.1 = κ'.1 ∧
      (((S.K β).lev.chi κ : ℂˣ) : ℂ) = (((St.K (St.chOf c')).lev.chi κ' : ℂˣ) : ℂ)) ∧
    ∀ (φ : C'.cls i → C'.Y i → ℂ) (z : Fr D i hi), φ c' (St.eY.symm z) = trC h i φ c.1 (S.eY.symm z) := by
  subst hSt hc' h
  obtain ⟨c, rfl⟩ := c
  exact ⟨rfl, fun κ' => ⟨κ', rfl, rfl⟩, fun φ z => rfl⟩

theorem nrmR_apply_eq {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (β : S.Ch) (φ : C.cls i → C.Y i → ℂ) (c : {c // S.chOf c = β}) (z : Fr D i hi) :
    nrmR S β φ c z = S.kTw β * (((S.tw β).ch ((S.K β).y c) : ℂ) * detF (cTw D i) z * φ c.1 (S.eY.symm z)) := rfl

end GlobalTheory.TwV.DelA


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.TwV.DelA.realAt_succ_decomp : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ (c : {c // (I.at' j hj).st.chOf c = ((I.at' j hj).st.eC.symm La.1).1}) (κ : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U), castCls (X.onCh j hj) (j + 1) c.1 = clsAt X H (j + 1) La.1 La.2 ∧ κ.1 = (d.kap (j + 1) hj La).1 ∧ ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 = (((I.at' j hj).st.K _).y c).1 ∧ ∀ φ V, RealAt d (j + 1) hj h La φ V ↔ ∀ z z' : Fr D (j + 1) hj, IsTr (atInf (embT D) (d.gam (j + 1) hj La).1) z' z → evC (gatJ Lv (j + 1)).P ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk (I.at' j hj).st.pos (gramC (gramN D (j + 1) hj) (embT D)) (crdB (embT D) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).B) V z = ((((I.at' j hj).st.K _).lev.chi κ : ℂˣ) : ℂ) * nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) c z') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  have hcls : clsAt X H (j + 1) La.1 La.2 = castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) :=
    clsAt_succ X H j hj La.1 La.2
  obtain ⟨hy, hk, hφ⟩ := GlobalTheory.TwV.DelA.castSt_ofStepIn_read (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj) _
    ⟨_, hc⟩ _ hcls
  obtain ⟨κ, hκ1, hκχ⟩ := hk (d.kap (j + 1) hj La)
  refine ⟨⟨_, hc⟩, κ, hcls.symm, hκ1, hy, fun φ V => ?_⟩
  have htw := GlobalTheory.T.stepTwist_at_classRep_eq_charPow_det S j hj _ ⟨_, hc⟩
  unfold RealAt
  refine forall_congr' fun z => forall_congr' fun z' => imp_congr_right fun _ => ?_
  have hR : d.chi (j + 1) hj La * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1) *
        dPow (bAt J (j + 1) hj La.1).1 (fun _ => -(cTw D (j + 1))) * detF (cTw D (j + 1)) z' *
        φ (clsAt X H (j + 1) La.1 La.2) ((J.St (j + 1) hj).eY.symm z') =
      ((((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.chi κ : ℂˣ) : ℂ) *
        nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) ⟨_, hc⟩ z' := by
    have a1 : d.chi (j + 1) hj La = ((((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.chi κ : ℂˣ) : ℂ) := hκχ.symm
    have a2 : ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1) =
        (((I.at' j hj).st.tw ((I.at' j hj).st.eC.symm La.1).1).ch (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩) : ℂ) := by
      rw [htw, Units.val_zpow_eq_zpow_val, hcls]
    have a3 : dPow (bAt J (j + 1) hj La.1).1 (fun _ => -(cTw D (j + 1))) = (I.at' j hj).st.kTw ((I.at' j hj).st.eC.symm La.1).1 := rfl
    rw [a1, a2, a3, hφ φ z', GlobalTheory.TwV.DelA.nrmR_apply_eq]
    ring
  simp only [J.pos j hj]
  refine Iff.trans (Eq.congr_right hR) ?_
  exact Iff.rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealAtSuccIffDecompositionValuesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realAt_succ_iff_decomposition_values : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ (c : {c // (I.at' j hj).st.chOf c = ((I.at' j hj).st.eC.symm La.1).1}) (κ : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U), castCls (X.onCh j hj) (j + 1) c.1 = clsAt X H (j + 1) La.1 La.2 ∧ κ.1 = (d.kap (j + 1) hj La).1 ∧ ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 = (((I.at' j hj).st.K _).y c).1 ∧ ∀ φ V, RealAt d (j + 1) hj h La φ V ↔ ∀ z z' : Fr D (j + 1) hj, IsTr (atInf (embT D) (d.gam (j + 1) hj La).1) z' z → evC (gatJ Lv (j + 1)).P ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk (I.at' j hj).st.pos (gramC (gramN D (j + 1) hj) (embT D)) (crdB (embT D) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).B) V z = ((((I.at' j hj).st.K _).lev.chi κ : ℂˣ) : ℂ) * nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) c z') := by
  first | exact @GlobalTheory.TwV.DelA.realAt_succ_decomp | exact GlobalTheory.TwV.DelA.realAt_succ_decomp | (intros; apply GlobalTheory.TwV.DelA.realAt_succ_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoords
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem realAt_iff_realises : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) (e : D.what₂.Tau → ℤ) (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), (∀ y, φ (clsAt X H j La.1 La.2) y = (∏ τ, (D.chTw u μ).de j y τ ^ e τ)⁻¹ * frPoly (t.O u μ) j P y) → ∀ V, RealAt d j hj h La φ V ↔ Realises (sysS H X std) D (hT.gat_pos u w hg) j h (fun τ => e τ - cTw D j) (sPt d j hj La • P) (actC (sysS H X std) D (hT.gat_pos u w hg) j h (mM d j hj La) V)) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj h La e φ P hφ V
  have hp := J.pins.frm j hj
  have hde := (t.O u μ).frm_de j hj

  have hdetU : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, IsUnit ((A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det := by
    intro A τ
    have e1 := RingHom.map_det (embT D τ) (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)
    rw [RingHom.mapMatrix_apply] at e1
    rw [← e1]
    exact (Matrix.isUnits_det_units A).map _
  have hmul : ∀ (A A' : GL (Fin (D.R.N j)) D.host.E) τ, ((A * A' : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) =
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * (A' : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) := by
    intro A A' τ
    rw [Units.val_mul, Matrix.map_mul]
  have hinv : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv' : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMB : mM d j hj La * (bAt J j hj La.1)⁻¹ = J.A.crd j hj * (d.gam j hj La)⁻¹ := by
    unfold mM
    exact mul_inv_cancel_right _ _
  have hat : ∀ τ, (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) =
      (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
        ((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) := by
    intro τ
    rw [hMB, ← hmul]
    rfl

  have alg : ∀ (z' : Fr D j hj) (f : Fr1 D (D.R.N j)),
      (∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ) →
      d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
          dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' *
          φ (clsAt X H j La.1 La.2) ((J.St j hj).eY.symm z') =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * GL3Theta.evFr D (sPt d j hj La • P) f.1 := by
    intro z' f hf
    have hfr : (t.O u μ).frm j ((J.St j hj).eY.symm z') = f.1 := by
      funext τ
      rw [hp, Equiv.apply_symm_apply, hf]
      rfl
    have hfp : frPoly (t.O u μ) j P ((J.St j hj).eY.symm z') = GL3Theta.evFr D P f.1 := by
      rw [← hfr]
      rfl
    have hdef : ∀ τ, (D.chTw u μ).de j ((J.St j hj).eY.symm z') τ = (f.1 τ).det := fun τ => by rw [hde, hfr]
    have hsm : GL3Theta.evFr D (sPt d j hj La • P) f.1 = sPt d j hj La * GL3Theta.evFr D P f.1 := by
      unfold GL3Theta.evFr
      rw [MvPolynomial.smul_eval]
    rw [hφ, hfp, hsm]
    simp only [hdef]
    have ha : ∀ τ, embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det ≠ 0 := fun τ =>
      ((Matrix.isUnits_det_units (J.A.crd j hj)).map (embT D τ)).ne_zero
    have hw : ∀ τ, (z'.1 τ).det ≠ 0 := fun τ => (z'.2 τ).ne_zero
    have hdf : ∀ τ, (f.1 τ).det = embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det * (z'.1 τ).det := by
      intro τ
      rw [hf, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
    have huB : dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) =
        ∏ τ, (embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det *
          embT D τ (bAt J j hj La.1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det) ^ (-(cTw D j)) := by
      unfold dPow uB
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Units.val_mul, Matrix.det_mul, map_mul]
    have hprod : dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' * (∏ τ, (f.1 τ).det ^ e τ)⁻¹ =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) := by
      rw [huB]
      unfold dPow detF
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hdf τ]
      have h1 := ha τ
      have h2 := hw τ
      rw [mul_zpow, mul_zpow, mul_zpow, neg_sub, zpow_sub₀ h1, zpow_sub₀ h2, zpow_neg, zpow_neg]
      field_simp
    unfold sPt
    linear_combination (d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j * GL3Theta.evFr D P f.1) * hprod
  unfold RealAt Realises
  constructor
  · intro hR f
    let z' : Fr D j hj := ⟨fun τ => ((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) * f.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (f.2 τ)⟩
    let z : Fr D j hj := ⟨fun τ => (d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hzz : IsTr (atInf (embT D) (d.gam j hj La).1) z' z := fun τ => rfl
    have hf' : ∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ := by
      intro τ
      show _ = _ * (_ * _)
      rw [← Matrix.mul_assoc, hinv', Matrix.one_mul]
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat]
      show _ = _ * _ * (_ * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul, hf']
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [← key, hR z z' hzz, alg z' f hf']
  · intro hR z z' hzz
    let f : Fr1 D (D.R.N j) := ⟨fun τ => (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat, hzz τ]
      show _ = _ * _ * ((d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul]
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [key, hR f, alg z' f (fun τ => rfl)]

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoordsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) (e : D.what₂.Tau → ℤ) (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), (∀ y, φ (clsAt X H j La.1 La.2) y = (∏ τ, (D.chTw u μ).de j y τ ^ e τ)⁻¹ * frPoly (t.O u μ) j P y) → ∀ V, RealAt d j hj h La φ V ↔ Realises (sysS H X std) D (hT.gat_pos u w hg) j h (fun τ => e τ - cTw D j) (sPt d j hj La • P) (actC (sysS H X std) D (hT.gat_pos u w hg) j h (mM d j hj La) V)) := by
  first | exact @GlobalTheory.TwV.DelA.realAt_iff_realises | exact GlobalTheory.TwV.DelA.realAt_iff_realises | (intros; apply GlobalTheory.TwV.DelA.realAt_iff_realises <;> assumption)
end
end
