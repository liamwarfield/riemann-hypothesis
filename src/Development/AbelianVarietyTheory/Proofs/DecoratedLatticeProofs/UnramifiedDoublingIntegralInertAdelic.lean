module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticExtensionCharactersPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumDoublingInert
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.DoublingSumU


set_option maxHeartbeats 1000000 in
theorem hasSum_doubling_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ χ : Lˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ m : ℕ, ((χ ϖ : ℂˣ) : ℂ) = (-1) ^ m → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q (χ ϖ) s) α) → (∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g)) ∧ HasSum (fun a : GU σ n ⧸ KU σ n => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n a.out) * ℓ (ρ a.out x)) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL q n α (χ ϖ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac q n m s * ℓ x) := by
  intro hD L _ _ _ ϖ σ q n hU χ hχ m hm s Φ hΦ V _ _ ρ x α hx ℓ hℓ hdom
  have hright : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) := by
    intro g k hk
    obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU g
    rw [mul_assoc (a * t) b k, GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha _ (mul_mem hb hk),
      GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb]
  refine ⟨hright, ?_⟩
  obtain ⟨h0, h1⟩ := GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal L ϖ σ q n hU V ρ x α hx ℓ hℓ
  by_cases hx0 : ℓ x = 0
  · simp only [h0 hx0, hx0, mul_zero]
    exact hasSum_zero
  · have hw := h1 hx0
    letI : MeasurableSpace (GU σ n) := borel _
    haveI : BorelSpace (GU σ n) := ⟨rfl⟩
    obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
    have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1
    obtain ⟨hint, -, hval⟩ := (hD L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α _ hw).1 (hdom hx0)
    have hval' := hval m hm
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) * (ℓ (ρ (g * k) x) / ℓ x) =
        Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x) := fun g k hk => by
      have h2 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h2
      rw [hright g k hk, h2]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK
      (fun g => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x)) _ hF hs.hasSum).2
    have hS := hs.hasSum
    rw [← hci, hval'] at hS
    have h3 := hS.mul_right (ℓ x)
    simpa only [mul_assoc, div_mul_cancel₀ _ hx0] using h3

end GlobalTheory.DoublingSumU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvInertEqStdL
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LocZetaInertAd

theorem domain_of_bound {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (α : Fin (n / 2) → ℂˣ) {ε : ℂ} (hε : ‖ε‖ = 1) {s : ℂ}
    (hs : (n : ℝ) < s.re) (hα : ∀ i, ‖((α i : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) ∧
      ‖(((α i)⁻¹ : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s) α := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hy : ‖GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s‖ = (q : ℝ) ^ (-(2 * s.re + 1)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
  have hQ : ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) = (q : ℝ) ^ (n : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have key : (q : ℝ) ^ (-(2 * s.re + 1)) * (q : ℝ) ^ (n : ℝ) < 1 := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(2 * s.re + 1)) := (Real.rpow_pos_of_pos hq0 _).le
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hy]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  · rw [hy]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((hα i).1.trans hQ.le) hpos) key
  · rw [hy]
    have := (hα i).2
    rw [Units.val_inv_eq_inv_val, norm_inv] at this
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (this.trans hQ.le) hpos) key

end GlobalTheory.LocZetaInertAd

namespace GlobalTheory.LocZetaInertAd

set_option maxHeartbeats 400000 in
theorem localZetaOn_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hU D hPB A L hL χ b hχ hRes v hv hunr μ hμ hμK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨-, V, _, _, ρ, x, ℓ, hpar, hℓ, hcx⟩ := hc'
  have hfix := (hpar w h).mem_fixed
  rcases hpar w h with ⟨hsplit, -⟩ | ⟨hw, c', ϖ0, e, α, hUI, he, hsat, hBw⟩
  · exact absurd hsplit hv
  have hϖ0 : ϖ0 ≠ 0 := by
    intro h0
    have := hUI.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let ϖ : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ0 hϖ0
  obtain ⟨hUnr, hχϖ, hχϖb, Φ, hΦ, hφΦ⟩ := GlobalTheory.KerInert.sphSec_inert D A L hL χ b hRes v w h hw (hunr w h) s φ hφ c' ϖ e hUI he
  let ρ' : Representation ℂ (Formalism.UG.GU c' A.rank) V := ρ.comp e.symm.toMonoidHom
  have hℓ' : ∀ k ∈ Formalism.UG.KU c' A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := (he.2.2 _).2 (by simpa using hk)
    have := hℓ _ hk' (e.symm g)
    simpa [ρ'] using this
  have hdom : ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY (Formalism.UG.qV D.host.F v) (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) s) α := by
    intro hx0
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, one_apply_eq_self]; exact hx0
    obtain ⟨-, hbd⟩ := hPB A L hL v hv par c hc hc1 w h
    have hN : Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq h2 hw
    have hq : 2 ≤ Formalism.UG.qV D.host.F v := hUI.2.2.2.2.2.1
    refine GlobalTheory.LocZetaInertAd.domain_of_bound hq α (GlobalTheory.LFun.norm_locChar _ _ _) (by exact_mod_cast hs) fun i => ?_
    have h1 := hbd (α i) (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    have h3 := hbd (α i)⁻¹ (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    rw [hN] at h1 h3
    exact ⟨h1, h3⟩
  obtain ⟨hΦK, hsum⟩ := GlobalTheory.DoublingSumU.hasSum_doubling_inert hU (w.adicCompletion D.host.E) ϖ c' (Formalism.UG.qV D.host.F v) A.rank hUI
    (GlobalTheory.LFun.locChar χ⁻¹ w) hUnr b hχϖb s Φ hΦ V ρ' x α hsat ℓ hℓ' hdom
  have hsum' : HasSum (fun a : Gv A v ⧸ stabLoc D.sp.cm.sig A.gram L v =>
      φ (ioAt A v a.out) * c a.out)
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (Formalism.UG.qV D.host.F v) A.rank α (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) (s + 1 / 2) /
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (Formalism.UG.qV D.host.F v) A.rank b s * ℓ x) := by
    refine GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e _ _ he.2.2 (fun g => φ (ioAt A v g) * c g) ?_ _ ?_
    · intro g k hk
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, mul_apply_eq_comp,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]
    · have hfun : ∀ a : Formalism.UG.GU c' A.rank ⧸ Formalism.UG.KU c' A.rank, φ (ioAt A v (e.symm a.out)) * c (e.symm a.out) =
          Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c' A.rank a.out) * ℓ (ρ' a.out x) := fun a => by
        rw [hφΦ, hcx, MulEquiv.apply_symm_apply]; rfl
      simp only [hfun]
      exact hsum
  have : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  obtain ⟨hint, hval⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v) (isOpen_stabLoc _ _ _ v) hμK
    (fun g => φ (ioAt A v g) * c g) _ (fun g k hk => by
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, mul_apply_eq_comp,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]) hsum'
  refine ⟨hint, ?_⟩
  rw [hval, GlobalTheory.LFun.LvTw_div_dv_inert_eq_stdL _ _ par (GlobalTheory.LFun.val χ) v w A.rank b α s h2 hw (GlobalTheory.LFun.isUnram_of_isInertAt hw) hBw, ← hχϖ,
    hcx 1, map_one, one_apply_eq_self]

end GlobalTheory.LocZetaInertAd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_doubling_integral_inert_adelic : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.LocZetaInertAd.localZetaOn_inert | exact GlobalTheory.LocZetaInertAd.localZetaOn_inert | (intros; apply GlobalTheory.LocZetaInertAd.localZetaOn_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalComponentData
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

namespace GlobalTheory.LineOffT

theorem exists_place (E : Type) [Field E] [NumberField E] {T : ℕ} (hT : T.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ P.asIdeal := by
  have hne : Ideal.span {(T : 𝓞 E)} ≠ ⊤ := fun h => by
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases (Nat.pow_eq_one.1 h1) with h2 | h2
    · exact hT.one_lt.ne' h2
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (T : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => Nat.cast_ne_zero.2 hT.ne_zero (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

variable {D : D7}

theorem isU_nat {x : GlobalTheory.FinPl.Pl D} {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ x.asIdeal) : IsU x (incA D (N : D.host.E)) := by
  have h0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => hN (by rw [h, Nat.cast_zero]; exact zero_mem _)
  refine IsU.of_pres (inU _ h0).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul]
    exact isIntegral_natCast _
  · refine UnitAt.incA_mul_mem_intAt (c := (N : D.host.E)⁻¹) (N := (N : ℤ)) (by rwa [Int.cast_natCast]) ?_
    rw [zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel₀ h0]
    exact isIntegral_one

theorem isU_xi_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal)
    (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T) : IsU x (xiU D : AE D) := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact (isIntegral_natCast _).neg
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hdp.ne_zero
  have h0 : D.host.sqrtMinusD ≠ 0 := fun e => by
    rw [e] at hsq
    exact hd0 (by simpa using hsq.symm)
  have hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdT : Nat.Coprime D.host.d T := (Nat.coprime_primes hdp hT).2 hd.symm
  refine IsU.of_pres (xiU D).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0) (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ))
      (by rw [Int.cast_natCast]; exact UnitAt.notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_
    convert hint using 1
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]
    field_simp
    linear_combination -hsq
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0⁻¹) (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul, Host.xi0, inv_div, div_neg, div_one]
    exact ((isIntegral_natCast _).mul hint).neg

theorem isU_alpha_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal) (h2 : T ∉ D.host.small)
    (hq : T ≠ D.host.q) (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T)
    {L : Formalism.BasicNotions.TH.HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) : IsU x (α : AE D) := by
  have h := UnitAt.latA_eq_latV (UnitAt.notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd))
    (UnitAt.notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)
  obtain ⟨e, he, hg⟩ := line_gen hζ (by
    first
    | exact GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L
    | exact (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1) x
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

end GlobalTheory.LineOffT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Filter
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Inhab

variable {D : D7}

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mem_intGrp {v : Pl D} {a : AE D} : a ∈ intGrp D v ↔ a ∈ intAt D (· = v) := Iff.rfl

theorem int_mul {v : Pl D} {a b : AE D} (ha : a ∈ intGrp D v) (hb : b ∈ intGrp D v) : a * b ∈ intGrp D v :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a := by
  have h := GlobalTheory.LatAlmostStd.tmul_mem_intAt (D := D)
    (GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) fun w => by rw [map_one]; exact one_mem _) 1
  rw [mul_one] at h
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)), GlobalTheory.IdemSupport.cA_algebraMap _, h,
    fun a => ⟨fun ha => ?_, fun ha => ha ▸ Ideal.mul_mem_right _ _ h.1⟩⟩
  rw [← Algebra.smul_def]
  exact GlobalTheory.LatAlmostStd.smul_eq_of_mem_idAt ha

theorem int_cA {v : Pl D} {a : AE D} (ha : a ∈ intGrp D v) : cA D a ∈ intGrp D v := by
  obtain ⟨ε, hc, -, hid⟩ := exists_idem v
  refine ⟨(hid _).2 ?_, GlobalTheory.IdemSupport.finPart_cA_mem ha.2⟩
  conv_lhs => rw [← hc, ← map_mul, (hid a).1 ha.1]

theorem int_cA_iff {v : Pl D} {a : AE D} : cA D a ∈ intGrp D v ↔ a ∈ intGrp D v :=
  ⟨fun h => by simpa only [Formalism.L2.Theta.cA_cA] using int_cA h, int_cA⟩

theorem mulVec_mem {v : Pl D} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {y : Fin n → AE D} {i : Fin m}
    (h : ∀ j, M i j * y j ∈ intGrp D v) : (M *ᵥ y) i ∈ intGrp D v := by
  simp only [mulVec, dotProduct]
  exact sum_mem fun j _ => h j

def RatInt (v : Pl D) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Prop :=
  ∀ i j, ∀ a ∈ intGrp D v, incA D (M i j) * a ∈ intGrp D v

theorem ae_family {ι : Type} [Finite ι] {x : ι → D.host.E} (hx : x ≠ 0) :
    ∀ᶠ v : Pl D in cofinite, ∀ a, (∀ k, a * incA D (x k) ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  filter_upwards [eventually_all.2 fun j => GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x j), GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x k)⁻¹] with v h1 h2 a
  refine ⟨fun h => ?_, fun h j => by rw [mul_comm]; exact h1 j a h⟩
  have := h2 _ (h k)
  rwa [mul_left_comm, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one] at this

def Std (S : HSp D) (L : Lat S) (v : Pl D) : Prop := ∀ y, y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intGrp D v

theorem ae_std {S : HSp D} {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, Std S L v :=
  GlobalTheory.LatAlmostStd.eventually_latV_iff D S L (GlobalTheory.ProjXCols.selfDual_isFullLattice S L h)

theorem ae_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) :
    ∀ᶠ v : Pl D in cofinite, ∀ u : WO S T, u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) ↔ ∀ i j, u i j ∈ intGrp D v := by
  filter_upwards [ae_std hS, ae_std hT, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D] with v h1 h2 h3 u
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, h3]
  refine ⟨fun ⟨hm, h⟩ i j => ?_, fun h => ⟨fun i j => (h i j).1, fun y hy => (h2 _).2 fun i =>
    mulVec_mem fun j => int_mul (h i j) ((h1 y).1 hy j)⟩⟩
  have := (h2 _).1 (h (Pi.single j ε) ((h1 _).2 fun k => by
    by_cases hk : k = j
    · subst hk; rw [Pi.single_eq_same]; exact hε
    · rw [Pi.single_eq_of_ne hk]; exact zero_mem _)) i
  rw [mulVec_single] at this
  have e : u i j * ε = u i j := by rw [mul_comm]; exact (hid _).1 (hm i j)
  rw [← e]
  exact this

def RatCols {m n : ℕ} (x : Mx D m n) : Prop := ∀ i, ∃ c : Fin m → D.host.E, c ≠ 0 ∧ ∀ k, x k i = incA D (c k)

theorem RatCols.ae {m n : ℕ} {x : Mx D m n} (h : RatCols x) :
    ∀ᶠ v : Pl D in cofinite, ∀ i a, (∀ k, colMul x i a k ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨c, hc, e⟩ := h i
  simpa only [colMul, e] using ae_family hc

theorem ratCols_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : RatCols d.jX := fun i => by
  refine ⟨fun k => d.e k i, fun h => ?_, fun _ => rfl⟩
  have := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun k _ => by rw [show d.e k i = 0 from congrFun h k, mul_zero]] at this
  exact zero_ne_one this

theorem ae_colsAt {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {x : Mx D W.rank ρ} (hx : RatCols x) {LV : Lat V}
    {LW : Lat W} (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW) : ∀ᶠ v : Pl D in cofinite, ColsAt d x LV LW v := by
  filter_upwards [ae_std hV, ae_std hW, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D, (ratCols_jX d).ae, hx.ae] with v h1 h2 h3 h4 h5 i a _
  rw [h3, h1, h2, h4, h5]

theorem ae_primAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, PrimAt ψ d L v := by
  filter_upwards [ae_std h, (ratCols_jX d).ae, GlobalTheory.FinPl.Conductor.eventually_conductor D ψ hψ] with v h1 h2 h3 i j _ s hs
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  simp only [h1 _, h2]
  rw [h3 s hs]
  refine ⟨fun h => ?_, fun h a ha => int_mul h ha⟩
  have := h ε hε
  rwa [mul_comm, (hid s).1 hs] at this

theorem incAdj_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (a : AE D) (y : Mx D S.rank ρ) :
    d.incAdj S (a • y) = cA D a • (show Mx D T.rank S.rank from d.incAdj S y) := by
  show d.jY * (incA D (-D.host.xi0⁻¹) • (adj (a • y) * gA S)) = cA D a • (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
  rw [adj_smul, Matrix.smul_mul, smul_comm, Matrix.mul_smul]

theorem incAdj_yZero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {z : Fin S.rank → D.host.E} (hz : z ≠ 0)
    (hρ : 0 < ρ) : ∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, M ≠ 0 ∧ d.incAdj S (yZero S ρ z) = rat M := by
  let y : Matrix (Fin S.rank) (Fin ρ) D.host.E := of fun k i => if i.1 + 1 = ρ then -z k else 0
  have hy : yZero S ρ z = rat y := by
    ext k i
    show -(incA D (z k) * (if i.1 + 1 = ρ then 1 else 0)) = incA D (if i.1 + 1 = ρ then -z k else 0)
    split_ifs
    · rw [mul_one, RingHom.map_neg]
    · rw [mul_zero, neg_zero, RingHom.map_zero]
  refine ⟨d.e' * (-D.host.xi0⁻¹ • (yᴴ * S.gram)), fun h => hz ?_, ?_⟩
  · have h1 : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
    have h2 : -D.host.xi0⁻¹ • (yᴴ * S.gram) = 0 := by
      rw [← Matrix.one_mul (-D.host.xi0⁻¹ • _), ← h1, Matrix.mul_assoc, h, Matrix.mul_zero]
    rw [smul_eq_zero, neg_eq_zero, inv_eq_zero] at h2
    have h3 : yᴴ = 0 := by
      rw [← Matrix.mul_one yᴴ, ← mul_nonsing_inv _ (gram_isUnit_det S), ← Matrix.mul_assoc,
        h2.resolve_left (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D), Matrix.zero_mul]
    funext k
    have h4 := congrFun (congrFun (conjTranspose_eq_zero.1 h3) k) ⟨ρ - 1, by omega⟩
    simpa [y, show ρ - 1 + 1 = ρ by omega] using h4
  · rw [hy, rat_mul, rat_smul, rat_mul, rat_conjTranspose]
    rfl

section Split

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Split

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

end Frames

section Ram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ram

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.FinPl.Inhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistIdentity
noncomputable section

section General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QVecJoin
open GlobalTheory.QVec GlobalTheory.LocMod.StepVec

theorem step_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j, j + 1 < D.R.m → GlobalTheory.FinPl.Moves (c.V j) (B.b j) (B.Λ j) (v.N j) S → GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → B.b j ∈ GfC (c.V j) → B.b (j + 1) ∈ GfC (c.V (j + 1)) → IsSelfDualC _ (B.Λ j) → IsSelfDualC _ (B.Λ (j + 1)) → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V j).rank) χj vac (d : WO (c.V j) (c.V (j + 1)) →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V j) (c.V (j + 1)) sS sT (B.Λ j : Set _) (B.Λ (j + 1) : Set _) (B.β j) (B.β (j + 1)) LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ j) (B.Λ (j + 1)) S g → om (B.b j, B.b (j + 1)) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).eL j)) (om (B.b j, B.b (j + 1)) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  have hn : ∀ i, ∃ n, j + n = (G i).s := fun i => ⟨(G i).s - j, by have := (G i).hs; omega⟩
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).eL j) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain ⟨n, hn⟩ := hn i
    exact ((E i).eL_at j n hn).1
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, -, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, -, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd j (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ j (n + 1) (by omega))) mS
        ((G i).latY j (n + 1) _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' (hv.sd (j + 1) hj) hmv' _ (eb.symm.trans (stdOrd _ _ (j + 1) n (by omega))) mT
        ((G i).latY (j + 1) n _) π' hπ⟩
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, ha, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, hb, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact puts (G i).q hstep.1.2.inf hom (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd | exact hsd.1) (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd' | exact hsd'.1) _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ _ _ _ mS mT ((E i).reg.1 j n hn) rfl ((E i).eL_at j n hn)

theorem step_top : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j (h : j + 2 * 0 + 2 = D.R.m), GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → GlobalTheory.FinPl.Moves c.T B.bT B.ΛT v.NT S → B.b (j + 1) ∈ GfC (c.V (j + 1)) → B.bT ∈ GfC c.T → IsSelfDualC _ (B.Λ (j + 1)) → IsSelfDualC _ B.ΛT → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V (j + 1)).rank) χj vac (d : WO (c.V (j + 1)) c.T →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V (j + 1)) c.T sS sT (B.Λ (j + 1) : Set _) (B.ΛT : Set _) (B.β (j + 1)) B.βT LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V (j + 1)) c.T χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ (j + 1)) B.ΛT S g → om (B.b (j + 1), B.bT) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).toAt.eT j h)) (om (B.b (j + 1), B.bT) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).toAt.eT j hj) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    exact (E i).eLT_at.1
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, -, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, -, mT⟩ := (G i).frameTop
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd _ (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ _ 0 rfl)) mS
        ((G i).latY _ 0 _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' hv.sdT hmv' _ eb.symm mT (G i).latT π' hπ⟩
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, ha, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, hb, mT⟩ := (G i).frameTop
    exact puts (G i).q hstep.1.2.inf hom (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd | exact hsd.1) (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd' | exact hsd'.1) _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ (Equiv.refl _) _ _ mS mT (E i).reg.2.1 rfl (E i).eLT_at

end GlobalTheory.QVecJoin
end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QVecJoin

theorem natCast_mem_under {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem false_of_coprime_mem {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

theorem isWeilDatum_cast {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

end GlobalTheory.QVecJoin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffFrame
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelData

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.LocMod
open _root_.Formalism.L2.Col (IntAt redP qOf)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {u : D.what₂.Word}

end Gen

section Chain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (a : E) : valuation k (ι a) < 1 ↔ P.valuation E a < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have h := hi a⁻¹
  rw [GlobalTheory.AtTypeExists.intAt_iff, Valuation.mem_integer_iff, map_inv₀, map_inv₀, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 (by simpa using ha)), inv_le_one₀ (zero_lt_iff.2 (by simpa using ha))] at h
  rw [← not_le, ← not_le, h]

theorem exists_unif {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (hd : DenseRange ι) (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, (ϖ : k) = ι (qOf P : E) ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P h
  have h0 : ((qOf P : ℕ) : E) ≠ 0 := fun e => by
    rw [e, map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  have h1 : valuation k (ι (qOf P : E)) < 1 := by
    rw [val_lt_one_iff hi, hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨Units.mk0 _ ((map_ne_zero ι).2 h0), rfl, fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx h1⟩⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have h2 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨Units.mk0 (valuation k x) (by simpa using hx0), by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have h3 : valuation k (ι a) = valuation k x := by simpa using Valuation.map_add_eq_of_lt_right (valuation k) ha
  have h4 : P.valuation E a < 1 := (val_lt_one_iff hi a).1 (h3 ▸ hx)
  have h5 : IntAt P (a / (qOf P : E)) := by
    rw [GlobalTheory.AtTypeExists.intAt_iff, map_div₀, hq, div_le_one₀ WithZero.exp_pos]
    by_cases ha0 : P.valuation E a = 0
    · simp [ha0]
    · rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log ha0, WithZero.exp_le_exp]
      omega
  have h6 := (hi _).2 h5
  rw [Valuation.mem_integer_iff, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero ι).2 h0))), h3] at h6
  exact h6

theorem mul_sec (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (y : k) : x * q.sec y = q.sec (q.pr x * y) := by
  have h := q.sec_pr (x * q.sec y)
  have h' := q.sec_pr (q.sec y)
  rw [map_mul, q.pr_sec] at h
  rw [q.pr_sec] at h'
  rw [h, mul_left_comm, ← h']

end Chain

section Place

end Place

section World

variable {B : Base} {X : PreX B.toPre}

theorem type_prime {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ (B.primes X).vGs) :
    ∃ i, qOf P = B.host.g i ∧ (B.host.g i).Prime ∧ ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal ∧
      ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal ^ 2 ∧ B.host.g i ∉ B.host.small ∧ B.host.g i ≠ B.host.q ∧ B.host.g i ≠ B.host.d ∧
      B.fields.conjO (X.piG i) ∈ P.asIdeal ∧ X.piG i ∉ P.asIdeal ∧ ∀ v, X.piT v - 1 ∈ P.asIdeal := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨i, hi⟩ : ∃ i, P ∈ (B.primes X).vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  obtain ⟨h1, h2⟩ := GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi
  have hp : (B.host.g i).Prime := hPr.g_prime i
  have key : ¬ B.host.g i ∣ B.host.QS * B.host.q * B.host.d := fun h => by
    have h3 : B.host.g i ≡ 1 [MOD B.host.g i] := (hPr.g_cong i).of_dvd h
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 (h3.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))))
  have hc : B.fields.conjO (X.piG i) ∈ P.asIdeal := by
    unfold Formalism.L2.Col.Primes.vG Formalism.L2.Col.divs at hi
    split_ifs at hi with h
    · exact h.mem_toFinset.1 hi
    · simp at hi
  refine ⟨i, hPr.vG_norm i P hi, hp, h1, h2, B.host.toHostRaw.notMem_small_of_not_dvd key,
    B.host.toHostRaw.ne_q_of_not_dvd key, B.host.toHostRaw.ne_d_of_not_dvd key, hc, fun h => ?_, fun v => ?_⟩
  · obtain ⟨x, y, e⟩ := hPr.piG_cop i
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hc)))
  · refine Ideal.mem_of_dvd _ (dvd_trans ?_ (hPr.piT_cong v)) h1
    refine Nat.cast_dvd_cast (Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _)
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]

end World

end GlobalTheory.SeeSaw.LevelData

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePlacesSplitIdempotents
section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.SumExtendByZeroLeSum
noncomputable section

namespace GlobalTheory.RamValCheck

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra _root_.Formalism.L2.Pj

theorem g_coprime (D : Formalism.BasicNotions.D7) (k : Fin 2) (p : ℕ)
    (hp : p ∈ D.host.condN.primeFactors) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hdvd : p ∣ D.host.QS * D.host.q * D.host.d := Nat.dvd_of_mem_primeFactors hp
  refine Nat.Coprime.coprime_dvd_right hdvd ?_
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

end GlobalTheory.RamValCheck
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePlacesSplitIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelPlaces

theorem not_isConjPl_lev {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : ¬ Formalism.BasicNotions.IsConjPl D.host P P) :
    ¬ Formalism.IndefR.Lev.IsConjPl (D := D) P P := by
  intro hl
  apply h
  intro x y hxy
  have hs : ∀ c c' : 𝓞 D.host.E, (c' : D.host.E) = star (c : D.host.E) → c' = GlobalTheory.IdemSupport.cO D c :=
    fun c c' e => RingOfIntegers.ext (by rw [e, GlobalTheory.IdemSupport.cO_coe])
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  subst hy
  constructor
  · intro hx
    obtain ⟨c', hc', e⟩ := hl x hx
    rwa [hs _ _ e] at hc'
  · intro hx
    obtain ⟨c', hc', e⟩ := hl _ hx
    rwa [hs _ _ e, GlobalTheory.IdemSupport.cO_cO] at hc'

end GlobalTheory.LevelPlaces

namespace GlobalTheory.LevelPlaces

theorem split_unit : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ PP ∈ (pk W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) = GlobalTheory.FinPl.latV V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hpk hTy PP hPP
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hTy.1 PP hPP
  rw [Nat.cast_mul] at hg
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hgp : (D.host.g k).Prime := D.host.g_prime k

  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rw [map_natCast]; exact hk

  obtain ⟨i, hi⟩ := ((GlobalTheory.PlacesOverG.places_over_g_k D k).2.1 PP).1 hk
  have key : ∀ {v v' : HeightOneSpectrum (𝓞 D.host.F)}, v = v' → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v') := by
    rintro v _ rfl h; exact h
  have hτ : Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := by
    rcases i with w | w
    · have hi' : D.naut.plGw k w = PP := hi
      exact key (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi')
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
    · have hi' : GlobalTheory.IdemSupport.cP (D.naut.plGw k w) = PP := hi
      exact key ((GlobalTheory.IdemSupport.under_cP _).symm.trans (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi'))
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
  obtain ⟨τ⟩ := hτ
  have he := GlobalTheory.AdelicU.Supp.splitAt_splitIdemAd (D := D) τ
  have hε := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have hs := he.2.2.trans (GlobalTheory.AdelicU.Supp.pl_eq D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))
  have hsplit : IsSplitIdem D (GlobalTheory.AdelicU.Supp.splitIdemAd _ τ) := ⟨he.1, he.2.1, _, _, hε, hs⟩
  obtain ⟨p, -, hpv⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D _ _ _ hsplit hε hs

  have hne : ∀ m ∈ D.host.condN.primeFactors, D.host.g k ≠ m := fun m hm e => by
    have := GlobalTheory.RamValCheck.g_coprime D k m hm
    rw [e, Nat.coprime_self] at this
    exact hgp.one_lt.ne' (e ▸ this)
  have hc : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hgp).2 fun ⟨m, hm⟩ => ?_)
    refine hpk.aa PP (Or.inr (Or.inl hPP)) ?_
    rw [hm, Nat.cast_mul]
    exact PP.asIdeal.mul_mem_right _ hk
  have hu := GlobalTheory.FinPl.UnitAt.unitAA_of_prime p hgp (by rw [hpv]; exact hv) (UpperTheory.Ram.g_notMem_small D k)
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.q_prime, D.host.q_dvd_condN, D.host.condN_ne_zero⟩))
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.d_prime, D.host.d_dvd_condN, D.host.condN_ne_zero⟩)) hc
  unfold GlobalTheory.FinPl.SplitPt.UnitAA at hu
  rw [hpv] at hu
  exact ⟨⟨_, _, hsplit, hε, hs⟩, hu.1, hu.2⟩

end GlobalTheory.LevelPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePlacesSplitIdempotentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_places_split_idempotents : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ PP ∈ (pk W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) = GlobalTheory.FinPl.latV V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := by
  first | exact @GlobalTheory.LevelPlaces.split_unit | exact GlobalTheory.LevelPlaces.split_unit | (intros; apply GlobalTheory.LevelPlaces.split_unit <;> assumption)
end
end
