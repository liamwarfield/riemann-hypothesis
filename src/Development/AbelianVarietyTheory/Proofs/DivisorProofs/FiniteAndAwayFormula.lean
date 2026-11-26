module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
section -- merged from Development.AbelianVarietyTheory.Counterexamples.RotationExamples.SigmaMonoInConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FpTiedIffExistsLeafFP
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledValuationFormula
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

open Formalism.DivisionValues _root_.Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K]

def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}


end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
end
end

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesCompare

open Formalism.DivisionValues _root_.Formalism.L2.Indef _root_.Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

omit [NumberField K] in
theorem localization_mono' {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    {L L' : Submodule (𝓞 K) W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem primePow_anti (w : HeightOneSpectrum (𝓞 K)) {n n' : ℤ} (h : n' ≤ n) : primePow w n ≤ primePow w n' := by
  have hP : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  obtain ⟨k, rfl⟩ := Int.le.dest h
  have h1 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one
  have h2 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (n' + (k : ℤ)) ≤
      (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' := by
    rw [zpow_add₀ hP, zpow_natCast]
    calc _ ≤ (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' * 1 := by gcongr
      _ = _ := mul_one _
  exact FractionalIdeal.coe_le_coe.mpr h2

theorem scaledAt_anti {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) {n n' : ℤ}
    (h : n' ≤ n) : scaledAt w n B ≤ scaledAt w n' B := by
  refine localization_mono' _ (Submodule.span_mono ?_)
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, primePow_anti w h ha, x, hx, rfl⟩

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end GlobalTheory.FinitePlacesCompare
end
end

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesProbe

open Formalism.DivisionValues _root_.Formalism.L2.Indef _root_.Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem logArg_nonneg (O : FunData K Df) {b : ℝ} (hb : 1 ≤ b) :
    0 ≤ Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|) := by
  have e : b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)| =
      b * ((O.nr * O.g1 * O.g2 * O.pd * O.pd' * O.dE.natAbs : ℕ) : ℝ) := by
    push_cast [Nat.cast_natAbs]; ring
  rw [e]
  rcases Nat.eq_zero_or_pos (O.nr * O.g1 * O.g2 * O.pd * O.pd' * O.dE.natAbs) with h | h
  · rw [h]; simp
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hb (by exact_mod_cast h))

theorem sigma_mono_in_constant (O : FunData K Df) {C C' b : ℝ} (h : C ≤ C') (hb : 1 ≤ b) : O.Sig0 C b ≤ O.Sig0 C' b := by
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
  have : O.ee C b q ≤ O.ee C' b q := by
    unfold FunData.ee
    split_ifs
    · refine Nat.succ_le_succ (Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg _)))
      unfold FunData.PPF
      have := logArg_nonneg O hb
      gcongr
    · exact le_rfl
  exact_mod_cast this

end GlobalTheory.FinitePlacesProbe
end
end

namespace LeafFixedPointPairing
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw matLat)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.IndefR.Datum Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_localization_of_smul_mem₂ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (M : Submodule (𝓞 K) (Fin n → K)) (y : Fin n → K) (s : K) (hs : s ≠ 0) (δ : ℤ) (hv : vw w s ≤ δ) (h : s • y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
      (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) := by
  obtain ⟨t, ht, hc⟩ := unit_at_val w s hs
  have h1 : s • y ∈ Formalism.HermitianLatticesTheory.idealSmul
      (((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K) M := by
    refine Submodule.subset_span ⟨1, ?_, s • y, h, (one_smul _ _).symm⟩
    exact FractionalIdeal.mem_coe.mpr (FractionalIdeal.one_mem_one _)
  have hm := smulK_mem_idealSmul _ _ M _ hc h1
  rw [one_mul] at hm
  have e : (algebraMap (𝓞 K) K t * s⁻¹) • s • y = t • y := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, algebraMap_smul]
  rw [e] at hm
  exact GlobalTheory.FinitePlacesCompare.scaledAt_anti w M (neg_le_neg hv)
    ((PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨t, ht, hm⟩)

variable {D : D7}

theorem absNorm_splitAuxiliaryPlace_eq_prime {T : Type} {Lc : LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) :
    Ideal.absNorm P.v0.asIdeal = GlobalTheory.ChiGrid.q0 D := by
  have hp := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  have h : (Ideal.primesOver (Ideal.span {((GlobalTheory.ChiGrid.q0 D : ℕ) : ℤ)}) (𝓞 D.host.E)).ncard =
      Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact Formalism.L2.Host.split_prime_splits_completely D
  have := P.v0.isPrime
  have := (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) (E := D.host.E) hp h P.v0.asIdeal P.basePlace_over_qZero).2
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact this

theorem one_le_b (s : Formalism.BasicNotions.Scale) : 1 ≤ s.b := by
  have h : 0 ≤ s.L := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  exact Real.one_le_exp h

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem sig_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hC : CF ≤ C) :
    sig d.G ≤ (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  refine le_trans (le_of_eq ?_) (GlobalTheory.FinitePlacesProbe.sigma_mono_in_constant _ hC hb)
  show _ = ∑ q ∈ d.G.pl.S0, ((d.O.ee CF p.Z.b q : ℕ) : ℝ) * Real.log (Ideal.absNorm q.asIdeal)
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [GlobalTheory.BigTop.Fun.Model.ee_eq d (absNorm_splitAuxiliaryPlace_eq_prime d.G.pl) v]

theorem local_clause {p : PtAt ex Csz} {CF : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a)
    {dl : GlobalTheory.SumSize.PlL D → ℝ} (hloc : ∀ X' M, IsTestLat a.ch.G a.ch.rp a.ch.n a.ch.e X' M →
      ∀ t w, Away a.ch.G t w → ∀ x ∈ (p.P.A3.A.fam.R t).Mt (p.P.A3.A.fam.lvl p.F.lv2.P0 p.F.lv2.ψ0), ∀ y : Fin a.ch.n → D.what₂.LL,
        (∀ i, D.what₂.embLL (y i) = vK a.ch t (formOf p.F.lv2 t x) i) → ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ dl w ∧ s • y ∈ M)
    (hAw : AwayAt (R := p.R.toRealDat) a.ch) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) (w : GlobalTheory.SumSize.PlL D) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ((d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w)) ((Df p).Mt ((p.S false).μ w))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-((d.data (fun _ => 1) Tf dF).dF w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (d.data (fun _ => 1) Tf dF).M) := by
  intro z hz
  obtain ⟨s0, hs0, hz0⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hz
  obtain ⟨x, hx, hxz⟩ := Submodule.mem_map.mp hz0
  have e0 : (d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w) = d.V ((p.S false).μ w) := by
    show (1 : D.what₂.LL)⁻¹ • d.V _ = _
    simp
  simp only [LinearMap.coe_restrictScalars, e0] at hxz
  obtain ⟨s, hs, hv, hsM⟩ := hloc d.X' d.M hT.test ((p.S false).μ w) w (hAw w) x hx (d.V _ |>.mulVec x)
    (fun i => hT.sums _ (Or.inr ⟨w, rfl⟩) x i)
  have hy := mem_localization_of_smul_mem₂ w d.M _ s hs (dF w) (by rw [hF]; exact Int.le_floor.mpr hv) hsM
  obtain ⟨s1, hs1, h1⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hy
  refine (PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨s1 * s0, w.asIdeal.primeCompl.mul_mem hs1 hs0, ?_⟩
  rw [mul_smul, ← hxz]
  exact h1

theorem sum_clause {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) {dl : GlobalTheory.SumSize.PlL D → ℝ}
    (hsum : ∀ s : Finset (GlobalTheory.SumSize.PlL D), ∑ w ∈ s, lw w * dl w ≤ D.R.m * bOne d.G C p.Z.b / 2)
    (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) :
    2 * ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ (d.data (fun _ => 1) Tf dF).bFP C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  have hb0 : 0 ≤ p.Z.b := by linarith
  have hL : 0 ≤ Real.log p.Z.b := Real.log_nonneg hb
  have h1 : ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ ∑ w ∈ Tf, lw w * dl w := by
    refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (GlobalTheory.FinitePlacesCompare.lw_nonneg w)
    rw [hF]
    exact Int.floor_le _
  have h2 := hsum Tf
  have hS := sig_le d Tf dF hC
  have hS0 := Sig0_nonneg (d.data (fun _ => 1) Tf dF) C p.Z.b
  have hN : (d.data (fun _ => 1) Tf dF).N = bigN D := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bFP
  rw [hN]
  show _ ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * _) +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + _) * p.Z.b
  set S := (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b
  have h3 : 0 ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * S) := by
    positivity
  have h4 : (D.R.m : ℝ) * bOne d.G C p.Z.b ≤ C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + S) * p.Z.b := by
    unfold bOne
    have : (D.R.m : ℝ) * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b) =
        C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b := by ring
    rw [this]
    gcongr
  linarith

theorem leaf_at {p : PtAt ex Csz} {CF C : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a) (hC0 : 0 ≤ C) (hC : CF ≤ C)
    (hFin : FinAt p.F.lv2 a.ch C p.Z.b) (hAw : AwayAt (R := p.R.toRealDat) a.ch) :
    ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b := by
  classical
  obtain ⟨dl, ⟨-, hfin, hsum⟩, hloc⟩ := hFin
  refine ⟨hfin.toFinset, fun w => ⌊dl w⌋, ?_, fun w hw => ?_, ?_⟩
  · exact local_clause hT hloc hAw _ _ (fun _ => rfl)
  · have hw' : w ∉ hfin.toFinset := hw
    have : dl w = 0 := by simpa using hw'
    show ⌊dl w⌋ = 0
    simp [this]
  · exact sum_clause d hC0 hC hsum _ _ (fun _ => rfl)

end GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

end

end

end LeafFixedPointPairing
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.zero_app_eq {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k] (G : PDivGroup p k)
    (n : ℕ) (a : G.A n) :
    (0 : G ⟶ G).app n a = algebraMap k _ (Coalgebra.counit (R := k) a) := by
  have h := congrArg (fun u : WithConv (G.A n →ₐ[k] G.A n) => u.ofConv a)
    (map_one (toPts (R := k) (A := G.A n) (C := G.A n)))
  simp only [toPts_ofConv] at h
  exact h.trans (AlgHom.convOne_apply _)

theorem Chart.isMapOf_nmul : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  intro p _ k _ d G c μ hμ j
  induction j with
  | zero =>
    intro n i
    rw [Nat.cast_zero, zero_smul, Chart.zero_app_eq, c.aug, map_zero]
    show c.ev n ((fun _ => (0 : MvPowerSeries (Fin d) k)) i) = 0
    exact map_zero _
  | succ j ih =>
    have hX : c.IsMapOf c (𝟙 G) (fun i => (X i : MvPowerSeries (Fin d) k)) := fun n i => by
      rw [Chart.ev_X, id_app]; rfl
    have e1 : ((j + 1 : ℕ) : ℤ_[p]) • 𝟙 G = (j : ℤ_[p]) • 𝟙 G + 𝟙 G := by
      rw [Nat.cast_succ, add_smul, one_smul]
    have e2 : nmul μ (j + 1) = op μ (nmul μ j) (fun i => X i) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact Chart.isMapOf_add p k d d G G c c μ _ _ _ _ hμ ih hX

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLawStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_nmul | exact GlobalTheory.Katz.Chart.isMapOf_nmul | (intros; apply GlobalTheory.Katz.Chart.isMapOf_nmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogeny
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu WithConv

namespace GlobalTheory.Dieu

theorem hom_eq_zero_of_pow_smul_eq_zero {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k]
    {G H : PDivGroup p k} (m : ℕ) {f : G ⟶ H} (e : (p : ℤ_[p]) ^ m • f = 0) : f = 0 := by
  induction m generalizing f with
  | zero => simpa using e
  | succ m ih =>
    refine ih ?_
    refine eq_zero_of_prime_smul_eq_zero ?_
    rw [← mul_smul, ← pow_succ']
    exact e

theorem exists_comp_eq_of_kerIdeal_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q →
    kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ k _ _ G Q H m q q' f h1 h2 hk

  have hq : kerIdeal (q.app m) ≤ RingHom.ker (q'.app m : G.A m →ₐ[k] Q.A m) := by
    refine (kerIdeal_le_ker_iff (q.app m) _).2 fun c => ?_
    have e := congrArg (fun x => Hom.conv x m) h2
    simp only [pow_smul_conv] at e
    have e2 := DFunLike.congr_fun (congrArg ofConv (congrArg toPts e)) c
    rw [map_one] at e2
    refine e2.trans ?_
    rfl
  have hf := (kerIdeal_le_ker_iff (f.app m) _).1 (hk.trans hq)
  have hc : Hom.conv (q' ≫ f) m = 1 := by
    refine toPts_injective (ofConv_injective (AlgHom.ext fun c => ?_))
    rw [map_one]
    refine (hf c).trans ?_
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k Q H m (q' ≫ f) hc
  refine ⟨g, sub_eq_zero.1 (hom_eq_zero_of_pow_smul_eq_zero m ?_)⟩
  rw [smul_sub, ← Linear.comp_smul, ← hg, ← Category.assoc, h1, Linear.smul_comp,
    Category.id_comp, sub_self]

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogenyStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q → kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  first | exact @GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | exact GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | (intros; apply GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRealisationLabelsInjectiveOfGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRealisationLabelsInjectiveOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem realPt_comp_pow {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem realPt_inj_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  intro o₂ Ω₂ _ _ _ S₂ ρ₂ T G _ f φ hφ x y hxy
  have hpt : ρ₂.pt x = ρ₂.pt y := by
    ext
    exact hφ.1.hom_ext hxy (by simp only [Category.assoc, Over.w])
  have hzero : ρ₂.pt 0 = 1 := by
    have h := ρ₂.pt_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsmul : ∀ (a : S₂.Gam) (n : ℕ), ρ₂.pt (n • a) = ρ₂.pt a ^ n := by
    intro a n
    induction n with
    | zero => rw [zero_smul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, ρ₂.pt_add, ih, pow_succ]
  have hkill : ∀ a : S₂.Gam, ρ₂.pt a ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [← hsmul]
    have : (S₂.r * S₂.N) • a = 0 := by
      funext i
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    rw [this, hzero]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap ((algebraMap Ω₂ K).comp (S₂.R.val : S₂.R →+* Ω₂))
  let u : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  have hz : (u ≫ ρ₂.pt x) ^ (S₂.r * S₂.N) = 1 := by
    rw [← realPt_comp_pow, hkill, MonObj.comp_one]
  obtain ⟨a, _, huniq⟩ := ρ₂.pt_bij K x₀ (u ≫ ρ₂.pt x) hz
  have h1 := huniq x rfl
  have h2 := huniq y (by rw [hpt])
  exact h1.trans h2.symm

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRealisationLabelsInjectiveOfGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRealisation_labels_injective_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  first | exact @GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback | exact GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback | (intros; apply GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelPermOfRingEndo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelPermOfRingEndo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open Classical

namespace GlobalTheory.Poinc

theorem labelHom_of_comp_eq : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → ∀ τ : S₂.R →+* S₂.R, τ.comp om = om → ∃ gl : S₂.Gam →+ S₂.Gam, ∀ a, (ρ₂.pt (gl a)).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ hφ τ hτ
  have hsp : spMap τ ≫ spMap om = spMap om := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    conv_rhs => rw [← hτ]
    rfl
  let B := baseOver (Sp S₂.R)
  let push : (B ⟶ ρ₂.P.A) → (Over.mk (B.hom ≫ spMap om) ⟶ ρ₁.P.A) := fun x =>
    Over.homMk (x.left ≫ φ) (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w x]; rfl)
  have push_mul : ∀ x y, push (x * y) = push x * push y := fun x y =>
    Over.OverMorphism.ext (hφ.2 B x y (push x) (push y) rfl rfl).symm
  have push_inj : ∀ x y, push x = push y → x = y := fun x y e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  let V : Over.mk (B.hom ≫ spMap om) ⟶ Over.mk (B.hom ≫ spMap om) :=
    Over.homMk (spMap τ) (by show spMap τ ≫ 𝟙 _ ≫ spMap om = 𝟙 _ ≫ spMap om; rw [Category.id_comp, hsp])
  have wa : ∀ a, (spMap τ ≫ (ρ₂.pt a).left ≫ φ) ≫ ρ₁.P.A.hom = 𝟙 _ ≫ spMap om := fun a => by
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (ρ₂.pt a).left, Over.w (ρ₂.pt a)]
    show spMap τ ≫ 𝟙 _ ≫ spMap om = _
    simp only [Category.id_comp]; exact hsp
  let s : S₂.Gam → (B ⟶ ρ₂.P.A) := fun a =>
    Over.homMk (hφ.1.lift (spMap τ ≫ (ρ₂.pt a).left ≫ φ) (𝟙 _) (wa a)) (hφ.1.lift_snd _ _ _)
  have hs : ∀ a, (s a).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := fun a => hφ.1.lift_fst _ _ _
  have push_s : ∀ a, push (s a) = V ≫ push (ρ₂.pt a) := fun a => Over.OverMorphism.ext (hs a)
  have s_add : ∀ a b, s (a + b) = s a * s b := fun a b => push_inj _ _ (by
    rw [push_s, ρ₂.pt_add, push_mul, MonObj.comp_mul, push_mul, push_s, push_s])
  let sH : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A) := MonoidHom.mk' (fun a => s a.toAdd) (fun a b => s_add _ _)
  let ptH : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A) := MonoidHom.mk' (fun a => ρ₂.pt a.toAdd) (fun a b => ρ₂.pt_add _ _)
  have hn : ∀ a : S₂.Gam, (S₂.r * S₂.N) • a = 0 := fun a => funext fun i => by
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
  have tors : ∀ (F : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A)) (a : S₂.Gam),
      F (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := fun F a => by
    rw [← map_pow, ← ofAdd_nsmul, hn, ofAdd_zero, map_one]
  have ex : ∀ a, ∃ b, ρ₂.pt b = s a := fun a =>
    GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) (s a) (tors sH a)
  let K := AlgebraicClosure Ω₂
  let j : S₂.R →+* K := (algebraMap Ω₂ K).comp S₂.R.val.toRingHom
  have inj : ∀ b b', ρ₂.pt b = ρ₂.pt b' → b = b' := by
    intro b b' e
    obtain ⟨c, -, hc⟩ := ρ₂.pt_bij K (spMap j)
      ((Over.homMk (spMap j) (by simp) : Over.mk (spMap j) ⟶ baseOver (Sp S₂.R)) ≫ ρ₂.pt b)
      (by rw [← MonObj.comp_pow, show ρ₂.pt b ^ (S₂.r * S₂.N) = 1 from tors ptH b, MonObj.comp_one])
    exact (hc b rfl).trans (hc b' (by rw [e])).symm
  refine ⟨AddMonoidHom.mk' (fun a => Classical.choose (ex a)) (fun a b => inj _ _ ?_), fun a => ?_⟩
  · rw [ρ₂.pt_add, Classical.choose_spec (ex (a + b)), Classical.choose_spec (ex a), Classical.choose_spec (ex b),
      s_add]
  · show (ρ₂.pt (Classical.choose (ex a))).left ≫ φ = _
    rw [Classical.choose_spec (ex a)]
    exact hs a

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelPermOfRingEndoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaRealisation_label_perm_of_ringEndo : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → ∀ τ : S₂.R →+* S₂.R, τ.comp om = om → ∃ gl : S₂.Gam →+ S₂.Gam, ∀ a, (ρ₂.pt (gl a)).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := by
  first | exact @GlobalTheory.Poinc.labelHom_of_comp_eq | exact GlobalTheory.Poinc.labelHom_of_comp_eq | (intros; apply GlobalTheory.Poinc.labelHom_of_comp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelsOfGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelsOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PullLab

open GlobalTheory.Poinc.DeepLab

theorem exists_lab_of_isGrpPullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left) (d : ℕ), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → S₂.r * S₂.N = S₁.r * S₁.N * d → ∃ lam : S₁.Gam →+ S₂.Gam, (∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left) ∧ ∀ a', ∃ a, lam a = d • a' := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ d hpb hd
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap om) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ φ = spMap om ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [hd, pow_mul, map_pow_self, one_pow]
  have uniq : ∀ z : baseOver (Sp S₂.R) ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, p₂ (Multiplicative.ofAdd b) = z := by
    intro z hz
    obtain ⟨b, hb⟩ := GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) z hz
    refine ⟨b, hb, fun b' hb' => ?_⟩
    have h2 : (V₂ ≫ z) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) hz
      rwa [map_pow, map_one] at h3
    exact (ρ₂.pt_bij K x₀ (V₂ ≫ z) h2).unique (congrArg (V₂ ≫ ·) hb') (congrArg (V₂ ≫ ·) hb)
  obtain ⟨lam, hlam⟩ := exists_lab _ p₂ σ uniq hσL
  have hpt : ∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left := fun a => by
    have h4 := hσl (Multiplicative.ofAdd a)
    rw [← hlam a] at h4
    exact h4
  refine ⟨lam, hpt, fun a' => ?_⟩
  set y := d • a' with hy
  have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, ← hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
  let T₀ : Over (Sp S₂.R) := Over.mk x₀
  let V₁ : Over.mk (x₀ ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap om) (by simp)
  let z₁ : Over.mk (x₀ ≫ spMap om) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
  have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
    have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
      have h3 := congrArg (preHom V₂) hyL
      rwa [map_pow, map_one] at h3
    show (pushHom hpb T₀) _ ^ _ = 1
    rw [← map_pow, h0, map_one]
  obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap om) z₁ hz₁
  refine ⟨a, ?_⟩
  have hpush : pushHom hpb T₀ (V₂ ≫ ρ₂.pt (lam a)) = V₁ ≫ ρ₁.pt a := by
    apply Over.OverMorphism.ext
    show (V₂ ≫ ρ₂.pt (lam a)).left ≫ φ = (V₁ ≫ ρ₁.pt a).left
    simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
    rw [hpt]
  have h1 : V₂ ≫ ρ₂.pt (lam a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
  have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
    have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
    rwa [map_pow, map_one] at h3
  exact (ρ₂.pt_bij K x₀ _ h2).unique h1 rfl

end GlobalTheory.Poinc.PullLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelsOfGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaRealisation_labels_of_grpPullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left) (d : ℕ), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → S₂.r * S₂.N = S₁.r * S₁.N * d → ∃ lam : S₁.Gam →+ S₂.Gam, (∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left) ∧ ∀ a', ∃ a, lam a = d • a' := by
  first | exact @GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback | exact GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback | (intros; apply GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFiniteGaloisStableThetaRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFiniteGaloisStableThetaRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.NormalClosureRing

theorem exists_integralClosure_finite : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (κ : o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ h.Finite ∧ IsIntegrallyClosed R ∧ ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ x ∈ R, σ x ∈ R := by
  intro o₁ Ω₁ _ _ _ _ R₁ hR₁ hfrac o₂ Ω₂ _ _ _ _ _ _ κ hκ hcomp
  haveI : IsDedekindDomain o₁ := ArithBase.ded (Ω := Ω₁)
  haveI : CharZero Ω₁ := ArithBase.char (o := o₁)
  have hinj₁ : Function.Injective (algebraMap o₁ Ω₁) := ArithBase.inj
  haveI : CharZero o₁ := (algebraMap o₁ Ω₁).charZero
  haveI : Algebra.FiniteType o₁ R₁ := (Subalgebra.fg_iff_finiteType R₁).mp hR₁
  haveI : FaithfulSMul o₁ R₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab => hinj₁ (congrArg Subtype.val hab)
  haveI : FaithfulSMul R₁ Ω₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing R₁ Ω₁ := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  haveI : IsScalarTower R₁ Ω₁ Ω₂ := inferInstance
  let C := integralClosure R₁ Ω₂
  have hmem : ∀ x : o₂, algebraMap o₂ Ω₂ x ∈ C := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hκ.to_isIntegral x
    refine ⟨p.map (algebraMap o₁ R₁), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have := congrArg (algebraMap o₂ Ω₂) hpx
    rw [Polynomial.hom_eval₂, map_zero, hcomp] at this
    exact this
  let R : Subalgebra o₂ Ω₂ :=
    { toSubsemiring := C.toSubsemiring
      algebraMap_mem' := hmem }
  let h : R₁ →+* R := (algebraMap R₁ Ω₂).codRestrict R fun a => (isIntegral_algebraMap : IsIntegral R₁ (algebraMap R₁ Ω₂ a))
  have hh : ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a => rfl
  haveI : Module.Finite R₁ C := GlobalTheory.finite_integralClosure_dedekind o₁ R₁ Ω₁ Ω₂
  classical
  have hfg : R.FG := by
    obtain ⟨s, hs⟩ := hR₁
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R₁ C).FG)
    refine ⟨s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val, le_antisymm ?_ ?_⟩
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe] at hy
      rcases hy with ⟨a, ha, rfl⟩ | ⟨z, -, rfl⟩
      · have ha' : a ∈ R₁ := hs ▸ Algebra.subset_adjoin ha
        exact (h ⟨a, ha'⟩).2
      · exact z.2
    · set A := Algebra.adjoin o₂ ((s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val : Finset Ω₂) : Set Ω₂)
      have hR₁A : ∀ z ∈ Algebra.adjoin o₁ (s : Set Ω₁), algebraMap Ω₁ Ω₂ z ∈ A := by
        intro z hz
        induction hz using Algebra.adjoin_induction with
        | mem z hz => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)))
        | algebraMap r =>
          have := congrArg (fun f => f r) hcomp
          simp only [RingHom.comp_apply] at this
          rw [← this]
          exact A.algebraMap_mem _
        | add x y _ _ hx hy => rw [map_add (f := _)]; exact A.add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact A.mul_mem hx hy
      suffices key : ∀ y : C, y ∈ Submodule.span R₁ (t : Set C) → (y : Ω₂) ∈ A from
        fun x hx => key ⟨x, hx⟩ (ht ▸ Submodule.mem_top)
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)))
      | zero => exact A.zero_mem
      | add y z _ _ hy hz => exact A.add_mem hy hz
      | smul r y _ hy =>
        convert A.mul_mem (hR₁A r.1 (hs ▸ r.2)) hy using 1
        first | rfl | exact Algebra.smul_def r (y : Ω₂) | simp [Algebra.smul_def]
  letI : Algebra R₁ R := h.toAlgebra
  haveI : IsScalarTower R₁ R Ω₂ := .of_algebraMap_eq fun a => rfl
  haveI : IsIntegralClosure R R₁ Ω₂ :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩ }
  have hfin : h.Finite := GlobalTheory.finite_of_isIntegralClosure_dedekind o₁ R₁ Ω₁ Ω₂ R
  have hic : IsIntegrallyClosed R := integralClosure.isIntegrallyClosedOfFiniteExtension (R := R₁) Ω₁ (L := Ω₂)
  refine ⟨R, h, hfg, ?_, hh, hfin, hic, ?_⟩
  · intro x
    have hxi : IsIntegral Ω₁ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors R₁) x hxi
    have hm0 : algebraMap R₁ Ω₂ (m : R₁) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R₁ Ω₁ Ω₂]
      exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors m.2)
    refine ⟨_, hm, algebraMap R₁ Ω₂ (m : R₁), isIntegral_algebraMap, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, mul_div_cancel_left₀ _ hm0]
  · intro σ x hx
    exact (show IsIntegral R₁ x from hx).map (σ.toAlgHom.restrictScalars R₁)

end GlobalTheory.Poinc.NormalClosureRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFiniteGaloisStableThetaRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralClosure_finite_galoisStable_thetaRing : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (κ : o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ h.Finite ∧ IsIntegrallyClosed R ∧ ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ x ∈ R, σ x ∈ R := by
  first | exact @GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite | exact GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite | (intros; apply GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquation
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle

theorem dvd_pow_of_vanishing {Y : Scheme.{0}} (O V : Y.Opens) (t : Γ(Y, V))
    (ht : ∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W))
    (hf : ∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z))
    (z : Y) (hz : z ∈ W) : ∃ n : ℕ, ger z (hW hz) t ∣ ger z hz f ^ n := by
  obtain ⟨A, hA, hzA, e⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hz
  have hA' : IsAffineOpen A := hA
  let f' : Γ(Y, A) := Y.presheaf.map (homOfLE e).op f
  let t' : Γ(Y, A) := Y.presheaf.map (homOfLE (e.trans hW)).op t
  have hle : Y.basicOpen f' ≤ Y.basicOpen t' := by
    intro x hx
    have hxA : x ∈ A := Y.basicOpen_le _ hx
    rw [Y.mem_basicOpen _ x hxA] at hx ⊢
    rw [Y.presheaf.germ_res_apply] at hx ⊢
    refine (ht x _).2 ?_
    by_contra hO
    exact hf x (e hxA) hO hx
  have h2 : PrimeSpectrum.basicOpen f' ≤ PrimeSpectrum.basicOpen t' := by
    rw [← hA'.fromSpec_preimage_basicOpen, ← hA'.fromSpec_preimage_basicOpen]
    exact fun x hx => hle hx
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 h2
  have h3 := map_dvd (Y.presheaf.germ A z hzA).hom (Ideal.mem_span_singleton.1 hn)
  rw [map_pow] at h3
  refine ⟨n, ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (e.trans hW)) z hzA t, ← Y.presheaf.germ_res_apply (homOfLE e) z hzA f]
  exact h3

theorem exists_section {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (hD : D.Eff)
    (hr : ∀ (y : X) (g : X.functionFieldˣ), D.IsEqn y g → ∀ (f : X.functionField) (n : ℕ), RegAt y f →
      RegAt y (f ^ n / g) → RegAt y (f / g)) (y : X) :
    ∃ (V : X.Opens) (_ : y ∈ V) (t : Γ(X, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∉ D.supp) ∧
      ∀ z (hz : z ∈ V) (b : X.presheaf.stalk z) (n : ℕ), ger z hz t ∣ b ^ n → ger z hz t ∣ b := by
  obtain ⟨U, hyU, g, hg⟩ := D.exists_isEqn_nhds y
  obtain ⟨a, ha⟩ := (hg y hyU).regularAt_iff.1 (hD y)
  rw [one_mul] at ha
  obtain ⟨W, hyW, s, rfl⟩ := X.presheaf.germ_exist a
  have inj := fun z : X => IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have key : ∀ z (hz : z ∈ W ⊓ U), algebraMap _ X.functionField
      (ger z hz (X.presheaf.map (homOfLE inf_le_left).op s)) = g := fun z hz => by
    refine Eq.trans ?_ ((algebraMap_germ hz.1 s).trans ((algebraMap_germ hyW s).symm.trans ha))
    exact congrArg _ (X.presheaf.germ_res_apply (homOfLE inf_le_left) z hz s)
  refine ⟨W ⊓ U, ⟨hyW, hyU⟩, X.presheaf.map (homOfLE inf_le_left).op s, fun z hz => ?_, fun z hz b n hb => ?_⟩
  · rw [(hg z hz.2).mem_supp_iff, not_not]
    refine ⟨fun h => ⟨_, h, key z hz⟩, fun ⟨u, hu, e⟩ => ?_⟩
    rwa [inj z (e.trans (key z hz).symm)] at hu
  · obtain ⟨c, hc⟩ := hb
    obtain ⟨d, hd⟩ := hr z g (hg z hz.2) (algebraMap _ X.functionField b) n ⟨b, rfl⟩ ⟨c, by
      rw [eq_div_iff g.ne_zero, ← map_pow, hc, map_mul, key z hz, mul_comm]⟩
    refine ⟨d, inj z ?_⟩
    rw [map_mul, key z hz, hd, mul_div_cancel₀ _ g.ne_zero]

theorem exists_reduced_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  intro _ E _ _ _ H Dw l Xo c T Z hF _ y _
  have hsm := GlobalTheory.VarFlag.smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, -, hl⟩ :=
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  obtain ⟨h, hiso, hh, -, -⟩ := GlobalTheory.CompProport.exists_iso T Z B j hB hcov C f hπ hl
  have hmem : ∀ z : Y₀ T.X Z, h z ∉ CartierDiv.supp C.bd ↔ z ∈ U₀ T.X Z := fun z => by
    have e : GlobalTheory.Toroidal.genι T.Y (C.π (h z)) = T.X.π (inc₀ T.X Z z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    refine (not_congr (C.bd_supp (h z))).trans (not_not.trans ?_)
    change C.π (h z) ∈ Set.range T.Y.jQ ↔ T.X.π (inc₀ T.X Z z) ∈ Set.range T.Y.j
    refine exists_congr fun x => ?_
    rw [← e, Model.j, Scheme.Hom.comp_apply]
    exact (GlobalTheory.Toroidal.genι T.Y).isOpenEmbedding.injective.eq_iff.symm
  obtain ⟨V, hyV, t, ht, hrad⟩ := exists_section C.bd C.bd_eff C.bd_red (h y)
  have hg : ∀ z (hz : z ∈ h ⁻¹ᵁ V), ger z hz (h.app V t) = (h.stalkMap z).hom (ger (h z) hz t) :=
    fun z hz => (Scheme.Hom.germ_stalkMap_apply h V z hz t).symm
  have hu : ∀ z (hz : z ∈ h ⁻¹ᵁ V), IsUnit (ger z hz (h.app V t)) ↔ z ∈ U₀ T.X Z := fun z hz => by
    rw [hg, isUnit_map_iff]
    exact (ht (h z) hz).trans (hmem z)
  refine ⟨h ⁻¹ᵁ V, hyV, h.app V t, hu, fun W hW s hs z hz => ?_⟩
  obtain ⟨n, c', hc⟩ := dvd_pow_of_vanishing _ _ _ hu W hW s hs z hz
  have hb := GlobalTheory.BoundaryDivisor.stalkMap_bijective h z
  obtain ⟨b, hb'⟩ := hb.2 (ger z hz s)
  obtain ⟨c'', rfl⟩ := hb.2 c'
  rw [hg, ← hb', ← map_pow, ← map_mul] at hc
  rw [hg, ← hb']
  exact map_dvd _ (hrad _ _ b n ⟨c'', hb.1 hc⟩)

end GlobalTheory.BdEquation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_boundary_local_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  first | exact @GlobalTheory.BdEquation.exists_reduced_equation | exact GlobalTheory.BdEquation.exists_reduced_equation | (intros; apply GlobalTheory.BdEquation.exists_reduced_equation <;> assumption)
end
end
