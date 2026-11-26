module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
public import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
section -- merged from Development.AutomorphicArithmetic.CMTraceForms.ProdPrimeFactorsPowCeilPadicValNatMulEqPow
theorem UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow :
    ∀ (Q T a b : ℕ), Q ≠ 0 → ∏ p ∈ Q.primeFactors.filter Nat.Prime,
      p ^ (T * ⌈(padicValNat p Q : ℝ) * (a : ℝ)⌉.toNat + ⌈(padicValNat p Q : ℝ) * (b : ℝ)⌉.toNat) = Q ^ (T * a + b) := by
  intro Q T a b hQ
  have hc : ∀ m n : ℕ, ⌈(m : ℝ) * (n : ℝ)⌉.toNat = m * n := by
    intro m n
    rw [← Nat.cast_mul, Int.ceil_natCast, Int.toNat_natCast]
  have hf : Q.primeFactors.filter Nat.Prime = Q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQ' : ∏ p ∈ Q.primeFactors, p ^ (Q.factorization p) = Q := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hQ
  rw [hf]
  conv_rhs => rw [← hQ', ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hc, hc, ← pow_mul, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp),
    Nat.padicValNat_def]
  congr 1
  ring
end

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScalarOfRun

theorem ceil_toNat (x : ℝ) : ⌈x⌉.toNat = ⌈x⌉₊ := rfl

theorem barE_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

theorem cP_of_mem_small (D : D7) (Tn : ℕ+) (N p : ℕ) (hp : p ∈ D.host.small) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP N p = ⌈(padicValNat p D.host.QS : ℝ) * (N : ℝ)⌉.toNat := by
  unfold DepPage.cP
  rw [if_pos (show (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p from Or.inl hp)]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉.toNat = _
  rw [GlobalTheory.RunDepth.vdOf, if_pos hp]

theorem cP_of_isRam_of_notMem_small (D : D7) (Tn : ℕ+) {j : ℕ} (w : WeightFamilies.Wt D j) (p : ℕ) (hp : p ∉ D.host.small)
    (hr : (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP (WeightAlgebra.DF w) p = Formalism.MainNotions.DIV.Cons.cHalf w := by
  unfold DepPage.cP
  rw [if_pos hr, ceil_toNat]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉₊ = _
  rw [GlobalTheory.RunDepth.vdOf, if_neg hp, Formalism.MainNotions.DIV.Cons.cHalf]
  congr 1; ring

theorem depth_page_first_zeta_factor_eq_prime_power (D : D7) (Tn : ℕ+) {j : ℕ} (wL wF : WeightFamilies.Wt D j) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) =
      pPow D (Tn * c2 D wL + c2 D wF) (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) := by
  have hq := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.q D.host.q_notMem_small (Or.inr (Or.inl rfl))
  have hd := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.d D.host.d_notMem_small (Or.inr (Or.inr rfl))
  have hS := UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow D.host.QS Tn (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) D.host.QS_pos.ne'
  unfold pPow c2
  rw [← hS]
  conv_rhs => enter [1, 2]; rw [← hq wL, ← hq wF]
  conv_rhs => enter [2]; rw [← hd wL, ← hd wF]
  unfold DepPage.Z1
  congr 2
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p ∈ D.host.small := (Finset.mem_filter.1 hp).1
  rw [cP_of_mem_small D Tn _ p hp', cP_of_mem_small D Tn _ p hp']
  rfl

theorem sigAt_eq_sigRec : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ), InR D j → HalfEX T.toCore EX → ∀ (K : Type) [Field K] [NumberField K] [Algebra (𝓞 D.host.E) K] (φ : T.Q.c.F →+* K), (∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) K x = φ ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F)) → sigAt (Dw := T.Q.Dw j) (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j = φ ((sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D L Pm Tp hK T h hinj EX j hj hE K _ _ _ φ hφ
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  let ψ : 𝓞 T.Q.c.F →+* K := φ.comp (algebraMap (𝓞 T.Q.c.F) T.Q.c.F)
  have hψ : ∀ x, algebraMap (𝓞 D.host.E) K x = ψ (iE D hinj (recB h.toLawsCore) x) := hφ
  let Tn : ℕ+ := ⟨Tp.TO, GlobalTheory.RunDepth.TO_pos Tp⟩
  have hnn : nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j =
      ψ (nnW (recB h.toLawsCore) hinj EX (kaR Tp hK j)) := by
    letI : StarRing (𝓞 D.host.E) := starRingOfComm
    refine (nnKAt_depDataOf T.toCore EX _ _ _ _ _ _ _ hM hE j).trans ?_
    refine Eq.trans ?_ (map_prod ψ _ _).symm
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [barE_eq_piBarO, hψ, hψ]
    exact ((map_mul ψ _ _).trans (congrArg₂ (· * ·) (map_pow ψ _ _) (map_pow ψ _ _))).symm
  have hL := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (lR Tp hK j)
  have hF := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (fR Tp hK j)
  have hn : (fR Tp hK j).n = 8 * D.R.f * D.R.r + 4 := Tp.nP_eq
  show nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j *
      (((D.host.g 0 * D.host.g 1 : ℕ) : K) ^ (D.R.f * D.R.r * (8 * D.R.f * D.R.r + 4)) *
        (((depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (lR Tp hK j)))
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (fR Tp hK j))) : ℕ) : K)) =
      ψ (sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
  rw [hnn, hL, hF, depth_page_first_zeta_factor_eq_prime_power, ← hn, ← Nat.cast_pow, ← Nat.cast_mul, ← map_natCast ψ, ← map_mul]
  rfl

end GlobalTheory.ScalarOfRun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private theorem exists_quotient_side_of_isType_lemma (k r : ℕ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (hk : 1 ≤ k)
    (z : Fin (2 * r + k + 1) → ℂ) (π : _root_.Formalism.FourierDecayAlt.B.Mat k r → W →L[ℂ] W) (u : ℕ → ℝ)
    (μW μN μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z)
    (hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW) (hN : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN)
    (hG : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.BranchingSupport.GG k r) μG) (hπ : _root_.Formalism.FourierDecayAlt.Q.IsType k r z π u) :
    ∃ ν, _root_.BranchingSupport.SideG k r z π u μW μN μG ν := by
  have hW' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW
  have hN' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1).2 hN
  have hG' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.BranchingSupport.GG k r) μG :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1).2 hG
  obtain ⟨ν, hν⟩ :=
    _root_.GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW μN μG hz hT hW' hN' hG'
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.besType_hcParam k r W z π u hz hT hπ
  exact ⟨ν, hz, hT, ⟨u₀, hu₀⟩, hπ.2.2.2.2.2, hW', hN', hG', hν⟩

theorem _root_.GlobalTheory.exists_sideG_both_of_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type)
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z D.π u →
    _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z' D.π' u' → ∃ νq νq',
      _root_.BranchingSupport.SideG k r D.z D.π u D.μW D.μN D.μG νq ∧
        _root_.BranchingSupport.SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D u u' hp hq
  obtain ⟨z, z', π, π', μG, μW, μN, μW', _, _, hk, hz, hz', hT, hT', _, _, _, _, _, _, hG, hW,
    hN, hW', _, _, _, _⟩ := D
  obtain ⟨ν, hν⟩ := exists_quotient_side_of_isType_lemma k r Wp hk z π u μW μN μG hz hT hW hN hG hp
  obtain ⟨ν', hν'⟩ :=
    exists_quotient_side_of_isType_lemma k r Wq hk z' π' u' μW' μN μG hz' hT' hW' hN hG hq
  exact ⟨ν, ν', hν, hν'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDatum_both_sides_are_sides : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' → ∃ νq νq', SideG k r D.z D.π u D.μW D.μN D.μG νq ∧ SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  first | exact @GlobalTheory.exists_sideG_both_of_isType | exact GlobalTheory.exists_sideG_both_of_isType | (intros; apply GlobalTheory.exists_sideG_both_of_isType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.WeightOnDatum

theorem weight_on_datum : ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ DomW (T.Q.Dw j) (wtA w) ∧ (w.LastPos → Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) ∧ 1 ≤ WeightAlgebra.DF w) ∧ (∀ τ, (T.Q.Dw j).mult τ ≤ D.R.r) ∧ Fintype.card (Lt1 (T.Q.Dw j)) ≤ 2 * D.R.f * D.R.r ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ Module.finrank ℚ D.host.E = 2 * D.R.f := by
  intro D T hP j hj w
  obtain ⟨hDF, -, hPsi, hN, hwt⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hP j hj w
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hp, hq, -⟩ := hP.2.2.2 j hj
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hj2 := hj.2
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]; omega
  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hp0 : 0 < (D.R.sigW j).1 := by
    simp only [Ranks.sigW]; omega
  have hlast : w.LastPos → ∀ t, 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := fun hw t =>
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine ⟨hDF, ?_, fun hw => ⟨?_, ?_⟩, fun τ => ?_, ?_, hf, by omega, hfr⟩
  · intro τ i i' h
    exact (dom_wtA w).1 τ h
  · intro τ hτ _
    obtain ⟨t, rfl⟩ := (hPsi τ).1 hτ
    have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
      unfold Datum.mult
      have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
      rw [if_pos hτ', hp]
    rw [hmult, (hwt t _).1]
    unfold ext0
    rw [dite_eq_left (by omega)]
    exact hlast hw t
  · have ht : Nonempty D.what₂.Tau := by
      by_cases h : InPsi T.Q.H D.host.φ₀
      · obtain ⟨t, -⟩ := (hPsi _).1 h
        exact ⟨t⟩
      · obtain ⟨t, -⟩ := (hN _).1 h
        exact ⟨t⟩
    obtain ⟨t⟩ := ht
    unfold WeightAlgebra.DF WeightAlgebra.degP
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, w.aP τ i) + ∑ i, w.aM τ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact le_trans (hlast hw t) (Finset.single_le_sum (f := fun i => w.aP t i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  · rw [← hr, Datum.mult]
    split_ifs <;> omega
  · refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]

end GlobalTheory.WeightOnDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EmbEqOfInPsi
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsInPsiIEEqEmbK
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem exists_inPsi_iE_eq_embK : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL), ∃ τ : D.host.E →+* ℂ, InPsi T.Q.H τ ∧ ∀ x : 𝓞 D.host.E, ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F) = embK T.Q.c τ x := by
  intro D T h hinj
  obtain ⟨hH, -, hF, -⟩ := h.pins
  refine ⟨D.host.φ₀, ?_, fun x => ?_⟩
  · unfold InPsi
    rw [hH.2.1, hH.2.2.1]
  · apply Subtype.ext
    rw [← hF]
    have h1 : T.Q.eO (iE D hinj (recB h.toLawsCore) x) = oEOsFun D x := T.Q.eO.apply_symm_apply _
    rw [h1, oEOsFun_spec]
    exact DFunLike.congr_fun D.embE_φ₀ (x : D.host.E)

end GlobalTheory.PtTie
end
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

noncomputable section

namespace GlobalTheory.PtTie

theorem emb_eq_of_inPsi {D : D7} {Q : Par D} (hp : Q.PinHost) {τ σ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ)
    (hσ : InPsi Q.H σ) {x : D.host.E} (hx : x ∈ D.host.K) : τ x = σ x := by
  have hs : τ D.host.sqrtMinusD = σ D.host.sqrtMinusD := by
    rw [← hp.2.1]; exact hτ.trans hσ.symm
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hs
  | algebraMap q => simp
  | add a b ha hb iha ihb => rw [map_add (f := _), map_add (f := _), iha ha, ihb hb]
  | inv a ha iha => rw [map_inv₀, map_inv₀, iha ha]
  | mul a b ha hb iha ihb => rw [map_mul, map_mul, iha ha, ihb hb]

theorem prod_pow_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {M : Type} [CommMonoid M] (F : (D.host.E →+* ℂ) → M) :
    ∏ τ : D.host.E →+* ℂ, F τ ^ (∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ))) =
      ∏ t : D.what₂.Tau, (F (DV.tauEmb D t) ^ (∑ i, w.aP t i) *
        F (ComplexEmbedding.conjugate (DV.tauEmb D t)) ^ (∑ i, w.aM t i)) := by
  classical
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [GlobalTheory.WeightExponents.wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.prod_congr rfl fun τ _ => by rw [hsw τ, ← Finset.prod_pow_eq_pow_sum], Finset.prod_comm]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [pow_add, pow_ite, pow_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 :=
    GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

theorem emb_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.host.E →+* ℂ) :
    τ ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = starRingEnd ℂ (τ ((EX.piG i : 𝓞 D.host.E) : D.host.E)) := by
  have h1 : ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = ((barE D (EX.piG i) : 𝓞 D.host.E) : D.host.E) := by
    rw [barE_eq_conj]; rfl
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj D.host.E τ _

theorem nrm_eq_prod {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    {τ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ) :
    nrm (Q.Dw j) Q.c (wtA w) (EX.piG 0 * EX.piG 1) =
      ∏ i : Fin 2, embK Q.c τ (EX.piG i) ^ Dplus w * embK Q.c τ (piBarO EX i) ^ Dminus w := by
  have h1 : ∀ t i, embK Q.c (DV.tauEmb D t) (EX.piG i) = embK Q.c τ (EX.piG i) := fun t i =>
    Subtype.ext (emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i))
  have h2 : ∀ t i, embK Q.c (ComplexEmbedding.conjugate (DV.tauEmb D t)) (EX.piG i) = embK Q.c τ (piBarO EX i) :=
    fun t i => Subtype.ext (by
      rw [embK_coe, embK_coe, emb_piBarO, ← emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i)]
      simp)
  unfold nrm Dplus Dminus
  rw [prod_pow_wtA hQ hj w fun σ => embK Q.c σ (EX.piG 0 * EX.piG 1)]
  simp only [map_mul, h1, h2]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Fin.prod_univ_two,
    mul_pow, mul_pow]
  ring

theorem map_nnW {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) :
    ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) = ∏ i : Fin 2, ((iE D hinj B (EX.piG i) : 𝓞 B.KO) : B.KO) ^ Dplus w *
      ((iE D hinj B (piBarO EX i) : 𝓞 B.KO) : B.KO) ^ Dminus w := by
  unfold nnW
  simp only [RingOfIntegers.coe_eq_algebraMap, map_prod, map_mul, map_pow]

theorem nrm_eq_nnW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j), nrm (T.Q.Dw j) T.Q.c (wtA w) (EX.piG 0 * EX.piG 1) = ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D T h j hj hinj EX w
  obtain ⟨τ, hτ, hE⟩ := exists_inPsi_iE_eq_embK D T h hinj
  rw [nrm_eq_prod h.pins hj EX w hτ]
  refine Eq.trans ?_ (map_nnW (recB h.toLawsCore) hinj EX w).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hE, ← hE]

end GlobalTheory.PtTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

private lemma opApply_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (c : ℂ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply Θ (c • F) g = c • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  simp only [_root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, Pi.smul_apply, map_smul]
  rw [List.smul_sum, List.map_map]
  rfl

private lemma vecV_smul_jet_harmonics {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν : Fin (2 * r + k + 1) → ℂ) (m : _root_.Formalism.FourierDecayAlt.B.Mat k r) (c : ℂ)
    (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m (fun g => c • G g) q = c • _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m G q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · apply _root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae
    refine MeasureTheory.ae_of_all _ fun x => ?_
    unfold _root_.Formalism.FourierDecayAlt.D.orbIntegrand _root_.Formalism.FourierDecayAlt.B.rho
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    exact smul_comm _ _ _
  · simp
  · simp

private lemma topLift_vecV_add_smul_lemma {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : _root_.Formalism.FourierDecayAlt.M.Par} (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    {Cb : ℝ} (a : ℂ) {H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List _root_.Formalism.FourierDecayAlt.C.Letter}
    (hdom : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hcut : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (h₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂) (i : _root_.Formalism.FourierDecayAlt.Wd.Ix (Fin w.length))
    (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    p.V (p.Θ.Θ w i (H₁ + a • H₂)) q = p.V (p.Θ.Θ w i H₁) q + a • p.V (p.Θ.Θ w i H₂) q := by
  obtain ⟨nf, fib, o, κ, D, -, hD, -, -, hΘ⟩ := hdom w hcut i
  have hlen : ∀ T ∈ D, T.word.length ≤ o := fun T hT => by
    obtain ⟨_, _, _, _, es, -, -, hl, -⟩ := hD.2.2 T hT
    omega
  have hpos : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GPos p.T.base, g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, by simp⟩
  have hc₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₁ hD.1
  have hc₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₂ hD.1
  have e₁ : p.V (p.Θ.Θ w i H₁) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₁ g (hpos g hg)
  have e₂ : p.V (p.Θ.Θ w i H₂) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₂ g (hpos g hg)
  have e₃ : p.V (p.Θ.Θ w i (H₁ + a • H₂)) q =
      p.V (fun g => _root_.Formalism.FourierDecayAlt.B.opApply D H₁ g - (fun g => (-a) • _root_.Formalism.FourierDecayAlt.B.opApply D H₂ g) g) q := by
    refine _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
    have hsum : H₁ + a • H₂ = H₁ - (-a) • H₂ := by rw [neg_smul, sub_neg_eq_add]
    rw [hΘ _ g (hpos g hg), hsum,
      _root_.Formalism.FourierDecayAlt.P.PBE.opApply_subGV D hlen (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₁.1 o) (_root_.Formalism.FourierDecayAlt.P.B4.ckOn_smul (-a) (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₂.1 o)) g hg.1, opApply_smul]
  have e₄ := _root_.Formalism.FourierDecayAlt.P.PBN.vecV_sub p.T.base p.ν' p.m₀ q hc₁ (_root_.Formalism.FourierDecayAlt.P.PBN.cpt_smul p.T.base (-a) hc₂)
  have e₅ := vecV_smul_jet_harmonics p.T.base p.ν' p.m₀ (-a) (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q
  rw [e₁, e₂, e₃]
  change _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q = _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q + a • _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q
  rw [e₄, e₅, neg_smul, sub_neg_eq_add]

private lemma hsVec_add_jet_harmonics {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (A B : Wq →L[ℂ] Wp) : _root_.Formalism.FourierDecayAlt.B.hsVec (A + B) = _root_.Formalism.FourierDecayAlt.B.hsVec A + _root_.Formalism.FourierDecayAlt.B.hsVec B := by
  unfold _root_.Formalism.FourierDecayAlt.B.hsVec
  rfl

theorem _root_.GlobalTheory.TopVec.tv_add_smul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (c : Fin (P.r + 1) → ℂ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂ → _root_.GlobalTheory.TopVec.tv p (H₁ + a • H₂) w c = _root_.GlobalTheory.TopVec.tv p H₁ w c + a • _root_.GlobalTheory.TopVec.tv p H₂ w c := by
  intro Wp Wq _ _ _ _ _ _ P p Cb a H₁ H₂ w c hdom hcut h₁ h₂
  unfold _root_.GlobalTheory.TopVec.tv
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  funext x
  rw [topLift_vecV_add_smul_lemma p a hdom hcut h₁ h₂, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, hsVec_add_jet_harmonics, _root_.Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, smul_add, Pi.add_apply, Pi.smul_apply,
    smul_comm a]

end GlobalTheory.TopVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficientsStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topVector_add_smul_compactCoefficients : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → KB.CptCoef p.T.base H₁ → KB.CptCoef p.T.base H₂ → tv p (H₁ + a • H₂) w c = tv p H₁ w c + a • tv p H₂ w c := by
  first | exact @GlobalTheory.TopVec.tv_add_smul | exact GlobalTheory.TopVec.tv_add_smul | (intros; apply GlobalTheory.TopVec.tv_add_smul <;> assumption)
end
end
