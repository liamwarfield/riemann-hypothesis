module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLetters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlInductiveRank
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentre
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ChiGrid

theorem botBig_add_botSmall_le_two_e_add_two_cen (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤
      2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have he := (GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) (cen D C τ)).2.2 j
  have hne : (num D C τ).e (j + 1) = (GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) (cen D C τ)).e (j.1 + 1) := rfl
  have hj := j.2
  have hi := i.2
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl
  have h1 := P.gap_be j
  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b j = (G.b (j.1 + 1) : ℚ) := hb j
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rcases Nat.eq_zero_or_pos j.1 with h0 | hj0
    · exact le_of_eq (congrArg P.b (Fin.ext (by simp [h0])))
    · have := G.b_mono 1 (j.1 + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le
  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1
  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc
  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j.1 * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i.1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hbot : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j ≤
      rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 := by
    unfold GlobalTheory.FunObj.SqNum.botBig GlobalTheory.FunObj.SqNum.botSmall; omega
  have hR : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j + 1 ≤ gap D C := by omega
  have hR' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by
    exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) := by positivity
  have key : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) <
      2 * ((num D C τ).e (j + 1) : ℚ) + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
    rw [hne, ← he]
    nlinarith
  have key' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) <
      2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) := by
    have : (((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) : ℚ) <
        ((2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) : ℤ) : ℚ) := by
      push_cast; push_cast at key; linarith
    exact_mod_cast this
  exact key'.le

end GlobalTheory.ChiGrid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentreStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre : ∀ (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau), ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤ 2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | exact GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvUnramifiedOverInertPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvUnramifiedOverInertPrime
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

theorem nuH_inv_unrAt_of_inertQ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → (nuH G μ₀ i j)⁻¹.UnrAt P := by
  intro D T L sc μ₀ hL G i j P hq
  obtain ⟨q, hqp, hqi, hqP⟩ := hq

  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hk
    have e := prime_unique (K := D.host.E) hqp (D.host.g_prime k) hqP hk'
    exact GlobalTheory.Mem.Col2.SplitChar.not_inertQ_g k (e ▸ hqi)

  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := by
    refine G.ch.unr (D.R.m - i) (by omega) (by omega) P fun hv => ?_
    obtain ⟨e, he⟩ := G.pl.w_split _ hv
    have hov := G.pl.w_over _ hv
    set w := G.pl.w (P.under (𝓞 D.host.F))
    have h1 : ((q : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
      simpa using hqP
    rw [← hov] at h1
    have hqw : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ w.asIdeal := h1
      simpa using h2
    have hfix := hqi _ w.isPrime w.ne_bot hqw
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact GlobalTheory.DualPairCheck.split_ne e ⟨e1, e2, v, ε, hε, e3⟩
      (GlobalTheory.EtaProduct.cA_of_fixed ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩ hfix)
  have e : nuH G μ₀ i j = L.C.mu0 j * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv]
  rw [e]
  exact (hmu.mul hchi.inv).inv

end GlobalTheory.FunObj.SqNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvUnramifiedOverInertPrimeStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNu_inv_unramified_over_inert_prime : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → (nuH G μ₀ i j)⁻¹.UnrAt P := by
  first | exact @GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ | exact GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ | (intros; apply GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ <;> assumption)
end
end

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BottomNu

theorem exists_heckeU_nu_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) ∧ ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  intro D T L sc μ₀ hL G i j
  have hu : (nuH G μ₀ i j)⁻¹.IsUnitary := by
    have h := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G μ₀ i j hL)
    intro x
    have e : (((nuH G μ₀ i j)⁻¹).1 x : ℂˣ) = ((nuH G μ₀ i j).1 x)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have htriv : (nuH G μ₀ i j)⁻¹.TrivOn D.host.F := by
    have h1 := (L.C.isMu0 j).triv
    have h2 := G.ch.triv (D.R.m - i) hm.1 hm.2
    have h3 : (L.xiH μ₀).TrivOn D.host.F := hL.xi_triv μ₀
    exact (((h1.mul h3).mul h2.inv)).inv
  have hp : ∀ τ, Even (2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i)) -
      ((botBig D i j + botSmall D i j : ℕ) : ℤ)) := by
    intro τ
    obtain ⟨h1, h2, -⟩ := ranks_exact D i j
    obtain ⟨u, hu⟩ := D.R.t_odd
    obtain ⟨v, hv⟩ := odd_sLen D
    have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
    obtain ⟨w, hw⟩ : ∃ w : ℕ, botBig D i j + botSmall D i j = 2 * w := ⟨(botBig D i j + botSmall D i j) / 2, by omega⟩
    refine ⟨(GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i) - w, ?_⟩
    rw [hw]; push_cast; ring
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units D.host.E (nuH G μ₀ i j)⁻¹
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar _ (nuH G μ₀ i j)⁻¹ _ hu (GlobalTheory.T.squareNu_inv_hasInfinityType_cmType hL G i j) hp hc
    (GlobalTheory.T.heckeCharacter_trivial_subfield_kills_idele_norms D _ htriv (GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units D.host.E _)) (GlobalTheory.T.heckeCharacter_unramified_inert_kills_units D _ fun P hP => GlobalTheory.T.squareNu_inv_unramified_over_inert_prime hL G i j P hP), fun x => rfl, fun τ => GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre D sc.cGap i j τ⟩

end GlobalTheory.BottomNu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def glTens (k : ℕ) : GL (Fin k) (AF F ⊗[F] E) ≃ₜ* GlobalTheory.CuspRep.GA E k where
  toMulEquiv := Units.mapEquiv (GlobalTheory.TateConv.tens F E).toRingEquiv.mapMatrix.toMulEquiv
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (GlobalTheory.TateConv.continuous_tens F E))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (GlobalTheory.TateConv.continuous_tens_symm F E))

theorem glTens_bc (k : ℕ) (γ : GL (Fin k) E) :
    glTens F E k (bc (inclR (F := F) (AF F)) γ) = GlobalTheory.CuspRep.ratGL E k γ := by
  ext i j
  change GlobalTheory.TateConv.tens F E ((1 : AF F) ⊗ₜ[F] (γ i j)) = algebraMap E _ (γ i j)
  rw [GlobalTheory.TateConv.tens, adeleTensorAlgEquivLeft_tmul, map_one, mul_one]

variable [_root_.NumberField.IsTotallyComplex E]

def cR (k : ℕ) (t : ℝ) : GL (Fin k) (AF F ⊗[F] E) := (glTens F E k).symm (GlobalTheory.UnitaryBC.splitCentre E k t)

def latR (k : ℕ) : Subgroup (GL (Fin k) (AF F ⊗[F] E)) :=
  (bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range ⊔ Subgroup.zpowers (cR F E k 1)

variable {F E}

theorem glTens_cR (k : ℕ) (t : ℝ) : glTens F E k (cR F E k t) = GlobalTheory.UnitaryBC.splitCentre E k t :=
  (glTens F E k).apply_symm_apply _

theorem continuous_cR (k : ℕ) : Continuous (cR F E k) :=
  (glTens F E k).symm.continuous.comp GlobalTheory.OneRep.SplitTwist.continuous_splitCentre

theorem cR_add (k : ℕ) (x y : ℝ) : cR F E k (x + y) = cR F E k x * cR F E k y := by
  rw [cR, cR, cR, splitCentre_add, map_mul]

theorem cR_comm (k : ℕ) (t : ℝ) (g : GL (Fin k) (AF F ⊗[F] E)) : cR F E k t * g = g * cR F E k t := by
  apply (glTens F E k).injective
  rw [map_mul, map_mul, glTens_cR, splitCentre_comm]

theorem latR_le (k : ℕ) : latR F E k ≤ (GlobalTheory.UnitaryBC.latticeGL E k).comap (glTens F E k).toMulEquiv.toMonoidHom := by
  refine sup_le ?_ ?_
  · rintro _ ⟨γ, rfl⟩
    show glTens F E k (bc (inclR (F := F) (AF F)) γ) ∈ GlobalTheory.UnitaryBC.latticeGL E k
    rw [glTens_bc]
    exact ratGL_mem_latticeGL γ
  · rw [Subgroup.zpowers_le]
    show glTens F E k (cR F E k 1) ∈ GlobalTheory.UnitaryBC.latticeGL E k
    rw [glTens_cR]
    simpa using zpow_mem_latticeGL (E := E) (a := k) 1

instance discreteTopology_latR (k : ℕ) : DiscreteTopology (latR F E k) :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : latR F E k => (⟨glTens F E k x.1, latR_le k x.2⟩ : GlobalTheory.UnitaryBC.latticeGL E k))
    (((glTens F E k).continuous.comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext ((glTens F E k).injective (congrArg Subtype.val h)))

end GlobalTheory.GLOneVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ATransportGramTranspose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ATransportGramTranspose
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Transport

theorem l2A_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilL2Words.l2A D.host.F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A D.host.F μ Φ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  refine GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn D.host.F κ om ?_
    (GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom)
  rintro ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D S T JA JB ξ hA hB a b
  exact (hom a b g h hh hg Φ hΦ).1

end GlobalTheory.WeilL2Transport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ATransportGramTransposeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l2A_transport_gram_transpose : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilL2Words.l2A D.host.F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A D.host.F μ Φ := by
  first | exact @GlobalTheory.WeilL2Transport.l2A_transport | exact GlobalTheory.WeilL2Transport.l2A_transport | (intros; apply GlobalTheory.WeilL2Transport.l2A_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelInduction
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviSliceTwo


set_option maxHeartbeats 1000000 in
theorem secondSlice_mem_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₂ : Submodule ℂ (GA E (a - r) → ℂ), FiniteDimensional ℂ V₂ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₁ : GA E r, (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₂ := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨L', W', hL', hW', hA⟩ := GlobalTheory.T.constant_term_finite_dimensional_span E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨X', D, hX', hB⟩ := GlobalTheory.T.constant_term_finite_dimensional_span_parabolic E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  have hfin := hind (a - r) (by omega)
  haveI := hfin L' hL' W' hW' X' hX' D
  refine ⟨(Submodule.span ℂ (GlobalTheory.HCF.formsGL E (a - r) L' W' X' D)).map (Sm E (a - r)).subtype, inferInstance, ?_⟩
  intro φ hφ m₁
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨ψ, hψ, hleft, hlev, hkfin, hgr, hL'ψ, hW'ψ⟩ := hA φ hφ m₁
    obtain ⟨hU, hUD, hchar⟩ := hB φ hφ m₁ ψ hψ
    have hAψ : IsAutForm ψ := ⟨hleft, hlev, hkfin, hU, hgr⟩
    have hdec := GlobalTheory.T.mem_span_genEigen_of_finiteDimensional_orbit_alt (Sm E (a - r)) (Zalg E (a - r))
      (fun x hx y hy => (GlobalTheory.AutGrowth.KilledFin.Zalg_commute hx hy).eq) X' D ψ hU hUD hchar
    refine ⟨ψ, Submodule.span_mono ?_ hdec, hψ⟩
    rintro ψ' ⟨hψ'U, χ, hχ, hnil⟩
    obtain ⟨e1, e2, e3⟩ := GlobalTheory.T.finiteDimensional_forms_gl_inductive_rank E (a - r) hfin L' W' ψ hAψ hL'ψ hW'ψ ψ' hψ'U
    exact ⟨e1, e2, e3, χ, hχ, hnil⟩
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    funext m₂
    simp only [Submodule.coe_subtype, ZeroMemClass.coe_zero, Pi.zero_apply, integral_zero]
  | add x y hx hy ihx ihy =>
    have hint : ∀ z ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ h,
        IntegrableOn (fun x => z.1 (unip x * h)) 𝓕 μ := by
      intro z hz h
      have hP : Continuous z.1 ∧ (∀ γ h, z.1 (ratGL E a γ * h) = z.1 h) := by
        induction hz using Submodule.span_induction with
        | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
        | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
        | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
        | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩
      haveI := hμ
      exact CuspidalL2GL.integrableOn_unip hP.1 hP.2 μ h𝓕 h
    obtain ⟨u, hu, eu⟩ := ihx
    obtain ⟨v, hv, ev⟩ := ihy
    refine ⟨u + v, add_mem hu hv, ?_⟩
    funext m₂
    have eu₂ := congrFun eu m₂
    have ev₂ := congrFun ev m₂
    simp only [Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply] at *
    rw [integral_add (hint x hx _) (hint y hy _)]
    exact congrArg₂ (· + ·) eu₂ ev₂
  | smul c x hx ihx =>
    obtain ⟨u, hu, eu⟩ := ihx
    refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
    funext m₂
    have := congrFun eu m₂
    simp only [Submodule.coe_subtype, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at *
    rw [integral_const_mul, this]

end GlobalTheory.LeviSliceTwo

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelInductionStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_gl_of_open_level_induction : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₂ : Submodule ℂ (GA E (a - r) → ℂ), FiniteDimensional ℂ V₂ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₁ : GA E r, (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₂ := by
  first | exact @GlobalTheory.LeviSliceTwo.secondSlice_mem_finiteDimensional | exact GlobalTheory.LeviSliceTwo.secondSlice_mem_finiteDimensional | (intros; apply GlobalTheory.LeviSliceTwo.secondSlice_mem_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoords
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoordAct

theorem at_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (a * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

theorem at_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (z * a) := fun u hu => by
  rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {ι : Type} (s : Finset ι) (f : ι → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hf : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu

theorem act_kap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  intro F E _ _ _ _ _ σ v w hw h n d X Y A Bm g₁ g₂ _ _ x
  set P : Matrix (Fin n) (Fin d) (w.adicCompletion E) := (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ with hP
  have hK : kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x = P.map (ptAt hw h) := kap_apply hw h _ _ x
  have hmm : (P.map (ptAt hw h)).map (locW h) = P := by
    rw [Matrix.map_map]; exact Matrix.ext fun i j => locW_ptAt hw h _
  rw [hK, kap_apply]
  simp only [actAB]
  change mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ = _
  have hat : ∀ i j, At (evFin F v) ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ) i j) := fun i j => by
    simp only [Matrix.mul_apply]
    refine at_sum _ _ fun k => at_mul_right _ (at_sum _ _ fun l => at_mul_left _ (at_ptAt hw h _))
  have e1 : mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ =
      ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ).map (locW h)).map (ptAt hw h) := by
    exact Matrix.ext fun i j => (ptAt_locW hw h (hat i j)).symm
  rw [e1]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, hmm, Matrix.transpose_map, hP]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hB : (((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ *
      ((Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hA : (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, Matrix.mul_one, ← Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)), hA, Matrix.one_mul]

end GlobalTheory.InertCoordAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoordsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_action_on_tensorCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  first | exact @GlobalTheory.InertCoordAct.act_kap | exact GlobalTheory.InertCoordAct.act_kap | (intros; apply GlobalTheory.InertCoordAct.act_kap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfStandardChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfStandardChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words.StdTheta

def negSum (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  -(∑ w : {w : InfinitePlace F // w.IsReal}, (LinearMap.proj w).comp (LinearMap.fst ℝ _ _))

theorem negSum_apply (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    negSum F z = -∑ w, z.1 w := by
  simp [negSum]

theorem negSum_nondeg (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (z : mixedEmbedding.mixedSpace F)
    (hz : z ≠ 0) : ∃ u, negSum F (z * u) ≠ 0 := by
  have h1 : z.1 ≠ 0 := by
    intro h0
    apply hz
    refine Prod.ext h0 (funext fun w => absurd (IsTotallyReal.isReal w.1) ?_)
    exact InfinitePlace.not_isReal_iff_isComplex.2 w.2
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h1
  refine ⟨(Pi.single w 1, 0), ?_⟩
  rw [negSum_apply]
  simpa [Pi.single_apply] using hw

theorem cmTypeComponents_sum_eq_realCoordinates_sum (D : D7) (x : Ainf D.host.F) :
    ∑ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((∑ w, (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x).1 w : ℝ) : ℂ) := by
  haveI := D.sp.cm.totReal
  have e1 : ∀ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (GlobalTheory.AdelicU.placeOf D ρ) (x (GlobalTheory.AdelicU.placeOf D ρ)) := by
    intro ρ
    show Formalism.L2.Fam.ThC.projAt (tauE D ρ) (x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Formalism.L2.Fam.ThC.projAt_tmul, map_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun ρ _ => e1 ρ,
    (GlobalTheory.AdelicU.placeOf_bijective D).sum_comp (fun w => InfinitePlace.Completion.extensionEmbedding w (x w)),
    Complex.ofReal_sum]
  refine (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w : InfinitePlace D.host.F => IsTotallyReal.isReal w) _ _
    fun w => ?_).symm
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (x w.1)

theorem isStdInf_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  intro D ψ hψ
  haveI := D.sp.cm.totReal
  have h := Formalism.L2.Fam.ThC.allSome_fam.1 hψ.2
  refine ⟨negSum D.host.F, negSum_nondeg D.host.F, fun z => ?_⟩
  have hx := h ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z)
  rw [cmTypeComponents_sum_eq_realCoordinates_sum, RingEquiv.apply_symm_apply] at hx
  show psiInf D.host.F ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z) = _
  rw [hx, negSum_apply]
  congr 1
  push_cast
  ring

end GlobalTheory.WeilL2Words.StdTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfStandardCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar | exact GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar | (intros; apply GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOne
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPairs

open Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj

theorem conjPl_eq_plMap {D : D7} [IsCMField D.host.E] (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.DivisionValues.conjPl P = plMap conjE P := by
  apply HeightOneSpectrum.ext
  rw [asIdeal_plMap]
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = _
  congr 1
  refine RingEquiv.ext fun x => RingOfIntegers.ext ?_
  rfl

theorem conjE_symm {E : Type} [Field E] [NumberField E] [IsCMField E] : (conjE (E := E)).symm = conjE :=
  RingEquiv.ext fun x => by rw [conjE_symm_apply, conjE_apply]

theorem finprod_val_nu_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T},
    Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E))
      (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  set ν := nuH G μ₀ i j with hν
  have hT : TrivOnF ν := (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1.2.1
  set c : HeightOneSpectrum (𝓞 D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun P => Formalism.DivisionValues.conjPl P with hcdef
  have hc : ∀ P, c P = plMap conjE P := fun P => conjPl_eq_plMap P
  have hcc : ∀ P, c (c P) = P := fun P => by
    rw [hc, hc]
    have h := plMap_symm_plMap (conjE (E := D.host.E)) P
    rwa [conjE_symm] at h
  have hcinj : Function.Injective c := fun x y h => by rw [← hcc x, h, hcc y]
  have hunr : ∀ P, ν.UnrAt P ↔ ν.UnrAt (c P) := fun P => by
    rw [hc, ← unrAt_inv_iff ν hT P]
    have hloc (x : (P.adicCompletion D.host.E)ˣ) :
        (ν⁻¹).loc P x = (ν.loc P x)⁻¹ := by
      rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single,
        GlobalTheory.CMVal.finPart_inv]
    constructor <;> intro h x hx
    · rw [hloc, h x hx, inv_one]
    · have := h x hx
      rw [hloc, inv_eq_one] at this
      exact this
  have hval : ∀ P, ν.UnrAt P → ((ν.val P : ℂˣ) : ℂ) * ((ν.val (c P) : ℂˣ) : ℂ) = 1 := fun P hP => by
    have h1 := val_inv_eq ν hT P (by rw [← hc]; exact (hunr P).1 hP)
    rw [HChar.val_inv] at h1
    rw [hc, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set Q' := (Lc.Q t).filter fun P => ν.UnrAt P with hQ'
  have hset : {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w} = (↑(Q' ∪ Q'.image c) : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe, hQ',
      Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (hL.Q_ram t w).1 h1 with h | ⟨P, hP, hcP⟩
      · exact Or.inl ⟨h, h2⟩
      · have e : w = c P := GlobalTheory.GoodPrimes.isConjPl_iff.1 hcP
        exact Or.inr ⟨P, ⟨hP, (hunr P).2 (e ▸ h2)⟩, e.symm⟩
    · rintro (⟨h, h2⟩ | ⟨P, ⟨hP, h2⟩, rfl⟩)
      · exact ⟨(hL.Q_ram t w).2 (Or.inl h), h2⟩
      · exact ⟨(hL.Q_ram t (c P)).2 (Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl⟩), (hunr P).1 h2⟩
  have hdisj : Disjoint Q' (Q'.image c) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨P', hP'Q, e⟩ := Finset.mem_image.1 hP'
    exact ((hL.Q_pl t) P' (Finset.mem_filter.1 hP'Q).1).2 P (Finset.mem_filter.1 hP).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 e.symm)
  show ∏ᶠ w ∈ {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w}, ((ν.val w : ℂˣ) : ℂ) = 1
  rw [hset, finprod_mem_coe_finset, Finset.prod_union hdisj, Finset.prod_image fun x _ y _ h => hcinj h,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun P hP => hval P (Finset.mem_filter.1 hP).2

end GlobalTheory.TwistPairs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOneStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_nu_values_twist_only_ramified_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E)) (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  first | exact @GlobalTheory.TwistPairs.finprod_val_nu_eq_one | exact GlobalTheory.TwistPairs.finprod_val_nu_eq_one | (intros; apply GlobalTheory.TwistPairs.finprod_val_nu_eq_one <;> assumption)
end
end
