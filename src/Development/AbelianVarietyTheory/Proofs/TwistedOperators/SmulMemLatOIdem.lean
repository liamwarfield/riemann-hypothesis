module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow


open Classical in
def extFn {D : D7} {m n : ℕ} (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (t : Mx D m n) : ℂ :=
  if IsHalf (e₀ + e₁) t then Φ (e₀ • t) * halfInd e₁ Λ (e₁ • t) else 0

section Gen
variable {D : D7} {m n : ℕ}

theorem symplO_eq_of_half {S T : HSp D} {e₀ e₁ : AE D} (h01 : e₀ * e₁ = 0) (t y : WO S T)
    (ht : IsHalf (e₀ + e₁) t) (hy : IsHalf (cA D e₀) y) : symplO S T t y = symplO S T (e₀ • t) y := by
  have hw : IsHalf e₁ (t - e₀ • t) := fun i j => by
    have := ht i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [add_mul] at this
    rw [mul_sub, ← mul_assoc, mul_comm e₁ e₀, h01, zero_mul, sub_zero]
    linear_combination this
  have hz : symplO S T (t - e₀ • t) y = 0 := by
    unfold symplO
    rw [GlobalTheory.VecProd.hO_zero' (a := e₁) (b := e₀) h01 hw hy, mul_zero, map_zero]
  have hs := GlobalTheory.VecProd.symplO_sub t (e₀ • t) y
  rw [hz] at hs
  linear_combination -hs

theorem smul_mem_latO_idem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {a : AE D} (ha : a * a = a) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    a • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) _ hu

end Gen

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem selfDual_chi {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) ∧ IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := by
  have hV : ∀ X : Node, X.InRange D.R.m → (G.V X).SigOK ∧ IsSelfDualC (G.V X) (G.Λ X) := fun X hX => by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact ⟨(G.isV hX h0).sigOK, (G.isV hX h0).sd⟩
    · push Not at h0
      obtain ⟨j, rfl⟩ := h0
      exact ⟨(GlobalTheory.ChiGrid.colY_isV D T L μ₀ hL j hX.2).sigOK, (GlobalTheory.ChiGrid.colY_isV D T L μ₀ hL j hX.2).sd⟩
  exact ⟨isSelfDualC_neg (hV (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).2, (hV (.grid i 0) ⟨hi.le, Nat.zero_le _⟩).2⟩

end Grid

end GlobalTheory.CosetRow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHold
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHold
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

namespace GlobalTheory.Chain.SourceLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isLift_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 := by
  unfold IsLevelLift
  refine ⟨Subgroup.one_mem _, ?_, ?_⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [map_one]
    exact rTup_one

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    levChi V β L 1 = 1 := by
  have h := (levChar D.sp.cm V.gram β L).map_one
  rw [levChar_apply] at h
  have h' : levFn β L 1 = 1 := h
  unfold levChi
  rw [map_one, h', Units.val_one]

theorem isLift_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {κ : GA D V} (h : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  have hm := h
  unfold levG levA at hm
  rw [Subgroup.mem_inf, Subgroup.mem_comap, mem_lev] at hm
  obtain ⟨h1, h2, h3⟩ := hm
  exact ⟨h1, h2, Subgroup.mem_bot.mp h3⟩

private lemma levChi_flag1L_eq_levChi_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) :
    levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  have e1 : ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  have e2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  unfold levChi levFn
  rw [e1, e2]
  rfl

theorem law_of_pair {V W : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (β' : GL (Fin W.rank) (Lev.EAf D)) (L' : LevDat D.host.E ℂ W.rank) {X : Type} [AddCommGroup X] [Module ℂ X]
    {κ : GA D V} {u v : X}
    (h : (levChi V β (flagL L) κ)⁻¹ • u = (levChi W β' (flagL L') 1)⁻¹ • v) :
    u = levChi V β (flag1L L) κ • v := by
  have hne : levChi V β (flagL L) κ ≠ 0 := by
    unfold levChi
    exact Units.ne_zero _
  rw [levChi_one W β' (flagL L'), inv_one, one_smul] at h
  rw [levChi_flag1L_eq_levChi_flagL, ← h, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem lawsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → LawsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hIs hθ hωY hωX hvY hvX
  have hInf : R.models_inf := hθ
  refine ⟨?_, ?_⟩
  · intro t k hk κ hκ
    have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) 1 κ := isLift_of_mem _ _ _ hκ
    have hl' := isLift_one (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv)
    have key := GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hIs hInf hωY hvY t k hk 1 κ 1 hl hl'
    have e : flag1L (R.datYt t k R.triv) = R.datYt t k R.triv := rfl
    have hlaw := law_of_pair (R.βY k) (R.datYt t k R.triv) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩
  · intro t κ hκ
    have hl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) 1 κ :=
      isLift_of_mem _ _ _ hκ
    have hl' := isLift_one D.sp.X' R.βX (R.datXt t)
    have key := GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hIs hInf hωX hvX t 1 κ 1 hl hl'
    have e : flag1L (R.datYt t (D.R.m - 1) R.triv) = R.datYt t (D.R.m - 1) R.triv := rfl
    have hlaw := law_of_pair (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) R.βX (R.datXt t) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩

end GlobalTheory.Chain.SourceLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHoldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainSteps_levelCharacter_conditions_hold : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → LawsOK R := by
  first | exact @GlobalTheory.Chain.SourceLaw.lawsOK | exact GlobalTheory.Chain.SourceLaw.lawsOK | (intros; apply GlobalTheory.Chain.SourceLaw.lawsOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)

theorem base_isGood {D : D7} (B : Base D.host.F D.host.E) (hψ : IsStdChar D B.ψ (-1))
    (hP : ∀ v ∈ B.P, ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) : B.IsGood D.sp.cm.sig := by
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := by
             intro v w hw
             have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
               rintro ⟨w1, w2, hne, h1, h2⟩
               apply hne
               have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
                 have hle : w.asIdeal ≤ u.asIdeal := by
                   rw [← hw]
                   exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
                 exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
               rw [key w1 h1, key w2 h2]
             obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
             exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
           psiP := fun v hv => GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v fun hle => hP v hv (Ideal.dvd_iff_le.2 hle) }

theorem exists_good_place (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ S ∧ SplitsFully D.host.E v₁ ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  classical
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := mul_ne_zero (mul_ne_zero hn hq) hd
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  refine ⟨v, fun hu => ?_, ?_, ?_⟩
  · refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt v hp ?_ hv
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.TripleDarboux

end
end
