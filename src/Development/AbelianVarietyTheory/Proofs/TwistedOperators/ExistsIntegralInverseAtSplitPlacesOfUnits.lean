module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LocalInvIdem

theorem toEAf_surj {D : D7} (a : EAf D) : ∃ α : AE D, toEAf D α = a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [RingHom.map_add (f := _), hp, hq]⟩
  | tmul x y => exact ⟨pairA D.host.F 0 y ⊗ₜ[D.host.F] x, rfl⟩

theorem inv_of_chart {D : D7} {ePP α : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hC : GlobalTheory.SplitHecke.Chart ePP v π) {c : Fv D.host.F v} (hc : π α = c) (hv1 : Valued.v c = 1) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv1; exact zero_ne_one hv1
  obtain ⟨t, ht⟩ := hC.1 c⁻¹
  refine ⟨ePP * t, ?_, ?_⟩
  · refine (hC.2.2.2 t).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
    rw [ht, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  · have h1 : π (α * t - 1) = 0 := by
      rw [map_sub, map_mul, ht, hc, mul_inv_cancel₀ hc0, map_one, sub_self]
    have h2 := (hC.2.1 _).1 h1
    linear_combination h2

theorem exists_local_inv {D : D7} {PP : Pl D.host.E} {ePP : AE D} (hPP : Formalism.L2.NTheta.IsIdemAt ePP PP)
    (α : AE D) (ha : toEAf D α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hu : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D α, ha⟩)) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  obtain ⟨v, τ, hIdem, hP⟩ := GlobalTheory.SplitIdemDict.exists_emb hPP
  have hProj := (GlobalTheory.SplitIdemDict.isProjAt_iff τ PP).2 hP
  obtain ⟨⟨r, -, hr0, -, hrS⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v (splitProj τ) PP hProj
  obtain ⟨hC, hE, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v (splitProj τ) ePP hIdem
  obtain ⟨hmem, hrr⟩ := hrS (toEAf D α) ha
  obtain ⟨c, hc⟩ : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA (splitProj τ) α = c := ⟨_, rfl⟩
  have hcE := (hE α).trans hc
  have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hv1 : Valued.v c = 1 := by
    have hle : Valued.v c ≤ 1 := by
      rw [← hcE]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hmem
    refine le_antisymm hle (not_lt.1 fun hlt => hu.ne_zero ?_)
    rw [← hrr]
    refine (hr0 _).2 ?_
    exact (congrArg Valued.v hcE).trans_lt hlt
  exact inv_of_chart hC hc hv1

theorem exists_inv : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  intro D Z e he a ha hZ
  obtain ⟨α, rfl⟩ := toEAf_surj a
  obtain ⟨es, hes, hsum⟩ := he.1
  have key : ∀ PP ∈ Z, ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = es PP :=
    fun PP hPP => exists_local_inv (hes PP hPP) α ha (hZ PP hPP)
  choose! γ hγ1 hγ2 using key
  refine ⟨toEAf D (∑ PP ∈ Z, γ PP), GlobalTheory.IdemIntegral.toEAf_mem_of_finPart ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum (finPart D)]; exact sum_mem fun PP hPP => hγ1 PP hPP
  · have hαw : α * ∑ PP ∈ Z, γ PP = e := by
      rw [Finset.mul_sum, hsum]; exact Finset.sum_congr rfl fun PP hPP => hγ2 PP hPP
    have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    rw [← map_mul, ← map_mul, hαw, hee]

end GlobalTheory.LocalInvIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  first | exact @GlobalTheory.LocalInvIdem.exists_inv | exact GlobalTheory.LocalInvIdem.exists_inv | (intros; apply GlobalTheory.LocalInvIdem.exists_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta

theorem isSBHalf_levDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) (levDatum S T βS βT LT Q m e) := by
  intro D S T ΛS ΛT βS βT LT Q m Z e hS hT hfS hfT he
  classical

  have hlin : ∀ (k : ℕ) (u : WO S T), frMapAdj S T βS βT (k • u) = k • frMapAdj S T βS βT u := by
    intro k u
    induction k with
    | zero =>
      have h0 := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT 0 0
      simpa using h0
    | succ n ih =>
      rw [succ_nsmul, GlobalTheory.PlaceVec.frMapAdj_add, ih, succ_nsmul]
  have hadd : ∀ (x u : WO S T) (k : ℕ) i j,
      frMapAdj S T βS βT (x + k • u) i j = frMapAdj S T βS βT x i j + k * frMapAdj S T βS βT u i j := by
    intro x u k i j
    rw [GlobalTheory.PlaceVec.frMapAdj_add, hlin, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]

  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), ∀ i j, (M : EAf D) * frMapAdj S T βS βT u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    obtain ⟨M, hM, hMl⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
    obtain ⟨k, hk, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
    refine ⟨k * M, Nat.mul_pos hk hM, fun u hu i j => ?_⟩
    have hint : IsIntM ((M • u).map (toEAf D)) := by
      intro a b
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, nsmul_eq_mul]
      exact hMl u hu a b
    have h := hup (M • u) hint i j
    rw [hlin, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc] at h
    simpa [Nat.cast_mul] using h

  have hC : ∃ K : ℕ, 0 < K ∧ ∀ t, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    obtain ⟨k, hk, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
    obtain ⟨K, hK, hKl⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
    refine ⟨K * k, Nat.mul_pos hK hk, fun t ht hti => ?_⟩
    have hinf : t.map (infPart D) = 0 :=
      GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)) ht
    have hinf' : (k • t).map (infPart D) = 0 := by
      ext a b
      have h1 := congrFun (congrFun hinf a) b
      rw [Matrix.map_apply, Matrix.zero_apply] at h1
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, h1, smul_zero, Matrix.zero_apply]
    have hint' : ∀ a b, toEAf D ((k • t) a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro a b
      have h2 := hdown t hti a b
      rwa [Matrix.smul_apply, Matrix.map_apply, ← map_nsmul] at h2
    rw [← smul_smul]
    exact hKl (k • t) hinf' hint'

  have hω : ∀ y y' : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)),
      (∀ PP ∈ LT.Pg ∪ Q, y PP = y' PP) →
        omegaG LT m y * omegaQ Q T.rank m (-1) y = omegaG LT m y' * omegaQ Q T.rank m (-1) y' := by
    intro y y' h
    rw [GlobalTheory.PlaceDatum.omegaG_congr LT m y y' (fun PP hP => h PP (Finset.mem_union_left _ hP)),
      GlobalTheory.PlaceDatum.omegaQ_congr Q T.rank m (-1) y y' (fun PP hP => h PP (Finset.mem_union_right _ hP))]
  have key := GlobalTheory.PlaceDatum.isSBHalf_of_red (cA D e)
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (frMapAdj S T βS βT) hadd hB hC (LT.Pg ∪ Q) (fun y => omegaG LT m y * omegaQ Q T.rank m (-1) y) hω
  unfold levDatum
  exact key

end GlobalTheory.FinZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFiniteDatum_isSchwartzBruhat_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) (levDatum S T βS βT LT Q m e) := by
  first | exact @GlobalTheory.FinZeta.isSBHalf_levDatum | exact GlobalTheory.FinZeta.isSBHalf_levDatum | (intros; apply GlobalTheory.FinZeta.isSBHalf_levDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgCol

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frRel (W : G.Weil) {U : Set T} (N : Std G U) (X : Node) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  (W.onb X τ)⁻¹ * N.frC X τ

def frCh (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => frRel W N (.top (j + 1)) τ) (fun τ => ((frRel W N (.top j) τ)⁻¹)ᵀ)

def frChInv (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => (frRel W N (.top (j + 1)) τ)⁻¹) (fun τ => (frRel W N (.top j) τ)ᵀ)

end GlobalTheory.AvgCol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.TermVolDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem isDefiniteSpace_of_isV {X : LSp D} {ν : ℕ} (h : X.IsV ν 0) : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace X.sp :=
  ⟨h.sigOK, fun τ => Or.inl (by rw [h.sig τ, h.rank, Nat.sub_zero])⟩

theorem isMeasDef_of_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U)
    {μ₀ : T} (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) (M : Vol G) (hM : IsTermVol t S Φ β M) :
    (∀ j (h : j < D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.top j)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.top j)) (S.levTop t Φ β j h) ∧
      IsMeasDef (G.V (.top j)) (S.levTop t Φ β j h) (M.ν (.top j)) (M.fd (.top j))) ∧
    ∀ i (h : i ≤ D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.grid i D.R.m)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.grid i D.R.m)) (S.levRow t i h) ∧
      IsMeasDef (G.V (.grid i D.R.m)) (S.levRow t i h) (M.ν (.grid i D.R.m)) (M.fd (.grid i D.R.m)) := by
  refine ⟨fun j h => ⟨?_, S.isCO_levTop W t Φ β h, ?_⟩, fun i h => ⟨?_, S.isCO_levRow W t h, ?_⟩⟩
  · exact isDefiniteSpace_of_isV (node_isV G hL (X := .top j) h.le)
  · have e := hM.1 j h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e
  · have hV := node_isV G hL (X := .grid i D.R.m) ⟨h, le_rfl⟩
    have e : Node.neg D.R.m (.grid i D.R.m) = 0 := by simp [Node.neg]
    rw [e] at hV
    exact isDefiniteSpace_of_isV hV
  · have e := hM.2 i h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e

end GlobalTheory.RowClaim.TermVolDef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndex
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHomIdx

open GlobalTheory.FinWeilO

theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X) (M : X →+ Y)
    (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    A.relIndex (A.map φ) = (A.map M).relIndex ((A.map M).map m) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := A.map M) M (A.map φ), ← AddSubgroup.inf_relIndex_right A,
    ← AddSubgroup.inf_relIndex_right ((A.map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨a, ha, hax⟩, hx⟩
  refine ⟨?_, hx⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : P (a - φ y) = 0 := hK _ (by rw [map_sub, hax, sub_self])
  have h2 : P (φ y) = P a := by rw [map_sub, sub_eq_zero] at h1; exact h1.symm
  have h3 : φ y = (y - P y) + P a := by rw [← hφ y hy, h2]; abel
  rw [h3]
  exact add_mem (sub_mem hy (hPA y hy)) (hPA a ha)

end GlobalTheory.InertHomIdx


open GlobalTheory.FinWeilO in
theorem GlobalTheory.InertHomIdx.idx_latF_moved : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : Gv T v, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v g))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1)) := by
  intro D S T v w h hi g
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hε : IsPlaceIdem D v ε := hns.1
  have hη : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hk : GlobalTheory.WeilParts.SuppPl ε T (embV T v g) := by
    rw [GlobalTheory.PlaceDatum.placeIdem_eq hε hη]
    exact GlobalTheory.PlaceTensor.suppPl_emb T v g
  have hg : GlobalTheory.WeilParts.SuppPl ε S (1 : GA D S) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have hmat : (mt T (embV T v g)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h g).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v g)
    rw [proj_emb_self] at e
    exact e
  refine GlobalTheory.InertHomIdx.relIndex_map_of_proj (latF S T (frameLat S) (frameLat T)).toAddSubgroup
    (rhoF S T (1, embV T v g)).toAddMonoidHom (mulF S T (algebraMap (AF D.host.F) (AE D) ε)).toAddMonoidHom
    (GlobalTheory.InertHomIdx.matW S T w) (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1) ?_ ?_ ?_ ?_
  · intro x
    show (actO S T 1 (embV T v g) x).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h g).1 * (x : WO S T).map (GlobalTheory.InertHomIdx.compW D w)
    rw [actO, inv_one, mt_one, Matrix.mul_one, Matrix.map_mul, hmat]
  · intro x hx
    refine XF.ext (Matrix.ext fun i j => ?_)
    have h0 : GlobalTheory.InertHomIdx.compW D w ((x : WO S T) i j) = 0 := congrFun (congrFun hx i) j
    show algebraMap (AF D.host.F) (AE D) ε * (x : WO S T) i j = 0
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hp, zero_mul, RingHom.map_zero]
    · rw [RingHom.map_mul, finPart_of_isPrimeIdem hp, singleAt_mul, RingHom.map_zero]
      have h1 : compAt D.host.F w (finPart D ((x : WO S T) i j)) = 0 := h0
      rw [h1, mul_zero, ← singleAt_zero]
  · intro a ha
    exact GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε ha)
  · intro a _
    refine XF.ext ?_
    have := hoff (a : WO S T)
    rw [sub_smul, sub_smul, one_smul, one_smul] at this
    exact this

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_homLattice_index_eq_localComponent_index : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : Gv T v, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v g))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1)) := by
  first | exact @GlobalTheory.InertHomIdx.idx_latF_moved | exact GlobalTheory.InertHomIdx.idx_latF_moved | (intros; apply GlobalTheory.InertHomIdx.idx_latF_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegrals
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegrals
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.RegClass

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

variable {D : D7} {V : HSp D}

theorem rat_mem (g : GF V) : rat V g ∈ GQ V := by
  rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; exact ⟨g, rfl⟩

def classEquiv (γ : GF V) : {δ : GF V | IsConj γ δ} ≃ ratClass (GQ V) (rat V γ) :=
  Equiv.ofBijective (fun δ => ⟨rat V δ, by
      obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
      refine ⟨rat V c⁻¹, rat_mem _, ?_⟩
      rw [← hc]; simp only [map_mul, map_inv, inv_inv]⟩)
    ⟨fun a b h => Subtype.ext (ratEmb_injective _ _ (congrArg Subtype.val h)), fun δ => by
      obtain ⟨δ, g, hg, rfl⟩ := δ
      rw [show GQ V = (rat V).range from (range_ratEmb ..).symm] at hg
      obtain ⟨c, rfl⟩ := hg
      refine ⟨⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩⟩, Subtype.ext ?_⟩
      simp only [map_mul, map_inv]⟩

theorem classKernel_eq (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) :=
  ((classEquiv γ).tsum_eq fun δ : ratClass (GQ V) (rat V γ) => f (x⁻¹ * δ * x)).symm

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_iff {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) :
    (IntegrableOn φ 𝓕 μ ↔ Integrable (descend (GQ V) φ) (autMeasure V μ)) ∧
      ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (F := descend (GQ V) φ) (p := 1))
    rw [hφ.lift_descend, memLp_one_iff_integrable, memLp_one_iff_integrable] at this
    exact this.symm
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

theorem regClass : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧
    ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x =
      ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧
    (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ),
      ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔
        Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧
          ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := by
  intro D V γ hγ
  refine ⟨GlobalTheory.regSS_conjClass_isSSClass γ hγ, fun f => ⟨classKernel_eq γ f, fun _ hcs μ _ c => ?_⟩⟩
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ) f) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  constructor
  · intro H
    have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) μ
    obtain ⟨-, hi, hv⟩ := H _ h𝓕
    obtain ⟨e1, e2⟩ := fd_iff h𝓕 hinv
    exact ⟨e1.1 hi, e2 ▸ hv⟩
  · rintro ⟨hi, hv⟩ 𝓕 h𝓕
    obtain ⟨e1, e2⟩ := fd_iff h𝓕 hinv
    exact ⟨summable_class hcs (rat_mem γ), e1.2 hi, e2.trans hv⟩

theorem main : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧ ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧ (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ), ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔ Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧ ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := regClass

end GlobalTheory.RegClass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegralsStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧ ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧ (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ), ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔ Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧ ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := by
  first | exact @GlobalTheory.RegClass.main | exact GlobalTheory.RegClass.main | (intros; apply GlobalTheory.RegClass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMulEntry
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section
namespace GlobalTheory.FrameScale

theorem vecMul_entry {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (x : k) (q r : Fin c) (m : ι)
    (hb : ∀ i, b i m = x * φ (a i r)) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = x * φ ((Formalism.UG.cT σ a * g * a) q r) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, hb, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameScale
end

theorem GlobalTheory.FrameScale.clauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m)
  (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
  (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : k) (e : ℕ), ϖ ≠ 0 → Function.Injective j →
  (∀ r i, β.b i (j r) = ϖ ^ (e * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) →
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) →
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1)) •
      (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (j ⟨q.1, by omega⟩) 1) ∧
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) *
      (if q.1 = σ then -1 else 1))⁻¹ • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
      Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1) := by
  intro D _ T L _ _ sc G W _ _ F hF σ h' k _ _ _ _ p β j ϖ e hϖ hj hb hout
  have hne : (-D.host.xi0) ≠ 0 := neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hc : p.pr (incA D (-D.host.xi0)) ≠ 0 := ((hne.isUnit.map (incA D)).map p.pr).ne_zero
  have hc' : p.pr (incA D (star (-D.host.xi0))) ≠ 0 :=
    (((star_ne_zero.2 hne).isUnit.map (incA D)).map p.pr).ne_zero
  have hcol : ∀ (q : Fin (σ + 1)) i, xFB F σ h' i q = incA D ((-D.host.xi0) ^ (q.1 + 1)) * incA D ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩) := by
    intro q i
    have := congrFun (GlobalTheory.CharXFB.xFB_col F hF σ h' q) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    rfl
  have key : ∀ m, β.b' *ᵥ (fun i => β.b i m) = Pi.single m 1 := by
    intro m
    have : (fun i => β.b i m) = β.b *ᵥ Pi.single m 1 := by
      funext i; simp [Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have hv : (fun i => p.pr (xFB F σ h' i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * (ϖ ^ (e * (q.1 + 1)))⁻¹) • fun i => β.b i (j ⟨q.1, by omega⟩) := by
      funext i
      rw [hcol]
      simp only [map_mul, map_pow, Pi.smul_apply, smul_eq_mul, hb]
      field_simp
    rw [hv, Matrix.mulVec_smul, key, smul_smul]
    convert one_smul k _
    rw [inv_pow]
    field_simp
  · have hv : (fun i => p.pr (cA D (xFB F σ h' i q))) = p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) •
        fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩))) := by
      funext i
      rw [hcol]
      simp only [map_mul, GlobalTheory.DualPairCheck.cA_incA, star_pow, map_pow, Pi.smul_apply, smul_eq_mul]
    have hsm : ∀ (x : k) (u : Fin (G.V (.grid (2 * σ + 2) 0)).rank → k)
        (M : Matrix (Fin (G.V (.grid (2 * σ + 2) 0)).rank) (Fin (G.V (.grid (2 * σ + 2) 0)).rank) k),
        (x • u) ᵥ* M = x • (u ᵥ* M) := by
      intro x u M
      funext m
      simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hg := (G.colDec (2 * σ + 2) (by omega) h').gram
    have hw : ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩)))) ᵥ*
        (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
        (ϖ ^ (e * (2 * σ + 1 - q.1)) * (if q.1 = σ then -1 else 1)) • Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1 := by
      funext m
      by_cases hm : m ∈ Set.range j
      · obtain ⟨r, rfl⟩ := hm
        refine (GlobalTheory.FrameScale.vecMul_entry (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * σ + 2) (by omega) h').a _ β.b _ ⟨q.1, by omega⟩ r (j r) (hb r)).trans ?_
        rw [hg]
        simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, RingHom.coe_comp, Function.comp_apply]
        by_cases hr : r = ⟨2 * σ - q.1, by omega⟩
        · subst hr
          have e1 : 2 * σ - q.1 + 1 = 2 * σ + 1 - q.1 := by omega
          rw [Pi.single_eq_same, if_pos (by simp only; omega), e1]
          by_cases hq : q.1 = σ
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hq]
            simp
          · rw [if_neg (fun h => hq (by have := congrArg Fin.val h; simp only at this; omega)), if_neg hq]
            simp
        · rw [Pi.single_eq_of_ne (hj.ne hr), if_neg (fun h => hr (Fin.ext (by simp only; omega)))]
          simp
      · rw [hout m hm ⟨q.1, by omega⟩, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hm ⟨_, h.symm⟩), smul_zero]
    have hs : (if q.1 = σ then (-1 : k) else 1) ≠ 0 := by split_ifs <;> norm_num
    rw [hv, hsm, hw, smul_smul, smul_smul]
    refine (congrArg (· • Pi.single (j ⟨2 * σ - q.1, by omega⟩) (1 : k)) ?_).trans (one_smul k _)
    field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandTame

theorem integral_prod_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) (μ₄ : Measure δ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (F : α × β × γ × δ → ℂ) (hF : Integrable F (μ₁.prod (μ₂.prod (μ₃.prod μ₄)))) :
    ∫ y, F y ∂(μ₁.prod (μ₂.prod (μ₃.prod μ₄))) = ∫ a, ∫ b, ∫ c, ∫ d, F (a, b, c, d) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [integral_prod _ hF]
  refine integral_congr_ae (hF.prod_right_ae.mono fun a ha => ?_)
  simp only
  rw [integral_prod _ ha]
  refine integral_congr_ae (ha.prod_right_ae.mono fun b hb => ?_)
  simp only
  rw [integral_prod _ hb]

theorem sfinite_of_finite {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] : SFinite μ := inferInstance

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simp only [hh f hf]; exact h.cont f hf
  · simp only [hh f hf]; exact h.bdd f hf
  · simp only [hh f hf]; rw [e _ hI]; exact h.sup f hf m α hα hI

theorem rapid_core {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {G : GA D S → ℂ} (hG : RapidDec S G) (k : ℕ) :
    ∃ C : ℝ, ∀ n ∈ flagN d, ∀ h, ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D S S₀ ρ d
  obtain ⟨C', hC'⟩ := hG.decay (a * k)
  refine ⟨|C| ^ k * C', fun n hn h => ?_⟩
  have h1 : quotHeight S₀ h ≤ |C| * quotHeight S (n * d.emb0 h) ^ a :=
    (hC n hn h).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k
      ≤ ‖G (n * d.emb0 h)‖ * (|C| * quotHeight S (n * d.emb0 h) ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos S₀ h).le h1 k) (norm_nonneg _)
    _ = |C| ^ k * (‖G (n * d.emb0 h)‖ * quotHeight S (n * d.emb0 h) ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * C' := mul_le_mul_of_nonneg_left (hC' _) (by positivity)

theorem rapid_theta {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χ χz om) {φ : GA D S → ℂ} (hφ : RapidDec S φ) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀)
    (k : ℕ) : ∃ C : ℝ, ∀ h v, ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ S L χ χz om hom Φ₀ hΦ
  obtain ⟨C', hC'⟩ := hφ.decay (a + k)
  refine ⟨|C| * C', fun h v => ?_⟩
  have h1 : ‖om (h, 1) Φ₀ v‖ ≤ |C| * quotHeight S h ^ a := by
    have := hC h 1 v
    rw [quotHeight_of_mem L (one_mem _), mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k
      ≤ ‖φ h‖ * (|C| * quotHeight S h ^ a) * quotHeight S h ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (pow_pos (quotHeight_pos S _) k).le
    _ = |C| * (‖φ h‖ * quotHeight S h ^ (a + k)) := by ring
    _ ≤ |C| * C' := mul_le_mul_of_nonneg_left (hC' _) (abs_nonneg _)

theorem handP₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B),
    ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G →
    IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ hφ hG hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.L.rank J.W₀.rank
  haveI : SecondCountableTopology (WO J.W₀ B.L) := i3
  haveI : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; exact ENNReal.one_ne_top)
  let Y : Type := GA D B.A × flagN B.d × GA D J.W₀ × WO J.W₀ B.L
  let m : Measure Y := (B.vA.μ.restrict B.vA.𝓕).prod ((B.vN.ν.restrict B.vN.𝓝).prod
    ((J.v0.μ.restrict J.v0.𝓕).prod (vL.μ.restrict vL.𝓕)))
  haveI : IsFiniteMeasure m := by dsimp only [m]; infer_instance
  haveI : SFinite m := sfinite_of_finite m
  let c : Y → ℂ := fun y => G (y.2.1.1 * embA B.d B.o y.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1) *
    (φ y.2.2.1 * star (omz (y.2.2.1, 1) Φ₀ y.2.2.2))
  have hn : Continuous fun y : Y => (y.2.1.1 : GA D B.V) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h0 : Continuous fun y : Y => y.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous fun y : Y => y.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have he : Continuous fun y : Y => B.o.emb (y.1, 1) := B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)
  have hw : Continuous fun y : Y => (B.o.resT J.W₀).symm (0, y.2.2.2) :=
    (B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk hv)
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V).2.2.2.2.1
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ
  have hc : Continuous c :=
    ((hG.continuous.comp (hn.mul (B.d.continuous_embed.comp he))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))).mul
      ((hφ.continuous.comp h0).mul (continuous_star.comp (hJ.comp ((h0.prodMk continuous_const).prodMk hv))))
  have hint : ∀ k : ℕ, Integrable
      (fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k) m := by
    intro k
    obtain ⟨C₁, h₁⟩ := rapid_core B.d hG k
    obtain ⟨C₂, h₂⟩ := rapid_theta homz hφ hΦ k
    have hcc : Continuous fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k :=
      hc.norm.mul ((((continuous_quotHeight _).comp h0).mul ((continuous_quotHeight _).comp he)).pow k)
    refine Integrable.of_bound hcc.measurable.aestronglyMeasurable (C₁ * C₂) (.of_forall fun y => ?_)
    have p1 := quotHeight_pos J.W₀ y.2.2.1
    have p2 := quotHeight_pos B.V₀ (B.o.emb (y.1, 1))
    have n1 : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1‖ = 1 := hψ.1.2.1 _
    rw [Real.norm_of_nonneg (by positivity)]
    have a1 := h₁ _ y.2.1.2 (B.o.emb (y.1, 1))
    have a2 := h₂ y.2.2.1 y.2.2.2
    calc ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k
        = (‖G (y.2.1.1 * B.d.emb0 (B.o.emb (y.1, 1)))‖ * quotHeight B.V₀ (B.o.emb (y.1, 1)) ^ k) *
          (‖φ y.2.2.1‖ * ‖omz (y.2.2.1, 1) Φ₀ y.2.2.2‖ * quotHeight J.W₀ y.2.2.1 ^ k) := by
          simp only [c, norm_mul, norm_star, n1, embA_apply, mul_pow]; ring
      _ ≤ C₁ * C₂ := mul_le_mul a1 a2 (by positivity) (le_trans (by positivity) a1)
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ Y m c (fun y => y.2.2.1) (fun y => B.o.emb (y.1, 1))
    (fun y => (B.o.resT J.W₀).symm (0, y.2.2.2)) hc.measurable h0 he hw hint
  refine tame_congr hψ hT fun f hf => ?_
  refine Eq.trans ?_ (integral_prod_four _ _ _ _ _ (hI f hf)).symm
  simp only [BesL.per, besPer, GlobalTheory.MixPer.besFun, handP, contractT, thPair]
  refine integral_congr_ae (.of_forall fun a => ?_)
  refine integral_congr_ae (.of_forall fun b => ?_)
  simp only
  rw [mul_assoc, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [c]
  ring

end GlobalTheory.HandTame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_handedDown_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  first | exact @GlobalTheory.HandTame.handP₂ | exact GlobalTheory.HandTame.handP₂ | (intros; apply GlobalTheory.HandTame.handP₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodReductionStableValuationRingExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodReductionStableValuationRingExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.GoodBaseChange

theorem good_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  intro E _ _ _ H Dw l Xo c T T' io io' y y' i r _ hv hx hy
  obtain ⟨G, t, m1, m2, hp⟩ := hy
  obtain ⟨φ, hφ⟩ := GlobalTheory.IntFrBaseChange.exists_restrict T T' i r hv
  obtain ⟨G', mG⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', mt⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap i)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap i) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mG⟩ := mG
  obtain ⟨mt⟩ := mt
  obtain ⟨n1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 mt
  have hsq : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => (hφ a).symm))
  rw [hsq] at n2
  obtain ⟨n3, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG n2
  have n4 : SABMap t' Xo.univ.t (xOf y') := by
    rw [hx]
    exact n1
  exact ⟨G', t', n4, n3, MorphismProperty.of_isPullback (P := @IsProper) mG.cart.1 hp⟩

end GlobalTheory.GoodBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodReductionStableValuationRingExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodReduction_stable_valuationRing_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  first | exact @GlobalTheory.GoodBaseChange.good_baseChange | exact GlobalTheory.GoodBaseChange.good_baseChange | (intros; apply GlobalTheory.GoodBaseChange.good_baseChange <;> assumption)
end
end
