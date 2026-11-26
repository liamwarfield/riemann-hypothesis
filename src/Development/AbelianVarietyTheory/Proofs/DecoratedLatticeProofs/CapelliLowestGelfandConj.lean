module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctoriality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolev
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ReflectionBoostMatrixConjTransposeMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliLowest

end GlobalTheory.CapelliLowest

namespace GlobalTheory.CapelliLowest

theorem single_comm {N : ℕ} (a b c d : Fin N) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h2), h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h1), h1]
  · simp [Matrix.single_mul_single_of_ne (h := h1), Matrix.single_mul_single_of_ne (h := h2), h1, h2]

theorem lie_of_glRel {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Q X * Q Y - Q Y * Q X = Q (X * Y - Y * X) := by
  refine Matrix.induction_on' X ?_ ?_ ?_
  · simp
  · intro p q hp hq
    have e : (p + q) * Y - Y * (p + q) = (p * Y - Y * p) + (q * Y - Y * q) := by noncomm_ring
    rw [e, map_add (f := _), map_add (f := _), ← hp, ← hq]
    noncomm_ring
  · intro i j x
    refine Matrix.induction_on' Y ?_ ?_ ?_
    · simp
    · intro p q hp hq
      have e : Matrix.single i j x * (p + q) - (p + q) * Matrix.single i j x =
          (Matrix.single i j x * p - p * Matrix.single i j x) + (Matrix.single i j x * q - q * Matrix.single i j x) := by
        noncomm_ring
      rw [e, map_add (f := _), map_add (f := _), ← hp, ← hq]
      noncomm_ring
    · intro k l y
      have hx : Matrix.single i j x = x • Matrix.single i j (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have hy : Matrix.single k l y = y • Matrix.single k l (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have e : x • Matrix.single i j (1 : ℂ) * (y • Matrix.single k l 1) - y • Matrix.single k l (1 : ℂ) * (x • Matrix.single i j 1)
          = (x * y) • (Matrix.single i j (1 : ℂ) * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1) := by
        simp only [smul_mul_smul_comm, mul_comm y x, smul_sub]
      rw [hx, hy, e, single_comm, map_smul, map_smul, map_smul, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x,
        ← smul_sub, h i j k l]
      split_ifs <;> simp

theorem glRel_conj {A : Type} [Ring A] [Algebra ℂ A] (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (g : GL (Fin N) ℂ) (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) :
    Formalism.REAL.GlRel (fun i j => Q (g.1 * Matrix.single i j 1 * (g⁻¹).1)) := by
  have HG : (g⁻¹).1 * g.1 = 1 := g.inv_mul
  have key : ∀ X Y : Matrix (Fin N) (Fin N) ℂ, (g.1 * X * (g⁻¹).1) * (g.1 * Y * (g⁻¹).1) = g.1 * (X * Y) * (g⁻¹).1 := by
    intro X Y
    rw [show g.1 * X * (g⁻¹).1 * (g.1 * Y * (g⁻¹).1) = g.1 * X * ((g⁻¹).1 * g.1) * Y * (g⁻¹).1 by simp only [mul_assoc],
      HG, mul_one]
    simp only [mul_assoc]
  intro a b c d
  simp only
  rw [lie_of_glRel Q h, key, key, ← sub_mul, ← mul_sub, single_comm]
  split_ifs <;> simp [mul_sub, sub_mul]

end GlobalTheory.CapelliLowest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (c : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * c ∈ 𝒪[k] := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[k]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : b ∣ ((Nat.card 𝓀[k] ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[k] ^ m, pow_pos Nat.card_pos m, ?_⟩
  have hb' : (algebraMap 𝒪[k] k b) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0
  have : ((Nat.card 𝓀[k] ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) =
      algebraMap 𝒪[k] k (d * a) := by
    rw [← map_natCast (algebraMap 𝒪[k] k), hd, map_mul, map_mul]
    field_simp
  rw [this]
  exact (d * a).2

theorem exists_nat_mul_mem_fin {ι : Type} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * c i ∈ 𝒪[k] := by
  classical
  choose N hN h using fun i => exists_nat_mul_mem (c i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_mem {n n' m m' : Type} [Fintype n] [Fintype n'] {N : ℕ} (b : Matrix m n k) (b' : Matrix n' m' k)
    (hb : ∀ i a, (N : k) * b i a ∈ 𝒪[k]) (hb' : ∀ a j, (N : k) * b' a j ∈ 𝒪[k]) (x : Matrix n n' k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) (i : m) (j : m') : ((N * N : ℕ) : k) * (b * x * b') i j ∈ 𝒪[k] := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine sum_mem fun a _ => sum_mem fun c _ => ?_
  have : ((N * N : ℕ) : k) * (b i c * x c a * b' a j) = ((N : k) * b i c) * x c a * ((N : k) * b' a j) := by
    push_cast; ring
  rw [this]
  exact mul_mem (mul_mem (hb i c) (hx c a)) (hb' a j)

end GlobalTheory.FinPl.RdInt

theorem GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × n => β.b x.1 x.2) (fun x : n' × Fin S.rank => α.b' x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  refine ⟨K * (N₀ * N₀), Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀), fun t ht hrd => ?_⟩
  have hent := GlobalTheory.FinPl.RdInt.entry_mem β.b α.b' (fun i a => h₀ (Sum.inl (i, a))) (fun a j => h₀ (Sum.inr (a, j)))
    (rd α β t) hrd
  have htw := GlobalTheory.FinPl.HalfInd.wr_rd α β ht
  have hu : IsHalf p.e ((N₀ * N₀) • t) := (GlobalTheory.PlaceModel.isHalf_iff S T).2
    ((GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) _)
  have hui : ∀ i j, toEAf D (((N₀ * N₀) • t) i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have h1 : ((N₀ * N₀) • t) i j = p.sec (((N₀ * N₀ : ℕ) : k) * (β.b * rd α β t * α.b') i j) := by
      rw [← nsmul_eq_mul, map_nsmul, ← GlobalTheory.FinPl.HalfInd.wr_apply, htw]
      rfl
    rw [h1]
    exact GlobalTheory.PlaceCoord.toEAf_mem ((p.int_iff _).1 (hent i j))
  have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) hu) hui
  have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h1).1
  have hh : K • (N₀ * N₀) • t ∈ GlobalTheory.PlaceModel.half S T p.e :=
    (GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) _
  rw [(GlobalTheory.PlaceModel.mem_half S T).1 hh] at h2
  rwa [mul_nsmul']

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoordsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_mem_homLattice_of_integral_frameCoords : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int | exact GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int | (intros; apply GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatrices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LinkKapMx

theorem mxAt_linkKappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (w : WO S L'), MxAt P w → MxAt P (l.κ S w) := by
  intro D ρ B L' ζ' l S P w hw
  exact GlobalTheory.LastOpPf.mxAt_kap _ S hw

end GlobalTheory.LinkKapMx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLink_kappa_preserves_supported_matrices : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (w : WO S L'), MxAt P w → MxAt P (l.κ S w) := by
  first | exact @GlobalTheory.LinkKapMx.mxAt_linkKappa | exact GlobalTheory.LinkKapMx.mxAt_linkKappa | (intros; apply GlobalTheory.LinkKapMx.mxAt_linkKappa <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealType
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealType
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ChainFr

namespace GlobalTheory.Corev.LiftUp

theorem liftUp_mult : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → IsWeilExp ψ V W (expS D k) (expT D k) ω → IsVacVec ψ θ M M' f → ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∃ T : PolF D W.rank V.rank → SmT M → SmT M', (∀ P v, T P v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v})) ∧ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = T P v} ∧ LiftsM θ M M' ν 𝓕 (fun P h g => conj (thetaKO ω g h (ptOf ψ θ M M' f P))) T := by
  intro hDS hHC hCD hCW D k V W S S' M M' θ ψ ω f hS hS' hθ hch hω hf ν 𝓕 hν h𝓕
  subst hS hS'
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hIn : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X hIn (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X hIn (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X hIn)))
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hadj : AdjLaw ψ V W := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hstd V W
  have h0 : adjO V W 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χS χT ω hW
  obtain ⟨j, -, hj⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D ψ θ hstd hθ V W (Fr.ofModel M) (Fr.ofModel M')
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hf)
  have hω'e : IsWeilExp ψ W V (expT D k) (expS D k) ω' :=
    ⟨χT, χS, hW', fun τ => ⟨(hexp τ).2, (hexp τ).1⟩⟩
  have hne : dag V W f ≠ 0 := by
    intro hz
    apply hf.ne
    funext x
    have hx := congrFun hz (adjO W V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec ψ θ M' M (dag V W f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := GlobalTheory.T.exists_realThetaIntertwiner_exchangedPair hDS hHC D k V W _ _ M M' θ ψ rfl rfl hθ hch
  have hItW := hIt ω' (dag V W f) hω'e hf'
  have hrule : ∀ τ, RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) :=
    fun τ => (GlobalTheory.T.firstOccurrenceRule_thetaChainStep_both_directions D X h3 h4 h5 k hch τ).2
  have hL := hPL _ _ _ _ hrule W V M' M θ ψ hθ ω' hω'e (dag V W f) It hf' hItW ν 𝓕 hν h𝓕 (dag V W f)
    (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v => GlobalTheory.T.real_intertwiner_values_kFinite D W V _ _ M' M θ ψ _ _ ω' (dag V W f) It hθ hω'e hf' hItW (j P) v,
    ?_, ?_⟩
  · refine (GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values hDS hHC D W V _ _ M' M θ ψ _ _ ω' (dag V W f) It hθ hω'e hf' hItW).trans
      (Submodule.span_mono ?_)
    rintro w ⟨P, v, hv, rfl⟩
    exact ⟨j.symm P, v, hv, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf ψ θ M M' f P)) =
        thetaKO ω' h g (ptOf ψ θ M' M (dag V W f) (j P)) := by
      intro g
      have e1 : ptOf ψ θ M' M (dag V W f) (j P) = dag V W (ptOf ψ θ M M' f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.Corev.LiftUp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → IsWeilExp ψ V W (expS D k) (expT D k) ω → IsVacVec ψ θ M M' f → ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∃ T : PolF D W.rank V.rank → SmT M → SmT M', (∀ P v, T P v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v})) ∧ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = T P v} ∧ LiftsM θ M M' ν 𝓕 (fun P h g => conj (thetaKO ω g h (ptOf ψ θ M M' f P))) T := by
  first | exact @GlobalTheory.Corev.LiftUp.liftUp_mult | exact GlobalTheory.Corev.LiftUp.liftUp_mult | (intros; apply GlobalTheory.Corev.LiftUp.liftUp_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsThetaIntegralLeSobolevSeminorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsThetaIntegralLeSobolevSeminorm
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem tendsto_enorm_of_le {v : ℕ → ℂ} {a : ℂ} {s : ℕ → ℝ≥0∞} (C : ℝ≥0) (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (h : ∀ j, ‖v j - a‖ₑ ≤ C * s j) : Filter.Tendsto (fun j => ‖v j‖ₑ) Filter.atTop (nhds ‖a‖ₑ) := by
  have h1 : Filter.Tendsto (fun j => (C : ℝ≥0∞) * s j) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hs (Or.inr ENNReal.coe_ne_top)
  have h2 : Filter.Tendsto (fun j => edist (v j) a) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      (fun j => by simpa [edist_eq_enorm_sub] using h j)
  exact (continuous_enorm.tendsto a).comp (tendsto_iff_edist_tendsto_0.2 h2)

theorem sobBdd_absThetaInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hc m _ Z hadd hsm hZ hcomm hint U hU K hK
  obtain ⟨U', hU', hl, hb⟩ := GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc (K ×ˢ {1})
    (hK.prod isCompact_singleton) U hU
  have pt : ∀ h : GA D T, ∃ (d : ℕ) (C : ℝ≥0), ∀ g ∈ GlobalTheory.Size.thetaLevel ψ S T U',
      ‖thetaKO om 1 h (Z g)‖ₑ ≤ C * sobO ψ θ μ 𝓕 d g := by
    intro h
    obtain ⟨U₁, hU₁, hl₁, hb₁⟩ := hZ U' hU'
    obtain ⟨U₂, hU₂, hl₂, hb₂⟩ := GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc {(1, h)}
      isCompact_singleton U₁ hU₁
    obtain ⟨d₃, C₃, hb₃⟩ := GlobalTheory.T.exists_sobolev_bound_theta_pointwise D ψ hom.std θ hθ S T μ 𝓕 hc U₂ hU₂
    obtain ⟨d₂, C₂, hb₂⟩ := hb₂ d₃
    obtain ⟨d₁, C₁, hb₁⟩ := hb₁ d₂
    refine ⟨d₁, C₃ * (C₂ * C₁), fun g hg => ?_⟩
    refine (hb₃ _ (hl₂ _ (hl₁ g hg) _ rfl) 0).trans ?_
    rw [ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc, mul_assoc]
    gcongr
    refine (hb₂ _ (hl₁ g hg) _ rfl).trans ?_
    gcongr
    exact hb₁ g hg
  obtain ⟨d, C, hN⟩ := GlobalTheory.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev D ψ hom.std θ hθ S T μ 𝓕 hc U' hU'
    (fun f => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om 1 h (Z f)) q‖ₑ ∂autMeasure T m)
    (fun f hf g hg => by
      rw [← lintegral_add_left' (hint f hf.1).1.enorm]
      refine lintegral_mono fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hadd f g hf.1 hg.1, map_add (f := _), Pi.add_apply]
      exact enorm_add_le _ _)
    (fun c f hf => by
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hsm c f hf.1, map_smul, Pi.smul_apply, enorm_smul])
    (fun f hf => (hint f hf.1).2.ne)
    (fun u hu f hf ht => by
      refine le_trans (lintegral_mono fun q => ?_) (lintegral_liminf_le' fun j => (hint _ (hu j).1).1.enorm)
      obtain ⟨d, C, hp⟩ := pt (Quotient.out q)
      refine (tendsto_enorm_of_le C (ht d) fun j => ?_).liminf_eq.ge
      refine le_of_eq_of_le ?_ (hp _ (sub_mem (hu j) hf))
      have e : u j - f = u j + (-1 : ℂ) • f := by rw [neg_one_smul, sub_eq_add_neg]
      have hf' : (-1 : ℂ) • f ∈ GlobalTheory.Size.thetaLevel ψ S T U' := Submodule.smul_mem _ _ hf
      rw [e, hadd _ _ (hu j).1 hf'.1, hsm _ _ hf.1]
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add (f := _), Pi.add_apply, neg_one_smul,
        sub_eq_add_neg, map_neg, Pi.neg_apply])
  obtain ⟨d', C', hb⟩ := hb d
  refine ⟨d', C * C', fun f hf x hx => ?_⟩
  have hx' : ((x, 1) : GA D S × GA D T) ∈ K ×ˢ {1} := ⟨hx, rfl⟩
  refine le_of_eq_of_le ?_ ((hN _ (hl f hf _ hx')).trans ?_)
  · refine lintegral_congr fun q => ?_
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]
    rw [← hcomm f hf.1 x, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  · rw [ENNReal.coe_mul, mul_assoc]
    gcongr
    exact hb f hf _ hx'

end GlobalTheory.ThetaDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsThetaIntegralLeSobolevSeminormStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absThetaIntegral_le_sobolevSeminorm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m := by
  first | exact @GlobalTheory.ThetaDens.sobBdd_absThetaInt | exact GlobalTheory.ThetaDens.sobBdd_absThetaInt | (intros; apply GlobalTheory.ThetaDens.sobBdd_absThetaInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorPairForm
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7}

theorem inner_sp {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E) (m : Dc.Mem)
    (c : Fin (Dc.a m) → ℂ) :
    ⟪sEE e, Sp.Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m).op (ramCrd (bR m) c)⟫_ℂ := by
  subst hSp
  obtain rfl := eq_of_heq h
  exact inner_spOf s Dc hK Gd wdD pw bR m _ c

theorem inner_join {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Z : Type}
    {sd : Z → DefSide Bs} (Dcf : ∀ z, DefCols (sd z)) (Spf : ∀ z, SPer (Dcf z)) (z0 z1 : Z) (hz : z0 = z1)
    (Dc : DefCols (sd z1)) (hdc : Dcf z1 = Dc) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hsp : HEq (Spf z1) (spOf s Dc hK Gd wdD pw bR))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] (Spf z0).HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E)
    (m : (Dcf z0).Mem) (m' : Dc.Mem) (hm : HEq m m') (c : Fin ((Dcf z0).a m) → ℂ) (c' : Fin (Dc.a m') → ℂ)
    (hc : HEq c c') :
    ⟪sEE e, (Spf z0).Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m').op (ramCrd (bR m') c')⟫_ℂ := by
  subst hz
  subst hdc
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hc
  exact inner_sp s (Dcf z0) hK Gd wdD pw bR (Spf z0) (eq_of_heq hsp) sEE sEEc h e m c

theorem iota_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) (x : I.GA) :
    ι.symm x = ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x := by
  subst h
  obtain rfl := eq_of_heq hι
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem op_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) (y : (D.mem u).A.Mu0)
    (T : Cu X u hK) (hT : Formalism.L2.SG.ColDict.colDictL X p.Tr hK T = (y : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    ((p.op y : HHX X) : L2X X) = PuFun X u hK p.Dt T := by
  have hd : (Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  show ((Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin
    ((Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y) : HHX X) : L2X X) = _
  rw [hd]
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

theorem exists_eval {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St}
    {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c)
    (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∀ T : E, ∃ F : L2X St,
      ((F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t (PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ v₀))) ∧
      star F ∈ HHX St ∧ ((sEEofTT M μ 𝓕 E St Gd ι t c T : HHX St) : L2X St) = star F := by
  refine ⟨hE.choose, hE.choose_spec.1, fun T => ⟨(hE.choose_spec.2.choose T : EEC St Gd), ?_, ?_, ?_⟩⟩
  · refine (hE.choose_spec.2.choose_spec T).1.trans (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ι.symm x = (iotaX St h).symm x := iota_symm_eq h ι hι x
    show (T : MMap M) hE.choose (ι.symm x * t) =
      PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ hE.choose) ((iotaX St h).symm x * t)
    rw [h1]
    exact (congrFun (PiTensorProduct.lift.tprod (φ := (T : MMap M)) hE.choose) _).symm
  · exact ((mem_EEC St Gd _).1 (hE.choose_spec.2.choose T).2).1
  · unfold sEEofTT
    simp only [dif_pos hE]
    rfl

theorem inner_smul_star {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (f g : GA D (D.sp.Y 0) → ℂ) (l a : ℂ) (hfg : f = l • g) (F φ P : L2X St)
    (hF : (F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t f) (hφ : (φ : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t g)
    (y z : HHX St) (hy : (y : L2X St) = star F) (hz : (z : L2X St) = P) :
    ⟪a • y, z⟫_ℂ = starRingEnd ℂ a * l * ⟪star φ, P⟫_ℂ := by
  have h1 : F = l • φ := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hF, hφ, MeasureTheory.Lp.coeFn_smul l φ] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, hfg]
    rfl
  have h2 : star (l • φ) = starRingEnd ℂ l • star φ := (Formalism.L2.SG.RowDict.conjL (muX St)).map_smulₛₗ l φ
  rw [inner_smul_left, Submodule.coe_inner, hy, hz, h1, h2, inner_smul_left, starRingEnd_self_apply, mul_assoc]

end GlobalTheory.MiTop.PairingL2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharIntegrable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.PlaceModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocReduction

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S0 T0 : HSp D} {m n : ℕ}

theorem isHalf_smul {e : AE D} {u : Mx D m n} : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem heis_add {x y : WO S T} (h : symplO S T x y = 0) (f : WO S T → ℂ) :
    heisO ψ S T (x + y) f = heisO ψ S T x (heisO ψ S T y f) := by
  have := heisL_heisL S T ψ x y f
  rw [symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  exact this.symm

theorem heis_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := heisL_comm S T ψ x y f

theorem heis_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f :=
  (heisL S T ψ x).map_smul c f

section Model

variable {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}

theorem fix_half (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf e u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.trans _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  rw [halfInd_eq_ind]
  exact ind_add _ t (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hu'⟩)

theorem fix_conj (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf (cA D e) u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  unfold halfInd
  split_ifs with h
  · rw [hLL' t h.1 h.2 u hu hu', mul_one]
  · rw [mul_zero]

end Model

section Periodic

open GlobalTheory.MixModel

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}

end Periodic

section Red

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x) (hcont : Continuous jA)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)

end Red

section Main

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {e : AE D} {Λ : AddSubgroup (WO S T)}
  {Λ0 : AddSubgroup (WO S0 T0)}
  (sA : ∀ (c : AE D) a, jA (c • a) = c • jA a) (sB : ∀ (c : AE D) b, jB (c • b) = c • jB b)
  (s0 : ∀ (c : AE D) z, j0 (c • z) = c • j0 z)
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hBB : ∀ b b', symplO S T (jB b) (jB b') = 0)
  (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0) (hB0 : ∀ b z, symplO S T (jB b) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hdec : ∀ x : WO S T, ∃ a b z, x = jA a + jB b + j0 z)
  (hhalf : ∀ (c : AE D) a b z, IsHalf c (jA a + jB b + j0 z) → IsHalf c a ∧ IsHalf c b ∧ IsHalf c z)
  (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
  (hX : ∀ x, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
  (hY : ∀ y, IsHalf (cA D e) y → (∀ x ∈ Λ, IsHalf e x → ψ (symplO S T x y) = 1) → y ∈ Λ)
  (hsp : ∀ a b z, IsHalf e a → IsHalf e b → IsHalf e z →
    (jA a + jB b + j0 z ∈ Λ ↔ jA a ∈ Λ ∧ jB b ∈ Λ ∧ j0 z ∈ Λ))
  (hsp0 : ∀ z, IsHalf e z → (j0 z ∈ Λ ↔ z ∈ Λ0))

variable {μw : Measure (Mx D m n)} (hψ : IsStdChar D ψ (-1)) (hcont : Continuous jA)
  (hcl : IsClosed {x : WO S T | x ∈ Λ ∧ IsHalf e x})
  (hw0 : μw {a | ¬ IsHalf e a} = 0) (hw1 : ∀ a₀ : Mx D m n, IsHalf e a₀ → Measure.map (fun a => a + a₀) μw = μw)
  (hw2 : μw {a | IsHalf e a ∧ jA a ∈ Λ} = 1)

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)
  (hec : e * cA D e = 0) (hinf : infPart D e = 0)
  {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hf₀ : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)

end Main

section Lattice

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {e : AE D}


open GlobalTheory.PlaceDatum in
theorem lattice_facts (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hinf : infPart D e = 0) :
    (∀ u ∈ latO S T ΛS ΛT fun _ => True, IsHalf e u → ∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y →
      ψ (symplO S T u y) = 1) ∧
    (∀ x, IsHalf e x → (∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) →
      x ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ y, IsHalf (cA D e) y → (∀ x ∈ latO S T ΛS ΛT fun _ => True, IsHalf e x → ψ (symplO S T x y) = 1) →
      y ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∃ r ∈ R, ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u) ∧
    ∀ y, IsHalf (cA D e) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ latO S T ΛS ΛT fun _ => True := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  refine ⟨fun u hu hu' y hy _ => (hdual u (infPart_of_half hinf hu')).1 hu y hy, fun x hx h => ?_, fun y hy h => ?_,
    fun k hk => ?_, fun y hy => exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) hy)⟩
  · refine (hdual x (infPart_of_half hinf hx)).2 fun u hu => ?_
    have := h _ (hsm _ he' u hu).1 ((isHalf_iff S T).2 (hsm _ he' u hu).2)
    rwa [← symplO_smul, isHalf_smul.1 hx] at this
  · refine (hdual y (infPart_of_half (infPart_cA hinf) hy)).2 fun u hu => ?_
    have := h _ (hsm _ he u hu).1 ((isHalf_iff S T).2 (hsm _ he u hu).2)
    rw [symplO_smul, isHalf_smul.1 hy] at this
    rw [symplO_skew, ← one_mul (ψ _), ← this, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, this]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

end Lattice

end GlobalTheory.LocReduction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfRealQuotHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.MixSumBound

theorem ofReal_quotHeight_pow {D : D7} (T : HSp D) (A : ℕ) (h : GA D T) :
    ENNReal.ofReal (quotHeight T h ^ A) = ⨅ γ : GQ T, ENNReal.ofReal (height T (γ * h) ^ A) := by
  set φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (max t 1 ^ A) with hφ
  have hmono : Monotone φ := fun a b hab =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans (le_max_right _ _)) (max_le_max hab le_rfl) A)
  have hcont : Continuous φ := ENNReal.continuous_ofReal.comp ((continuous_id.max continuous_const).pow A)
  have hbdd : BddBelow (Set.range fun γ : GQ T => height T (γ * h)) :=
    ⟨1, by rintro _ ⟨γ, rfl⟩; exact one_le_height T _⟩
  have e := Monotone.map_ciInf_of_continuousAt hcont.continuousAt hmono hbdd
  have e1 : φ (quotHeight T h) = ENNReal.ofReal (quotHeight T h ^ A) := by
    simp only [hφ, max_eq_left (one_le_quotHeight T h)]
  have e2 : ∀ γ : GQ T, φ (height T (γ * h)) = ENNReal.ofReal (height T (γ * h) ^ A) := fun γ => by
    simp only [hφ, max_eq_left (one_le_height T _)]
  rw [← e1, quotHeight, e]
  exact iInf_congr e2

end GlobalTheory.MixSumBound
end
end
