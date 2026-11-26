module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CcExCore

open GlobalTheory.ClsVal.Cmp

theorem exists_ccIs_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hC i A.μ0 hO.lift.std
  have hM := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs0
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) O.s0 := by
    rw [hs0, chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) O.s0 = W),
      MuVal W (T.chiW ((i : ℕ) + 1) O.s0) (castDict hV (T.mu ((i : ℕ) + 1) O.s0)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) O.s0) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) O.s0) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ
    exact ⟨hT.laws.muVal _ (inR i) _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ O.hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (O.dict 1).1
  exact GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair hci hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt _ hσ (hT.laws.unf _ (inR i) _ hσ) hr1
    hT.laws.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1) (fun k => (hM k).2.2.1)
    (hC.thP.vP i A.μ0).1 _

end GlobalTheory.AdTh.CcExCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCoreStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameConstants_of_characterisationCore : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  first | exact @GlobalTheory.AdTh.CcExCore.exists_ccIs_core | exact GlobalTheory.AdTh.CcExCore.exists_ccIs_core | (intros; apply GlobalTheory.AdTh.CcExCore.exists_ccIs_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO t x
  have hj := inR i
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨-, -, -, -, hr, -, hr1, -, -, -, hDom, -, hLast⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i _ rfl
    (T.dict ((i : ℕ) + 1) T.toCore.σ₀ 1).1
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ hj _ hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨hxi, n, hn, hxn⟩ := GlobalTheory.ClassSumRule.xi_laws hR.lev (hO.tuple t).xi
  obtain ⟨hd, hA, -⟩ := hO.cov t
  have hpq := hr ▸ hr1
  have hN : 0 < m * n := Nat.mul_pos hm hn
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  have hxN : ∀ h : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) ^ (m * n) = 1 := fun h => by
    rw [mul_comm, pow_mul, hxn, one_pow]
  obtain ⟨_, _, _, hfam⟩ := hR.fam.tie
  obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.ClassSumRule.exists_char hR.lev (O.dδ t) hd hι (hr.symm.trans (rank_Wc i).symm) hpq
    (hO.tuple t).half (fun P hP z => by
      obtain ⟨a, ha⟩ := GlobalTheory.RationalValues.xiR_mem R hR.lev hR.fam.pl_onto hR.fam.muVal hfam.ok i (tup t) P hP z
      rw [← ha, ← hO.lift.field]
      exact (O.jL a).2) (hO.tuple t).xi (hO.tuple t).phi
  obtain ⟨f, hf, hcls, -⟩ := GlobalTheory.ClsVal.exists_cusp_isThClsD_unique hci _ _ _ _ _ O.c' _ (O.dδ t) _
    (unfBC O.hle (T.U ((i : ℕ) + 1))) hr1
    (fun σ hσ => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.laws.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ))
    hT.laws.pins.2.1.2 (fun _ => hO.cov t)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ _ _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN _ _ c0 hcN (hv t))
    ψ (GlobalTheory.ClassSumRule.psiTie_of_values _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN hxi _ _ c0 hcN (hv t) ψ hψ)
    _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) hDom hLast
    (fun k => hw _ (hO.w t k)) (hO.reps t).1 (by
      obtain ⟨-, _, h⟩ := hO.io
      exact h.2.2.1.le) x
  exact ⟨f, hf, hcls⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedDataStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_classSum_normalisedData : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f := by
  first | exact @GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core | exact GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core | (intros; apply GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

variable {D : D7}

def toE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp
    (GlobalTheory.BotFormula.toAfE D).toRingHom

def matE {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (EAf D) :=
  ((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (toE D)

def IsIntE {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) : Prop := ∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)

def Approx (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) (z : Matrix (Fin d) (Fin a) D.host.E) : Prop :=
  ∀ i j, (z.map (inc D) - (unitBlock D o a d).map (inc D) *
    (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ hatId D 𝔪

def GoodMod (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e SS ∧ (∀ w ∈ SS, 0 < c w) ∧
    𝔪 = ∏ w ∈ SS, w.asIdeal ^ c w ∧ IsCoprime 𝔪 D.host.𝔟

def KillsCong (ν : (AE D)ˣ →* Circle) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ x y, IsFinIdl x y → IntU D y → (y : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → ν x = 1

def cosInd (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (z : Matrix (Fin d) (Fin a) D.host.E) (t : WO S T) : ℂ :=
  if IsHalf e t ∧ ∀ i j, InId 𝔪 (toEAf D (t i j) - toEAf D e * eToEAf D (z (Fin.cast hT i) (Fin.cast hS j))) then 1 else 0

def cosV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (G : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z)
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) G)

theorem cosV_smul (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (c : ℂ)
    (G : VC D a d → ℂ) : cosV δ 𝔪 z (c • G) = c • cosV δ 𝔪 z G := by
  have hU : ∀ (x : VC D a d) (F : VC D a d → ℂ),
      Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x (c • F) = c • Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x F := fun x F => by
    funext y
    simp only [Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hI : ∀ A B : AddSubgroup (VC D a d), Iop D (tor0 D ⊤ δ) A B (c • G) = c • Iop D (tor0 D ⊤ δ) A B G := fun A B => by
    funext y
    simp only [Iop, hU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [← mul_finsum, mul_left_comm]
  funext y
  simp only [cosV, Wd, hI, hU, Pi.smul_apply, smul_eq_mul]
  ring

theorem GoodMod.ne_bot {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : 𝔪 ≠ ⊥ := by
  obtain ⟨SS, c, -, -, rfl, -⟩ := h
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_approx {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) {a : ℕ} (d : ℕ) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) : ∃ z : Matrix (Fin d) (Fin a) D.host.E, IsIntE z ∧ Approx 𝔪 o k z := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hI : ∀ i j, ((unitBlock D o a d).map (inc D) *
      (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ OhE D := by
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => mul_mem ?_ (((GlobalTheory.NormSum.mem_intG k).1 hk) l j).2
    by_cases h : i.1 = o + l.1
    · simp [unitBlock, h]
    · simp [unitBlock, h]
  choose b w hw hb using fun i j => GlobalTheory.CongApprox.exists_int_approx D _ hn _ (hI i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, rfl⟩, fun i j => ?_⟩
  rw [Matrix.sub_apply, hb i j]
  have e : (Matrix.of fun i j => (b i j : D.host.E)).map (inc D) i j -
      (inc D (b i j : D.host.E) + (Ideal.absNorm 𝔪 : Formalism.MainNotions.StandardLatticesGL3.AE D) * w i j) =
      inc D (((Ideal.absNorm 𝔪 : 𝓞 D.host.E)) : D.host.E) * (-w i j) := by
    simp
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, _, neg_mem (hw i j), rfl⟩

end GlobalTheory.StdRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChrLocal

open scoped TensorProduct
open GlobalTheory.AdelicU

theorem map_eq_zero_of_at {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {B : Type} [CommRing B]
    [Algebra F B] {v : Pl (F := F)} {x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hx : At (evFin F v) x) {a : AF F}
    (ha : evFin F v a = 0) (f : AF F →ₐ[F] B) (hf : f a = 1) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x = 0 := by
  have h := hx a ha
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply] at h
  have h2 := congrArg (Algebra.TensorProduct.map f (AlgHom.id F E)) h
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_zero] at h2
  simpa [hf, ← Algebra.TensorProduct.one_def] using h2

theorem eq_locIdele_splitPrime {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ)
    (hz : At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) (h1 : piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1) :
    z = GlobalTheory.LFun.locIdele F (splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (splitPrime_under τ)).toMonoidHom (Units.map (piW τ).toMonoidHom z)) := by
  refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun u => ?_)
  · have h := map_eq_zero_of_at hz (a := ((1 : Ainf F), (0 : Af F))) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0 = 0
      exact map_zero _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) rfl
    change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · by_cases hu : u.under (𝓞 F) = v
    · rw [GlobalTheory.LFun.finAdEquiv_apply hu]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = compFin F E v (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      rw [e]
      obtain ⟨τ', rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hu
      rw [GlobalTheory.LFun.SplitTie.toCompl_eq_complMap τ' hu]
      change _ = Neutral.B1.finiteSingle E (splitPrime τ) _ (splitPrime τ')
      rcases eq_or_eq_comp_conj hσ τ τ' with rfl | rfl
      · rw [GlobalTheory.LFun.finSingle_self]
        rfl
      · rw [GlobalTheory.LFun.finSingle_ne (splitPrime_comp_ne hσ τ)]
        change GlobalTheory.LFun.complMap hu (piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1
        rw [h1, map_one]
    · rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = compFin F E (u.under (𝓞 F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      have h := map_eq_zero_of_at hz (a := GlobalTheory.LatVac.liftV (u.under (𝓞 F)) 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin (u.under (𝓞 F)) 1) = 0
        exact evalV_singleFin_ne (Ne.symm hu) 1) (evFin F (u.under (𝓞 F))) (GlobalTheory.LatVac.evFin_liftV _ 1)
      rw [map_sub, map_one, sub_eq_zero] at h
      have h' : compFin F E (u.under (𝓞 F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := h
      rw [e, h', map_one]
      change (1 : u.adicCompletion E) = Neutral.B1.finiteSingle E (splitPrime τ) _ u
      exact (GlobalTheory.LFun.finSingle_ne (fun e => hu (by rw [e]; exact splitPrime_under τ)) _).symm

theorem chrW_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ), At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) →
    piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  intro F E _ _ _ _ _ σ hσ χ v τ z hz h1
  change Circle.toUnits (χ (GlobalTheory.LFun.locIdele F (splitPrime τ) _)) = _
  rw [← eq_locIdele_splitPrime hσ τ z hz h1]

end GlobalTheory.ChrLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnitStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_norm_one_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ), At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) →
    piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  first | exact @GlobalTheory.ChrLocal.chrW_piW_eq | exact GlobalTheory.ChrLocal.chrW_piW_eq | (intros; apply GlobalTheory.ChrLocal.chrW_piW_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchLocalAct

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def liftI (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

end GlobalTheory.ArchLocalAct

end

namespace GlobalTheory.ArchLocalAct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul' (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem comm_offI {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hw : M.IsWeil ψ χX χW om) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evI F)) (hx2 : x.2 ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := _root_.GlobalTheory.ArchFactor.comm_offI (n := n) (d := d) (X := X) (W := W) (M := M) (ψ := ψ) (χX := χX) (χW := χW) (om := om) hw x hx1 hx2 u hu p q Φ hΦ

theorem schr_trans' (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (w : κ → AF F) (Φ : (κ → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

end GlobalTheory.ArchLocalAct

namespace GlobalTheory.ArchLocalAct

theorem exists_op_of_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hψ : IsStd ψ) (hw : M.IsWeil ψ χX χW om) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evI F)) (hx2 : x.2 ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      Acts (evI F) (om x) (⇑f) (⇑(T f)) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_offI hw x hx1 hx2
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d),
      ∀ t, g t = (R 0)⁻¹ * om x (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := GlobalTheory.ArchSlice.exists_schwartz_slice _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om x with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hψ hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring

theorem exists_op_of_KInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∃ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) (⇑f) (⇑(A f)) := by
  intro F E _ _ _ _ _ σ B n d Y W M om χ₁ χ₂ hB _ hw k hk
  have h1 : (1 : UA σ Y.J) ∈ UAt σ Y (evI F) := by
    intro u _
    simp [mat]
  exact exists_op_of_UAt hB.std hw (1, k) h1 hk.1

end GlobalTheory.ArchLocalAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archOperator_compact_unitaryW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∃ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) (⇑f) (⇑(A f)) := by
  first | exact @GlobalTheory.ArchLocalAct.exists_op_of_KInf | exact GlobalTheory.ArchLocalAct.exists_op_of_KInf | (intros; apply GlobalTheory.ArchLocalAct.exists_op_of_KInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRank
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.PolRank

open Module

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := Basis.piTensorProduct (fun _ : InfinitePlace F =>
    (MvPolynomial.basisMonomials _ ℂ : Basis _ ℂ (Formalism.BasicNotions.TH.Pol P Q R S)))
  have hb := b.mk_eq_rank
  rw [Cardinal.lift_id, Cardinal.lift_id] at hb
  rw [← hb]
  exact Cardinal.mk_le_aleph0

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

end GlobalTheory.ThK.PolRank

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem exists_rest_tens_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)),
    ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  intro F _ _ κ _ v φ hφ hne
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  refine ⟨R, hR φ hφ, fun h => ?_⟩
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (x i)) :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have h1 := (hR φ hφ).1 0 _ hz
  rw [zero_add] at h1
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (x i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1, Pi.zero_apply] at e
  exact mul_ne_zero hx hR0 e

end GlobalTheory.InertSph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)), ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  first | exact @GlobalTheory.InertSph.exists_rest_tens_ne_zero | exact GlobalTheory.InertSph.exists_rest_tens_ne_zero | (intros; apply GlobalTheory.InertSph.exists_rest_tens_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuous
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ThK.ModelLocInt

open scoped Classical
open Filter GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem incM_one (m : ℕ) : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem heis_loc {B : Base F E} {M M₁ : Model σ X W} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e : Fn F n d →ₗ[ℂ] Fn F n d} (he : IsEv B M M₁ 1 1 ∅ e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB _)
    (φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₁ : φ₁ ∈ SB _) (hA : Acts (evFin F v) (M.co.rho B.ψ z) φ φ₁)
    (χ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hA₁ : Acts (evFin F v) (M₁.co.rho B.ψ z) (ev v φ) χ₁) :
    ev v φ₁ = χ₁ := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
  rw [incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h1
  rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
  have hevφ : ev v φ ∈ SB _ := by
    rw [← (hvm v).2]
    exact Submodule.mem_map_of_mem hφ
  rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
  exact canc _ _ h1

def ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k))

theorem at_ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    At (evFin F v) (ptAt M v w) := by
  intro a ha
  unfold ptAt
  rw [← LinearEquiv.map_smul, ← M.co.e.symm.map_zero]
  congr 1
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · exact GlobalTheory.LatVac.at_liftV v _ a ha

theorem locCo_ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    GlobalTheory.LatVac.locCo M.co v (ptAt M v w) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp [ptAt, GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.ThK.ModelLocInt


open GlobalTheory.ThK.ModelLocInt in
theorem GlobalTheory.ThK.ModelLocInt.exists_loc_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl (F := F)) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e he ei ev hei hvm hloc v _
  obtain rfl : ‹Invertible (2 : Fv F v)› = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  have hψe : GlobalTheory.LatVac.psiAt B.ψ v = GlobalTheory.VacAny.psiV B.ψ v :=
    by
    ext t
    exact (GlobalTheory.LatVac.psiAt_apply B.ψ v t).trans (GlobalTheory.VacAny.psiV_eq_psiLoc B.ψ v t).symm
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := by
    rw [hψe]; exact GlobalTheory.VacAny.continuous_psiV hP.base.std.1 v
  refine ⟨GlobalTheory.LatVac.psiAt B.ψ v, hψc, by rw [hψe]; exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hP.base.std v,
    fun w => GlobalTheory.LatVac.locCo M₁.co v (ptAt M v w), fun w φ hφ => ?_⟩
  have hA := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v (ptAt M v w) (at_ptAt M v w) φ
  rw [locCo_ptAt] at hA
  have hA₁ := GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v (ptAt M v w) (at_ptAt M v w) (ev v φ)
  exact heis_loc hP.good hM₁ he ei ev hei hvm hloc v (ptAt M v w) φ hφ _
    (GlobalTheory.SchrSBFin.schr_mem_SB v _ hψc w φ hφ) hA _ hA₁
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuousStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_normalizing_schrodinger_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl (F := F)) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  first | exact @GlobalTheory.ThK.ModelLocInt.exists_loc_schr | exact GlobalTheory.ThK.ModelLocInt.exists_loc_schr | (intros; apply GlobalTheory.ThK.ModelLocInt.exists_loc_schr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformSchwartzCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformSchwartzCm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.ThetaTrContF

theorem continuous_thetaTrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc

end GlobalTheory.ThetaTrContF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformSchwartzCmStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaTransform_schwartz_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.ThetaTrContF.continuous_thetaTrF | exact GlobalTheory.ThetaTrContF.continuous_thetaTrF | (intros; apply GlobalTheory.ThetaTrContF.continuous_thetaTrF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGrids
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGrids
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SquareInfGap

theorem square_infExp_gap : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro _ i j
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := by
    show (G.V (.grid (i : ℕ) (j : ℕ))).rank % 2 = _
    rw [(node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).rank]
    rfl
  refine ⟨fun τ => -(D.hc τ).e ⟨j, j.2⟩ + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2),
    fun τ => (cen D 1 τ (D.R.m - i) : ℚ) + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2), fun t τ => ⟨?_, ?_, ?_⟩⟩
  · have h := GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, hε] at h
    exact h
  · have h := GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps] at h
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps, hε] at h
    exact h
  · have key := GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen (D := D) 1 τ i j i.2 j.2
    push_cast at key ⊢
    linarith

end GlobalTheory.SquareInfGap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGridsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
  first | exact @GlobalTheory.SquareInfGap.square_infExp_gap | exact GlobalTheory.SquareInfGap.square_infExp_gap | (intros; apply GlobalTheory.SquareInfGap.square_infExp_gap <;> assumption)
end
end
