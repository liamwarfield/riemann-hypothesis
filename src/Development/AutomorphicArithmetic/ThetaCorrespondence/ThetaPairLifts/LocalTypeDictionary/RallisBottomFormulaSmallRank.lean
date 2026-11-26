module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallStageBottomKernelEqTerm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
noncomputable section
namespace GlobalTheory.BotSmallDict
open GlobalTheory.BotFormula (IsFinPt)
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}
end GlobalTheory.BotSmallDict
namespace GlobalTheory.BotSmallDict
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}
end GlobalTheory.BotSmallDict
namespace GlobalTheory.BotSmallDict
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
  {A A' WW : HSp D} {X : Tri T A A' WW} {μ₀ : T} {δ t0 : ℂ} {s : T} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q}
theorem bottomKernel_eq_classSum_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₂ : ℂ, Ω₂ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ (x : GA D P'.a) (g' : GA D A'), GlobalTheory.BotFormula.IsFinPt A' g' x → ∀ T' : Tup D P'.a P'.d P'.n,
              X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' = Ω₂ * u * P'.term x h T' := by
  intro _ _ _ hI _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j A A' WW X δ t0 hX hβ
  have hc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', hB₀⟩ := hex
    have s1 : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have s3 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have hv := hX.is.isVac'
    rw [s1, s3] at hv
    obtain ⟨κ, hκ, hvac⟩ := vac_const (hI D) hc (setup hc hX P₀'.crv) P₀'.pt0 hX.std'.2.1 hX.stdW.2.1 hv
    refine ⟨(∏ τ, GlobalTheory.NormExact.period D δ 1 τ ^ (P₀'.a * P₀'.n τ)) * κ,
      mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (period_ne_zero P₀'.crv τ)) hκ, fun s Q P P' hB => ?_⟩
    have hS : A'.rank = P'.a := hX.rank'.trans hB.rank.2.1.symm
    have hT : WW.rank = P'.d := by rw [hB.rank.2.2.2, hB.rank.2.2.1, ← hX.rank, ← hX.rank', hX.is.rank]
    obtain ⟨ζ, hζ, r1⟩ := hvac hS hT P'.e0 P'.vac P'.W.nz
    obtain ⟨ζ', hζ', r2⟩ := reads_datum (hI D) hR hL hX hβ hB hS hT r1
    have hu := hζ.mul hζ'.isAlgUnit
    refine ⟨ζ * ζ', hu.1, hu.2.1, fun p _ _ lam => hu.2.2 p lam, fun ea ed h g hg x g' hg' T' => ?_⟩
    obtain ⟨-, e1, -, e2, -⟩ := GlobalTheory.BottomReal.bottom_real_eq G hL hB₀ hB
    rw [ker'_eq (hI D) hc hL hX hB ea ed (mul_ne_zero (mul_ne_zero hκ hζ.1) hζ'.ne_zero) r2 hg hg' T', e1, e2]
    ring
  · exact ⟨1, one_ne_zero, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩
end GlobalTheory.BotSmallDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallStage_bottomKernel_eq_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₂ : ℂ, Ω₂ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ (x : GA D P'.a) (g' : GA D A'), GlobalTheory.BotFormula.IsFinPt A' g' x → ∀ T' : Tup D P'.a P'.d P'.n,
              X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' = Ω₂ * u * P'.term x h T' := by
  first | exact @_root_.GlobalTheory.BotSmallDict.bottomKernel_eq_classSum_term | exact _root_.GlobalTheory.BotSmallDict.bottomKernel_eq_classSum_term | (intros; apply _root_.GlobalTheory.BotSmallDict.bottomKernel_eq_classSum_term <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumSmallStageEq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerMinorMulRealOfRealInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped Matrix
namespace GlobalTheory.BotRealInv
theorem ker_minor_mul_real_of_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q),
        IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (T' : Tup D P'.a P'.d P'.n)
          (h : GA D WW), ∀ k ∈ GinfC A', ∀ g : GA D A',
            X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h (g * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h g := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T L μ₀ hL G W _ i j A A' WW X δ t0 hX t Q P P' hB ea ed T' h g hg x => ?_⟩⟩
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW : IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
    hX.is.weil' t
  have hinf := GlobalTheory.BotWeights.hasInf_of_chars P' _ hB.chars'.2
  have hinf' : (nuH G t i j).HasInfQ (tauE D) fun τ => -((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2 := by
    refine ⟨fun τ => -(P'.W.ep' * P'.W.chV'.n τ), fun τ => by push_cast; ring, fun k => ?_⟩
    have h1 := hinf k
    rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, inv_eq_iff_eq_inv, ← Finset.prod_inv_distrib] at h1
    rw [h1]
    exact Finset.prod_congr rfl fun τ _ => (zpow_neg _ _).symm
  have hb : ∀ τ, HasInfExp D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) τ (-((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2) := by
    rw [succ_mul_succ_sub_one_div_succ]
    exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (chrEq_nu G t i j hL) hinf'
  have he₂ : ∀ τ, (((P'.n τ : ℕ) : ℤ) : ℚ) = -(-((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2 + (WW.rank : ℚ) / 2) := fun τ => by
    have h2 : ((2 * (P'.n τ : ℤ) : ℤ) : ℚ) = ((P'.W.ep' * P'.W.chV'.n τ - (P'.d : ℤ) : ℤ) : ℚ) := by rw [P'.wt τ]
    rw [← ed]
    push_cast at h2 ⊢
    linarith
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ hW.hecS hW.resS
  choose e₁ he₁ using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ A'.rank τ (a τ) hW.hecS hW.resS (ha τ)
  have hψ : Continuous W.ψ := hX.is.isVac.1.1.1
  have es : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
  have eB : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
  have esW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have eBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO 1 1) (X.f' t) := fun τ => by
    have h0 := hX.is.isVac'.2.fock τ
    rw [es, esW] at h0
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq (hX.is.snd t)
      hX.is.isVac'.2.theta hf h0
  have hBS : ∀ τ, ((fun _ => (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) τ)ᴴ * gramAt D A' τ * 1 = 1 := fun τ => by
    rw [GlobalTheory.RealColAct.gramAt_of_gram_one hV]; simp
  have hBT : ∀ τ, ((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)ᴴ * gramAt D WW τ * 1 = 1 := fun τ => by
    rw [GlobalTheory.RealColAct.gramAt_of_gram_one hVW]; simp
  have key := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ (fun _ => 1) (fun _ => 1) hBS hBT
    a _ ha hb e₁ (fun τ => (P'.n τ : ℤ)) he₁ he₂ (X.f' t) hf hv g hg 1 (one_mem _) (GlobalTheory.BotFormula.minorF ea ed T')
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
    at key
  have hc : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' g)).det ^ (P'.n τ : ℤ)) *
      ∏ τ, ((compAt W.θ τ (Formalism.L2.Theta.mt A' g))⁻¹).det ^ P'.n τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ g
    rw [Matrix.inv_eq_right_inv h1, zpow_natCast, ← mul_pow, ← Matrix.det_mul, h1, Matrix.det_one, one_pow]
  rw [substF_minorF, map_smul, smul_smul, hc, one_smul] at key
  unfold Tri.ker' thetaKO
  rw [es, eB, esW, eBW]
  have e : ((x * g, h) : Formalism.L2.Theta.GA D A' × Formalism.L2.Theta.GA D WW) = (x, h) * (g, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, key]
end GlobalTheory.BotRealInv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_kernel_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q),
        IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (T' : Tup D P'.a P'.d P'.n)
          (h : GA D WW), ∀ k ∈ GinfC A', ∀ g : GA D A',
            X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h (g * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h g := by
  first | exact @_root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant | exact _root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant | (intros; apply _root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFiniteLevelFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.BotFinLevel
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar _root_.Formalism.L2.DIV
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)
variable {D : D7}
end GlobalTheory.BotFinLevel
theorem GlobalTheory.BotFinLevel.bottom_finite_level_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX s k hk
  exact GlobalTheory.BotFinLevel.fix_of_unram hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ s i j _ hv) hk
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_layer_finite_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  first | exact @_root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | exact _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | (intros; apply _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotClassSumSmall
open scoped ComplexOrder
set_option maxHeartbeats 4000000 in
theorem classSum_smallStage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  intro hPr hK hM hI hB
  obtain ⟨c1, h1⟩ := _root_.GlobalTheory.T.bottom_layer_finite_level hPr hK hM hI hB
  obtain ⟨c2, h2⟩ := _root_.GlobalTheory.T.minor_kernel_real_invariant hPr hK hM hI hB
  refine ⟨max c1 c2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have h1 := h1 C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have h2 := h2 C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX
  obtain ⟨hJo, hJc⟩ := openCompact X hX.std'
  haveI : X.m'.IsHaarMeasure := hX.is.meas'.1
  have hJtop : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ 0 :=
    (hJo.measure_pos X.m' ⟨1, Subgroup.one_mem _⟩).ne'
  refine ⟨((X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))).toReal : ℂ),
    by exact_mod_cast (ENNReal.toReal_pos hJ0 hJtop).ne', fun s Q P P' hP ea ed h g hg gx hgx T' => ?_⟩
  obtain ⟨hu, hcard⟩ := GlobalTheory.T.standardLattice_doubleCosetClasses_stabilisers A' X.rA' hX.is.rigA' hX.std' ea gx hgx
  haveI : Finite (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := (GlobalTheory.NormSum.cls_finite_card_le D P'.a).1
  letI : Fintype (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := Fintype.ofFinite _
  have hfin : ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧
      (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))}.Finite := fun x => by
    have h1 := GlobalTheory.InnerClassSum.finite_stab_of_measure X.m' (GQ A') _ hX.is.meas'.2 hJ0 hJtop (gx x)
    have him : {γ : GA D A' | γ ∈ GQ A' ∧
        (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} =
        Subtype.val '' {γ : GQ A' | (gx x)⁻¹ * (γ : GA D A') * gx x ∈
          ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact h1.image _
  have hl := GlobalTheory.SqTower.Normal.ker'_left hX.is s (GlobalTheory.BotFormula.minorF ea ed T') g
  have hr : ∀ k ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')), ∀ x,
      X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (x * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g x := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    refine GlobalTheory.DefiniteClassSum.invariant_sup ?_ ?_
    · intro k hk x
      obtain ⟨hk1, -⟩ := Lev.mem_levA.1 hk
      have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' s) := hX.is.weil' s
      have hf' : IsThetaFunO W.ψ A' WW (X.f' s) :=
        GlobalTheory.GalLift.Vec.theta_of_thetaAt hX.is.isVac.1 hX.is.isVac.2.inf (hX.is.snd s) hX.is.isVac'.2.theta
      show X.ω' s (x * k, g) _ 0 = X.ω' s (x, g) _ 0
      have e : ((x * k, g) : GA D A' × GA D WW) = (x, g) * (k, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hX.is.isVac'.2.inf k hk1 1
        (GfC WW).one_mem _ _ _ _ _ _ hf', h1 W hψ i j A A' WW X hX s k hk]
    · intro k hk x
      exact h2 W hψ i j A A' WW X δ t0 hX s Q P P' hP ea ed T' g k hk x
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (GA D A') X.m' (GQ A') _ X.fd' hX.is.meas'.2 hJo hJtop
    _ gx hu hfin _ hl hr
  rw [Tri.I', heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]
end GlobalTheory.BotClassSumSmall
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_classSum_smallStage_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  first | exact @_root_.GlobalTheory.BotClassSumSmall.classSum_smallStage | exact _root_.GlobalTheory.BotClassSumSmall.classSum_smallStage | (intros; apply _root_.GlobalTheory.BotClassSumSmall.classSum_smallStage <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BotFormula.rallis_bottom_formula_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω' : ℂ, Ω' ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T', X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g = Ω' * u * P'.coord h T' := by
  intro hPr hK hM hI hB
  have hA := _root_.GlobalTheory.T.bottom_classSum_smallStage_eq hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := hA
  have hB' := _root_.GlobalTheory.T.smallStage_bottomKernel_eq_term hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := hB'
  refine ⟨max cA cB, fun ε CF hCF => ?_⟩
  obtain ⟨CA, xA, hA⟩ := hA ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max CA CB, max xA xB, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have hA := hA C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have hB' := hB' C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω₁, h1, HA⟩ := hA W hψ i j A A' WW X δ t0 hX
  obtain ⟨Ω₂, h2, HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  refine ⟨Ω₁ * Ω₂, mul_ne_zero h1 h2, fun s Q P P' hP => ?_⟩
  obtain ⟨u, hu, huQ, huU, HB⟩ := HB s Q P P' hP
  refine ⟨u, hu, huQ, huU, fun ea ed h g hg T' => ?_⟩
  have hgx : ∀ x : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a), ∃ g', GlobalTheory.BotFormula.IsFinPt A' g' x.out :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one A' hX.std'.1 x.out ea.symm
  choose gx hgx using hgx
  rw [HA s Q P P' hP ea ed h g hg gx hgx T', Pair.coord]
  have e : ∀ x : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ * X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) =
        (Ω₂ * u) * (((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ * P'.term x.out h T') := by
    intro x; rw [HB ea ed h g hg x.out (gx x) (hgx x) T']; ring
  simp_rw [e]
  rw [← mul_finsum]
  ring
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottom_formula_small : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω' : ℂ, Ω' ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T', X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g = Ω' * u * P'.coord h T' := by
  first | exact @_root_.GlobalTheory.BotFormula.rallis_bottom_formula_small_rank | exact _root_.GlobalTheory.BotFormula.rallis_bottom_formula_small_rank | (intros; apply _root_.GlobalTheory.BotFormula.rallis_bottom_formula_small_rank <;> assumption)
end
