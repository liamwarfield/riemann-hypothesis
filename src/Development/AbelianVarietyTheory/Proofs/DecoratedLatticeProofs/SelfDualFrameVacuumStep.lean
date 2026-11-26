module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelComb
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalves
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumHalves

variable {D : D7}

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  simp

theorem omegaG_of_empty {a b : ℕ} (L : LevDat D.host.E ℂ a) (hL : L.Pg = ∅) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaG L χj y = 1 := by
  have hn : ∀ PP, PP ∉ L.Pg := fun PP h => Finset.notMem_empty PP (hL ▸ h)
  haveI : IsEmpty ↥L.Pg := ⟨fun PP => hn PP.1 PP.2⟩
  have h1 : ∀ g : G0 L.Pg L.r, g = 1 := fun g => funext fun PP => isEmptyElim PP
  have h2 : ∀ g : L.P.H, L.P.chi g = 1 := fun g => by
    rw [show g = 1 from Subtype.ext (h1 _), map_one]
  unfold omegaG
  rw [dite_eq_left ⟨fun PP h => absurd h (hn PP), fun PP => isEmptyElim PP, fun PP => isEmptyElim PP, fun PP => isEmptyElim PP,
    by rw [h1 (fun PP => _)]; exact L.P.H.one_mem⟩, h2, Fintype.prod_empty, Fintype.prod_empty]
  simp

theorem omegaG_datY {n b : ℕ} (r t j : ℕ) (hr : r ≤ n) (Pg Q Q' : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin n) (kP PP)) :
    omegaG (datY n r t j hr Pg Q P χ ξ Frm.B) χj y = omegaG (datY n r t j hr Pg Q' P χ ξ' Frm.B) χj y := rfl

theorem isHalf_smul {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {S T : HSp D} (x : WO S T) :
    IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]


set_option maxHeartbeats 800000 in
theorem stepDatum_eq_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eG eQ : AE D), IsIdemSum eG Pg → IsIdemSum eQ Q → eG * eQ = 0 → ∀ x : WO S T, (if IsHalf (eG + eQ) x ∧ IsIntM (frMapO S T βS βT x) then omegaG (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q (datY S.rank r t j hr Pg Q P χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) = (if IsHalf eG (eG • x) ∧ IsIntM (frMapO S T βS βT (eG • x)) then omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eG • x))) * omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO S T βS βT (eG • x))) else 0) * (if IsHalf eQ (eQ • x) ∧ IsIntM (frMapO S T βS βT (eQ • x)) then omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eQ • x))) * omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT (eQ • x))) else 0) * (if IsHalf (eG + eQ) x then 1 else 0) := by
  intro D S T βS βT r t j hr Pg Q P χ χj ξ eG eQ hG hQ _ x
  obtain ⟨iG, rG⟩ := GlobalTheory.InnerSteps.resS_idemSum hG
  obtain ⟨iQ, rQ⟩ := GlobalTheory.InnerSteps.resS_idemSum hQ
  have hsm : ∀ e : AE D, frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x :=
    fun e => GlobalTheory.RedHalfDrop.frMapO_smul_eq βS βT e x
  have hhG : IsHalf eG (eG • x) := isHalf_smul hG x
  have hhQ : IsHalf eQ (eQ • x) := isHalf_smul hQ x
  by_cases hx : IsHalf (eG + eQ) x
  swap
  · rw [if_neg hx, if_neg (fun h => hx h.1), mul_zero]
  have hxx : (eG + eQ) • x = x := funext fun a => funext fun b => hx a b
  have hNs := hsm (eG + eQ)
  rw [hxx, RingHom.map_add (f := _), add_smul] at hNs
  rw [if_pos hx, hsm, hsm]
  generalize frMapO S T βS βT x = N at hNs ⊢
  by_cases hI : IsIntM N
  · have iGN : IsIntM (toEAf D eG • N) := fun a b => mul_mem iG (hI a b)
    have iQN : IsIntM (toEAf D eQ • N) := fun a b => mul_mem iQ (hI a b)
    have e1 := GlobalTheory.PlaceDatum.omegaG_congr (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj
      (fun PP => redM PP (toEAf D eG • N)) (fun PP => redM PP N)
      (fun PP hPP => GlobalTheory.LocSuppTw.redM_smul_of_res iG PP (rG PP hPP) hI)
    have e2 := GlobalTheory.PlaceDatum.omegaQ_congr Q r ξ 1 (fun PP => redM PP (toEAf D eQ • N)) (fun PP => redM PP N)
      (fun PP hPP => GlobalTheory.LocSuppTw.redM_smul_of_res iQ PP (rQ PP hPP) hI)
    rw [if_pos (And.intro hx hI), if_pos (And.intro hhG iGN), if_pos (And.intro hhQ iQN), omegaQ_empty,
      omegaG_of_empty (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) rfl, e1, mul_one, mul_one, one_mul,
      omegaG_datY r t j hr Pg Q ∅ P χ ξ (fun _ => 1)]
    exact congrArg _ e2.symm
  · rw [if_neg (fun h : IsHalf (eG + eQ) x ∧ IsIntM N => hI h.2)]
    by_cases h1 : IsIntM (toEAf D eG • N)
    · have h2 : ¬ IsIntM (toEAf D eQ • N) := fun h2 => hI fun a b => by
        have e : N a b = (toEAf D eG • N) a b + (toEAf D eQ • N) a b := congrFun (congrFun hNs a) b
        exact e.symm ▸ Subring.add_mem _ (h1 a b) (h2 a b)
      rw [if_neg (fun k : IsHalf eQ (eQ • x) ∧ IsIntM (toEAf D eQ • N) => h2 k.2), mul_zero, zero_mul]
    · rw [if_neg (fun k : IsHalf eG (eG • x) ∧ IsIntM (toEAf D eG • N) => h1 k.2), zero_mul, zero_mul]

end GlobalTheory.DatumHalves
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalvesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_eq_mul_halves : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eG eQ : AE D), IsIdemSum eG Pg → IsIdemSum eQ Q → eG * eQ = 0 → ∀ x : WO S T, (if IsHalf (eG + eQ) x ∧ IsIntM (frMapO S T βS βT x) then omegaG (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q (datY S.rank r t j hr Pg Q P χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) = (if IsHalf eG (eG • x) ∧ IsIntM (frMapO S T βS βT (eG • x)) then omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eG • x))) * omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO S T βS βT (eG • x))) else 0) * (if IsHalf eQ (eQ • x) ∧ IsIntM (frMapO S T βS βT (eQ • x)) then omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eQ • x))) * omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT (eQ • x))) else 0) * (if IsHalf (eG + eQ) x then 1 else 0) := by
  first | exact @GlobalTheory.DatumHalves.stepDatum_eq_mul | exact GlobalTheory.DatumHalves.stepDatum_eq_mul | (intros; apply GlobalTheory.DatumHalves.stepDatum_eq_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelComb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries

variable {D : D7}

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := fun V Λ hΛ => _root_.DedupShared.selfDual_isFullLattice V Λ hΛ



set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem stepVec_of_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ : WO S T → ℂ) (dG dQ : WO S T →₀ ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q → (∀ PP ∈ Pg, ∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) → (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dG → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dQ → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj ∅ (fun _ => 1) f₀ (comb ψ S T dG f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ (comb ψ S T dG f₀)) := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT r t j hr Pg Q P χ χj ξ f₀ dG dQ hS hT _ _ hdisj hunder hex hdG hdQ hG hQv
  obtain ⟨hvac, eG, heG, hthG⟩ := hG
  obtain ⟨-, eQ, heQ, hthQ⟩ := hQv
  obtain ⟨e, he⟩ := hex
  change IsIdemSum eG (Pg ∪ ∅) at heG
  change IsIdemSum eQ (∅ ∪ Q) at heQ
  rw [Finset.union_empty] at heG
  rw [Finset.empty_union] at heQ
  have heq : e = eG + eQ := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := heQ
    have := GlobalTheory.IdemSumAdd.idemSum_union D eG e Pg Q es hdisj hes heG he
    rw [this, hsum]
  subst heq
  refine ⟨hvac, eG + eQ, he, ?_⟩
  have hGG := idemSum_mul_self heG
  have hQQ := idemSum_mul_self heQ
  have hee := idemSum_mul_self he
  have hGQ : eG * eQ = 0 := by
    have h2 : (2 : AE D) * (eG * eQ) = 0 := by
      have h := hee
      rw [add_mul, mul_add, mul_add, hGG, hQQ, mul_comm eQ eG] at h
      linear_combination h
    have h2' : (2 : AE D) = algebraMap D.host.F (AE D) 2 := (map_ofNat _ 2).symm
    calc eG * eQ = algebraMap D.host.F (AE D) (1 / 2) * ((2 : AE D) * (eG * eQ)) := by
          rw [← mul_assoc, h2', ← map_mul, show (1 / 2 : D.host.F) * 2 = 1 by norm_num, map_one, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      a • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO (selfDual_isFullLattice S ΛS hS) (selfDual_isFullLattice T ΛT hT) βS βT
  have hsbG := isSBHalf_of_red eG _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (infPart_of_half (infPart_idemSum heG) ht)⟩ Pg
    (fun y => omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj y *
      omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 y) fun y y' h => by
      rw [omegaG_congr _ χj y y' h, omegaQ_congr ∅ _ _ 1 y y' fun PP hP => absurd hP (Finset.notMem_empty PP)]
  have hsbQ := isSBHalf_of_red eQ _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (infPart_of_half (infPart_idemSum heQ) ht)⟩ Q
    (fun y => omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj y *
      omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 y) fun y y' h => by
      rw [omegaG_congr _ χj y y' fun PP hP => absurd hP (Finset.notMem_empty PP), omegaQ_congr Q _ _ 1 y y' h]
  refine ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hvac.1 S T ΛS ΛT hS hT (Pg ∪ Q) (eG + eQ) he f₀
    hvac.2.theta hvac.2.lat).1, fun Tm hTm => ?_⟩
  have hTG := isPlaceModel_comp_restrictHalf hGG hQQ hGQ hΛ hTm
  have hTm' := hTm
  rw [add_comm eG eQ] at hTm'
  have hTQ := isPlaceModel_comp_restrictHalf hQQ hGG (by rw [mul_comm, hGQ]) hΛ hTm'
  have hvG := hthG.2 _ hTG
  have hvQ := hthQ.2 _ hTQ
  have hL1 := isPlaceModel_prodHalf hGG hQQ hGQ hΛ hsbQ hTm
  have hbase : ∀ Ψ : WO S T → ℂ, prodHalf eG eQ Ψ (halfInd eG (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) = restrictHalf eQ eG (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Ψ := fun Ψ => by
    funext x
    simp only [prodHalf_apply, restrictHalf_apply, add_comm eG eQ]
    ring
  rw [hbase, ← LinearMap.comp_apply, ← hvQ] at hL1
  have hd : ∀ PP ∈ Pg, ¬ (fun p => ∃ PP ∈ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
    fun PP hP ⟨PP', hP', h⟩ => hunder PP hP PP' hP' h
  have hL2 := GlobalTheory.T.supportedTranslatesCombination_commutes_schrodinger D ψ hvac.1 S T _ eG Pg _ heG hd dQ hdQ f₀ _ (combL ψ S T dQ ∘ₗ
    (Tm ∘ₗ restrictHalf eG eQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)))
    hTG fun Φ => by rw [LinearMap.comp_apply, combL_apply]
  have hu := placeModel_eq hvac.1 hS hT hGG (infPart_idemSum heG) hL1 hL2 hsbG
  rw [LinearMap.comp_apply, LinearMap.comp_apply, combL_apply, ← hvG] at hu
  rw [← hu]
  beta_reduce
  congr 1
  funext x
  exact (GlobalTheory.T.stepDatum_eq_mul_halves D S T βS βT r t j hr Pg Q P χ χj ξ eG eQ heG heQ hGQ x).symm

end GlobalTheory.HalfProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelCombStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaStepVector_eq_tupleComb_of_levelComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ : WO S T → ℂ) (dG dQ : WO S T →₀ ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q → (∀ PP ∈ Pg, ∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) → (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dG → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dQ → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj ∅ (fun _ => 1) f₀ (comb ψ S T dG f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ (comb ψ S T dG f₀)) := by
  first | exact @GlobalTheory.HalfProd.stepVec_of_prod | exact GlobalTheory.HalfProd.stepVec_of_prod | (intros; apply GlobalTheory.HalfProd.stepVec_of_prod <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamSplit

theorem stepVecOf_unique {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f)
    (h' : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f') : f = f' := by
  obtain ⟨-, e, he, hθ⟩ := h
  obtain ⟨-, e', he', hθ'⟩ := h'
  obtain rfl := GlobalTheory.DatumFourier.idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm, hθ'.2 Tm hTm]

end GlobalTheory.FamSplit

namespace GlobalTheory.FamSplit

end GlobalTheory.FamSplit
