module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeConjRead
open Classical

theorem cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ} (f : Fin m → Formalism.L2.SG.HidaSetting.VA I)
    (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
  subst h
  exact hf a

theorem cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
  subst h
  exact hv

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M)
    (z : M) (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
    flagV ρ k n e f b z i ∈ S := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, h0]

theorem colMat_entry {D : D7} {n : ℕ} (M : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (M * colMat w) i j = Matrix.mulVec M (w j) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]

theorem flag_pair_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β₀ : GL (Fin (Yc D 0).rank) (EAf D)), Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 = GlobalTheory.NormSum.AdLattice.lat β₀ → ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank), ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β₀ hL PP i j
  have hF : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := hL ▸ GlobalTheory.StdFrames.isFrame_lat β₀
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
      Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro v hv
    rw [hLf] at hv
    exact (hF v).1 hv i
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
  refine ⟨?_, ?_⟩
  · rw [colMat_entry]
    apply key
    unfold flagAt
    split_ifs
    · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
    · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
  · rw [colMat_entry]
    apply key
    unfold pairAt
    split_ifs
    · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
    · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j

end GlobalTheory.SeeConjRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingVectors_integral_inFrame : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β₀ : GL (Fin (Yc D 0).rank) (EAf D)), Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 = GlobalTheory.NormSum.AdLattice.lat β₀ → ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank), ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjRead.flag_pair_int | exact GlobalTheory.SeeConjRead.flag_pair_int | (intros; apply GlobalTheory.SeeConjRead.flag_pair_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.LevelInLatStab

theorem mulVec_mem_of_integral {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B)
    (β : GL (Fin n) B) {P : AddSubgroup (Fin n → A)}
    (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S) (m : Matrix (Fin n) (Fin n) A)
    (T : Matrix (Fin n) (Fin n) S) (hm : m.map e = β.val * T.map S.subtype * (β⁻¹).val) :
    ∀ z ∈ P, m *ᵥ z ∈ P := by
  intro z hz
  rw [hP] at hz ⊢
  intro i
  rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (T i j).2 (hz j)

theorem lev_le_latLev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  intro D V β Λ L hβ x hx
  have hp := Formalism.L2.DIV.lev_le_parLev hx
  have hUA := Formalism.L2.DIV.parLev_UA hp
  have hSt := Formalism.L2.DIV.parLev_St hp
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
  obtain ⟨t, ht⟩ := hSt
  let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
  let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
  have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
    simp only [g, MulEquiv.apply_symm_apply, u]
  have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
    have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
    rw [← hg]
    exact h1.symm
  refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
  refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
  constructor
  · intro hy
    exact mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
      (by rw [hmat, ← ht]; rfl) y hy
  · intro hy
    let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
    have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
      ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
    have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
      apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
      have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
        (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
      have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
      refine (e.trans ?_).trans e1.symm
      change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
      rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
      (by rw [hm', ← ht']; rfl) _ hy
    rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LevelInLatStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_le_stabilizer_selfDual_lattice_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  first | exact @GlobalTheory.LevelInLatStab.lev_le_latLev | exact GlobalTheory.LevelInLatStab.lev_le_latLev | (intros; apply GlobalTheory.LevelInLatStab.lev_le_latLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityVanishingAndSameParamsSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityVanishingAndSameParamsSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this


open GlobalTheory.LFun.ParLin in
theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

theorem vanish_and_parLin : ∀ D : D7, MetEx D → (ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧ ∀ (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B :=
  fun D hM => ⟨val_eq_zero_imp D hM, isPar_add_smul D⟩

end GlobalTheory.EvenOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityVanishingAndSameParamsSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_vanishing_and_same_params_subspace : ∀ D : D7, MetEx D → (ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧ ∀ (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  first | exact @GlobalTheory.EvenOnto.vanish_and_parLin | exact GlobalTheory.EvenOnto.vanish_and_parLin | (intros; apply GlobalTheory.EvenOnto.vanish_and_parLin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliser
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

section RedLemmas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem redV_eq_of_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (h : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
      Formalism.L2.Herm.intAf F E) (i : Fin n) :
    redV β PP v i = resS F PP ⟨_, h i⟩ := by
  unfold redV
  rw [dite_eq_left (h i)]

end RedLemmas

theorem redV_add_smul_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  intro F E _ _ _ _ _ n β Λ hF PP
  have hint : ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ i,
      ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
        Formalism.L2.Herm.intAf F E := fun v hv => (hF v).1 hv
  refine ⟨?_, ?_, ?_⟩
  · intro v hv w hw
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (v + w) i ∈
        Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_add]
      exact Subring.add_mem _ (hint v hv i) (hint w hw i)
    funext i
    rw [Pi.add_apply, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), redV_eq_of_int β PP _ (hint w hw),
      ← map_add]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  · intro c v hv
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) i ∈ Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ c.2 (hint v hv i)
    funext i
    rw [Pi.smul_apply, smul_eq_mul, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), ← map_mul]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_smul]
  · rintro M ⟨y, rfl⟩ v hv
    set X : Fin n → Formalism.L2.Herm.intAf F E := fun j => ⟨_, hint v hv j⟩ with hX
    have hM : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((intGL F E n y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      simp [frGL, MulAut.conj_apply]
    have hkey : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i =
        ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
      intro i
      rw [hM, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, hX]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rfl
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i ∈
          Formalism.L2.Herm.intAf F E := fun i => by rw [hkey i]; exact Subtype.property _
    funext i
    rw [redV_eq_of_int β PP _ hs, redFn_frGL]
    have e1 : (⟨_, hs i⟩ : Formalism.L2.Herm.intAf F E) = ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i :=
      Subtype.ext (hkey i)
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [redV_eq_of_int β PP _ (hint v hv) j]
    rfl

end GlobalTheory.SeeConjGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliserStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  exact @GlobalTheory.SeeConjGroup.redV_add_smul_stab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem smallAt_natCast_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((N : EAf D) * t) := by
  unfold SmallAt
  rw [map_mul, map_natCast, Valuation.map_mul]
  have hv : Valued.v (N : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 hN
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  have ht' := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ht') hv

theorem sg_hY {D : D7} (x y : Fin (Yc D 0).rank → EAf D) : GlobalTheory.StdFrames.sg D (hY D x y) = hY D y x := by
  have := GlobalTheory.AdIsom.cjA_hA (Yc D 0) y x
  rw [GlobalTheory.AdIsom.hA_eq, GlobalTheory.AdIsom.hA_eq] at this
  exact this

theorem smallAt_of_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {c : EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c = (N : EAf D) * t) : SmallAt PP c := by
  obtain ⟨t, ht, rfl⟩ := h
  exact smallAt_natCast_mul hN ht

theorem smallAt_hY_of_swap {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} {d : EAf D} (hd : GlobalTheory.StdFrames.sg D d = d)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - d = (N : EAf D) * t) : SmallAt PP (hY D x y - d) := by
  obtain ⟨t, ht, e⟩ := h
  have e' := congrArg (GlobalTheory.StdFrames.sg D) e
  rw [map_sub, sg_hY, hd, map_mul, map_natCast] at e'
  rw [e']
  exact smallAt_natCast_mul hN (GlobalTheory.AdIsom.cjA_mem ht)

theorem smallAt_hY_of_swap0 {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x = (N : EAf D) * t) :
    SmallAt PP (hY D x y) := by
  have := smallAt_hY_of_swap hN (x := x) (y := y) (d := 0) (map_zero _) (by simpa using h)
  simpa using this

theorem smallAt_hY_of_swap_delta {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {a c : ι} {x y : Fin (Yc D 0).rank → EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - (if c = a then 1 else 0) = (N : EAf D) * t) :
    SmallAt PP (hY D x y - if a = c then 1 else 0) := by
  refine smallAt_hY_of_swap hN (by split_ifs <;> simp) ?_
  simpa only [eq_comm (a := a)] using h

theorem smallAt_sub_of_cpt {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {i j : ι} {c e : EAf D} (he : GlobalTheory.StdFrames.cpt PP e = 1)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c - (if i = j then e else 0) = (N : EAf D) * t) :
    SmallAt PP (c - if i = j then 1 else 0) := by
  obtain ⟨t, ht, e'⟩ := h
  have h1 : GlobalTheory.StdFrames.cpt PP (c - if i = j then 1 else 0) = GlobalTheory.StdFrames.cpt PP ((N : EAf D) * t) := by
    rw [← e']
    split_ifs <;> simp [he]
  have h2 := smallAt_natCast_mul hN ht
  unfold SmallAt at h2 ⊢
  rwa [h1]

theorem pairTable_of_cpt_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  intro D X h PP hg hew
  have F0g := X.gramIntegral
  have F0z := X.formsAtZero
  have F0W := X.weightVectorsIntegral
  have bd := X.bw_dual
  have ge := X.g_eq
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h F0g F0z F0W bd ge hew ⊢
  subst h
  subst ge
  refine ⟨fun a c => smallAt_hY_of_swap_delta hg (F0g c a).2.2, fun a j => smallAt_of_mul hg ((F0W j).2.2 a).2.1,
    fun a => smallAt_of_mul hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).2.1,
    fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.1, fun i j => smallAt_sub_of_cpt hg hew (bd i j),
    fun i => smallAt_hY_of_swap0 hg (F0W i).2.1, fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.2,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).1, fun j => smallAt_of_mul hg (F0W j).1, smallAt_of_mul hg F0z.1,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).1,
    fun a j => smallAt_of_mul hg ((F0W j).2.2 a).1, fun a => smallAt_of_mul hg (F0z.2 a).1,
    fun a c => smallAt_of_mul hg (F0g a c).2.2⟩

end GlobalTheory.SeeConjRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingTable_idempotentComponent_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  first | exact @GlobalTheory.SeeConjRead.pairTable_of_cpt_one | exact GlobalTheory.SeeConjRead.pairTable_of_cpt_one | (intros; apply GlobalTheory.SeeConjRead.pairTable_of_cpt_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostA
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroIntSmulMemOfIsLattice
namespace GlobalTheory.IntSmulMemLatticeTwistedOperators

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : Fin n → E) : ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hcx d
    · rw [mul_smul]; exact zsmul_mem hdy c
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_mul_integral a
    let b : RingOfIntegers E := ⟨(d : E) * a, hint⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have key : (d * c) • (a • x) = b • (c • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      rw [Algebra.smul_def]
      have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := rfl
      rw [hb]
      simp
      ring
    rw [key]
    exact L.smul_mem b hcx

theorem exists_nonzero_int_smul_mem_of_isLattice : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : Fin n → E), ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • v ∈ L :=
  fun L hL v => exists_int_smul_mem L hL v

end GlobalTheory.IntSmulMemLatticeTwistedOperators
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertSph Matrix Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LatAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_integral (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2

theorem smul_mem_latAt (X : Spc F E n) (w : Pl (F := F)) {b : AF F} (hb : evFin F w b ∈ w.adicCompletionIntegers F)
    {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : z ∈ latAt X w) : b • z ∈ latAt X w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨b * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hb hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (v : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice L hL v

theorem exists_int_mulVec_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L, c • (N *ᵥ y) ∈ L := by
  have key : ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L', c • (N *ᵥ y) ∈ L := by
    intro L' hL'
    induction L', hL' using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨c, hc, hx⟩ := exists_int_smul_mem L hL (N *ᵥ x)
      refine ⟨c, hc, fun y hy => ?_⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [Matrix.mulVec_smul, smul_comm]
      exact L.smul_mem r hx
    | sup A B _ _ hA hB =>
      obtain ⟨c, hc, hA⟩ := hA
      obtain ⟨d, hd, hB⟩ := hB
      refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Matrix.mulVec_add, smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact zsmul_mem (hA a ha) d
      · rw [mul_smul]; exact zsmul_mem (hB b hb) c
  exact key L hL.fg

theorem eventually_incM (X : Spc F E n) (hL : X.L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, incM F N *ᵥ z ∈ latAt X w := by
  obtain ⟨c, hc, hN⟩ := exists_int_mulVec_mem X.L hL N
  filter_upwards [eventually_integral (algebraMap F (AF F) (c : F)⁻¹)] with w hw z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    have h1 : (a • fun i => inclR (F := F) (AF F) ((c • (N *ᵥ y)) i)) ∈ latAt X w :=
      AddSubgroup.subset_closure ⟨a, ha, hv, _, hN y hy, rfl⟩
    have h2 := smul_mem_latAt X w hw h1
    convert h2 using 1
    rw [Matrix.mulVec_smul, smul_comm]
    congr 1
    ext i
    have hc' : (c : F) ≠ 0 := Int.cast_ne_zero.2 hc
    have h3 : (incM F N *ᵥ fun i => inclR (F := F) (AF F) (y i)) i = inclR (F := F) (AF F) ((N *ᵥ y) i) :=
      (RingHom.map_mulVec (inclR (F := F) (AF F)) N y i).symm
    rw [h3, Pi.smul_apply, Pi.smul_apply, map_zsmul, algebraMap_smul, ← Int.cast_smul_eq_zsmul F, smul_smul,
      inv_mul_cancel₀ hc', one_smul]
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem eventually_single (X : Spc F E n) (hL : X.L.IsFullLattice E) (i j : Fin n) (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, Matrix.single i j t *ᵥ z ∈ latAt X w := by
  induction t using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun w z _ => by simp [zero_mem]
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs
      · simp [inclR, TensorProduct.smul_tmul']
      · simp
    filter_upwards [eventually_integral a, eventually_incM X hL (Matrix.single i j e)] with w hw h2 z hz
    rw [h, Matrix.smul_mulVec]
    exact smul_mem_latAt X w hw (h2 z hz)
  | add s t hs ht =>
    filter_upwards [hs, ht] with w h1 h2 z hz
    rw [Matrix.single_add, Matrix.add_mulVec]
    exact add_mem (h1 z hz) (h2 z hz)

theorem eventually_mulVec_mem (X : Spc F E n) (hL : X.L.IsFullLattice E) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, M *ᵥ z ∈ latAt X w := by
  have h : ∀ᶠ w : Pl F in cofinite, ∀ i j, ∀ z ∈ latAt X w, Matrix.single i j (M i j) *ᵥ z ∈ latAt X w :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_single X hL i j (M i j)
  filter_upwards [h] with w hw z hz
  rw [Matrix.matrix_eq_sum_single M, Matrix.sum_mulVec]
  refine sum_mem fun i _ => ?_
  rw [Matrix.sum_mulVec]
  exact sum_mem fun j _ => hw i j z hz

theorem exists_finset_keeps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  intro F E _ _ _ _ _ σ n X hL g
  have h := (eventually_mulVec_mem X hL (mat g)).and (eventually_mulVec_mem X hL (mat g⁻¹))
  refine ⟨(eventually_cofinite.1 h).toFinset, fun w hw z hz => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
  exact ⟨hw.1 z hz, hw.2 z hz⟩

end GlobalTheory.LatAlmostAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.RevTab

open Classical Formalism.L2.SG.HidaSetting

theorem pairTable_of {M A : Type} [Ring A] (p : M → M → A) (Z sm : A → Prop) (hZ : ∀ c, Z c → sm c)
    (hadd : ∀ a b, sm a → sm b → sm (a + b)) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M) (z : M) (u : A)
    (hu : sm (u - 1))
    (t1 : ∀ a c, Z (p (f a) (e c) - if a = c then 1 else 0)) (t2 : ∀ a j, Z (p (f a) (b j))) (t3 : ∀ a, Z (p (f a) z))
    (t4 : ∀ a c, Z (p (f a) (f c)))
    (t5 : ∀ i a, Z (p (b' i) (e a))) (t6 : ∀ i j, Z (p (b' i) (b j) - if i = j then u else 0)) (t7 : ∀ i, Z (p (b' i) z))
    (t8 : ∀ i a, Z (p (b' i) (f a)))
    (t9 : ∀ a, Z (p z (e a))) (t10 : ∀ j, Z (p z (b j))) (t11 : Z (p z z + 1)) (t12 : ∀ a, Z (p z (f a)))
    (t13 : ∀ a c, Z (p (e a) (e c))) (t14 : ∀ a j, Z (p (e a) (b j))) (t15 : ∀ a, Z (p (e a) z))
    (t16 : ∀ a c, Z (p (e a) (f c) - if a = c then 1 else 0)) :
    PairTable p sm e f b b' z := by
  refine ⟨fun a c => hZ _ (t1 a c), fun a j => hZ _ (t2 a j), fun a => hZ _ (t3 a), fun a c => hZ _ (t4 a c),
    fun i a => hZ _ (t5 i a), fun i j => ?_, fun i => hZ _ (t7 i), fun i a => hZ _ (t8 i a),
    fun a => hZ _ (t9 a), fun j => hZ _ (t10 j), hZ _ t11, fun a => hZ _ (t12 a),
    fun a c => hZ _ (t13 a c), fun a j => hZ _ (t14 a j), fun a => hZ _ (t15 a), fun a c => hZ _ (t16 a c)⟩
  have h := hZ _ (t6 i j)
  by_cases hij : i = j
  · simp only [hij, if_true] at h ⊢
    have := hadd _ _ h hu
    rwa [show p (b' j) (b j) - u + (u - 1) = p (b' j) (b j) - 1 by abel] at this
  · simpa only [hij, if_false] using h

variable {D : D7}

theorem smallAt_add {PP : Pl D.host.E} {a b : EAf D} (ha : SmallAt PP a) (hb : SmallAt PP b) : SmallAt PP (a + b) := by
  unfold SmallAt at *
  rw [RingHom.map_add (f := _)]
  exact Valuation.map_add_lt _ ha hb

theorem smallAt_of_mul {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((g : EAf D) * t) := by
  unfold SmallAt
  have hv : Valued.v (g : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (g : 𝓞 D.host.E)).2 hg
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  rw [RingHom.map_mul, map_natCast, Valuation.map_mul]
  have h1 := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  calc Valued.v (g : PP.adicCompletion D.host.E) * Valued.v (GlobalTheory.StdFrames.cpt PP t)
      ≤ Valued.v (g : PP.adicCompletion D.host.E) * 1 := mul_le_mul_of_nonneg_left h1 zero_le'
    _ = Valued.v (g : PP.adicCompletion D.host.E) := mul_one _
    _ < 1 := hv

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead.RevTab

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf
open scoped TensorProduct

section Cong

variable {I : Formalism.MainNotions.S.AutInst} {g : ℕ}

theorem zmod_swap {x y : VA I} {d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (h : ZMod' I g (hA I x y - d)) :
    ZMod' I g (hA I y x - sigA I d) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [map_sub, ← unitaryCongruence.hA_symm] at this

theorem zmod_swap0 {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [← unitaryCongruence.hA_symm] at this

theorem zmod_swap_delta {ρ : ℕ} {x y : VA I} {a c : Fin ρ} (h : ZMod' I g (hA I x y - if c = a then 1 else 0)) :
    ZMod' I g (hA I y x - if a = c then 1 else 0) := by
  have := zmod_swap h
  by_cases hac : a = c
  · subst hac
    simpa using this
  · simpa [hac, Ne.symm hac] using this

theorem zmod_diag {k : ℕ} {bw bwd : Fin k → VA I} {ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F}
    (hD : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) (i j : Fin k) :
    ZMod' I g (hA I (bw (Fin.rev i)) (bwd (Fin.rev j)) - if i = j then sigA I ew else 0) := by
  have := zmod_swap (hD (Fin.rev j) (Fin.rev i))
  by_cases hij : i = j
  · subst hij
    simpa using this
  · have h2 : ¬ Fin.rev j = Fin.rev i := fun h => hij (Fin.rev_injective h).symm
    simpa [hij, h2] using this

end Cong

variable {D : D7}

theorem smallAt_sg_sub_one {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {ew : EAf D}
    (hc0 : ∃ t ∈ GlobalTheory.StdFrames.OA D, 1 - ew - GlobalTheory.StdFrames.sg D ew = (g : EAf D) * t) (hid : ew * ew = ew)
    (hne : GlobalTheory.StdFrames.cpt PP ew ≠ 1) : SmallAt PP (GlobalTheory.StdFrames.sg D ew - 1) := by
  have h0 : GlobalTheory.StdFrames.cpt PP ew = 0 := by
    have h1 := congrArg (GlobalTheory.StdFrames.cpt PP) hid
    rw [map_mul] at h1
    have h2 : GlobalTheory.StdFrames.cpt PP ew * (GlobalTheory.StdFrames.cpt PP ew - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  obtain ⟨t, ht, hc⟩ := hc0
  have hs := smallAt_of_mul hg ht
  rw [← hc] at hs
  have e1 : GlobalTheory.StdFrames.sg D ew - 1 = -(1 - ew - GlobalTheory.StdFrames.sg D ew) - ew := by ring
  unfold SmallAt at *
  rw [e1, map_sub, map_neg, h0, sub_zero, Valuation.map_neg]
  exact hs

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf RevTab

theorem pairTable_rev : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  intro D X h PP hg hne
  have hc0 : ZMod' X.B.I X.B.g (1 - X.ew - sigA X.B.I X.ew) := by
    have hz := X.vectorsInLattice.2.1
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 ((1 - X.ew - sigA X.B.I X.ew) • X.z0)) :=
      unitaryCongruence.mL_Qs X.B.I X.B.g hz (X.ew_full _ hz)
    rw [unitaryCongruence.hA_smul_right] at h2
    have hint : (1 - X.ew - sigA X.B.I X.ew) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (unitaryCongruence.sigA_mem _ X.ew_int)
    have h4 := unitaryCongruence.Z_sub X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g hint X.formsAtZero.1) h2
    rwa [show (1 - X.ew - sigA X.B.I X.ew) * (hA X.B.I X.z0 X.z0 + 1) -
      (1 - X.ew - sigA X.B.I X.ew) * hA X.B.I X.z0 X.z0 = 1 - X.ew - sigA X.B.I X.ew by ring] at h4
  have hG := X.gramIntegral
  have hZ := X.formsAtZero
  have hW := X.weightVectorsIntegral
  have hD := X.bw_dual
  have hgq := X.g_eq
  have hid := X.ew_idem
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hc0 hG hZ hW hD hgq hid hne ⊢
  subst h
  subst hgq
  refine pairTable_of (hY D) (ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1)) (SmallAt PP)
    (fun c ⟨t, ht, hc⟩ => hc ▸ RevTab.smallAt_of_mul hg ht) (fun a b => smallAt_add) _ _ _ _ _ _
    (smallAt_sg_sub_one hg hc0 hid hne)
    (fun a c => zmod_swap_delta (hG c a).2.2) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.2) (fun a => (hZ.2 a).2)
    (fun a c => (hG a c).2.1)
    (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).1) (fun i j => zmod_diag hD i j)
    (fun i => zmod_swap0 (hW (Fin.rev i)).1) (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).2.1)
    (fun a => zmod_swap0 (hZ.2 a).1) (fun j => (hW (Fin.rev j)).2.1) hZ.1 (fun a => zmod_swap0 (hZ.2 a).2)
    (fun a c => (hG a c).1) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.1) (fun a => (hZ.2 a).1)
    (fun a c => (hG a c).2.2)

end GlobalTheory.SeeConjRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  first | exact @GlobalTheory.SeeConjRead.pairTable_rev | exact GlobalTheory.SeeConjRead.pairTable_rev | (intros; apply GlobalTheory.SeeConjRead.pairTable_rev <;> assumption)
end
end
