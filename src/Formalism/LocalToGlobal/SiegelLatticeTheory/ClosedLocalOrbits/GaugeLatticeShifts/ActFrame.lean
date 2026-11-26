module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviElt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Saturated

section FrameFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) : frame (mapLF γ (lf D F)) a = γ (F.fvec a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]

end FrameFix

end Formalism.L2.SG.Pf.Act
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolS
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def DimG : Prop :=
  ∀ k r : ℕ, Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r))) =
    2 * Module.finrank ℝ (Formalism.MainNotions.S.lieE (Nset k r)) + 2 * r + Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def LieG : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0}

def LieWb : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0 ∧
    ∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0}

def expL (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (Y : Formalism.MainNotions.S.lieE S) : Mt k r :=
  fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j

def RhoN : Prop :=
  ∀ (k r : ℕ) (Y : Formalism.MainNotions.S.lieE (Nset k r)), rhoS k r (Nset k r) (expL k r (Nset k r) Y) = (‖Y‖₊ : ℝ≥0∞)

def RhoMeas : Prop :=
  ∀ (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Measurable (rhoS k r S)

def ModelVol : Prop :=
  ∀ (E1 E2 : Type) [NormedAddCommGroup E1] [InnerProductSpace ℝ E1] [FiniteDimensional ℝ E1] [MeasurableSpace E1]
    [BorelSpace E1] [NormedAddCommGroup E2] [InnerProductSpace ℝ E2] [FiniteDimensional ℝ E2] [MeasurableSpace E2]
    [BorelSpace E2] (r : ℕ) (s : ℝ), 0 < s →
    ∫⁻ c : Fin r → ℂ, ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1,
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal ((2 : ℝ) ^ r)⁻¹ *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E1 + 2 * r + Module.finrank ℝ E2))) s)

def BallDim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (s : ℝ),
    volume (Metric.ball (0 : E) s) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) s)

end Formalism.L2.SG.Pf.BH
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfG
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfF
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Concrete

variable {D : D7} (Z : LocDat D) (p : PlF D)

def IotaEl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ g : Loc.SplitG (Z.M p).L, (Z.M p).split = some g →
    IotaG (locH Z p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ)
      (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))
      (fun b => sF' Z p b • baseChange₂ D p (g2 b)) (betaP p β)

theorem omp_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Z.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Z.hcj p), cj_iota (Z.hcj p)]
  congr 2 <;> ring

end Concrete

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameAct

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

abbrev Xs (h : Fin (r + 1) → S.V) : Submodule E S.V :=
  Submodule.span E (Set.range fun a : Fin r => h a.castSucc)

theorem frameAct_castSucc_mem (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hξ : ∀ a b, b < a → ξ a b = 0) (a : Fin r) : frameAct h ξ a.castSucc ∈ Xs h := by
  show ∑ c, ((ξ c a.castSucc : 𝓞 E) : E) • h c ∈ _
  have h0 : ((ξ (Fin.last r) a.castSucc : 𝓞 E) : E) = 0 := by
    rw [hξ _ _ (Fin.castSucc_lt_last a)]
    rfl
  rw [Fin.sum_univ_castSucc, h0, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_last_sub (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hl : ξ (Fin.last r) (Fin.last r) = 1) : frameAct h ξ (Fin.last r) - h (Fin.last r) ∈ Xs h := by
  show ∑ c, ((ξ c (Fin.last r) : 𝓞 E) : E) • h c - h (Fin.last r) ∈ _
  have h1 : ((ξ (Fin.last r) (Fin.last r) : 𝓞 E) : E) = 1 := by
    rw [hl]
    rfl
  rw [Fin.sum_univ_castSucc, h1, one_smul, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_mem_span (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : frameAct h ξ b ∈ Submodule.span E (Set.range h) :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_frameAct (h : Fin (r + 1) → S.V) (ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    frameAct (frameAct h ξ) ξ' = frameAct h (ξ * ξ') := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem frameAct_one (h : Fin (r + 1) → S.V) : frameAct h 1 = h := by
  funext b
  simp only [frameAct, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · intro hb; exact absurd (Finset.mem_univ b) hb

theorem det_unitri {n : ℕ} {R : Type*} [CommRing R] (ξ : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : ξ.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

theorem frameAct_inv_back (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : frameAct (frameAct h ξ⁻¹) ξ = h := by
  rw [frameAct_frameAct, Matrix.nonsing_inv_mul _ (by rw [det_unitri ξ h1 h2]; exact isUnit_one),
    frameAct_one]

theorem Xs_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : Xs (frameAct h ξ⁻¹) = Xs h := by
  have hi := inv_unitri ξ h1 h2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_castSucc_mem h _ hi.1 a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_castSucc_mem (frameAct h ξ⁻¹) ξ h1 a
    rwa [frameAct_inv_back h ξ h1 h2] at this

theorem span_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span E (Set.range (frameAct h ξ⁻¹)) = Submodule.span E (Set.range h) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_mem_span h _ a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_mem_span (frameAct h ξ⁻¹) ξ a
    rwa [frameAct_inv_back h ξ h1 h2] at this

end FrameAct

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GZ

variable {D : D7}

theorem unitri_map (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    (∀ a b, b < a → η.map (fun x => (x : D.host.E)) a b = 0) ∧ (∀ a, η.map (fun x => (x : D.host.E)) a a = 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.map_apply, h1 a b hab]; rfl
  · rw [Matrix.map_apply, h2 a]; rfl

theorem GZ_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V) (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    GZ u (frameAct h η) = GZ u h * η.map (fun x => (x : D.host.E)) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GZ, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, frameAct, brS, map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem GDl_frameAct_top (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) (D.R.rS + 1) = GDl u h (D.R.rS + 1) := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dite_eq_left le_rfl, dite_eq_left le_rfl]
  have e : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      M.submatrix (Fin.castLE (le_refl _)) (Fin.castLE (le_refl _)) = M := fun M => by ext i j; rfl
  rw [e, e, GZ_frameAct, Matrix.det_mul, det_unitri _ hm.1 hm.2, mul_one]

theorem GDl_frameAct_r (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) D.R.rS = GDl u h D.R.rS := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dite_eq_left (Nat.le_succ _), dite_eq_left (Nat.le_succ _), GZ_frameAct]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]
  have e : (GZ u h * η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc =
      (GZ u h).submatrix Fin.castSucc Fin.castSucc *
      (η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hm.1 _ _ (Fin.castSucc_lt_last j), mul_zero, add_zero]
    rfl
  rw [e, Matrix.det_mul, det_unitri ((η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc)
    (fun a b hab => hm.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab)) (fun a => hm.2 _), mul_one]

theorem Gom'_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom' u (frameAct h η) = Gom' u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hkey : ηE * (ηE.adjugate * (GZ u h).adjugate) = (GZ u h).adjugate := by
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, det_unitri _ hm.1 hm.2, one_smul, Matrix.one_mul]
  unfold Gom'
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  simp only [frameAct, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrFun (congrFun hkey c) (Fin.last _)
  rw [Matrix.mul_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem Gom_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom u (frameAct h η) = Gom u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hadj : ηE.adjugate = ηE⁻¹ := by
    rw [Matrix.inv_def, det_unitri _ hm.1 hm.2, Ring.inverse_one, one_smul]
  have hinv := inv_unitri ηE hm.1 hm.2
  unfold Gom
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last _), hadj, hinv.2, one_mul]
  · intro k _ hk
    rw [hadj, hinv.1 _ _ (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end GZ

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsMatLift
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Matrix Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace MatLiftPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem near_one (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (P : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hP : ∀ v, P.map (TR.res v) = 1) :
    ∃ T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • P = ηO • (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) := by
  have h : ∀ i j, ∃ t : ↥(IntAf X.B.I.F X.B.I.E), X.ew * ((P - 1) i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    intro i j
    have h0 : ∀ v, TR.res v ((P - 1) i j) = 0 := fun v => by
      have := congrFun (congrFun (hP v) i) j
      simp only [Matrix.map_apply] at this
      rw [Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨t, ht, e⟩ := (TR.res_ker _).1 h0
    exact ⟨⟨t, ht⟩, e⟩
  choose T hT using h
  refine ⟨Matrix.of T, ?_⟩
  ext i j
  have e := hT i j
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply] at e ⊢
  generalize ((1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) i j) = o at e ⊢
  push_cast at e ⊢
  linear_combination (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e -
    ((P i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - (o : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * hew

theorem det_near (T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) :
    ∃ s0 : ↥(IntAf X.B.I.F X.B.I.E), (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det = 1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0 := by
  set J := Ideal.span {((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E))}
  have hm : (Ideal.Quotient.mk J).mapMatrix (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) = 1 := by
    have hg : Ideal.Quotient.mk J ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.add_apply, *]
  have h1 : Ideal.Quotient.mk J ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  have h2 : (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
  exact ⟨a, by rw [mul_comm, ha]; ring⟩

theorem right_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (A * B).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (A * B') = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (A * B) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate), ?_⟩
  have e0 : A * ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate)) =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (A * B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate) := by
    rw [Matrix.mul_smul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.smul_mul, hT, Matrix.smul_mul, Matrix.mul_adjugate, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

theorem left_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (B * A).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (B' * A) = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (B * A) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B), ?_⟩
  have e0 : ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B)) * A =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * (B * A)) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.mul_smul, hT, Matrix.mul_smul, Matrix.adjugate_mul, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

theorem coe_eq (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (P Q : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (h : ηO • (P * Q) = ηO • 1) :
    (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P.map Subtype.val * Q.map Subtype.val) =
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (1 : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
  ext i j
  have := congrArg (fun M : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E) => ((M i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) h
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Subring.coe_mul, Matrix.map_apply,
    Matrix.one_apply] at this ⊢
  push_cast at this
  split_ifs at this ⊢ <;> simpa using this

theorem integral_matrix_lift_exists : MatLift TR := by
  intro η hη _ hew _ hj s
  set ηO : ↥(IntAf X.B.I.F X.B.I.E) := ⟨η, hη⟩
  have hs : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v, TR.res v c = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  have hs' : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v,
      TR.res v c = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  choose A hA using hs
  choose B hB using hs'
  have hAm : ∀ v, (Matrix.of A).map (TR.res v) = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := fun v => by
    ext i j; simp [hA]
  have hBm : ∀ v, (Matrix.of B).map (TR.res v) = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) :=
    fun v => by ext i j; simp [hB]
  have hAB : ∀ v, (Matrix.of A * Matrix.of B).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ∀ v, (Matrix.of B * Matrix.of A).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨R', hR'⟩ := right_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hAB
  obtain ⟨L', hL'⟩ := left_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hBA
  have e1 : ηO • L' = ηO • R' := by
    calc ηO • L' = L' * (ηO • (1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E))) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = L' * (ηO • (Matrix.of A * R')) := by rw [hR']
      _ = (ηO • (L' * Matrix.of A)) * R' := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = ηO • R' := by rw [hL', Matrix.smul_mul, Matrix.one_mul]
  refine ⟨(Matrix.of A).map Subtype.val, R'.map Subtype.val, fun i j => ⟨(A i j).2, (R' i j).2⟩, ?_, ?_, ?_⟩
  · exact coe_eq ηO _ _ hR'
  · refine coe_eq ηO _ _ ?_
    calc ηO • (R' * Matrix.of A) = (ηO • R') * Matrix.of A := by rw [Matrix.smul_mul]
      _ = (ηO • L') * Matrix.of A := by rw [e1]
      _ = ηO • 1 := by rw [Matrix.smul_mul, hL']
  · intro v
    ext i j
    show resT TR v ((A i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j
    rw [LeviEltPf.resT_of_mem TR v (A i j).2]
    exact hA i j v

end MatLiftPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
end
end
