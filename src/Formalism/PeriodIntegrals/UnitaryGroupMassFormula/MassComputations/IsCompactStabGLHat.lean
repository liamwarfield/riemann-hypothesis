module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.TensLiftSelf
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def pv (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : Fin n → Fv F v ⊗[F] E :=
  fun i => tensMap (E := E) (evalV F v) (x i)

def latHat (Λ : Set (Fin n → E)) : Set (Fin n → Af F ⊗[F] E) :=
  {x | ∀ v, pv v x ∈ latLoc (E := E) v Λ}

theorem pv_mulVec (v : HeightOneSpectrum (𝓞 F)) (m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (x : Fin n → Af F ⊗[F] E) :
    pv v (m *ᵥ x) = (m.map (tensMap (E := E) (evalV F v))) *ᵥ pv v x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [pv, Matrix.mulVec, dotProduct, map_sum]

open Classical in
theorem singleV_smul (v : HeightOneSpectrum (𝓞 F)) (c : F) (y : Fv F v) :
    singleV F v (c • y) = c • singleV F v y := by
  apply RestrictedProduct.ext
  intro j
  show (singleV F v (c • y)) j = evalV F j (c • singleV F v y)
  rw [map_smul]
  show _ = c • (singleV F v y) j
  by_cases h : j = v
  · subst h
    rw [PI.VolStabSW.VolAAW.singleV_self, PI.VolStabSW.VolAAW.singleV_self]
  · rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, PI.VolStabSW.VolAAW.singleV_ne _ _ h, smul_zero]

def sV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' := PI.VolStabSW.SdUniqW.singleV_add v
  map_smul' := singleV_smul v

def liftV (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : Fin n → Af F ⊗[F] E :=
  fun i => LinearMap.rTensor E (sV v) (y i)

theorem tens_lift_self (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F v) (LinearMap.rTensor E (sV v) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F v (singleV F v a)) ⊗ₜ[F] e = a ⊗ₜ e
    show (singleV F v a v) ⊗ₜ[F] e = a ⊗ₜ e
    rw [PI.VolStabSW.VolAAW.singleV_self]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem tens_lift_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F w) (LinearMap.rTensor E (sV v) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F w (singleV F v a)) ⊗ₜ[F] e = 0
    show (singleV F v a w) ⊗ₜ[F] e = 0
    rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem pv_liftV_self (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : pv v (liftV v y) = y := by
  funext i
  exact tens_lift_self v (y i)

theorem pv_liftV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fin n → Fv F v ⊗[F] E) :
    pv w (liftV v y) = 0 := by
  funext i
  exact tens_lift_ne h (y i)

theorem liftV_mem (Λ : Set (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : liftV v y ∈ latHat (F := F) Λ := by
  intro w
  by_cases h : w = v
  · subst h
    rw [pv_liftV_self]
    exact hy
  · rw [pv_liftV_ne h]
    exact zero_mem _

theorem loc_of_matStab (Λ : Set (Fin n → E)) {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)}
    (hm : m ∈ matStab (latHat (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : (m.map (tensMap (E := E) (evalV F v))) *ᵥ y ∈ latLoc (E := E) v Λ := by
  have h := hm _ (liftV_mem Λ v hy) v
  rwa [pv_mulVec, pv_liftV_self] at h

end Lift

end MassDataMassesW.KCptW
end
end

noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Char

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def stabGLHat (Λ : Set (Fin n → E)) : Set (GL (Fin n) (Af F ⊗[F] E)) :=
  {g | (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) ∧
    ((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ)}

theorem mem_Kloc_of (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)} (hg : g ∈ stabGLHat Λ)
    (v : HeightOneSpectrum (𝓞 F)) : compV v g ∈ Kloc (E := E) v Λ := by
  intro y
  constructor
  · intro hy
    exact loc_of_matStab Λ hg.1 v hy
  · intro hy
    have hy' : ((g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E := E) (evalV F v))) *ᵥ y ∈
        latLoc (E := E) v Λ := hy
    have h := loc_of_matStab Λ hg.2 v hy'
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h

theorem matStab_of_mem (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)}
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), compV v g ∈ Kloc (E := E) v Λ) :
    (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) := by
  intro x hx v
  rw [pv_mulVec]
  exact ((hg v) (pv v x)).1 (hx v)

theorem kf_iff (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ incAf σ J g ∈ stabGLHat Λ := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Kf σ J Λ := (Kf σ J Λ).inv_mem hg
    refine ⟨matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg v), ?_⟩
    rw [← map_inv]
    exact matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg' v)
  · intro h
    rw [Kf, Subgroup.mem_iInf]
    intro v
    exact mem_Kloc_of Λ h v

end Char

def LatHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsOpen (latHat (F := F) (L : Set (Fin n → E)))

def LatHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsCompact (latHat (F := F) (L : Set (Fin n → E)))

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

theorem pv_intSmul_single (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (j : Fin n) :
    pv v ((N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E)) = ratV (F := F) (Fv F v) (N • (Pi.single j (1 : E) : Fin n → E)) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [pv, ratV, Algebra.smul_def, tensMap, inclR]
  · simp [pv, ratV, h, tensMap, inclR]

theorem hcol_hat (L : Submodule (𝓞 E) (Fin n → E)) {N : ℤ}
    (hN : ∀ j : Fin n, N • (Pi.single j (1 : E) : Fin n → E) ∈ L) (j : Fin n) :
    (N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) (L : Set (Fin n → E)) := by
  intro v
  rw [pv_intSmul_single]
  exact Submodule.subset_span ⟨_, hN j, rfl⟩

theorem isCompact_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E)))) :
    IsCompact (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  classical
  set M := latHat (F := F) (L : Set (Fin n → E))
  have hMcl : IsClosed M := hc.isClosed
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  have hN : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hSc := isCompact_matStab (K := F) hc hMcl (N : F) hN (hcol_hat L hNmem)
  have e : stabGLHat (F := F) (L : Set (Fin n → E)) =
      Units.embedProduct _ ⁻¹' (matStab M ×ˢ (MulOpposite.op '' matStab M)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyg⟩
      refine ⟨h1, ?_⟩
      have hy' : y = (((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
        MulOpposite.op_injective hyg
      rwa [hy'] at hy
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod (hSc.image MulOpposite.continuous_op))

theorem isOpen_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E))))
    (ho : IsOpen (latHat (F := F) (L : Set (Fin n → E)))) :
    IsOpen (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  have hS := isOpen_matStab hc ho
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

end Glob

end MassDataMassesW.KCptW

namespace MassDataMassesW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub KCptW

end MassDataMassesW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NVolAllOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.BridgeKHolds
noncomputable section

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open Matrix

namespace MassDataMassesW.NBr

theorem incAf_finHA {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Gf) :
    Formalism.L2.SG.Sub.incAf X.B.I.cm.sig X.B.I.J (finHA X hb x) =
      Formalism.UG.bc (Formalism.L2.SG.AdBridge.prF X.B.I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
          (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x))) := rfl

theorem bridgeK_holds : BridgeK := by
  intro D X hb x
  have hbr' : X.B.I.fmat x = _ := (hb.choose_spec (1, x)).2
  have hK : x ∈ X.B.I.Kset ↔
      Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x) ∈ Formalism.L2.SG.AdBridge.KfHA X.B.I := by
    refine Iff.trans ?_ (adelic_compact_finite_places X.B.I (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x)))
    show (∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf) ↔ _
    rw [hbr']
    rfl
  refine hK.trans ?_
  simp only [KX, Formalism.L2.SG.Sub.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply,
    incAf_finHA]
  rfl

end MassDataMassesW.NBr
end
end

noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

def FdA {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf) :
    Set ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  {n | ∃ s ∈ FdN, (splitA X.B.I.cm.sig X.B.I.J (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).1 = X.toInf hb s ∧
    (splitA X.B.I.cm.sig X.B.I.J (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).2 ∈ KX X}

def UnipotentFundamentalDomain : Prop :=
  StrongApproxN → NLevel → BridgeK → SplitIso →
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word)
    (FdN : Set X.B.I.Ginf), X.MeasTie hb → X.LevelSubgroupNormalized →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    IsFundamentalDomain (ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (FdA X hb u FdN) (X.measW u).μN

def N4 : Prop :=
  SplitIso →
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf),
    (X.measW u).IsTextNorm → X.MeasTie hb →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    (X.measW u).μN (FdA X hb u FdN) =
      X.muN u FdN * (X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))

def UnipotentCoveringCount : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word)
    (𝓕 : Set ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))),
    (X.measW u).IsTextNorm →
    IsFundamentalDomain (ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μN →
    covol (X.measW u).μN = ((X.measW u).μN 𝓕).toReal

theorem nVolAll_of (hSA : StrongApproxN) (hS : SplitIso) (h3 : UnipotentFundamentalDomain) (h4 : N4) (hc : UnipotentCoveringCount) : NVolAll := by
  intro D X hb hK u FdN hT hL hF
  have hN : (X.measW u).IsTextNorm := X.measW_norm u
  have hfd := h3 hSA NLev.nLevel_holds NBr.bridgeK_holds hS X hb hK u FdN hT hL hF
  have h4' := h4 hS X hb u FdN hN hT hF
  have hc' := hc X u _ hN hfd
  show covol (X.measW u).μN = (X.muN u FdN).toReal *
    ((X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal
  rw [hc', h4', ENNReal.toReal_mul]

end MassDataMassesW
end
end
