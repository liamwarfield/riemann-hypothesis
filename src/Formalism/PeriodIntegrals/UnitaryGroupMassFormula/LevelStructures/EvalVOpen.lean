module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FinProjOpen
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdxGlobOfFinProj
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelOpenUnitary
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

variable {D : D7}

def levelSubgroupOfCharacter (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2.1 _ ha

def conjugateLevelSubgroup (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  ((levelSubgroupOfCharacter X hK).map (PI.MassDataKppVolLemmas.tfHom X.B.I hb)).map
    (MulAut.conj (finHA X hb (X.xu w))).toMonoidHom

theorem coe_K2uSub (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    (conjugateLevelSubgroup X hb hK w : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = K2u X hb w := by
  rw [conjugateLevelSubgroup, Subgroup.coe_map, Subgroup.coe_map]
  rfl

def conjugateLevelLocal (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 X.B.I.F)) : Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (conjugateLevelSubgroup X hb hK w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v))

theorem coe_K2vSub (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (conjugateLevelLocal X hb hK w v : Set (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J)) =
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) v := by
  rw [conjugateLevelLocal, Subgroup.coe_map, coe_K2uSub]
  rfl

def KvSub (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).comap
    (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J).subtype

theorem local_level_le_maximal (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (w : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) : conjugateLevelLocal X hb hK w v ≤ KvSub X v := by
  rintro _ ⟨h, hh, rfl⟩
  have h1 : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hh)
  rw [Kf, Subgroup.mem_iInf] at h1
  exact h1 v

def ConjugateLevelOpenUnitary : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, IsOpen (Subtype.val ⁻¹' K2u X hb w :
      Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))

def ParabolicLevelOpenLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), IsOpen (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

theorem contMul_sub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (S : Subgroup G) :
    ContinuousMul S := by
  have hc : Continuous fun q : S × S => ((q.1 : G) * (q.2 : G)) :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  exact ⟨hc.subtype_mk (fun q => S.mul_mem q.1.2 q.2.2)⟩

theorem contMul_HAf {D : D7} (X : HidaSetting D) : ContinuousMul (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalRing (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)
  exact inferInstanceAs (ContinuousMul (HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

theorem contMul_HAv {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    ContinuousMul (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalRing (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
  exact inferInstanceAs (ContinuousMul (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J))

theorem haarIdxGlob_of (hO : ConjugateLevelOpenUnitary) : HaarIdxGlob := by
  intro D X hb hK hT hL w
  have hH : ((X.measW w).μHf).IsHaarMeasure := (X.measW_norm w).2.2.1
  have := contMul_HAf X
  have := contMul_sub (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
  haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have eA : (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := by
    ext x
    show (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ↔ (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelSubgroup X hb hK w
    rw [← coe_K2uSub X hb hK w]
    rfl
  have eB : (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := rfl
  have hle : (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤
      (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hx)
  have hop := hO X hb hK hT hL w
  rw [eA] at hop
  have hBor : BorelSpace (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) :=
    Subtype.borelSpace (fun x => x ∈ ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))
  have key := toReal_eq_relIndex_mul_of_haar (G := Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
    (contMul_sub _) hBor
    (X.measW w).μHf hH _ _ hle hop
  have eA' : Subgroup.closure (Subtype.val ⁻¹' K2u X hb w :
      Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eA, Subgroup.closure_eq]
  have eB' : Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eB, Subgroup.closure_eq]
  unfold muHf muHfpp idxH
  erw [eA', eB', eA, eB]
  all_goals exact key

theorem haarIdxLoc_of (hO : ParabolicLevelOpenLocal) : HaarIdxLoc := by
  intro D X hb hK hT hL w p
  have hH : ((X.measW w).μSv p.1).IsHaarMeasure := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  have := contMul_HAv X p.1
  have := contMul_sub (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))
  haveI : BorelSpace (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have eA : (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := by
    ext x
    show (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔
      (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelLocal X hb hK w p.1
    rw [← coe_K2vSub X hb hK w p.1]
    rfl
  have eB : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := rfl
  have hle : (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤
      (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact local_level_le_maximal X hb hK hL w p.1 hx
  have hop := hO X hb hK hT hL w p
  rw [eA] at hop
  have hBor : BorelSpace (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) :=
    Subtype.borelSpace (fun x => x ∈ ((Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) :
      Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)))
  have key := toReal_eq_relIndex_mul_of_haar (G := Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))
    (contMul_sub _) hBor
    ((X.measW w).μSv p.1) hH _ _ hle hop
  have eA' : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eA, Subgroup.closure_eq]
  have eB' : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eB, Subgroup.closure_eq]
  unfold muSv muSvpp idxS
  erw [eA', eB', eA, eB]
  all_goals exact key

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
open Formalism.MainNotions.S (AutInst)
open scoped TensorProduct

def FinProjOpen : Prop :=
  ∀ I : AutInst, IsOpenMap (fun h : HAd I => (splitA I.cm.sig I.J h).2)

theorem finPart_inf_one (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) :
    (splitA I.cm.sig I.J (toHA I hb (s, 1))).2 = 1 := by
  apply Bridge_HA_ext
  have hB : I.fmat 1 = ofHAFin I (toHA I hb (s, 1)) := (toHA_isBridge I hb (s, 1)).2
  have hm : ((HA.mat (Af I.F) I.cm.sig I.J ((splitA I.cm.sig I.J (toHA I hb (s, 1))).2) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _) =
      (ofHAFin I (toHA I hb (s, 1))).map (swapE I) := by
    ext i j
    simp only [ofHAFin, Matrix.map_apply]
    rw [← Bridge_tens_eq]
    rfl
  rw [hm, ← hB]
  have h1 : I.fmat 1 = 1 := rfl
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem finPart_eq (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) (x : I.Gf) :
    (splitA I.cm.sig I.J (toHA I hb (s, x))).2 = tf I hb x := by
  unfold tf
  rw [show ((s, x) : I.GA) = (s, 1) * (1, x) by ext <;> simp, map_mul, map_mul, Prod.snd_mul,
    finPart_inf_one I hb s, one_mul]

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, by simp [Formalism.MainNotions.S.AutInst.fmat]⟩⟩
  show _ ∈ Formalism.UG.stabGL I.Lf
  simpa using one_mem (Formalism.UG.stabGL I.Lf)

theorem level_subgroup_isOpen {D : D7} (X : HidaSetting D) (hL : X.LevelSubgroupNormalized) (hK : X.LevelSubgroupCharacter) :
    IsOpen (X.K2 : Set X.B.I.Gf) := by
  have hg1 : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hKg : IsOpen (X.B.I.Kg X.B.g : Set X.B.I.Gf) := X.B.I.topf_open X.B.g hg1
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (X.B.I.Kg X.B.g : Set X.B.I.Gf)) :=
    hKg.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using one_mem_Kg X.B.I X.B.g)) ?_
  intro y hy
  have h2 := hK.2.1 x hx _ (hL.1 _ hy).1
  simpa using h2

theorem conjugate_level_isOpen (hP : FinProjOpen) {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)
    (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    IsOpen (K2u X hb w) := by
  set a := X.xu w
  have hU : IsOpen ((fun y => a * y * a⁻¹) '' X.K2) := by
    have e : (fun y => a * y * a⁻¹) '' X.K2 = (fun y => a⁻¹ * y * a) ⁻¹' X.K2 := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro hy
        exact ⟨a⁻¹ * y * a, hy, by group⟩
    rw [e]
    exact (level_subgroup_isOpen X hL hK).preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hW : IsOpen ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) :=
    (toHA X.B.I hb).toHomeomorph.isOpenMap _ (isOpen_univ.prod hU)
  have e : K2u X hb w = (fun h : HAd X.B.I => (splitA X.B.I.cm.sig X.B.I.J h).2) ''
      ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) := by
    have hom : ∀ k, tf X.B.I hb (a * k * a⁻¹) = finHA X hb a * finHA X hb k * (finHA X hb a)⁻¹ := by
      intro k
      show tfHom X.B.I hb (a * k * a⁻¹) = tfHom X.B.I hb a * tfHom X.B.I hb k * (tfHom X.B.I hb a)⁻¹
      rw [map_mul, map_mul, map_inv]
    ext h
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨toHA X.B.I hb (1, a * k * a⁻¹), ⟨(1, a * k * a⁻¹), ⟨trivial, k, hk, rfl⟩, rfl⟩, ?_⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, a * k * a⁻¹))).2 = _
      rw [finPart_eq, hom]
    · rintro ⟨_, ⟨⟨s, x⟩, ⟨-, k, hk, rfl⟩, rfl⟩, rfl⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, a * k * a⁻¹))).2 ∈ K2u X hb w
      rw [finPart_eq, hom]
      exact ⟨finHA X hb k, ⟨k, hk, rfl⟩, rfl⟩
  rw [e]
  exact hP X.B.I _ hW

theorem k2uOpenH_of (hP : FinProjOpen) : ConjugateLevelOpenUnitary := by
  unfold ConjugateLevelOpenUnitary
  intro D X hb hK _ hL w
  exact (conjugate_level_isOpen hP X hb hK hL w).preimage continuous_subtype_val

theorem haarIdxGlob_of_finProj (hP : FinProjOpen) : HaarIdxGlob :=
  haarIdxGlob_of (k2uOpenH_of hP)

def EvalVOpen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsOpenMap (haMap I.cm.sig I.J (evalV I.F v))

theorem k2vOpenS_of (hP : FinProjOpen) (hE : EvalVOpen) : ParabolicLevelOpenLocal := by
  intro D X hb hK _ hL w p
  exact ((hE X.B.I p.1) _ (conjugate_level_isOpen hP X hb hK hL w)).preimage continuous_subtype_val

theorem haarIdxLoc_of_open (hP : FinProjOpen) (hE : EvalVOpen) : HaarIdxLoc :=
  haarIdxLoc_of (k2vOpenS_of hP hE)

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S (AutInst)

theorem finProjOpen_holds : FinProjOpen := by
  intro I
  obtain ⟨e, he⟩ := MassDataMassesW.splitIso_holds I.cm.sig I.J
  have h : (fun h : HAd I => (splitA I.cm.sig I.J h).2) = Prod.snd ∘ e := by
    funext h
    simp only [Function.comp, he]
  rw [h]
  exact isOpenMap_snd.comp e.toHomeomorph.isOpenMap

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

namespace EvalVW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures

theorem isOpenMap_of_section {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousMul G] (π : G →* H) (s : H → G) (hs : Continuous s) (hπ : ∀ y, π (s y) = y) :
    IsOpenMap π := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩

  let t : H → G := fun y => s y * ((s (π x))⁻¹ * x)
  have ht : Continuous t := hs.mul continuous_const
  refine ⟨t ⁻¹' U, fun y hy => ⟨t y, hy, by simp [t, hπ]⟩, hU.preimage ht, ?_⟩
  show s (π x) * ((s (π x))⁻¹ * x) ∈ U
  rwa [mul_inv_cancel_left]

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
variable (j : R' →ₗ[F] R)

def Jt : R' ⊗[F] E →ₗ[F] R ⊗[F] E := TensorProduct.map j LinearMap.id

theorem Jt_tmul (a : R') (e : E) : Jt (E := E) j (a ⊗ₜ e) = j a ⊗ₜ e := rfl

variable {j}

theorem Jt_mul (hj : ∀ x y, j (x * y) = j x * j y) (x y : R' ⊗[F] E) :
    Jt j (x * y) = Jt j x * Jt j y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | tmul b e' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Jt_tmul, Jt_tmul, Jt_tmul, hj, Algebra.TensorProduct.tmul_mul_tmul]
    | add y y' hy hy' => rw [mul_add, map_add (f := _), hy, hy', map_add (f := _), mul_add]
  | add x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]

def eps (j : R' →ₗ[F] R) : R ⊗[F] E := Jt j 1

theorem Jt_mul_eps (hj : ∀ x y, j (x * y) = j x * j y) (x : R' ⊗[F] E) : Jt j x * eps (E := E) j = Jt j x := by
  rw [eps, ← Jt_mul hj, mul_one]

theorem eps_mul_Jt (hj : ∀ x y, j (x * y) = j x * j y) (x : R' ⊗[F] E) : eps (E := E) j * Jt j x = Jt j x := by
  rw [eps, ← Jt_mul hj, one_mul]

theorem eps_mul_eps (hj : ∀ x y, j (x * y) = j x * j y) : eps (E := E) j * eps (E := E) j = eps (E := E) j :=
  Jt_mul_eps hj 1

theorem Jt_inclR (e : E) : Jt j (inclR R' e) = eps (E := E) j * inclR R e := by
  show Jt j ((1 : R') ⊗ₜ e) = Jt j ((1 : R') ⊗ₜ (1 : E)) * ((1 : R) ⊗ₜ e)
  rw [Jt_tmul, Jt_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem sigR_Jt (σ : E →ₐ[F] E) (x : R' ⊗[F] E) : sigR R σ (Jt j x) = Jt j (sigR R' σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    show Algebra.TensorProduct.map (AlgHom.id F R) σ (Jt j (a ⊗ₜ e)) =
      Jt j (Algebra.TensorProduct.map (AlgHom.id F R') σ (a ⊗ₜ e))
    rw [Jt_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Jt_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem tensMap_Jt (φ : R →ₐ[F] R') (hφ : ∀ x, φ (j x) = x) (x : R' ⊗[F] E) :
    tensMap (E := E) φ (Jt j x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    show Algebra.TensorProduct.map φ (AlgHom.id F E) (Jt j (a ⊗ₜ e)) = a ⊗ₜ e
    rw [Jt_tmul, Algebra.TensorProduct.map_tmul, hφ]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

section Mat

variable {n : ℕ}

def secM (j : R' →ₗ[F] R) (M : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  M.map (Jt j) + (1 - eps (E := E) j) • (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E))

variable (hj : ∀ x y, j (x * y) = j x * j y)
include hj

theorem mapJ_mul (A B : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    (A * B).map (Jt j) = A.map (Jt j) * B.map (Jt j) := by
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Jt_mul hj]

theorem eps_smul_mapJ (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) : eps (E := E) j • A.map (Jt j) = A.map (Jt j) := by
  ext i k
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eps_mul_Jt hj]

theorem c_smul_mapJ (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) : (1 - eps (E := E) j) • A.map (Jt j) = 0 := by
  rw [sub_smul, one_smul, eps_smul_mapJ hj, sub_self]

theorem JR_mapJ (J : Matrix (Fin n) (Fin n) E) : (JR (F := F) R' J).map (Jt j) = eps (E := E) j • JR (F := F) R J := by
  ext i k
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact Jt_inclR (J i k)

theorem mapJ_mul_JR (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    A.map (Jt j) * JR (F := F) R J = (A * JR (F := F) R' J).map (Jt j) := by
  rw [mapJ_mul hj, JR_mapJ hj, Matrix.mul_smul, ← Matrix.smul_mul, eps_smul_mapJ hj]

theorem JR_mul_mapJ (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    JR (F := F) R J * A.map (Jt j) = (JR (F := F) R' J * A).map (Jt j) := by
  rw [mapJ_mul hj, JR_mapJ hj, Matrix.smul_mul, ← Matrix.mul_smul, eps_smul_mapJ hj]

theorem c_mul_c : (1 - eps (E := E) j) * (1 - eps (E := E) j) = 1 - eps (E := E) j := by
  linear_combination eps_mul_eps (E := E) hj

theorem secM_mul (M N : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    secM j (M * N) = secM j M * secM j N := by
  simp only [secM, mapJ_mul hj, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    c_smul_mapJ hj, smul_smul, c_mul_c hj, add_zero, zero_add]

theorem secM_one : secM j (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)).map (Jt j) = eps (E := E) j • 1 := by
    ext i k
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [eps]
  rw [secM, h1, ← add_smul, add_sub_cancel, one_smul]

theorem cT_secM (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    Formalism.UG.cT (sigR R σ) (secM j M) = secM j (Formalism.UG.cT (sigR R' σ) M) := by
  have hc : sigR R σ (1 - eps (E := E) j) = 1 - eps (E := E) j := by
    rw [map_sub, map_one, eps, sigR_Jt, map_one]
  ext i k
  simp only [Formalism.UG.cT, secM, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul, hc, sigR_Jt]
  rcases eq_or_ne i k with rfl | h
  · simp
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem secM_unitary (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (R' ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R' σ) M * JR (F := F) R' J * M = JR (F := F) R' J) :
    Formalism.UG.cT (sigR R σ) (secM j M) * JR (F := F) R J * secM j M = JR (F := F) R J := by
  rw [cT_secM hj]
  simp only [secM]
  rw [add_mul, Matrix.smul_mul, Matrix.one_mul, mapJ_mul_JR hj, add_mul, mul_add, mul_add, ← mapJ_mul hj, hM,
    JR_mapJ hj, Matrix.mul_smul, Matrix.mul_one, c_smul_mapJ hj, Matrix.smul_mul, JR_mul_mapJ hj, c_smul_mapJ hj,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, c_mul_c hj, add_zero, zero_add,
    ← add_smul, add_sub_cancel, one_smul]

end Mat

section Grp

variable {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
variable (hj : ∀ x y, j (x * y) = j x * j y)

def secGL (g : GL (Fin n) (R' ⊗[F] E)) : GL (Fin n) (R ⊗[F] E) where
  val := secM j g
  inv := secM j (g⁻¹ : GL (Fin n) (R' ⊗[F] E))
  val_inv := by rw [← secM_mul hj, Units.mul_inv, secM_one hj]
  inv_val := by rw [← secM_mul hj, Units.inv_mul, secM_one hj]

def secHA (h : HA R' σ J) : HA R σ J :=
  (⟨secGL hj (HA.mat R' σ J h), secM_unitary hj σ J _ (show ↥(HR R' σ J) from h).2⟩ : HR R σ J)

theorem haMap_secHA (φ : R →ₐ[F] R') (hφ : ∀ x, φ (j x) = x) (h : HA R' σ J) :
    haMap σ J φ (secHA σ J hj h) = h := by
  apply Subtype.ext
  apply Units.ext
  show (secM j (HA.mat R' σ J h : Matrix (Fin n) (Fin n) (R' ⊗[F] E))).map (tensMap (E := E) φ) =
    (HA.mat R' σ J h : Matrix (Fin n) (Fin n) (R' ⊗[F] E))
  ext i k
  simp [secM, eps, tensMap_Jt φ hφ]

theorem continuous_secM [TopologicalSpace R] [TopologicalSpace R'] (hc : Continuous (Jt (E := E) j)) :
    Continuous (secM (E := E) (n := n) j) := by
  haveI : ContinuousAdd (R ⊗[F] E) := ModuleTopology.continuousAdd R _
  exact (continuous_id.matrix_map hc).add continuous_const

theorem continuous_secHA [TopologicalSpace R] [TopologicalSpace R'] (hc : Continuous (Jt (E := E) j)) :
    Continuous (secHA σ J hj) := by
  have hM : Continuous (secM (E := E) (n := n) j) := continuous_secM hc
  have hG : Continuous (fun h : HA R' σ J => secGL hj (HA.mat R' σ J h)) :=
    Units.continuous_iff.2 ⟨hM.comp (Units.continuous_val.comp continuous_subtype_val),
      hM.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩
  exact hG.subtype_mk _

end Grp

end EvalVW

end MassDataLevelSSteps

namespace MassDataLevelSSteps

namespace EvalVSpec

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures
open Formalism.MainNotions.S (AutInst)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]


open Classical in
def singleL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' x y := by
    unfold singleV
    exact RestrictedProduct.single_add _ v x y
  map_smul' c x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    unfold singleV
    exact RestrictedProduct.mul_single _ v x (algebraMap F (Af F) c)

open Classical in
theorem singleV_self (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : (singleV F v x) v = x := by
  unfold singleV
  exact RestrictedProduct.single_eq_same _ v x

open Classical in
theorem singleL_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    singleL v (x * y) = singleL v x * singleL v y := by
  have h := RestrictedProduct.single_mul (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x
    (singleV F v y)
  have e : x * y = x * (singleV F v y) v := by rw [singleV_self]
  exact (congrArg (singleV F v) e).trans h

theorem evalV_singleL (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : evalV F v (singleL v x) = x :=
  singleV_self v x

def uHom (v : HeightOneSpectrum (𝓞 F)) : Fv F v →* Af F where
  toFun a := singleL v a + (1 - singleL v 1)
  map_one' := add_sub_cancel _ _
  map_mul' a b := by
    have hab := singleL_mul v a b
    have h1 : singleL v a * singleL v 1 = singleL v a := by rw [← singleL_mul, mul_one]
    have h2 : singleL v b * singleL v 1 = singleL v b := by rw [← singleL_mul, mul_one]
    have h3 : singleL v (1 : Fv F v) * singleL v 1 = singleL v 1 := by rw [← singleL_mul, mul_one]
    linear_combination hab + h1 + h2 - h3

theorem continuous_uHom (v : HeightOneSpectrum (𝓞 F)) : Continuous (uHom v) :=
  (PI.VolStabSW.SdUniqW.continuous_singleV v).add continuous_const

theorem uHom_mul_single (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    uHom v a * singleL v b = singleL v (a * b) := by
  show (singleL v a + (1 - singleL v 1)) * singleL v b = singleL v (a * b)
  rw [add_mul, sub_mul, one_mul, ← singleL_mul, ← singleL_mul, one_mul, sub_self, add_zero]

theorem Jt_smul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (z : Fv F v ⊗[F] E) :
    EvalVW.Jt (singleL v) (a • z) = uHom v a • EvalVW.Jt (singleL v) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', EvalVW.Jt_tmul, EvalVW.Jt_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
      uHom_mul_single]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

theorem continuous_Jt_single (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (EvalVW.Jt (E := E) (singleL v)) := by

  let τ : TopologicalSpace (Fv F v ⊗[F] E) := TopologicalSpace.induced (EvalVW.Jt (E := E) (singleL v)) inferInstance
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := ModuleTopology.continuousSMul _ _
  haveI : ContinuousAdd (Af F ⊗[F] E) := ModuleTopology.continuousAdd _ _
  have h1 : @ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) _ _ τ := by
    letI := τ
    refine ⟨continuous_induced_rng.2 ?_⟩
    have e : (EvalVW.Jt (E := E) (singleL v)) ∘ (fun p : Fv F v × (Fv F v ⊗[F] E) => p.1 • p.2) =
        fun p => uHom v p.1 • EvalVW.Jt (E := E) (singleL v) p.2 := funext fun p => Jt_smul v p.1 p.2
    rw [e]
    exact ((continuous_uHom v).comp continuous_fst).smul (continuous_induced_dom.comp continuous_snd)
  have h2 : @ContinuousAdd (Fv F v ⊗[F] E) τ _ := by
    letI := τ
    refine ⟨continuous_induced_rng.2 ?_⟩
    have e : (EvalVW.Jt (E := E) (singleL v)) ∘ (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + p.2) =
        fun p => EvalVW.Jt (E := E) (singleL v) p.1 + EvalVW.Jt (E := E) (singleL v) p.2 :=
      funext fun p => map_add _ _ _
    rw [e]
    exact (continuous_induced_dom.comp continuous_fst).add (continuous_induced_dom.comp continuous_snd)
  exact continuous_iff_le_induced.2 (sInf_le ⟨h1, h2⟩)

end EvalVSpec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)
open scoped TensorProduct

theorem evalVOpen_holds : EvalVOpen := by
  intro I v
  exact EvalVW.isOpenMap_of_section _ (EvalVW.secHA I.cm.sig I.J (EvalVSpec.singleL_mul v))
    (EvalVW.continuous_secHA I.cm.sig I.J _ (EvalVSpec.continuous_Jt_single v))
    (EvalVW.haMap_secHA I.cm.sig I.J (EvalVSpec.singleL_mul v) (evalV I.F v) (EvalVSpec.evalV_singleL v))

theorem haarIdxGlob_holds : HaarIdxGlob :=
  haarIdxGlob_of_finProj finProjOpen_holds

theorem haarIdxLoc_holds : HaarIdxLoc :=
  haarIdxLoc_of_open finProjOpen_holds evalVOpen_holds

end MassDataLevelSSteps
