module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
noncomputable section

namespace MassDataLevelSSteps.FrameW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem host_star_conj : Formalism.BasicNotions.bridge_star := by
  intro R H x
  haveI : NumberField.IsCMField H.E := H.isCMField_hostE
  have hemb : ∀ y : H.E, H.φ₀ (star y) = starRingEnd ℂ (H.φ₀ y) := by
    intro y
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj H.φ₀ y
      | exact NumberField.IsCMField.complexEmbedding_complexConj (K := H.E) H.φ₀ y
      | (show H.φ₀ (NumberField.IsCMField.complexConj H.E y) = _
         simp)
      | done
  have h1 : ∀ y, H.φ₀ (H.conj y) = starRingEnd ℂ (H.φ₀ y) :=
    (H.der.conj_iff H.φ₀ H.conj).mpr (by
      unfold Formalism.HC.HostRaw.conj
      exact MulEquiv.apply_symm_apply _ _)
  exact H.φ₀.injective ((hemb x).trans (h1 x).symm)

theorem sig_apply {D : D7} (X : HidaSetting D) (a : X.B.I.E) : X.B.I.cm.sig a = star a := rfl

theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  unfold hE crdOf
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply]
  conv_rhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  have hs : ∀ a : D.host.E,
      X.ιE ((X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) (X.ιE.symm a)) = star a := by
    intro a
    show X.ιE (star (X.ιE.symm a)) = _
    rw [X.ιE_conj, RingEquiv.apply_symm_apply]
    exact (host_star_conj _ D.host a).symm
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, RingEquiv.apply_symm_apply, hs, X.J_eq, LinearMap.map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem frameOf_isStd {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) := by
  refine ⟨fun a b => (hE_crdOf X (X.eX a) (X.eX b)).trans ?_,
    fun a b => (hE_crdOf X (X.fY a) (X.fY b)).trans ?_,
    fun a b => (hE_crdOf X (X.eX a) (X.fY b)).trans ?_,
    fun a => (hE_crdOf X (X.eX a) (X.zu u)).trans ?_,
    fun a => (hE_crdOf X (X.fY a) (X.zu u)).trans ?_,
    (hE_crdOf X (X.zu u) (X.zu u)).trans ?_, ?_⟩
  · rw [X.ee, map_zero]
  · rw [X.ff, map_zero]
  · rw [X.ef]
    split_ifs <;> simp
  · rw [(X.zu_orth u a).1, map_zero]
  · rw [(X.zu_orth u a).2, map_zero]
  · rw [X.zu_norm]
    simp
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact (D.mem u).A.T_prime.ne_zero

end MassDataLevelSSteps.FrameW

namespace MassDataLevelSSteps

theorem frameStd_holds : FrameStd := by
  intro D X w
  exact ⟨_, FrameW.frameOf_isStd X w⟩

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.CMInst
noncomputable section

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cmInst_holds : CMInst := by
  intro D X
  refine ⟨⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩,
    fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  have h' : (starRingEnd X.B.I.E) (X.B.I.J j i) = X.B.I.J i j := by simpa [Formalism.UG.cT] using h
  exact h'

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finHA_mem_Kf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf)
    (hx : x ∈ X.B.I.Kset) :
    finHA X hb x ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb x).2 hx

theorem k2uLeKf_holds : ConjugateLevelLeMaximalCompact := by
  intro D X hb _ hL w
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have h1 := finHA_mem_Kf X hb (X.xu w) (X.xu_K w)
  have h2 := finHA_mem_Kf X hb k (hL.2.1 k hk)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatTop
noncomputable section

namespace MassDataLevelSSteps.LatTop

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation

section Key

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1, m1⟩ := hy
    obtain ⟨N2, h2, m2⟩ := hz
    refine ⟨N1 * N2, mul_ne_zero h1 h2, ?_⟩
    have e1 : (N1 * N2) • y = N2 • (N1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (N1 * N2) • z = N1 • (N2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem m1 N2) (zsmul_mem m2 N1)
  | smul e y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hi : IsIntegral ℤ (c • e) := hint e (Finset.mem_singleton_self e)
    refine ⟨c * N, mul_ne_zero hc hN, ?_⟩
    have e3 : (c * N) • (e • y) = (c • e) • (N • y) := by
      rw [mul_smul, smul_comm N e y, smul_assoc]
    rw [e3]
    have e4 : (c • e) • (N • y) = (IsIntegralClosure.mk' (𝓞 E) (c • e) hi) • (N • y) := by
      rw [← algebraMap_smul E (IsIntegralClosure.mk' (𝓞 E) (c • e) hi) (N • y),
        IsIntegralClosure.algebraMap_mk']
    rw [e4]
    exact L.smul_mem _ m

end Key

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def ratAdd : (Fin n → E) →+ (Fin n → Fv F v ⊗[F] E) :=
  AddMonoidHom.compLeft (inclR (F := F) (Fv F v) : E →+* Fv F v ⊗[F] E).toAddMonoidHom (Fin n)

theorem smul_mem_latLoc (Λ : Set (Fin n → E)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc (E := E) v Λ) : c • y ∈ latLoc (E := E) v Λ :=
  (latLoc (E := E) v Λ).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hy

theorem isCompact_latLoc (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : CompactSpace (v.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v)
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := L)
  let g : s → (Fin n → Fv F v ⊗[F] E) := fun i => ratV (F := F) (Fv F v) ((i.1 : L) : Fin n → E)
  let f : (s → v.adicCompletionIntegers F) → (Fin n → Fv F v ⊗[F] E) :=
    fun c => ∑ i, ((c i : v.adicCompletionIntegers F) : Fv F v) • g i
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun i _ => ?_
    have hi : Continuous fun c : (s → v.adicCompletionIntegers F) =>
        ((c i : v.adicCompletionIntegers F) : Fv F v) := (continuous_apply i).subtype_val
    exact hi.smul (continuous_const : Continuous fun _ : (s → v.adicCompletionIntegers F) => g i)
  have hle : latLoc (E := E) v (L : Set (Fin n → E)) ≤
      Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have key : ∀ x : L, x ∈ Submodule.span ℤ (s : Set L) →
        ratAdd v (x : Fin n → E) ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      | zero =>
        show ratAdd v ((0 : L) : Fin n → E) ∈ _
        simp
      | add x y _ _ hx hy =>
        show ratAdd v ((x + y : L) : Fin n → E) ∈ _
        rw [Submodule.coe_add, map_add (f := _)]
        exact Submodule.add_mem _ hx hy
      | smul k x _ hx =>
        show ratAdd v ((k • x : L) : Fin n → E) ∈ _
        rw [Submodule.coe_smul_of_tower, map_zsmul]
        exact zsmul_mem hx k
    exact key ⟨l, hl⟩ (hs ▸ Submodule.mem_top)
  have e : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = Set.range f := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hle hy)
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      refine Submodule.sum_mem _ fun i _ => smul_mem_latLoc v _ (c i).2 ?_
      exact Submodule.subset_span ⟨_, (i.1 : L).2, rfl⟩
  rw [e]
  exact isCompact_range hf

theorem one_tmul_intCast_mul (N : ℤ) (e : E) :
    (1 : Fv F v) ⊗ₜ[F] ((N : E) * e) = (N : Fv F v) ⊗ₜ[F] e := by
  induction N using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [add_mul, one_mul, TensorProduct.tmul_add, ih, TensorProduct.add_tmul]
  | pred k ih =>
    push_cast at ih ⊢
    rw [sub_mul, one_mul, TensorProduct.tmul_sub, ih, TensorProduct.sub_tmul]

theorem ratV_zsmul_single (N : ℤ) (j : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (N • (Pi.single j e : Fin n → E)) =
      (N : Fv F v) • (Pi.single j ((1 : Fv F v) ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [ratV, inclR, TensorProduct.smul_tmul']
    exact one_tmul_intCast_mul v N e
  · simp [ratV, inclR, h]

end Lat

end MassDataLevelSSteps.LatTop
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uGrpHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLocalCongruence
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem index_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (C : ∀ i, Subgroup (β i)) : (Subgroup.pi Set.univ C).index = ∏ i, (C i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem index_comap_pi {A : Type*} [Group A] {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (φ : A →* ((i : ι) → β i)) (hφ : Function.Surjective φ) (C : ∀ i, Subgroup (β i)) :
    ((Subgroup.pi Set.univ C).comap φ).index = ∏ i, (C i).index := by
  rw [Subgroup.index_comap_of_surjective _ hφ, index_pi_dep]

theorem closure_val_preimage {G : Type*} [Group G] (H T : Subgroup G) :
    Subgroup.closure (Subtype.val ⁻¹' (T : Set G) : Set H) = T.subgroupOf H :=
  Subgroup.closure_eq (T.subgroupOf H)

def CompH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈ Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w)

def CompK : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J),
    h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) →
    haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
      Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v

def ConjugateLevelIsSubgroup : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → ∀ w : D.what₂.Word,
    (1 : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ∧
    (∀ x ∈ K2u X hb w, ∀ y ∈ K2u X hb w, x * y ∈ K2u X hb w) ∧ (∀ x ∈ K2u X hb w, x⁻¹ ∈ K2u X hb w)

def SurjKH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word)
    (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    (∀ p, t p ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) →
    (∀ p, t p ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1) →
    ∃ h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w),
      h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ∧
      ∀ p, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p

def ConjugateLevelLocalCongruence : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ (w : D.what₂.Word)
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) →
    (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h ∈
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1) → h ∈ K2u X hb w

section Der

variable {D : D7} (X : HidaSetting D)

def KvS (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F)) : Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) where
  carrier := Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v
  one_mem' := Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
  mul_mem' := fun {_ _} ha hb => Subgroup.mul_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) ha hb
  inv_mem' := fun {_} ha => Subgroup.inv_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) ha

def concreteLevelAdelicSubset (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hg : ConjugateLevelIsSubgroup) (w : D.what₂.Word) :
    Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) where
  carrier := K2u X hb w
  one_mem' := (hg X hb hK w).1
  mul_mem' := fun {a b} ha hb' => (hg X hb hK w).2.1 a ha b hb'
  inv_mem' := fun {a} ha => (hg X hb hK w).2.2 a ha

def compHom (ha : CompH) (hk : CompK) (w : D.what₂.Word) :
    ↥((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) →*
      ((p : TypX X) → ↥((KvS X p.1).subgroupOf (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))) where
  toFun x := fun p => ⟨⟨haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) x.1.1, ha X w p.1 x.1.1 x.1.2⟩,
    hk X p.1 x.1.1 (Subgroup.mem_subgroupOf.1 x.2)⟩
  map_one' := by
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact map_one _
  map_mul' := by
    intro x y
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact map_mul _ _ _

end Der

theorem globProd_of (ha : CompH) (hk : CompK) (hg : ConjugateLevelIsSubgroup) (hs : SurjKH) (hp : ConjugateLevelLocalCongruence) : GlobProd := by
  intro D X hb hK hT hL w
  classical
  have e1 : idxH X hb w = (((concreteLevelAdelicSubset X hb hK hg w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))).subgroupOf
      ((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))).index := by
    unfold idxH
    rw [show (Subtype.val ⁻¹' K2u X hb w : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((concreteLevelAdelicSubset X hb hK hg w : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) from rfl,
      closure_val_preimage, closure_val_preimage]
    rfl
  have e2 : ∀ p : TypX X, idxHp X hb w p =
      ((((concreteLevelAdelicSubset X hb hK hg w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1))).subgroupOf
        (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))).subgroupOf
        ((KvS X p.1).subgroupOf (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).index := by
    intro p
    unfold idxHp
    rw [show (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
        Set ↥(Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((((concreteLevelAdelicSubset X hb hK hg w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1))) :
        Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) from by
          rw [Subgroup.coe_map]; rfl,
      show (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
        Set ↥(Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((KvS X p.1 : Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) from rfl,
      closure_val_preimage, closure_val_preimage]
    rfl
  rw [e1, Finset.prod_congr rfl (fun p _ => e2 p), ← index_comap_pi (compHom X ha hk w)]
  · congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx p
      exact ⟨x.1.1, hx, rfl⟩
    · intro hx
      exact hp X hb hK hL w x.1.1 x.1.2 (Subgroup.mem_subgroupOf.1 x.2) (fun p => hx p)
  · intro y
    obtain ⟨h, hH, hKf, hh⟩ := hs X w (fun p => (y p).1.1) (fun p => (y p).1.2) (fun p => (y p).2)
    refine ⟨⟨⟨h, hH⟩, Subgroup.mem_subgroupOf.2 hKf⟩, ?_⟩
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact hh p

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

theorem compK_holds : CompK := by
  intro D X v h hh
  exact (Subgroup.mem_iInf.1 hh) v

theorem compH_holds : CompH := by
  intro D X w v h hh
  unfold Hsub at hh ⊢
  rw [mem_stabT] at hh ⊢
  intro b
  funext i
  have hi := congrFun (hh b) i
  change (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j *
      inclR (Af X.B.I.F) (tupH (frameOf X w) b j)) = inclR (Af X.B.I.F) (tupH (frameOf X w) b i) at hi
  change (∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j *
      inclR (Fv X.B.I.F v) (tupH (frameOf X w) b j)) = inclR (Fv X.B.I.F v) (tupH (frameOf X w) b i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← tensMap_inclR (E := X.B.I.E) (evalV X.B.I.F v) (tupH (frameOf X w) b i), ← hi, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

section Fin

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finHA_mul (x y : X.B.I.Gf) : finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), x * y) = (1, x) * (1, y) by simp, map_mul, map_mul, Prod.snd_mul]

theorem finHA_one : finHA X hb 1 = 1 := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), (1 : X.B.I.Gf)) = 1 from rfl, map_one, map_one, Prod.snd_one]

theorem finHA_inv (x : X.B.I.Gf) : finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), x⁻¹) = (1, x)⁻¹ by simp, map_inv, map_inv, Prod.snd_inv]

end Fin

theorem k2uGrp_holds : ConjugateLevelIsSubgroup := by
  intro D X hb hK w
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨finHA X hb 1, ⟨1, hK.1, rfl⟩, ?_⟩
    simp only [finHA_one, mul_one, mul_inv_cancel]
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb', rfl⟩, rfl⟩
    refine ⟨finHA X hb (a * b), ⟨a * b, hK.2.1 a ha b hb', rfl⟩, ?_⟩
    simp only [finHA_mul]
    group
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨finHA X hb a⁻¹, ⟨a⁻¹, hK.2.2.1 a ha, rfl⟩, ?_⟩
    simp only [finHA_inv]
    group

end MassDataLevelSSteps
end
end
