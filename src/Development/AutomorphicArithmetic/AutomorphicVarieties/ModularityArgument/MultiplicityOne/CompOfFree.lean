module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RIdent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RCountAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ContinuousESp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.AbsCoreA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.HasOfSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.CpUniq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwTrConjEquiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem twTr_conj_equiv : ∀ (G : Type) [Group G] (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (e : ρ.Equiv ρ') (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V), twTr ρ' K K' f (e.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ e.toLinearEquiv.symm.toLinearMap) = twTr ρ K K' f A := by
  intro G _ V V' _ _ _ _ ρ ρ' e K K' f A
  set φ := e.toLinearEquiv with hφ
  have hint : ∀ g v, φ (ρ g v) = ρ' g (φ v) := fun g v => by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    simpa [hφ] using h
  have hint' : ∀ g v', ρ' g v' = φ (ρ g (φ.symm v')) := fun g v' => by
    rw [hint, φ.apply_symm_apply]
  have hmem : ∀ v', v' ∈ fixed ρ' K' ↔ φ.symm v' ∈ fixed ρ K' := by
    intro v'
    show (∀ h : K', ρ' h v' = ((1 : K' →* ℂˣ) h : ℂ) • v') ↔
      (∀ h : K', ρ h (φ.symm v') = ((1 : K' →* ℂˣ) h : ℂ) • φ.symm v')
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    refine forall_congr' fun h => ?_
    rw [hint']
    constructor
    · intro H
      exact (φ.symm_apply_eq.2 H.symm).symm
    · intro H
      rw [H, φ.apply_symm_apply]
  have hlev : levOp ρ' K K' f (φ.conj A) = φ.conj (levOp ρ K K' f A) := by
    have hs := (φ.conj.toAddEquiv).map_finsum (fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A))
    unfold levOp
    rw [map_smul]
    congr 1
    refine Eq.trans ?_ hs.symm
    congr 1
    funext q
    ext v'
    simp [LinearEquiv.conj_apply, hint']
  have hA : φ.toLinearMap ∘ₗ A ∘ₗ φ.symm.toLinearMap = φ.conj A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hA]
  have hmap : (fixed ρ K').map (φ : V →ₗ[ℂ] V') = fixed ρ' K' := by
    ext v'
    rw [Submodule.mem_map_equiv, hmem]
  set L := levOp ρ K K' f A with hL
  have hc : (∀ v ∈ fixed ρ' K', φ.conj L v ∈ fixed ρ' K') ↔ (∀ v ∈ fixed ρ K', L v ∈ fixed ρ K') := by
    constructor
    · intro H v hv
      have h1 : φ v ∈ fixed ρ' K' := (hmem _).2 (by simpa using hv)
      have h2 := (hmem _).1 (H _ h1)
      simpa [LinearEquiv.conj_apply] using h2
    · intro H v' hv'
      rw [hmem]
      simpa [LinearEquiv.conj_apply] using H _ ((hmem _).1 hv')
  unfold twTr
  simp only [hlev]
  by_cases h : ∀ v ∈ fixed ρ K', L v ∈ fixed ρ K'
  · rw [dite_eq_left (hc.2 h), dite_eq_left h]
    let ψ := φ.ofSubmodules _ _ hmap
    have hr : (φ.conj L).restrict (hc.2 h) = ψ.conj (L.restrict h) := by
      ext ⟨v', hv'⟩
      simp [ψ, LinearEquiv.conj_apply, LinearMap.restrict_apply]
    rw [hr, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hc.1 h), dite_eq_right h]

end GlobalTheory.BCT
end

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun

private theorem trc_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (K : Subgroup G) (f : G → ℂ) :
    trc ρ K f = trc ρ' K f := by
  have hid : e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id ∘ₗ e.toLinearEquiv.symm.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact e.toLinearEquiv.apply_symm_apply v
  have h := GlobalTheory.BCT.twTr_conj_equiv G V V' ρ ρ' e K (K ⊓ GlobalTheory.BCT.rStab f ⊓ GlobalTheory.BCT.rStab fun y => f y⁻¹) f LinearMap.id
  rw [hid] at h
  exact h.symm

section Split

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hw]
  trivial

private noncomputable def toUL (hw : IsSplitAt w) (τ : SmIrr (GLw n w)) : SmIrr (UL n w) where
  V := τ.V
  ρ := τ.ρ.comp (UL n w).subtype
  smooth v := (τ.smooth v).preimage continuous_subtype_val
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
    exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, mem_UL hw g⟩ x hx⟩

private theorem isCompU_toUL (hw : IsSplitAt w) {σ : Submodule ℂ (UA E n → ℂ)} {τ : SmIrr (GLw n w)} (h : Cp σ w τ) :
    IsCompU σ w (toUL hw τ) := by
  obtain ⟨-, F, hF0, hFσ, hF⟩ := h
  refine ⟨{ toFun := fun x => ⟨cLoc w x.1, mem_UL hw _⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp) }, fun _ => rfl, (toUL hw τ).irred, F, hF0, hFσ, fun x v => hF x v⟩

private noncomputable def equivOfUL (hw : IsSplitAt w) {τ τ' : SmIrr (GLw n w)} (e : (toUL hw τ).ρ.Equiv (toUL hw τ').ρ) : τ.ρ.Equiv τ'.ρ :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' ⟨g, mem_UL hw g⟩

end Split

theorem UpperTheory.V.Z.Mult.cpUniq :
    UpperTheory.V.Z.Mult.CpUniq := by
  intro E _ _ _ hU n hn σ hσ w hw τ τ' h h'
  obtain ⟨e⟩ := (GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn σ hσ w).2 (toUL hw τ) (toUL hw τ') (isCompU_toUL hw h) (isCompU_toUL hw h')
  have e' := equivOfUL hw e
  exact ⟨fun B hB => GlobalTheory.PrinSat.hasSatGL_of_equiv e'.symm hB, fun f => trc_of_equiv e' _ f⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ChoiceM
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)

theorem UpperTheory.V.Z.Mult.choiceM :
    UpperTheory.V.Z.Mult.ChoiceM := by
  classical
  intro E _ _ _ n hn π hns μ e hμ S hS K' hK' hKn
  obtain ⟨-, hc, hInf, hSec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hbad : {w : Pl E | ¬ (((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (((GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E n π).and
      (GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ).1).and hK'.2)
  obtain ⟨Bd, hBd⟩ : ∃ Bd : Finset (Pl E), ∀ w, w ∈ Bd ↔
      ¬ (((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w) :=
    ⟨hbad.toFinset, fun w => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hgood : ∀ w, w ∉ Bd → ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w := fun w hw => by
    by_contra h
    exact hw ((hBd w).2 h)
  have hsplit : ∀ w ∈ Bd, IsSplitAt w := fun w hw => by
    by_contra hs
    exact (hBd w).1 hw ⟨⟨hns w hs, fun x hx => by
      rw [hμ.2.2.1 w hs]
      exact GlobalTheory.CompanionTheory.MuOpen.unrChar_apply_of_isUnitAt w _ x hx⟩, hKn w hs⟩
  have hcs : ∀ w, IsSplitAt w → IsSplitAt (cPl w) := fun w hw =>
    (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hw).symm)
  obtain ⟨m, hm, hmS⟩ : ∃ m : Pl E → Pl E, (∀ w, m w ∈ S ∧ (m w = w ∨ m w = cPl w)) ∧ ∀ w ∈ S, m w = w :=
    ⟨fun w => if w ∈ S then w else cPl w, fun w => by
      by_cases h : w ∈ S
      · simp [h]
      · simpa [h] using ((hSec S hS w).1.resolve_left h), fun w h => by simp [h]⟩
  have hms : ∀ w, IsSplitAt w → IsSplitAt (m w) := fun w hw => by
    rcases (hm w).2 with e | e
    · rwa [e]
    · rw [e]; exact hcs w hw
  obtain ⟨w₀, hw₀, hw₀'⟩ := (hInf.diff (Bd ∪ Bd.image cPl).finite_toSet).nonempty
  have hn₀ : w₀ ∉ Bd := fun h => hw₀' (by simp [h])
  have hn₁ : cPl w₀ ∉ Bd := fun h => hw₀' (by
    refine Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, (hc w₀).1⟩)))
  obtain ⟨w₁, hw₁, hw₁S, hw₁s⟩ : ∃ w₁, w₁ ∉ Bd ∧ w₁ ∈ S ∧ IsSplitAt w₁ := by
    refine ⟨m w₀, ?_, (hm w₀).1, hms w₀ hw₀⟩
    rcases (hm w₀).2 with e | e <;> rwa [e]
  choose! B hB using fun w (h : ∃ B, (CG.mk π).HasSat w B) => h
  choose τ hτ using fun w => GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
  obtain ⟨b, hb⟩ := (hgood w₁ hw₁).1.1
  obtain ⟨g, h1, h2, h3⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regFn E n w₁ (τ w₁) b
    (((GlobalTheory.Cong.satake_locComp E n π w₁ (τ w₁) (hτ w₁).1).1 b).1 hb)
  refine ⟨insert w₁ (Bd.image m), B, τ, w₁, g, fun w hw => ?_, fun w hw hwZ => ?_, fun w hw => ?_,
    fun w _ => (hτ w).1, Finset.mem_insert_self _ _, h1, h2, h3⟩
  · rcases Finset.mem_insert.1 hw with rfl | h
    · exact ⟨hw₁S, hw₁s⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hm u).1, hms u (hsplit u hu)⟩
  · refine (hgood w fun h => hwZ ?_).2
    have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
    rwa [hmS w hw] at hi
  · have hw' : w ∉ Bd := fun h => by
      have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
      rcases (hm w).2 with e | e
      · exact hw.1 (e ▸ hi)
      · exact hw.2 (e ▸ hi)
    exact ⟨hB w (hgood w hw').1.1, (hgood w hw').1.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LcLev
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryBC GlobalTheory.LFun Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Mult.lcLev :
    UpperTheory.V.Z.Mult.LcLev := by
  intro E _ _ _ n w hw f hf
  obtain ⟨K', hKo, hKle, hK⟩ := hf
  have hU : UL n w = ⊤ := if_pos hw
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨K'.subgroupOf (UL n w), hKo.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_subgroupOf.mp hx))
  · exact hK.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal
  · intro k hk x
    exact hK.2 k.1 (Subgroup.mem_subgroupOf.mp hk) x.1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RelIndexGlobNe
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

namespace UpperTheory.V.Z.Mult.LevelTrace

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem mem_fixed_iff (ρ : Representation ℂ G V) (U : Subgroup G) (v : V) :
    v ∈ fixed ρ U ↔ ∀ k ∈ U, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

private theorem fixed_anti (ρ : Representation ℂ G V) {U₂ U₁ : Subgroup G} (h : U₂ ≤ U₁) :
    fixed ρ U₁ ≤ fixed ρ U₂ := fun v hv =>
  (mem_fixed_iff ρ U₂ v).2 fun k hk => (mem_fixed_iff ρ U₁ v).1 hv k (h hk)

private theorem trOn_eq_of_range (M₁ M₂ : Submodule ℂ V) [FiniteDimensional ℂ M₁] [FiniteDimensional ℂ M₂]
    (hle : M₂ ≤ M₁) (L₁ L₂ : V →ₗ[ℂ] V) (h : ∀ v ∈ M₁, L₁ v ∈ M₂) (he : ∀ v ∈ M₂, L₁ v = L₂ v) :
    trOn M₁ L₁ = trOn M₂ L₂ := by
  have h₁ : ∀ v ∈ M₁, L₁ v ∈ M₁ := fun v hv => hle (h v hv)
  have h₂ : ∀ v ∈ M₂, L₂ v ∈ M₂ := fun v hv => by
    rw [← he v hv]
    exact h v (hle hv)
  unfold trOn
  rw [dite_eq_left h₁, dite_eq_left h₂]
  let g : M₁ →ₗ[ℂ] M₂ := L₁.restrict h
  let i : M₂ →ₗ[ℂ] M₁ := Submodule.inclusion hle
  have e₁ : L₁.restrict h₁ = i ∘ₗ g := by
    ext v
    rfl
  have e₂ : L₂.restrict h₂ = g ∘ₗ i := by
    ext v
    exact (he v v.2).symm
  rw [e₁, e₂]
  exact LinearMap.trace_comp_comm' g i

private theorem apply_finsum (ρ : Representation ℂ G V) (U : Subgroup G) (F : G → ℂ) (v : V) :
    (∑ᶠ q : G ⧸ U, F q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))) v = ∑ᶠ q : G ⧸ U, F q.out • ρ q.out v := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hinj : ∀ g : G, ρ g v ≠ 0 := by
    intro g h0
    apply hv
    have h1 : ρ g⁻¹ (ρ g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [← h1, h0, map_zero]
  have hs : (Function.support fun q : G ⧸ U => F q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))) =
      Function.support fun q : G ⧸ U => F q.out • ρ q.out v := by
    ext q
    simp only [Function.mem_support]
    constructor
    · intro h h0
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact h (by rw [h1, zero_smul])
      · exact hinj _ h1
    · intro h h0
      apply h
      have := congrArg (fun L : V →ₗ[ℂ] V => L v) h0
      simpa using this
  by_cases hf : (Function.support fun q : G ⧸ U => F q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite
  · exact map_finsum (LinearMap.applyₗ v) hf
  · rw [finsum_of_infinite_support hf, finsum_of_infinite_support (hs ▸ hf)]
    simp

private theorem out_inv {X : Type} (U : Subgroup G) (c : G → X) (hc : ∀ u ∈ U, ∀ x, c (x * u) = c x) (g : G) :
    c (Quotient.out (g : G ⧸ U)) = c g := by
  have h : (Quotient.out (g : G ⧸ U))⁻¹ * g ∈ U := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have := hc _ h (Quotient.out (g : G ⧸ U))
  rw [mul_inv_cancel_left] at this
  exact this.symm

private theorem levOp_mem_fixed (ρ : Representation ℂ G V) (K U₂ U₁ : Subgroup G) (F : G → ℂ)
    (hl : ∀ k ∈ U₁, ∀ x, F (k * x) = F x) (hr : ∀ k ∈ U₂, ∀ x, F (x * k) = F x) {v : V} (hv : v ∈ fixed ρ U₂) :
    levOp ρ K U₂ F LinearMap.id v ∈ fixed ρ U₁ := by
  have hfix := (mem_fixed_iff ρ U₂ v).1 hv
  rw [mem_fixed_iff]
  intro k hk
  let c : G → V := fun g => F g • ρ g v
  have hc : ∀ u ∈ U₂, ∀ x, c (x * u) = c x := by
    intro u hu x
    simp only [c]
    rw [hr u hu x, map_mul, Module.End.mul_apply, hfix u hu]
  let e : V ≃+ V :=
    { toFun := ρ k
      invFun := ρ k⁻¹
      left_inv := fun x => by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      right_inv := fun x => by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      map_add' := map_add _ }
  have key : ∀ q : G ⧸ U₂, e (c q.out) = c ((k • q : G ⧸ U₂).out) := by
    intro q
    have hq : k • q = ((k * q.out : G) : G ⧸ U₂) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, out_inv U₂ c hc]
    show ρ k (F q.out • ρ q.out v) = F (k * q.out) • ρ (k * q.out) v
    rw [hl k hk, map_smul, map_mul, Module.End.mul_apply]
  have hsum : ρ k (∑ᶠ q : G ⧸ U₂, c q.out) = ∑ᶠ q : G ⧸ U₂, c q.out := by
    show e (∑ᶠ q : G ⧸ U₂, c q.out) = _
    rw [AddEquiv.map_finsum, finsum_congr key]
    exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ U₂ => c q.out)
  unfold levOp
  rw [LinearMap.smul_apply, apply_finsum, map_smul]
  exact congrArg _ hsum

private theorem finsum_fibre {U₂ U₁ : Subgroup G} (hle : U₂ ≤ U₁) (hN : U₂.relIndex U₁ ≠ 0) (c : G → V)
    (hc : ∀ u ∈ U₁, ∀ x, c (x * u) = c x) :
    ∑ᶠ q : G ⧸ U₂, c q.out = U₂.relIndex U₁ • ∑ᶠ p : G ⧸ U₁, c p.out := by
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite (U₁ ⧸ U₂.subgroupOf U₁) := Nat.finite_of_card_ne_zero hN
  have h1 : ∀ q : G ⧸ U₂, c q.out = c (e q).1.out := by
    intro q
    have : (e q).1 = ((q.out : G) : G ⧸ U₁) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this, out_inv U₁ c hc]
  rw [finsum_congr h1, finsum_comp_equiv e (f := fun x : (G ⧸ U₁) × (U₁ ⧸ U₂.subgroupOf U₁) => c x.1.out)]
  by_cases hb : (Function.support fun p : G ⧸ U₁ => c p.out).Finite
  · have hs : (Function.support fun x : (G ⧸ U₁) × (U₁ ⧸ U₂.subgroupOf U₁) => c x.1.out).Finite :=
      (hb.prod (Set.finite_univ (α := U₁ ⧸ U₂.subgroupOf U₁))).subset fun x hx => ⟨hx, trivial⟩
    rw [finsum_curry _ hs]
    have h2 : ∀ p : G ⧸ U₁, ∑ᶠ _ : U₁ ⧸ U₂.subgroupOf U₁, c p.out = U₂.relIndex U₁ • c p.out := by
      intro p
      haveI := Fintype.ofFinite (U₁ ⧸ U₂.subgroupOf U₁)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ]
      simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
    simp only [h2]
    exact (map_finsum (nsmulAddMonoidHom (U₂.relIndex U₁)) hb).symm
  · rw [finsum_of_infinite_support hb, smul_zero, finsum_of_infinite_support]
    intro hfin
    apply hb
    refine (hfin.image Prod.fst).subset fun p hp => ?_
    exact ⟨(p, ((1 : U₁) : U₁ ⧸ U₂.subgroupOf U₁)), hp, rfl⟩

private theorem levOp_eq (ρ : Representation ℂ G V) (K U₂ U₁ : Subgroup G) (F : G → ℂ) (hle : U₂ ≤ U₁) (hK : U₁ ≤ K)
    (hN : U₂.relIndex U₁ ≠ 0) (hr : ∀ k ∈ U₁, ∀ x, F (x * k) = F x) {v : V} (hv : v ∈ fixed ρ U₁) :
    levOp ρ K U₂ F LinearMap.id v = levOp ρ K U₁ F LinearMap.id v := by
  have hfix := (mem_fixed_iff ρ U₁ v).1 hv
  have hc : ∀ u ∈ U₁, ∀ x, (fun g : G => F g • ρ g v) (x * u) = (fun g : G => F g • ρ g v) x := by
    intro u hu x
    simp only
    rw [hr u hu x, map_mul, Module.End.mul_apply, hfix u hu]
  have hs := finsum_fibre hle hN (fun g : G => F g • ρ g v) hc
  unfold levOp
  rw [LinearMap.smul_apply, LinearMap.smul_apply, apply_finsum, apply_finsum, hs,
    ← Subgroup.relIndex_mul_relIndex U₂ U₁ K hle hK, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hN' : ((U₂.relIndex U₁ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [Nat.cast_mul, mul_inv, mul_right_comm, inv_mul_cancel₀ hN', one_mul]

private theorem trOn_levOp_eq (ρ : Representation ℂ G V) (K U₂ U₁ : Subgroup G) (F : G → ℂ) (hle : U₂ ≤ U₁)
    (hK : U₁ ≤ K) (hN : U₂.relIndex U₁ ≠ 0) (hr : ∀ k ∈ U₁, ∀ x, F (x * k) = F x) (M₂ M₁ : Submodule ℂ V)
    [FiniteDimensional ℂ M₂] [FiniteDimensional ℂ M₁] (hM : M₁ ≤ M₂) (hfix : M₁ ≤ fixed ρ U₁)
    (hmap : ∀ v ∈ M₂, levOp ρ K U₂ F LinearMap.id v ∈ M₁) :
    trOn M₂ (levOp ρ K U₂ F LinearMap.id) = trOn M₁ (levOp ρ K U₁ F LinearMap.id) :=
  trOn_eq_of_range M₂ M₁ hM _ _ hmap fun _ hv => levOp_eq ρ K U₂ U₁ F hle hK hN hr (hfix hv)

end Generic

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem globLev_mono (S : Set (Pl E)) {K₂ K₁ : ∀ w : Pl E, Subgroup (UL n w)} (h : ∀ w, K₂ w ≤ K₁ w) :
    globLev S K₂ ≤ globLev S K₁ := by
  intro k hk
  rw [mem_globLev_iff] at hk ⊢
  intro w hw
  obtain ⟨a, ha, e⟩ := hk w hw
  exact ⟨a, h w ha, e⟩

private theorem relIndex_glob_ne (hU : GlobalTheory.BCT.Unr E) (S : Set (Pl E)) (hS : IsSection S)
    (K : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K) :
    (globLev S K).relIndex (globLev S (KL n)) ≠ 0 := by
  have h := HopLev2.relIndex_globLev hU S hS K (fun w => (hK.1 w).2.1) hK.2
  have h2 : (∏ᶠ w ∈ S, (((K w).relIndex (KL n w) : ℕ) : ℂ)) ≠ 0 :=
    finprod_mem_induction (· ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun w _ =>
      Nat.cast_ne_zero.2 (GlobalTheory.LocFinU.relIndex_ne_zero_of_subset_cpt _ _ (hK.1 w).1 _
        (GlobalTheory.LocFinU.isCompact_KL n w) subset_rfl)
  rw [← h] at h2
  exact_mod_cast h2

private theorem forms_le_fixed (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K : ∀ w : Pl E, Subgroup (UL n w)) : forms S lam K ≤ fixed (RF E n) (globLev S K) :=
  iSup₂_le fun _ _ => inf_le_right

private theorem forms_mono (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    {K₂ K₁ : ∀ w : Pl E, Subgroup (UL n w)} (h : ∀ w, K₂ w ≤ K₁ w) : forms S lam K₁ ≤ forms S lam K₂ :=
  iSup₂_mono fun _ _ => inf_le_inf_left _ (fixed_anti _ (globLev_mono S h))

private theorem hop_mem_forms (S : Set (Pl E)) (hS : IsSection S) (lam : InfinitePlace E → DomWeight n)
    (K₂ K₁ : ∀ w : Pl E, Subgroup (UL n w))
    (hK₂ : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₂)
    (hUle : globLev S K₂ ≤ globLev S K₁) (f : ∀ w : Pl E, UL n w → ℂ) (hf₂ : GlobalTheory.BCT.IsTest (KL n) K₂ f)
    (hl : ∀ k ∈ globLev S K₁, ∀ x, globFn S f (k * x) = globFn S f x)
    (hr : ∀ k ∈ globLev S K₂, ∀ x, globFn S f (x * k) = globFn S f x) :
    ∀ v ∈ forms S lam K₂, hop S K₂ f v ∈ forms S lam K₁ := by
  have hmap : forms S lam K₂ ≤ (forms S lam K₁).comap (hop S K₂ f) := by
    refine iSup₂_le fun π hπ v hv => ?_
    have h1 : hop S K₂ f v ∈ π ⊓ fixed (RF E n) (globLev S K₂) :=
      GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms E n S hS K₂ hK₂ f hf₂ π hπ.1 v hv
    have h2 : levOp (RF E n) (globLev S (KL n)) (globLev S K₂) (globFn S f) LinearMap.id v ∈
        fixed (RF E n) (globLev S K₁) :=
      levOp_mem_fixed (RF E n) (globLev S (KL n)) (globLev S K₂) (globLev S K₁) (globFn S f) hl hr
        (Submodule.mem_inf.1 hv).2
    have h3 : π ⊓ fixed (RF E n) (globLev S K₁) ≤ forms S lam K₁ := by
      unfold forms
      exact le_iSup₂_of_le π hπ le_rfl
    exact h3 (Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 h1).1, h2⟩)
  exact fun v hv => hmap hv

end Global

end UpperTheory.V.Z.Mult.LevelTrace

open UpperTheory.V.Z.Mult.LevelTrace in
theorem UpperTheory.V.Z.Mult.levTr :
    UpperTheory.V.Z.Mult.LevTr := by
  intro E _ _ _ hU n hn S hS lam K' K'' hK' hK'' hle f hf
  have hf'' : GlobalTheory.BCT.IsTest (KL n) K'' f :=
    ⟨fun w => ⟨(hf.1 w).1, fun k hk => (hf.1 w).2 k (hle w hk)⟩, hf.2⟩
  have hUle : globLev S K'' ≤ globLev S K' := globLev_mono S hle
  have hK0 : globLev S K' ≤ globLev S (KL n) := globLev_mono S fun w => (hK'.1 w).2.1
  have hN : (globLev S K'').relIndex (globLev S K') ≠ 0 := by
    have := relIndex_glob_ne hU S hS K'' hK''
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hUle hK0] at this
    exact left_ne_zero_of_mul this
  have hF := globFn_inv S K' f fun w => (hf.1 w).2
  haveI := (GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K' hK').1
  haveI := (GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K'' hK'').1
  exact trOn_levOp_eq (RF E n) (globLev S (KL n)) (globLev S K'') (globLev S K') (globFn S f) hUle hK0 hN
    (fun k hk x => (hF k hk x).2) (forms S lam K'') (forms S lam K') (forms_mono S lam hle)
    (forms_le_fixed S lam K')
    (hop_mem_forms S hS lam K'' K' hK'' hUle f hf'' (fun k hk x => (hF k hk x).1)
      (fun k hk x => (hF k (hUle hk) x).2))
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.GeomTr
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

theorem UpperTheory.V.Z.Mult.geomTr :
    UpperTheory.V.Z.Mult.GeomTr := by
  intro E _ _ _ hU n hn S hS lam K' hK'
  refine ⟨dimW_ne_zero lam, fun f hf hsep => ?_⟩
  have hOrb : geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) =
      geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) := by
    unfold geomURat
    refine finsum_congr fun c => ?_
    split_ifs with hc
    · exact congrArg (_ * ·) (GlobalTheory.T.twistedOrbitalIntegral_product_eq_finprod E hU n hn S hS K' hK' f hf c.rep hc)
    · rfl
  rw [GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses E hU n hn S hS lam K' hK' f hf hsep, hOrb,
    GlobalTheory.PreStabU.geomURat_eq_geomU E hU n hn S hS lam K' hK' f hf hsep]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.OffSec
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Mult.offSec :
    UpperTheory.V.Z.Mult.OffSec := by
  intro E _ _ _ n S K' K'' h
  unfold GlobalTheory.BCT.globLev
  refine iInf_congr fun w => iInf_congr fun hw => ?_
  rw [h w hw]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockSA
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableSA
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.stableSA :
    Enlarge → Places → StableBlockGA → StableBlockSA := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn l₁ l₂
  obtain ⟨c₀, hc₀, hl⟩ := hG E hunr n hn l₁ l₂
  refine ⟨c₀, hc₀, fun π hreg hd hinf S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl π hreg hd hinf S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableGA
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CmbPiA
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem isTestH_sum {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {J : Type} (s : Finset J)
    (f : J → H E a b → ℂ) (h : ∀ j ∈ s, IsTestH (f j)) : IsTestH (∑ j ∈ s, f j) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨continuous_zero, HasCompactSupport.zero⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩

private theorem isTestH_trM {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type} [Fintype ι]
    (Φ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) (h : IsTestM Φ) : IsTestH (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  rw [e]
  refine isTestH_sum _ _ fun i _ => isTestH_sum _ _ fun j _ => ?_
  exact ⟨(h i j).1.mul continuous_const, (h i j).2.mul_right⟩

private theorem lef_zero (lam : Fin 0 → ℤ) (μ : Measure (G 0)) [μ.IsHaarMeasure] (k : Mat 0 → ((lefE 0 lam).V →L[ℂ] (lefE 0 lam).V))
    (val : Inf 0 → ℂ) (T : ℝ) (hm : IsMult μ (lefE 0 lam) k val T) :
    (μ.real Set.univ : ℂ) * phiOf (lefE 0 lam) (lefT 0 lam) k 1 = val (infOf lam) := by
  haveI : BorelSpace (G 0) := ⟨rfl⟩
  have h := ((lefModel 0 lam (fun i => i.elim0)).2.2.2 μ k val T hm).2 1 (fun i => i.elim0)
    (Subsingleton.elim _ _) (fun a => a.elim0) (Function.injective_of_subsingleton _)
  have e : (fun x : G 0 => phiOf (lefE 0 lam) (lefT 0 lam) k (PositivityTheory.RgTw.tw x 1)) =
      fun _ => phiOf (lefE 0 lam) (lefT 0 lam) k 1 := by
    funext x
    rw [Subsingleton.elim (PositivityTheory.RgTw.tw x 1) 1]
  have h2 := h.2
  rw [e, integral_const] at h2
  simpa [weylChar] using h2

private theorem real_univ_ne (μ : Measure (G 0)) [μ.IsHaarMeasure] : (μ.real Set.univ : ℂ) ≠ 0 := by
  have h1 : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have h2 : μ Set.univ ≠ ⊤ := (Set.subsingleton_of_subsingleton.isCompact.measure_lt_top).ne
  exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩)

def CmbPiA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (l₁ : InfinitePlace E → DomWeight n) (l₂ : InfinitePlace E → DomWeight 0) (D : Dom E n 0) (A : Ar l₁ l₂ D)
    (u₁ : GL (Fin n) E) (u₂ : GL (Fin 0) E), IsTransl u₁ → ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (l₁ v))) →
    ∀ S : Set (Pl E), IsSection S →
    ∀ Z : Finset (Pl E), SplitIn S Z → ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
    (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) → (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, ‖c‖ = c₀ ∧
    ∀ (L : Lv n 0 Z) φ T (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (C : Cmb A.blk) (R : ℝ), L.Fix φ → TEv S T e₂ →
      Disjoint T Z → C.Ok (rt u₁ u₂ (A.fx S L T φ e₁ e₂)) R → IsTwTr D.μ π (trM C.Φ A.tw)
        (c * C.val (chi l₁) (chi l₂) * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1)) * val T e₁ e₂ B 0)

theorem cmbPiA : UpperTheory.V.Z.Mult.PiTermA → TwTrSum → CmbPiA := by
  intro hPi hSum E _ _ _ hU n hn l l₂ D A u₁ u₂ hu₁
  haveI := A.ha
  haveI := A.hb
  have hμ : D.μ.IsHaarMeasure := by
    obtain ⟨h1, -, h3, h4⟩ := D.haar
    exact { }
  obtain ⟨c₁, hc₁, hP⟩ := hPi E hU n hn l u₁ hu₁ A.μa D.μ A.ha hμ
  obtain ⟨S₀, hS₀⟩ := (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E).1
  have hvol : A.blk.vol ≠ 0 := (ffAlg E n 0 l l₂ D A S₀ hS₀).1
  have hm := real_univ_ne A.μb
  generalize hmdef : (A.μb.real Set.univ : ℂ) = m at hm
  refine ⟨c₁ * ‖A.blk.vol⁻¹‖ * ‖(m⁻¹) ^ Fintype.card (InfinitePlace E)‖,
    mul_pos (mul_pos hc₁ (norm_pos_iff.2 (inv_ne_zero hvol))) (norm_pos_iff.2 (pow_ne_zero _ (inv_ne_zero hm))), ?_⟩
  intro π hreg hdual hl S hS Z hZ B τ hB hτ
  obtain ⟨c₀, hc₀, hc⟩ := hP π hreg hdual hl S hS Z hZ B τ hB hτ
  refine ⟨c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E), by rw [norm_mul, norm_mul, hc₀], ?_⟩
  intro L φ T e₁ e₂ C R hφ hTE hTZ hC
  have hLc : ∀ w ∈ Z, Lc (K2 n 0 w) (φ w) ∧ Lc (K2 n 0 w) (L.ln w) := by
    intro w hw
    have h := positionTest E n 0 S Z L hZ
    exact ⟨(h.2.2 φ hφ).1 w hw, (h.2.2 L.ln h.1).1 w hw⟩
  have hseen : ∀ w ∈ Z, (fun g => seen φ L.ln w (g, 1)) = fun g => φ w (g, 1) := by
    intro w hw
    have h := ((locAlg E n 0 Z L w).2.2.2.1 (φ w) (hφ w hw)).1
    funext g
    simp only [seen, if_pos (hZ w hw).2]
    exact congrFun h (g, 1)
  have hX : (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ L.ln w (g, 1)) =
      ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1) :=
    Finset.prod_congr rfl fun w hw => by rw [hseen w hw]
  generalize (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1)) = X at hX ⊢
  have term : ∀ j ∈ C.s, IsTestH (trM (C.t j).Φ A.tw) ∧ IsTwTr D.μ π (trM (C.t j).Φ A.tw)
      (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X * val T e₁ e₂ B 0) := by
    intro j hj
    obtain ⟨ok, hψ, -, -⟩ := hC j hj
    generalize C.t j = t at ok hψ ⊢
    have hPt := hc φ L.ln hLc T hTZ e₁ e₂ t.ka t.va t.T hTE ok.ka
    rw [hX] at hPt
    have hf : trM t.Φ A.tw = ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) •
        phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) := by
      funext g
      have h1 := tensTr E n 0 (Ml l) (Ml l₂) Unit t.ka t.kb (Tl l) (Tl l₂) t.ψ 1 g
      have hp : (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹ : Hf E n 0) = (finOf E n g.1 * (ratF E n u₁)⁻¹, 1) :=
        Prod.ext rfl (Subsingleton.elim _ _)
      have hg : ∀ v, gInf v g.2 = 1 := fun v => Subsingleton.elim _ _
      have h2 : ∑ x, ∑ y, t.ψ x y (hFin g) * (1 : Matrix Unit Unit ℂ) y x =
          A.blk.vol⁻¹ * finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂) (finOf E n g.1) := by
        rw [hψ]
        simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq, mul_one]
        show A.blk.vol⁻¹ * finFn S _ _ (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹) = _
        rw [hp]
        rfl
      refine h1.trans ?_
      rw [h2]
      simp only [hg, Pi.smul_apply, smul_eq_mul, phiProd]
      show (∏ v, phiOf (lefE n (l v).w) (lefT n (l v).w) (t.ka v) (gInf v g.1)) * _ * _ = _
      have h3 : ∀ v, gInf v g.1 = infAt E n v g.1 := fun v => rfl
      simp only [h3]
      show _ * (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * _ = _
      ring
    have hval : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * t.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 =
        ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) *
          (c₀ * (∏ v, t.va v (infOf (l v).w)) * X * val T e₁ e₂ B 0) := by
      have hb : ∀ v, t.vb v (chi l₂ v) = m * phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1 := fun v => by
        rw [← hmdef]
        exact (lef_zero (l₂ v).w A.μb (t.kb v) (t.vb v) t.T (ok.kb v)).symm
      have e : t.val (chi l) (chi l₂) = (∏ v, t.va v (infOf (l v).w)) *
          (m ^ Fintype.card (InfinitePlace E) * ∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) := by
        show (∏ v, t.va v (chi l v)) * ∏ v, t.vb v (chi l₂ v) = _
        simp only [hb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        rfl
      rw [e, inv_pow]
      field_simp
    have htest : IsTestH (trM t.Φ A.tw) := isTestH_trM _ _ (BlockFiniteConvolution.blkOp₀ E A.blk t t ok ok).1
    refine ⟨htest, ?_⟩
    rw [hval, hf]
    by_cases h0 : (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹ = 0
    · have h := hSum E n D π Empty ∅ (fun _ => 0) (fun _ => 0) (fun _ => 0) (by simp)
      rw [h0, zero_smul, zero_mul]
      simpa using h
    · rw [hf] at htest
      have hPtest : IsTestH (phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))) := by
        refine ⟨(continuous_const_smul_iff₀ h0).1 htest.1, ?_⟩
        have h1 := htest.2.mul_left (f := fun _ => ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹)
        have e : phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) = fun y =>
            ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹ *
              (((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) •
                phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))) y := by
          funext y
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [inv_mul_cancel_left₀ h0]
        rw [e]
        exact h1
      have key : ∀ (s : ℂ) (P : H E n 0 → ℂ) (x : ℂ), IsTestH P → IsTwTr D.μ π P x → IsTwTr D.μ π (s • P) (s * x) := by
        intro s P x h1 h2
        have h := hSum E n D π Unit {()} (fun _ => s) (fun _ => P) (fun _ => x) (fun _ _ => ⟨h1, h2⟩)
        simpa using h
      exact key _ _ _ hPtest hPt
  have hS' := hSum E n D π C.J C.s C.c (fun j => trM (C.t j).Φ A.tw) _ term
  have e1 : trM C.Φ A.tw = ∑ j ∈ C.s, C.c j • trM (C.t j).Φ A.tw := Growth.trM_sum _ _ _ _
  have e2 : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * C.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 =
      ∑ j ∈ C.s, C.c j * (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X *
        val T e₁ e₂ B 0) := by
    rw [Cmb.val, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  exact hS'

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem pow_norm_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (U : H →L[ℂ] H) (k : ℕ) :
    ‖U ^ k‖ ≤ (‖U‖ + 1) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))

private theorem final_bd (κ g t : ℂ) (hκ : κ ≠ 0) (C a b u ρ : ℝ) (N k : ℕ) (hρ : 0 < ρ) (hu : 0 ≤ u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ ρ ^ k) (hb : b ≤ (u + 1) ^ k)
    (h : ‖κ * 1 * g - t / 2‖ ≤ C * (1 + k) ^ N * a + C * b * (ρ / (u + 1)) ^ k) :
    ‖g - t / (2 * κ)‖ ≤ ‖κ‖⁻¹ * (2 * |C|) * (1 + k) ^ N * ρ ^ k := by
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  have e : κ * 1 * g - t / 2 = κ * (g - t / (2 * κ)) := by field_simp
  rw [e, norm_mul] at h
  have h1 : (1 : ℝ) ≤ (1 + k) ^ N := one_le_pow₀ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have h2 : C * (1 + k) ^ N * a ≤ |C| * (1 + k) ^ N * ρ ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) ha ha0 (by positivity)
  have h3 : C * b * (ρ / (u + 1)) ^ k ≤ |C| * (1 + k) ^ N * ρ ^ k := by
    calc C * b * (ρ / (u + 1)) ^ k ≤ |C| * (u + 1) ^ k * (ρ / (u + 1)) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C) hb hb0 (abs_nonneg C)) (by positivity)
      _ = |C| * 1 * ρ ^ k := by
          rw [mul_assoc, ← mul_pow, mul_one]
          congr 2
          field_simp
      _ ≤ _ := by gcongr
  rw [mul_assoc, mul_assoc, le_inv_mul_iff₀ hκ']
  linarith

end UpperTheory.Zero.ConvolutionTheory.EB

open UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Mult.stableGA :
    PiFin → PiAdm → GrowthPiJ → CmbPiA → CuspReadI → UpperTheory.V.Z.Mult.StableBlockGA := by
  intro hFin hAdm hG hPi hR E _ _ _ hE n hn l₁ l₂
  have hSp := specP _ (cuspReadP_inf hR)
  haveI : Nontrivial (InfinitePlace E) := GlobalTheory.T.nontrivial_infinite_place_of_unramified E hE
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  haveI : BorelSpace (GA E 0) := ⟨rfl⟩
  obtain ⟨μ₁, hμ₁⟩ := haarEx E n
  obtain ⟨μ₂, hμ₂⟩ := haarEx E 0
  obtain ⟨D, -, hD⟩ := hG E n hn μ₁ μ₂
  obtain ⟨A⟩ := arEx E n 0 l₁ l₂ D
  obtain ⟨u₁, hu₁⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E n
  obtain ⟨u₂, hu₂⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E 0
  obtain ⟨κ, hκ, hell⟩ := cmbEll E hE n 0 l₁ l₂ D A μ₁ μ₂ hμ₁ hμ₂
  obtain ⟨c₁, hc₁, hl⟩ := hPi E hE n hn l₁ l₂ D A u₁ u₂ hu₁
  refine ⟨c₁ / ‖2 * κ‖, div_pos hc₁ (norm_pos_iff.2 (mul_ne_zero two_ne_zero hκ)),
    fun π hreg hdual hinf S hS Z hZ B τ hB hτ => ?_⟩
  have hθ : ThetaFix π := DiscreteGroups.T1.G.thetaFixOf E n hn π hdual
  obtain ⟨c₀, hc₀, htr⟩ := hl π hreg hdual hinf S hS Z hZ B τ hB hτ
  refine ⟨c₀ / (2 * κ), by rw [norm_div, hc₀], fun φ hφ hrg => ?_⟩
  obtain ⟨L, hL⟩ := lvEx E n 0 Z φ hφ
  obtain ⟨c, hc, htest⟩ := cmbTest E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  obtain ⟨k1, k2, -⟩ := kgFacts E n S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)
  obtain ⟨k3, -, -⟩ := kgFacts E 0 S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)
  have hT := fun W hW => testsEx hAdm E n hn l₁ l₂ D A π hθ (Kg S L.L₁) W k1 k2 hW
  obtain ⟨kp, ko, -⟩ := hT ⊥ inferInstance
  haveI : CompleteSpace ((piSp D π A.blk.I)ᗮ : Submodule ℂ A.blk.Hb) := (Submodule.isClosed_orthogonal _).completeSpace_coe
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hSp E n 0 l₁ l₂ D A S Z L hS hZ {π} Set.subsingleton_singleton
    (fun π' h => by rw [Set.mem_singleton_iff.1 h]; exact hθ.1) (piSp D π A.blk.I)ᗮ ko (fun W hW => (hT W hW).2.2)
  refine ⟨J, hJ, D₁, B₁, fun j => ⟨(a1 j).1 π rfl, fun w hw => ((a1 j).2 w hw).1⟩, fun j => (a2 j).1,
    fun T hTS hd e₁ e₂ ρ hT' hρ hv => ?_⟩
  obtain ⟨U, R, hR, hU, hn'⟩ := a3 T e₁ e₂ ρ ⟨hTS, hT'⟩ hd hρ fun j => by
    rw [valNil E n Z T S (D₂ j) (B₁ j) (B₂ j) e₁ e₂ hS hZ hTS hd fun w hw => ((a1 j).2 w hw).2]
    exact hv j
  obtain ⟨o₁, o₂, r₀, r₁, hr₀, hr₁, hk⟩ := powRep E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hL hR hU
  have b₁ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₁ o₁
  have b₂ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₂ o₂
  have hfin := hFin E n hn D π hθ A.μa A.μb A.ha A.hb _ _ Unit _ _ _ _ _ _ ((Kg S L.L₁).prod (Kg S L.L₂)) o₁.ka o₁.kb o₁.ψ
    (k1.prod k3) (fun x y u hu h => (idmAct E n 0 l₁ l₂ D A S Z L hS hZ).2.1 T φ _ _ hL x y u.1 hu.1 u.2 hu.2 h)
  obtain ⟨C, N, hb⟩ := hD π hθ A.blk.I _ _ _ _ A.tw (c * (1 + r₀)) (c * r₁) (ρ / (‖U‖ + 1)) b₁.1 b₂.1 hfin b₁.2.1 b₂.2.1
    (by positivity) (by positivity) (by positivity)
  obtain ⟨CU, u1, -, u3⟩ := hU
  obtain ⟨v1, v2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 CU _ _ u1
  rw [u3] at v2
  have p1 := powNorm A.blk.Hb (piSp D π A.blk.I) U _ (kp _ _ v1 v2) le_rfl
  have p2 := powNorm A.blk.Hb (piSp D π A.blk.I)ᗮ U ρ (ko _ _ v1 v2) hn'.le
  obtain ⟨-, hs⟩ := seenFam E n 0 S Z L hZ φ T e₁ e₂ hL ⟨hTS, hT'⟩
  refine ⟨‖κ‖⁻¹ * (2 * |C|), N, fun k => ?_⟩
  obtain ⟨Cm, c1, c2, c3⟩ := hk k
  have hrk : 0 ≤ r₀ + k * r₁ := by positivity
  obtain ⟨q1, q2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 Cm _ _ c1
  have ht := (htest φ T _ _ Cm _ hL hrg hrk c1).2
  have he := hell S Z L hS hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k Cm _ hL hrg ⟨hTS, hT'⟩ hrk c1
  have hw := htr L φ T _ _ Cm _ hL (hs k).1 hd c1
  rw [c3] at q2
  have hb' := hb k (U ^ k) Cm.Φ _ q1 q2 (p1 k).1 (p2 k).1
    (by rw [show c * (1 + r₀) + k * (c * r₁) = c * (1 + (r₀ + k * r₁)) by ring]; exact ht) hw
  rw [he, c2, (hs k).2.2.2] at hb'
  have hf := final_bd κ _ _ hκ C _ _ ‖U‖ ρ N k hρ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (p2 k).2 (pow_norm_le U k) hb'
  refine le_of_eq_of_le (congrArg norm ?_) hf
  ring
end
end

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem stableBlockSA : StableBlockSA :=
  stableSA (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues Asm.places) Asm.places
    (stableGA Pi.piFin_holds Pi.piAdm_pf Pi.growthPiJ_holds (UpperTheory.Zero.ConvolutionTheory.EB.cmbPiA piTermA Pi.twTrSum_pf) cuspReadI)

end UpperTheory.V.Z.Mult
end

open UpperTheory.V.Z.Tf UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.V.Z.Mult

theorem noData_free : NoData := fun _ _ _ _ hE _ hn _ π _ hd D h1 h2 _ h4 => h1 (SR.has_of_split hE hn π hd D h2 h4)

theorem compOf_free : CompOf := fun E _ _ _ hE n hn _ π _ hd σ hσ hun hae =>
  (UpperTheory.Gal.Desc.match_of UpperTheory.Gal.Desc.speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
    PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin hE hn π (GOne.unitOf E n hn π hd) σ hσ hun hae).3

theorem mult_free : Mult := by
  have hCount : CountAt := rCountAt compOf_free evalD cpUniq Asm.places
  have hEndo : EndoBlockS :=
    endoS
      (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor
        unitary_one_characters_separated_by_eigenvalues Asm.places)
      Asm.places (UpperTheory.Zero.ConvolutionTheory.EB.endoBlockG cuspReadI)
  have hIdent : Ident :=
    rIdent noData_free hCount geomTr UpperTheory.ConvolutionTheory.G2.g2s
      UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit
      hEndo stableBlockSA
  exact rMult hIdent hCount levTr geomTr levInd lcLev choiceM offSec muEx

end UpperTheory.V.Z.Mult
