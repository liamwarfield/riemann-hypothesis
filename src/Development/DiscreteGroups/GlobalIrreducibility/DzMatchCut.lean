module

public import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepW

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def nmChar {g : ℕ} (K : Type) [Field K] [Algebra (ZMod g) K] (χ : (ZMod g)ˣ →* ℂˣ) : Kˣ →* ℂˣ :=
  χ.comp (Units.map (Algebra.norm (ZMod g) : K →* ZMod g))

end DiscreteGroups.sglob.DzType
end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSep
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepT
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepR
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ}

def whittakerPairingValue (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (W : GL (Fin m) k → ℂ) (x : WT (m := m) ψ) : ℂ :=
  I fun g => (x : GL (Fin m) k → ℂ) g * W g

def pairW (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (W : GL (Fin m) k → ℂ) : WT (m := m) ψ →ₗ[ℂ] ℂ where
  toFun := whittakerPairingValue I W
  map_add' a b := by
    simp only [whittakerPairingValue]
    rw [← map_add (f := _)]; congr 1; funext g
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c a := by
    simp only [whittakerPairingValue, RingHom.id_apply]
    rw [← map_smul]; congr 1; funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

include hψ in
theorem repr_delta (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K)
    {y : WT (m := m) ψ} (hy : ∀ κ ∈ K, rhoW ψ κ y = y) :
    I (fun g => (delta ψ K : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = B y (delta ψ K) := by
  have e : (fun g => (delta ψ K : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = lam ψ hψ I B y •
      fun g => (starRingEnd ℂ) ((delta ψ K : GL (Fin m) k → ℂ) g) * (delta ψ K : GL (Fin m) k → ℂ) g := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
    · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
      rw [delta_mul hK hu hκ, Wf_left hψ hI hB y hu, Wf_apply, hy κ hκ, conj_psi]
      ring
    · rw [delta_eq_zero h]
      ring
  rw [e, map_smul, smul_eq_mul, ← formI_apply, lam_eq hψ hI hB hK hy, lamK]
  exact div_mul_cancel₀ _ (cK_ne_zero hI hK)


include hψ in
theorem repr (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y x : WT (m := m) ψ) :
    I (fun g => (x : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = B y x := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ x y
  have hspan := mem_span_delta hK.1 hK.2.1 x (fun κ hκ => (hKf κ hκ).1)
  refine LinearMap.eqOn_span' (f := pairW I (Wf ψ hψ I B y)) (g := B y) ?_ hspan
  rintro _ ⟨g, hg, rfl⟩
  have hfix : ∀ κ ∈ K.map (MulAut.conj g).toMonoidHom, rhoW ψ κ (rhoW ψ g y) = rhoW ψ g y := by
    intro κ hκ
    have e : κ * g = g * (g⁻¹ * κ * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hKf _ (mem_conj.1 hκ)).2]
  have hF := isTestFun_mul (delta ψ (K.map (MulAut.conj g).toMonoidHom)) (Wf ψ hψ I B (rhoW ψ g y))
    (fun u hu h => Wf_left hψ hI hB _ hu h) (isLocallyConstant_Wf hψ _)
  have h1 := hI.1 _ hF g⁻¹
  have h2 := repr_delta hψ hI hB hg hfix
  show whittakerPairingValue I (Wf ψ hψ I B y) _ = _
  simp only [whittakerPairingValue, rhoW_apply]
  rw [← hB.2.2 g y, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, ← h2,
    ← h1]
  congr 1
  funext h
  rw [Wf_right, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B)

def WSp : Submodule ℂ (GL (Fin m) k → ℂ) where
  carrier := Set.range (Wf ψ hψ I B)
  zero_mem' := ⟨0, Wf_eq_zero hψ hI hB (by simp)⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y + z, Wf_add hψ hI hB y z⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩
    exact ⟨(starRingEnd ℂ) c • y, by rw [Wf_smul hψ hI hB, Complex.conj_conj]⟩

def Phi (y : WT (m := m) ψ) : WSp hψ hI hB := ⟨Wf ψ hψ I B y, y, rfl⟩

def tauRep : Representation ℂ (GL (Fin m) k) (WSp hψ hI hB) where
  toFun x :=
    { toFun := fun w => ⟨fun g => (w : GL (Fin m) k → ℂ) (g * x), by
        obtain ⟨y, hy⟩ := w.2
        exact ⟨rhoW ψ x y, funext fun g => by rw [← Wf_right hψ, hy]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext w g
    simp
  map_mul' x y := by
    ext w g
    simp [mul_assoc]

theorem tauRep_apply (x : GL (Fin m) k) (w : WSp hψ hI hB) (g : GL (Fin m) k) :
    ((tauRep hψ hI hB x w : WSp hψ hI hB) : GL (Fin m) k → ℂ) g = (w : GL (Fin m) k → ℂ) (g * x) := rfl

theorem tauRep_Phi (x : GL (Fin m) k) (y : WT (m := m) ψ) :
    tauRep hψ hI hB x (Phi hψ hI hB y) = Phi hψ hI hB (rhoW ψ x y) :=
  Subtype.ext (funext fun g => Wf_right hψ y g x)

theorem isSmooth_tau : IsSmooth (tauRep hψ hI hB) := fun w => by
  obtain ⟨y, hy⟩ := w.2
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  let S : Subgroup (GL (Fin m) k) :=
    { carrier := {g | tauRep hψ hI hB g w = w}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : K ≤ S := fun κ hκ => by
    show tauRep hψ hI hB κ w = w
    refine Subtype.ext (funext fun g => ?_)
    rw [tauRep_apply, ← hy, Wf_right hψ, hK κ hκ]
  exact Subgroup.isOpen_mono hle hKo

theorem isIrreducible_tau
    (hZ : ∀ Z : Submodule ℂ (WT (m := m) ψ), (∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z) →
      (∀ z ∈ Z, B z z = 0) ∨ ∀ x : WT (m := m) ψ, ∃ z ∈ Z, B (x - z) (x - z) = 0)
    {x₀ : WT (m := m) ψ} (hx₀ : B x₀ x₀ ≠ 0) : (tauRep hψ hI hB).IsIrreducible := by
  have hne : Wf ψ hψ I B x₀ ≠ 0 := fun h => hx₀ (by rw [← repr hψ hI hB x₀ x₀, h]; simp; exact map_zero I)
  haveI : Nontrivial (WSp hψ hI hB) := ⟨⟨Phi hψ hI hB x₀, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (Subrepresentation (tauRep hψ hI hB)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ (WSp hψ hI hB)) this⟩
  have hPadd : ∀ a b, Phi hψ hI hB (a + b) = Phi hψ hI hB a + Phi hψ hI hB b := fun a b =>
    Subtype.ext (Wf_add hψ hI hB a b)
  have hPsmul : ∀ (c : ℂ) a, Phi hψ hI hB (c • a) = (starRingEnd ℂ) c • Phi hψ hI hB a := fun c a =>
    Subtype.ext (Wf_smul hψ hI hB c a)
  have hPof : ∀ w : WSp hψ hI hB, ∃ y, Phi hψ hI hB y = w := fun w => by
    obtain ⟨y, hy⟩ := w.2
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨fun S => ?_⟩
  let Z : Submodule ℂ (WT (m := m) ψ) :=
    { carrier := {y | Phi hψ hI hB y ∈ S.toSubmodule}
      zero_mem' := by
        show Phi hψ hI hB 0 ∈ S.toSubmodule
        have : Phi hψ hI hB 0 = 0 := by rw [← zero_smul ℂ (0 : WT (m := m) ψ), hPsmul, map_zero, zero_smul]
        rw [this]; exact S.toSubmodule.zero_mem
      add_mem' := fun {a b} ha hb => by
        show Phi hψ hI hB (a + b) ∈ S.toSubmodule
        rw [hPadd]; exact S.toSubmodule.add_mem ha hb
      smul_mem' := fun c a ha => by
        show Phi hψ hI hB (c • a) ∈ S.toSubmodule
        rw [hPsmul]; exact S.toSubmodule.smul_mem _ ha }
  have hinv : ∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z := fun g z hz => by
    show Phi hψ hI hB (rhoW ψ g z) ∈ S.toSubmodule
    rw [← tauRep_Phi]; exact S.2 g hz
  rcases hZ Z hinv with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊥
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    obtain ⟨y, rfl⟩ := hPof w
    exact Subtype.ext (Wf_eq_zero hψ hI hB (h y hw))
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊤
    refine Submodule.eq_top_iff'.2 fun w => ?_
    obtain ⟨x, rfl⟩ := hPof w
    obtain ⟨z, hz, h0⟩ := h x
    have e : Phi hψ hI hB x = Phi hψ hI hB (x - z) + Phi hψ hI hB z := by rw [← hPadd, sub_add_cancel]
    rw [e, show Phi hψ hI hB (x - z) = 0 from Subtype.ext (Wf_eq_zero hψ hI hB h0), zero_add]
    exact hz

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem sepOfExtreme : SepOfExtreme := by
  intro hEx hIrr hUA k _ _ _ _ _ m
  obtain ⟨I, hI1, hI2, hI3⟩ := exists_pos_isInvIntegral k m
  have hI : PosInt I := ⟨hI1, hI2, hI3⟩
  refine ⟨I, hI1, fun ψ hψ f hf hsep => ?_⟩
  by_contra hf0
  let x₀ : WT (m := m) ψ := ⟨f, hf⟩
  have hx₀ : x₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨B, hBext, hBf⟩ := hEx _ _ (rhoW ψ) exists_countable_span (formI ψ I) (isInvForm_formI hI) x₀
    (formI_self_ne_zero hI hx₀)
  have hB := hBext.1
  have hZ := hIrr _ _ (rhoW ψ) isSmooth_rhoW exists_fix (fun K hKo hKc => hUA k m K hKo hKc) B hBext
  let τ : IrrRep (GL (Fin m) k) :=
    ⟨WSp hψ hI hB, tauRep hψ hI hB, isSmooth_tau hψ hI hB, isIrreducible_tau hψ hI hB hZ hBf⟩
  let l : Module.Dual ℂ τ.V := (LinearMap.proj (1 : GL (Fin m) k)).comp (WSp hψ hI hB).subtype
  have hl : IsFunctional ψ⁻¹ τ.ρ l := fun u hu w => by
    obtain ⟨y, hy⟩ := w.2
    show (w : GL (Fin m) k → ℂ) (1 * u) = _ * (w : GL (Fin m) k → ℂ) 1
    have h1 := Wf_left hψ hI hB y hu 1
    rw [mul_one] at h1
    rw [one_mul, ← hy, h1]
  have h0 := hsep τ l hl (Phi hψ hI hB x₀)
  have e : (fun g => f g * l (τ.ρ g (Phi hψ hI hB x₀))) =
      fun g => (x₀ : GL (Fin m) k → ℂ) g * Wf ψ hψ I B x₀ g := funext fun g => by
    show f g * Wf ψ hψ I B x₀ (1 * g) = f g * Wf ψ hψ I B x₀ g
    rw [one_mul]
  apply hBf
  rw [← repr hψ hI hB x₀ x₀, ← e]
  exact h0

end DiscreteGroups.sglob.LConv

end
end
