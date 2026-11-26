module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRightInvRightTwisted
namespace GlobalTheory.TwistedInverseSubgroups

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]

def leftInvRightTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (h * g) = f g) ∧ ∀ g, f (g * γ) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

variable {H : Subgroup G} {γ : G} {T : E →ₗ[ℂ] E} {f : G → E}

end GlobalTheory.TwistedInverseSubgroups
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def twInv (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) : Submodule ℂ (G → E) :=
  GlobalTheory.TwistedInverseSubgroups.leftInvRightTwisted Γ g A

def cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) : Submodule ℂ (Γ → E) where
  carrier := {z | ∀ γ δ : Γ, z (γ * δ) = ρ (δ : G) (z γ) + z δ}
  add_mem' := by
    intro z z' h h' γ δ
    simp only [Pi.add_apply, h γ δ, h' γ δ, map_add (f := _)]
    abel
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c z h γ δ
    simp only [Pi.smul_apply, h γ δ, map_smul, smul_add]

def extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : Submodule ℂ (G → E) where
  carrier := {u | (∀ γ ∈ Γ, ∀ x, u (γ * x) - u x = ρ x (u γ - u 1)) ∧ ∀ x, u (x * s) = ρ s (u x)}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2, h2']⟩
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, h1 γ hγ, h1' γ hγ, add_sub_add_comm, map_add (f := _)]
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2]⟩
    simp only [Pi.smul_apply]
    rw [← smul_sub, h1 γ hγ, ← smul_sub, map_smul]

def relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G) : Submodule ℂ (G → E) where
  carrier := {Φ | Φ ∈ twInv Γ (t ^ 3) (ρ (t ^ 3)) ∧
    ∀ x, ρ (t ^ 2) (Φ x) + ρ t (Φ (x * t)) + Φ (x * t ^ 2) = 0}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨Submodule.add_mem _ h1 h1', fun x => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [← add_zero (0 : E)]
    nth_rewrite 1 [← h2 x]
    rw [← h2' x]
    abel
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, fun x => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_add, ← smul_add, h2, smul_zero]

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLe
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem finrank_relThree_add_finrank_twInv_le :
    ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G)
      (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) →
      t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) →
      FiniteDimensional ℂ (relThree Γ ρ t) ∧
        Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤
          Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  intro G _ E _ _ Γ ρ t hmul hone ht hfd
  have h2 : ∀ v, ρ (t ^ 2) v = ρ t (ρ t v) := fun v => by rw [pow_two, hmul]
  have h3 : ∀ v, ρ (t ^ 3) v = ρ t (ρ t (ρ t v)) := fun v => by
    rw [pow_succ t 2, hmul, h2]
  have h6 : ∀ v, ρ t (ρ t (ρ t (ρ t (ρ t (ρ t v))))) = v := fun v => by
    have h : t ^ 3 * t ^ 3 = 1 := by rw [← pow_add]; exact ht
    have h' := hmul (t ^ 3) (t ^ 3) v
    rw [h, hone, h3, h3] at h'
    exact h'.symm
  have e2 : ∀ x : G, x * t * t = x * t ^ 2 := fun x => by rw [pow_two, mul_assoc]
  have e3 : ∀ x : G, x * t * t ^ 2 = x * t ^ 3 := fun x => by
    rw [mul_assoc, ← pow_succ']
  have hle : relThree Γ ρ t ≤ twInv Γ (t ^ 3) (ρ (t ^ 3)) := fun Φ hΦ => hΦ.1
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  let P : twInv Γ (t ^ 3) (ρ (t ^ 3)) →ₗ[ℂ] twInv Γ t (ρ t) :=
    { toFun := fun Φ => ⟨fun x => ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2), by
        obtain ⟨Φ, hΓ, hΦ⟩ := Φ
        refine ⟨fun γ hγ x => ?_, fun x => ?_⟩
        · simp only [mul_assoc, hΓ γ hγ]
        · simp only [e2, e3, hΦ, h2, h3, map_add (f := _)]
          abel⟩
      map_add' := fun Φ Ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        abel
      map_smul' := fun c Φ => by
        ext x
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add] }
  have hP : ∀ Φ x, (P Φ).1 x = ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2) :=
    fun _ _ => rfl
  have hsurj : LinearMap.range P = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨Ψ, hΓ, hΨ⟩
    have hΨ2 : ∀ x, Ψ (x * t ^ 2) = ρ t (ρ t (Ψ x)) := fun x => by rw [← e2, hΨ, hΨ]
    have hΨ3 : ∀ x, Ψ (x * t ^ 3) = ρ t (ρ t (ρ t (Ψ x))) := fun x => by rw [← e3, hΨ2, hΨ]
    refine ⟨⟨fun x => (1 / 3 : ℂ) • ρ t (ρ t (ρ t (ρ t (Ψ x)))), fun γ hγ x => ?_, fun x => ?_⟩, ?_⟩
    · simp only [hΓ γ hγ]
    · simp only [hΨ3, h3, map_smul]
    · ext x
      rw [hP]
      simp only [hΨ, hΨ2, h2, map_smul, h6]
      module
  have hker : Module.finrank ℂ (relThree Γ ρ t) ≤ Module.finrank ℂ (LinearMap.ker P) := by
    let ι : relThree Γ ρ t →ₗ[ℂ] LinearMap.ker P :=
      (Submodule.inclusion hle).codRestrict _ (fun Φ => by
        rw [LinearMap.mem_ker]
        ext x
        rw [hP]
        exact Φ.2.2 x)
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) ?_
    intro a b hab
    exact Submodule.inclusion_injective hle (congrArg Subtype.val hab)
  have hrk := LinearMap.finrank_range_add_finrank_ker P
  rw [hsurj, finrank_top] at hrk
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLeStatement
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) → FiniteDimensional ℂ (relThree Γ ρ t) ∧ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤ Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtension
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

theorem exists_extend_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u : G → E, ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := by
  classical
  let r : G → G := fun x => (Quotient.mk (QuotientGroup.rightRel Γ) x).out
  have hr : ∀ x, x * (r x)⁻¹ ∈ Γ := fun x =>
    QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq
      (Quotient.mk (QuotientGroup.rightRel Γ) x)))
  have hrγ : ∀ (γ : Γ) (x : G), r (γ * x) = r x := fun γ x => by
    have : Quotient.mk (QuotientGroup.rightRel Γ) ((γ : G) * x)
        = Quotient.mk (QuotientGroup.rightRel Γ) x := by
      apply Eq.symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.2
      simp
    simp only [r, this]
  refine ⟨fun x => ρ (r x) (z ⟨x * (r x)⁻¹, hr x⟩), fun γ x => ?_⟩
  have h1 : (⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩ : Γ) = γ * ⟨x * (r x)⁻¹, hr x⟩ := by
    apply Subtype.ext
    simp [hrγ, mul_assoc]
  show ρ (r (γ * x)) (z ⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩) = _
  rw [h1, hz, hrγ, map_add (f := _), ← hmul]
  simp

theorem exists_extn_of_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u ∈ extn Γ ρ s, ∀ γ : Γ, u γ - u 1 = z γ := by
  obtain ⟨u0, hu0⟩ := exists_extend_cocyc Γ ρ hmul z hz
  let u : G → E := fun x => (1 / 4 : ℂ) •
    (u0 x + ρ (s ^ 3) (u0 (x * s)) + ρ (s ^ 2) (u0 (x * s ^ 2)) + ρ s (u0 (x * s ^ 3)))
  have e1 : s * s ^ 3 = 1 := by rw [← hs]; group
  have e2 : s ^ 2 * s ^ 2 = 1 := by rw [← hs]; group
  have e3 : s ^ 3 * s = 1 := by rw [← hs]; group
  have key : ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := fun γ x => by
    simp only [u, mul_assoc, hu0, map_add (f := _), ← hmul, e1, e2, e3, mul_one]
    module
  have key1 : ∀ γ : Γ, u γ - u 1 = z γ := fun γ => by
    have := key γ 1
    rw [mul_one, hone] at this
    rw [this]; abel
  refine ⟨u, ⟨fun γ hγ x => ?_, fun x => ?_⟩, key1⟩
  · have h1 := key ⟨γ, hγ⟩ x
    have h2 := key1 ⟨γ, hγ⟩
    simp only at h1 h2
    rw [h1, h2]; abel
  · have f1 : s * s = s ^ 2 := (pow_two s).symm
    have f2 : s * s ^ 2 = s ^ 3 := by group
    have f3 : s ^ 2 * s = s ^ 3 := by group
    simp only [u, mul_assoc, map_add (f := _), map_smul, ← hmul, e1, e3, f1, f2, f3, mul_one, hone]
    module

def extnToCocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : extn Γ ρ s →ₗ[ℂ] cocyc Γ ρ where
  toFun u := ⟨fun γ => u.1 γ - u.1 1, fun γ δ => by
    have := u.2.1 γ γ.2 δ
    simp only [Subgroup.coe_mul]
    rw [← this]; abel⟩
  map_add' u v := by
    apply Subtype.ext; funext γ
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' c u := by
    apply Subtype.ext; funext γ
    simp [smul_sub]

theorem twInv_le_extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) :
    twInv Γ s (ρ s) ≤ extn Γ ρ s := by
  rintro f ⟨h1, h2⟩
  refine ⟨fun γ hγ x => ?_, h2⟩
  have := h1 γ hγ 1
  rw [mul_one] at this
  rw [h1 γ hγ, this]; simp

theorem finrank_cocyc_add_twInv_le_extn {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (hfd : FiniteDimensional ℂ (extn Γ ρ s)) :
    FiniteDimensional ℂ (cocyc Γ ρ) ∧
      Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s))
        ≤ Module.finrank ℂ (extn Γ ρ s) := by
  have hsurj : Function.Surjective (extnToCocyc Γ ρ s) := by
    rintro ⟨z, hz⟩
    obtain ⟨u, hu, h⟩ := exists_extn_of_cocyc Γ ρ s hmul hone hs z hz
    exact ⟨⟨u, hu⟩, Subtype.ext (funext h)⟩
  refine ⟨Module.Finite.of_surjective _ hsurj, ?_⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (extnToCocyc Γ ρ s)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  let i : twInv Γ s (ρ s) →ₗ[ℂ] LinearMap.ker (extnToCocyc Γ ρ s) :=
    (Submodule.inclusion (twInv_le_extn Γ ρ s)).codRestrict _ (fun f => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext; funext γ
      have := f.2.1 γ γ.2 1
      rw [mul_one] at this
      show f.1 γ - f.1 1 = 0
      rw [this, sub_self])
  have hi : Function.Injective i := by
    intro a b hab
    exact Submodule.inclusion_injective _ (congrArg Subtype.val hab)
  have := LinearMap.finrank_le_finrank_of_injective hi
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtensionStatement
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 4 = 1 → FiniteDimensional ℂ (extn Γ ρ s) → FiniteDimensional ℂ (cocyc Γ ρ) ∧ Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s)) ≤ Module.finrank ℂ (extn Γ ρ s) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeAction
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeAction
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem free_mod_eq {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ)
    (a γ γ' : G) (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) (i j : ℕ)
    (h : γ * a * g ^ i = γ' * a * g ^ j) : i % m = j % m := by
  have key : ∀ (γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ i j : ℕ, i < j → j < m →
      γ * a * g ^ i ≠ γ' * a * g ^ j := by
    intro γ γ' hγ hγ' i j hij hj h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    apply hfree a (d + 1) (by omega) (by omega)
    have e : a * g ^ (d + 1) * a⁻¹ = γ'⁻¹ * γ := by
      have h2 : γ * a * g ^ i = (γ' * a * g ^ (d + 1)) * g ^ i := by
        rw [h, mul_assoc (γ' * a), ← pow_add]
        congr 2
        omega
      have h3 := mul_right_cancel h2
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, ← h3, mul_inv_cancel_right]
    rw [e]
    exact Γ.mul_mem (Γ.inv_mem hγ') hγ
  rw [pow_eq_pow_mod i hg, pow_eq_pow_mod j hg] at h
  rcases lt_trichotomy (i % m) (j % m) with hlt | heq | hlt
  · exact absurd h (key γ γ' hγ hγ' _ _ hlt (Nat.mod_lt _ hm))
  · exact heq
  · exact absurd h.symm (key γ' γ hγ' hγ _ _ hlt (Nat.mod_lt _ hm))

def freeSetoid {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) : Setoid G where
  r x y := ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k
  iseqv :=
    { refl := fun x => ⟨1, Γ.one_mem, 0, by simp⟩
      symm := by
        rintro x y ⟨γ, hγ, k, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k * (m - 1), ?_⟩
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
        have : g ^ k * g ^ (k * (0 + n + 1 - 1)) = 1 := by
          rw [← pow_add]
          have : k + k * (0 + n + 1 - 1) = (0 + n + 1) * k := by
            simp only [zero_add, Nat.add_sub_cancel]
            ring
          rw [this, pow_mul, hg, one_pow]
        rw [mul_assoc, mul_assoc, this, mul_one, inv_mul_cancel_left]
      trans := by
        rintro x y z ⟨γ, hγ, k, rfl⟩ ⟨δ, hδ, l, rfl⟩
        refine ⟨δ * γ, Γ.mul_mem hδ hγ, k + l, ?_⟩
        simp only [pow_add, mul_assoc] }

theorem twInv_apply_pow {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    {Γ : Subgroup G} {g : G} {A : E →ₗ[ℂ] E} {f : G → E} (hf : f ∈ twInv Γ g A) (x : G) (k : ℕ) :
    f (x * g ^ k) = (A ^ k) (f x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, hf.2, ih, pow_succ', Module.End.mul_apply]

theorem finrank_twInv_mul_of_free {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ) (hΓ : Γ.FiniteIndex)
    (hE : FiniteDimensional ℂ E) (hm : 0 < m) (hg : g ^ m = 1) (hA : A ^ m = 1)
    (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) :
    FiniteDimensional ℂ (twInv Γ g A) ∧
      Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  classical
  let s := freeSetoid Γ g m hm hg
  have hs : ∀ x y : G, s.r x y ↔ ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k := fun _ _ => Iff.rfl
  let R := Quotient s
  have hmk : ∀ γ ∈ Γ, ∀ (x : G) (k : ℕ), Quotient.mk s (γ * x * g ^ k) = Quotient.mk s x :=
    fun γ hγ x k => (Quotient.sound (s := s) ((hs _ _).2 ⟨γ, hγ, k, rfl⟩)).symm
  have hout : ∀ x : G, ∃ γ ∈ Γ, ∃ k : ℕ, x = γ * (Quotient.mk s x).out * g ^ k :=
    fun x => (hs _ _).1 (Quotient.mk_out (s := s) x)

  let F : R × Fin m → Quotient (QuotientGroup.rightRel Γ) :=
    fun p => Quotient.mk _ (p.1.out * g ^ (p.2 : ℕ))
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ h
      have h1 := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
      dsimp only at h1
      set γ := d.out * g ^ (j : ℕ) * (c.out * g ^ (i : ℕ))⁻¹ with hγ
      have h2 : 1 * d.out * g ^ (j : ℕ) = γ * c.out * g ^ (i : ℕ) := by
        rw [hγ, mul_assoc _ c.out, inv_mul_cancel_right, one_mul]
      have h3 : d = c := by
        have := congrArg (Quotient.mk s) h2
        rw [hmk 1 Γ.one_mem, hmk γ h1, Quotient.out_eq, Quotient.out_eq] at this
        exact this
      subst h3
      have h4 := free_mod_eq Γ g m hm hg hfree _ _ _ Γ.one_mem h1 _ _ h2
      rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at h4
      rw [Fin.ext h4]
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        obtain ⟨γ, hγ, k, hx⟩ := hout x
        refine ⟨(Quotient.mk s x, ⟨k % m, Nat.mod_lt _ hm⟩), ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.2
        dsimp only
        rw [← pow_eq_pow_mod k hg]
        have : x * ((Quotient.mk s x).out * g ^ k)⁻¹ = γ := by
          rw [mul_inv_eq_iff_eq_mul, ← mul_assoc]
          exact hx
        rw [this]
        exact hγ
  have hcard : Nat.card R * m = Γ.index := by
    have h1 := Nat.card_congr (Equiv.ofBijective F hF)
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)] at h1
    exact h1
  have hR : Finite R := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0, zero_mul] at hcard
    exact hΓ.index_ne_zero hcard.symm
  letI : Fintype R := Fintype.ofFinite R

  let ev : twInv Γ g A →ₗ[ℂ] (R → E) :=
    { toFun := fun f c => (f : G → E) c.out
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    constructor
    · intro f f' h
      apply Subtype.ext
      funext x
      obtain ⟨γ, hγ, k, hx⟩ := hout x
      have h1 : (f : G → E) (Quotient.mk s x).out = (f' : G → E) (Quotient.mk s x).out :=
        congrFun h (Quotient.mk s x)
      rw [hx, twInv_apply_pow f.2, twInv_apply_pow f'.2, f.2.1 γ hγ, f'.2.1 γ hγ, h1]
    · intro φ
      choose γ hγ κ hκ using hout
      have hval : ∀ (x δ : G) (k : ℕ), δ ∈ Γ → x = δ * (Quotient.mk s x).out * g ^ k →
          A ^ κ x = A ^ k := by
        intro x δ k hδ hx
        have := free_mod_eq Γ g m hm hg hfree _ _ _ (hγ x) hδ _ _ ((hκ x).symm.trans hx)
        rw [pow_eq_pow_mod _ hA, this, ← pow_eq_pow_mod _ hA]
      refine ⟨⟨fun x => (A ^ κ x) (φ (Quotient.mk s x)), ?_, ?_⟩, ?_⟩
      · intro δ hδ x
        have e : Quotient.mk s (δ * x) = Quotient.mk s x := by
          simpa using hmk δ hδ x 0
        have := hval (δ * x) (δ * γ x) (κ x) (Γ.mul_mem hδ (hγ x)) (by
          rw [e, mul_assoc, mul_assoc δ, ← mul_assoc (γ x), ← hκ x])
        dsimp only
        rw [this, e]
      · intro x
        have e : Quotient.mk s (x * g) = Quotient.mk s x := by
          simpa using hmk 1 Γ.one_mem x 1
        have := hval (x * g) (γ x) (κ x + 1) (hγ x) (by
          rw [e, pow_succ, ← mul_assoc, ← hκ x])
        dsimp only
        rw [this, e, pow_succ', Module.End.mul_apply]
      · funext c
        have := hval c.out 1 0 Γ.one_mem (by rw [Quotient.out_eq]; simp)
        change (A ^ κ c.out) (φ (Quotient.mk s c.out)) = φ c
        rw [this, Quotient.out_eq]
        simp
  let e := LinearEquiv.ofBijective ev hev
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, ← hcard]
  ring

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeActionStatement
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ), Γ.FiniteIndex → FiniteDimensional ℂ E → 0 < m → g ^ m = 1 → A ^ m = 1 → (∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) → FiniteDimensional ℂ (twInv Γ g A) ∧ Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAdd
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def rightDefect (ρ : G → E →ₗ[ℂ] E) (t : G) : (G → E) →ₗ[ℂ] (G → E) where
  toFun u := fun x => u (x * t) - ρ t (u x)
  map_add' u v := by
    funext x
    simp only [Pi.add_apply, map_add (f := _)]
    abel
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

theorem rightDefect_apply (ρ : G → E →ₗ[ℂ] E) (t : G) (u : G → E) (x : G) :
    rightDefect ρ t u x = u (x * t) - ρ t (u x) := rfl

theorem rightDefect_mem_relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hst : s ^ 2 = t ^ 3) (u : G → E)
    (hu : u ∈ extn Γ ρ s) : rightDefect ρ t u ∈ relThree Γ ρ t := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨ha, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have ha' : ∀ γ ∈ Γ, ∀ x, u (γ * x) = u x + ρ x (u γ - u 1) := by
    intro γ hγ x
    rw [← ha γ hγ x]
    abel
  have hs2 : ∀ x, u (x * t ^ 3) = ρ (t ^ 3) (u x) := by
    intro x
    rw [← hst, pow_two, ← mul_assoc, hb, hb, hρc]
  have p2 : t * t = t ^ 2 := (pow_two t).symm
  have p3 : t ^ 2 * t = t ^ 3 := (pow_succ t 2).symm
  have p3' : t * t ^ 2 = t ^ 3 := (pow_succ' t 2).symm
  simp only [relThree, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, rightDefect_apply]
  refine ⟨?_, ?_⟩
  · show (∀ h ∈ Γ, ∀ g : G, rightDefect ρ t u (h * g) = rightDefect ρ t u g) ∧
      ∀ g : G, rightDefect ρ t u (g * t ^ 3) = ρ (t ^ 3) (rightDefect ρ t u g)
    simp only [rightDefect_apply]
    refine ⟨?_, ?_⟩
    · intro h hh g
      rw [mul_assoc, ha' h hh (g * t), ha' h hh g, map_add (f := _), hρc]
      abel
    · intro g
      have e : g * t ^ 3 * t = g * t * t ^ 3 := by
        rw [mul_assoc, mul_assoc, (Commute.self_pow t 3).eq]
      rw [e, hs2, hs2, map_sub, hρc, hρc, (Commute.self_pow t 3).eq]
  · intro x
    have e1 : x * t * t = x * t ^ 2 := by rw [mul_assoc, p2]
    have e2 : x * t ^ 2 * t = x * t ^ 3 := by rw [mul_assoc, p3]
    rw [e1, e2, hs2, map_sub, map_sub, hρc, hρc, p3', p2]
    abel

theorem eq_zero_of_rightDefect_eq_zero (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (u : G → E)
    (hu : u ∈ extn Γ ρ s) (hΦ : rightDefect ρ t u = 0) (hu1 : u 1 = 0) : u = 0 := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨-, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have hw : ∀ x, u (x * t) = ρ t (u x) := by
    intro x
    have hx := congrFun hΦ x
    rw [rightDefect_apply, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  let H : Subgroup G :=
    { carrier := {g | ∀ x, u (x * g) = ρ g (u x)}
      mul_mem' := by
        intro a b ha hb'
        simp only [Set.mem_ofPred_eq] at ha hb' ⊢
        intro x
        rw [← mul_assoc, hb', ha, hρc]
      one_mem' := by
        simp only [Set.mem_ofPred_eq]
        intro x
        rw [mul_one, h1]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro x
        have hx := ha (x * a⁻¹)
        rw [inv_mul_cancel_right] at hx
        rw [hx, hρc, mul_inv_cancel, h1] }
  have hle : Subgroup.closure ({s, t} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hb
    · exact hw
  rw [hgen] at hle
  funext g
  have hg : g ∈ H := hle (Subgroup.mem_top g)
  have h1g := (show ∀ x, u (x * g) = ρ g (u x) from hg) 1
  rw [one_mul, hu1, map_zero] at h1g
  exact h1g

theorem finrank_extn_le {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v) (hst : s ^ 2 = t ^ 3)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (hE : FiniteDimensional ℂ E)
    (hR : FiniteDimensional ℂ (relThree Γ ρ t)) :
    FiniteDimensional ℂ (extn Γ ρ s) ∧
      Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  have := hE
  have := hR
  have hmem : ∀ u : extn Γ ρ s, ((rightDefect ρ t).comp (extn Γ ρ s).subtype) u ∈ relThree Γ ρ t :=
    fun u => rightDefect_mem_relThree Γ ρ s t hρ hst u.1 u.2
  let Φ : extn Γ ρ s →ₗ[ℂ] relThree Γ ρ t × E :=
    LinearMap.prod (LinearMap.codRestrict (relThree Γ ρ t) ((rightDefect ρ t).comp (extn Γ ρ s).subtype) hmem)
      ((LinearMap.proj (R := ℂ) (φ := fun _ : G => E) (1 : G)).comp (extn Γ ρ s).subtype)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro u hu
    have h1' := congrArg (fun p : relThree Γ ρ t × E => (p.1 : G → E)) hu
    have h2' := congrArg Prod.snd hu
    exact Subtype.ext (eq_zero_of_rightDefect_eq_zero Γ ρ s t hρ h1 hgen u.1 u.2 h1' h2')
  have hfin : FiniteDimensional ℂ (extn Γ ρ s) := FiniteDimensional.of_injective Φ hinj
  refine ⟨hfin, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod] at hle

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAddStatement
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 2 = t ^ 3 → Subgroup.closure ({s, t} : Set G) = ⊤ → FiniteDimensional ℂ E → FiniteDimensional ℂ (relThree Γ ρ t) → FiniteDimensional ℂ (extn Γ ρ s) ∧ Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1
section

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, lcoeff_apply,
    LinearMap.toSpanSingleton_apply]

theorem homogenize_eq_sum (w : ℕ) (p : ℂ[X]) :
    p.homogenize w = ∑ i ∈ Finset.range (w + 1),
      p.coeff i • ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ i * MvPolynomial.X 1 ^ (w - i)) := by
  rw [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← homogenize_monomial hi', ← homogenize_X_pow hi', ← homogenize_smul, smul_X_eq_monomial]

theorem polySlash_eq_aeval (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = MvPolynomial.aeval
      ![C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ), C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)]
      (p.homogenize w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply, homogenize_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

theorem isHomogeneous_lin (a b : ℂ) :
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul b)

theorem homogenize_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).homogenize w = ∑ i ∈ Finset.range (w + 1), MvPolynomial.C (p.coeff i) *
      ((MvPolynomial.C ((g 0 0 : ℤ) : ℂ) * MvPolynomial.X 0 + MvPolynomial.C ((g 0 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ i *
        (MvPolynomial.C ((g 1 0 : ℤ) : ℂ) * MvPolynomial.X 0 +
          MvPolynomial.C ((g 1 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ (w - i)) := by
  apply homogenize_eq_of_isHomogeneous
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := (((isHomogeneous_lin ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)).pow i).mul
      ((isHomogeneous_lin ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)).pow (w - i))).C_mul (p.coeff i)
    rwa [one_mul, one_mul, Nat.add_sub_of_le hi'] at h
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [polySlash_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, ← C_eq_algebraMap, smul_eq_C_mul]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w h (slP w g p) = slP w (g * h) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_eq_aeval w h, homogenize_slP, polySlash_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← C_eq_algebraMap, smul_eq_C_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul]
  congr 3 <;> ring

theorem polySlash_mem_degreeLT (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h1 : ∀ a b : ℂ, (C a * X + C b).natDegree ≤ 1 := fun a b => natDegree_linear_le
  have h2 := natDegree_mul_le_of_le (natDegree_pow_le_of_le i (h1 ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)))
    (natDegree_pow_le_of_le (w - i) (h1 ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)))
  rw [mul_one, mul_one, Nat.add_sub_of_le hi'] at h2
  exact_mod_cast Nat.lt_succ_of_le h2

theorem polySlash_one (w : ℕ) (p : ℂ[X]) (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  have h : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  conv_rhs => rw [p.as_sum_range' (w + 1) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_X_eq_monomial]

theorem polySlash_action (w : ℕ) :
    (∀ (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), slP w g p ∈ degreeLT ℂ (w + 1)) ∧
      (∀ p ∈ degreeLT ℂ (w + 1), slP w 1 p = p) ∧
      ∀ (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), slP w (g * h) p = slP w h (slP w g p) :=
  ⟨polySlash_mem_degreeLT w, polySlash_one w, fun g h p => (polySlash_polySlash w g h p).symm⟩

theorem dvd_trace_sub_two (N : ℕ) (x g : SL(2, ℤ)) (h : x * g * x⁻¹ ∈ CongruenceSubgroup.Gamma1 N) :
    (N : ℤ) ∣ (mat g).trace - 2 := by
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have ht : (mat (x * g * x⁻¹)).trace = (mat g).trace := by
    change (mat (x * g) * mat x⁻¹).trace = _
    rw [Matrix.trace_mul_comm]
    change (mat (x⁻¹ * (x * g))).trace = _
    rw [inv_mul_cancel_left]
  rw [← ht, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Matrix.trace_fin_two]
  push_cast
  rw [h.1, h.2.1]
  norm_num

theorem not_conj_mem (N : ℕ) (hN : 5 ≤ N) (x g : SL(2, ℤ)) (h1 : -2 ≤ (mat g).trace) (h2 : (mat g).trace < 2) :
    x * g * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have := Int.le_of_dvd (by omega) ((dvd_neg).2 (dvd_trace_sub_two N x g h))
  omega

theorem torsion_not_mem (N : ℕ) (hN : 5 ≤ N) (x : SL(2, ℤ)) (k : ℕ) (hk : 0 < k) :
    (k < 4 → x * ModularGroup.S ^ k * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N) ∧
      (k < 6 → x * (ModularGroup.S * ModularGroup.T) ^ k * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N) := by
  constructor <;> intro hk' <;> interval_cases k <;> exact not_conj_mem N hN x _ (by decide) (by decide)

end GlobalTheory.HeckeFamilyMatrices.CocBound

end

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

def rho (w : ℕ) (g : SL(2, ℤ)) : degreeLT ℂ (w + 1) →ₗ[ℂ] degreeLT ℂ (w + 1) :=
  ((slP w (mat g)).comp (degreeLT ℂ (w + 1)).subtype).codRestrict _ (fun p => (polySlash_action w).1 _ _)

theorem rho_mul (w : ℕ) (g h : SL(2, ℤ)) (v : degreeLT ℂ (w + 1)) :
    rho w (g * h) v = rho w h (rho w g v) := by
  apply Subtype.ext
  change slP w (mat (g * h)) v = slP w (mat h) (slP w (mat g) v)
  rw [← (polySlash_action w).2.2]
  rfl

theorem rho_one (w : ℕ) (v : degreeLT ℂ (w + 1)) : rho w 1 v = v := by
  apply Subtype.ext
  change slP w (mat 1) v = v
  exact (polySlash_action w).2.1 _ v.2

theorem rho_pow (w : ℕ) (g : SL(2, ℤ)) (m : ℕ) : rho w g ^ m = rho w (g ^ m) := by
  induction m with
  | zero => ext1 v; simp [rho_one]
  | succ m ih => ext1 v; rw [pow_succ', pow_succ, rho_mul, ← ih]; rfl

theorem rho_pow_eq_one (w : ℕ) (g : SL(2, ℤ)) (m : ℕ) (h : g ^ m = 1) : rho w g ^ m = 1 := by
  rw [rho_pow, h]; ext1 v; exact rho_one w v

def zMap (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Z1 Γ w →ₗ[ℂ] cocyc Γ (rho w) where
  toFun z := ⟨fun γ => ⟨z.1 γ, z.2.1 γ⟩, fun γ δ => Subtype.ext (z.2.2 γ δ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zMap_injective (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Function.Injective (zMap Γ w) := by
  intro z z' h
  apply Subtype.ext
  funext γ
  exact congrArg (fun f : cocyc Γ (rho w) => (f.1 γ : ℂ[X])) h

open ModularGroup in
theorem closure_S_ST : Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  have hS : S ∈ Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) := Subgroup.subset_closure (by simp)
  have hU : S * T ∈ Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) := Subgroup.subset_closure (by simp)
  intro x hx
  rcases hx with rfl | rfl
  · exact hS
  · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hS) hU
    simpa using this

end GlobalTheory.HeckeFamilyMatrices.CocBound

namespace GlobalTheory.HeckeFamilyMatrices


open CocBound ModularGroup in
theorem finrank_eichlerShimuraCocycles_le_Gamma1 (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (hN : 5 ≤ N)
    (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hfi : Γ.FiniteIndex) :
    FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  have hE : FiniteDimensional ℂ (degreeLT ℂ (w + 1)) := inferInstance
  have hr : Module.finrank ℂ (degreeLT ℂ (w + 1)) = w + 1 := by
    rw [(degreeLTEquiv ℂ (w + 1)).finrank_eq]; simp
  have hS4 : S ^ 4 = 1 := by decide
  have hU6 : (S * T) ^ 6 = 1 := by decide
  have hSU : S ^ 2 = (S * T) ^ 3 := by decide
  have hU3 : ((S * T) ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hU6
  obtain ⟨-, h4⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ S (rho w S) 4 hfi hE (by norm_num) hS4 (rho_pow_eq_one w _ _ hS4)
    (fun x k hk hk' h => (torsion_not_mem N hN x k hk).1 hk' (hΓ h))
  obtain ⟨-, h6⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ (S * T) (rho w (S * T)) 6 hfi hE (by norm_num) hU6 (rho_pow_eq_one w _ _ hU6)
    (fun x k hk hk' h => (torsion_not_mem N hN x k hk).2 hk' (hΓ h))
  obtain ⟨f2, h2⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ ((S * T) ^ 3) (rho w ((S * T) ^ 3)) 2 hfi hE (by norm_num) hU3
    (rho_pow_eq_one w _ _ hU3) (fun x k hk hk' h => by
      obtain rfl : k = 1 := by omega
      rw [pow_one] at h
      exact (torsion_not_mem N hN x 3 (by norm_num)).2 (by norm_num) (hΓ h))
  obtain ⟨fC, hC⟩ := GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le Γ (rho w) (S * T) (rho_mul w) (rho_one w) hU6 f2
  obtain ⟨fB, hB⟩ := GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add Γ (rho w) S (S * T) (rho_mul w) (rho_one w) hSU closure_S_ST hE fC
  obtain ⟨fA, hA⟩ := GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension Γ (rho w) S (rho_mul w) (rho_one w) hS4 fB
  have hZ := LinearMap.finrank_le_finrank_of_injective (zMap_injective Γ w)
  refine ⟨Module.Finite.of_injective _ (zMap_injective Γ w), ?_⟩
  rw [hr] at h4 h6 h2 hB
  have : (w + 1) * (12 + Γ.index) = 12 * (w + 1) + Γ.index * (w + 1) := by ring
  omega

end GlobalTheory.HeckeFamilyMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1Statement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 <;> assumption)
end
