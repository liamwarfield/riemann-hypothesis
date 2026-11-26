module

public import GroundTheory.AutomorphicForms.CuspidalSplittingPositivity

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.CuspidalSplittingProjective
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin n) F) V}
  {ρ : Representation ℂ (GL (Fin n) F) U} {σ : Representation ℂ (GL (Fin n) F) W}
  {ω : GL (Fin n) F → ℂ}

theorem exists_coeffSum_eq_smul_ne_zero [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ c : ℂ, c ≠ 0 ∧ ∀ w, coeffSum π π K f v w = c • w := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, w₀, hw₀⟩ := exists_coeffSum_ne_zero hπ hsc hωπ
  obtain ⟨c, hc⟩ := exists_coeffSum_eq_smul hπ hsc hKo hωπ hf hv
  refine ⟨K, hKc, hKo, f, hf, v, hv, c, fun h0 => hw₀ ?_, hc⟩
  rw [hc, h0, zero_smul]

theorem isSmooth_of_surjective (hρ : IsSmooth ρ) (p : Representation.IntertwiningMap ρ σ)
    (hp : Surjective p) : IsSmooth σ := by
  intro y
  obtain ⟨u, rfl⟩ := hp y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ u)
  rw [mem_stabilizerOf] at hg ⊢
  rw [← Representation.IntertwiningMap.isIntertwining, hg]

theorem exists_lift_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ)
    (hωρ : HasCentralChar ρ ω) (p : Representation.IntertwiningMap ρ σ) (hp : Surjective p)
    (φ : Representation.IntertwiningMap π σ) :
    ∃ s : Representation.IntertwiningMap π ρ, p.comp s = φ := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, c, hc0, hc⟩ := exists_coeffSum_eq_smul_ne_zero hπ hsc hωπ
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1 :=
    fun z hz => hωπ.inv_mul hu₀ hz
  have hσ := isSmooth_of_surjective hρ p hp
  have hφv : φ v ∈ fixedVectors σ K := map_mem_fixedVectors π φ hv
  obtain ⟨u, hu⟩ := fixedMap_surjective hρ hσ hKc hKo hp ⟨φ v, hφv⟩
  have hpu : p (u : U) = φ v := congrArg Subtype.val hu
  refine ⟨c⁻¹ • coeffMap hπ hsc hKo hωπ hωρ hω hf u.2, ?_⟩
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  change p (c⁻¹ • coeffSum π ρ K f (u : U) w) = φ w
  rw [map_smul, map_coeffSum hπ hsc hKo hf, hpu, ← map_coeffSum hπ hsc hKo hf, hc, map_smul,
    smul_smul, inv_mul_cancel₀ hc0, one_smul]

section Injective


variable (σ π) in
def pairingSum (K : Subgroup (GL (Fin n) F)) (ψ : Module.Dual ℂ W) (v : V) (b : W)
    (ũ : smoothVectors (Representation.dual π)) : ℂ :=
  quotSum (centerSup K) fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)

variable {K : Subgroup (GL (Fin n) F)} {ψ : Module.Dual ℂ W} {v : V}

theorem finite_support_pairingSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      ψ (σ q.out⁻¹ b) * (ũ : Module.Dual ℂ V) (π q.out v) :=
  finite_support_centerSup (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) hKo
    (isCompactModCenter_matrixCoeff hπ hsc v ũ.2) fun g h0 => by
      change (ũ : Module.Dual ℂ V) (π g v) = 0 at h0
      simp only [h0, mul_zero]

theorem pairingSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x) (hv : v ∈ fixedVectors π K) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ∀ g, ∀ h ∈ centerSup K, ψ (σ (g * h)⁻¹ b) * (ũ : Module.Dual ℂ V) (π (g * h) v) =
      ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) := by
  refine rightInv_centerSup
    (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : σ (g * z)⁻¹ b = ω z⁻¹ • σ g⁻¹ b := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωσ _ (inv_mem hz)]
    have e2 : π (g * z) v = ω z • π g v := by
      rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul]
    simp only [e1, e2, map_smul, smul_eq_mul]
    linear_combination ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) * hω z hz
  · have e1 : σ (g * k)⁻¹ b = σ k⁻¹ (σ g⁻¹ b) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    simp only [e1, hψ _ (inv_mem hk), map_mul, Module.End.mul_apply, hv k hk]

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
  (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
  (hv : v ∈ fixedVectors π K)

include hπ hsc hωπ hωσ hω hKo hψ hv


omit hπ hsc hKo in
theorem pairingSum_act (h : GL (Fin n) F) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) := by
  unfold pairingSum
  rw [← quotSum_mul_left (pairingSum_summand_rightInv hωπ hωσ hω hψ hv (σ h b) ũ) h]
  refine quotSum_congr fun g => ?_
  rw [contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (σ h⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_mul, Module.End.mul_apply]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_add (b : W) (ũ₁ ũ₂ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (ũ₁ + ũ₂) = pairingSum π σ K ψ v b ũ₁ + pairingSum π σ K ψ v b ũ₂ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b ũ₁)
    (finite_support_pairingSum hπ hsc hKo b ũ₂)]
  refine finsum_congr fun q => ?_
  simp only [Submodule.coe_add, LinearMap.add_apply, mul_add]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul (b : W) (c : ℂ) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (c • ũ) = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit hωπ hωσ hω hψ hv in
theorem pairingSum_add_left (b₁ b₂ : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (b₁ + b₂) ũ = pairingSum π σ K ψ v b₁ ũ + pairingSum π σ K ψ v b₂ ũ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b₁ ũ)
    (finite_support_pairingSum hπ hsc hKo b₂ ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_add (f := _), add_mul]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul_left (c : ℂ) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (c • b) ũ = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_smul, smul_eq_mul]
  ring


omit hωπ hωσ hω hψ hv in
def pairingForm (b : W) : Module.Dual ℂ (smoothVectors (Representation.dual π)) where
  toFun := pairingSum π σ K ψ v b
  map_add' := pairingSum_add hπ hsc hKo b
  map_smul' c ũ := pairingSum_smul hπ hsc hKo b c ũ

theorem pairingForm_mem (hσ : IsSmooth σ) (b : W) :
    pairingForm (σ := σ) hπ hsc hKo (K := K) (ψ := ψ) (v := v) b ∈
      smoothVectors (Representation.dual (contragredient π)) := by
  rw [mem_smoothVectors]
  refine Subgroup.isOpen_mono (fun h hh => ?_) (hσ b)
  rw [mem_stabilizerOf] at hh ⊢
  refine LinearMap.ext fun ũ => ?_
  rw [dual_apply_apply]
  change pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) = pairingSum π σ K ψ v b ũ
  rw [← pairingSum_act hωπ hωσ hω hψ hv, hh]


omit hπ hsc hωπ hωσ hω hKo hψ hv in
def pairingMap (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
    (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) :
    Representation.IntertwiningMap σ (contragredient (contragredient π)) where
  toFun b := ⟨pairingForm (σ := σ) hπ hsc hKo b, pairingForm_mem hπ hsc hωπ hωσ hω hKo hψ hv hσ b⟩
  map_add' b₁ b₂ := Subtype.ext (LinearMap.ext fun ũ => pairingSum_add_left hπ hsc hKo b₁ b₂ ũ)
  map_smul' c b := Subtype.ext (LinearMap.ext fun ũ => pairingSum_smul_left hπ hsc hKo c b ũ)
  isIntertwining' h := LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun ũ => by
    change pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ)
    exact pairingSum_act hωπ hωσ hω hψ hv h b ũ)

omit hπ hsc hωπ hωσ hω hKo hψ hv in
theorem pairingMap_apply_apply (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ((pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ b :
      smoothVectors (Representation.dual (contragredient π))) :
        Module.Dual ℂ (smoothVectors (Representation.dual π))) ũ = pairingSum π σ K ψ v b ũ := rfl

end Injective

theorem exists_extend_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hωσ : HasCentralChar σ ω) (i : Representation.IntertwiningMap ρ σ) (hi : Injective i)
    (φ : Representation.IntertwiningMap ρ π) :
    ∃ Φ : Representation.IntertwiningMap σ π, Φ.comp i = φ := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, c, hc0, hc⟩ := exists_coeffSum_eq_smul_ne_zero hπ hsc hωπ
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1 :=
    fun z hz => hωπ.inv_mul hu₀ hz

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective i.toLinearMap
    (LinearMap.ker_eq_bot.2 hi)
  let ψ : Module.Dual ℂ W := (f ∘ₗ φ.toLinearMap ∘ₗ l) ∘ₗ (fixedVectors σ K).subtype ∘ₗ
    fixedProj σ hσ hKc hKo
  have hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x := fun k hk x => by
    simp only [ψ, LinearMap.comp_apply, fixedProj_apply_act hσ hKc hKo hk]
  have hψi : ∀ u, ψ (i u) = f (φ u) := by
    have h := eq_of_invariant_of_eqOn hρ hKc hKo (f := ψ ∘ₗ i.toLinearMap)
      (g := f ∘ₗ φ.toLinearMap)
      (fun k hk u => by
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining, hψ k hk])
      (fun k hk u => by
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining, hf k hk])
      (fun u hu => by
        have hiu : i u ∈ fixedVectors σ K := map_mem_fixedVectors ρ i hu
        have hl' : l (i u) = u := LinearMap.congr_fun hl u
        simp only [ψ, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Submodule.subtype_apply, fixedProj_apply_of_mem hσ hKc hKo hiu, hl'])
    exact fun u => LinearMap.congr_fun h u

  have hπa := isAdmissible_of_isIrreducible hπ
  let e := (toDoubleContragredient hπa.1).ofBijective (toDoubleContragredient_bijective hπa)
  let Φ₀ := pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ
  refine ⟨c⁻¹ • (e.symm.toIntertwiningMap.comp Φ₀), ?_⟩
  have key : ∀ u, Φ₀ (i u) = c • toDoubleContragredient hπa.1 (φ u) := fun u =>
    Subtype.ext (LinearMap.ext fun ũ => by
      rw [pairingMap_apply_apply]
      change pairingSum π σ K ψ v (i u) ũ = c * (ũ : Module.Dual ℂ V) (φ u)
      unfold pairingSum
      calc quotSum (centerSup K) (fun g => ψ (σ g⁻¹ (i u)) * (ũ : Module.Dual ℂ V) (π g v))
          = quotSum (centerSup K) (fun g => (ũ : Module.Dual ℂ V) (f (π g⁻¹ (φ u)) • π g v)) :=
            quotSum_congr fun g => by
              rw [← Representation.IntertwiningMap.isIntertwining, hψi,
                Representation.IntertwiningMap.isIntertwining, map_smul, smul_eq_mul]
        _ = (ũ : Module.Dual ℂ V) (coeffSum π π K f v (φ u)) :=
            (linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf (φ u))).symm
        _ = c * (ũ : Module.Dual ℂ V) (φ u) := by rw [hc, map_smul, smul_eq_mul])
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)
  change c⁻¹ • e.symm (Φ₀ (i u)) = φ u
  rw [key, map_smul]
  change c⁻¹ • c • e.symm (e (φ u)) = φ u
  rw [Representation.Equiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Parabolic

end GroundTheory.Automorphic
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Constructions

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}

def subrepIncl (Y : Subrepresentation ρ) :
    Representation.IntertwiningMap Y.toRepresentation ρ where
  toLinearMap := Y.toSubmodule.subtype
  isIntertwining' _ := rfl


theorem isSmooth_toRepresentation (hρ : IsSmooth ρ) (Y : Subrepresentation ρ) :
    IsSmooth Y.toRepresentation := by
  intro y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ (y : U))
  rw [mem_stabilizerOf] at hg ⊢
  exact Subtype.ext hg

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem HasCentralChar.toRepresentation (hωρ : HasCentralChar ρ ω) (Y : Subrepresentation ρ) :
    HasCentralChar Y.toRepresentation ω := fun z hz y => Subtype.ext (hωρ z hz y)

theorem isSmooth_prod (hπ : IsSmooth π) (hρ : IsSmooth ρ) : IsSmooth (π.prod ρ) := by
  intro x
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf π x.1 ⊓ stabilizerOf ρ x.2) (fun g hg => ?_)
    ((hπ x.1).inter (hρ x.2))
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  rw [mem_stabilizerOf] at h1 h2 ⊢
  exact Prod.ext h1 h2


variable (π) in
def piRep (m : ℕ) : Representation ℂ (GL (Fin n) F) (Fin m → V) where
  toFun g := LinearMap.pi fun i => π g ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' g h := by ext; simp


theorem isSmooth_piRep (hπ : IsSmooth π) (m : ℕ) : IsSmooth (piRep π m) := by
  intro x
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h : ⋂ i, (stabilizerOf π (x i) : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    Filter.iInter_mem.2 fun i => (hπ (x i)).mem_nhds (one_mem _)
  refine Filter.mem_of_superset h fun g hg => ?_
  rw [SetLike.mem_coe, mem_stabilizerOf]
  funext i
  exact (Set.mem_iInter.1 hg i)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem HasCentralChar.piRep (hωπ : HasCentralChar π ω) (m : ℕ) :
    HasCentralChar (piRep π m) ω := fun z hz x => funext fun i => hωπ z hz (x i)


variable (π) in
def piIncl (m : ℕ) (i : Fin m) : Representation.IntertwiningMap π (piRep π m) where
  toLinearMap := LinearMap.single ℂ (fun _ => V) i
  isIntertwining' g := by
    ext x j
    change (Pi.single i (π g x) : Fin m → V) j = π g ((Pi.single i x : Fin m → V) j)
    exact (LinearMap.apply_single (fun _ : Fin m => π g) i j x).symm




end Constructions

section Detect

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}

theorem exists_retraction [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
    (Y : Subrepresentation ρ) (t : Representation.IntertwiningMap π ρ)
    (ht : ∀ x, t x ∈ Y.toSubmodule → x = 0) :
    ∃ Fm : Representation.IntertwiningMap ρ π, (∀ x, Fm (t x) = x) ∧
      ∀ y ∈ Y.toSubmodule, Fm y = 0 := by
  let j : Representation.IntertwiningMap (π.prod Y.toRepresentation) ρ :=
    t.comp (Representation.IntertwiningMap.fst ℂ π Y.toRepresentation) +
      (subrepIncl Y).comp (Representation.IntertwiningMap.snd ℂ π Y.toRepresentation)
  have hj : ∀ p : V × Y.toSubmodule, j p = t p.1 + (p.2 : U) := fun p => rfl
  have hjinj : Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hj] at hp
    have h1 : p.1 = 0 := ht p.1 (by
      rw [eq_neg_of_add_eq_zero_left hp]
      exact Y.toSubmodule.neg_mem p.2.2)
    have h2 : (p.2 : U) = 0 := by rw [h1, map_zero, zero_add] at hp; exact hp
    exact Prod.ext h1 (Subtype.ext h2)
  obtain ⟨Fm, hFm⟩ := exists_extend_of_isSupercuspidal hπ hsc hωπ
    (isSmooth_prod hπ (isSmooth_toRepresentation hρ Y)) hρ hωρ j hjinj
    (Representation.IntertwiningMap.fst ℂ π Y.toRepresentation)
  have hF : ∀ p, Fm (j p) = p.1 := fun p =>
    congrArg (fun φ : Representation.IntertwiningMap (π.prod Y.toRepresentation) π => φ p) hFm
  refine ⟨Fm, fun x => ?_, fun y hy => ?_⟩
  · have := hF (x, 0)
    rwa [hj, ZeroMemClass.coe_zero, add_zero] at this
  · have := hF (0, ⟨y, hy⟩)
    rwa [hj, map_zero, zero_add] at this


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem iSup_range_stable (s : Finset (Representation.IntertwiningMap π ρ))
    (g : GL (Fin n) F) {y : U}
    (hy : y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) :
    ρ g y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap := by
  have hle : (⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) ≤
      (⨆ t ∈ s, LinearMap.range
        (t : Representation.IntertwiningMap π ρ).toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
      ← Representation.IntertwiningMap.isIntertwining]
    exact (le_iSup₂ (f := fun t (_ : t ∈ s) =>
      LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) t ht) ⟨π g x, rfl⟩
  exact hle hy

theorem exists_apply_ne_zero_of_mem_iSup [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ)
    (hωρ : HasCentralChar ρ ω) (s : Finset (Representation.IntertwiningMap π ρ)) :
    ∀ y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap,
      y ≠ 0 → ∃ Fm : Representation.IntertwiningMap ρ π, Fm y ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy hy0
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hy
    exact absurd hy hy0
  | insert t s hts ih =>
    intro y hy hy0
    rw [Finset.iSup_insert] at hy
    obtain ⟨a, ⟨w, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    by_cases hyY : t w + b ∈
        ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap
    · exact ih _ hyY hy0
    · let Y : Subrepresentation ρ :=
        ⟨⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap,
          fun g _ hy => iSup_range_stable s g hy⟩
      let L : Subrepresentation π :=
        ⟨Y.toSubmodule.comap t.toLinearMap, fun g x hx => by
          rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
            Representation.IntertwiningMap.isIntertwining]
          exact Y.apply_mem_toSubmodule g hx⟩
      have hL : ∀ x, t x ∈ Y.toSubmodule → x = 0 := by
        rcases eq_bot_or_eq_top L with h | h
        · intro x hx
          have hxL : x ∈ L.toSubmodule := hx
          rw [h] at hxL
          exact (Submodule.mem_bot ℂ).1 hxL
        · exfalso
          have hwL : w ∈ L.toSubmodule := by rw [h]; exact Submodule.mem_top
          exact hyY (Y.toSubmodule.add_mem hwL hb)
      obtain ⟨Fm, hFt, hFY⟩ := exists_retraction hπ hsc hωπ hρ hωρ Y t hL
      refine ⟨Fm, ?_⟩
      rw [map_add (f := _), Representation.IntertwiningMap.toLinearMap_apply, hFt, hFY b hb, add_zero]
      rintro rfl
      exact hyY (by rw [map_zero, zero_add]; exact hb)

end Detect

section Isotypic

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}


variable (π ρ) in
def isotypicPart : Submodule ℂ U :=
  ⨆ t : Representation.IntertwiningMap π ρ, LinearMap.range t.toLinearMap


variable (π ρ) in
def isotypicKernel : Submodule ℂ U :=
  ⨅ Fm : Representation.IntertwiningMap ρ π, LinearMap.ker Fm.toLinearMap

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_isotypicKernel {u : U} :
    u ∈ isotypicKernel π ρ ↔ ∀ Fm : Representation.IntertwiningMap ρ π, Fm u = 0 := by
  simp only [isotypicKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    Representation.IntertwiningMap.toLinearMap_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem apply_mem_isotypicPart (t : Representation.IntertwiningMap π ρ) (x : V) :
    t x ∈ isotypicPart π ρ :=
  (le_iSup (fun t : Representation.IntertwiningMap π ρ => LinearMap.range t.toLinearMap) t)
    ⟨x, rfl⟩



omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isotypicKernel_stable (g : GL (Fin n) F) {u : U} (hu : u ∈ isotypicKernel π ρ) :
    ρ g u ∈ isotypicKernel π ρ := by
  rw [mem_isotypicKernel] at hu ⊢
  intro Fm
  rw [Representation.IntertwiningMap.isIntertwining, hu, map_zero]

variable [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
  (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
include hπ hsc hωπ hρ hωρ

theorem disjoint_isotypicPart_isotypicKernel :
    Disjoint (isotypicPart π ρ) (isotypicKernel π ρ) := by
  rw [Submodule.disjoint_def]
  intro y hy1 hy2
  by_contra hy0
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy1
  obtain ⟨Fm, hFm⟩ := exists_apply_ne_zero_of_mem_iSup hπ hsc hωπ hρ hωρ s y hs hy0
  exact hFm (mem_isotypicKernel.1 hy2 Fm)

theorem exists_sub_mem_isotypicKernel (u : U) :
    ∃ u' ∈ isotypicPart π ρ, u - u' ∈ isotypicKernel π ρ := by
  classical
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hπa := isAdmissible_of_isIrreducible hπ
  obtain ⟨K, hKc, hKo, huK⟩ := (isSmooth_iff_forall_exists ρ).1 hρ u

  let ev : Representation.IntertwiningMap ρ π →ₗ[ℂ] V :=
    { toFun := fun Fm => Fm u, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let E := LinearMap.range ev
  have hEK : E ≤ fixedVectors π K := by
    rintro _ ⟨Fm, rfl⟩
    exact map_mem_fixedVectors ρ Fm huK
  have : FiniteDimensional ℂ (fixedVectors π K) := hπa.2 K hKc hKo
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hEK
  let m := Module.finrank ℂ E
  let bE := Module.finBasis ℂ E
  have hb : ∀ i, ∃ Gi : Representation.IntertwiningMap ρ π, Gi u = (bE i : V) :=
    fun i => (bE i).2
  choose Gs hGs using hb

  let Γ : Representation.IntertwiningMap ρ (piRep π m) :=
    { toLinearMap := LinearMap.pi fun i => (Gs i).toLinearMap
      isIntertwining' := fun g => by
        ext x i
        simp [piRep, Representation.IntertwiningMap.isIntertwining] }
  have hΓ : ∀ x i, Γ x i = Gs i x := fun _ _ => rfl

  let W0 : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun g => ρ g u), fun g x hx => by
      have hle : Submodule.span ℂ (Set.range fun h => ρ h u) ≤
          (Submodule.span ℂ (Set.range fun h => ρ h u)).comap (ρ g) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, rfl⟩
        exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
      exact hle hx⟩
  have huW0 : u ∈ W0.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have hvanish : ∀ H : Representation.IntertwiningMap ρ π, H u = 0 →
      ∀ x ∈ W0.toSubmodule, H x = 0 := by
    intro H hH x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      rw [Representation.IntertwiningMap.isIntertwining, hH, map_zero]
    | zero => exact map_zero H
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  let Γ0 := Γ.comp (subrepIncl W0)
  have hΓ0 : ∀ x i, Γ0 x i = Gs i (x : U) := fun _ _ => rfl
  have hρ0 := isSmooth_toRepresentation hρ W0
  have hωρ0 := hωρ.toRepresentation W0

  have hsurj : Surjective Γ0 := by
    by_contra hns
    let R : Subrepresentation (piRep π m) := Γ0.range
    have hRmem : ∀ y, y ∈ R.toSubmodule ↔ ∃ x, Γ0 x = y := fun y => Iff.rfl
    have hR : ∃ j, ∀ x, piIncl π m j x ∈ R.toSubmodule → x = 0 := by
      by_contra hall
      push Not at hall
      apply hns
      have hsub : ∀ j, ∀ x, piIncl π m j x ∈ R.toSubmodule := by
        intro j
        obtain ⟨x₀, hx₀R, hx₀⟩ := hall j
        let L : Subrepresentation π :=
          ⟨R.toSubmodule.comap (piIncl π m j).toLinearMap, fun g x hx => by
            rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
              Representation.IntertwiningMap.isIntertwining]
            exact R.apply_mem_toSubmodule g hx⟩
        rcases eq_bot_or_eq_top L with h | h
        · exfalso
          have hx₀L : x₀ ∈ L.toSubmodule := hx₀R
          rw [h] at hx₀L
          exact hx₀ ((Submodule.mem_bot ℂ).1 hx₀L)
        · intro x
          have hxL : x ∈ L.toSubmodule := by rw [h]; exact Submodule.mem_top
          exact hxL
      intro y
      have hy : y ∈ R.toSubmodule := by
        rw [← Finset.univ_sum_single y]
        exact Submodule.sum_mem _ fun j _ => hsub j (y j)
      exact (hRmem y).1 hy
    obtain ⟨j, hj⟩ := hR
    obtain ⟨Φ, hΦj, hΦR⟩ := exists_retraction hπ hsc hωπ (isSmooth_piRep hπ m)
      (hωπ.piRep m) R (piIncl π m j) hj
    have hc : ∀ i, ∃ c : ℂ, ∀ x, Φ (piIncl π m i x) = c • x := fun i => by
      obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hπ).2
        (Φ.comp (piIncl π m i))
      exact ⟨c, fun x =>
        (congrArg (fun ψ : Representation.IntertwiningMap π π => ψ x) hc).symm⟩
    choose c hcx using hc
    have hΦ : ∀ y : Fin m → V, Φ y = ∑ i, c i • y i := fun y => by
      conv_lhs => rw [← Finset.univ_sum_single y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hcx i (y i)
    have hzero : ∑ i, c i • bE i = 0 := by
      have h1 : Φ (Γ u) = 0 := hΦR _ ((hRmem _).2 ⟨⟨u, huW0⟩, rfl⟩)
      rw [hΦ] at h1
      apply Subtype.ext
      simpa [hΓ, hGs] using h1
    have hcj : c j = 0 := (Fintype.linearIndependent_iff.1 bE.linearIndependent) c hzero j
    have h1 : (1 : ℂ) • u₀ = c j • u₀ := by rw [one_smul, ← hcx j u₀, hΦj]
    rw [hcj, zero_smul, one_smul] at h1
    exact hu₀ h1

  have hlift : ∀ i, ∃ s : Representation.IntertwiningMap π W0.toRepresentation,
      Γ0.comp s = piIncl π m i := fun i =>
    exists_lift_of_isSupercuspidal hπ hsc hωπ hρ0 hωρ0 Γ0 hsurj (piIncl π m i)
  choose s hs using hlift
  let u' : U := ∑ i, (s i (Gs i u) : U)
  have hu'W0 : u' ∈ W0.toSubmodule := Submodule.sum_mem _ fun i _ => (s i (Gs i u)).2
  have hGu' : ∀ i, Gs i u' = Gs i u := by
    intro i
    have h2 : Γ0 (∑ k, s k (Gs k u)) = Γ u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have h3 : ∀ k, Γ0 (s k (Gs k u)) = Pi.single k (Gs k u) := fun k => by
        rw [← Representation.IntertwiningMap.comp_apply, hs]
        rfl
      simp only [h3]
      exact Finset.univ_sum_single (Γ u)
    have h4 := congrFun h2 i
    rw [hΓ0, hΓ] at h4
    simpa [u'] using h4
  refine ⟨u', Submodule.sum_mem _ fun i _ => apply_mem_isotypicPart ((subrepIncl W0).comp (s i))
    (Gs i u), ?_⟩
  rw [mem_isotypicKernel]
  intro Fm
  have hFE : Fm u ∈ E := ⟨Fm, rfl⟩
  let a := bE.repr ⟨Fm u, hFE⟩
  have hFu : Fm u = ∑ i, a i • (bE i : V) := by
    have h5 := congrArg Subtype.val (bE.sum_repr ⟨Fm u, hFE⟩)
    rw [Submodule.coe_sum] at h5
    simp only [Submodule.coe_smul] at h5
    exact h5.symm
  let H : Representation.IntertwiningMap ρ π := Fm - ∑ i, a i • Gs i
  have hHx : ∀ x, H x = Fm x - ∑ i, a i • Gs i x := fun x => by
    simp [H, Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  have hHu : H u = 0 := by
    rw [hHx, hFu]
    simp [hGs]
  have hHu' := hvanish H hHu u' hu'W0
  rw [hHx, sub_eq_zero] at hHu'
  rw [map_sub, hHu', hFu, sub_eq_zero]
  simp [hGu', hGs]

theorem isCompl_isotypicPart_isotypicKernel :
    IsCompl (isotypicPart π ρ) (isotypicKernel π ρ) := by
  refine ⟨disjoint_isotypicPart_isotypicKernel hπ hsc hωπ hρ hωρ,
    codisjoint_iff.2 (eq_top_iff.2 fun u _ => ?_)⟩
  obtain ⟨u', hu', h⟩ := exists_sub_mem_isotypicKernel hπ hsc hωπ hρ hωρ u
  exact Submodule.mem_sup.2 ⟨u', hu', u - u', h, add_sub_cancel u' u⟩

theorem not_surjective_of_le_isotypicKernel (A : Subrepresentation ρ)
    (hA : A.toSubmodule ≤ isotypicKernel π ρ)
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  intro hp
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨s, hs⟩ := exists_lift_of_isSupercuspidal hπ hsc hωπ (isSmooth_toRepresentation hρ A)
    (hωρ.toRepresentation A) p hp (Representation.IntertwiningMap.id π)
  have hps : ∀ x, p (s x) = x := fun x =>
    congrArg (fun φ : Representation.IntertwiningMap π π => φ x) hs
  let i := (subrepIncl A).comp s
  have hi : Injective i := fun x y hxy => by
    have h1 : s x = s y := Subtype.ext hxy
    rw [← hps x, ← hps y, h1]
  obtain ⟨Fm, hFm⟩ := exists_extend_of_isSupercuspidal hπ hsc hωπ hπ hρ hωρ i hi
    (Representation.IntertwiningMap.id π)
  have h1 : Fm (i x₀) = x₀ :=
    congrArg (fun φ : Representation.IntertwiningMap π π => φ x₀) hFm
  have h2 : Fm (i x₀) = 0 := mem_isotypicKernel.1 (hA (s x₀).2) Fm
  exact hx₀ (h1.symm.trans h2)

end Isotypic

end Parabolic

end GroundTheory.Automorphic
