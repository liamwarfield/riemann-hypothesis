module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceA
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceBlocks
open MulAction

namespace UpperTheory.V.Z.Sym.Tf

variable {Γ Y V : Type} [Group Γ] [MulAction Γ Y] [AddCommGroup V] [Module ℂ V]

theorem sum_fib {A B : Type} (m : A → B) (F : A → V) (F' : B → V) (c : B → ℕ) (hB : (Function.support F').Finite)
    (hc : ∀ b, F' b ≠ 0 → c b ≠ 0 ∧ Nat.card {a // m a = b} = c b) (hF : ∀ a, F a = (c (m a) : ℂ)⁻¹ • F' (m a)) :
    (Function.support F).Finite ∧ ∑ᶠ a, F a = ∑ᶠ b, F' b := by
  classical
  have hfibfin : ∀ b, F' b ≠ 0 → {a | m a = b}.Finite := by
    intro b hb
    have h1 := hc b hb
    have hne : Nat.card {a // m a = b} ≠ 0 := by rw [h1.2]; exact h1.1
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  have hsuppF : Function.support F ⊆ ⋃ b ∈ Function.support F', {a | m a = b} := by
    intro a ha
    refine Set.mem_iUnion₂.mpr ⟨m a, fun h0 => ha ?_, rfl⟩
    rw [hF, h0, smul_zero]
  have hfin : (Function.support F).Finite :=
    (hB.biUnion fun b hb => hfibfin b hb).subset hsuppF
  refine ⟨hfin, ?_⟩
  set s := hfin.toFinset with hs
  set T := hB.toFinset with hT
  rw [finsum_eq_sum_of_support_subset F (s := s) (by simp [s]),
    finsum_eq_sum_of_support_subset F' (s := T) (by simp [T])]
  have hmaps : ∀ a ∈ s, m a ∈ T := by
    intro a ha
    have ha' : F a ≠ 0 := by simpa [s] using ha
    have : F' (m a) ≠ 0 := fun h0 => ha' (by rw [hF, h0, smul_zero])
    simpa [T] using this
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun b hbT => ?_
  have hb' : F' b ≠ 0 := by simpa [T] using hbT
  obtain ⟨hcb, hcard⟩ := hc b hb'
  have hset : (↑(s.filter (fun a => m a = b)) : Set A) = {a | m a = b} := by
    ext a
    simp only [Finset.coe_filter, Set.mem_setOf_eq, s, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hF, h]
      exact smul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr hcb)) hb'
  have hcard' : (s.filter (fun a => m a = b)).card = c b := by
    rw [← Set.ncard_coe_finset, hset, ← Nat.card_coe_set_eq]
    exact hcard
  rw [Finset.sum_congr rfl (g := fun _ => (c b : ℂ)⁻¹ • F' b)]
  · rw [Finset.sum_const, hcard', ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hcb), one_smul]
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [hF, ha.2]

theorem rel_smul (Γ₀ : Subgroup Γ) [Γ₀.Normal] (g : Γ) (y : Y) :
    Γ₀.relIndex (stabilizer Γ (g • y)) = Γ₀.relIndex (stabilizer Γ y) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← Subgroup.Normal.map_conj_eq Γ₀ g]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem card_fib (H : Subgroup Γ) (b : orbitRel.Quotient H Y) :
    Nat.card {a : orbitRel.Quotient Γ Y × (Γ ⧸ H) // (Quotient.mk'' (a.2.out⁻¹ • a.1.out) : orbitRel.Quotient H Y) = b} =
      H.relIndex (stabilizer Γ b.out) := by
  classical
  set y0 := b.out with hy0
  set O0 : orbitRel.Quotient Γ Y := Quotient.mk'' y0 with hO0
  obtain ⟨t, ht⟩ : ∃ t : Γ, t • y0 = O0.out := by
    have h1 : (orbitRel Γ Y) O0.out y0 := Quotient.exact' (Quotient.out_eq' O0)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
    exact h1
  have hbq : (Quotient.mk'' y0 : orbitRel.Quotient H Y) = b := Quotient.out_eq' b
  have hinv : ∀ s : stabilizer Γ y0, (s : Γ)⁻¹ • y0 = y0 := fun s =>
    inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp s.2).symm
  have hmem : ∀ s : stabilizer Γ y0,
      (Quotient.mk'' ((((t * (s : Γ) : Γ) : Γ ⧸ H)).out⁻¹ • O0.out) : orbitRel.Quotient H Y) = b := by
    intro s
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (t * (s : Γ))
    rw [hh, ← ht, smul_smul]
    have e1 : (t * (s : Γ) * (h : Γ))⁻¹ * t = (h : Γ)⁻¹ * (s : Γ)⁻¹ := by group
    rw [e1, mul_smul, hinv s, ← hbq]
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨h⁻¹, rfl⟩))
  let Fib := {a : orbitRel.Quotient Γ Y × (Γ ⧸ H) //
    (Quotient.mk'' (a.2.out⁻¹ • a.1.out) : orbitRel.Quotient H Y) = b}
  let F : stabilizer Γ y0 → Fib := fun s => ⟨(O0, ((t * (s : Γ) : Γ) : Γ ⧸ H)), hmem s⟩
  have hF : ∀ s1 s2 : stabilizer Γ y0, F s1 = F s2 ↔ s1⁻¹ * s2 ∈ H.subgroupOf (stabilizer Γ y0) := by
    intro s1 s2
    rw [Subgroup.mem_subgroupOf]
    have e2 : (t * (s1 : Γ))⁻¹ * (t * (s2 : Γ)) = ((s1⁻¹ * s2 : stabilizer Γ y0) : Γ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    constructor
    · intro h12
      have h3 : ((t * (s1 : Γ) : Γ) : Γ ⧸ H) = ((t * (s2 : Γ) : Γ) : Γ ⧸ H) :=
        congrArg (fun z : Fib => z.1.2) h12
      have h4 := QuotientGroup.eq.mp h3
      rw [e2] at h4
      exact h4
    · intro h12
      apply Subtype.ext
      refine Prod.ext rfl (QuotientGroup.eq.mpr ?_)
      show (t * (s1 : Γ))⁻¹ * (t * (s2 : Γ)) ∈ H
      rw [e2]
      exact h12
  have hsurj : Function.Surjective F := by
    rintro ⟨⟨O, q⟩, hq⟩
    obtain ⟨h, hh⟩ : ∃ h : H, (h : Γ) • y0 = q.out⁻¹ • O.out := by
      have h1 : (orbitRel H Y) (q.out⁻¹ • O.out) y0 := Quotient.exact' (hq.trans hbq.symm)
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
      exact h1
    have hO : O = O0 := by
      rw [← Quotient.out_eq' O]
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
        ⟨q.out * h, by rw [mul_smul, hh, smul_inv_smul]⟩))
    subst hO
    refine ⟨⟨t⁻¹ * q.out * h, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh, smul_inv_smul, ← ht, inv_smul_smul]
    · apply Subtype.ext
      refine Prod.ext rfl ?_
      show ((t * (t⁻¹ * q.out * (h : Γ)) : Γ) : Γ ⧸ H) = q
      rw [show t * (t⁻¹ * q.out * (h : Γ)) = q.out * (h : Γ) by group,
        QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
  rw [Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift F fun a b hab => (hF a b).mpr (QuotientGroup.leftRel_apply.mp hab)) ⟨?_, ?_⟩).symm
  · intro x y hxy
    induction x using Quotient.inductionOn'
    induction y using Quotient.inductionOn'
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr ((hF _ _).mp hxy))
  · intro z
    obtain ⟨s, rfl⟩ := hsurj z
    exact ⟨Quotient.mk'' s, rfl⟩

theorem countC (Γ₀ H : Subgroup Γ) [Γ₀.Normal] (h0 : ∀ z ∈ Γ₀, ∀ y : Y, z • y = y) (hH : Γ₀ ≤ H)
    (hs : ∀ y : Y, Γ₀.relIndex (stabilizer Γ y) ≠ 0) (k : Y → V) (hk : ∀ h ∈ H, ∀ y, k (h • y) = k y)
    (fin : {b : orbitRel.Quotient H Y | k b.out ≠ 0}.Finite) :
    (Function.support fun a : orbitRel.Quotient Γ Y × (Γ ⧸ H) =>
      (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out)).Finite ∧
    ∑ᶠ a : orbitRel.Quotient Γ Y × (Γ ⧸ H), (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out) =
      ∑ᶠ b : orbitRel.Quotient H Y, (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out := by
  have hmul : ∀ y : Y, Γ₀.relIndex (H ⊓ stabilizer Γ y) * H.relIndex (stabilizer Γ y) =
      Γ₀.relIndex (stabilizer Γ y) := by
    intro y
    rw [Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.mpr hH]
  have hcne : ∀ y : Y, H.relIndex (stabilizer Γ y) ≠ 0 := fun y h => hs y (by rw [← hmul y, h, mul_zero])
  let m : orbitRel.Quotient Γ Y × (Γ ⧸ H) → orbitRel.Quotient H Y :=
    fun a => Quotient.mk'' (a.2.out⁻¹ • a.1.out)
  have key : ∀ a : orbitRel.Quotient Γ Y × (Γ ⧸ H),
      (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out) =
      ((H.relIndex (stabilizer Γ (m a).out) : ℕ) : ℂ)⁻¹ •
        ((Γ₀.relIndex (H ⊓ stabilizer Γ (m a).out) : ℂ)⁻¹ • k (m a).out) := by
    intro a
    obtain ⟨h, hh⟩ : ∃ h : H, (h : Γ) • (a.2.out⁻¹ • a.1.out) = (m a).out := by
      have h1 : (orbitRel H Y) (m a).out (a.2.out⁻¹ • a.1.out) := Quotient.exact' (Quotient.out_eq' (m a))
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
      exact h1
    have hk' : k (m a).out = k (a.2.out⁻¹ • a.1.out) := by
      rw [← hh]
      exact hk h h.2 _
    have hidx : Γ₀.relIndex (stabilizer Γ (m a).out) = Γ₀.relIndex (stabilizer Γ a.1.out) := by
      rw [← hh, rel_smul, rel_smul]
    rw [smul_smul, ← mul_inv, ← Nat.cast_mul, mul_comm, hmul, hidx, hk']
  have hF'fin : (Function.support fun b : orbitRel.Quotient H Y =>
      (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out).Finite := by
    refine fin.subset ?_
    intro b hb hkb
    exact hb (by simp only [hkb, smul_zero])
  exact sum_fib m
    (fun a => (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out))
    (fun b => (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out)
    (fun b => H.relIndex (stabilizer Γ b.out)) hF'fin (fun b _ => ⟨hcne _, card_fib H b⟩) key

theorem finsum_sig {I : Type} {A : I → Type} (F : (Σ i, A i) → ℂ) (h : (Function.support F).Finite) :
    ∑ᶠ a, F a = ∑ᶠ i, ∑ᶠ x, F ⟨i, x⟩ := by
  classical
  set s := h.toFinset with hs
  let t := s.image Sigma.fst
  let u : ∀ i, Finset (A i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : Function.support F ⊆ ↑(t.sigma u) := by
    intro a ha
    have ha' : a ∈ s := by simpa [s] using ha
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, t, u, Finset.mem_image,
      Finset.mem_preimage]
    exact ⟨⟨a, ha', rfl⟩, ha'⟩
  rw [finsum_eq_sum_of_support_subset F hsub, Finset.sum_sigma]
  rw [finsum_eq_sum_of_support_subset (s := t)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro x hx
    simpa [u, s] using hx
  · intro i hi
    obtain ⟨x, hx⟩ : ∃ x, F ⟨i, x⟩ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hi (by simp [hc])
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, x⟩, by simpa [s] using hx, rfl⟩)

theorem trace_blocks {Q : Type} [Fintype Q] [FiniteDimensional ℂ V] (E : Q → Q → Module.End ℂ V) (L : Module.End ℂ (Q → V))
    (h : ∀ w o', L w o' = ∑ o, E o' o (w o)) : LinearMap.trace ℂ _ L = ∑ o, LinearMap.trace ℂ V (E o o) := by
  classical
  have hL : L = ∑ o', ∑ o, LinearMap.single ℂ (fun _ : Q => V) o' ∘ₗ (E o' o ∘ₗ LinearMap.proj o) := by
    refine LinearMap.ext fun w => funext fun p => ?_
    simp only [h, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single, Pi.single_apply]
    rw [Finset.sum_comm]
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, map_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hterm : ∀ o, LinearMap.trace ℂ (Q → V)
      (LinearMap.single ℂ (fun _ : Q => V) o' ∘ₗ (E o' o ∘ₗ LinearMap.proj o)) =
      if o = o' then LinearMap.trace ℂ V (E o' o) else 0 := by
    intro o
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    split_ifs with hoo
    · subst hoo
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id]
    · rw [LinearMap.proj_comp_single_ne ℂ _ _ _ hoo, LinearMap.comp_zero, map_zero]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finsum_triv (Γ₀ : Subgroup Γ) (h0 : ∀ z ∈ Γ₀, ∀ y : Y, z • y = y) (k : Y → V) (hk : (Function.support k).Finite) :
    {b : orbitRel.Quotient Γ₀ Y | k b.out ≠ 0}.Finite ∧
    ∑ᶠ b : orbitRel.Quotient Γ₀ Y, (Γ₀.relIndex (Γ₀ ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out = ∑ᶠ y, k y := by
  have hrel : ∀ y y' : Y, (orbitRel Γ₀ Y) y y' → y = y' := by
    intro y y' h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, hg⟩ := h
    rw [← hg, Subgroup.smul_def]
    exact h0 g g.2 y'
  let e : Y ≃ orbitRel.Quotient Γ₀ Y :=
    { toFun := fun y => Quotient.mk'' y
      invFun := fun b => b.out
      left_inv := fun y => hrel _ _ (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' y : orbitRel.Quotient Γ₀ Y)))
      right_inv := fun b => Quotient.out_eq' b }
  refine ⟨?_, ?_⟩
  · refine (hk.image e).subset ?_
    intro b hb
    exact ⟨b.out, hb, Quotient.out_eq' b⟩
  · have hcoef : ∀ b : orbitRel.Quotient Γ₀ Y, Γ₀.relIndex (Γ₀ ⊓ stabilizer Γ b.out) = 1 :=
      fun b => Subgroup.relIndex_eq_one.mpr inf_le_left
    simp only [hcoef, Nat.cast_one, inv_one, one_smul]
    exact finsum_comp_equiv e.symm (f := k)

end UpperTheory.V.Z.Sym.Tf
end

open MulAction

namespace UpperTheory.V.Z.Sym.Tf

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V)

@[reducible] def act : MulAction Γ (G ⧸ B.U) := MulAction.compHom _ B.ι

theorem normal0 : B.Γ₀.Normal := ⟨fun z hz g => by rwa [Subgroup.mem_center_iff.1 (B.cenΓ hz) g, mul_inv_cancel_right]⟩

theorem triv0 : (letI := act B; ∀ z ∈ B.Γ₀, ∀ y : G ⧸ B.U, z • y = y) := by
  intro z hz y
  induction y using QuotientGroup.induction_on with
  | H g =>
    show ((B.ι z * g : G) : G ⧸ B.U) = g
    rw [← Subgroup.mem_center_iff.1 (B.cenG z hz) g]
    exact QuotientGroup.mk_mul_of_mem _ (B.memU z hz)

theorem stab0 (hB : B.Fin) : (letI := act B; ∀ y : G ⧸ B.U, B.Γ₀.relIndex (stabilizer Γ y) ≠ 0) := by
  letI := act B
  intro y
  induction y using QuotientGroup.induction_on with
  | H g =>
    convert hB.stab g
    ext γ
    rw [mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.mem_map_equiv]
    show ((B.ι γ * g : G) : G ⧸ B.U) = g ↔ _
    rw [eq_comm, QuotientGroup.eq]; simp [mul_assoc]

theorem finQ (hB : B.Fin) : (letI := act B; Finite (orbitRel.Quotient Γ (G ⧸ B.U))) := by
  letI := act B
  obtain ⟨S, hS⟩ := hB.cls
  refine Finite.of_surjective (fun s : S => (Quotient.mk'' ((s : G) : G ⧸ B.U) : orbitRel.Quotient Γ (G ⧸ B.U))) ?_
  rintro ⟨y⟩
  induction y using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
    refine ⟨⟨s, hs⟩, Eq.symm (Quotient.sound ?_)⟩
    exact ⟨γ, (QuotientGroup.mk_mul_of_mem _ hu).symm⟩

variable {B} (s : B.Tw) (f : G → ℂ)

noncomputable def Tk (g y : G) (γ : Γ) : Module.End ℂ V := f (g⁻¹ * s.θ (B.ι γ * y)) • (s.Θ ∘ₗ B.W γ)

variable {s f}

theorem twistedKernelSummand_mul_trivialActing (hf : s.IsTest f) (g y : G) (γ : Γ) {z : Γ} (hz : z ∈ B.Γ₀) : Tk s f g y (γ * z) = Tk s f g y γ := by
  ext v
  have := hf.right ⟨_, B.memU z hz⟩ (g⁻¹ * s.θ (B.ι γ * y))
  simp only [Tk, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [map_mul B.ι, mul_assoc (B.ι γ), ← Subgroup.mem_center_iff.1 (B.cenG z hz) y, ← mul_assoc (B.ι γ), map_mul s.θ _ (B.ι z), ← mul_assoc,
    this, map_mul B.W, Module.End.mul_apply, B.scal z hz, map_smul, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]
  simp

theorem Tk_out (hf : s.IsTest f) (g y : G) (γ : Γ) : Tk s f g y ((γ : Γ ⧸ B.Γ₀).out)⁻¹ = Tk s f g y γ⁻¹ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul B.Γ₀ γ
  rw [hz, mul_inv_rev, ← Subgroup.mem_center_iff.1 (B.cenΓ (inv_mem z.2)), twistedKernelSummand_mul_trivialActing hf _ _ _ (inv_mem z.2)]

def HD (s : B.Tw) (f : G → ℂ) : Prop :=
  ∀ g g' : G, ∃ D : Finset Γ, ∀ δ, f (g⁻¹ * B.ι δ * s.θ g') ≠ 0 → ∃ d ∈ D, ∃ z ∈ B.Γ₀, δ = d * z

theorem f_fin (hD : HD s f) (g y : G) : {x : Γ ⧸ B.Γ₀ | f (g⁻¹ * s.θ (B.ι x.out⁻¹ * y)) ≠ 0}.Finite := by
  obtain ⟨D, hD⟩ := hD g y
  refine (D.finite_toSet.image fun d => (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀)).subset fun x hx => ?_
  obtain ⟨d, hd, z, hz, h⟩ := hD (s.θΓ x.out⁻¹) (by rwa [← s.comm, mul_assoc, ← map_mul])
  refine ⟨d, hd, ?_⟩
  have : s.θΓ.symm d = x.out⁻¹ * z⁻¹ := by
    rw [MulEquiv.symm_apply_eq, map_mul, h, s.fix _ (inv_mem hz), mul_inv_cancel_right]
  show (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x
  rw [this, mul_inv_rev, inv_inv, inv_inv, ← Subgroup.mem_center_iff.1 (B.cenΓ hz), QuotientGroup.mk_mul_of_mem _ hz, QuotientGroup.out_eq']

theorem Tk_fin (hD : HD s f) (g y : G) : (Function.support fun x : Γ ⧸ B.Γ₀ => Tk s f g y x.out⁻¹).Finite :=
  (f_fin hD g y).subset fun x hx h => hx (by simp only [Tk, h, zero_smul])

variable (s f) in
noncomputable def Ek (s : B.Tw) (f : G → ℂ) (g y : G) : Module.End ℂ V :=
  ∑ᶠ x : Γ ⧸ B.Γ₀, Tk s f g y x.out⁻¹

theorem Ek_left (hf : s.IsTest f) (hD : HD s f) (γ : Γ) (g y : G) : Ek s f (B.ι γ * g) y = B.W γ * Ek s f g y := by
  haveI := normal0 B
  unfold Ek
  rw [mul_finsum' _ _ (Tk_fin hD g y), ← finsum_comp_equiv (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) (f := fun x => B.W γ * Tk s f g y x.out⁻¹)]
  refine finsum_congr fun x => ?_
  have e : (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) x = ((x.out * s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀) := by simp
  rw [e, Tk_out hf]
  obtain ⟨γ, rfl⟩ := s.θΓ.surjective γ
  ext v
  simp only [Tk, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.mul_apply, MulEquiv.symm_apply_apply, map_smul, ← s.int, ← s.comm]
  rw [← Module.End.mul_apply (B.W γ), ← map_mul]
  simp [mul_assoc]

theorem Ek_right (hf : s.IsTest f) (hD : HD s f) (u : B.U) (g y : G) : Ek s f (g * u) y = (B.ω u : ℂ) • Ek s f g y := by
  unfold Ek
  rw [smul_finsum' _ (Tk_fin hD g y)]
  refine finsum_congr fun x => ?_
  have := hf.left u⁻¹ (g⁻¹ * s.θ (B.ι x.out⁻¹ * y))
  simp only [map_inv B.ω, inv_inv, InvMemClass.coe_inv] at this
  simp only [Tk]
  rw [mul_inv_rev, mul_assoc, this, smul_smul]

theorem traceA [FiniteDimensional ℂ V] (hB : B.Fin) (hf : s.IsTest f) (hD : HD s f) : (letI := act B
    LinearMap.trace ℂ B.Forms (s.R f) = ∑ᶠ o : orbitRel.Quotient Γ (G ⧸ B.U), ∑ᶠ x : Γ ⧸ B.Γ₀,
      (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹ * LinearMap.trace ℂ V (Tk s f o.out.out o.out.out x.out⁻¹)) := by
  letI := act B
  haveI := normal0 B
  haveI := finQ B hB
  haveI := formsFin _ _ _ B hB
  letI := Fintype.ofFinite (orbitRel.Quotient Γ (G ⧸ B.U))
  let n : orbitRel.Quotient Γ (G ⧸ B.U) → ℂ := fun o => (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹
  let A : (orbitRel.Quotient Γ (G ⧸ B.U) → V) →ₗ[ℂ] B.Forms :=
    { toFun := fun w => ⟨fun g => ∑ o, n o • Ek s f g o.out.out (w o), fun γ g => by simp [Ek_left hf hD], fun g u => by
        simp only [Ek_right hf hD, Finset.smul_sum, LinearMap.smul_apply]; exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp [Finset.sum_add_distrib])
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Submodule.coe_smul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _) }
  let ev : B.Forms →ₗ[ℂ] (orbitRel.Quotient Γ (G ⧸ B.U) → V) := (LinearMap.funLeft ℂ V fun o => o.out.out).comp B.Forms.subtype
  have hR : s.R f = A ∘ₗ ev := by
    ext φ g
    rw [rSpec _ _ _ B s f hf]
    let k : G ⧸ B.U → V := fun y => f (g⁻¹ * s.θ y.out) • s.Θ (φ.1 y.out)
    have wd : ∀ y : G, k y = f (g⁻¹ * s.θ y) • s.Θ (φ.1 y) := fun y => by
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U y
      simp only [k]
      rw [hu, map_mul, ← mul_assoc, hf.right, φ.2.2, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]; simp
    have e : ∀ x : G ⧸ B.U, k (MulAction.toPerm (s.θ.symm g) x) = f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)) := fun x => by
      have : (MulAction.toPerm (s.θ.symm g) x : G ⧸ B.U) = ((s.θ.symm g * x.out : G) : G ⧸ B.U) := by
        conv_lhs => rw [← x.out_eq]
        rfl
      rw [this, wd]; simp
    have kf : (Function.support k).Finite := by
      refine Set.Finite.of_preimage (f := MulAction.toPerm (s.θ.symm g)) (hf.fin.subset fun x hx h => hx ?_) (Equiv.surjective _)
      rw [e, h, zero_smul]
    obtain ⟨t1, t2⟩ := finsum_triv B.Γ₀ (triv0 B) k kf
    obtain ⟨c1, c2⟩ := countC B.Γ₀ B.Γ₀ (triv0 B) le_rfl (stab0 B hB) k (fun z hz y => by rw [triv0 B z hz]) t1
    rw [t2, finsum_curry _ c1, finsum_eq_sum_of_fintype, ← finsum_comp_equiv (MulAction.toPerm (s.θ.symm g))] at c2
    simp only [e] at c2
    refine c2.symm.trans (Finset.sum_congr rfl fun o _ => ?_)
    show _ = n o • Ek s f g o.out.out (φ.1 o.out.out)
    have := map_finsum (n o • LinearMap.applyₗ (R := ℂ) (M₂ := V) (φ.1 o.out.out)) (Tk_fin hD g o.out.out)
    refine Eq.trans (finsum_congr fun x => ?_) this.symm
    have e2 : x.out⁻¹ • o.out = ((B.ι x.out⁻¹ * o.out.out : G) : G ⧸ B.U) := by
      conv_lhs => rw [← o.out.out_eq]
      rfl
    rw [e2, wd, φ.2.1]
    rfl
  rw [hR, LinearMap.trace_comp_comm', trace_blocks (fun o' o => n o • Ek s f o'.out.out o.out.out) _ fun w o' => rfl, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun o _ => ?_
  exact map_finsum (LinearMap.trace ℂ V ∘ₗ LinearMap.lsmul ℂ _ (n o)) (Tk_fin hD _ _) |>.trans (finsum_congr fun x => by simp [n])

end UpperTheory.V.Z.Sym.Tf
end

open MulAction UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Tf

section

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V} {s : B.Tw} {f : G → ℂ}

private noncomputable def FF (s : B.Tw) (f : G → ℂ) (δ : Γ) (y : G ⧸ B.U) : ℂ := s.ker f δ y * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)

private theorem ker_mk (hf : s.IsTest f) (δ : Γ) (g : G) : s.ker f δ g = f (g⁻¹ * B.ι δ * s.θ g) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U g
  unfold Base.Tw.ker
  rw [hu]
  have e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * u) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u) := by
    simp only [map_mul, mul_inv_rev, Subgroup.coe_inv, mul_assoc]
  rw [e, hf.left, hf.right, map_inv]
  simp

private theorem FF_tr (δ : Γ) (y : G ⧸ B.U) : FF s f δ y = LinearMap.trace ℂ V (Tk s f y.out y.out (s.θΓ.symm δ)) := by
  unfold FF Tk Base.Tw.ker
  have hθ : s.θ (B.ι (s.θΓ.symm δ) * Quotient.out y) = B.ι δ * s.θ (Quotient.out y) := by
    rw [map_mul, s.comm, MulEquiv.apply_symm_apply]
  have hL : s.Θ ∘ₗ B.W (s.θΓ.symm δ) = B.W δ ∘ₗ s.Θ := by
    ext v
    simp [s.int]
  rw [hθ, hL, map_smul, smul_eq_mul]
  simp only [mul_assoc]

private theorem cusp_function_invariant (hf : s.IsTest f) (δ : Γ) (y : G ⧸ B.U) {z : Γ} (hz : z ∈ B.Γ₀) : FF s f (δ * z) y = FF s f δ y := by
  set u : B.U := ⟨B.ι z, B.memU z hz⟩ with hu
  have hθz : s.θ (B.ι z) = B.ι z := by rw [s.comm, s.fix z hz]
  have hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z :=
    (Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm
  have hk : s.ker f (δ * z) y = ((B.ω u)⁻¹ : ℂˣ) * s.ker f δ y := by
    unfold Base.Tw.ker
    have e : (Quotient.out y)⁻¹ * B.ι (δ * z) * s.θ (Quotient.out y) =
        ((Quotient.out y)⁻¹ * B.ι δ * s.θ (Quotient.out y)) * s.θ (u : G) := by
      rw [map_mul, show (u : G) = B.ι z from rfl, hθz]
      simp only [mul_assoc, hc]
    rw [e, hf.right]
  have ht : LinearMap.trace ℂ V (B.W (δ * z) ∘ₗ s.Θ) = (B.ω u : ℂ) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) := by
    have hW : B.W (δ * z) ∘ₗ s.Θ = (B.ω u : ℂ) • (B.W δ ∘ₗ s.Θ) := by
      ext v
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, B.scal z hz, LinearMap.smul_apply, map_smul]
      rfl
    rw [hW, map_smul, smul_eq_mul]
  unfold FF
  rw [hk, ht, mul_mul_mul_comm, Units.inv_mul, one_mul]

private theorem ker_conj (hf : s.IsTest f) (δ x : Γ) (y : G ⧸ B.U) : s.ker f δ (B.ι x • y) = s.ker f (x⁻¹ * δ * s.θΓ x) y := by
  have hy : B.ι x • y = ((B.ι x * Quotient.out y : G) : G ⧸ B.U) := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  rw [hy, ker_mk hf]
  unfold Base.Tw.ker
  simp only [mul_inv_rev, map_mul, map_inv, s.comm, mul_assoc]

private theorem FF_conj [FiniteDimensional ℂ V] (hf : s.IsTest f) (δ x : Γ) (y : G ⧸ B.U) :
    FF s f δ (B.ι x • y) = FF s f (x⁻¹ * δ * s.θΓ x) y := by
  unfold FF
  rw [ker_conj hf]
  congr 1
  have e : B.W (x⁻¹ * δ * s.θΓ x) ∘ₗ s.Θ = B.W x⁻¹ * ((B.W δ ∘ₗ s.Θ) * B.W x) := by
    ext v
    simp [map_mul, s.int]
  rw [e, LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem termC [FiniteDimensional ℂ V] (hB : B.Fin) (hf : s.IsTest f) (δ : Γ) : letI := act B
    s.term f δ = ∑ᶠ a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ),
      (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out := by
  letI := act B
  haveI := normal0 B
  have hle : B.Γ₀ ≤ s.Cent δ := by
    intro z hz
    show ∃ w ∈ B.Γ₀, z⁻¹ * δ * s.θΓ z = δ * w
    refine ⟨1, B.Γ₀.one_mem, ?_⟩
    rw [s.fix z hz, mul_one, mul_assoc, (Subgroup.mem_center_iff.mp (B.cenΓ hz) δ), inv_mul_cancel_left]
  have hinv : ∀ h ∈ s.Cent δ, ∀ y : G ⧸ B.U, FF s f δ (h • y) = FF s f δ y := by
    intro h hh y
    obtain ⟨w, hw, hhw⟩ := hh
    show FF s f δ (B.ι h • y) = _
    rw [FF_conj hf, hhw, cusp_function_invariant hf δ y hw]
  have hfin : {b : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U) | FF s f δ (Quotient.out b) ≠ 0}.Finite := by
    obtain ⟨S, hS⟩ := centFin Γ G V B hB s f hf δ
    refine (S.finite_toSet.image (fun g : G =>
      (Quotient.mk'' ((g : G ⧸ B.U)) : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U)))).subset ?_
    intro b hb
    have hk : s.ker f δ (Quotient.out b) ≠ 0 := fun h0 => hb (by unfold FF; rw [h0, zero_mul])
    obtain ⟨t, s1, hs1, u, hu, hy⟩ := hS _ hk
    refine ⟨s1, hs1, ?_⟩
    rw [← Quotient.out_eq b]
    apply Quotient.sound
    show (s1 : G ⧸ B.U) ∈ MulAction.orbit (s.Cent δ) (Quotient.out b)
    refine ⟨t⁻¹, ?_⟩
    conv_lhs => rw [← QuotientGroup.out_eq' (Quotient.out b)]
    show ((B.ι ((t⁻¹ : s.Cent δ) : Γ) * Quotient.out (Quotient.out b) : G) : G ⧸ B.U) = s1
    rw [hy]
    apply QuotientGroup.eq.mpr
    have e : (B.ι ((t⁻¹ : s.Cent δ) : Γ) * ((B.ι.comp (s.Cent δ).subtype) t * s1 * u))⁻¹ * s1 = u⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact B.U.inv_mem hu
  obtain ⟨-, hC⟩ := countC B.Γ₀ (s.Cent δ) (triv0 B) hle (stab0 B hB) (FF s f δ) hinv hfin
  have lhs : (fun a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ) =>
      (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out) =
      fun a => (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • FF s f δ (a.2.out⁻¹ • a.1.out) := by
    funext a
    rw [smul_eq_mul]
    congr 1
    rw [show (a.2.out⁻¹ • a.1.out : G ⧸ B.U) = B.ι a.2.out⁻¹ • a.1.out from rfl, FF_conj hf, inv_inv]
  rw [lhs, hC]
  unfold Base.Tw.term gqOn gq
  rw [mul_comm, finsum_mul]
  apply finsum_congr
  intro b
  unfold FF
  rw [smul_eq_mul, div_eq_mul_inv]
  have key : ∀ n m : ℕ, n = m → s.ker f δ (Quotient.out b) * (n : ℂ)⁻¹ * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) =
      (m : ℂ)⁻¹ * (s.ker f δ (Quotient.out b) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)) := by
    intro n m h
    rw [h]
    ring
  apply key
  rw [← Subgroup.relIndex_subgroupOf inf_le_left, Subgroup.inf_subgroupOf_left]
  congr 1

end

private theorem trace_mul_re_nonneg_of_posSemidef {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    {B : Base Γ G V} {s : B.Tw} {f : G → ℂ} (hf : s.IsTest f) (ε : Γ) (y : G ⧸ B.U) {z : Γ}
    (hz : z ∈ B.Γ₀) : s.ker f (ε * z) y = ((B.ω ⟨B.ι z, B.memU z hz⟩)⁻¹ : ℂˣ) * s.ker f ε y := by
  have hθz : s.θ (B.ι z) = B.ι z := by rw [s.comm, s.fix z hz]
  have hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z :=
    (Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm
  unfold Base.Tw.ker
  have e : (Quotient.out y)⁻¹ * B.ι (ε * z) * s.θ (Quotient.out y) =
      ((Quotient.out y)⁻¹ * B.ι ε * s.θ (Quotient.out y)) * s.θ ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) := by
    rw [map_mul, show ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) = B.ι z from rfl, hθz]
    simp only [mul_assoc, hc]
  rw [e, hf.right]

private theorem sum_phi_add_star_eq_trace {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    {B : Base Γ G V} (s : B.Tw) (δ₀ x : Γ) :
    ∃ w ∈ B.Γ₀, Quotient.out (x : Γ ⧸ s.Cent δ₀) * δ₀ * s.θΓ (Quotient.out (x : Γ ⧸ s.Cent δ₀))⁻¹ =
      x * δ₀ * s.θΓ x⁻¹ * w := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (s.Cent δ₀) x
  obtain ⟨z, hz, hcz⟩ := c.2
  have hzc : ∀ g : Γ, g * z⁻¹ = z⁻¹ * g := fun g =>
    Subgroup.mem_center_iff.mp (B.cenΓ (B.Γ₀.inv_mem hz)) g
  refine ⟨z⁻¹, B.Γ₀.inv_mem hz, ?_⟩
  have key : (c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹ = δ₀ * z⁻¹ := by
    rw [map_inv, mul_inv_eq_iff_eq_mul]
    have h1 : δ₀ * s.θΓ c = c * (δ₀ * z) := by
      rw [← hcz]
      group
    calc (c : Γ) * δ₀ = c * (δ₀ * z) * z⁻¹ := by group
      _ = δ₀ * s.θΓ c * z⁻¹ := by rw [h1]
      _ = δ₀ * z⁻¹ * s.θΓ c := by rw [mul_assoc, hzc, ← mul_assoc]
  rw [hc]
  calc x * (c : Γ) * δ₀ * s.θΓ (x * c)⁻¹ = x * ((c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹) * s.θΓ x⁻¹ := by
        rw [mul_inv_rev, map_mul]
        group
    _ = x * δ₀ * s.θΓ x⁻¹ * z⁻¹ := by
        rw [key]
        simp only [mul_assoc, hzc (s.θΓ x⁻¹)]

theorem UpperTheory.V.Z.Sym.Tf.trace :
    UpperTheory.V.Z.Sym.Tf.Trace := by
  intro Γ G V _ _ _ _ _ B hB s f hf I δ hinj hcov
  letI := act B
  haveI := finQ B hB
  have hHD : HD s f := finD B hB s f hf
  have hzc : ∀ z ∈ B.Γ₀, ∀ g : Γ, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (B.cenΓ hz) g
  let e : (i : I) → Γ ⧸ s.Cent (δ i) → Γ := fun i a => Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹
  let m : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) →
      orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) :=
    fun p => (p.2.1, (((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ) : Γ ⧸ B.Γ₀))
  let ε : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → Γ := fun b => s.θΓ (Quotient.out b.2)⁻¹
  have K1 : ∀ p, ∃ w ∈ B.Γ₀, ε (m p) = e p.1 p.2.2 * w := by
    intro p
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul B.Γ₀ ((s.θΓ.symm (e p.1 p.2.2))⁻¹)
    refine ⟨(w : Γ)⁻¹, B.Γ₀.inv_mem w.2, ?_⟩
    show s.θΓ (Quotient.out ((((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ)) : Γ ⧸ B.Γ₀))⁻¹ = _
    rw [hw, mul_inv_rev, inv_inv, map_mul, MulEquiv.apply_symm_apply, map_inv, s.fix _ w.2]
    exact (hzc _ (B.Γ₀.inv_mem w.2) _).symm
  have Minj : Function.Injective m := by
    rintro ⟨i, o, a⟩ ⟨i', o', a'⟩ h
    have ho : o = o' := congrArg Prod.fst h
    have ha : (((s.θΓ.symm (e i a))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = (((s.θΓ.symm (e i' a'))⁻¹ : Γ) : Γ ⧸ B.Γ₀) :=
      congrArg Prod.snd h
    have hu : s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹ ∈ B.Γ₀ := by
      have := QuotientGroup.eq.mp ha
      rwa [inv_inv] at this
    have hfix := s.fix _ hu
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hfix
    obtain ⟨z, hz, hEz⟩ : ∃ z ∈ B.Γ₀, e i' a' = e i a * z := by
      refine ⟨(s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹)⁻¹, B.Γ₀.inv_mem hu, ?_⟩
      rw [hzc _ (B.Γ₀.inv_mem hu) (e i a), ← hfix]
      group
    have h2 : Quotient.out a' * δ i' * s.θΓ (Quotient.out a')⁻¹ =
        Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹ * z := hEz
    have gen : ∀ d d' q q' : Γ, q' * d' * s.θΓ q'⁻¹ = q * d * s.θΓ q⁻¹ * z →
        d' = (q⁻¹ * q')⁻¹ * d * s.θΓ (q⁻¹ * q') * z := by
      intro d d' q q' hq
      have h3 : d' = q'⁻¹ * (q * d * s.θΓ q⁻¹ * z) * s.θΓ q' := by
        rw [← hq, map_inv]
        group
      calc d' = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (z * s.θΓ q') := by
            rw [h3, map_inv]
            group
        _ = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (s.θΓ q' * z) := by rw [← hzc z hz (s.θΓ q')]
        _ = _ := by
            rw [map_mul, map_inv]
            group
    have hx := gen _ _ _ _ h2
    have hii := hinj i i' ⟨_, z, hz, hx⟩
    subst hii
    have hcent : (Quotient.out a)⁻¹ * Quotient.out a' ∈ s.Cent (δ i) :=
      ⟨z⁻¹, B.Γ₀.inv_mem hz, eq_mul_inv_of_mul_eq hx.symm⟩
    have haa : a = a' := by
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a']
      exact QuotientGroup.eq.mpr hcent
    rw [ho, haa]
  let F' : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → ℂ := fun b =>
    (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ *
      LinearMap.trace ℂ V (Tk s f (Quotient.out (Quotient.out b.1)) (Quotient.out (Quotient.out b.1))
        (Quotient.out b.2)⁻¹)
  let F : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) → ℂ := fun p =>
    (B.Γ₀.relIndex (stabilizer Γ (Quotient.out p.2.1)) : ℂ)⁻¹ * FF s f (e p.1 p.2.2) (Quotient.out p.2.1)
  have hF'FF : ∀ b, F' b = (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ *
      FF s f (ε b) (Quotient.out b.1) := by
    intro b
    show _ * _ = _ * FF s f (s.θΓ (Quotient.out b.2)⁻¹) _
    rw [FF_tr, MulEquiv.symm_apply_apply]
  have hFeq : ∀ p, F p = ((((fun _ => 1) : _ → ℕ) (m p) : ℕ) : ℂ)⁻¹ • F' (m p) := by
    intro p
    rw [Nat.cast_one, inv_one, one_smul, hF'FF]
    obtain ⟨w, hw, hwe⟩ := K1 p
    rw [hwe, cusp_function_invariant hf _ _ hw]
  have hKfin : {b : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) | s.ker f (ε b) (Quotient.out b.1) ≠ 0}.Finite := by
    refine (Set.finite_iUnion (fun o : orbitRel.Quotient Γ (G ⧸ B.U) =>
      (Set.finite_singleton o).prod (f_fin hHD (Quotient.out (Quotient.out o)) (Quotient.out (Quotient.out o))))).subset ?_
    rintro ⟨o, x⟩ hb
    have hb' : f ((Quotient.out (Quotient.out o))⁻¹ * B.ι (s.θΓ (Quotient.out x)⁻¹) *
        s.θ (Quotient.out (Quotient.out o))) ≠ 0 := hb
    refine Set.mem_iUnion.mpr ⟨o, Set.mem_singleton o, ?_⟩
    show f _ ≠ 0
    convert hb' using 2
    rw [map_mul, s.comm, mul_assoc]
  have hF'fin : (Function.support F').Finite := hKfin.subset (fun b hb h0 => hb (by
    rw [hF'FF]
    unfold FF
    rw [h0]
    ring))
  have Msurj : ∀ b, s.ker f (ε b) (Quotient.out b.1) ≠ 0 → ∃ p, m p = b := by
    rintro ⟨o, x⟩ hb
    obtain ⟨i, y, z, hz, hy⟩ := hcov _ ⟨_, hb⟩
    refine ⟨⟨i, o, ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_⟩
    obtain ⟨w, hw, hwe⟩ := sum_phi_add_star_eq_trace s (δ i) y⁻¹
    have hy' : s.θΓ (Quotient.out x)⁻¹ = y⁻¹ * δ i * s.θΓ y * z := hy
    have hE : e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i)) = s.θΓ (Quotient.out x)⁻¹ * (z⁻¹ * w) := by
      show Quotient.out _ * δ i * s.θΓ (Quotient.out _)⁻¹ = _
      rw [hwe, inv_inv, hy']
      group
    have hsym : ∀ q ∈ B.Γ₀, s.θΓ.symm q = q := fun q hq =>
      (MulEquiv.symm_apply_eq _).mpr (s.fix q hq).symm
    have hzw : z⁻¹ * w ∈ B.Γ₀ := B.Γ₀.mul_mem (B.Γ₀.inv_mem hz) hw
    refine Prod.ext rfl ?_
    show (((s.θΓ.symm (e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x
    rw [← QuotientGroup.out_eq' x, QuotientGroup.eq, inv_inv, hE, map_mul, MulEquiv.symm_apply_apply,
      hsym _ hzw, mul_assoc, ← hzc _ hzw (Quotient.out x), ← mul_assoc, inv_mul_cancel, one_mul]
    exact hzw
  have hcard : ∀ b, F' b ≠ 0 → ((fun _ => 1) : _ → ℕ) b ≠ 0 ∧
      Nat.card {p // m p = b} = ((fun _ => 1) : _ → ℕ) b := by
    intro b hb
    refine ⟨one_ne_zero, Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun p q => Subtype.ext (Minj (p.2.trans q.2.symm))⟩, ?_⟩⟩
    have hk : s.ker f (ε b) (Quotient.out b.1) ≠ 0 := fun h0 => hb (by
      rw [hF'FF]
      unfold FF
      rw [h0]
      ring)
    obtain ⟨p, hp⟩ := Msurj b hk
    exact ⟨⟨p, hp⟩⟩
  obtain ⟨hFfin, hsum⟩ := sum_fib m F F' (fun _ => 1) hF'fin hcard hFeq
  refine ⟨?_, ?_⟩
  · have hP : {p : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) |
        s.ker f (e p.1 p.2.2) (Quotient.out p.2.1) ≠ 0} ⊆
        m ⁻¹' {b | s.ker f (ε b) (Quotient.out b.1) ≠ 0} := by
      intro p hp
      obtain ⟨w, hw, hwe⟩ := K1 p
      show s.ker f (ε (m p)) (Quotient.out (m p).1) ≠ 0
      rw [hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]
      exact mul_ne_zero (Units.ne_zero _) hp
    have hPfin := (hKfin.preimage Minj.injOn).subset hP
    refine (hPfin.image Sigma.fst).subset ?_
    rintro i ⟨y, hy⟩
    obtain ⟨g, hg⟩ : ∃ g : Γ, g • y = Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)) :=
      Quotient.mk_out (s := orbitRel Γ (G ⧸ B.U)) y
    refine ⟨⟨i, (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)), ((g : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_, rfl⟩
    obtain ⟨w, hw, hwe⟩ := sum_phi_add_star_eq_trace s (δ i) g
    show s.ker f (e i ((g : Γ) : Γ ⧸ s.Cent (δ i))) (Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U))) ≠ 0
    rw [show e i ((g : Γ) : Γ ⧸ s.Cent (δ i)) = _ from hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]
    refine mul_ne_zero (Units.ne_zero _) ?_
    rw [← hg, show g • y = B.ι g • y from rfl, ker_conj hf]
    convert hy using 2
    rw [map_inv]
    group
  · rw [traceA hB hf hHD]
    calc _ = ∑ᶠ (a : orbitRel.Quotient Γ (G ⧸ B.U)) (b : Γ ⧸ B.Γ₀), F' (a, b) := rfl
      _ = ∑ᶠ ab, F' ab := (finsum_curry F' hF'fin).symm
      _ = ∑ᶠ p, F p := hsum.symm
      _ = ∑ᶠ (i : I) (q : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))), F ⟨i, q⟩ := finsum_sig F hFfin
      _ = ∑ᶠ i, s.term f (δ i) := finsum_congr fun i => (termC hB hf (δ i)).symm
