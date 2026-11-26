module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvIrrAvg
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvIrrComm
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvIrrPre
noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def IsPsd (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop := (∀ x y, starRingEnd ℂ (B x y) = B y x) ∧ ∀ x, 0 ≤ (B x x).re

def Pre (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (_ : IsPsd B) : Type := M

variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

instance : AddCommGroup (Pre B hB) := inferInstanceAs (AddCommGroup M)
instance : Module ℂ (Pre B hB) := inferInstanceAs (Module ℂ M)

instance core : PreInnerProductSpace.Core ℂ (Pre B hB) where
  inner x y := B x y
  conj_inner_symm x y := hB.1 y x
  re_inner_nonneg x := hB.2 x
  add_left x y z := LinearMap.map_add₂ B x y z
  smul_left x y r := (LinearMap.map_smulₛₗ₂ B r x y).trans (smul_eq_mul _ _)

instance : SeminormedAddCommGroup (Pre B hB) := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (Pre B hB) := InnerProductSpace.ofCore (core B hB)

abbrev Hs := Completion (Pre B hB)

def iota : M →ₗ[ℂ] Hs B hB := (Completion.toComplL : Pre B hB →L[ℂ] Hs B hB).toLinearMap

theorem iota_apply (x : M) : iota B hB x = ((show Pre B hB from x : Pre B hB) : Hs B hB) := rfl

theorem inner_iota (x y : M) : ⟪iota B hB x, iota B hB y⟫_ℂ = B x y := by
  rw [iota_apply, iota_apply, Completion.inner_coe]; rfl

theorem re_B (x : M) : (B x x).re = ‖iota B hB x‖ ^ 2 := by
  have h := @inner_self_eq_norm_sq ℂ _ _ _ _ (iota B hB x)
  rw [inner_iota] at h
  simpa using h

theorem ind {p : Hs B hB → Prop} (hp : IsClosed {y | p y}) (h : ∀ x : M, p (iota B hB x)) (y : Hs B hB) :
    p y :=
  Completion.induction_on y hp fun a => h a

theorem ext_iota {T S : Hs B hB →L[ℂ] Hs B hB} (h : ∀ x, T (iota B hB x) = S (iota B hB x)) : T = S :=
  ContinuousLinearMap.ext fun y => ind B hB (p := fun y => T y = S y) (isClosed_eq T.continuous S.continuous) h y

variable {G : Type} [Group G] (ρ : Representation ℂ G M)

theorem rho_mul (g h : G) (x : M) : ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl
theorem rho_one (x : M) : ρ 1 x = x := by rw [map_one]; rfl
theorem rho_inv (g : G) (x : M) : ρ g⁻¹ (ρ g x) = x := by rw [← rho_mul, inv_mul_cancel, rho_one]

variable (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def rhoP (g : G) : Pre B hB →ₗ[ℂ] Pre B hB := ρ g

include hinv in
theorem norm_rhoP (g : G) (x : Pre B hB) : ‖rhoP B hB ρ g x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) x]
  rw [show ⟪rhoP B hB ρ g x, rhoP B hB ρ g x⟫_ℂ = ⟪x, x⟫_ℂ from hinv g x x]

def piF (g : G) : Hs B hB →L[ℂ] Hs B hB :=
  (LinearMap.mkContinuous (rhoP B hB ρ g) 1 fun x => by rw [one_mul, norm_rhoP B hB ρ hinv]).completion

theorem piF_iota (g : G) (x : M) : piF B hB ρ hinv g (iota B hB x) = iota B hB (ρ g x) := by
  rw [iota_apply, piF, ContinuousLinearMap.completion_apply_coe]; rfl

def pi : G →* (Hs B hB →L[ℂ] Hs B hB) where
  toFun := piF B hB ρ hinv
  map_one' := ext_iota B hB fun x => by rw [piF_iota, rho_one]; rfl
  map_mul' g h := ext_iota B hB fun x => by
    rw [ContinuousLinearMap.mul_apply, piF_iota, piF_iota, piF_iota, rho_mul]

theorem pi_iota (g : G) (x : M) : pi B hB ρ hinv g (iota B hB x) = iota B hB (ρ g x) := piF_iota B hB ρ hinv g x

theorem norm_pi (g : G) (y : Hs B hB) : ‖pi B hB ρ hinv g y‖ = ‖y‖ :=
  ind B hB (p := fun y => ‖pi B hB ρ hinv g y‖ = ‖y‖)
    (isClosed_eq (continuous_norm.comp (pi B hB ρ hinv g).continuous) continuous_norm)
    (fun x => by rw [pi_iota, iota_apply, iota_apply, Completion.norm_coe, Completion.norm_coe]; exact norm_rhoP B hB ρ hinv g x) y

theorem pi_inner (g : G) (u v : Hs B hB) : ⟪pi B hB ρ hinv g u, pi B hB ρ hinv g v⟫_ℂ = ⟪u, v⟫_ℂ :=
  let V : Hs B hB →ₗᵢ[ℂ] Hs B hB := { toLinearMap := (pi B hB ρ hinv g : Hs B hB →ₗ[ℂ] Hs B hB), norm_map' := norm_pi B hB ρ hinv g }
  V.inner_map_map u v

theorem inner_left (g : G) (v w : Hs B hB) : ⟪pi B hB ρ hinv g v, w⟫_ℂ = ⟪v, pi B hB ρ hinv g⁻¹ w⟫_ℂ := by
  rw [← pi_inner B hB ρ hinv g v, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem star_pi (g : G) : star (pi B hB ρ hinv g) = pi B hB ρ hinv g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [inner_left B hB ρ hinv g⁻¹, inv_inv]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

theorem comm_apply {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {S T : E →L[ℂ] E}
    (h : S * T = T * S) (v : E) : S (T v) = T (S v) := by
  have := congrArg (fun A : E →L[ℂ] E => A v) h
  exact this

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

def formOf (S : Hs B hB →L[ℂ] Hs B hB) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪iota B hB x, S (iota B hB y)⟫_ℂ)
    (fun x₁ x₂ y => by simp [map_add (f := _), inner_add_left])
    (fun c x y => by simp [map_smul, inner_smul_left])
    (fun x y₁ y₂ => by simp [map_add (f := _), inner_add_right])
    (fun c x y => by simp [map_smul, inner_smul_right])

theorem formOf_apply (S : Hs B hB →L[ℂ] Hs B hB) (x y : M) :
    formOf B hB S x y = ⟪iota B hB x, S (iota B hB y)⟫_ℂ := rfl

variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

theorem scalar_sa (hext : IsExtremeForm ρ B) (S : Hs B hB →L[ℂ] Hs B hB) (hS : IsSelfAdjoint S)
    (hc : ∀ g, S * pi B hB ρ hinv g = pi B hB ρ hinv g * S) : ∃ c : ℂ, S = c • 1 := by
  set a : ℝ := (2 * (‖S‖ + 1))⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hsym : ∀ u v, ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ := fun u v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]
  have hherm : ∀ x y, starRingEnd ℂ (formOf B hB S x y) = formOf B hB S y x := fun x y => by
    rw [formOf_apply, formOf_apply, inner_conj_symm, hsym]
  have hinvQ : ∀ g x y, formOf B hB S (ρ g x) (ρ g y) = formOf B hB S x y := fun g x y => by
    rw [formOf_apply, formOf_apply, ← pi_iota B hB ρ hinv, ← pi_iota B hB ρ hinv, comm_apply (hc g), pi_inner]
  have hbd : ∀ x, |(formOf B hB S x x).re| ≤ ‖S‖ * ‖iota B hB x‖ ^ 2 := fun x => by
    rw [formOf_apply]
    calc _ ≤ ‖⟪iota B hB x, S (iota B hB x)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖iota B hB x‖ * ‖S (iota B hB x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖iota B hB x‖ * (‖S‖ * ‖iota B hB x‖) := by gcongr; exact S.le_opNorm _
      _ = _ := by ring
  have key : ∀ x, |a * (formOf B hB S x x).re| ≤ (B x x).re / 2 := fun x => by
    rw [re_B B hB, abs_mul, abs_of_pos ha]
    calc a * |(formOf B hB S x x).re| ≤ a * ((‖S‖ + 1) * ‖iota B hB x‖ ^ 2) := by
          gcongr; exact (hbd x).trans (by gcongr; linarith)
      _ = _ := by rw [ha_def]; field_simp
  have h1 : IsInvForm ρ (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_add (f := _), map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  have h2 : IsInvForm ρ (B - (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S)) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_sub, map_add (f := _), map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  obtain ⟨c, hc'⟩ := hext.2 _ h1 h2
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hQ : ∀ x y, formOf B hB S x y = ((a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))) * B x y := fun x y => by
    have h := hc' x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ ha']
    linear_combination h
  set d := (a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))
  have hQ' : ∀ x y : M, ⟪iota B hB x, S (iota B hB y)⟫_ℂ = d * ⟪iota B hB x, iota B hB y⟫_ℂ := fun x y => by
    rw [inner_iota, ← formOf_apply]; exact hQ x y
  have hall : ∀ u v : Hs B hB, ⟪u, S v⟫_ℂ = d * ⟪u, v⟫_ℂ := by
    intro u v
    refine Completion.induction_on₂ u v ?_ fun p q => ?_
    · exact isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd))
        (continuous_const.mul (continuous_fst.inner continuous_snd))
    · exact hQ' p q
  refine ⟨d, ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_⟩
  rw [hall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]

theorem commutant (hext : IsExtremeForm ρ B) (T : Hs B hB →L[ℂ] Hs B hB)
    (hT : ∀ g, T * pi B hB ρ hinv g = pi B hB ρ hinv g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g, star T * pi B hB ρ hinv g = pi B hB ρ hinv g * star T := fun g => by
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, star_pi, inv_inv] at h
    exact h.symm
  have hre : ∀ g, (realPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * realPart T := fun g => by
    simp only [realPart_apply_coe, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hT, hT']
  have him : ∀ g, (imaginaryPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * imaginaryPart T := fun g => by
    simp only [imaginaryPart_apply_coe, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hT, hT']
  obtain ⟨c₁, h₁⟩ := scalar_sa B hB ρ hinv hext _ (realPart T).prop hre
  obtain ⟨c₂, h₂⟩ := scalar_sa B hB ρ hinv hext _ (imaginaryPart T).prop him
  refine ⟨c₁ + Complex.I * c₂, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h₁, h₂, smul_smul, add_smul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def fixSub (K : Subgroup G) : Submodule ℂ M where
  carrier := {a | ∀ κ ∈ K, ρ κ a = a}
  add_mem' {a b} ha hb κ hκ := by rw [map_add (f := _), ha κ hκ, hb κ hκ]
  zero_mem' κ _ := map_zero _
  smul_mem' c a ha κ hκ := by rw [map_smul, ha κ hκ]

include hinv in
theorem avg_exists [TopologicalSpace G] [IsTopologicalGroup G] (hsm : IsSmooth ρ) (Z : Submodule ℂ M)
    (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (x : M)
    (hx : ∀ κ ∈ K, ρ κ x = x) (z : M) (hz : z ∈ Z) :
    ∃ a ∈ Z, (∀ κ ∈ K, ρ κ a = a) ∧
      dist (iota B hB x) (iota B hB a) ≤ dist (iota B hB x) (iota B hB z) := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hf : Continuous fun g : G => ρ g z := by
    refine continuous_discrete_rng.2 fun b => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨(fun h => g⁻¹ * h) ⁻¹' {h | ρ h z = z}, fun h hh => ?_,
      (continuous_const_mul g⁻¹).isOpen_preimage _ (hsm z), ?_⟩
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at hh hg ⊢
      rw [← hg, show h = g * (g⁻¹ * h) by group, rho_mul, hh]
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, rho_one]
  have hfin : ((fun g : G => ρ g z) '' (K : Set G)).Finite := (hKc.image hf).finite_of_discrete
  set O := hfin.toFinset with hO
  have hmem : ∀ m, m ∈ O ↔ ∃ k ∈ K, ρ k z = m := fun m => by
    rw [hO, Set.Finite.mem_toFinset]; rfl
  have hzO : z ∈ O := (hmem z).2 ⟨1, K.one_mem, rho_one ρ z⟩
  have hcard : (O.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  have hcardC : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ m ∈ O, m, Z.smul_mem _ (Z.sum_mem fun m hm => ?_), fun κ hκ => ?_, ?_⟩
  · obtain ⟨k, _, rfl⟩ := (hmem m).1 hm
    exact hZ k z hz
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
      apply congrArg (fun v : M => (O.card : ℂ)⁻¹ • v)
      refine Finset.sum_nbij' (fun m => ρ κ m) (fun m => ρ κ⁻¹ m) (fun m hm => ?_) (fun m hm => ?_)
        (fun m _ => rho_inv ρ κ m) (fun m _ => ?_) (fun _ _ => rfl)
      · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
        exact (hmem _).2 ⟨κ * k, K.mul_mem hκ hk, rho_mul ρ κ k z⟩
      · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
        exact (hmem _).2 ⟨κ⁻¹ * k, K.mul_mem (K.inv_mem hκ) hk, rho_mul ρ κ⁻¹ k z⟩
      · simp
  · have hdist : ∀ m ∈ O, ‖iota B hB x - iota B hB m‖ = ‖iota B hB x - iota B hB z‖ := by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      have e : iota B hB x - iota B hB (ρ k z) = pi B hB ρ hinv k (iota B hB x - iota B hB z) := by
        rw [map_sub, pi_iota, pi_iota, hx k hk]
      rw [e, norm_pi]
    have hsum : iota B hB x - iota B hB ((O.card : ℂ)⁻¹ • ∑ m ∈ O, m) =
        (O.card : ℂ)⁻¹ • ∑ m ∈ O, (iota B hB x - iota B hB m) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, map_smul, map_sum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcardC, one_smul]
    rw [dist_eq_norm, dist_eq_norm, hsum, norm_smul]
    calc ‖((O.card : ℂ))⁻¹‖ * ‖∑ m ∈ O, (iota B hB x - iota B hB m)‖
        ≤ ‖((O.card : ℂ))⁻¹‖ * ∑ m ∈ O, ‖iota B hB x - iota B hB m‖ := by gcongr; exact norm_sum_le _ _
      _ = ‖((O.card : ℂ))⁻¹‖ * (O.card * ‖iota B hB x - iota B hB z‖) := by
          rw [Finset.sum_congr rfl hdist, Finset.sum_const, nsmul_eq_mul]
      _ = ‖iota B hB x - iota B hB z‖ := by
          rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

include hinv in
theorem closure_top (hext : IsExtremeForm ρ B) (Z : Submodule ℂ M) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z)
    (z₀ : M) (hz₀ : z₀ ∈ Z) (hne : B z₀ z₀ ≠ 0) (y : Hs B hB) :
    y ∈ (Z.map (iota B hB)).topologicalClosure := by
  set W := (Z.map (iota B hB)).topologicalClosure with hW
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hWinv : ∀ g, ∀ w ∈ W, pi B hB ρ hinv g w ∈ W := by
    intro g w hw
    rw [← SetLike.mem_coe, hW, Submodule.topologicalClosure_coe] at hw ⊢
    refine map_mem_closure (pi B hB ρ hinv g).continuous hw fun v hv => ?_
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨ρ g z, hZ g z hz, (pi_iota B hB ρ hinv g z).symm⟩
  have hP : ∀ g, W.starProjection * pi B hB ρ hinv g = pi B hB ρ hinv g * W.starProjection := by
    intro g
    refine ContinuousLinearMap.ext fun v => ?_
    show W.starProjection (pi B hB ρ hinv g v) = pi B hB ρ hinv g (W.starProjection v)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hWinv g _ (W.starProjection_apply_mem v)
    · intro w hw
      rw [← map_sub, inner_left]
      exact W.starProjection_inner_eq_zero v _ (hWinv _ _ hw)
  obtain ⟨c, hc⟩ := commutant B hB ρ hinv hext _ hP
  have hι0 : iota B hB z₀ ≠ 0 := fun h => hne (by rw [← inner_iota B hB, h, inner_zero_left])
  have hmem : iota B hB z₀ ∈ W := Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hz₀)
  have h1 : W.starProjection (iota B hB z₀) = iota B hB z₀ := Submodule.starProjection_eq_self_iff.2 hmem
  rw [hc] at h1
  have hc1 : c = 1 := by
    have e : (c - 1) • iota B hB z₀ = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]; simpa using h1
    rcases smul_eq_zero.1 e with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hι0
  apply Submodule.starProjection_eq_self_iff.1
  rw [hc, hc1, one_smul]; rfl

end DiscreteGroups.sglob.LConv.IrreduciblePresentation

namespace DiscreteGroups.sglob.LConv

open IrreduciblePresentation in
theorem extremeIrred : ExtremeIrred := by
  intro G M _ _ _ _ _ ρ hsm hK hAdm B hext Z hZ
  by_cases h0 : ∀ z ∈ Z, B z z = 0
  · exact Or.inl h0
  right
  simp only [not_forall, exists_prop] at h0
  obtain ⟨z₀, hz₀, hne⟩ := h0
  have hB : IsPsd B := ⟨hext.1.1, hext.1.2.1⟩
  have hinv := hext.1.2.2
  intro x
  obtain ⟨K, hKo, hKc, hxK⟩ := hK x
  obtain ⟨s, hs⟩ := hAdm K hKo hKc (Hs B hB) (pi B hB ρ hinv) (norm_pi B hB ρ hinv)
    (commutant B hB ρ hinv hext)
  set L : Submodule ℂ (Hs B hB) := (Z ⊓ fixSub ρ K).map (iota B hB) with hL
  have hle : L ≤ Submodule.span ℂ (s : Set (Hs B hB)) := by
    intro v hv
    obtain ⟨a, ⟨_, haK⟩, rfl⟩ := Submodule.mem_map.1 hv
    exact hs _ fun κ hκ => by rw [pi_iota, haK κ hκ]
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed (L : Set (Hs B hB)) := L.closed_of_finiteDimensional
  have hxL : iota B hB x ∈ L := by
    rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hxW := closure_top B hB ρ hinv hext Z hZ z₀ hz₀ hne (iota B hB x)
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hxW
    obtain ⟨_, hb, hd⟩ := hxW ε hε
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hb
    obtain ⟨a, haZ, haK, hda⟩ := avg_exists B hB ρ hinv hsm Z hZ K hKc x hxK z hz
    exact ⟨iota B hB a, Submodule.mem_map_of_mem ⟨haZ, haK⟩, lt_of_le_of_lt hda hd⟩
  obtain ⟨a, ⟨haZ, _⟩, ha⟩ := Submodule.mem_map.1 hxL
  refine ⟨a, haZ, ?_⟩
  rw [← inner_iota B hB, map_sub, ha, sub_self, inner_zero_left]

end DiscreteGroups.sglob.LConv
