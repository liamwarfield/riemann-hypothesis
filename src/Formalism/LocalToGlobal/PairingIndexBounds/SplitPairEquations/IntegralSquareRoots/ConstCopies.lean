module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemImgLatIff
noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {ι : Type} [Fintype ι] {V V₁ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]

structure Copies (e : V ≃ₗ[ℂ] (ι → V₁)) (H : Sesq V) (H₁ : Sesq V₁) (α : V → ℂ) (α₁ : V₁ → ℂ)
    (Λ : AddSubgroup V) (Λ₁ : AddSubgroup V₁) (δ Ae : V ≃ₗ[ℂ] V) (δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁) : Prop where
  form : ∀ x y, H x y = ∑ i, H₁ (e x i) (e y i)
  char : ∀ x ∈ Λ, α x = ∏ i, α₁ (e x i)
  lat : ∀ x, x ∈ Λ ↔ ∀ i, e x i ∈ Λ₁
  map : ∀ x i, e (δ x) i = δ₁ (e x i)
  cay : ∀ x i, e (Ae x) i = Ae₁ (e x i)

theorem mem_imgLat_iff {W : Type} [AddCommGroup W] [Module ℂ W] (g : W ≃ₗ[ℂ] W) (M : AddSubgroup W) (x : W) :
    x ∈ imgLat (g : W →ₗ[ℂ] W) M ↔ g.symm x ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g.symm (g y) ∈ M
    rw [LinearEquiv.symm_apply_apply]; exact hy
  · intro h
    exact ⟨g.symm x, h, g.apply_symm_apply x⟩

theorem symm_coord (e : V ≃ₗ[ℂ] (ι → V₁)) (g : V ≃ₗ[ℂ] V) (g₁ : V₁ ≃ₗ[ℂ] V₁) (h : ∀ x i, e (g x) i = g₁ (e x i))
    (x : V) (i : ι) : e (g.symm x) i = g₁.symm (e x i) := by
  have := h (g.symm x) i
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, LinearEquiv.symm_apply_apply]

variable {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.mem_latA (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (x : V) :
    x ∈ latA Λ δ Ae ↔ ∀ i, e x i ∈ latA Λ₁ δ₁ Ae₁ := by
  unfold latA
  simp only [mem_imgLat_iff, AddSubgroup.mem_inf, c.lat, symm_coord e Ae Ae₁ c.cay, symm_coord e δ δ₁ c.map]
  exact forall_and.symm

def prodReps (e : V ≃ₗ[ℂ] (ι → V₁)) (S₁ : Finset V₁) : Finset V :=
  (Fintype.piFinset fun _ : ι => S₁).image e.symm

theorem mem_prodReps (S₁ : Finset V₁) (x : V) : x ∈ prodReps e S₁ ↔ ∀ i, e x i ∈ S₁ := by
  unfold prodReps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩ i
    rw [LinearEquiv.apply_symm_apply]
    exact Fintype.mem_piFinset.mp hp i
  · intro h
    exact ⟨e x, Fintype.mem_piFinset.mpr h, e.symm_apply_apply x⟩

theorem Copies.reps (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) {S₁ : Finset V₁}
    (hS : IsReps (latA Λ₁ δ₁ Ae₁) Λ₁ S₁) : IsReps (latA Λ δ Ae) Λ (prodReps e S₁) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (c.lat x).2 fun i => h1 _ ((mem_prodReps S₁ x).1 hx i)
  · intro x hx y hy hxy
    apply e.injective
    funext i
    refine h2 _ ((mem_prodReps S₁ x).1 hx i) _ ((mem_prodReps S₁ y).1 hy i) ?_
    have := (c.mem_latA (x - y)).1 hxy i
    rwa [map_sub] at this
  · intro y hy
    have hy' := (c.lat y).1 hy
    choose s hs hs' using fun i => h3 (e y i) (hy' i)
    refine ⟨e.symm s, (mem_prodReps S₁ _).2 fun i => by rw [LinearEquiv.apply_symm_apply]; exact hs i, ?_⟩
    refine (c.mem_latA _).2 fun i => ?_
    rw [map_sub, LinearEquiv.apply_symm_apply]
    exact hs' i

theorem Copies.phi (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) {x : V} (hx : x ∈ Λ) :
    phiC H α Ae x = ∏ i, phiC H₁ α₁ Ae₁ (e x i) := by
  unfold phiC
  rw [Finset.prod_mul_distrib, c.char x hx, ← Complex.exp_sum, c.form, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  unfold cayC
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, symm_coord e Ae Ae₁ c.cay]

theorem sqrt_pow' (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih]

theorem Copies.gauss (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) {S₁ : Finset V₁} (hS : ∀ x ∈ S₁, x ∈ Λ₁) :
    gaussC H α Ae (prodReps e S₁) = gaussC H₁ α₁ Ae₁ S₁ ^ Fintype.card ι := by
  unfold gaussC
  have hcard : (prodReps e S₁).card = S₁.card ^ Fintype.card ι := by
    unfold prodReps
    rw [Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
  have hsum : ∑ x ∈ prodReps e S₁, phiC H α Ae x = (∑ x ∈ S₁, phiC H₁ α₁ Ae₁ x) ^ Fintype.card ι := by
    unfold prodReps
    rw [Finset.sum_image (fun x _ y _ h => e.symm.injective h), ← Finset.card_univ, ← Finset.prod_const,
      Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Fintype.mem_piFinset.mp hp
    rw [c.phi ((c.lat _).2 fun i => by rw [LinearEquiv.apply_symm_apply]; exact hS _ (hp' i))]
    simp only [LinearEquiv.apply_symm_apply]
  rw [hcard, hsum, mul_pow, Nat.cast_pow, sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]

theorem det_copies [FiniteDimensional ℂ V₁] (e : V ≃ₗ[ℂ] (ι → V₁)) (g : V →ₗ[ℂ] V) (g₁ : V₁ →ₗ[ℂ] V₁)
    (h : ∀ x i, e (g x) i = g₁ (e x i)) : LinearMap.det g = LinearMap.det g₁ ^ Fintype.card ι := by
  rw [← LinearMap.det_conj g e, ← Finset.card_univ, ← Finset.prod_const, ← LinearMap.det_pi]
  congr 1
  ext x i
  simp [h]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {ι : Type} [Fintype ι] {V V₁ : Type}

section Idx

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]
  {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.idx (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (h : relIdx (latA Λ δ Ae) Λ ≠ 0) :
    relIdx (latA Λ₁ δ₁ Ae₁) Λ₁ ≠ 0 := by
  obtain ⟨S, hS⟩ := (repsExist V _ _ h).1
  let f : S → Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁ := fun x =>
    QuotientAddGroup.mk ⟨e x.1 i₀, (c.lat x.1).1 (hS.1 x.1 x.2) i₀⟩
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      have hY : e.symm (Pi.single i₀ (y : V₁)) ∈ Λ := by
        refine (c.lat _).2 fun i => ?_
        rw [LinearEquiv.apply_symm_apply]
        by_cases hi : i = i₀
        · subst hi; rw [Pi.single_eq_same]; exact y.2
        · rw [Pi.single_eq_of_ne hi]; exact Λ₁.zero_mem
      obtain ⟨x, hx, hxy⟩ := hS.2.2 _ hY
      refine ⟨⟨x, hx⟩, ?_⟩
      have h2 := (c.mem_latA _).1 hxy i₀
      rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.single_eq_same] at h2
      show (QuotientAddGroup.mk _ : Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) = QuotientAddGroup.mk y
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      show -(e x i₀) + (y : V₁) ∈ _
      rwa [neg_add_eq_sub]
  haveI : Finite (Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) := Finite.of_surjective f hf
  exact AddSubgroup.index_ne_zero_of_finite

end Idx

theorem unit_sq (a : ℂ) (ha : a ≠ 0) : ((‖a‖ : ℂ) / a) ^ 2 = conj a / a := by
  have h : ((‖a‖ : ℂ)) ^ 2 = a * conj a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [div_pow, h]
  field_simp

variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V₁] [Module ℂ V₁]
  [FiniteDimensional ℂ V₁]
  {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem const_copies (hLat : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) (hLine : AtMostLine H α Λ)
    (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (hH₁ : IsHerm H₁) (hP₁ : IsPosDef H₁)
    (hI₁ : IsIsom H₁ H₁ (δ₁ : V₁ →ₗ[ℂ] V₁)) (hA₁ : ∀ x, Ae₁ x = x - δ₁.symm x)
    (hn : Even (Fintype.card ι)) (hr : Even (Module.finrank ℂ V₁))
    (hG : ∀ S₁ : Finset V₁, IsReps (latA Λ₁ δ₁ Ae₁) Λ₁ S₁ → gaussC H₁ α₁ Ae₁ S₁ ^ 2 = 1)
    (θ : V → ℂ) (hθ : θ ∈ Th H α Λ) :
    pullInv δ θ = LinearMap.det (δ₁ : V₁ →ₗ[ℂ] V₁) ^ (Fintype.card ι / 2) •
      inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · haveI : Subsingleton V := e.injective.subsingleton
    have h1 : imgLat (δ : V →ₗ[ℂ] V) Λ = Λ := by
      ext x
      rw [Subsingleton.elim x 0]
      exact ⟨fun _ => Λ.zero_mem, fun _ => AddSubgroup.zero_mem _⟩
    rw [h1, Formalism.L2.Ker.inter_self H hU.herm Λ α hU.semi hθ.2, Fintype.card_eq_zero, Nat.zero_div, pow_zero, one_smul]
    funext z
    show θ (δ.symm z) = θ z
    rw [Subsingleton.elim (δ.symm z) z]
  · obtain ⟨S₁, hS₁⟩ := (repsExist V₁ _ _ (c.idx i₀ (UC.latA_idx_ne hLat hU))).1
    have hc := unitaryConstant V H Λ α δ Ae hLat hU hLine (prodReps e S₁) (c.reps hS₁) θ hθ
    rw [hc]
    congr 1
    obtain ⟨k, hk⟩ := hn
    have hk2 : Fintype.card ι / 2 = k := by omega
    have hk' : Fintype.card ι = 2 * k := by omega
    have ha : LinearMap.det (Ae₁ : V₁ →ₗ[ℂ] V₁) ≠ 0 := (LinearEquiv.isUnit_det' Ae₁).ne_zero
    have hd := detCayley V₁ H₁ hH₁ hP₁ δ₁ Ae₁ hI₁ hA₁
    rw [hr.neg_one_pow, one_mul] at hd
    rw [c.gauss hS₁.1, det_copies e (Ae : V →ₗ[ℂ] V) (Ae₁ : V₁ →ₗ[ℂ] V₁) c.cay, hk2, hk', pow_mul (gaussC _ _ _ _),
      hG S₁ hS₁, one_pow, mul_one, norm_pow, Complex.ofReal_pow, ← div_pow, pow_mul, unit_sq _ ha, hd,
      mul_div_assoc, div_self ha, mul_one]

end Formalism.L2.PairingIndexBounds.Eq.J
