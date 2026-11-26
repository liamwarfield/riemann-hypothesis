module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFCnt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS
noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add (f := _), ← hs.herm, ← hs.herm]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]
  ring

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by
  exact LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') := by
  refine ⟨⟨fun x y z => hs.add_right x y z, fun c x y => hs.smul_right c x y,
    fun x y => hs.herm x y⟩, ?_⟩
  · intro w hw
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : LinearMap.range (hs.lin e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / h e e) • e, ?_⟩
    rw [IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]
  have e1 := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [hsurj, finrank_top, Module.finrank_self] at e1
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 := congrArg (hs.lin (f i)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at e1
  simp only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1
  rw [Finset.sum_eq_single i] at e1
  · exact (mul_eq_zero.1 e1).resolve_right (h2 i)
  · intro j _ hji
    rw [h1 i j (Ne.symm hji), mul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  have hwe : h w e = 0 := by rw [hs.herm e w, hw, map_zero]
  rw [hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right,
    hs.smul_right, hw, hwe]
  ring

end basic

end PI.VolStabSW.FFHS
end
end

noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right, mul_right_comm, inv_mul_cancel₀ he, one_mul, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  classical
  let T : V → K := fun x => (h e e)⁻¹ * h e x
  have hTe : ∀ (t : K) (w : perp hs e), T ((t • e) + (w : V)) = t := by
    intro t w
    simp only [T]
    rw [hs.add_right, hs.smul_right, (mem_perp hs e w).1 w.2, add_zero, ← mul_assoc,
      mul_comm ((h e e)⁻¹) t, mul_assoc, inv_mul_cancel₀ he, mul_one]
  let eqv : {x : V // h x x = c} ≃ Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨T x.1, ⟨⟨x.1 - T x.1 • e, perp_sub_mem hs e x.1 he⟩, by
        have h1 := decomp_val hs e (x.1 - T x.1 • e)
          ((mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)) (T x.1)
        have hx : T x.1 • e + (x.1 - T x.1 • e) = x.1 := by abel
        rw [hx, x.2] at h1
        show h (x.1 - T x.1 • e) (x.1 - T x.1 • e) = c - σ (T x.1) * T x.1 * h e e
        rw [eq_sub_iff_add_eq, add_comm]
        exact h1.symm⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
        rw [decomp_val hs e p.2.1 ((mem_perp hs e _).1 p.2.1.2) p.1]
        have h2 : h (p.2.1 : V) (p.2.1 : V) = c - σ p.1 * p.1 * h e e := p.2.2
        rw [h2]
        ring⟩
      left_inv := fun x => Subtype.ext (by
        show T x.1 • e + (x.1 - T x.1 • e) = x.1
        abel)
      right_inv := fun p => by
        refine Sigma.subtype_ext (hTe p.1 p.2.1) (Subtype.ext ?_)
        show p.1 • e + (p.2.1 : V) - T (p.1 • e + (p.2.1 : V)) • e = (p.2.1 : V)
        rw [hTe]
        abel }
  rw [Nat.card_congr eqv, Nat.card_sigma]

end PI.VolStabSW.FFHS
end
end

noncomputable section

namespace PI.VolStabSW.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y z
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · intro c x y
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  · intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  · intro x hx
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

end matrix

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

private theorem card_le_natDegree_of_eval_eq_zero {L : Type} [Field L] (P : L[X]) (hP : P ≠ 0)
    (Z : Finset L) (hZ : ∀ z ∈ Z, P.eval z = 0) : Z.card ≤ P.natDegree := by
  have hsub : Z.val ⊆ P.roots := fun z hz =>
    (Polynomial.mem_roots hP).mpr (hZ z (Finset.mem_val.mp hz))
  exact (Multiset.card_le_card ((Multiset.le_iff_subset Z.nodup).mpr hsub)).trans
    (Polynomial.card_roots' P)

private theorem card_le_of_pow_eq_mul_add {L : Type} [Field L] (n : ℕ) (hn : 1 < n) (b c : L)
    (Z : Finset L) (hZ : ∀ z ∈ Z, z ^ n = b * z + c) : Z.card ≤ n := by
  have hlt : (C b * X + C c : L[X]).natDegree < (X ^ n : L[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt Polynomial.natDegree_linear_le hn
  have hdeg : (X ^ n - (C b * X + C c) : L[X]).natDegree = n := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hP0 : (X ^ n - (C b * X + C c) : L[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have := card_le_natDegree_of_eval_eq_zero _ hP0 Z fun z hz => by simp [hZ z hz]
  rwa [hdeg] at this

private theorem exists_algebraMap_eq_of_frobenius_fixed (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  by_contra hne
  push_neg at hne
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hdS : d ∉ Finset.univ.image (algebraMap k K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hc := card_le_of_pow_eq_mul_add (Fintype.card k) hq 1 0
    (Finset.cons d (Finset.univ.image (algebraMap k K)) hdS) (by
      intro z hz
      rw [Finset.mem_cons] at hz
      rcases hz with h | hz
      · rw [h, hd, one_mul, add_zero]
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
        rw [← map_pow, FiniteField.pow_card, one_mul, add_zero])
  rw [Finset.card_cons, Finset.card_image_of_injective _ (algebraMap k K).injective,
    Finset.card_univ] at hc
  omega

theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  intro x
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  by_cases hx : ∃ a : k, algebraMap k K a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [AlgEquiv.commutes, ← map_pow, FiniteField.pow_card]
  push_neg at hx
  have hq : x ^ Fintype.card k ≠ x := fun h => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_frobenius_fixed x h
    exact hx a ha
  have hσx : σ x ≠ x := by
    intro hfix
    apply hne
    have hli : LinearIndependent k ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        exact ⟨by simpa using hst, rfl⟩
      · exfalso
        have htK : algebraMap k K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        apply hx (-s * t⁻¹)
        rw [map_mul, map_neg, map_inv₀, eq_comm, eq_mul_inv_iff_mul_eq₀ htK]
        linear_combination hst
    have hlin : σ.toLinearMap = LinearMap.id :=
      (basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])).ext fun i => by
        fin_cases i <;> simp [coe_basisOfLinearIndependentOfCardEqFinrank, hfix]
    ext y
    simpa using LinearMap.congr_fun hlin y
  have hint_r : IsIntegral k x := IsIntegral.of_finite k x
  have hP0 : (minpoly k x).map (algebraMap k K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint_r)
  have hroot : ∀ y, Polynomial.aeval y (minpoly k x) = 0 →
      ((minpoly k x).map (algebraMap k K)).eval y = 0 := fun y hy => by
    rw [Polynomial.eval_map_algebraMap]
    exact hy
  have r1 := hroot x (minpoly.aeval k x)
  have r2 := hroot (σ x) (by
    rw [show σ x = (σ : K →ₐ[k] K) x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero])
  have r3 := hroot (x ^ Fintype.card k) (by
    rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval,
      zero_pow Fintype.card_ne_zero])
  by_contra hne3
  have hcard : ({x, σ x, x ^ Fintype.card k} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, σ x, x ^ Fintype.card k, hσx.symm, hq.symm, hne3, rfl⟩
  have hle := card_le_natDegree_of_eval_eq_zero _ hP0 {x, σ x, x ^ Fintype.card k} (by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h <;> rw [h] <;> assumption)
  rw [hcard, Polynomial.natDegree_map] at hle
  have hdeg : (minpoly k x).natDegree ≤ finrank k K := minpoly.natDegree_le x
  omega

theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hKcard' : Fintype.card K = Fintype.card k ^ finrank k K := Module.card_eq_pow_finrank
  have hKcard : Fintype.card K = Fintype.card k ^ 2 := by rw [hKcard', h2]
  have hσσ : ∀ t, σ (σ t) = t := by
    intro t
    rw [hfrob (σ t), hfrob t, ← pow_mul, ← sq, ← hKcard, FiniteField.pow_card]
  let c : K → ℕ := fun y => (Finset.univ.filter fun t : K => t * σ t = y).card
  let F : Finset K := Finset.univ.filter fun y : K => y ^ Fintype.card k = y
  have hsum : Fintype.card K = ∑ y ∈ F, c y := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := fun t => t * σ t) fun t _ => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, map_mul, hσσ, mul_comm]
  have hF : F.card ≤ Fintype.card k :=
    card_le_of_pow_eq_mul_add _ hq1 1 0 F fun z hz => by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [hz, one_mul, add_zero]
  have hfib : ∀ y, c y ≤ Fintype.card k + 1 := fun y =>
    card_le_of_pow_eq_mul_add _ (by omega) 0 y (Finset.univ.filter fun t : K => t * σ t = y)
      fun t ht => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [pow_succ', ← hfrob, ht, zero_mul, zero_add]
  have hc0 : c 0 = 1 := by
    show (Finset.univ.filter fun t : K => t * σ t = 0).card = 1
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext t
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  split_ifs with hd0
  · subst hd0
    exact hc0
  · have hdF : d ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, hd]
    have h0F : (0 : K) ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact zero_pow (by omega)
    refine le_antisymm (hfib d) ?_
    by_contra hlt
    push_neg at hlt
    have key : ∑ y ∈ F.erase 0, c y < ∑ _y ∈ F.erase 0, (Fintype.card k + 1) :=
      Finset.sum_lt_sum (fun y _ => hfib y) ⟨d, Finset.mem_erase.mpr ⟨hd0, hdF⟩, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0F] at key
    have hs := Finset.add_sum_erase F c h0F
    rw [hc0] at hs
    have hn : 1 ≤ F.card := Finset.card_pos.mpr ⟨0, h0F⟩
    have h3 : (F.card - 1) * (Fintype.card k + 1) ≤
        (Fintype.card k - 1) * (Fintype.card k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (Fintype.card k - 1) * (Fintype.card k + 1) + 1 = Fintype.card k ^ 2 := by
      obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      ring
    omega

end field

end PI.VolStabSW.FFHS
