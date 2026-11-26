module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd
namespace Formalism.MainNotions.Pf14

open Module

theorem smith_mem {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsLocalRing O]
    {I : Type*} [Fintype I] (S : Submodule O (I → O)) (a : O)
    (h : ∀ φ : I → O, (∃ i, IsUnit (φ i)) → ∃ s ∈ S, (∑ i, φ i * s i) ∣ a) (x : I → O) : a • x ∈ S := by
  classical
  obtain ⟨n, snf⟩ := S.smithNormalForm (Pi.basisFun O I)
  have key : ∀ j, a • snf.bM j ∈ S := by
    intro j
    set φ : I → O := fun i => snf.bM.coord j (Pi.single i 1) with hφdef
    have hφ : ∀ y : I → O, ∑ i, φ i * y i = snf.bM.coord j y := by
      intro y
      conv_rhs => rw [show y = ∑ i, y i • Pi.single i (1 : O) by
        ext k; simp [Finset.sum_apply, Pi.single_apply]]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, hφdef, mul_comm]
    have hprim : ∃ i, IsUnit (φ i) := by
      by_contra hne
      push_neg at hne
      have h1 : snf.bM.coord j (snf.bM j) = 1 := by simp
      rw [← hφ] at h1
      have hmem : ∑ i, φ i * snf.bM j i ∈ IsLocalRing.maximalIdeal O :=
        Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      rw [h1] at hmem
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
    obtain ⟨s, hs, hsd⟩ := h φ hprim
    rw [hφ] at hsd
    have hs' : s = ∑ k, snf.bN.repr ⟨s, hs⟩ k • snf.a k • snf.bM (snf.f k) := by
      have := congrArg Subtype.val (snf.bN.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, snf.snf] at this
      exact this.symm
    have hc : snf.bM.coord j s =
        ∑ k, snf.bN.repr ⟨s, hs⟩ k * snf.a k * (if snf.f k = j then 1 else 0) := by
      conv_lhs => rw [hs']
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_smul, Finsupp.single_apply, mul_assoc]
    by_cases hj : ∃ k, snf.f k = j
    · obtain ⟨k0, rfl⟩ := hj
      have hc0 : snf.bM.coord (snf.f k0) s = snf.bN.repr ⟨s, hs⟩ k0 * snf.a k0 := by
        rw [hc, Finset.sum_eq_single k0]
        · simp
        · intro k _ hk
          simp [snf.f.injective.ne hk]
        · simp
      rw [hc0] at hsd
      obtain ⟨t, ht⟩ := (Dvd.intro_left _ rfl : snf.a k0 ∣ snf.bN.repr ⟨s, hs⟩ k0 * snf.a k0).trans hsd
      rw [ht, mul_comm, mul_smul, ← snf.snf k0]
      exact S.smul_mem t (snf.bN k0).2
    · push_neg at hj
      have hc0 : snf.bM.coord j s = 0 := by
        rw [hc]
        exact Finset.sum_eq_zero fun k _ => by simp [hj k]
      rw [hc0, zero_dvd_iff] at hsd
      simp [hsd]
  rw [← snf.bM.sum_repr x, Finset.smul_sum]
  refine S.sum_mem fun j _ => ?_
  rw [smul_comm]
  exact S.smul_mem _ (key j)

theorem dvd_of_add {O : Type*} [CommRing O] [IsLocalRing O] (π : O) (hπ : ¬ IsUnit π) (D : ℕ) (a z : O)
    (ha : a ∣ π ^ D) : (a + π ^ (D + 1) * z) ∣ π ^ D := by
  obtain ⟨c, hc⟩ := ha
  have hu : IsUnit (1 + π * c * z) := by
    by_contra h1
    have hm : π * c * z ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hπ))
    have h2 : 1 + π * c * z ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h1
    have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      simpa using Ideal.sub_mem _ h2 hm
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hx : a + π ^ (D + 1) * z = a * (1 + π * c * z) := by
    rw [pow_succ, hc]; ring
  rw [hx, hu.mul_right_dvd]
  exact ⟨c, hc⟩

end Formalism.MainNotions.Pf14
end

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Ring

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem p_nonunit (hS : HidaSetting p n' W Qq O Kf ι σ j w) : ¬ IsUnit (p : O) := by
  intro hu
  let _ : Algebra W O := j.toAlgebra
  have _ : Module.Finite W O := hS.finite
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := W) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal O)
  have heq : (IsLocalRing.maximalIdeal O).comap (algebraMap W O) = IsLocalRing.maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal hmax
  have hpW : (p : W) ∈ IsLocalRing.maximalIdeal W := hS.p_unif.not_isUnit
  rw [← heq, Ideal.mem_comap, map_natCast] at hpW
  exact hpW hu

end Ring

theorem goodRank_of_prim {O Kf X : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup X] [Module O X]
    (hinj : Function.Injective (algebraMap O Kf)) (π : O) (A : Submodule O X) {M : ℕ} (φ : Fin M → X → Kf) (D : ℕ)
    (hadd : ∀ i G G', φ i (G + G') = φ i G + φ i G')
    (hsmul : ∀ i (c : O) G, φ i (c • G) = algebraMap O Kf c * φ i G)
    (hint : ∀ i, ∀ G ∈ A, φ i G ∈ Set.range (algebraMap O Kf))
    (hprim : ∀ c : Fin M → O, (∃ i, IsUnit (c i)) →
      ∃ G ∈ A, ValLe π D (∑ i, algebraMap O Kf (c i) * φ i G)) :
    GoodRankK π A φ M D := by
  classical
  have h0 : ∀ i, φ i 0 = 0 := fun i => by
    have h := hadd i 0 0
    rw [add_zero] at h
    linear_combination -h
  let S : Submodule O (Fin M → O) :=
    { carrier := {v | ∃ G ∈ A, ∀ i, algebraMap O Kf (v i) = φ i G}
      add_mem' := by
        rintro v v' ⟨G, hG, hv⟩ ⟨G', hG', hv'⟩
        exact ⟨G + G', A.add_mem hG hG', fun i => by rw [Pi.add_apply, map_add (f := _), hv, hv', hadd]⟩
      zero_mem' := ⟨0, A.zero_mem, fun i => by rw [Pi.zero_apply, map_zero, h0]⟩
      smul_mem' := by
        rintro c v ⟨G, hG, hv⟩
        exact ⟨c • G, A.smul_mem c hG, fun i => by rw [Pi.smul_apply, smul_eq_mul, map_mul, hv, hsmul]⟩ }
  have hS : ∀ c : Fin M → O, (∃ i, IsUnit (c i)) → ∃ s ∈ S, (∑ i, c i * s i) ∣ π ^ D := by
    intro c hc
    obtain ⟨G, hG, a, b, hab, hb⟩ := hprim c hc
    choose v hv using fun i => hint i G hG
    refine ⟨v, ⟨G, hG, hv⟩, ?_⟩
    have hsum : ∑ i, c i * v i = a := hinj (by rw [← hab, map_sum]; simp only [map_mul, hv])
    exact ⟨b, by rw [hsum, hb]⟩
  have hmem : ∀ k : Fin M, π ^ D • Pi.single k (1 : O) ∈ S := fun k => smith_mem S (π ^ D) hS _
  choose G hGA hG using hmem
  have hsumφ : ∀ i (s : Finset (Fin M)) (f : Fin M → X), φ i (∑ k ∈ s, f k) = ∑ k ∈ s, φ i (f k) :=
    fun i s f => map_sum (AddMonoidHom.mk' (φ i) (hadd i)) f s
  let u : (Fin M → O) →ₗ[O] A :=
    { toFun := fun x => ∑ k, x k • (⟨G k, hGA k⟩ : A)
      map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have key : ∀ x i, φ i (u x : X) = algebraMap O Kf (π ^ D * x i) := by
    intro x i
    have hu : (u x : X) = ∑ k, x k • G k := by simp [u]
    rw [hu, hsumφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hsmul, ← hG, ← map_mul, ← map_sum]
    congr 1
    simp [Pi.single_apply, mul_comm]
  refine ⟨u, 1, fun x k => ?_⟩
  simp [key, Matrix.one_apply]

section Be

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

theorem be_add_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0)
    (G G' : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (G + G') = be p r lam0 F G + be p r lam0 F G' := by
  simp only [be, LinearMap.add_apply]

theorem be_smul_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) (c : O)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (c • G) = algebraMap O Kf c * be p r lam0 F G := by
  simp only [be, LinearMap.smul_apply, Algebra.smul_def]

theorem be_smulK_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) (c : Kf)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (c • G) = c * be p r lam0 F G := by
  simp only [be, LinearMap.smul_apply, smul_eq_mul]

theorem be_sum_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) {n : ℕ} (c : Fin n → O) (F : Fin n → Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) :
    be p r lam0 (∑ i, c i • F i) G = ∑ i, algebraMap O Kf (c i) * be p r lam0 (F i) G := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [be, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul Kf (c i) (F i), smul_smul, mul_comm, ← smul_smul, map_smul, smul_eq_mul]

end Be

theorem s7 : S7 := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS hBP m r lam0 t D κ cStar L hdom hc hsrc
  classical
  have _ := hS.frac_O
  obtain ⟨E, nE, F, hE, hFsrc, hFoth, hprim, hcard⟩ := hsrc
  have hRe : ∀ e ∈ E, ∀ i, F e i ∈ Re p ι σ w r lam0 e := by
    intro e he i
    have h := (Submodule.mem_inf.mp (hFsrc e he i)).2
    rw [Submodule.mem_iInf] at h
    exact (Submodule.mem_iInf _).mp (h e) ⟨(hE e he).1, rfl⟩
  let T := Σ e : E, Fin (nE e.1)
  let eqv : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, fun k => (eqv k).1.1, fun k => F (eqv k).1.1 (eqv k).2,
    fun k => hE _ (eqv k).1.2, fun k => hFsrc _ (eqv k).1.2 _,
    fun k e' he' hs' hne => hFoth _ (eqv k).1.2 _ e' he' hs' hne, Fintype.card T, ?_, ?_⟩
  · have hT : Fintype.card T = ∑ e ∈ E, nE e := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort E nE
    rw [hT]
    exact hcard
  refine goodRank_of_prim (IsFractionRing.injective O Kf) (p : O) _ _ D
    (fun k G G' => be_add_right p r lam0 _ G G') (fun k c G => be_smul_right p r lam0 _ c G) ?_ ?_
  · intro k G hG
    have he := hE _ (eqv k).1.2
    have hG' : G ∈ Re' p ι σ w r lam0 (eqv k).1.1 := by
      have h := (Submodule.mem_inf.mp hG).2
      rw [Submodule.mem_iInf] at h
      exact (Submodule.mem_iInf _).mp (h _) he
    exact ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom _ he.1).1 G).mp hG' _ (hRe _ (eqv k).1.2 _)
  · rintro c ⟨k0, hk0⟩
    obtain ⟨⟨e0, i0⟩, hx⟩ : ∃ x, eqv k0 = x := ⟨_, rfl⟩
    have hk0' : IsUnit (c (eqv.symm ⟨e0, i0⟩)) := by
      rw [← hx, Equiv.symm_apply_apply]
      exact hk0
    obtain ⟨G, hGN, hval, hGoth⟩ := hprim e0.1 e0.2 (fun i => c (eqv.symm ⟨e0, i⟩)) ⟨i0, hk0'⟩
    obtain ⟨a, b, hva, hab⟩ := hval
    refine ⟨G, hGN, ?_⟩
    have hterm : ∀ e : E, ∀ i : Fin (nE e.1), e ≠ e0 →
        ∃ z : O, be p r lam0 (F e.1 i) G = algebraMap O Kf ((p : O) ^ (D + 1) * z) := by
      intro e i hne
      have he := hE e.1 e.2
      obtain ⟨G₀, hG₀, hGeq⟩ := Submodule.mem_map.mp (hGoth e.1 e.2 (fun h => hne (Subtype.ext h)))
      obtain ⟨y, hy⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom _ he.1).1 G₀).mp hG₀ _ (hRe _ e.2 i)
      refine ⟨w ^ (cStar - 2 * (D + 1)) * y, ?_⟩
      rw [← hGeq, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, be_smulK_right, ← hy, zpow_natCast,
        ← map_pow, ← map_mul, ← hS.w_sq, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 3
      omega
    have hsplit : ∑ k, algebraMap O Kf (c k) * be p r lam0 (F (eqv k).1.1 (eqv k).2) G =
        be p r lam0 (∑ i, c (eqv.symm ⟨e0, i⟩) • F e0.1 i) G +
          ∑ e ∈ Finset.univ.erase e0, ∑ i, algebraMap O Kf (c (eqv.symm ⟨e, i⟩)) * be p r lam0 (F e.1 i) G := by
      have h1 : ∑ k, algebraMap O Kf (c k) * be p r lam0 (F (eqv k).1.1 (eqv k).2) G =
          ∑ x : T, algebraMap O Kf (c (eqv.symm x)) * be p r lam0 (F x.1.1 x.2) G :=
        Fintype.sum_equiv eqv _ _ (fun k => by rw [Equiv.symm_apply_apply])
      rw [h1, Fintype.sum_sigma, be_sum_left, ← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
    have hrest : ∃ z : O, (∑ e ∈ Finset.univ.erase e0, ∑ i,
        algebraMap O Kf (c (eqv.symm ⟨e, i⟩)) * be p r lam0 (F e.1 i) G) = algebraMap O Kf ((p : O) ^ (D + 1) * z) := by
      refine Finset.sum_induction _ (fun x => ∃ z : O, x = algebraMap O Kf ((p : O) ^ (D + 1) * z))
        (fun x y ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => ⟨z₁ + z₂, by rw [h₁, h₂, mul_add, map_add (f := _)]⟩) ⟨0, by simp⟩ ?_
      intro e he
      refine Finset.sum_induction _ (fun x => ∃ z : O, x = algebraMap O Kf ((p : O) ^ (D + 1) * z))
        (fun x y ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => ⟨z₁ + z₂, by rw [h₁, h₂, mul_add, map_add (f := _)]⟩) ⟨0, by simp⟩ ?_
      intro i _
      obtain ⟨z, hz⟩ := hterm e i (Finset.ne_of_mem_erase he)
      exact ⟨c (eqv.symm ⟨e, i⟩) * z, by rw [hz, ← map_mul]; congr 1; ring⟩
    obtain ⟨z, hz⟩ := hrest
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D a z ⟨b, hab.symm⟩
    exact ⟨a + (p : O) ^ (D + 1) * z, b', by rw [hsplit, hva, hz, map_add (f := _)], hb'.symm⟩

end Formalism.MainNotions.Pf14
