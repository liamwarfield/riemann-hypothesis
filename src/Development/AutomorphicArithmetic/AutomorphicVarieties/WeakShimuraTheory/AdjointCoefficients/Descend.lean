module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Descend
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen {Γ Γb M R κ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group Γb]
    [TopologicalSpace Γb] [Monoid M] [CommRing R] (I : Ideal R) [IsHausdorff I R] (N : Set Γ) (π : Γ →* Γb)
    (hq : Topology.IsQuotientMap π) (hk : π.ker = (Subgroup.normalClosure N).topologicalClosure)
    (e : κ → M → R) (he : ∀ x y, (∀ k, e k x = e k y) → x = y) (r : Γ →* M) (hN : ∀ g ∈ N, r g = 1)
    (hc : ∀ k, AdicCont I fun g => e k (r g)) :
    ∃ rb : Γb →* M, rb.comp π = r ∧ ∀ k, AdicCont I fun g => e k (rb g) := by
  have hcl : IsClosed (r.ker : Set Γ) := by
    have : (r.ker : Set Γ) = ⋂ k, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (I ^ n) (e k (r g)) = Ideal.Quotient.mk (I ^ n) (e k 1)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h k n => by rw [h], fun h => he _ _ fun k => ?_⟩
      rw [← sub_eq_zero]
      refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
      exact h k n
    rw [this]
    exact isClosed_iInter fun k => isClosed_iInter fun n => (hc k n).isClosed_fiber _
  have hle : π.ker ≤ r.ker := by
    rw [hk]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => hN g hg) hcl
  have hle' : π.ker ≤ r.toHomUnits.ker := fun g hg => Units.ext (hle hg)
  have hs := hq.surjective
  let φ := π.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩
  have hφ : ∀ g, ((Units.coeHom M).comp φ) (π g) = r g := fun g =>
    congrArg Units.val (π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩ g)
  refine ⟨(Units.coeHom M).comp φ, MonoidHom.ext hφ, fun k n s => ?_⟩
  rw [← hq.isOpen_preimage]
  have := hc k n s
  simp only [← hφ] at this
  exact this

theorem UpperTheory.V.Ws.X1.descend :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (Φ : Fr O Γ) , ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R], (∀ (r : Γ →* M4 R), (∀ g ∈ Φ.N, r g = 1) → (∀ i j, AdicCont I fun g => r g i j) → ∃ rb : Γb →* M4 R, rb.comp π = r ∧ ∀ i j, AdicCont I fun g => rb g i j) ∧ ∀ (ν : Γ →* Rˣ), (∀ g ∈ Φ.N, ν g = 1) → AdicCont I (fun g => (ν g : R)) → ∃ νb : Γb →* Rˣ, νb.comp π = ν ∧ AdicCont I fun g => (νb g : R) := by
  intro O Γ _ _ _ _ _ Φ Γb _ _ _ _ π hπ R _ I _
  have hq : Topology.IsQuotientMap π := hπ.cont.isClosedMap.isQuotientMap hπ.cont hπ.onto
  refine ⟨fun r hN hc => ?_, fun ν hN hc => ?_⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (k : Fin 4 × Fin 4) (x : M4 R) => x k.1 k.2)
      (fun x y h => Matrix.ext fun i j => h (i, j)) r hN fun k => hc k.1 k.2
    exact ⟨rb, h1, fun i j => h2 (i, j)⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (_ : Unit) (x : Rˣ) => (x : R))
      (fun x y h => Units.ext (h ())) ν hN fun _ => hc
    exact ⟨rb, h1, h2 ()⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AdFacts
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [CommRing k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) : IsUp (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]

theorem UpperTheory.V.Ws.X1.adFacts :
    ∀ {k Γ : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), ((∀ i j, IsLocallyConstant fun g => r g i j) → IsOpen ((adSp r h).ker : Set Γ) ∧ ∀ X, IsLocallyConstant fun g => adSp r h g X) ∧ ∀ (n : M4 k) (s : Γ), IsGSp 1 n → IsUp (adj n * r s * n) → IsUp (adj n * r s⁻¹ * n) → ∀ X ∈ bor n, adSp r h s X ∈ bor n := by
  intro k Γ _ _ _ _ r h
  refine ⟨fun hloc => ?_, fun n s hn h1 h2 X hX => ?_⟩
  · have hr : IsLocallyConstant fun g => r g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro M
      have hset : (fun g => r g) ⁻¹' {M} = ⋂ i, ⋂ j, (fun g => r g i j) ⁻¹' {M i j} := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
        exact ⟨fun e i j => by rw [e], fun e => Matrix.ext e⟩
      rw [hset]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hloc i j).isOpen_fiber _
    refine ⟨?_, fun X => ?_⟩
    · have hker : IsOpen ((r.ker : Subgroup Γ) : Set Γ) := by
        have : ((r.ker : Subgroup Γ) : Set Γ) = (fun g => r g) ⁻¹' {1} := by
          ext g
          simp [MonoidHom.mem_ker]
        rw [this]
        exact hr.isOpen_fiber _
      refine Subgroup.isOpen_mono ?_ hker
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      apply LinearMap.ext
      intro Y
      apply Subtype.ext
      have hgi : r g⁻¹ = 1 := by
        have e := r.map_mul g⁻¹ g
        rw [inv_mul_cancel, r.map_one, hg, mul_one] at e
        exact e.symm
      rw [adSp_val, hg, hgi]
      simp
    · have hinv : IsLocallyConstant fun g => r g⁻¹ := hr.comp_continuous continuous_inv
      have hprod : IsLocallyConstant fun g => r g * (X : M4 k) * r g⁻¹ :=
        IsLocallyConstant.comp₂ (IsLocallyConstant.comp₂ hr (IsLocallyConstant.const (X : M4 k)) (· * ·)) hinv (· * ·)
      refine IsLocallyConstant.desc _ (fun Y : sp4 k => (Y : M4 k)) ?_ Subtype.val_injective
      convert hprod using 1
      funext g
      simp [adSp_val]
  · have hn' : n * adj n = 1 := by
      have e : adj n * n = 1 := by simpa [IsGSp] using hn
      exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.mp e
    show IsUp (adj n * ((adSp r h s X : sp4 k) : M4 k) * n)
    rw [adSp_val]
    have key : adj n * (r s * (X : M4 k) * r s⁻¹) * n
        = (adj n * r s * n) * (adj n * (X : M4 k) * n) * (adj n * r s⁻¹ * n) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul, ← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul]
    rw [key]
    exact up_mul (up_mul h1 hX) h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContLift
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ (maximalIdeal R ^ (k + 1) • ⊤ ⊓ (I : Submodule R R)) :=
    ⟨by simpa [smul_eq_mul] using hxm, hxI⟩
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hmem : x ∈ maximalIdeal R • (I : Submodule R R) := Submodule.smul_mono le_rfl inf_le_right hx
  rw [smul_eq_mul, h] at hmem
  simpa using hmem

theorem UpperTheory.V.Ws.X1.contLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → (∀ (S : Type) [TopologicalSpace S] (x : S → R), AdicCont (maximalIdeal R) x → ∃ y : S → A, AdicCont (maximalIdeal A) y ∧ ∀ s, p (y s) = x s) ∧ ∀ (S : Type) [TopologicalSpace S] (y : S → A), AdicCont (maximalIdeal A) y → (∀ s, p (y s) = 0) → IsLocallyConstant y := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p hp hK
  haveI : IsNoetherianRing A := IsCO.toIsNoetherian Λ
  obtain ⟨N0, hN0⟩ := inf_pow_bot A (RingHom.ker p) hK
  have hm : ∀ a : A, a ∈ maximalIdeal A ↔ p a ∈ maximalIdeal R := by
    intro a
    rw [← res_eq_zero_iff Λ A, ← res_eq_zero_iff Λ R, res_map]
  have hmap1 : Ideal.map p (maximalIdeal A) = maximalIdeal R := by
    ext r
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hm a).mp ha
    · intro hr
      obtain ⟨a, rfl⟩ := hp r
      exact ⟨a, (hm a).mpr hr, rfl⟩
  have hmap : ∀ n, ∀ r ∈ maximalIdeal R ^ n, ∃ z ∈ maximalIdeal A ^ n, p z = r := by
    intro n r hr
    rw [← hmap1, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective p hp] at hr
    exact hr
  choose ρ hρ using fun c : R ⧸ maximalIdeal R ^ N0 => Ideal.Quotient.mk_surjective c
  choose l hl using fun c : R ⧸ maximalIdeal R ^ N0 => hp (ρ c)
  have hu : ∀ r : R, ∃ z ∈ maximalIdeal A ^ N0, p z = r - ρ (Ideal.Quotient.mk _ r) := by
    intro r
    apply hmap
    rw [← Ideal.Quotient.eq, hρ]
  choose u hu1 hu2 using hu
  let σ : R → A := fun r => l (Ideal.Quotient.mk _ r) + u r
  have hpσ : ∀ r, p (σ r) = r := by
    intro r
    simp only [σ, map_add (f := _), hl, hu2]
    ring
  have hL : ∀ M, N0 ≤ M → ∀ r r' : R, r - r' ∈ maximalIdeal R ^ M → σ r - σ r' ∈ maximalIdeal A ^ M := by
    intro M hM r r' h
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N0) r) = Ideal.Quotient.mk _ r' :=
      Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right hM h)
    obtain ⟨z, hz, hpz⟩ := hmap M _ h
    have hzero : z - (u r - u r') = 0 := by
      apply hN0
      · rw [RingHom.mem_ker]
        simp only [map_sub]
        rw [hpz, hu2, hu2, hq]
        ring
      · exact sub_mem (Ideal.pow_le_pow_right hM hz) (sub_mem (hu1 r) (hu1 r'))
    have hz' : u r - u r' = z := (sub_eq_zero.mp hzero).symm
    simp only [σ]
    rw [hq, add_sub_add_left_eq_sub, hz']
    exact hz
  refine ⟨?_, ?_⟩
  · intro S _ x hx
    refine ⟨fun s => σ (x s), ?_, fun s => hpσ _⟩
    intro n
    have hc := hx (max n N0)
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 := hL (max n N0) (le_max_right _ _) _ _ h1
    exact Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right (le_max_left _ _) h2)
  · intro S _ y hy h0
    have hc := hy N0
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 : y s' - y s = 0 := by
      apply hN0 _ _ h1
      rw [RingHom.mem_ker, map_sub, h0, h0, sub_zero]
    exact sub_eq_zero.mp h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.SpDims
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {k : Type} [Field k]

private theorem ent (X : sp4 k) (i j : Fin 4) : (sgn i * sgn j) • X.1 j.rev i.rev = -X.1 i j := by
  have h : adj X.1 = -X.1 := X.2
  have h' := congrFun (congrFun h i) j
  rwa [adj_apply, Matrix.neg_apply] at h'

private theorem conj_mem (n : M4 k) (X : sp4 k) : adj n * X.1 * n ∈ sp4 k := by
  show adj (adj n * X.1 * n) = -(adj n * X.1 * n)
  rw [(grp k).1, (grp k).1, (grp k).2.1, show adj X.1 = -X.1 from X.2]
  noncomm_ring

private noncomputable def cj (n : M4 k) : sp4 k →ₗ[k] sp4 k where
  toFun X := ⟨adj n * X.1 * n, conj_mem n X⟩
  map_add' X Y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c X := Subtype.ext (by simp)

private noncomputable def cjE (n : M4 k) (hn : IsGSp 1 n) : sp4 k ≃ₗ[k] sp4 k :=
  LinearEquiv.ofLinear (cj n) (cj (adj n))
    (LinearMap.ext fun X => Subtype.ext (by
      have h : adj n * n = 1 := by simpa [IsGSp] using hn
      show adj n * (adj (adj n) * X.1 * adj n) * n = X.1
      rw [(grp k).2.1, mul_assoc n, ← mul_assoc (adj n), h, one_mul, mul_assoc, h, mul_one]))
    (LinearMap.ext fun X => Subtype.ext (by
      have h : adj n * n = 1 := by simpa [IsGSp] using hn
      have h' : n * adj n = 1 := mul_eq_one_comm.mp h
      show adj (adj n) * (adj n * X.1 * n) * adj n = X.1
      rw [(grp k).2.1, mul_assoc (adj n), ← mul_assoc n, h', one_mul, mul_assoc, h', mul_one]))

private theorem cj_one (X : M4 k) : adj 1 * X * 1 = X := by
  rw [(grp k).2.2.2.2.1, one_mul, mul_one]

private theorem mem_borel_identity_iff_upper (X : sp4 k) : X ∈ bor (1 : M4 k) ↔ IsUp X.1 := by
  show IsUp (adj 1 * X.1 * 1) ↔ _
  rw [cj_one]

private theorem mem_nilradical_identity_iff (X : sp4 k) : X ∈ nil (1 : M4 k) ↔ ∀ i j, i ≤ j → X.1 i j = 0 := by
  show (∀ i j, i ≤ j → (adj 1 * X.1 * 1 : M4 k) i j = 0) ↔ _
  rw [cj_one]

private theorem bor_eq (n : M4 k) (hn : IsGSp 1 n) : bor n = (bor 1).comap (cjE n hn : sp4 k →ₗ[k] sp4 k) := by
  ext X
  rw [Submodule.mem_comap, mem_borel_identity_iff_upper]
  rfl

private theorem nil_eq (n : M4 k) (hn : IsGSp 1 n) : nil n = (nil 1).comap (cjE n hn : sp4 k →ₗ[k] sp4 k) := by
  ext X
  rw [Submodule.mem_comap, mem_nilradical_identity_iff]
  rfl

private theorem compl1 : IsCompl (bor (1 : M4 k)) (nil 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X h1 h2
    rw [mem_borel_identity_iff_upper] at h1
    rw [mem_nilradical_identity_iff] at h2
    apply Subtype.ext
    ext i j
    rcases lt_or_ge j i with h | h
    · exact h1 i j h
    · exact h2 i j h
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    let L : M4 k := Matrix.of fun i j => if j < i then X.1 i j else 0
    have hL : L ∈ sp4 k := by
      show adj L = -L
      ext i j
      rw [adj_apply, Matrix.neg_apply]
      simp only [L, Matrix.of_apply, Fin.rev_lt_rev]
      split_ifs with h
      · exact ent X i j
      · simp
    have hU : X.1 - L ∈ sp4 k := Submodule.sub_mem _ X.2 hL
    rw [Submodule.mem_sup]
    refine ⟨⟨X.1 - L, hU⟩, ?_, ⟨L, hL⟩, ?_, ?_⟩
    · rw [mem_borel_identity_iff_upper]
      intro i j h
      simp [L, h]
    · rw [mem_nilradical_identity_iff]
      intro i j h
      simp [L, not_lt.mpr h]
    · apply Subtype.ext
      simp

private theorem up_mem (a b c d e f : k) : (!![a, c, d, e; 0, b, f, d; 0, 0, -b, -c; 0, 0, 0, -a] : M4 k) ∈ sp4 k := by
  show adj _ = -_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem up_zero (X : sp4 k) (hu : IsUp X.1) (h0 : X.1 0 0 = 0) (h1 : X.1 1 1 = 0) (h2 : X.1 0 1 = 0)
    (h3 : X.1 0 2 = 0) (h4 : X.1 0 3 = 0) (h5 : X.1 1 2 = 0) : X = 0 := by
  apply Subtype.ext
  ext i j
  have e := ent X i j
  fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, h0, h1, h2, h3, h4, h5] at e ⊢ <;>
    first
    | exact hu _ _ (by decide)
    | exact e
    | exact neg_eq_zero.mp e.symm
    | skip

private theorem bor1 : Module.finrank k (bor (1 : M4 k)) = 6 := by
  let f : bor (1 : M4 k) →ₗ[k] (Fin 6 → k) :=
    { toFun := fun X => ![X.1.1 0 0, X.1.1 1 1, X.1.1 0 1, X.1.1 0 2, X.1.1 0 3, X.1.1 1 2]
      map_add' := fun X Y => by
        ext t
        fin_cases t <;> rfl
      map_smul' := fun c X => by
        ext t
        fin_cases t <;> rfl }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hc : ∀ t, f X t = 0 := fun t => congrFun hX t
    exact Subtype.ext (up_zero X.1 ((mem_borel_identity_iff_upper X.1).mp X.2) (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5))
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨⟨!![v 0, v 2, v 3, v 4; 0, v 1, v 5, v 3; 0, 0, -v 1, -v 2; 0, 0, 0, -v 0],
      up_mem _ _ _ _ _ _⟩, ?_⟩, ?_⟩
    · rw [mem_borel_identity_iff_upper]
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · ext t
      fin_cases t <;> rfl
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), Module.finrank_fin_fun]

private theorem tor2 : Module.finrank k (tor k) = 2 := by
  let f : tor k →ₗ[k] (Fin 2 → k) :=
    { toFun := fun X => ![X.1.1 0 0, X.1.1 1 1]
      map_add' := fun X Y => by
        ext t
        fin_cases t <;> rfl
      map_smul' := fun c X => by
        ext t
        fin_cases t <;> rfl }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h0 : X.1.1 0 0 = 0 := congrFun hX 0
    have h1 : X.1.1 1 1 = 0 := congrFun hX 1
    have hd : Matrix.IsDiag X.1.1 := X.2
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have e := ent X.1 i j
    fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, h0, h1] at e ⊢ <;>
      first
      | exact hd (by decide)
      | exact e
      | exact neg_eq_zero.mp e.symm
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨⟨!![v 0, 0, 0, 0; 0, v 1, 0, 0; 0, 0, -v 1, -0; 0, 0, 0, -v 0],
      up_mem _ _ _ _ _ _⟩, ?_⟩, ?_⟩
    · show Matrix.IsDiag _
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · ext t
      fin_cases t <;> rfl
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), Module.finrank_fin_fun]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.spDims :
    ∀ (k : Type) [Field k], (2 : k) ≠ 0 → Module.finrank k (tor k) = 2 ∧ ∀ n : M4 k, IsGSp 1 n → Module.finrank k (bor n) = 6 ∧ IsCompl (bor n) (nil n) := by
  intro k _ _
  refine ⟨X1.tor2, fun n hn => ⟨?_, ?_⟩⟩
  · have hm : (bor (1 : M4 k)).map ((X1.cjE n hn).symm : sp4 k →ₗ[k] sp4 k)
        = (bor 1).comap (X1.cjE n hn : sp4 k →ₗ[k] sp4 k) :=
      Submodule.map_equiv_eq_comap_symm _ _
    rw [X1.bor_eq n hn, ← hm, LinearEquiv.finrank_map_eq, X1.bor1]
  · rw [X1.bor_eq n hn, X1.nil_eq n hn]
    exact (Submodule.orderIsoMapComap (X1.cjE n hn)).symm.isCompl X1.compl1
end
