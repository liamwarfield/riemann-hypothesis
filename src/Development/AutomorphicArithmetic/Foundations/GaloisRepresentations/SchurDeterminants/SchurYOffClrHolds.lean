module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PVdmSplit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseCoset
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private def latt {O K ι : Type} [CommRing O] [Field K] (τ : ι → (O →+* K)) (N : O) (k : ℕ) :
    AddSubgroup (ι × Fin k → K) where
  carrier := {x | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)}
  add_mem' := by
    rintro _ _ ⟨β, rfl⟩ ⟨β', rfl⟩
    refine ⟨β + β', ?_⟩
    funext p
    simp [pt, mul_add]
  zero_mem' := by
    refine ⟨0, ?_⟩
    funext p
    simp [pt]
  neg_mem' := by
    rintro _ ⟨β, rfl⟩
    refine ⟨-β, ?_⟩
    funext p
    simp [pt]

theorem denseCoset_of : DenseSub → SpanTop → DenseOff → DenseCoset := by
  intro hS hT hO O K ι _ _ _ _ τ hτ N hN k a Q hQ
  have hspan : Submodule.span K ((latt τ N k : AddSubgroup (ι × Fin k → K)) : Set (ι × Fin k → K)) = ⊤ :=
    hT O K ι τ hτ N hN k
  have hd := hS K (ι × Fin k) (latt τ N k) (pt τ a) hspan
  have hd2 := hO K (ι × Fin k) _ hd Q hQ
  intro P hP
  apply hd2
  rintro x ⟨hx, hxQ⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin k → O, x - pt τ a = pt τ (fun s => N * β s) := hx
  have hxe : x = pt τ (fun s => a s + N * β s) := by
    rw [sub_eq_iff_eq_add.mp hβ]
    funext p
    simp [pt, add_comm]
  refine hP x ⟨fun s => a s + N * β s, fun s => ?_, ?_, hxe⟩
  · simp
  · rw [← hxe]
    exact hxQ

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanTop
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem span_embeddings_mul_eq_univ_of_injective {O K ι : Type} [CommRing O] [Field K] [Fintype ι] (τ : ι → O →+* K)
    (hτ : Function.Injective τ) (N : O) (hN : ∀ t, τ t N ≠ 0) :
    Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hφv : ∀ v : ι → K, φ v = ∑ t, v t * φ (Pi.single t 1) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext s
    simp [Pi.single_apply, eq_comm]
  have hzero : ∀ x : O, ∑ t, (φ (Pi.single t 1) * τ t N) * τ t x = 0 := by
    intro x
    have hx : (fun t => τ t (N * x)) ∈ Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} :=
      Submodule.subset_span ⟨x, rfl⟩
    have : φ (fun t => τ t (N * x)) = 0 := by
      have h2 := Submodule.mem_map_of_mem (f := φ) hx
      rw [hmap, Submodule.mem_bot] at h2
      exact h2
    rw [hφv] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul]
    ring
  have hli : LinearIndependent K (fun t => ((τ t : O →* K) : O → K)) := by
    refine (linearIndependent_monoidHom O K).comp (fun t => (τ t : O →* K)) ?_
    intro a b hab
    apply hτ
    ext y
    exact DFunLike.congr_fun hab y
  have hc : ∀ t, φ (Pi.single t 1) * τ t N = 0 := by
    refine Fintype.linearIndependent_iff.1 hli _ ?_
    funext x
    simpa [Finset.sum_apply] using hzero x
  apply hφ
  refine LinearMap.ext fun v => ?_
  rw [hφv, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(mul_eq_zero.1 (hc t)).resolve_right (hN t), mul_zero]

theorem spanTop : SpanTop := by
  classical
  intro O K ι _ _ _ τ hτ N hN k
  have hA := span_embeddings_mul_eq_univ_of_injective τ hτ N hN
  let L : Fin k → (ι → K) →ₗ[K] (ι × Fin k → K) := fun j =>
    LinearMap.pi (fun p => if p.2 = j then LinearMap.proj p.1 else 0)
  have hL : ∀ j w p, L j w p = if p.2 = j then w p.1 else 0 := by
    intro j w p
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> simp
  have hsub : ∀ j, Submodule.map (L j) (Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)}) ≤
      Submodule.span K {x | ∃ β : Fin k → O, x = pt τ fun s ↦ N * β s} := by
    intro j
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨v, ⟨x, rfl⟩, rfl⟩
    refine ⟨Pi.single j x, ?_⟩
    funext p
    rw [hL]
    simp only [pt, Pi.single_apply]
    split_ifs <;> simp_all
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ j, L j (fun t => v (t, j)) := by
    funext p
    simp [Finset.sum_apply, hL]
  rw [hv]
  refine Submodule.sum_mem _ fun j _ => hsub j ?_
  refine Submodule.mem_map_of_mem ?_
  rw [hA]
  exact Submodule.mem_top

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExtract
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem extract : Extract := by
  classical
  intro K σ A M _ _ _ x hx e he w
  set v : A → M → K := fun a m => ∏ p, x a p ^ e m p with hvdef
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    have hφv : ∀ u : M → K, φ u = ∑ m, u m * φ (Pi.single m 1) := by
      intro u
      rw [LinearMap.pi_apply_eq_sum_univ φ u]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_mul]
      congr 2
      ext s
      simp [Pi.single_apply, eq_comm]
    let E : M → σ →₀ ℕ := fun m => Finsupp.equivFunOnFinite.symm (e m)
    have hE : Function.Injective E := fun a b h => he (by simpa [E] using h)
    let Q : MvPolynomial σ K := ∑ m, monomial (E m) (φ (Pi.single m 1))
    have hQ : Q = 0 := by
      refine hx Q ?_
      rintro _ ⟨a, rfl⟩
      have h1 : φ (v a) = 0 := by
        have h2 := Submodule.mem_map_of_mem (f := φ) (Submodule.subset_span ⟨a, rfl⟩ : v a ∈ Submodule.span K (Set.range v))
        rw [hmap, Submodule.mem_bot] at h2
        exact h2
      rw [hφv] at h1
      rw [← h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Q, map_sum, eval_monomial]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), mul_comm]
      rfl
    apply hφ
    refine LinearMap.ext fun u => ?_
    rw [hφv, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hc := congrArg (AddMonoidAlgebra.coeff · (E m)) hQ
    simp only [Q, coeff_sum, coeff_monomial, AddMonoidAlgebra.coeff_zero, hE.eq_iff] at hc
    simp at hc
    rw [hc, mul_zero]
  have hw : w ∈ Submodule.span K (Set.range v) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hw
  refine ⟨c, fun m => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvdef]

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairCount
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairCount_of :
    PairSplit → PairCount := by
  intro hP n i
  have hS : ∑ a : Fin n, (n - 1 - (a : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a), Finset.sum_range_reflect (fun a => a) n,
      Finset.sum_range_id, Nat.choose_two_right]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hC : (m + 1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hi : (i : ℕ) ≤ m := by have := i.isLt; omega
  simp only [Nat.add_sub_cancel] at hS ⊢
  refine ⟨?_, ?_⟩
  · have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun k => m - (k : ℕ))
      (Finset.mem_univ i)
    omega
  · have h := hP (Multiplicative ℕ) (m + 1) (fun _ _ => Multiplicative.ofAdd 1) i
    apply_fun Multiplicative.toAdd at h
    simp [toAdd_prod] at h
    omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibreOff
open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma prod_scale_at {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleAt y i g k = y * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h1 : scaleAt y i g i = y * g i := by simp [scaleAt]
  have h2 : ∏ k ∈ univ.erase i, scaleAt y i g k = ∏ k ∈ univ.erase i, g k :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleAt, ne_of_mem_erase hk])
  rw [h1, h2]; ring

theorem UpperTheory.Gal.Schur.fibreOff_of :
    SchurYOff → SchurHomog → SchurDet → FibreOff := by
  intro hY hH hD
  intro R ι _ _ _ _ n t₀ t₁ h ε lam m hm g y hu
  have hsplit : ∀ F : ι → R,
      ∏ t, F t = F t₀ * (F t₁ * ∏ t ∈ (univ.erase t₀).erase t₁, F t) := by
    intro F
    rw [← Finset.mul_prod_erase univ F (mem_univ t₀),
      ← Finset.mul_prod_erase (univ.erase t₀) F (mem_erase.2 ⟨h.symm, mem_univ _⟩)]
  have hlam : lam t₀ = fun i => (fun _ => 0 : Fin n → ℕ) i + m := by
    funext i; simp [hm]
  have hsch0 : ∀ h' : Fin n → R, sch (lam t₀) h' = (∏ k, h' k) ^ m := by
    intro h'
    rw [hlam]
    exact ((hD R n h').2 _ m).trans (by rw [(hD R n h').1, mul_one])
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    have hc : ∀ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
        y ^ (ε t * ∑ i, lam t i) * sch (lam t) (g t) := by
      intro t ht
      have ht1 : t ≠ t₁ := ne_of_mem_erase ht
      have ht0 : t ≠ t₀ := ne_of_mem_erase (mem_of_mem_erase ht)
      simp only [twist, if_neg ht0, if_neg ht1]
      rw [hH, ← pow_mul]
    rw [Finset.prod_congr rfl hc, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have tw0 : ∀ i, twist t₀ t₁ ε y i g t₀ = scaleAt y i (g t₀) := by
    intro i; simp [twist]
  have tw1 : ∀ i, twist t₀ t₁ ε y i g t₁ = scaleOff y i (g t₁) := by
    intro i; simp [twist, h.symm]
  have hterm : ∀ i : Fin n,
      (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
          ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k)) =
        (y ^ m * (∏ k, g t₀ k) ^ m *
            (y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
              ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t))) *
          (sch (lam t₁) (scaleOff y i (g t₁)) *
            ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k))) := by
    intro i
    rw [hsplit (fun t => sch (lam t) (twist t₀ t₁ ε y i g t)), tw0, tw1, hrest, hsch0,
      prod_scale_at, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hY R n (lam t₁) (g t₁) y hu,
    hsplit (fun t => sch (lam t) (g t)), hsch0, pow_add]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseOff
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.denseOff :
    DenseOff := by
  intro K σ _ D hD Q hQ P hP
  have hPQ : P * Q = 0 := by
    apply hD
    intro x hx
    by_cases hq : eval x Q = 0
    · rw [map_mul, hq, mul_zero]
    · rw [map_mul, hP x ⟨hx, hq⟩, zero_mul]
  exact (mul_eq_zero.1 hPQ).resolve_right hQ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOf
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.schurY_of :
    SchurYClr → VdmSplit → SchurY := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  have hScale : ∀ i, vdm (scaleAt y i g) =
      (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [hSplit R n (scaleAt y i g) i]
    congr 1
    · congr 1
      unfold vdmAway
      refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
      have ha' : a ≠ i := Finset.ne_of_mem_erase ha
      have hb' : b ≠ i := Finset.ne_of_mem_erase hb
      simp [scaleAt, ha', hb']
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := Finset.ne_of_mem_erase hk
      simp [scaleAt, hk']
  have key : ∀ i, (∏ k ∈ univ.erase i, (g k - y * g i) * Ring.inverse (g k - g i)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [show g i - g k = -(g k - g i) by ring, mul_neg, mul_assoc,
      Ring.inverse_mul_cancel _ (hu i k hki), mul_one]
    ring
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) * vdm g =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ))) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hScale i, hSplit R n g i, ← key i]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairSplit
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairSplit :
    PairSplit := by
  intro R _ n F i
  have hA : ∀ a : Fin n, ∏ b ∈ Ioi a, F a b =
      (∏ b ∈ (Ioi a).erase i, F a b) * (if a < i then F a i else 1) := by
    intro a
    split_ifs with h
    · exact (Finset.prod_erase_mul _ _ (by simpa using h)).symm
    · rw [Finset.erase_eq_self.mpr (by simpa using h), mul_one]
  have hL : ∏ a, ∏ b > a, F a b = ∏ a, ∏ b ∈ Ioi a, F a b := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rfl
  have h1 : (univ : Finset (Fin n)).filter (fun a => a < i) = (univ.erase i).filter (fun k => k < i) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
    constructor
    · intro h; exact ⟨ne_of_lt h, h⟩
    · intro h; exact h.2
  have h2 : (univ.erase i).filter (fun k => ¬ k < i) = Ioi i := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, Finset.mem_Ioi, and_true, not_lt]
    constructor
    · intro h; exact lt_of_le_of_ne h.2 (Ne.symm h.1)
    · intro h; exact ⟨ne_of_gt h, le_of_lt h⟩
  rw [hL, Finset.prod_congr rfl fun a _ => hA a, Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    Finset.erase_eq_self.mpr (by simp), ← Finset.prod_filter, Finset.prod_ite, h1, h2]
  simp only [mul_comm, mul_left_comm, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PMixDet
open Finset MvPolynomial UpperTheory.Gal.Schur

private theorem prod_ite_eq_mul_prod_erase {R : Type} [CommRing R] {n : ℕ} (d d' : Fin n → R) (a : Fin n) :
    ∏ b, (if b = a then d b else d' b) = d a * ∏ b ∈ univ.erase a, d' b := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ a), if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [if_neg (Finset.ne_of_mem_erase hb)]

theorem UpperTheory.Gal.Schur.mixDet :
    MixDet := by
  intro R _ n M d d'
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]
  have key : ∀ i, (∏ j, if j = i then d (σ j) else d' (σ j)) =
      ∏ b, (if b = σ i then d b else d' b) := by
    intro i
    rw [← Equiv.prod_comp σ (fun b => if b = σ i then d b else d' b)]
    simp only [σ.injective.eq_iff]
  calc _ = (∑ i, ∏ b, (if b = σ i then d b else d' b)) *
        ((Equiv.Perm.sign σ : ℤ) * ∏ x, M (σ x) x) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key]
        ring
    _ = _ := by
        congr 1
        rw [Equiv.sum_comp σ (fun a => ∏ b, if b = a then d b else d' b)]
        exact Finset.sum_congr rfl fun a _ => prod_ite_eq_mul_prod_erase d d' a
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Vdm
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.tie :
    Comparison₂ := by
  intro R _ _ n lam g
  have h := congrArg (aeval g) (GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_add_staircase_eq lam)
  rw [AlgHom.map_det, map_mul] at h
  have hM : ((Matrix.of fun i j => (X j : MvPolynomial (Fin n) ℚ) ^ (lam i + (n - 1 - (i : ℕ)))).map
      (aeval g)) = Matrix.of fun i j => g j ^ (lam i + (n - 1 - (i : ℕ))) := by
    ext i j
    simp
  simp [AlgHom.mapMatrix_apply, GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf, map_prod, hM] at h
  simpa [sch, vdm, altn, shift] using h.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYClrOf
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYClr_of : Comparison₂ → MixDet → SchurYClr ∧ SchurYOffClr := by
  intro hT hM
  constructor
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun a => y ^ shift lam a) (fun _ => 1)
    simp only [Matrix.of_apply, prod_const_one, mul_one] at h
    calc ∑ i, altn (shift lam) (scaleAt y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then y ^ shift lam a else 1) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleAt]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun _ => 1) (fun a => y ^ shift lam a)
    simp only [Matrix.of_apply, one_mul, prod_pow_eq_pow_sum] at h
    calc ∑ i, altn (shift lam) (scaleOff y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then 1 else y ^ shift lam a) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleOff]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffPow
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrPow_of :
    SchurYOffClr → VdmSplit → PairCount → OffClrPow := by
  intro hS hV hP R _ _ n lam g y
  have key : ∀ i : Fin n, vdm (scaleOff y i g) = y ^ (n - 1).choose 2 *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) := by
    intro i
    have h1 : vdmAway i (scaleOff y i g) = y ^ (n - 1).choose 2 * vdmAway i g := by
      rw [← (hP n i).2, ← Finset.prod_pow_eq_pow_sum]
      unfold vdmAway
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      have ha' : a ≠ i := (Finset.mem_erase.mp ha).1
      calc ∏ b ∈ (Finset.Ioi a).erase i, (scaleOff y i g a - scaleOff y i g b)
          = ∏ b ∈ (Finset.Ioi a).erase i, (y * (g a - g b)) := by
            refine Finset.prod_congr rfl fun b hb => ?_
            have hb' : b ≠ i := (Finset.mem_erase.mp hb).1
            simp [scaleOff, ha', hb', mul_sub]
        _ = y ^ ((Finset.Ioi a).erase i).card * ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h2 : ∏ k ∈ univ.erase i, (scaleOff y i g i - scaleOff y i g k) =
        ∏ k ∈ univ.erase i, (g i - y * g k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [scaleOff, hk']
    rw [hV R n (scaleOff y i g) i, h1, h2]
    ring
  have hL : y ^ (n - 1).choose 2 * ∑ i, sch lam (scaleOff y i g) *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i]
    ring
  have hR : ∀ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ)))) =
      y ^ (n - 1).choose 2 * y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by
    intro i
    rw [Finset.sum_add_distrib, (hP n i).1, ← pow_add]
    congr 1
    omega
  rw [hL, hS R n lam g y, Finset.sum_congr rfl fun i _ => hR i, ← Finset.mul_sum]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanE
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem one_mem_eSpan (K : Type) [CommRing K] (n : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n 0 := by
  unfold eSpan
  exact Submodule.subset_span ⟨Fin.elim0, by simp⟩

private theorem esymm_mem_eSpan (K : Type) [CommRing K] (n : ℕ) (i : Fin n) :
    esymm (Fin n) K ((i : ℕ) + 1) ∈ eSpan K n 1 := by
  unfold eSpan
  exact Submodule.subset_span ⟨fun _ => i.succ, by simp⟩

private theorem exists_mem_eSpan (h : ESpanMul) (K : Type) [CommRing K] (n : ℕ)
    (q : MvPolynomial (Fin n) K) :
    ∃ k, aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q ∈ eSpan K n k := by
  obtain ⟨hmono, hmul⟩ := h K n
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (one_mem_eSpan K n)
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    refine ⟨k + 1, ?_⟩
    rw [map_mul, aeval_X]
    exact hmul _ _ _ _ hk (esymm_mem_eSpan K n i)

theorem spanE_of : ESpanMul → SpanE := by
  intro h K _ n P hP
  obtain ⟨q, hq⟩ := esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩
  have hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P := by
    have := congrArg Subtype.val hq
    rwa [esymmAlgHom_apply] at this
  obtain ⟨k₀, hk₀⟩ := exists_mem_eSpan h K n q
  refine ⟨k₀, fun k hk => ?_⟩
  have hmem := (h K n).1 _ _ hk hk₀
  rw [hq'] at hmem
  unfold eSpan at hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨w, hw.symm⟩

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseSub
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem denseSub : DenseSub := by
  intro K σ _ _ _ L a hL Q hQ
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have hx : x - a ∈ Submodule.span K (L : Set (σ → K)) := by
    rw [hL]
    exact Submodule.mem_top
  obtain ⟨n, c, v, hcv⟩ := Submodule.mem_span_set'.mp hx
  let p0 : (Fin n → K) → σ → K := fun t j => a j + ∑ i, t i * (v i : σ → K) j
  let F : σ → MvPolynomial (Fin n) K := fun j => C (a j) + ∑ i, X i * C ((v i : σ → K) j)
  have hev : ∀ t, eval t (bind₁ F Q) = eval (p0 t) Q := by
    intro t
    have h1 : aeval t (bind₁ F Q) = eval t (bind₁ F Q) := rfl
    have h2 : aeval (fun j => aeval t (F j)) Q = eval (fun j => aeval t (F j)) Q := rfl
    rw [← h1, aeval_bind₁, h2]
    congr 2
    funext j
    simp [p0, F]
  have hzero : bind₁ F Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → K)) ?_ ?_
    · intro _
      exact Set.infinite_range_of_injective Int.cast_injective
    · intro t ht
      rw [hev, map_zero]
      choose m hm using fun i => ht i (Set.mem_univ i)
      apply hQ
      show p0 t - a ∈ L
      have hsum : p0 t - a = ∑ i, m i • (v i : σ → K) := by
        funext j
        simp [p0, ← hm, Finset.sum_apply, zsmul_eq_mul]
      rw [hsum]
      exact sum_mem (fun i _ => zsmul_mem (v i).2 (m i))
  have hxp : p0 c = x := by
    funext j
    have hj := congrFun hcv j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hj
    simp only [p0, hj]
    ring
  rw [← hxp, ← hev, hzero, map_zero]

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExpand
open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma one_factor {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (n : ℕ) (x : R)
    (g : Fin n → R) :
    detOne x g = ∑ a : Fin (n + 1), x ^ (a : ℕ) * ((-1) ^ (a : ℕ) * aeval g (esymm (Fin n) K a)) := by
  have key : ∀ a : ℕ, x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a)) =
      ∑ t ∈ powersetCard a (univ : Finset (Fin n)), ∏ j ∈ t, (-(x * g j)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [esymm, map_sum, map_prod, aeval_X, mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [prod_neg, prod_mul_distrib, prod_const, (mem_powersetCard.1 ht).2]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun a => x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a))) (n + 1)]
  simp only [key]
  have hc : n + 1 = #(univ : Finset (Fin n)) + 1 := by simp
  rw [hc, ← sum_powerset, ← prod_one_add]
  unfold detOne
  simp only [sub_eq_add_neg]

theorem UpperTheory.Gal.Schur.expand :
    Expand := by
  intro K R π _ _ _ _ _ n x g
  simp only [one_factor (K := K)]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [prod_mul_distrib]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterpNF
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private lemma resO_injective {E K : Type} [Field E] [NumberField E] [Field K] :
    Function.Injective (resO : (E →+* K) → (NumberField.RingOfIntegers E →+* K)) := by
  intro τ τ' h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (NumberField.RingOfIntegers E)) h

private lemma resO_ne_zero {E K : Type} [Field E] [NumberField E] [Field K] (τ : E →+* K)
    {N : NumberField.RingOfIntegers E} (hN : N ≠ 0) : resO τ N ≠ 0 := by
  intro h
  apply hN
  have h1 : τ (algebraMap (NumberField.RingOfIntegers E) E N) = 0 := h
  have h2 : algebraMap (NumberField.RingOfIntegers E) E N = 0 := by
    simpa using h1
  exact NumberField.RingOfIntegers.coe_injective (by simpa using h2)

private lemma one_sub_ne_zero {K σ : Type} [Field K] (p : σ) (b : K) :
    (1 - X p * C b : MvPolynomial σ K) ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ : σ => (0 : K))) h
  simp at this

theorem interpNF_of : Interp → InterpNF := by
  intro hI E K _ _ _ _ n lam
  classical
  by_cases hE : IsEmpty (E →+* K)
  · refine ⟨0, fun k _ N hN B => ?_⟩
    refine ⟨Finsupp.single (fun _ => N) 1, ?_, ?_⟩
    · intro α hα s
      have hα' : α = fun _ => N := by
        simpa using Finsupp.support_single_subset hα
      subst hα'
      exact ⟨hN, dvd_rfl, fun τ => hE.elim τ⟩
    · intro R _ _ _ g
      rw [Finsupp.sum_single_index (by simp)]
      simp [Finset.univ_eq_empty]
  · rw [not_isEmpty_iff] at hE
    obtain ⟨τ₀⟩ := hE
    obtain ⟨k₀, hk⟩ := hI (NumberField.RingOfIntegers E) K (E →+* K) resO resO_injective n
      (fun τ => MvPolynomial.map (algebraMap ℚ K)
        (GroundTheory.Heights₂.Heights.RestTerms.schur (Fin n) (lam τ)))
      (fun τ => (GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric _).map _)
    refine ⟨k₀, fun k hkk N hN B => ?_⟩
    let Q : MvPolynomial ((E →+* K) × Fin k) K :=
      ∏ p, (X p * ∏ b ∈ B, (1 - X p * C b))
    have hQ : Q ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p _ => mul_ne_zero (X_ne_zero p) ?_
      exact Finset.prod_ne_zero_iff.mpr fun b _ => one_sub_ne_zero p b
    obtain ⟨c, hc, hsum⟩ := hk k hkk N (fun t => resO_ne_zero t hN) (fun _ => 0) Q hQ
    refine ⟨c, ?_, ?_⟩
    · intro α hα s
      obtain ⟨hdvd, hev⟩ := hc α hα
      have hfac : ∀ p : (E →+* K) × Fin k, pt resO α p ≠ 0 ∧
          ∀ b ∈ B, 1 - pt resO α p * b ≠ 0 := by
        intro p
        have h0 : eval (pt resO α) (X p * ∏ b ∈ B, (1 - X p * C b)) ≠ 0 := by
          intro h
          apply hev
          exact (map_prod (eval (pt resO α)) _ _).trans
            (Finset.prod_eq_zero (Finset.mem_univ p) h)
        simp only [map_mul, eval_X, map_prod, map_sub, map_one, eval_C] at h0
        refine ⟨left_ne_zero_of_mul h0, fun b hb => ?_⟩
        exact (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h0)) b hb
      refine ⟨?_, by simpa using hdvd s, fun τ b hb => (hfac (τ, s)).2 b hb⟩
      intro h0
      apply (hfac (τ₀, s)).1
      simp [pt, h0]
    · intro R _ _ _ g
      have hR := hsum R g
      letI : IsScalarTower ℚ K R := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
      rw [hR]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact MvPolynomial.aeval_map_algebraMap _ _ _

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffOf
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYOff_of : OffClrRed → VdmSplit → SchurYOff := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))) * vdm g =
      sch lam g * vdm g * ∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hSplit R n g i]
  have key : (∏ k ∈ univ.erase i, (g i - y * g k) * Ring.inverse (g i - g k)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (g i - y * g k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [mul_assoc, Ring.inverse_mul_cancel _ (by simpa using (hu i k hki).neg), mul_one]
  rw [← key]
  ring

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.FibreSum
noncomputable section

open Finset
open scoped Classical

namespace UpperTheory.Gal.Schur

def FibreSum : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [CharZero K] (n : ℕ)
    (lam : (E →+* K) → Fin n → ℕ), ∃ k₀, ∀ k, k₀ ≤ k →
    ∀ (N : NumberField.RingOfIntegers E), N ≠ 0 → ∀ B : Finset K,
      ∃ c : (Fin k → NumberField.RingOfIntegers E) →₀ K,
        (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ N ∣ α s ∧ ∀ τ : E →+* K, ∀ b ∈ B, 1 - resO τ (α s) * b ≠ 0) ∧
        ∀ (R : Type) [CommRing R] [Algebra K R] [Algebra ℚ R] (t₀ t₁ : E →+* K), t₀ ≠ t₁ →
          ∀ (ε : (E →+* K) → ℕ) (m : ℕ) (g : (E →+* K) → Fin n → R) (y : R),
          ((∀ i, lam t₁ i = m) → (∀ i j, j ≠ i → IsUnit (g t₀ j - g t₀ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₀ j - y * g t₀ i) * Ring.inverse (g t₀ j - g t₀ i))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ ((n - 1) * m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))) ∧
          ((∀ i, lam t₀ i = m) → (∀ i j, j ≠ i → IsUnit (g t₁ j - g t₁ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₁ i - y * g t₁ j) * Ring.inverse (g t₁ i - g t₁ j))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ (m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (∑ j ∈ univ.erase i, lam t₁ j + (i : ℕ))))

theorem fibreSum_of (h : InterpNF) (h₁ : Fibre) (h₂ : FibreOff) : FibreSum := by
  intro E K _ _ _ _ n lam
  obtain ⟨k₀, hk⟩ := h E K n lam
  refine ⟨k₀, fun k hk' N hN B => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk k hk' N hN B
  refine ⟨c, hc, fun R _ _ _ t₀ t₁ ht ε m g y => ?_⟩
  have swap : ∀ C : Fin n → R,
      (c.sum fun α r => r • ∑ i,
        (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) * C i) =
      ∑ i, (∏ τ, sch (lam τ) (twist t₀ t₁ ε y i g τ)) * C i := by
    intro C
    rw [Finsupp.sum]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsum R (twist t₀ t₁ ε y i g), Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_mul_assoc]
  refine ⟨fun hm hu => ?_, fun hm hu => ?_⟩
  · rw [swap]
    exact h₁ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu
  · rw [swap]
    exact h₂ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.WeylTieOf
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem vdm_ne {K : Type} [Field K] {n : ℕ} (g : Fin n → K)
    (hg : Function.Injective g) : vdm g ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  refine sub_ne_zero.2 fun h => ?_
  have := hg h
  subst this
  simp at hj

private theorem num_eq {K : Type} [Field K] {n : ℕ} (l : Fin n → ℤ) (m : ℕ) (lam : Fin n → ℕ)
    (g : Fin n → K) (hl : ∀ i, l i + m = lam i) (h0 : ∀ i, g i ≠ 0) :
    (∏ k, g k) ^ m * altnZ (fun i => l i + n - 1 - (i : ℕ)) g = altn (shift lam) g := by
  unfold altnZ altn shift
  rw [← Finset.prod_pow, ← Matrix.det_mul_row (fun k => g k ^ m)]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [← zpow_natCast (g j) m, ← zpow_natCast (g j) (lam i + (n - 1 - (i : ℕ))), ← zpow_add₀ (h0 j)]
  congr 1
  have h1 := hl i
  have h2 := i.isLt
  push_cast
  omega

theorem weylTie_of : Comparison₂ → WeylTie := by
  intro hT K _ _ n l m lam g hl hg h0
  have hv := vdm_ne g hg
  have hp : (∏ k, g k) ^ m ≠ 0 := pow_ne_zero _ (prod_ne_zero_iff.mpr fun k _ => h0 k)
  rw [div_eq_div_iff hv hp, hT K n lam g, ← num_eq l m lam g hl h0]
  ring

end UpperTheory.Gal.Schur
end
end

noncomputable section

open Finset

namespace UpperTheory.Gal.Schur

theorem SchurYClr_holds : SchurYClr := (schurYClr_of tie mixDet).1
theorem SchurYOffClr_holds : SchurYOffClr := (schurYClr_of tie mixDet).2
theorem VdmSplit_holds : VdmSplit := vdmSplit_of pairSplit
theorem SchurY_holds : SchurY := schurY_of SchurYClr_holds VdmSplit_holds
theorem SchurYOff_holds : SchurYOff :=
  schurYOff_of (offClrRed_of (offClrPow_of SchurYOffClr_holds VdmSplit_holds (pairCount_of pairSplit)))
    VdmSplit_holds
theorem SchurHomog_holds : SchurHomog := schurHomog
theorem SchurDet_holds : SchurDet := schurDet_of tie
theorem WeylTie_holds : WeylTie := weylTie_of tie
theorem SpanE_holds : SpanE := spanE_of eSpanMul
theorem DenseCoset_holds : DenseCoset := denseCoset_of denseSub spanTop denseOff
theorem Interp_holds : Interp := interp_of (spanProd_of SpanE_holds) expand extract DenseCoset_holds
theorem InterpNF_holds : InterpNF := interpNF_of Interp_holds
theorem Fibre_holds : Fibre := fibre_of SchurY_holds schurHomog SchurDet_holds
theorem FibreOff_holds : FibreOff := fibreOff_of SchurYOff_holds schurHomog SchurDet_holds
theorem FibreSum_holds : FibreSum := fibreSum_of InterpNF_holds Fibre_holds FibreOff_holds

end UpperTheory.Gal.Schur
