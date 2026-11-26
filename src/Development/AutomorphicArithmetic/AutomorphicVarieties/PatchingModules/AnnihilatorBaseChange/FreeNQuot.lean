module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OneAddPowSubOneMem
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.prime_pow_dvd_choose (l : ℕ) (hl : l.Prime) (e j s : ℕ) (hj : j ≤ e)
    (hs : s + 1 < l ^ (e - j)) : l ^ j ∣ (l ^ e).choose (s + 1) := by
  have hm : s + 1 ≤ l ^ e :=
    le_of_lt (lt_of_lt_of_le hs (Nat.pow_le_pow_right hl.pos (Nat.sub_le e j)))
  have hC : (l ^ e).choose (s + 1) ≠ 0 := (Nat.choose_pos hm).ne'
  have hv : (s + 1).factorization l < e - j := by
    have h1 : l ^ (s + 1).factorization l ≤ s + 1 :=
      Nat.le_of_dvd (Nat.succ_pos s) (Nat.ordProj_dvd (s + 1) l)
    exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 (lt_of_le_of_lt h1 hs)
  rw [hl.pow_dvd_iff_le_factorization hC, Nat.factorization_choose_prime_pow hl hm (Nat.succ_ne_zero s)]
  omega

theorem UpperTheory.V.AlgebraTools.one_add_pow_sub_one_mem :
    ∀ (R : Type) [CommRing R] (l : ℕ), l.Prime → ∀ (y : R) (e j k : ℕ), j ≤ e → k ≤ l ^ (e - j) →
      (1 + y) ^ l ^ e - 1 ∈ Ideal.span {y ^ k} ⊔ Ideal.span {(l : R) ^ j} := by
  intro R _ l hl y e j k hj hk
  have hN : (1 + y) ^ l ^ e - 1 =
      ∑ s ∈ Finset.range (l ^ e), y ^ (s + 1) * ((l ^ e).choose (s + 1) : R) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [hN]
  refine Ideal.sum_mem _ fun s _ => ?_
  by_cases hks : k ≤ s + 1
  · apply Ideal.mem_sup_left
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow y hks) _
  · apply Ideal.mem_sup_right
    rw [Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.prime_pow_dvd_choose l hl e j s hj (by omega)
    exact ⟨y ^ (s + 1) * c, by rw [hc]; push_cast; ring⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeModuleQuotient
theorem UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot
    {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ)
    (e : M ≃+ (Fin c → S ⧸ I)) (he : ∀ (z : S) (x : M), e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K),
      ∀ (a : S) (x : M ⧸ (Ideal.map s K • ⊤ : Submodule R M)), e' (s a • x) = a • e' x := by
  classical
  let φ : M →+ (Fin c → S ⧸ K) :=
    { toFun := fun x i => Ideal.Quotient.factor hIK (e x i)
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hφ : ∀ x i, φ x i = Ideal.Quotient.factor hIK (e x i) := fun _ _ => rfl
  have hsm : ∀ (a : S) (x : M), φ (s a • x) = a • φ x := by
    intro a x
    funext i
    rw [Pi.smul_apply, hφ, hφ, he, Pi.smul_apply]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e x i)
    rw [← hy]
    rfl
  have hsurj : Function.Surjective φ := by
    intro y
    choose t ht using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨e.symm (fun i => Ideal.Quotient.mk I (t i)), ?_⟩
    funext i
    rw [hφ, e.apply_symm_apply, Ideal.Quotient.factor_mk, ht]
  have h1 : ∀ r ∈ Ideal.map s K, ∀ x : M, φ (r • x) = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ => ∀ x : M, φ (r • x) = 0) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨k, hk, rfl⟩ x
      rw [hsm]
      funext i
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ x i)
      rw [Pi.smul_apply, ← hy]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (K.mul_mem_right y hk)
    · intro x; simp
    · intro a b _ _ ha hb x
      rw [add_smul, map_add (f := _), ha, hb, add_zero]
    · intro a b _ hb x
      rw [smul_eq_mul, mul_comm, mul_smul, hb]
  have hker : ∀ x : M, x ∈ (Ideal.map s K • ⊤ : Submodule R M) ↔ φ x = 0 := by
    intro x
    constructor
    · intro hx
      refine Submodule.smul_induction_on (p := fun x => φ x = 0) hx ?_ ?_
      · intro r hr n _; exact h1 r hr n
      · intro a b ha hb; rw [map_add (f := _), ha, hb, add_zero]
    · intro hx
      choose t ht using fun i => Ideal.Quotient.mk_surjective (e x i)
      have htK : ∀ i, t i ∈ K := by
        intro i
        have := congrFun hx i
        rw [hφ, ← ht, Ideal.Quotient.factor_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.1 this
      have hxe : x = ∑ i, s (t i) • e.symm (Pi.single i 1) := by
        apply e.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [he, e.apply_symm_apply]
        rw [← Finset.univ_sum_single (e x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Pi.single_smul, ← ht, ← Algebra.algebraMap_eq_smul_one]
        rfl
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (Ideal.mem_map_of_mem s (htK i)) Submodule.mem_top
  let ψ : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) →+ (Fin c → S ⧸ K) :=
    QuotientAddGroup.lift (Ideal.map s K • ⊤ : Submodule R M).toAddSubgroup φ
      (fun x hx => (hker x).1 hx)
  have hψ : ∀ x : M, ψ (Submodule.Quotient.mk x) = φ x := fun _ => rfl
  have hbij : Function.Bijective ψ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hψ] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((hker y).2 hx)
    · intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk x, hψ x⟩
  refine ⟨AddEquiv.ofBijective ψ hbij, fun a x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul]
  exact hsm a y
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem UpperTheory.V.Pa.Core.freeN_quot {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ) (e : M ≃+ (Fin c → S ⧸ I))
    (he : ∀ z x, e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (K.map s • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K), ∀ a x, e' (s a • x) = a • e' x :=
  _root_.UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot s I K hIK c e he

private theorem UpperTheory.V.Pa.Core.freeN_le (l : ℕ) (hl : l.Prime) (R : Type) [CommRing R] [IsLocalRing R]
    (hR : (l : R) ∈ maximalIdeal R) (q n : ℕ) (a : Fin q → ℕ) (k j : ℕ) (ha : ∀ i, j + k ≤ a i) :
    delIdeal l R n a ≤ kjIdeal R (Fin q × Fin n) k j := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨p, rfl⟩
  have h1 := ha p.1
  have h2 : a p.1 - j < l ^ (a p.1 - j) := Nat.lt_pow_self hl.one_lt
  have h := one_add_pow_sub_one_mem (MvPowerSeries (Fin q × Fin n) R) l hl (MvPowerSeries.X p) (a p.1) j k
    (by omega) (by omega)
  refine (sup_le_sup ?_ ?_ : _ ≤ kjIdeal R (Fin q × Fin n) k j) h
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self p)) k
  · rw [Ideal.span_singleton_le_iff_mem]
    have := Ideal.mem_map_of_mem (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) (Ideal.pow_mem_pow hR j)
    rwa [map_pow, map_natCast] at this

theorem UpperTheory.V.Pa.Core.freeN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (k j : ℕ), ∀ᶠ N in (Λ.U : Filter ℕ), ∃ (c : ℕ) (e : (MN m N ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j).map m.s.toRingHom • ⊤ : Submodule W.R (MN m N))) ≃+ (Fin c → Sinf O Unit D T.q n ⧸ kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j)), ∀ a x, e (m.s.toRingHom a • x) = a • e x := by
  intro l hl L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m k j
  have hlm : (l : abelian₂ O Unit D) ∈ maximalIdeal (abelian₂ O Unit D) := by
    intro hu
    have h1 := hu.map ((residue O).comp (MvPowerSeries.constantCoeff : abelian₂ O Unit D →+* O))
    haveI := hO.char
    rw [map_natCast, CharP.cast_eq_zero] at h1
    exact not_isUnit_zero h1
  refine Λ.U_le ((eventually_ge_atTop (j + k)).mono fun N hN => ⟨(A.A N).rk, ?_⟩)
  refine freeN_quot (M := MN m N) m.s.toRingHom _ _
    (freeN_le l hl.out _ hlm T.q n (A.A N).a k j fun i => hN.trans ((A.A N).le_a i)) _ (A.A N).e ?_
  intro z x
  have := (A.A N).e_smul z x
  rw [← m.specializationMap_comp_universalSection N z] at this
  exact this
