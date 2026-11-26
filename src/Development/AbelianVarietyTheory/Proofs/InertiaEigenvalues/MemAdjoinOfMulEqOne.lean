module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
noncomputable section

namespace GlobalTheory.UnitLemma.UnitBase

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  obtain ⟨p, hp, hpt⟩ := ht
  have e : aeval t p = 0 := hpt
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at e
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at e
    simp at e
    have : t = 0 := by simpa using congrArg (t * ·) e
    rw [this]; exact Subalgebra.zero_mem _
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at e
  have hts : t * s = 1 := by rw [mul_comm]; exact h
  have h1 : t ^ (k + 1) * s ^ k = t := by
    rw [pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]
  have h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc]
    congr 1
    rw [show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc,
      ← mul_pow, hts, one_pow, one_mul]
  have e2 := congrArg (· * s ^ k) e
  simp only [add_mul, zero_mul, Finset.sum_mul] at e2
  rw [Finset.sum_congr rfl h2, h1] at e2
  have key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i) := by
    linear_combination e2
  rw [key]
  exact Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)

theorem exists_isUnit_add_mul_twist {R : Type} [CommRing R] (τ : R ≃+* R) (hτ : ∀ y, τ (τ y) = y)
    (a : R) (ha : IsUnit a) (hfin : {M : Ideal R | M.IsMaximal}.Finite)
    (x : R) (hx : IsUnit (τ x - x)) : ∃ y : R, IsUnit (y + a * τ y) := by
  classical
  haveI : Finite {M : Ideal R // M.IsMaximal} := hfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {M : Ideal R // M.IsMaximal}
  let pt : {M : Ideal R // M.IsMaximal} → {M : Ideal R // M.IsMaximal} := fun M =>
    ⟨M.1.comap (τ : R →+* R), by haveI := M.2; exact Ideal.comap_isMaximal_of_surjective _ τ.surjective⟩
  have mem_pt : ∀ M z, z ∈ (pt M).1 ↔ τ z ∈ M.1 := fun M z => Iff.rfl
  have pt_pt : ∀ M, pt (pt M) = M := by
    intro M; apply Subtype.ext; ext z; rw [mem_pt, mem_pt, hτ]
  let t : {M : Ideal R // M.IsMaximal} → R := fun M =>
    if pt M = M then (if 1 + a ∈ M.1 then x else 1) else if e M < e (pt M) then 1 else 0
  have hcop : Pairwise (Function.onFun IsCoprime fun M : {M : Ideal R // M.IsMaximal} => M.1) := by
    intro M N hne
    haveI := M.2; haveI := N.2
    exact Ideal.isCoprime_of_isMaximal (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun M => Ideal.Quotient.mk M.1 (t M))
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : ∀ M : {M : Ideal R // M.IsMaximal}, y - t M ∈ M.1 := by
    intro M
    have := congrFun hq M
    rw [Ideal.quotientInfToPiQuotient_mk'] at this
    exact Ideal.Quotient.eq.1 this
  refine ⟨y, ?_⟩
  by_contra hnu
  obtain ⟨M0, hM0, hyM⟩ := exists_max_ideal_of_mem_nonunits hnu
  set M : {M : Ideal R // M.IsMaximal} := ⟨M0, hM0⟩ with hMdef
  have hyM' : y + a * τ y ∈ M.1 := hyM
  have hne1 : (1 : R) ∉ M.1 := fun h => hM0.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hunit : ∀ {u : R}, IsUnit u → u ∉ M.1 := fun hu h => hM0.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  by_cases hfix : pt M = M
  · have hτM : ∀ z, z ∈ M.1 → τ z ∈ M.1 := by
      intro z hz; rw [← mem_pt, hfix]; exact hz
    have hd := hy M
    have ht : t M + a * τ (t M) ∈ M.1 := by
      have : t M + a * τ (t M) = (y + a * τ y) - (y - t M) - a * τ (y - t M) := by
        rw [map_sub]; ring
      rw [this]
      exact M.1.sub_mem (M.1.sub_mem hyM' hd) (M.1.mul_mem_left _ (hτM _ hd))
    by_cases h1a : 1 + a ∈ M.1
    · have htx : t M = x := by simp only [t, if_pos hfix, if_pos h1a]
      rw [htx] at ht
      have : a * (τ x - x) ∈ M.1 := by
        have : a * (τ x - x) = (x + a * τ x) - x * (1 + a) := by ring
        rw [this]; exact M.1.sub_mem ht (M.1.mul_mem_left _ h1a)
      exact hunit (ha.mul hx) this
    · have ht1 : t M = 1 := by simp only [t, if_pos hfix, if_neg h1a]
      rw [ht1, map_one, mul_one, add_comm] at ht
      exact h1a (by rwa [add_comm])
  · have hfix' : pt (pt M) ≠ pt M := by rw [pt_pt]; exact Ne.symm hfix
    by_cases hlt : e M < e (pt M)
    · have ht1 : t M = 1 := by simp only [t, if_neg hfix, if_pos hlt]
      have hlt' : ¬ e (pt M) < e (pt (pt M)) := by rw [pt_pt]; exact not_lt.2 hlt.le
      have ht0 : t (pt M) = 0 := by simp only [t, if_neg hfix', if_neg hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht1] at h1
      rw [ht0, sub_zero, mem_pt] at h2
      have : (1 : R) = (y + a * τ y) - (y - 1) - a * τ y := by ring
      exact hne1 (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))
    · have ht0 : t M = 0 := by simp only [t, if_neg hfix, if_neg hlt]
      have hne : e (pt M) ≠ e M := fun h => hfix (e.injective h)
      have hlt' : e (pt M) < e (pt (pt M)) := by
        rw [pt_pt]; exact lt_of_le_of_ne (not_lt.1 hlt) hne
      have ht1 : t (pt M) = 1 := by simp only [t, if_neg hfix', if_pos hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht0, sub_zero] at h1
      rw [ht1, mem_pt, map_sub, map_one] at h2
      have : a = (y + a * τ y) - y - a * (τ y - 1) := by ring
      exact hunit ha (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))

def cO (K : UQ) : K.O →+* K.O where
  toFun x := Classical.choose (K.c_int x)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x * y)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x + y)), map_add (f := _), map_add (f := _), map_add (f := _),
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]

theorem algebraMap_cO (K : UQ) (x : K.O) : algebraMap K.O K.E (cO K x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm

theorem σ_algebraMap_O {K : UQ} (B : InvAlg K) (x : K.O) :
    B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A (cO K x) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← algebraMap_cO,
    ← IsScalarTower.algebraMap_apply]

theorem isIntegral_σ {K : UQ} (B : InvAlg K) {y : B.A} (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (cO K), hp.map _, ?_⟩
  have hc : (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) = (algebraMap K.O B.A).comp (cO K) := by
    ext x; exact σ_algebraMap_O B x
  have := congrArg (B.σ : B.A →+* B.A) hpy
  rw [map_zero, Polynomial.hom_eval₂, hc] at this
  rw [Polynomial.eval₂_map]; exact this

theorem σ_mem_adjoin {K : UQ} (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (hint : IsIntegral K.O B.g)
    {y : B.A} (hy : y ∈ Algebra.adjoin K.O {B.g}) : B.σ y ∈ Algebra.adjoin K.O {B.g} := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact mem_adjoin_of_mul_eq_one' hg (isIntegral_σ B hint)
  | algebraMap r => rw [σ_algebraMap_O]; exact Subalgebra.algebraMap_mem _ _
  | add x z _ _ hx hz => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hz
  | mul x z _ _ hx hz => rw [map_mul]; exact Subalgebra.mul_mem _ hx hz

theorem maximal_finite {K : UQ} (B : InvAlg K) (hint : IsIntegral K.O B.g) :
    {M : Ideal (Algebra.adjoin K.O {B.g}) | M.IsMaximal}.Finite := by
  haveI : Module.Finite K.O (Algebra.adjoin K.O {B.g}) := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  refine (Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal K.O)).subset ?_
  intro M hM
  have hM' : M.IsMaximal := hM
  letI : M.IsMaximal := hM'
  have hc : (M.comap (algebraMap K.O (Algebra.adjoin K.O {B.g}))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap K.O (Algebra.adjoin K.O {B.g}))
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) M
  exact ⟨hM'.isPrime, ⟨(IsLocalRing.eq_maximalIdeal hc).symm⟩⟩

theorem exists_unit_base : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  intro K B hg _ hint ε hε
  set R := Algebra.adjoin K.O {B.g} with hR
  have hσR : ∀ y : R, B.σ (y : B.A) ∈ R := fun y => σ_mem_adjoin B hg hint y.2
  let τ : R ≃+* R :=
    { toFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      invFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      left_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      right_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      map_mul' := fun x y => Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
      map_add' := fun x y => Subtype.ext (map_add B.σ (x : B.A) (y : B.A)) }
  have hτc : ∀ y : R, ((τ y : R) : B.A) = B.σ y := fun y => rfl
  have hτ : ∀ y, τ (τ y) = y := fun y => Subtype.ext (B.σ_σ (y : B.A))

  obtain ⟨ε', hε'c, hε'u, hεε, hσε⟩ : ∃ ε' : R, (ε' : B.A) = ε ∧ IsUnit ε' ∧ ε * ε = 1 ∧ B.σ ε = ε := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, isUnit_one, by simp, by simp⟩
    · exact ⟨-1, by simp, isUnit_one.neg, by simp, by simp⟩

  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let h' : R := τ g'
  have hgh : g' * h' = 1 := Subtype.ext hg
  have hh'u : IsUnit h' := ⟨⟨h', g', by rw [mul_comm]; exact hgh, hgh⟩, rfl⟩

  obtain ⟨x0, y0, hxy, hxy0⟩ := K.c_res
  have hcx : cO K x0 = y0 := IsFractionRing.injective K.O K.E (by rw [algebraMap_cO, hxy])
  have hx : IsUnit (τ (algebraMap K.O R x0) - algebraMap K.O R x0) := by
    have hu : IsUnit (y0 - x0) := by
      have : IsUnit (x0 - y0) := by
        by_contra hn; exact hxy0 ((IsLocalRing.mem_maximalIdeal _).2 hn)
      simpa [neg_sub] using this.neg
    have : τ (algebraMap K.O R x0) - algebraMap K.O R x0 = algebraMap K.O R (y0 - x0) := by
      apply Subtype.ext
      simp only [hτc, Subalgebra.coe_sub, Subalgebra.coe_algebraMap, σ_algebraMap_O, hcx, map_sub]
    rw [this]; exact hu.map _
  obtain ⟨y, hy⟩ := exists_isUnit_add_mul_twist τ hτ (ε' * h') (hε'u.mul hh'u) (maximal_finite B hint) _ hx
  refine ⟨Units.map (R.val : R →* B.A) hy.unit, ?_, ?_, ?_⟩
  · have hc : ((Units.map (R.val : R →* B.A) hy.unit : B.Aˣ) : B.A) = (y : B.A) + ε * B.σ B.g * B.σ y := by
      simp [Units.coe_map, IsUnit.unit_spec, hε'c, hτc, h', g', mul_assoc]
    rw [hc, map_add (f := _), map_mul, map_mul, hσε, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ (y : B.A)) * ε * ε) * hg - B.σ (y : B.A) * hεε
  · simp only [Units.coe_map]; exact (hy.unit : R).2
  · rw [← map_inv]; simp only [Units.coe_map]; exact ((hy.unit⁻¹ : Rˣ) : R).2

end GlobalTheory.UnitLemma.UnitBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigmaStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.UnitBase.exists_unit_base | exact GlobalTheory.UnitLemma.UnitBase.exists_unit_base | (intros; apply GlobalTheory.UnitLemma.UnitBase.exists_unit_base <;> assumption)
end
end

namespace GlobalTheory.UnitLemma.TwistUnit

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  exact GlobalTheory.UnitLemma.UnitBase.mem_adjoin_of_mul_eq_one' h ht

theorem adjoin_stab {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)

variable {K : UQ}

theorem trace_σ (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  let b := Module.Free.chooseBasis K.E B.A
  have hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y := by
    intro e y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b) := by
    refine b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro m hm
      have : B.σ m = 0 := hm
      simpa using this
    · intro r m
      show B.σ (K.c.symm r • m) = r • B.σ m
      rw [hsm, RingEquiv.apply_symm_apply]
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b)) := by
    intro y _
    have h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hsm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => by
    simp only [b', Module.Basis.mk_apply]
    rfl
  have hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsm, hb']
    rw [h1, b'.repr_sum_self]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hb', ← map_mul, hrepr]

theorem mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := K.c_int a
    refine ⟨b, ?_⟩
    rw [← hb, ha, K.c_c]
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, hb.symm⟩

theorem trace_σ_mem (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by
  rw [trace_σ, mem_range_c]

theorem twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs hi ε hε
  obtain ⟨β₀, hβ, hb1, hb2⟩ := GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma K B hg hs hi ε hε
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A,
      ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L hL w
    have s1 := adjoin_stab L hL hb1
    have s2 := adjoin_stab L hL hb2
    constructor
    · intro h y hy
      have := h _ (s2 y hy)
      have e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w := by
        have := β₀.mul_inv
        linear_combination (↑x * y * B.σ w) * this
      rwa [e] at this
    · intro h y hy
      have := h _ (s1 y hy)
      rwa [show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring] at this
  have hX' : ∀ (L : Submodule K.O B.A) (w : B.A),
      ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L w
    refine forall₂_congr fun y _ => ?_
    rw [← trace_σ_mem B]
    rw [show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by
      rw [map_mul, map_mul, hx, B.σ_σ]; ring]
  have hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔
      T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b),
      show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  have hgg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hg
  have hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g} := mem_adjoin_of_mul_eq_one hgg hi
  ext L
  simp only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, Units.val_mul, ← hT, ← hR]
  constructor
  · rintro ⟨hLat, hU⟩
    have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
      intro y hy
      rw [hU]
      intro y' hy'
      rw [hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by
        linear_combination ((β₀ : B.A) * x * y * B.σ y') * hg]
      exact (hU y').1 hy' y hy
    have h2 : ∀ y ∈ L, B.g * y ∈ L := adjoin_stab L h1 hgad
    refine ⟨hLat, h2, fun y => ?_⟩
    rw [hX' L y, ← hstab L h2, ← hU]
  · rintro ⟨hLat, h2, hXc⟩
    refine ⟨hLat, fun z => ?_⟩
    rw [hstab L h2, ← hX', ← hXc]

end GlobalTheory.UnitLemma.TwistUnit
