module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenLeOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulMemSpanInvariantsSup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_smul_mem_span_invariants_sup :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B] (N : Type)
      [AddCommGroup N] [Module B N] [DistribMulAction Γ N],
      (∀ (g : Γ) (b : B) (x : N), g • (b • x) = (g • b) • (g • x)) → ∀ q : Ideal B, q.IsPrime →
      (Nat.card (q.inertia Γ) : B) ∉ q →
      (∀ g ∈ q.inertia Γ, ∀ x : N, g • x - x ∈ q • (⊤ : Submodule B N)) →
      ∀ x : N, ∃ s : B, s ∉ q ∧
        s • x ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} ⊔ q • (⊤ : Submodule B N) := by
  intro Γ _ _ B _ _ N _ _ _ hsemi q hq hcard htriv x
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨n, c, d, s, hs, hsep⟩ := exists_sum_smul_separating_inertia Γ B q hq

  refine ⟨(Nat.card (q.inertia Γ) : B) * s, fun h => (hq.mem_or_mem h).elim hcard hs, ?_⟩

  have hinv : ∀ j, (∑ g : Γ, g • (c j • x)) ∈ {y : N | ∀ g : Γ, g • y = y} := by
    intro j h
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = ∑ j, d j • ∑ g : Γ, g • (c j • x) := ⟨_, rfl⟩
  have hz : z ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} := by
    rw [hzdef]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hinv j)))
  have hz' : z = ∑ g : Γ, (∑ j, d j * g • c j) • (g • x) := by
    rw [hzdef]
    simp only [Finset.smul_sum, hsemi, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : Nat.card (q.inertia Γ) = (Finset.univ.filter (fun g : Γ => g ∈ q.inertia Γ)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hsumI : ((Nat.card (q.inertia Γ) : B) * s) • x
      = ∑ g : Γ, if g ∈ q.inertia Γ then s • x else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul B, smul_smul]

  have hdiff : z - ((Nat.card (q.inertia Γ) : B) * s) • x ∈ q • (⊤ : Submodule B N) := by
    rw [hz', hsumI, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    by_cases hg : g ∈ q.inertia Γ
    · rw [if_pos hg]
      have e : (∑ j, d j * g • c j) • (g • x) - s • x
          = ((∑ j, d j * g • c j) - s) • (g • x) + s • (g • x - x) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul ((hsep g).1 hg) Submodule.mem_top)
        (Submodule.smul_mem _ s (htriv g hg x))
    · rw [if_neg hg, sub_zero]
      exact Submodule.smul_mem_smul ((hsep g).2 hg) Submodule.mem_top
  have key := Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hdiff)
  rwa [sub_sub_cancel] at key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsumSmulEqOneOfTame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_finsum_smul_eq_one_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B],
      (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) →
        ∃ b : B, ∑ᶠ g : Γ, g • b = 1 := by
  intro Γ _ _ B _ _ htame
  classical
  haveI := Fintype.ofFinite Γ
  let A := FixedPoints.subring B Γ
  haveI : Algebra.IsInvariant A B Γ := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI := Algebra.IsInvariant.isIntegral A B Γ
  have tr_inv : ∀ b : B, ∑ g : Γ, g • b ∈ A := by
    intro b h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • b)
  let T : Ideal A := Ideal.span {t | ∃ b : B, (t : B) = ∑ g : Γ, g • b}
  have hT : ∀ t ∈ T, ∃ b : B, (t : B) = ∑ g : Γ, g • b := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ht
    | zero => exact ⟨0, by simp⟩
    | add t u _ _ htb hub =>
      obtain ⟨b, hb⟩ := htb
      obtain ⟨c, hc⟩ := hub
      exact ⟨b + c, by simp [hb, hc, Finset.sum_add_distrib]⟩
    | smul a t _ htb =>
      obtain ⟨b, hb⟩ := htb
      refine ⟨(a : B) * b, ?_⟩
      simp only [smul_eq_mul, Subring.coe_mul, hb, Finset.mul_sum, smul_mul']
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [a.2 g]
  suffices h1 : (1 : A) ∈ T by
    obtain ⟨b, hb⟩ := hT 1 h1
    exact ⟨b, by rw [finsum_eq_sum_of_fintype, ← hb]; rfl⟩
  by_contra h1
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal T ((Ideal.ne_top_iff_one T).mpr h1)
  have hker : RingHom.ker (algebraMap A B) ≤ m := by
    intro z hz
    have : z = 0 := Subtype.ext hz
    rw [this]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  obtain ⟨n, c, d, s, hs, hsep⟩ := _root_.GlobalTheory.exists_sum_smul_separating_inertia Γ B Q hQ.isPrime
  have trace_mem : ∀ j, ∑ g : Γ, g • c j ∈ Q := by
    intro j
    have hmemT : (⟨∑ g : Γ, g • c j, tr_inv (c j)⟩ : A) ∈ T :=
      Ideal.subset_span ⟨c j, rfl⟩
    have := hTm hmemT
    rw [← hQm, Ideal.mem_comap] at this
    exact this
  have hz : ∑ g : Γ, ∑ j, d j * g • c j ∈ Q := by
    rw [Finset.sum_comm]
    exact Q.sum_mem fun j _ => by
      rw [← Finset.mul_sum]
      exact Q.mul_mem_left _ (trace_mem j)
  have hdiff : ∑ g : Γ, (∑ j, d j * g • c j - if g ∈ Q.inertia Γ then s else 0) ∈ Q := by
    refine Q.sum_mem fun g _ => ?_
    split_ifs with hg
    · exact (hsep g).1 hg
    · simpa using (hsep g).2 hg
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at hdiff
  have hcs := Q.sub_mem hz hdiff
  rw [sub_sub_cancel] at hcs
  rcases hQ.isPrime.mem_or_mem hcs with hc | hc
  · apply htame Q hQ.isPrime
    convert hc using 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · exact hs hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTame
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantTowerAlgebraMapInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubalgebraEqTopOfForallPrimeSmulMemSup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem _root_.GlobalTheory.span_range_algebraMap_eq_top_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → Module.Finite R C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Submodule.span B (Set.range (algebraMap R C)) = ⊤ := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcompat _ htame hin
  classical
  let M : Subalgebra B C := Algebra.adjoin B (Set.range (algebraMap R C))
  have hRM : ∀ r : R, algebraMap R C r ∈ M := fun r => Algebra.subset_adjoin ⟨r, rfl⟩
  letI : Algebra R M := ((algebraMap R C).codRestrict M hRM).toAlgebra
  haveI : IsScalarTower R M C := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite M C := Module.Finite.of_restrictScalars_finite R M C
  have hsmulM : ∀ (m : M) (c : C), m • c = (m : C) * c := fun m c => rfl
  have hsmulB : ∀ (b : B) (c : C), b • c = (algebraMap B M b : C) * c := fun b c => by
    rw [Algebra.smul_def]
    rfl
  let P' : Submodule M C := Submodule.span M {1}
  have hmemP' : ∀ c ∈ M, c ∈ P' := by
    intro c hc
    rw [Submodule.mem_span_singleton]
    exact ⟨⟨c, hc⟩, by rw [hsmulM, _root_.mul_one]⟩
  have hcomp : ∀ (g : Γ) (b : B) (x : C), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hcompat]
  have hin' : ∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ x : C,
      g • x - x ∈ q • (⊤ : Submodule B C) := by
    intro q hq g hg x
    rw [Ideal.smul_top_eq_map]
    exact hin q hq g hg x
  have hloc : ∀ P : Ideal M, P.IsMaximal → (⊤ : Submodule M (C ⧸ P')) ≤ P • ⊤ := by
    intro P hP x _
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P' x
    haveI : P.IsPrime := hP.isPrime
    have hq : (P.comap (algebraMap B M)).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨s, hs, hsc⟩ := _root_.GlobalTheory.exists_smul_mem_span_invariants_sup Γ B C hcomp _ hq
      (htame _ hq) (hin' _ hq) c
    have hsmall : ∀ y ∈ Submodule.span B {y : C | ∀ g : Γ, g • y = y} ⊔
        (P.comap (algebraMap B M)) • (⊤ : Submodule B C),
        (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P')) := by
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [Submodule.Quotient.mk_add]
      refine add_mem ?_ ?_
      · have h1 : y₁ ∈ Subalgebra.toSubmodule M := by
          refine (Submodule.span_le (p := Subalgebra.toSubmodule M)).mpr ?_ hy₁
          intro z hz
          obtain ⟨r, rfl⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := Γ) z hz
          exact hRM r
        rw [(Submodule.Quotient.mk_eq_zero P').mpr (hmemP' _ h1)]
        exact zero_mem _
      · refine Submodule.smul_induction_on
          (p := fun y => (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P'))) hy₂ ?_ ?_
        · intro b hb z _
          rw [show b • z = (algebraMap B M b) • z by rw [hsmulM, hsmulB],
            Submodule.Quotient.mk_smul]
          exact Submodule.smul_mem_smul hb trivial
        · intro z w hz hw
          simp only [Submodule.Quotient.mk_add]
          exact add_mem hz hw
    have hσ : algebraMap B M s ∉ P := hs
    obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hσ
    have hx : (Submodule.Quotient.mk c : C ⧸ P') =
        u • (Submodule.Quotient.mk (s • c) : C ⧸ P') + i • Submodule.Quotient.mk c := by
      rw [show s • c = (algebraMap B M s) • c by rw [hsmulM, hsmulB], Submodule.Quotient.mk_smul,
        smul_smul, ← add_smul, hui, one_smul]
    rw [hx]
    exact add_mem (Submodule.smul_mem _ _ (hsmall _ hsc)) (Submodule.smul_mem_smul hi trivial)
  have hann : Module.annihilator M (C ⧸ P') = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P
      (⊤ : Submodule M (C ⧸ P')) Module.Finite.fg_top (hloc P hP)
    have hrP : r ∈ P := hle (Module.mem_annihilator.mpr fun n => hr n trivial)
    have h1 : (1 : M) ∈ P := by simpa using P.sub_mem hrP hr1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  refine eq_top_iff.mpr fun c _ => ?_
  have h1 : (1 : M) ∈ Module.annihilator M (C ⧸ P') := by
    rw [hann]
    exact Submodule.mem_top
  have hc0 : (Submodule.Quotient.mk c : C ⧸ P') = 0 := by
    have h := Module.mem_annihilator.mp h1 (Submodule.Quotient.mk c)
    rwa [one_smul] at h
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero P').mp hc0)
  rw [hsmulM, _root_.mul_one] at hm
  have hcM : c ∈ Subalgebra.toSubmodule M := hm ▸ m.2
  rw [Algebra.adjoin_eq_span] at hcM
  refine Submodule.span_mono ?_ hcM
  intro z hz
  have hcl : Submonoid.closure (Set.range (algebraMap R C)) ≤
      (algebraMap R C).rangeS.toSubmonoid :=
    Submonoid.closure_le.mpr fun w ⟨r, hr⟩ => ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hcl hz
  exact ⟨r, hr⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantTowerAlgebraMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem mem_smul_ker_of_flat_quotient {B T C : Type} [CommRing B] [AddCommGroup T] [Module B T]
    [AddCommGroup C] [Module B C] [Module.Flat B C] (φ : T →ₗ[B] C) (hφ : Function.Surjective φ)
    (q : Ideal B) (x : LinearMap.ker φ) (hx : (x : T) ∈ q • (⊤ : Submodule B T)) :
    x ∈ q • (⊤ : Submodule B (LinearMap.ker φ)) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat φ hφ (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map φ) (B ⧸ q)
  have h0 : ∀ (M : Type) [AddCommGroup M] [Module B M] (y : M),
      ((1 : B ⧸ q) ⊗ₜ[B] y = 0 ↔ y ∈ q • (⊤ : Submodule B M)) := by
    intro M _ _ y
    rw [← Submodule.Quotient.mk_eq_zero, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk,
      LinearEquiv.map_eq_zero_iff]
  rw [← h0]
  apply hinj
  rw [LinearMap.lTensor_tmul, map_zero, h0]
  exact hx

theorem ideal_eq_bot_of_forall_prime_smul_mem {B T : Type} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal T) (hJ : J.FG)
    (h : ∀ q : Ideal B, q.IsPrime → ∀ x ∈ J, ∃ s : B, s ∉ q ∧
      s • x ∈ q • (J.restrictScalars B)) : J = ⊥ := by
  by_cases hJt : Submodule.annihilator J = ⊤
  · exact Submodule.annihilator_eq_top_iff.1 hJt
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJt
  have hle : J ≤ n • J := by
    intro x hxJ
    obtain ⟨s, hs, hx⟩ := h (n.comap (algebraMap B T)) (Ideal.comap_isPrime _ _) x hxJ
    have hx' : s • x ∈ n • J := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr c hc
        rw [← algebraMap_smul T r c]
        exact Submodule.smul_mem_smul hr hc
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    obtain ⟨t, m, hm, e⟩ := hn.exists_inv (x := algebraMap B T s) hs
    have e' : x = t • (s • x) + m • x := by
      rw [← algebraMap_smul T s x, ← mul_smul, ← add_smul, e, one_smul]
    rw [e']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx') (Submodule.smul_mem_smul hm hxJ)
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n J hJ hle
  have hrJ : r ∈ n := hJn (Submodule.mem_annihilator.2 hrM)
  exfalso
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one]
  have := n.sub_mem hrJ hr
  rwa [sub_sub_cancel] at this

theorem isPushout_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAB hRC heq hnoeth hfAB hfRC hflat hcard hI
  classical
  haveI := Fintype.ofFinite Γ
  haveI : SMulCommClass A Γ B := SMulCommClass.symm _ _ _
  let φ : B ⊗[A] R →ₐ[B] C := Algebra.TensorProduct.lift (Algebra.ofId B C)
    (IsScalarTower.toAlgHom A R C) (fun _ _ => Commute.all _ _)
  have hφ : ∀ (b : B) (r : R), φ (b ⊗ₜ r) = algebraMap B C b * algebraMap R C r := by
    intro b r
    simp [φ, Algebra.ofId_apply]
  have hsurj : Function.Surjective φ := by
    have := span_range_algebraMap_eq_top_of_tame Γ A B R C hAB hRC heq hfRC hcard hI
    have h2 : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← this, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact ⟨1 ⊗ₜ r, by simp [hφ]⟩
    exact LinearMap.range_eq_top.1 h2
  have hR : ∀ (g : Γ) (r : R), g • algebraMap R C r = algebraMap R C r := by
    intro g r
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hequi : ∀ (g : Γ) (x : B ⊗[A] R), φ (g • x) = g • φ x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b r => rw [TensorProduct.smul_tmul', hφ, hφ, smul_mul', heq, hR]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
  have hsl : ∀ (g : Γ) (b : B) (x : B ⊗[A] R), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]
  have htr : ∀ x : B ⊗[A] R, ∃ r : R, ∑ g : Γ, g • x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c r =>
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • c) (by
        intro k
        rw [Finset.smul_sum]
        simp only [← mul_smul]
        exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => g • c))
      refine ⟨a • r, ?_⟩
      simp only [TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, ← ha, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp only [smul_add, Finset.sum_add_distrib, hr, hs, TensorProduct.tmul_add]⟩
  have hinv : ∀ x : B ⊗[A] R, φ x = 0 → (∀ g : Γ, g • x = x) → x = 0 := by
    intro x hx hg
    obtain ⟨b, hb⟩ := exists_finsum_smul_eq_one_of_tame Γ B hcard
    rw [finsum_eq_sum_of_fintype] at hb
    obtain ⟨r, hr⟩ := htr (b • x)
    simp only [hsl, hg] at hr
    rw [← Finset.sum_smul, hb, one_smul] at hr
    rw [hr, hφ, map_one, _root_.one_mul, map_eq_zero_iff _ hRC] at hx
    rw [hr, hx, TensorProduct.tmul_zero]
  have hinert : ∀ q : Ideal B, ∀ g ∈ q.inertia Γ, ∀ x : B ⊗[A] R,
      g • x - x ∈ q • (⊤ : Submodule B (B ⊗[A] R)) := by
    intro q g hg x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      have : g • (c ⊗ₜ[A] r) - c ⊗ₜ[A] r = (g • c - c) • ((1 : B) ⊗ₜ[A] r) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, TensorProduct.sub_tmul]
      rw [this]
      exact Submodule.smul_mem_smul (hg c) Submodule.mem_top
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  let K : Submodule B (B ⊗[A] R) := LinearMap.ker φ.toLinearMap
  have hK : ∀ x, x ∈ K ↔ φ x = 0 := fun x => Iff.rfl
  letI : SMul Γ K := ⟨fun g x => ⟨g • (x : B ⊗[A] R), by
    rw [hK, hequi, (hK _).1 x.2, smul_zero]⟩⟩
  letI : DistribMulAction Γ K :=
    Function.Injective.distribMulAction K.subtype.toAddMonoidHom K.injective_subtype
      (fun _ _ => rfl)
  haveI : IsNoetherianRing (B ⊗[A] R) := by
    haveI : IsNoetherianRing (R ⊗[A] B) := Algebra.FiniteType.isNoetherianRing R _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hker : RingHom.ker φ = ⊥ := by
    refine ideal_eq_bot_of_forall_prime_smul_mem (B := B) _ (IsNoetherian.noetherian _) ?_
    intro q hq x hx
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_span_invariants_sup Γ B K
      (fun g b y => Subtype.ext (hsl g b y)) q hq (hcard q hq)
      (fun g hg y => mem_smul_ker_of_flat_quotient φ.toLinearMap hsurj q _ (hinert q g hg y))
      ⟨x, hx⟩
    refine ⟨s, hs, ?_⟩
    have hbot : Submodule.span B {y : K | ∀ g : Γ, g • y = y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro y hy
      exact Subtype.ext (hinv y y.2 fun g => congrArg Subtype.val (hy g))
    rw [hbot, bot_sup_eq, Submodule.mem_smul_top_iff] at hsx
    exact hsx
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  exact ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj⟩)
    (fun r => (hφ 1 r).trans (by simp))⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantTowerAlgebraMapInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.invariant_tower_isPushout : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  first | exact @GlobalTheory.isPushout_of_tame | exact GlobalTheory.isPushout_of_tame | (intros; apply GlobalTheory.isPushout_of_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfTameDescent
open scoped TensorProduct

namespace GlobalTheory

namespace TameFlat

open TensorProduct

theorem flat_of_retraction {A B R : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R] (e : B →ₗ[A] A) (he : e 1 = 1)
    [Module.Flat B (B ⊗[A] R)] : Module.Flat A R := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro I

  have hmem : ∀ z ∈ I.map (algebraMap A B), ∀ c : B, e (c * z) ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact I.mul_mem_right _ ha
    | zero => intro c; simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add (f := _)]; exact I.add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
  set J : Ideal B := I.map (algebraMap A B)

  let eJ : J →ₗ[A] I := LinearMap.codRestrict (I.restrictScalars A)
    (e ∘ₗ J.subtype.restrictScalars A) (fun z => by simpa using hmem z z.2 1)
  have heJ : eJ ∘ₗ Algebra.idealMap B I = LinearMap.id := by
    ext i
    change e (algebraMap A B (i : A)) = (i : A)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, he, smul_eq_mul, mul_one]

  let Φ : I ⊗[A] R →ₗ[A] J ⊗[B] (B ⊗[A] R) :=
    (AlgebraTensorModule.cancelBaseChange A B B J R).symm.toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.map (Algebra.idealMap B I) LinearMap.id
  let Ψ : J ⊗[B] (B ⊗[A] R) →ₗ[A] I ⊗[A] R :=
    TensorProduct.map eJ LinearMap.id ∘ₗ
      (AlgebraTensorModule.cancelBaseChange A B B J R).toLinearMap.restrictScalars A
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    have : Ψ ∘ₗ Φ = LinearMap.id := by
      apply TensorProduct.ext'
      intro i r
      simp only [Ψ, Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← LinearMap.comp_apply eJ, heJ, LinearMap.id_apply]
    exact congrArg (fun f => f x) this
  have hinc : Function.Injective (LinearMap.rTensor (B ⊗[A] R) J.subtype) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance J

  have hkey : ∀ x, TensorProduct.lid B (B ⊗[A] R) (LinearMap.rTensor (B ⊗[A] R) J.subtype (Φ x)) =
      (1 : B) ⊗ₜ[A] TensorProduct.lid A R (LinearMap.rTensor R I.subtype x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul i r =>
      simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.rTensor_tmul,
        Submodule.subtype_apply, TensorProduct.lid_tmul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change algebraMap A B (i : A) ⊗ₜ[A] r = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  intro x y hxy
  have h1 : Φ x = Φ y := by
    apply hinc
    apply (TensorProduct.lid B (B ⊗[A] R)).injective
    rw [hkey, hkey, hxy]
  rw [← hΨΦ x, ← hΨΦ y, h1]

theorem exists_retraction {Γ A B : Type} [Group Γ] [Finite Γ] [CommRing A] [CommRing B]
    [MulSemiringAction Γ B] [Algebra A B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ]
    (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : ∑ᶠ g : Γ, g • b = 1) :
    ∃ e : B →ₗ[A] A, e 1 = 1 := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [finsum_eq_sum_of_fintype] at hb
  have hfix : ∀ x : B, ∃ a : A, algebraMap A B a = ∑ g : Γ, g • (b * x) := by
    intro x
    apply Algebra.IsInvariant.isInvariant (G := Γ)
    intro h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • (b * x))
  choose f hf using hfix
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply hinj
    rw [map_add (f := _), hf, hf, hf, ← Finset.sum_add_distrib]
    simp_rw [mul_add, smul_add]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, ← Algebra.smul_def, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_smul_comm, smul_comm]
  · show f 1 = 1
    apply hinj
    rw [hf, mul_one, map_one, hb]

end TameFlat

theorem flat_of_tame_descent :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R]
      [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R]
      [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C]
      [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ]
      [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) →
      Function.Injective (algebraMap R C) →
      (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) →
      Algebra.IsPushout A B R C → Module.Flat B C → (∃ b : B, ∑ᶠ g : Γ, g • b = 1) →
      Module.Flat A R := by
  intro Γ _ _ A B R C
  intros
  rename_i hAB _ _ hpo hflat htr
  obtain ⟨b, hb⟩ := htr
  obtain ⟨e, he⟩ := TameFlat.exists_retraction (Γ := Γ) (A := A) hAB b hb
  have : Module.Flat B (B ⊗[A] R) := Module.Flat.of_linearEquiv hpo.out.equiv
  exact TameFlat.flat_of_retraction e he

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemMapKerOfOneTmulEqZeroOfFlat
open scoped TensorProduct

namespace GlobalTheory

theorem mem_map_ker_of_one_tmul_eq_zero_of_flat (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by
  classical
  set I : Ideal B := RingHom.ker (algebraMap B k) with hI
  let f : (B ⧸ I) →ₗ[B] k :=
    Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)
  have hinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0 := by
    apply hinj
    have h1 : f (Ideal.Quotient.mk I 1) = 1 := by
      show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]
    rw [LinearMap.rTensor_tmul, map_zero, h1]
    exact h
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Ideal.smul_top_eq_map] at hq
  exact hq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameDescent

theorem specMap_fromSpec_comp_eq_iff {X : Scheme.{0}} (t : X ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : U ≤ t ⁻¹ᵁ U) {k : CommRingCat.{0}} (a : Γ(X, U) ⟶ k) :
    (Spec.map a ≫ hU.fromSpec) ≫ t = Spec.map a ≫ hU.fromSpec ↔
      ∀ b, a.hom ((t.appLE U U h).hom b - b) = 0 := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec t hU hU h, ← Category.assoc,
    cancel_mono, ← Spec.map_comp, Spec.map_injective.eq_iff]
  simp only [map_sub, sub_eq_zero]
  exact ⟨fun e b => congr(($e).hom b), fun e => CommRingCat.hom_ext (RingHom.ext e)⟩

theorem appLE_sub_mem_map {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by
  let := a.toAlgebra
  let := (p.appLE U W e).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, W) := p.flat_appLE hU hW e
  refine mem_map_ker_of_one_tmul_eq_zero_of_flat Γ(X, U) Γ(Y, W) k _ ?_
  let r : Γ(Y, W) ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l : CommRingCat.of k ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have w : (Spec.map r ≫ hW.fromSpec) ≫ p =
      Spec.map l ≫ Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW e,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct Γ(X, U) k Γ(Y, W)).w.symm
  refine (specMap_fromSpec_comp_eq_iff t hW h r).1 ?_ c
  rw [← pullback.lift_fst _ _ w, Category.assoc, ht]

theorem isPullback_specMap_app {X X' : Scheme.{0}} (π : X ⟶ X') [IsAffineHom π] {V : X'.Opens}
    (hV : IsAffineOpen V) :
    IsPullback (Spec.map (π.app V)) (hV.preimage π).fromSpec hV.fromSpec π :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]) (by simp)

theorem isPullback_of_isPushout_app {X X' Y Y' : Scheme.{0}} (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsAffineHom π] [IsAffineHom φ] (w : φ ≫ p' = p ≫ π)
    (H : ∀ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V → IsAffineOpen W →
      ∀ (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V),
      IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e')) :
    IsPullback φ p p' π := by
  have h : ∀ y : Y', ∃ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
      y ∈ W ∧ W ≤ p' ⁻¹ᵁ V := fun y => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p' y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, hle⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ p' ⁻¹ᵁ V from hx) (p' ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hy, hle⟩
  choose V W hV hW hy hle using h
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y => Spec Γ(Y', W y))
    (fun y => (hW y).fromSpec) (fun y => ⟨y, by
      have : y ∈ Set.range (hW y).fromSpec := by
        rw [IsAffineOpen.range_fromSpec]; exact hy y
      exact this⟩)
  refine Scheme.isPullback_of_openCover φ p p' π 𝒰 fun y => ?_
  have e' : φ ⁻¹ᵁ W y ≤ p ⁻¹ᵁ π ⁻¹ᵁ V y := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
    exact φ.preimage_mono (hle y)
  have H1 := isPullback_specMap_app φ (hW y)
  have H2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (H _ _ (hV y) (hW y) (hle y) e')).paste_vert (isPullback_specMap_app π (hV y)).flip.flip
  rw [IsAffineOpen.SpecMap_appLE_fromSpec p _ ((hW y).preimage φ),
    IsAffineOpen.SpecMap_appLE_fromSpec p' _ (hW y)] at H2
  refine H2.of_iso H1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  · exact (Category.comp_id _).trans (H1.flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact (H1.flip.isoPullback_hom_fst).symm

theorem isPushout_and_flat {Γ : Type} [Group Γ] [Finite Γ] {X X' Y Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsFinite π] [IsFinite φ] [Flat p]
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hπ' : ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
      (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (π.app V).hom)
    (hφ : ∀ g, (τ g).asIso.hom ≫ φ = φ)
    (hφ' : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (w : φ ≫ p' = p ≫ π) (hp : ∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x →
      pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x)
    (V : X'.Opens) (W : Y'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V) :
    IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e') ∧
      (p'.appLE V W e).hom.Flat := by
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hU' : IsAffineOpen (φ ⁻¹ᵁ W) := hW.preimage φ
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ W
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  let := (π.app V).hom.toAlgebra
  let := (φ.app W).hom.toAlgebra
  let := (p'.appLE V W e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (p'.appLE V W e ≫ φ.app W).hom.toAlgebra
  have sq : p'.appLE V W e ≫ φ.app W = π.app V ≫ p.appLE _ _ e' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w]
  have : IsScalarTower Γ(X', V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) :=
    .of_algebraMap_eq' congr(($sq).hom)
  have : SMulCommClass Γ Γ(X', V) Γ(X, π ⁻¹ᵁ V) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(X', V) Γ(X, π ⁻¹ᵁ V) a = algebraMap _ _ a :=
      (isInvariantSection_app ρ π hπ V a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : SMulCommClass Γ Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) a = algebraMap _ _ a :=
      (isInvariantSection_app τ φ hφ W a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ := ⟨fun s hs ↦
    (hπ' V).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩
  have : Algebra.IsInvariant Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    (hφ' W).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (τ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst' _) s = s from hs g⁻¹)⟩
  have heq : ∀ (g : Γ) (b : Γ(X, π ⁻¹ᵁ V)), g • algebraMap _ Γ(Y, φ ⁻¹ᵁ W) b =
      algebraMap _ Γ(Y, φ ⁻¹ᵁ W) (g • b) := fun g b => by
    change (τ g⁻¹).asIso.hom.appLE _ _ (hst' _) (p.appLE _ _ e' b) =
      p.appLE _ _ e' ((ρ g⁻¹).asIso.hom.appLE _ _ (hst _) b)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hflat : Module.Flat Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) := p.flat_appLE hU hU' e'
  have key : ∀ q : Ideal Γ(X, π ⁻¹ᵁ V), q.IsPrime → ((Nat.card (q.inertia Γ) : Γ(X, π ⁻¹ᵁ V)) ∉ q) ∧
      ∀ g ∈ q.inertia Γ, ∀ c : Γ(Y, φ ⁻¹ᵁ W), g • c - c ∈ q.map (algebraMap _ Γ(Y, φ ⁻¹ᵁ W)) := by
    intro q hq
    let k := AlgebraicClosure q.ResidueField
    let a : Γ(X, π ⁻¹ᵁ V) →+* k := (algebraMap q.ResidueField k).comp (algebraMap _ _)
    have ha : ∀ b, a b = 0 ↔ b ∈ q := fun b => by
      simp [a]
    have hker : RingHom.ker a = q := Ideal.ext ha
    let x : Sp k ⟶ X := Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec
    have hx : ∀ g, x ≫ (ρ g⁻¹).asIso.hom = x ↔ g ∈ q.inertia Γ := fun g =>
      (specMap_fromSpec_comp_eq_iff _ hU (hst _) _).trans (forall_congr' fun b => ha _)
    refine ⟨fun h => htame k x ?_, fun g hg c => ?_⟩
    · rw [← Nat.card_congr ((Equiv.inv Γ).subtypeEquiv (p := fun g => g ∈ q.inertia Γ)
        (q := fun g => x ≫ (ρ g).asIso.hom = x) fun g => (hx g).symm), ← map_natCast a]
      exact (ha _).2 h
    · rw [← hker]
      exact appLE_sub_mem_map p _ hU hU' e' (hst' _) a (hfix k x _ ((hx g).2 hg)) c
  have hpo : Algebra.IsPushout Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) :=
    GlobalTheory.T.invariant_tower_isPushout Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq
      (IsLocallyNoetherian.component_noetherian ⟨W, hW⟩) (π.finite_app V hV) (φ.finite_app W hW)
      hflat (fun q hq => (key q hq).1) (fun q hq => (key q hq).2)
  refine ⟨CommRingCat.isPushout_iff_isPushout.2 hpo.symm, ?_⟩
  exact flat_of_tame_descent Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq hpo hflat
    (exists_finsum_smul_eq_one_of_tame Γ _ fun q hq => (key q hq).1)

theorem isPullback_flat_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  intro Γ _ _ X X' Y Y' _ ρ τ π φ p p' hπ hφ w hp _ _ _ htame hfix
  obtain ⟨_, _, -⟩ := GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ Y Y' τ φ hφ X' p' (by rw [w]; infer_instance)
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p'
  have H := isPushout_and_flat ρ τ π φ p p' hπ.2.1 hπ.2.2 hφ.2.1 hφ.2.2 w hp htame hfix
  refine ⟨isPullback_of_isPushout_app π φ p p' w fun V W hV hW e e' => (H V W hV hW e e').1,
    ⟨fun {V} hV {W} hW e => (H V W hV hW e ?_).2⟩, inferInstance⟩
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact φ.preimage_mono e

end GlobalTheory.TameDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_flat_of_tame_alt : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  first | exact @GlobalTheory.TameDescent.isPullback_flat_of_tame | exact GlobalTheory.TameDescent.isPullback_flat_of_tame | (intros; apply GlobalTheory.TameDescent.isPullback_flat_of_tame <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_smooth_descent_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (s : X ⟶ Sp R) (τ : Γ →* Aut G.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (G.hom ≫ s) → Smooth G.hom → (∀ g, (τ g).asIso.hom ≫ G.hom = G.hom ≫ (ρ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst G.hom x ≫ (τ g).asIso.hom = pullback.fst G.hom x) → ∃ (G' : Over X') (φ : G.left ⟶ G'.left), IsPullback φ G.hom G'.hom π ∧ Smooth G'.hom ∧ ∀ g, (τ g).asIso.hom ≫ φ = φ := by
  intro Γ _ _ R _ X X' _ ρ π G s τ hπ hfin hqp hsm hτ hstab hfib
  have hsepG : G.left.IsSeparated := by
    obtain ⟨N, i, hi, -, hcomp⟩ := hqp
    haveI := isProper_str R N
    haveI : IsSeparated (G.hom ≫ s) := by rw [← hcomp]; infer_instance
    constructor
    rw [show terminal.from G.left = (G.hom ≫ s) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨Y', φ, hφ⟩ := exists_quotient_of_finite_group Γ G.left τ (fun y => by
    obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver R G.left (G.hom ≫ s) hqp
      (Set.range fun g => (τ g).asIso.hom y) ⊤ (Set.finite_range _) (fun _ _ => trivial)
    exact ⟨V, hV, fun g => hF ⟨g, rfl⟩⟩)
  obtain ⟨p', hp', -⟩ := quotient_existsUnique_comp_eq Γ G.left Y' τ φ hφ X' (G.hom ≫ π)
    (fun g => by rw [← Category.assoc, hτ g, Category.assoc, hπ.2.1 g])
  obtain ⟨hpb, hflat, hlft⟩ := GlobalTheory.T.isPullback_flat_of_tame_alt Γ X X' G.left Y' ρ τ π φ G.hom p' hπ hφ hp' hτ hfin
    inferInstance inferInstance hstab hfib
  have hsurj : Surjective π := (quotient_isIntegral_surjective_orbits Γ X X' ρ π hπ).2.1
  haveI : LocallyOfFinitePresentation p' := inferInstance
  exact ⟨Over.mk p', φ, hpb,
    smooth_of_isPullback_of_surjective_of_flat X X' G.left Y' π φ G.hom p' hpb hsurj hflat
      inferInstance hsm, fun g => hφ.2.1 g⟩

end GlobalTheory
