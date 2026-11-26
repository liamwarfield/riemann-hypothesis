module

public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AdmissibleLatticesCommensurable

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IsLocallyConstantTorsionPushOfContinuous
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.isLocallyConstant_torsion_push_of_continuous :
    ∀ {G O LL Q : Type} [TopologicalSpace G] [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [TopologicalSpace LL]
      [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup Q] [Module O Q] {a n : ℕ}
      (Y : Submodule O (Fin a → Fin n → LL)) (φ : ↥Y →ₗ[O] Q) (u : G → Fin a → Fin n → LL) (hu : ∀ g, u g ∈ Y) (c : O),
      IsOpen (Set.range (algebraMap O LL)) → Continuous u → c ≠ 0 → (∀ y, c • φ y = 0) →
      IsLocallyConstant fun g => φ ⟨u g, hu g⟩ := by
  classical
  intro G O LL Q _ _ _ _ _ _ _ _ _ _ _ a n Y φ u hu c hopen hcont hc hkill
  let Lmap : (Fin a → Fin n → O) →ₗ[O] (Fin a → Fin n → LL) :=
    ((Algebra.linearMap O LL).compLeft (Fin n)).compLeft (Fin a)
  let Λ := LinearMap.range Lmap
  have hΛ : Λ.FG := by
    show (LinearMap.range Lmap).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  obtain ⟨μ, hμ0, hμ⟩ := admissible_lattices_commensurable (LL := LL) Λ Y hΛ c hc
  have hμL : algebraMap O LL μ ≠ 0 := fun h =>
    hμ0 ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  let W : Set LL := (fun x => (algebraMap O LL μ)⁻¹ * x) ⁻¹' Set.range (algebraMap O LL)
  have hW : IsOpen W := hopen.preimage (continuous_const.mul continuous_id)
  let U : Set (Fin a → Fin n → LL) := {v | ∀ j m, v j m ∈ W}
  have hU : IsOpen U := by
    have hUe : U = ⋂ j, ⋂ m, (fun v : Fin a → Fin n → LL => v j m) ⁻¹' W := by
      ext v; simp [U]
    rw [hUe]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun m =>
      hW.preimage ((continuous_apply m).comp (continuous_apply j))
  have key : ∀ v ∈ Y, v ∈ U → ∃ y ∈ Y, v = c • y := by
    intro v hvY hvU
    simp only [U, W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range] at hvU
    choose x hx using hvU
    have hxΛ : Lmap x ∈ Λ := LinearMap.mem_range_self _ _
    have hmul : μ • Lmap x = v := by
      funext j m
      show μ • algebraMap O LL (x j m) = v j m
      rw [Algebra.smul_def, hx j m, ← mul_assoc, mul_inv_cancel₀ hμL, one_mul]
    obtain ⟨y, hy, hyeq⟩ := hμ _ hxΛ (hmul ▸ hvY)
    exact ⟨y, hy, hmul ▸ hyeq⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have hnhds : {g | u g - u g0 ∈ U} ∈ nhds g0 := by
    refine (hU.preimage (hcont.sub continuous_const)).mem_nhds ?_
    intro j m
    refine ⟨0, ?_⟩
    simp
  filter_upwards [hnhds] with g hg
  obtain ⟨y, hy, hyeq⟩ := key _ (Y.sub_mem (hu g) (hu g0)) hg
  have hsplit : (⟨u g, hu g⟩ : Y) = ⟨u g0, hu g0⟩ + c • ⟨y, hy⟩ := by
    ext1
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [← hyeq]
    abel
  rw [hsplit, map_add (f := _), map_smul, hkill, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsPowUniformizerSmulEqZeroQuotientLattice
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_pow_uniformizer_smul_eq_zero_quotient_lattice :
    ∀ {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      (lam : O), Irreducible lam → ∀ {k : ℕ} {Y : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
      (φ : Y →ₗ[O] ((Fin k → LL) ⧸ stdG O LL k)), ∃ a : ℕ, ∀ y, lam ^ a • φ y = 0 := by
  classical
  intro O LL _ _ _ _ _ _ lam hlam k Y _ _ _ φ
  have hz : ∀ z : LL, ∃ a : ℕ, ∃ r : O, algebraMap O LL r = lam ^ a • z := by
    intro z
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) z
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hlam
    refine ⟨m, r * ↑u⁻¹, ?_⟩
    have hU : algebraMap O LL ↑u⁻¹ * algebraMap O LL ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hU0 : algebraMap O LL ↑u ≠ 0 := right_ne_zero_of_mul_eq_one hU
    have hinv : algebraMap O LL ↑u⁻¹ = (algebraMap O LL ↑u)⁻¹ := eq_inv_of_mul_eq_one_left hU
    have hL0 : algebraMap O LL (lam ^ m) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ fun h => hlam.ne_zero ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
    rw [Algebra.smul_def, map_mul, map_mul, hinv]
    field_simp
  have hq : ∀ x : (Fin k → LL) ⧸ stdG O LL k, ∃ a : ℕ, lam ^ a • x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    choose a r hr using fun i => hz (v i)
    refine ⟨∑ i, a i, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, stdG, LinearMap.mem_range]
    refine ⟨fun i => lam ^ (∑ j, a j - a i) * r i, funext fun i => ?_⟩
    have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    show algebraMap O LL (lam ^ (∑ j, a j - a i) * r i) = lam ^ (∑ j, a j) • v i
    rw [map_mul, hr i, ← Algebra.smul_def, smul_smul, pow_sub_mul_pow lam hle]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := Y)
  choose a ha using fun y => hq (φ y)
  refine ⟨∑ y ∈ s, a y, fun y => ?_⟩
  have hmem : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    rw [← pow_sub_mul_pow lam (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hx), mul_smul, ha x,
      smul_zero]
  | zero => rw [map_zero, smul_zero]
  | add x z _ _ h1 h2 => rw [map_add (f := _), smul_add, h1, h2, add_zero]
  | smul c x _ h => rw [map_smul, smul_comm, h, smul_zero]
end

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_cocycle_torsion_of_hasPres :
    ∀ {G O LL : Type} [Group G] [TopologicalSpace G] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
      [TopologicalSpace LL] [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] (hinj : Function.Injective (algebraMap O LL))
      (lam : O) {Xs : Type} {n k : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (M : G →* Matrix (Fin k) (Fin k) O)
      (f : G → (Fin k → LL) ⧸ stdG O LL k), Irreducible lam → IsOpen (Set.range (algebraMap O LL)) →
      (∀ x, Continuous fun g => (N x g).map (algebraMap O LL)) →
      HasPres LL N (Q := (Fin k → LL) ⧸ stdG O LL k) (fun g => actD (stdLatG hinj M) g) f →
      ∃ a : ℕ, f ∈ divisibleCocycles (stdLatG hinj M) ∧ ∀ g, lam ^ a • f g = 0 := by
  intro G O LL _ _ _ _ _ _ _ _ _ _ hinj lam Xs n k N M f hlam hopen hN hP
  obtain ⟨m, x, E, Y, hYfg, hst, hE, φ, hφ, hf⟩ := hP
  haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hYfg
  obtain ⟨e, he⟩ := exists_pow_uniformizer_smul_eq_zero_quotient_lattice lam hlam φ
  have hmul : ∀ g h (v : Fin m → Fin n → LL), actN LL (fun j => N (x j)) (g * h) v =
      actN LL (fun j => N (x j)) g (actN LL (fun j => N (x j)) h v) := by
    intro g h v
    funext j
    simp only [actN, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]
  have hsub : ∀ g (v w : Fin m → Fin n → LL), actN LL (fun j => N (x j)) g (v - w) =
      actN LL (fun j => N (x j)) g v - actN LL (fun j => N (x j)) g w := by
    intro g v w
    funext j
    simp only [actN, Pi.sub_apply, Matrix.mulVec_sub]
  have hfun : f = fun g => φ ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩ := funext hf
  refine ⟨e, ⟨?_, fun g h => ?_⟩, fun g => by rw [hf g]; exact he _⟩
  · rw [hfun]
    refine isLocallyConstant_torsion_push_of_continuous Y φ _ hE (lam ^ e) hopen ?_ (pow_ne_zero _ hlam.ne_zero) he
    exact (continuous_pi fun j => (hN (x j)).matrix_mulVec continuous_const).sub continuous_const
  · have hsplit : (⟨actN LL (fun j => N (x j)) (g * h) E - E, hE (g * h)⟩ : Y) =
        ⟨actN LL (fun j => N (x j)) g ↑(⟨actN LL (fun j => N (x j)) h E - E, hE h⟩ : Y),
          hst g _ (hE h)⟩ + ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, hmul, hsub]
      abel
    rw [hf, hf, hf, hsplit, map_add (f := _), hφ]
    exact add_comm _ _
