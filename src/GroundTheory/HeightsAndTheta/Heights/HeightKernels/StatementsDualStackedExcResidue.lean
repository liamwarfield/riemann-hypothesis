module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointResidue

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

def IsExcResidueData {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) {k : Type} [Field k]
    (α : T → k) (M : T → Fin i → k) : Prop :=
  ∃ (ρ : 𝓞 K →+* k) (ρ' : dualLattice F' →+ k) (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ ∧ Function.Surjective ρ' ∧ Function.Surjective σ ∧
    (∀ φ : dualLattice F', ρ' φ = 0 ↔ (φ : Fin i → K) ∈ dualLattice F) ∧
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F'),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → ρ' ψ = ρ μ * ρ' φ) ∧
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) ∧
    (∀ t, α t = ρ' (b' t)) ∧ ∀ t, M t = σ (b t)

def DualStackedExcResidueExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
      IsExcResidueData b b' α M ∧ Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def DualStackedExcBaseLe.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      stackedBase b' a ≤ linPrime α M

def DualStackedExcLinPrimeLe.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      ∀ P : Ideal (MRing (stackedBlocks T)), P.IsPrime → stackedBase b' a ≤ P → ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant P →
        linPrime α M ≤ P

namespace DualStackedExcResidueExample

open DualTopSimpleSubExample DualStackedExcExample

end DualStackedExcResidueExample

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def IsExcCoords {K : Type} [Field K] [NumberField K] {i : ℕ} (F F' : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) {k : Type} [Field k]
    (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) {m : ℕ} (g : Fin m → Fin i → K) (α : T → k)
    (M : T → Fin (m + 1) → k) : Prop :=
  Function.Surjective ρ ∧ ρ π = 0 ∧ y₀ ∈ F.lattice ∧ (∀ j, g j ∈ F'.lattice) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) ∧
      ρ c = α t) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ y₀ ∧ ρ c = M t 0) ∧
    (∀ t j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ g j ∧ ρ c = M t j.succ) ∧
    (∃ t, α t ≠ 0) ∧ (∃ t, M t 0 ≠ 0) ∧
    (∀ c : 𝓞 K, ρ c = 0 → ∀ φ ∈ dualLattice F', algebraMap (𝓞 K) K c • φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F', ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) →
      ρ c = 0 → φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F, (∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ y₀ → ρ c = 0) →
      (∀ j, ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ g j → ρ c = 0) →
      φ ∈ Submodule.span ℤ {ψ | ∃ c : 𝓞 K, ρ c = 0 ∧ ∃ χ ∈ dualLattice F, ψ = algebraMap (𝓞 K) K c • χ})

def DualStackedExcCoords.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ (k : Type) (_ : Field k) (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M

def DualStackedExcBase.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      stackedBase b' a ≤ linPrime α M

def DualStackedExcChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ N : ℕ, ∀ e ∈ linPrime α M,
        (graphFirst v * graphSecond u) ^ N * e ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

namespace DualStackedExcChartExample

open DualTopSimpleSubExample

end DualStackedExcChartExample

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointMultiplicityChart

theorem length_localizedModule_quotient {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e := (IsLocalizedModule.linearEquiv p.primeCompl
    (I.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p)))
    (LocalizedModule.mkLinearMap p.primeCompl (R ⧸ I))).restrictScalars (Localization.AtPrime p)
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ (Ideal.localized'_eq_map _ _ I)).length_eq

theorem length_quotient_of_surjective {A N : Type*} [CommRing A] [CommRing N] (Φ : A →+* N)
    (hΦ : Function.Surjective Φ) (J : Ideal A) (hJ : RingHom.ker Φ ≤ J) :
    Module.length A (A ⧸ J) = Module.length N (N ⧸ J.map Φ) := by
  let _ := Φ.toAlgebra
  have hs : Function.Surjective (algebraMap A (N ⧸ J.map Φ)) :=
    (Ideal.Quotient.mk_surjective).comp hΦ
  have hker : RingHom.ker (Algebra.ofId A (N ⧸ J.map Φ)) = J := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (Φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hΦ,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hJ]
  let e := (Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (N ⧸ J.map Φ)) hs)
  rw [e.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective hΦ

theorem aeval_C_mul_X {T : Type} [Fintype T] {S : Type*} [CommRing S] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => d)) :
    eval₂ (Int.castRingHom (Polynomial S)) (fun p => Polynomial.C (r p) * Polynomial.X) f =
      Polynomial.C (eval₂ (Int.castRingHom S) r f) * Polynomial.X ^ d := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eval₂_eq, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m ⟨(), i⟩ = d := hf m hm ()
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fintype.sum_sigma, Fintype.sum_unique, hmd, map_mul, map_prod]
  simp only [map_pow, eq_intCast, map_intCast]
  ring

end VerticalPointMultiplicityChart


open VerticalPointMultiplicityChart in
theorem VertPointMultChart.proof (hCh : VertPointChart.Statement) (hN : VertPointNagata.Statement) :
    VertPointMultChart.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW t ht a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN T K' y s hP hs hsP W hW t ht a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    apply ht
    apply hPW
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let ι : Localization.AtPrime (curvePtIdeal y W) →+* K' := IsLocalization.lift hunit
  have hinj : Function.Injective ι := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl) (Localization.AtPrime (curvePtIdeal y W))
      (le_nonZeroDivisors_of_noZeroDivisors fun h => h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  have hbc' : ∀ u, b' u ∈ (curvePtIdeal y W).primeCompl := hb'
  let r : (Σ _ : Unit, T) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p.2) (⟨b' p.2, hbc' p.2⟩ : (curvePtIdeal y W).primeCompl)
  have hιr : ∀ p, ι (r p) = y p / y ⟨(), t⟩ := by
    rintro ⟨⟨⟩, u⟩
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' u).symm
  have hιa : ∀ f : MRing (fun _ : Unit => T), ι (aeval r f) = aeval (fun p => ι (r p)) f := fun f => by
    induction f using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [hιa, funext hιr, VerticalPointResidue.aeval_div y t s 1 hs]
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : K') = (b : K') * (aeval y s * (y ⟨(), t⟩ ^ 1)⁻¹)
    rw [pow_one, ← mul_assoc, hab, mul_assoc, mul_inv_cancel₀ hyt, mul_one]

  have hX : (Polynomial.X : Polynomial (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (Polynomial.C : _ →+* Polynomial _)).primeCompl := by
    intro h
    have h1 := Ideal.mem_map_C_iff.mp h 1
    rw [Polynomial.coeff_X_one] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) := by
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (Polynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
          (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W))) Polynomial.X) := by
    have hΦ' : Φ (algebraMap _ _ s) = algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W)))
        (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (aeval (fun p => Polynomial.C (r p) * Polynomial.X) s) := hΦ s
    rw [hΦ', aeval_def, RingHom.ext_int (algebraMap ℤ (Polynomial (Localization.AtPrime (curvePtIdeal y W))))
      (Int.castRingHom (Polynomial (Localization.AtPrime (curvePtIdeal y W)))), aeval_C_mul_X r s 1 hs,
      ← RingHom.ext_int (algebraMap ℤ (Localization.AtPrime (curvePtIdeal y W)))
        (Int.castRingHom (Localization.AtPrime (curvePtIdeal y W))), ← aeval_def, hsr, IsLocalization.mk'_eq_mul_mk'_one, pow_one, map_mul, map_mul,
      map_mul, IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing _), Polynomial.algebraMap_eq,
      mul_assoc]
  have hv : IsUnit (algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (Polynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
          (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W))) Polynomial.X) :=
    ((hbu.map Polynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hX⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (nagataRing (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing _), ← Ideal.map_map,
      Polynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
      (nagataRing (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (nagataRing (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dite_eq_left hWp, locLen, dite_eq_left hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace SectionQuotientLocal

variable {T : Type} {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem coord_mem_sectionMod (t : T) : y ⟨(), t⟩ ∈ sectionMod y := by
  show ∀ c : Unit → T, (∀ k, y ⟨k, c k⟩ ≠ 0) → _ ∈ chartRingZ y c
  intro c _
  have hg : y ⟨(), t⟩ / y ⟨(), c ()⟩ ∈ chartRingZ y c := by
    unfold chartRingZ
    exact Algebra.subset_adjoin ⟨⟨(), t⟩, rfl⟩
  simpa [div_eq_mul_inv] using hg

theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (t : T)
    (h : ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a)
    {z : K'} (hz : z ∈ chartRingZ y (fun _ => t)) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : K') * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    exact h u
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end SectionQuotientLocal


open SectionQuotientLocal in
theorem SectionQuotLocal.proof : SectionQuotLocal.Statement := by
  intro T _ K' _ _ y s _hy hs hsP m t hm hrat a b hb hba
  set x := aeval y s with hx_def
  have hx0 : x ≠ 0 := SectionQuotientFinite.aeval_ne_zero y hs hsP
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hba
    rcases mul_eq_zero.mp hba with h | h
    · have hb0 : b = 0 := by exact_mod_cast h
      exact hb (hb0 ▸ m.zero_mem)
    · exact hx0 h

  let e : sectionMod y := ⟨y ⟨(), t⟩, coord_mem_sectionMod y t⟩
  let φ : curveRing y →ₗ[curveRing y] sectionQuot y x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : K') * x = β * y ⟨(), t⟩ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] sectionQuot y x := (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ hyt
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : sectionMod y, ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : K') ∈ chartLat y (fun _ => 1) 1 := n.2
    have hnt : (n : K') * (y ⟨(), t⟩)⁻¹ ∈ chartRingZ y (fun _ => t) := by
      simpa using hn (fun _ => t) (fun _ => hyt)
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm t hrat hnt
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : K') * n = β * y ⟨(), t⟩
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (sectionQuot y x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dite_eq_left hm, dite_eq_left hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdFibreRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace StandardDualFibreRatios

theorem nonempty_of_basis {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by
  by_contra hT
  rw [not_nonempty_iff] at hT
  have h := DualArithmeticVariety.span_basis (K := K) b
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  have h1 : (Pi.single (⟨0, hi⟩ : Fin i) 1 : Fin i → K) ∈ (⊥ : Submodule K (Fin i → K)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨0, hi⟩
  simp at h2

end StandardDualFibreRatios


open StandardDualFibreRatios in
theorem DualStdFibreRatios.proof (hTr : GenFibreModelTransport.Statement) (hMod : DualStdGraphModel.Statement)
    (hRk : DualStdModelRank.Statement) (hTc : DualStdModelTransc.Statement) : DualStdFibreRatios.Statement := by
  intro K _ _ i T _ _ b G hi
  obtain ⟨c⟩ := nonempty_of_basis b hi
  let Φ₀ : Subfield (dualStdModelField K i) :=
    Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)))
  have hΦ₀ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Φ₀ := Subfield.fieldRange_subtype _
  obtain ⟨h0, hrk, htr⟩ := hTr Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i))
    (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
    (graphIdeal (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))) G (dualStdModelField K i)
    (dualStdModelPt b) (hMod K i T b) Φ₀ hΦ₀ T
    (fun t => (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
    (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)
  obtain ⟨hz, hrk₀⟩ := hRk K i T b Φ₀ hΦ₀ hi c
  refine ⟨c, fun h => hz (h0.mp h), ?_, ?_⟩
  · exact hrk.trans hrk₀
  · exact htr.mpr (hTc K i T b Φ₀ hΦ₀ hi c)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGraphModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualGraphModel

open StandardDualImageBottom

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem mConeMap_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (q : Σ _ : Unit, Fin i) :
    mConeMap (dualLatticeCoord b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) =
      C (aeval (dualLatticeCoord b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b) q)) * X () := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, map_sum, map_mul, Finset.sum_mul, mConeMap, aeval_X, eq_intCast, map_intCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

def coneLift (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MRing (dualBlocks T) ⧸ dualIdeal b →+* MvPolynomial Unit (ProjField K i) :=
  Ideal.Quotient.lift (dualIdeal b)
    (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) fun _ ha => ha

omit [Fintype T] in
theorem coneLift_mk (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (dualBlocks T)) :
    coneLift b (Ideal.Quotient.mk _ f) = mConeMap (dualLatticeCoord b) f :=
  rfl

omit [Fintype T] in
theorem coneLift_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (coneLift b) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun _ ha => ha

def modelMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp (MvPolynomial.map (coneLift b))

omit [Fintype T] in
theorem modelMap_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (modelMap b) :=
  (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i)).comp
    (MvPolynomial.map_injective _ (coneLift_injective b))

theorem modelMap_comp_graphMap [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    (modelMap b).comp (graphMap (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))) =
      (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) := by
  refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
  rintro ⟨(u | u), j⟩ <;> cases u
  · simp [graphMap, modelMap, coneLift_mk, dualStdModelPt, dualStdModelEmb, dualStdModelS,
      mConeMap]
  · have h := mConeMap_linForm b ⟨(), j⟩
    rw [aeval_linForm] at h
    simp only [RingHom.comp_apply, graphMap, eval₂Hom_X', modelMap, map_mul, map_C, map_X, coneLift_mk, h,
      dualStdModelPt, dualStdModelEmb, dualStdModelS, dualStdModelT, genPt]

end StandardDualGraphModel


open StandardDualGraphModel in
theorem DualStdGraphModel.proof : DualStdGraphModel.Statement := by
  intro K _ _ i T _ _ b
  rw [← modelMap_comp_graphMap b]
  ext f
  rw [graphIdeal, RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (modelMap_injective b)]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGenFibreModelTransport
section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.QuotientLiftInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFibreModelTransport

open MvPolynomial

theorem adjoin_transport {k₁ A₁ k₂ A₂ : Type*} [Field k₁] [Field A₁] [Algebra k₁ A₁] [Field k₂] [Field A₂]
    [Algebra k₂ A₂] (i : k₁ ≃+* k₂) (h : A₁ →+* A₂)
    (hc : (algebraMap k₂ A₂).comp i.toRingHom = h.comp (algebraMap k₁ A₁)) (s : Set A₁) (a : A₁) :
    Module.finrank k₁ (Algebra.adjoin k₁ s) = Module.finrank k₂ (Algebra.adjoin k₂ (h '' s)) ∧
      (Transcendental (Algebra.adjoin k₁ s) a ↔ Transcendental (Algebra.adjoin k₂ (h '' s)) (h a)) := by
  have hring : (Algebra.adjoin k₂ (h '' s)).toSubring = (Algebra.adjoin k₁ s).toSubring.map h := by
    rw [Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure, RingHom.map_closure, Set.image_union]
    congr 2
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap k₁ A₁ (i.symm c), ⟨_, rfl⟩, by simpa using (congr($hc (i.symm c))).symm⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨i c, by simpa using congr($hc c)⟩
  have hmem : ∀ y, y ∈ Algebra.adjoin k₂ (h '' s) ↔ ∃ x ∈ Algebra.adjoin k₁ s, h x = y := fun y => by
    rw [← Subalgebra.mem_toSubring, hring, Subring.mem_map]; rfl
  let g : Algebra.adjoin k₁ s →+* Algebra.adjoin k₂ (h '' s) :=
    (h.comp (Algebra.adjoin k₁ s).val.toRingHom).codRestrict (Algebra.adjoin k₂ (h '' s))
      (fun x => (hmem _).2 ⟨x, x.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (h.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    obtain ⟨x, hx, e⟩ := (hmem y).1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  let j := RingEquiv.ofBijective g hg
  refine ⟨Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun c => Subtype.ext congr($hc c)),
    (transcendental_ringHom_iff_of_comp_eq j h h.injective (RingHom.ext fun x => rfl)).symm⟩

theorem eval₂_mem_closure {σ F : Type*} [Field F] (c : ℤ →+* F) (y : σ → F) (f : MvPolynomial σ ℤ) :
    eval₂ c y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [eval₂_C, eq_intCast]; exact intCast_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p n hp => rw [eval₂_mul, eval₂_X]; exact mul_mem hp (Subfield.subset_closure ⟨n, rfl⟩)

theorem quotient_lift_injective {A F : Type*} [CommRing A] [Field F] (φ : A →+* F) (P : Ideal A)
    (h : RingHom.ker φ = P) (hP : ∀ a ∈ P, φ a = 0) : Function.Injective (Ideal.Quotient.lift P φ hP) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.lift_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← h]
  exact ha

theorem subfield_equiv {L A Φ : Type*} [Field L] [Field A] [Field Φ] (k : Subfield L) (α : L →+* A)
    (ι : Φ →+* A) (hr : ι.fieldRange = k.map α) : ∃ e : k ≃+* Φ, ∀ c, ι (e c) = α c := by
  let g : k →+* ι.fieldRange :=
    (α.comp k.subtype).codRestrict ι.fieldRange (fun c => hr ▸ Subfield.mem_map.2 ⟨c, c.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (α.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    have hy : (y : A) ∈ k.map α := hr ▸ y.2
    obtain ⟨x, hx, e⟩ := Subfield.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨(RingEquiv.ofBijective g hg).trans ι.rangeRestrictFieldEquiv.symm, fun c =>
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ι (g c)⟩

end GenericFibreModelTransport

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial GenericFibreModelTransport

theorem GenFibreModelTransport.proof : GenFibreModelTransport.Statement := by
  intro K _ ι _ K' _ ι' _ v P' G Ω _ z hz Φ₀ _ _ hΦ₀ τ w q
  let φ : MRing ι' →+* G.Φ' := (aeval G.x').toRingHom
  let ψ : MRing ι' →+* Ω := eval₂Hom (Int.castRingHom Ω) z
  have : P'.IsPrime := hz ▸ RingHom.ker_isPrime ψ
  have hφ : ∀ a ∈ P', φ a = 0 := fun a ha => RingHom.mem_ker.1 (G.genericFibre_ker_target.symm ▸ ha)
  have hψ : ∀ a ∈ P', ψ a = 0 := fun a ha => RingHom.mem_ker.1 (hz.symm ▸ ha)
  let α : FractionRing (MRing ι' ⧸ P') →+* G.Φ' :=
    IsFractionRing.lift (quotient_lift_injective φ P' G.genericFibre_ker_target hφ)
  let β : FractionRing (MRing ι' ⧸ P') →+* Ω := IsFractionRing.lift (quotient_lift_injective ψ P' hz hψ)
  let ξ : (Σ k', ι' k') → FractionRing (MRing ι' ⧸ P') := fun p =>
    algebraMap _ _ (Ideal.Quotient.mk P' (X p))
  have hα : α ∘ ξ = G.x' := funext fun p => by simp [α, ξ, φ]
  have hβ : β ∘ ξ = z := funext fun p => by simp [β, ξ, ψ]
  let k := Subfield.closure (Set.range (ξ ∘ v))
  have h₁ : (algebraMap G.Φ G.Φ').fieldRange = k.map α := by
    rw [RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hα]
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have key : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ Subfield.closure (Set.range (G.x' ∘ v)) := by
        intro f
        rw [aeval_def, eval₂_comp_left]
        convert eval₂_mem_closure _ (G.x' ∘ v) f using 2
        exact funext fun p => (G.compat p).symm
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rintro _ ⟨p, rfl⟩
      exact ⟨G.x p, (G.compat p).symm⟩
  have h₂ : (algebraMap Φ₀ Ω).fieldRange = k.map β := by
    rw [hΦ₀, RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hβ]
  obtain ⟨e₁, he₁⟩ := subfield_equiv k α (algebraMap G.Φ G.Φ') h₁
  obtain ⟨e₂, he₂⟩ := subfield_equiv k β (algebraMap Φ₀ Ω) h₂
  let s : Set (FractionRing (MRing ι' ⧸ P')) := Set.range fun t => ξ (w t) / ξ q
  have hs : ∀ (F : Type) [Field F] (γ : FractionRing (MRing ι' ⧸ P') →+* F) (y : (Σ k', ι' k') → F),
      γ ∘ ξ = y → γ '' s = Set.range fun t => y (w t) / y q := by
    rintro F _ γ y rfl
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun t => map_div₀ γ _ _)
  obtain ⟨f₁, t₁⟩ := adjoin_transport e₁ α (RingHom.ext he₁) s (ξ q)
  obtain ⟨f₂, t₂⟩ := adjoin_transport e₂ β (RingHom.ext he₂) s (ξ q)
  rw [hs _ α _ hα] at f₁ t₁
  rw [show α (ξ q) = G.x' q from congrFun hα q] at t₁
  rw [hs _ β _ hβ] at f₂ t₂
  rw [show β (ξ q) = z q from congrFun hβ q] at t₂
  refine ⟨?_, f₁.symm.trans f₂, t₁.symm.trans t₂⟩
  rw [← congrFun hα q, ← congrFun hβ q]
  exact (map_eq_zero α).trans (map_eq_zero β).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoSecond
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

noncomputable section

namespace StackedExceptionalSecondGeometric

variable {T : Type} [Fintype T] {k : Type} [Field k]

theorem comap_linPrime {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    (linPrime α M).comap (C : ℤ →+* MRing (stackedBlocks T)) = RingHom.ker (Int.castRingHom k) := by
  ext z
  rw [Ideal.mem_comap, linPrime, RingHom.mem_ker, RingHom.mem_ker, linPointMap, coe_eval₂Hom, eval₂_C, eq_intCast,
    ← map_intCast (C : k →+* MvPolynomial (Option (Fin n)) k), C_eq_zero, eq_intCast]

theorem charOf_linPrime {n : ℕ} (α : T → k) (M : T → Fin n → k) : charOf (linPrime α M) = ringChar k := by
  have hker : RingHom.ker (Int.castRingHom k) = Ideal.span {((ringChar k : ℕ) : ℤ)} := by
    ext z
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast, CharP.intCast_eq_zero_iff k (ringChar k)]
  have key : ∀ I : Ideal ℤ, I = Ideal.span {((ringChar k : ℕ) : ℤ)} →
      (Submodule.IsPrincipal.generator I).natAbs = ringChar k := fun I hI => by
    have h := Ideal.span_singleton_eq_span_singleton.mp ((Ideal.span_singleton_generator I).trans hI)
    rw [Int.associated_iff_natAbs] at h
    rw [h, Int.natAbs_natCast]
  exact key _ ((comap_linPrime α M).trans hker)


omit [Fintype T] in
theorem exists_alpha_ne {α : T → k} (hα : Submodule.span ℤ (Set.range α) = ⊤) : ∃ s, α s ≠ 0 := by
  by_contra h
  push Not at h
  have hle : Submodule.span ℤ (Set.range α) ≤ ⊥ := Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; simp [h t])
  rw [hα, top_le_iff] at hle
  exact one_ne_zero ((Submodule.mem_bot ℤ).mp (hle ▸ Submodule.mem_top : (1 : k) ∈ (⊥ : Submodule ℤ k)))

theorem isRelevant_linPrime {n : ℕ} {α : T → k} {M : T → Fin (n + 1) → k}
    (hα : Submodule.span ℤ (Set.range α) = ⊤) (hM : LinFormsIndep M) : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (linPrime α M) := by
  rintro (⟨⟩ | ⟨⟩)
  · obtain ⟨s, hs⟩ := exists_alpha_ne hα
    refine ⟨s, fun h => hs ?_⟩
    have h1 := LinPrimeExample.linPointMap_first α M s
    rw [graphFirst] at h1
    rw [linPrime, RingHom.mem_ker, h1] at h
    have h2 := congrArg (MvPolynomial.eval fun _ => (1 : k)) h
    simpa using h2
  · have hw : (Pi.single 0 1 : Fin (n + 1) → k) ≠ 0 := fun h0 => by
      simpa using congrFun h0 0
    obtain ⟨t, ht⟩ : ∃ t, ∑ j, M t j * (Pi.single 0 1 : Fin (n + 1) → k) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (hM _ h)
    refine ⟨t, fun h => ht ?_⟩
    have h1 := LinPrimeExample.linPointMap_second α M t
    rw [graphSecond] at h1
    rw [linPrime, RingHom.mem_ker, h1] at h
    have h2 := congrArg
      (MvPolynomial.eval fun o : Option (Fin (n + 1)) => o.elim (0 : k) fun j => (Pi.single 0 1 : Fin (n + 1) → k) j) h
    simpa using h2

theorem degSecond_inl : degSecond (Sum.inl ()) = 0 := by
  rw [degSecond, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inr_ne_inl hu)]
  rfl

theorem length_mul_log [Finite k] :
    ((Module.length ℤ k).toNat : ℝ) * Real.log (ringChar k) = Real.log (Nat.card k) := by
  set p := ringChar k with hp
  have : CharP k p := ringChar.charP k
  have := Fact.mk (CharP.char_is_prime k p)
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : Fintype k := Fintype.ofFinite k
  have hlen : Module.length ℤ k = Module.finrank (ZMod p) k := by
    rw [Module.length_eq_of_surjective (R := ZMod p) ZMod.intCast_surjective, Module.length_eq_finrank]
  rw [hlen, ENat.toNat_natCast, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card,
    Nat.cast_pow, Real.log_pow]

theorem geoNum_linPrime (hCut : LinPrimeCut.Statement) (hBase : LinPrimeBase.Statement) :
    ∀ (n : ℕ) (α : T → k) (M : T → Fin (n + 1) → k), Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
      geoNum n (linPrime α M) (fun _ => degSecond) = ((Module.length ℤ k).toNat : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro α M hα hM
    have hrel := isRelevant_linPrime hα hM
    rw [geoNum, dite_eq_left hrel]
    unfold LinPrimeBase.Statement at hBase
    obtain ⟨e⟩ := hBase T k α M hα hM (fun κ => (hrel κ).choose) (fun κ => (hrel κ).choose_spec)
    rw [e.toAddEquiv.toIntLinearEquiv.length_eq]
  | succ n ih =>
    intro α M hα hM
    have hrel : ∀ κ, ∃ j, (X ⟨κ, j⟩ : MRing (stackedBlocks T)) ∉ linPrime α M := isRelevant_linPrime hα hM
    rw [geoNum]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant
    rw [dite_eq_left hrel, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique]
    rw [show degSecond (Sum.inl default) = 0 from degSecond_inl, show degSecond (Sum.inr default) = 1 from degSecond_inr,
      zero_mul, zero_add, one_mul]
    obtain ⟨M', hM', hsupp, hmult⟩ := hCut T k n α M hα hM ((hrel (Sum.inr ())).choose)
      (hrel (Sum.inr ())).choose_spec
    have hsupp' : divSupp (linPrime α M) (X ⟨Sum.inr default, (hrel (Sum.inr default)).choose⟩) =
        {linPrime α M'} := hsupp
    rw [hsupp', finsum_mem_singleton]
    have hmult' : multAt (linPrime α M ⊔ Ideal.span {(X ⟨Sum.inr default, (hrel (Sum.inr default)).choose⟩ :
        MRing (stackedBlocks T))}) (linPrime α M') = 1 := hmult
    rw [hmult', Nat.cast_one, one_mul]
    exact ih α M' hα hM'

end StackedExceptionalSecondGeometric


open StackedExceptionalSecondGeometric in
theorem DualStackedExcGeoSecond.proof (hLin : DualStackedExcLinear.Statement) (hCut : LinPrimeCut.Statement)
    (hBase : LinPrimeBase.Statement) : DualStackedExcGeoSecond.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, _, _, α, M, hα, hM, rfl, hcard⟩ := hLin K i F F' T b b' a hi hlt hcov hab E hE
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, geoNum_linPrime hCut hBase n α M hα hM, charOf_linPrime, ← hcard,
    ← Nat.card_eq_fintype_card, ← length_mul_log]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
end
