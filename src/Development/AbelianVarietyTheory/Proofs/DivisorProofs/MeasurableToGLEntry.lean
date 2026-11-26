module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GlobalTheory.JSW

variable {n : ℕ}

def htGL (g : GL (Fin n) ℂ) : ℝ :=
  1 + ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ + ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖

def levSet (n r : ℕ) : Set (GL (Fin n) ℂ) :=
  {g | ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}

def rowCut (ρ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ := fun j => if j ≤ ρ then x ρ j else 0

def secMat (ρ j : Fin n) (v : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i l => if i = ρ then (if l ≤ ρ then v l else 0) else if l = Equiv.swap j ρ i then 1 else 0


open Classical in
def toGL (x : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n) ℂ := if h : IsUnit x then h.unit else 1

theorem val_toGL {x : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit x) : (toGL x : Matrix (Fin n) (Fin n) ℂ) = x := by
  simp [toGL, h]

theorem one_le_htGL (g : GL (Fin n) ℂ) : 1 ≤ htGL g := by
  unfold htGL
  have h1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  linarith

theorem htGL_pos (g : GL (Fin n) ℂ) : 0 < htGL g := lt_of_lt_of_le one_pos (one_le_htGL g)

theorem htGL_inv (g : GL (Fin n) ℂ) : htGL g⁻¹ = htGL g := by
  unfold htGL; rw [inv_inv]; ring

theorem sum_norm_mul_le (a b : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(a * b) i j‖ ≤ ∑ j, ∑ l, ‖a i l‖ * ‖b l j‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ = ∑ l, ‖a i l‖ * ∑ j, ‖b l j‖ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ l, ‖a i l‖ * ∑ l', ∑ j, ‖b l' j‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun l' => ∑ j, ‖b l' j‖) (fun _ _ => by positivity) (Finset.mem_univ l))
          (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem htGL_mul_le (g h : GL (Fin n) ℂ) : htGL (g * h) ≤ htGL g * htGL h := by
  unfold htGL
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have h1 := sum_norm_mul_le (g : Matrix (Fin n) (Fin n) ℂ) h
  have h2 := sum_norm_mul_le ((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (g⁻¹ : GL (Fin n) ℂ)
  have a1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a3 : 0 ≤ ∑ i, ∑ j, ‖(h : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a4 : 0 ≤ ∑ i, ∑ j, ‖((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  nlinarith [mul_nonneg a1 a4, mul_nonneg a2 a3]

theorem norm_entry_le_htGL (g : GL (Fin n) ℂ) (i j : Fin n) : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ htGL g := by
  unfold htGL
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h1 : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ i))
  linarith

theorem continuous_htGL : Continuous (htGL : GL (Fin n) ℂ → ℝ) := by
  have h1 : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) ℂ => ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    Units.continuous_coe_inv
  unfold htGL
  fun_prop

theorem isOpenEmbedding_valGL :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) ℂ => fun i j => (g : Matrix (Fin n) (Fin n) ℂ) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) ℂ)

theorem measurable_comp_GL {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) ℂ → β} (hF : Continuous F) {γ : X → GL (Fin n) ℂ}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGL.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_dual {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {η : X → Z →L[ℝ] ℝ} (h : ∀ z, Measurable fun x => η x z) : Measurable η := by
  let b := Module.finBasis ℝ Z
  have : η = fun x => ∑ i, η x (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
    funext x
    ext z
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr z, map_sum]
    simp only [map_smul]
    simp [mul_comm]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (h _).smul_const _


end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMovePreservingLocalParts
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.SemilocalBasis

def awayFrom {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    Submonoid R where
  carrier := {s | s ≠ 0 ∧ ∀ P ∈ SB, s ∉ P.asIdeal}
  one_mem' := ⟨one_ne_zero, fun P _ h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, fun P hP h =>
    (P.isPrime.mem_or_mem h).elim (ha.2 P hP) (hb.2 P hP)⟩

theorem awayFrom_le {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    awayFrom SB ≤ nonZeroDivisors R := fun _ h => mem_nonZeroDivisors_of_ne_zero h.1

theorem isPrincipalIdealRing_awayFrom {R : Type} [CommRing R] [IsDedekindDomain R]
    (SB : Finset (HeightOneSpectrum R)) (A : Type) [CommRing A] [IsDomain A] [Algebra R A]
    [IsLocalization (awayFrom SB) A] : IsPrincipalIdealRing A := by
  classical
  haveI : IsDedekindDomain A := IsLocalization.isDedekindDomain R (awayFrom_le SB) A
  apply IsPrincipalIdealRing.of_finite_primes
  let T : Finset (Ideal R) := insert ⊥ (SB.image (·.asIdeal))
  have hT : ∀ Q ∈ T, Q.IsPrime := by
    intro Q hQ
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact Ideal.isPrime_bot
    · obtain ⟨P, _, rfl⟩ := Finset.mem_image.1 hQ
      exact P.isPrime
  have hinj : Function.Injective (fun I : Ideal A => I.comap (algebraMap R A)) := by
    intro I J h
    rw [← IsLocalization.map_under (awayFrom SB) A I, ← IsLocalization.map_under (awayFrom SB) A J]
    exact congrArg _ h
  refine ((T.finite_toSet).preimage hinj.injOn).subset ?_
  intro I hI
  have hI' : I.IsPrime := hI
  have hsub : ((I.comap (algebraMap R A) : Ideal R) : Set R) ⊆ ⋃ i ∈ (T : Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro s hs
    by_contra hn
    simp only [Set.mem_iUnion, not_exists, id] at hn
    have hS : s ∈ awayFrom SB := by
      refine ⟨fun h0 => hn ⊥ (by simp [T]) (by simp [h0]), fun P hP h => hn P.asIdeal ?_ h⟩
      exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))
    exact hI'.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (IsLocalization.map_units A ⟨s, hS⟩))
  obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ (fun i hi _ _ => hT i hi)).1 hsub
  show I.comap (algebraMap R A) ∈ (T : Set (Ideal R))
  by_cases h0 : I.comap (algebraMap R A) = ⊥
  · rw [h0]; simp [T]
  · have hmax : (I.comap (algebraMap R A)).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime h0 (Ideal.comap_isPrime _ _)
    rw [hmax.eq_of_le (hT Q hQ).ne_top hle]
    exact hQ

theorem exists_basis {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (SB : Finset (HeightOneSpectrum R))
    (N : Submodule R (Fin n → K)) (hN : Submodule.IsFullLattice K N) :
    ∃ v : Module.Basis (Fin n) K (Fin n → K), (∀ i, v i ∈ N) ∧
      ∀ x ∈ N, ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R (Set.range v) := by
  classical
  let A : Subalgebra R K := Localization.subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsLocalization (awayFrom SB) A :=
    Localization.subalgebra.isLocalization_subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsPrincipalIdealRing A := isPrincipalIdealRing_awayFrom SB A
  haveI : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (awayFrom SB) A K

  have clear : ∀ (X : Set (Fin n → K)) (x : Fin n → K), x ∈ Submodule.span A X →
      ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R X := by
    intro X x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_mem _, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, mul_mem hs ht, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hty
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hr⟩ := IsLocalization.surj (awayFrom SB) a
      refine ⟨s * t, mul_mem hs t.2, ?_⟩
      have : (t : R) • a • x = r • x := by
        rw [← algebraMap_smul A (t : R), ← mul_smul, mul_comm, hr, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hsx
  let M : Submodule A (Fin n → K) := Submodule.span A (N : Set (Fin n → K))
  haveI hMlat : Submodule.IsLattice K M := by
    apply Submodule.IsLattice.of_fg K
    obtain ⟨X, hX⟩ := hN.fg
    refine ⟨X, ?_⟩
    simp only [M, ← hX]
    exact (Submodule.span_span_of_tower R A _).symm
  haveI hM : Submodule.IsFullLattice K M := by
    refine ⟨?_⟩
    simp only [M]
    rw [Submodule.span_span_of_tower]
    exact hN.span_eq_top
  haveI : Module.Free A M := Submodule.IsLattice.free K M
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  have hrk : Module.finrank A M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq K M).trans (Module.finrank_fintype_fun_eq_card K))
  let b : Module.Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hb : ∀ i, ∃ s ∈ awayFrom SB, s • (b i : Fin n → K) ∈ N := by
    intro i
    obtain ⟨s, hs, h⟩ := clear _ _ (b i).2
    exact ⟨s, hs, by simpa using h⟩
  choose s hs hsb using hb
  let b' : Module.Basis (Fin n) A M :=
    b.isUnitSMul (w := fun i => algebraMap R A (s i)) (fun i => IsLocalization.map_units A ⟨s i, hs i⟩)
  have hb' : ∀ i, (b' i : Fin n → K) = s i • (b i : Fin n → K) := by
    intro i
    simp only [b', Module.Basis.isUnitSMul_apply, Submodule.coe_smul, algebraMap_smul]
    try rfl
  refine ⟨b'.extendOfIsFullLattice K, fun i => ?_, fun x hx => ?_⟩
  · rw [Module.Basis.extendOfIsFullLattice_apply, hb']
    exact hsb i
  · apply clear
    have hxM : x ∈ M := Submodule.subset_span hx
    have h1 := b'.sum_repr ⟨x, hxM⟩
    have h2 : x = ∑ i, b'.repr ⟨x, hxM⟩ i • (b' i : Fin n → K) := by
      have := congrArg Subtype.val h1
      rw [AddSubmonoidClass.coe_finsetSum] at this
      exact this.symm
    rw [h2]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    rw [Module.Basis.extendOfIsFullLattice_apply]

theorem mem_localization_iff {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem stdLat_eq_span (E : Type) [Field E] (n : ℕ) :
    Formalism.L2.Col.stdLat E n = Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n))) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
      Submodule.mem_one.1 (hx i (Set.mem_univ _))
    choose r hr using hx'
    have : x = ∑ i, r i • Pi.basisFun E (Fin n) i := by
      conv_lhs => rw [← (Pi.basisFun E (Fin n)).sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.basisFun_repr, ← hr, algebraMap_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ j _
    rw [Pi.basisFun_apply]
    by_cases h : j = i
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

theorem exists_equiv (E : Type) [Field E] [NumberField E] (n : ℕ)
    (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsFullLattice E N) :
    ∃ γ : Sp E n ≃ₗ[E] Sp E n, (∀ x ∈ Formalism.L2.Col.stdLat E n, γ x ∈ N) ∧
      ∀ P ∈ SB, ∀ x, γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔
        x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E n) := by
  obtain ⟨v, hv, hgen⟩ := exists_basis E n SB N hN
  let γ : Sp E n ≃ₗ[E] Sp E n := (Pi.basisFun E (Fin n)).equiv v (Equiv.refl _)
  have key : ∀ x, x ∈ Formalism.L2.Col.stdLat E n ↔ γ x ∈ Submodule.span (𝓞 E) (Set.range v) := by
    intro x
    have hmap : (Formalism.L2.Col.stdLat E n).map ((γ.restrictScalars (𝓞 E)) : Sp E n →ₗ[𝓞 E] Sp E n)
        = Submodule.span (𝓞 E) (Set.range v) := by
      rw [stdLat_eq_span, Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      exact (Pi.basisFun E (Fin n)).equiv_apply i v (Equiv.refl _)
    rw [← hmap]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, h⟩
      have : y = x := γ.injective h
      exact this ▸ hy
  have hle : Submodule.span (𝓞 E) (Set.range v) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hsm : ∀ (s : 𝓞 E) x, γ (s • x) = s • γ x := fun s x =>
    (γ.restrictScalars (𝓞 E)).map_smul s x
  refine ⟨γ, fun x hx => hle ((key x).1 hx), fun P hP x => ?_⟩
  rw [mem_localization_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, ht, h'⟩ := hgen _ h
    refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim (ht.2 P hP) hs, ?_⟩
    rw [key, hsm, mul_smul]
    exact h'
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, hle ?_⟩
    rw [← hsm]
    exact (key _).1 h

end GlobalTheory.SemilocalBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMTypeCard

theorem bijective_mk_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

theorem card_eq_finrank_of_isCMType : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2),
    Fintype.card I = Module.finrank K E := by
  intro K E _ _ _ _ _ _ I _ φ hφ h2
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (bijective_mk_of_isCMType hφ)
  have hE : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have hr : NumberField.InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    omega
  have hKE : Module.finrank ℚ E = Module.finrank ℚ K * Module.finrank K E :=
    (Module.finrank_mul_finrank ℚ K E).symm
  rw [h2] at hKE
  omega

end GlobalTheory.CMTypeCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrankStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := by
  first | exact @GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | exact GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | (intros; apply GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartan
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.RealPar Matrix

namespace GlobalTheory.CoverExp

variable {p q : ℕ}

theorem sq_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    ((T.sq (T.expt X) : ℂˣ) : ℂ) = Complex.exp (X.trace / 2) := by
  set c : ℂ := X.trace / 2 with hc
  set f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • X)) : ℂˣ) : ℂ) with hf
  have hd : ∀ t, HasDerivAt f (f t * c) t := by
    intro t
    have h0 : HasDerivAt f c 0 := Cover.hasDerivAt_sq (T := T) hX
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) c t :=
      HasDerivAt.comp_sub_const t t (f := f) (f' := c) (by rw [sub_self]; exact h0)
    have h2 : f = fun s => f t * f (s - t) := by
      funext s
      simp only [hf]
      rw [← Units.val_mul, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    have h3 := h1.const_mul (f t)
    rw [← h2] at h3
    exact h3
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) * f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    exact (h1.fun_mul (hd t)).congr_deriv (by ring)
  have h := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, Units.val_one] at h
  calc _ = Complex.exp c * (Complex.exp (-c) * ((T.sq (T.expt X) : ℂˣ) : ℂ)) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = _ := by rw [h, mul_one]

theorem exists_expt_ker (hn : 1 ≤ p + q) (T : GrpData p q) :
    ∃ Z ∈ upq p q, T.cov (T.expt Z) = 1 ∧ T.sq (T.expt Z) = -1 := by
  let a : Ix p q := finSumFinEquiv.symm ⟨0, hn⟩
  refine ⟨TorusWt.torX (Pi.single a (2 * Real.pi)), TorusWt.torX_mem _, ?_, ?_⟩
  · apply Units.ext
    rw [T.expt_cov _ (TorusWt.torX_mem _), TorusWt.torX, Matrix.exp_diagonal, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    by_cases h : b = a
    · subst h
      simp [Complex.exp_two_pi_mul_I]
    · simp [h]
  · apply Units.ext
    rw [sq_expt T (TorusWt.torX_mem _), TorusWt.torX, Matrix.trace_diagonal, Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I / 2 = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
      simp
    · intro b _ h
      simp [h]
    · simp

theorem exists_blockOrd (p q : ℕ) : ∃ (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool), BlockOrd e ε := by
  refine ⟨finSumFinEquiv, fun i => (finSumFinEquiv.symm i).isLeft, fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) h
  · have h' : a < b := h
    exact h'
  · exact h.elim
  · exact h.elim
  · have h' : a < b := h
    exact Nat.add_lt_add_left h' p

theorem isPC_of_anticomm {X : Mat p q} (h : X * Jm p q = -(Jm p q * X)) : IsPC X := by
  intro a b hab
  have := congrFun (congrFun h a) b
  rw [Matrix.neg_apply, KStabLie.Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  rcases a with a | a <;> rcases b with b | b
  · simp only [Sum.elim_inl] at this
    linear_combination (1 / 2 : ℂ) * this
  · simp [sameBlock] at hab
  · simp [sameBlock] at hab
  · simp only [Sum.elim_inr] at this
    linear_combination (-1 / 2 : ℂ) * this

theorem exists_exp_mul_exp {g : Mat p q} (hg : gᴴ * Jm p q * g = Jm p q) :
    ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, g = NormedSpace.exp Z * NormedSpace.exp X := by
  obtain ⟨e, ε, hb⟩ := exists_blockOrd p q
  obtain ⟨Z, X, hZ, hX, h⟩ := Formalism.REAL.genExp_of Formalism.REAL.compact_exponential_surjective _ ε _ ((hb.inUJ_iff g).2 hg)
  obtain ⟨Z, rfl⟩ := (Matrix.reindex e e).surjective Z
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective X
  have hG : ∀ Y : Mat p q, Formalism.REAL.inG ε (Matrix.reindex e e Y) → Y ∈ upq p q := by
    intro Y h1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hexp : ∀ Y : Mat p q, NormedSpace.exp (Matrix.reindex e e Y) = Matrix.reindex e e (NormedSpace.exp Y) := by
    intro Y
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) Y).symm
  refine ⟨Z, hG Z hZ.1, (KStabLie.isKC_iff Z).2 ?_, X, ⟨hG X hX.1, isPC_of_anticomm ?_⟩, ?_⟩
  · have h2 := hZ.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h2
  · have h2 := hX.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h2
    exact h2
  · rw [hexp, hexp] at h
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h

theorem closure_expt_eq_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q,
    Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  intro p q hn T
  have key : ∀ g : T.G, ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, T.cov g = T.cov (T.expt Z) * T.cov (T.expt X) := by
    intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := exists_exp_mul_exp ((mem_Upq _).1 (T.cov_mem g))
    exact ⟨Z, hZ, hK, X, hX, Units.ext (by rw [Units.val_mul, T.expt_cov Z hZ, T.expt_cov X hX.1, h])⟩
  constructor
  · rw [eq_top_iff]
    intro g _
    obtain ⟨Z, hZ, -, X, hX, h⟩ := key g
    obtain ⟨C, hC, hC1, hC2⟩ := exists_expt_ker hn T
    have hm : ∀ Y ∈ upq p q, T.expt Y ∈ Subgroup.closure (T.expt '' upq p q) :=
      fun Y hY => Subgroup.subset_closure ⟨Y, hY, rfl⟩
    have hx := Subgroup.mul_mem _ (hm Z hZ) (hm X hX.1)
    rw [← map_mul] at h
    set x := T.expt Z * T.expt X
    have h2 : ((T.sq g : ℂˣ) : ℂ) ^ 2 = ((T.sq x : ℂˣ) : ℂ) ^ 2 := by rw [T.sq_sq, T.sq_sq, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · rw [Cover.ext_of h (Units.ext h3)]
      exact hx
    · have : g = T.expt C * x := Cover.ext_of (by rw [map_mul, hC1, one_mul, h])
        (Units.ext (by rw [map_mul, hC2, h3]; simp))
      rw [this]
      exact Subgroup.mul_mem _ (hm C hC) hx
  · intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := key g
    refine ⟨g * (T.expt X)⁻¹, ?_, X, hX, by simp⟩
    have h1 := KStabLie.expt_mem T hZ hK 1
    rw [one_smul] at h1
    change IsKC _
    rw [map_mul, map_inv, h, mul_inv_cancel_right]
    exact h1

end GlobalTheory.CoverExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverUpq_closure_exp_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q, Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  first | exact @GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | exact GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | (intros; apply GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.NumeratorIdeal

section general
variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem count_span_int (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    v.valuation K (algebraMap R K a) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a))) := by
  classical
  have hJ : (Ideal.span {a} : Ideal R) ≠ 0 := by simpa using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v hJ,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v ha]

theorem valuation_eq_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha0
  have hb' : algebraMap R K b ≠ 0 := by simpa using hb0
  rw [map_div₀, count_span_int K v ha0, count_span_int K v hb0, div_eq_mul_inv (algebraMap R K a),
    ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using ha0)
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hb0),
    ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
  congr 1
  ring

theorem le_one_of_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) : I ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  refine finprod_induction (fun J : FractionalIdeal R⁰ K => J ≤ 1) le_rfl
    (fun a b ha hb => mul_le_one' ha hb) fun v => ?_
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
  show _ ≤ _
  rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

theorem le_of_count {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) :
    I ≤ J := by
  have h1 : I * J⁻¹ ≤ 1 := le_one_of_count K (mul_ne_zero hI (inv_ne_zero hJ)) fun v => by
    rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
    linarith [h v]
  have h2 := mul_le_mul_left h1 J
  rwa [inv_mul_cancel_right₀ hJ, one_mul] at h2

theorem mem_iff_valuation {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K v I) := by
  by_cases hx : x = 0
  · subst hx
    simp [FractionalIdeal.zero_mem]
  have hs : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp only [valuation_eq_count K _ hx, WithZero.exp_le_exp, neg_le_neg_iff]
  exact ⟨fun h v => FractionalIdeal.count_mono K v hs h, le_of_count K hs hI⟩

theorem one_le_count {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (h : I ≤ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  rw [← FractionalIdeal.count_self K v]
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 h)

theorem sup_eq_top_of {I J : Ideal R} (hI : I ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum R, I ≤ v.asIdeal → J ≤ v.asIdeal → False) : I ⊔ J = ⊤ := by
  by_contra H
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ H
  have h1 : I ≤ p := le_sup_left.trans hle
  exact h ⟨p, hp.isPrime, fun e => hI (le_bot_iff.1 (e ▸ h1))⟩ h1 (le_sup_right.trans hle)

theorem count_prod_pow (s : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ)
    (f : HeightOneSpectrum R → HeightOneSpectrum R) (hf : ∀ Q, f (f Q) = Q)
    (hs : ∀ Q, Q ∉ s → n Q = 0) (P : HeightOneSpectrum R) :
    FractionalIdeal.count K P ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = n (f P) := by
  classical
  have e : ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = ∏ Q ∈ s, ((f Q).asIdeal : FractionalIdeal R⁰ K) ^ n Q := by
    have := map_prod (FractionalIdeal.coeIdealHom R⁰ K) (fun Q => (f Q).asIdeal ^ n Q) s
    simp only [map_pow] at this
    exact this
  rw [e, FractionalIdeal.count_prod K P _ _
    (fun Q _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (f Q).ne_bot)),
    Finset.sum_eq_single (f P)]
  · rw [hf, FractionalIdeal.count_pow_self]
  · intro Q _ hQ
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime, mul_zero]
    rintro rfl
    exact hQ (hf Q).symm
  · intro h
    rw [hs _ h, pow_zero, FractionalIdeal.count_one]

end general

theorem exists_numerator : ∀ (E : Type) [Field E] [NumberField E] (σ : 𝓞 E ≃+* 𝓞 E) (cp : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E)), (∀ x, σ (σ x) = x) → (∀ Q x, x ∈ (cp Q).asIdeal ↔ σ x ∈ Q.asIdeal) → ∀ δ : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support δ).Finite → (∀ Q, δ (cp Q) = -δ Q) → ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ cc.map (σ : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0) ∧ (∀ b : 𝓞 E, (∀ Q, δ Q ≠ 0 → b ∉ Q.asIdeal) → cc ⊔ Ideal.span {b} = ⊤) ∧ ∀ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ WithZero.exp (-δ Q)) → J * idlE (cc.map (σ : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  intro E _ _ σ cp hσ hcp δ hfin hanti
  have hinv : ∀ Q, cp (cp Q) = Q := fun Q => by
    ext x
    rw [hcp, hcp, hσ]
  have hmap : ∀ Q : HeightOneSpectrum (𝓞 E),
      Q.asIdeal.map (σ : 𝓞 E →+* 𝓞 E) = (cp Q).asIdeal := fun Q => by
    ext x
    rw [hcp, Ideal.mem_map_iff_of_surjective (σ : 𝓞 E →+* 𝓞 E) σ.surjective]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hσ] using hy
    · intro h
      exact ⟨σ x, h, hσ x⟩
  set s := hfin.toFinset with hsdef
  have hs : ∀ Q, Q ∉ s → (δ Q).toNat = 0 := fun Q hQ => by
    have : δ Q = 0 := by simpa [hsdef] using hQ
    simp [this]
  set cc : Ideal (𝓞 E) := ∏ Q ∈ s, Q.asIdeal ^ (δ Q).toNat with hcc
  have hbar : cc.map (σ : 𝓞 E →+* 𝓞 E) = ∏ Q ∈ s, (cp Q).asIdeal ^ (δ Q).toNat := by
    have := map_prod (Ideal.mapHom (σ : 𝓞 E →+* 𝓞 E)) (fun Q => Q.asIdeal ^ (δ Q).toNat) s
    simp only [map_pow, Ideal.mapHom_apply, hmap] at this
    exact this
  have h0 : cc ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ Q.ne_bot
  have h0' : cc.map (σ : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    rw [hbar]
    exact Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (cp Q).ne_bot
  have hc : ∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0 :=
    fun Q => by
      rw [← Int.ofNat_toNat]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) id (fun _ => rfl) hs Q
  have hc' : ∀ Q, FractionalIdeal.count E Q
      ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = max (-δ Q) 0 :=
    fun Q => by
      rw [← hanti, ← Int.ofNat_toNat, hbar]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) cp hinv hs Q
  refine ⟨cc, h0, sup_eq_top_of h0 fun v h1 h2 => ?_, hc, fun b hb => sup_eq_top_of h0 fun v h1 h2 => ?_,
    fun J hJ => ?_⟩
  · have a1 := one_le_count E h0 v h1
    have a2 := one_le_count E h0' v h2
    rw [hc] at a1
    rw [hc'] at a2
    omega
  · have a1 := one_le_count E h0 v h1
    rw [hc] at a1
    exact hb v (by omega) ((Ideal.span_singleton_le_iff_mem _).1 h2)
  · have f0 : (cc : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h0
    have f0' : ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 h0'
    have hJD : J = (((cc : FractionalIdeal (𝓞 E)⁰ E) *
        ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :
          FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      ext x
      rw [hJ, FractionalIdeal.mem_coe, mem_iff_valuation E (mul_ne_zero f0 (inv_ne_zero f0'))]
      refine forall_congr' fun Q => ?_
      rw [FractionalIdeal.count_mul E Q f0 (inv_ne_zero f0'), FractionalIdeal.count_inv, hc, hc']
      have : max (δ Q) 0 + -max (-δ Q) 0 = δ Q := by omega
      rw [this]
    have hid : ∀ I : Ideal (𝓞 E),
        idlE I = ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := fun _ => rfl
    rw [hJD, hid, hid, ← FractionalIdeal.coe_mul, inv_mul_cancel_right₀ f0']

end GlobalTheory.NumeratorIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisorStatement
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numeratorIdeal_of_antiInvariant_divisor : ∀ (E : Type) [Field E] [NumberField E] (σ : 𝓞 E ≃+* 𝓞 E) (cp : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E)), (∀ x, σ (σ x) = x) → (∀ Q x, x ∈ (cp Q).asIdeal ↔ σ x ∈ Q.asIdeal) → ∀ δ : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support δ).Finite → (∀ Q, δ (cp Q) = -δ Q) → ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ cc.map (σ : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0) ∧ (∀ b : 𝓞 E, (∀ Q, δ Q ≠ 0 → b ∉ Q.asIdeal) → cc ⊔ Ideal.span {b} = ⊤) ∧ ∀ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ WithZero.exp (-δ Q)) → J * idlE (cc.map (σ : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  first | exact @GlobalTheory.NumeratorIdeal.exists_numerator | exact GlobalTheory.NumeratorIdeal.exists_numerator | (intros; apply GlobalTheory.NumeratorIdeal.exists_numerator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem isLattice_of_eq_span_frac_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) (M N : Submodule (𝓞 K) V)
    (h : M = Submodule.span (𝓞 K) {x | ∃ a ∈ I, ∃ y ∈ N, x = (a : K) • y})
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K N := by
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ (0 : K) := by
    by_contra hc
    push_neg at hc
    exact hI (FractionalIdeal.eq_zero_iff.2 hc)
  refine ⟨?_, ?_⟩
  · let f : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V a).restrictScalars (𝓞 K)
    have hf : Function.Injective f := fun x y hxy => smul_right_injective V ha0 hxy
    have hle : N.map f ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      rw [h]
      exact Submodule.subset_span ⟨a, haI, y, hy, rfl⟩
    have hfg : (N.map f).FG := Submodule.FG.of_le hM.fg hle
    exact Submodule.fg_of_fg_map_injective f hf hfg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isLattice_comap_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W]
    [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (e : W ≃ₗ[K] V) (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.comap ((e : W →ₗ[K] V).restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective ((e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.injective ?_
    rw [Submodule.map_comap_eq_of_surjective
      (f := (e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.surjective]
    exact hN.fg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem nuLat_comap_isLattice : ∀ (D : D7) (L : SizeData₂ D), Formalism.BasicNotions.DV.NprimeDef D L → ∀ u, Submodule.IsLattice D.what₂.LL (D.div.Nu u).L → ∀ (d : ℕ) (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Submodule.IsLattice D.what₂.LL ((L.NuLat u).comap ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))) := by
  intro D L hdef u hL d e
  have hI : Formalism.BasicNotions.DV.Iu D L u ≠ 0 := by
    unfold Formalism.BasicNotions.DV.Iu
    rw [Finset.prod_ne_zero_iff]
    intro w _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq w).ne_bot)
  exact isLattice_comap_equiv e _
    (isLattice_of_eq_span_frac_smul (Formalism.BasicNotions.DV.Iu D L u) hI _ _ (hdef u) hL)

end GlobalTheory.ColRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem card_sq_mod_prime : ∀ (p : ℕ), p.Prime → p % 4 = 3 →
    2 * Fintype.card (Sq p) + 1 = p ∧ Odd (Fintype.card (Sq p)) := by
  intro p hp h4
  obtain ⟨e, -⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum] at hc
  have h2 : Fintype.card (Finset.Ico 1 p : Finset ℕ) = p - 1 := by
    simp
  rw [h2] at hc
  have hp2 := hp.two_le
  have hsum : 2 * Fintype.card (Sq p) + 1 = p := by omega
  refine ⟨hsum, ?_⟩
  rw [Nat.odd_iff]
  omega

end GlobalTheory.CMModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrimeStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three : ∀ (p : ℕ), p.Prime → p % 4 = 3 → 2 * Fintype.card (Sq p) + 1 = p ∧ Odd (Fintype.card (Sq p)) := by
  first | exact @GlobalTheory.CMModel.card_sq_mod_prime | exact GlobalTheory.CMModel.card_sq_mod_prime | (intros; apply GlobalTheory.CMModel.card_sq_mod_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPull

theorem weilIs_diag_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left),
    IsAbelianScheme A → P.IsLB → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    Out.WeilIs (G2 A) P n (lift u u) (lift v v) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n u v c' →
    c = c' := by
  intro S A _ _ P hA hP n T u v c c' h h'
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hw : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1) (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    have h1 : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1).IsLB := LB.isLB_linComb hL _ _
    refine (CechPic.cls_eq_iff h1 hL).1 ?_
    rw [CechPic.cls_lbPow hL, one_smul]
  have hu : u ≫ lift (𝟙 A) (𝟙 A) = lift u u := by simp
  have hv : v ≫ lift (𝟙 A) (𝟙 A) = lift v v := by simp
  rw [← hu, ← hv] at h
  have h2 := WeilIsogeny.weilIs_pull_hom globalFns_holds hA hL hP (lift (𝟙 A) (𝟙 A)) hw h
  rw [Nat.cast_one, Int.mul_one] at h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hA hL h2 h'

end GlobalTheory.DiagPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_diagonal_pullback_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift u u) (lift v v) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n u v c' → c = c' := by
  first | (exact @GlobalTheory.DiagPull.weilIs_diag_eq) | (exact GlobalTheory.DiagPull.weilIs_diag_eq) | (intros; apply GlobalTheory.DiagPull.weilIs_diag_eq  <;> assumption)
end
end
