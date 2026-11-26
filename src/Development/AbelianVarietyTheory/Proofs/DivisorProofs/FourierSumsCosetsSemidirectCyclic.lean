module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Formalism.SatakeDualWeyl.StatementC
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import GroundTheory.LocalFields.Interface
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetFourier

theorem star_eq_inv_of_pow_eq_one {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n = 1) :
    star w = w⁻¹ := by
  have h1 : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hn
  have h2 : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.inv_def, h2]; simp [Complex.star_def]

theorem geom_sum_root_of_unity {w : ℂ} {n : ℕ} (hw : w ^ n = 1) :
    ∑ a ∈ Finset.range n, w ^ a = if w = 1 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, hw]; simp

theorem fourier_coset_sums : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  intro G Γ _ _ _ _ φ s hs ζ hζ
  have hn0 : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  let u : ℂˣ := Units.mk0 ζ (hζ.ne_zero hn0)
  have hu : orderOf u ∣ orderOf s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hord]; ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]
    exact hζ.pow_eq_one
  let η₀ : Γ →* ℂˣ := monoidHomOfForallMemZpowers hs hu
  have hη₀s : η₀ s = u := monoidHomOfForallMemZpowers_apply_gen hs hu
  have hinj : Function.Injective η₀ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs t)
    rw [map_zpow, hη₀s] at ht
    have hk : ζ ^ k = 1 := by
      have := congrArg Units.val ht
      simpa [u, Units.val_zpow_eq_zpow_val] using this
    rw [hζ.zpow_eq_one_iff_dvd] at hk
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact hk
  let η : G ⋊[φ] Γ →* ℂˣ := η₀.comp rightHom
  have hηx : ∀ x, η x = η₀ x.right := fun x => rfl
  have hpow : ∀ x, (η x : ℂ) ^ Nat.card Γ = 1 := by
    intro x
    rw [hηx, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']; simp
  have hstar : ∀ x, star (η x : ℂ) = (η x : ℂ)⁻¹ := fun x => star_eq_inv_of_pow_eq_one hn0 (hpow x)
  have hone : ∀ x : G ⋊[φ] Γ, (η x : ℂ)⁻¹ = 1 ↔ x.right = 1 := by
    intro x
    rw [inv_eq_one, Units.val_eq_one, hηx, ← map_one η₀, hinj.eq_iff]
  have hzeta : ∀ x : G ⋊[φ] Γ, ζ * (η x : ℂ)⁻¹ = 1 ↔ x.right = s := by
    intro x
    have hne : (η x : ℂ) ≠ 0 := (η x).ne_zero
    rw [mul_inv_eq_one₀ hne, eq_comm, hηx]
    have : ζ = ((η₀ s : ℂˣ) : ℂ) := by rw [hη₀s]; rfl
    rw [this, Units.val_inj, hinj.eq_iff]
  refine ⟨η, fun g => by simp [η], by rw [show η (inr s) = η₀ s from by simp [η], hη₀s]; rfl, ?_⟩
  intro X Y
  haveI : Fintype G := Fintype.ofFinite G
  let e : G ⋊[φ] Γ ≃ G × Γ :=
    ⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  haveI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv (G × Γ) e.symm

  have key : ∀ (c : ℂ) (t : Γ), (∀ x : G ⋊[φ] Γ, c * (η x : ℂ)⁻¹ = 1 ↔ x.right = t) →
      c ^ Nat.card Γ = 1 →
      ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) =
        (Nat.card Γ : ℂ) * ∑ g : G, X ⟨g, t⟩ * star (Y ⟨g, t⟩) := by
    intro c t hct hc
    simp_rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ x : G ⋊[φ] Γ, ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * (X x * star (Y x * (η x : ℂ) ^ a))
        = X x * star (Y x) * (if x.right = t then (Nat.card Γ : ℂ) else 0) := by
      intro x
      have : ∀ a, c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (c * (η x : ℂ)⁻¹) ^ a := by
        intro a
        rw [star_mul', star_pow, hstar, mul_pow]; ring
      simp_rw [this]
      rw [← Finset.mul_sum, geom_sum_root_of_unity (by rw [mul_pow, inv_pow, hc, hpow, inv_one, one_mul])]
      simp only [hct]
    simp_rw [hterm]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [e, mul_comm]
  refine ⟨?_, ?_⟩
  · have := key 1 1 (fun x => by rw [one_mul]; exact hone x) (one_pow _)
    simp only [one_pow, one_mul] at this
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  · rw [key ζ s hzeta hζ.pow_eq_one, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    have : (inl g * inr s : G ⋊[φ] Γ) = ⟨g, s⟩ := by ext <;> simp
    rw [this]

end GlobalTheory.Shin.CosetFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclicStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzCovol

open NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def embPlace : (F →+* ℝ) ≃ {w : InfinitePlace F // IsReal w} where
  toFun τ := ⟨mk (Complex.ofRealHom.comp τ), IsTotallyReal.isReal _⟩
  invFun w := embedding_of_isReal w.2
  left_inv τ := by
    have h : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
      isReal_of_mk_isReal (IsTotallyReal.isReal _)
    ext x
    apply Complex.ofReal_injective
    rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal h]
    rfl
  right_inv w := by
    apply Subtype.ext
    have : Complex.ofRealHom.comp (embedding_of_isReal w.2) = embedding w.1 := by
      ext x; simp
    simp only [this, mk_embedding]

theorem embPlace_symm_apply (w : {w : InfinitePlace F // IsReal w}) :
    (embPlace.symm w : F →+* ℝ) = embedding_of_isReal w.2 := rfl

instance isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩

def toMixed : RSp F ≃ₗ[ℝ] mixedSpace F where
  toFun x := (fun w => x (embPlace.symm w), 0)
  invFun p := WithLp.toLp 2 (fun τ => p.1 (embPlace τ))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by ext τ; simp
  right_inv p := by
    refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
    simp

theorem toMixed_remb (a : F) : toMixed (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
  simp [toMixed, embPlace_symm_apply]

theorem measurePreserving_toMixed :
    MeasurePreserving (toMixed (F := F)).toContinuousLinearEquiv volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (F →+* ℝ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
    (embPlace (F := F))
  have h3 : MeasurePreserving (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
      (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) volume volume := by
    refine ⟨measurable_id.prodMk measurable_const, ?_⟩
    rw [Measure.volume_eq_prod, show (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac 0 from Measure.volume_pi_eq_dirac 0, Measure.prod_dirac]
  have h := h3.comp (h2.comp h1)
  have he : ⇑(toMixed (F := F)).toContinuousLinearEquiv =
      (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
        (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
        (embPlace (F := F))) ∘ WithLp.ofLp := by
    funext x
    refine Prod.ext (funext fun w => ?_) rfl
    simp [toMixed, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact h

end GlobalTheory.LipschitzCovol

open scoped Classical in
open GlobalTheory.LipschitzCovol in
theorem GlobalTheory.LipschitzCovol.covolume_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)],
    ZLattice.covolume (latOf N) = covol N := by
  intro F _ _ _ N hN _ _
  have hmem : ∀ x : RSp F, x ∈ latOf N ↔
      toMixed x ∈ mixedEmbedding.idealLattice F (Units.mk0 N hN) := by
    intro x
    rw [mem_latOf, mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, by simpa using ha, (toMixed_remb a).symm⟩
    · rintro ⟨a, ha, h⟩
      refine ⟨a, by simpa using ha, toMixed.injective ?_⟩
      rw [toMixed_remb, h]
  have hL : latOf N = ZLattice.comap ℝ (mixedEmbedding.idealLattice F (Units.mk0 N hN))
      (toMixed (F := F)).toContinuousLinearEquiv.toLinearMap :=
    Submodule.ext fun x => hmem x
  have key := ZLattice.covolume_comap (mixedEmbedding.idealLattice F (Units.mk0 N hN)) volume volume
    (measurePreserving_toMixed (F := F))
  have hc := covol_eq_covolume (Units.mk0 N hN)
  rw [Units.val_mk0] at hc
  rw [hc, ← key]
  congr 1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImageStatement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)], ZLattice.covolume (latOf N) = covol N := by
  first | exact @GlobalTheory.LipschitzCovol.covolume_latOf | exact GlobalTheory.LipschitzCovol.covolume_latOf | (intros; apply GlobalTheory.LipschitzCovol.covolume_latOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

section
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem inner_remb_eq_trace (a b : F) :
    ⟪remb F a, remb F b⟫ = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by
  rw [GlobalTheory.trace_eq_sum_realEmbeddings, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [map_mul, mul_comm]

theorem remb_mem_dual_latOf_iff (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) (ν : F) :
    remb F ν ∈ Formalism.H.dual (latOf N) ↔ ν ∈ FractionalIdeal.dual ℤ ℚ N := by
  rw [Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule, FractionalIdeal.mem_dual hN]
  constructor
  · intro h a ha
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (h (remb F a) ((mem_latOf N _).mpr ⟨a, ha, rfl⟩))
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    have : ((z : ℚ) : ℝ) = ((Algebra.trace ℚ F (ν * a) : ℚ) : ℝ) := by
      have h2 : ((z : ℤ) : ℝ) = ⟪remb F ν, remb F a⟫ := by simpa using hz
      rw [inner_remb_eq_trace] at h2
      exact_mod_cast h2
    exact_mod_cast this
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := (mem_latOf N y).mp hy
    obtain ⟨z, hz⟩ := h a ha
    rw [Algebra.traceForm_apply] at hz
    refine Submodule.mem_one.mpr ⟨z, ?_⟩
    rw [show (innerₗ (RSp F)) (remb F ν) (remb F a) = ⟪remb F ν, remb F a⟫ from rfl,
      inner_remb_eq_trace, ← hz]
    simp

theorem exists_remb_eq_of_mem_dual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F)
    (N : FractionalIdeal (𝓞 F)⁰ F) (hbN : ∀ i, b i ∈ N) (μ : RSp F)
    (hμ : μ ∈ Formalism.H.dual (latOf N)) : ∃ ν : F, remb F ν = μ := by
  set B := Algebra.traceForm ℚ F
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ F
  set b' := B.dualBasis hB b
  have hdel : ∀ i j, Algebra.trace ℚ F (b' j * b i) = if i = j then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
    rwa [Algebra.traceForm_apply] at this
  have hc : ∀ i, ∃ z : ℤ, ⟪μ, remb F (b i)⟫ = z := fun i => by
    have := (LinearMap.BilinForm.mem_dualSubmodule _).mp hμ (remb F (b i))
      ((mem_latOf N _).mpr ⟨b i, hbN i, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp this
    exact ⟨z, by simpa using hz.symm⟩
  choose c hc using hc
  set ν : F := ∑ j, (c j : ℚ) • b' j
  have hνb : ∀ i, ⟪remb F ν, remb F (b i)⟫ = c i := fun i => by
    rw [inner_remb_eq_trace]
    have : Algebra.trace ℚ F (ν * b i) = c i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ν, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hdel, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this]; simp
  have hind : LinearIndependent ℝ (fun i => remb F (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun w => ⟪w, remb F (b' j)⟫) hg
    simp only [sum_inner, real_inner_smul_left, inner_remb_eq_trace, inner_zero_left] at this
    simp only [mul_comm (b _) (b' j), hdel] at this
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi]; simp) (by simp)] at this
    simpa using this
  have hcard : Fintype.card ι = Module.finrank ℝ (RSp F) := by
    rw [finrank_euclideanSpace, GlobalTheory.card_realEmbeddings, Module.finrank_eq_card_basis b]
  haveI : Nonempty ι := b.index_nonempty
  let E := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hz : innerₛₗ ℝ (μ - remb F ν) = 0 := E.ext fun i => by
    simp [E, inner_sub_left, hνb, hc]
  have h0 := LinearMap.congr_fun hz (μ - remb F ν)
  have h1 : ⟪μ - remb F ν, μ - remb F ν⟫ = 0 := by
    rw [LinearMap.zero_apply] at h0; exact h0
  rw [inner_self_eq_zero, sub_eq_zero] at h1
  exact ⟨ν, h1.symm⟩

end

theorem dual_latOf_eq_latOf_traceDual (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  classical
  ext μ
  constructor
  · intro hμ
    rw [mem_latOf]
    let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hbN : ∀ i, basisOfFractionalIdeal F I i ∈ N := fun i => by
      have := (mem_span_basisOfFractionalIdeal F (I := I) (x := basisOfFractionalIdeal F I i)).mp
        (Submodule.subset_span ⟨i, rfl⟩)
      simpa [I] using this
    obtain ⟨ν, hν⟩ := exists_remb_eq_of_mem_dual (basisOfFractionalIdeal F I) N hbN μ hμ
    subst hν
    exact ⟨ν, (remb_mem_dual_latOf_iff N hN ν).mp hμ, rfl⟩
  · intro hμ
    obtain ⟨ν, hν, rfl⟩ := (mem_latOf _ μ).mp hμ
    exact (remb_mem_dual_latOf_iff N hN ν).mpr hν

end GlobalTheory.LipschitzTR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDualStatement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  first | exact @GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | exact GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | (intros; apply GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
noncomputable section

open Polynomial Formalism.UG

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL_of {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]; exact hx

def sigO (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  σ.restrict (intL L) (intL L) fun _ hx => mem_intL_of hσ hx

def piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : intL L :=
  ⟨ϖ, by
    change Valued.v ϖ ≤ 1
    rw [h.2.2.2.1]
    exact_mod_cast (WithZero.coe_le_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1))⟩

@[simp] theorem coe_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : ((piO h : intL L) : L) = ϖ := rfl

def unitFil {R : Type} [CommRing R] (I : Ideal R) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : ((a * b : Rˣ) : R) - 1 = (a : R) * ((b : R) - 1) + ((a : R) - 1) := by push_cast; ring
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [e]; exact I.add_mem (I.mul_mem_left _ hb) ha
  inv_mem' := fun {a} ha => by
    have e : ((a⁻¹ : Rˣ) : R) - 1 = -((a⁻¹ : Rˣ) : R) * ((a : R) - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul, mul_one]; ring
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [e]; exact I.mul_mem_left _ ha

theorem mem_unitFil {R : Type} [CommRing R] {I : Ideal R} {u : Rˣ} : u ∈ unitFil I ↔ (u : R) - 1 ∈ I := Iff.rfl

def piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (m : ℕ) :
    Ideal (AdjoinRoot P.1) :=
  Ideal.span {algebraMap (intL L) (AdjoinRoot P.1) (piO h) ^ m}

def filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (m : ℕ) :
    Subgroup (AdjoinRoot P.1)ˣ :=
  unitFil (piPow h P m)

theorem mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} {h : IsUnramInv ϖ σ q} {P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)} {m : ℕ}
    {u : (AdjoinRoot P.1)ˣ} : u ∈ filt h P m ↔ (u : AdjoinRoot P.1) - 1 ∈ piPow h P m := Iff.rfl

theorem piPow_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    Antitone (piPow h P) := fun a b hab => by
  unfold piPow
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow _ hab

theorem filt_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    Antitone (filt h P) := fun a b hab _ hu => piPow_antitone h P hab hu

theorem filt_zero {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    filt h P 0 = ⊤ := by
  ext u; simp [filt, mem_unitFil, piPow]

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem piO_mem_of_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {M : Ideal (intL L)}
    (hM : M.IsMaximal) : piO h ∈ M := by
  by_contra hϖ
  obtain ⟨y, i, hi, e⟩ := hM.exists_inv hϖ
  have hlt : Valued.v ((y : L) * ϖ) < 1 := by
    rw [map_mul, h.2.2.2.1]
    have hy : Valued.v (y : L) ≤ 1 := y.2
    calc Valued.v (y : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
  have hi1 : (i : L) = 1 - (y : L) * ϖ := by
    have := congrArg Subtype.val e
    simp only [Subring.coe_add, Subring.coe_mul, coe_piO, OneMemClass.coe_one] at this
    linear_combination this
  have hv : Valued.v (i : L) = 1 := by rw [hi1]; exact Valuation.map_one_sub_of_lt _ hlt
  have hi0 : (i : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hinv : (i : L)⁻¹ ∈ intL L := by
    change Valued.v ((i : L)⁻¹) ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hu : IsUnit i := isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hi0])⟩
  exact hM.ne_top (M.eq_top_of_isUnit_mem hi hu)

theorem isUnit_one_add_piO_mul {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (a : AdjoinRoot P.1) :
    IsUnit (1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a) := by
  by_contra hn
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  letI : Module.Finite (intL L) (AdjoinRoot P.1) := .of_basis (AdjoinRoot.powerBasis' P.2.1).basis
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap (intL L) (AdjoinRoot P.1))
    (RingHom.IsIntegral.of_finite (RingHom.finite_algebraMap.mpr inferInstance)) M
  have hϖ : algebraMap (intL L) (AdjoinRoot P.1) (piO h) ∈ M := piO_mem_of_isMaximal h hmax
  have h1 : 1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a ∈ M := hxM (Ideal.mem_span_singleton_self _)
  have : (1 : AdjoinRoot P.1) ∈ M := by
    have := M.sub_mem h1 (M.mul_mem_right a hϖ)
    simpa using this
  exact hM.ne_top ((Ideal.eq_top_iff_one M).2 this)

theorem isUnit_of_sub_one_mem {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) {m : ℕ} (hm : 1 ≤ m) {x : AdjoinRoot P.1} (hx : x - 1 ∈ piPow h P m) :
    IsUnit x := by
  have hx1 : x - 1 ∈ piPow h P 1 := piPow_antitone h P hm hx
  unfold piPow at hx1
  rw [pow_one, Ideal.mem_span_singleton'] at hx1
  obtain ⟨a, ha⟩ := hx1
  have := isUnit_one_add_piO_mul h P a
  rwa [mul_comm, ha, add_sub_cancel] at this

end GlobalTheory.NormEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernel
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

theorem mul_im_pos_of_sign_mul_pos {w : ℂ} {t : ℝ} (h : 0 < (SignType.sign w.im : ℝ) * t) :
    0 < t * w.im := by
  rcases lt_trichotomy w.im 0 with hw | hw | hw
  · rw [sign_neg hw] at h
    simp at h
    nlinarith
  · rw [hw, sign_zero] at h
    simp at h
  · rw [sign_pos hw] at h
    simp at h
    positivity

theorem norm_lipschitzOneVariableKernel_le (k : ℕ) (w : ℂ) (t : ℝ) :
    ‖phi1 k w t‖ ≤ |t| ^ (k - 1) * Real.exp (-(2 * Real.pi * |w.im|) * |t|) := by
  unfold phi1
  split_ifs with h
  · have hp := mul_im_pos_of_sign_mul_pos h
    have habs : |t| * |w.im| = t * w.im := by rw [← abs_mul]; exact abs_of_pos hp
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * w).re = -(2 * Real.pi * |w.im|) * |t| := by
      simp [Complex.mul_re]
      linear_combination (-2 * Real.pi) * habs
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  · simp only [norm_zero]
    positivity

theorem abs_pow_mul_exp_le (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| ^ n * Real.exp (-a * |t|) ≤ (n.factorial * (2 / a) ^ n) * Real.exp (-(a / 2) * |t|) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * |t|) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |t| ^ n ≤ n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|) := by
    calc |t| ^ n = (2 / a) ^ n * (a / 2 * |t|) ^ n := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / a) ^ n * (Real.exp (a / 2 * |t|) * n.factorial) := by gcongr
      _ = _ := by ring
  calc |t| ^ n * Real.exp (-a * |t|)
      ≤ (n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|)) * Real.exp (-a * |t|) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem continuous_lipschitzOneVariableKernel {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w.im ≠ 0) : Continuous (phi1 k w) := by
  have hg : Continuous fun t : ℝ =>
      ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) := by fun_prop
  show Continuous fun t => if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) else 0
  refine continuous_if (fun a ha => ?_) hg.continuousOn continuous_const.continuousOn
  have h0 := frontier_lt_subset_eq (continuous_const (y := (0 : ℝ)))
    (continuous_const.mul continuous_id (f := fun _ : ℝ => (SignType.sign w.im : ℝ))) ha
  simp only [Set.mem_setOf_eq, id] at h0
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exfalso
      rcases lt_trichotomy w.im 0 with h' | h' | h'
      · rw [sign_neg h'] at h; norm_num at h
      · exact hw h'
      · rw [sign_pos h'] at h; norm_num at h
    · exact h
  subst ha0
  have : k - 1 ≠ 0 := by omega
  simp [this]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem norm_le_sum_abs {F : Type} [Field F] [NumberField F] (v : RSp F) :
    ‖v‖ ≤ ∑ τ, |v τ| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun τ => |v τ|) fun _ _ => abs_nonneg _

theorem continuous_and_isBigO_rpow_Phi (F : Type) [Field F] [NumberField F] (k : ℕ) (hk : 2 ≤ k)
    (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  refine ⟨?_, fun b => ?_⟩
  · unfold Phi
    exact continuous_finsetProd _ fun τ _ =>
      (continuous_lipschitzOneVariableKernel hk (hz τ)).comp ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ τ, c ≤ 2 * Real.pi * |(z τ).im| / 2 := by
    rcases isEmpty_or_nonempty (F →+* ℝ) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ0, hτ0⟩ := Finite.exists_min (fun τ => 2 * Real.pi * |(z τ).im| / 2)
      exact ⟨_, by have := abs_pos.2 (hz τ0); positivity, hτ0⟩
  set K : ℝ := ∏ τ, (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) with hK
  have hbound : ∀ v : RSp F, ‖Phi k z v‖ ≤ K * Real.exp (-c * ‖v‖) := by
    intro v
    have hfac : ∀ τ, ‖phi1 k (z τ) (v τ)‖ ≤
        (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|) := by
      intro τ
      have ha : 0 < 2 * Real.pi * |(z τ).im| := by have := abs_pos.2 (hz τ); positivity
      refine (norm_lipschitzOneVariableKernel_le k (z τ) (v τ)).trans ((abs_pow_mul_exp_le (k - 1) ha (v τ)).trans ?_)
      gcongr
      have := hcle τ
      nlinarith [abs_nonneg (v τ)]
    calc ‖Phi k z v‖ = ∏ τ, ‖phi1 k (z τ) (v τ)‖ := by unfold Phi; rw [norm_prod]
      _ ≤ ∏ τ, ((((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => hfac τ
      _ = K * Real.exp (-c * ∑ τ, |v τ|) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ ≤ K * Real.exp (-c * ‖v‖) := by
        have hK0 : 0 ≤ K := Finset.prod_nonneg fun τ _ => by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [norm_le_sum_abs v])) hK0
  have h1 : Phi k z =O[Filter.cocompact (RSp F)] fun v : RSp F => Real.exp (-c * ‖v‖) :=
    Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound v)
  have h2 : (fun v : RSp F => Real.exp (-c * ‖v‖)) =O[Filter.cocompact (RSp F)]
      fun v : RSp F => ‖v‖ ^ (-b) :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-b)).isBigO.comp_tendsto tendsto_norm_cocompact_atTop
  exact h1.trans h2

end GlobalTheory.LipschitzTR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernelStatement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  first | exact @GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | exact GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | (intros; apply GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem phi_zero (w : ℂ) : phi 0 w = w⁻¹ ^ 2 := by
  simp [phi]

theorem hTrans_zero_neg (ν y : ℝ) : hTrans 0 ν (-y) = hTrans 0 (-ν) y := by
  unfold hTrans
  conv_lhs => rw [← MeasureTheory.integral_neg_eq_self]
  congr 1; funext t
  simp only [phi_zero, ofReal_neg]
  congr 1
  · rw [show -(t : ℂ) + -(y : ℂ) * I = -((t : ℂ) + (y : ℂ) * I) by ring, inv_neg, neg_sq]
  · congr 1; ring

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  have : Nonempty (F →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := this
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem abs_norm_eq_prod [IsTotallyReal F] (ν : F) :
    ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) = ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ) := by
  have h := prod_emb ν
  have h' : ((Algebra.norm ℚ ν : ℚ) : ℝ) = ∏ τ : Emb F, τ ν := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_prod, h]; push_cast; rfl
  rw [h', Finset.abs_prod, Complex.ofReal_prod]

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

def toQ (𝔞 𝔟 : Frac F) : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → Quotient (qRel 𝔞 𝔟) :=
  fun s => Quotient.mk _ ⟨(s.2.1.1, s.1.out.1), s.2.1.2.1, s.1.out.2.1, s.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨c, ν⟩ ⟨c', ν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  dsimp only at h1 h2
  have hc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨ε, h2⟩
  subst hc
  have hne : c.out.1 ≠ 0 := c.out.2.2
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h3 : (((ε : 𝓞 F) : F) - 1) * c.out.1 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : ν = ν' := Subtype.ext (Subtype.ext h1.symm)
  subst this
  rfl

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p => ?_
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  obtain ⟨τ₀⟩ := emb_nonempty (F := F)
  have hνb : ν * b ≠ 0 := by
    intro h0; have := hpos τ₀; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul hνb
  set c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := Quotient.mk _ ⟨b, hb, hb0⟩ with hcdef
  obtain ⟨ε, hε⟩ := Quotient.exact (Quotient.out_eq c : Quotient.mk _ c.out = Quotient.mk _ ⟨b, hb, hb0⟩)
  dsimp only at hε
  have hmem : ((ε : 𝓞 F) : F) * ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
    have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hν
    rw [Algebra.smul_def] at this
    exact this
  have hne : ((ε : 𝓞 F) : F) * ν ≠ 0 := by
    refine mul_ne_zero ?_ hν0
    intro h0
    have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hprod : ((ε : 𝓞 F) : F) * ν * c.out.1 = ν * b := by rw [hε]; ring
  refine ⟨⟨c, ⟨⟨((ε : 𝓞 F) : F) * ν, hmem, hne⟩, fun τ => by rw [hprod]; exact hpos τ⟩⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, hε⟩
  show ν = _ * (((ε : 𝓞 F) : F) * ν)
  rw [← mul_assoc, unit_inv_mul, one_mul]

theorem tsum_qClass_eq [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hS : Summable (qClass 𝔞 𝔟 2 z)) :
    ∑' c, qClass 𝔞 𝔟 2 z c = ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
        if ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1) then qTerm 𝔞 2 z (ν.1, c.out.1) else 0 := by
  set e := Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩ with he
  have hS' : Summable (qClass 𝔞 𝔟 2 z ∘ e) := e.summable_iff.2 hS
  have h1 : ∑' c, qClass 𝔞 𝔟 2 z c = ∑' p, qClass 𝔞 𝔟 2 z (e p) := (e.tsum_eq _).symm
  have h2 : ∑' p, qClass 𝔞 𝔟 2 z (e p) = ∑' c, ∑' ν, qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) := hS'.tsum_sigma
  rw [h1, h2]
  refine tsum_congr fun c => ?_
  have h3 := tsum_subtype {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) | ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}
    (fun ν => qTerm 𝔞 2 z (ν.1, c.out.1))
  have h4 : ∀ ν : {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)},
      qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) = qTerm 𝔞 2 z (ν.1.1, c.out.1) := fun ν => by
    rw [he]; exact qClass_mk 𝔞 𝔟 2 z _
  rw [tsum_congr h4]
  refine h3.trans (tsum_congr fun ν => ?_)
  rw [Set.indicator_apply]
  rfl

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem kFac_zero_mul : kFac (F := F) 0 * (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * (-4 * (Real.pi : ℂ) ^ 2) = 1 := by
    rw [inv_pow, mul_pow, mul_pow, I_sq]
    field_simp
    ring
  unfold kFac
  simp only [mul_zero, cpow_zero, mul_one, Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, h1, one_pow]

theorem dF_pos : 0 < dF F := abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero F))

theorem nrm_ne_zero (𝔞 : Frac F) : nrm 𝔞 ≠ 0 := by
  unfold nrm
  rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact 𝔞.ne_zero

end GlobalTheory.HeckeTwoExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealsEqOfSpanIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdelicSL2
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_ideal_eq_of_span_of_linearIndependent
    (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ}
    (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)) (h12 : J₁ ≤ J₂)
    (hspan : Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤)
    (hli : LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k))) :
    J₁ = J₂ := by
  refine le_antisymm h12 (fun t ht => ?_)
  have hmem : Ideal.Quotient.mk J₁ t ∈ Submodule.span R
      (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  set s : R ⊗[A] B := ∑ k, c k • ((1 : R) ⊗ₜ[A] v k) with hs
  have hmk : ∀ (J : Ideal (R ⊗[A] B)), Ideal.Quotient.mk J s
      = ∑ k, c k • Ideal.Quotient.mk J ((1 : R) ⊗ₜ[A] v k) := by
    intro J
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have h1 : t - s ∈ J₁ := by
    rw [← Ideal.Quotient.eq, hmk J₁, hc]
  have h2 : s ∈ J₂ := by
    have := J₂.sub_mem ht (h12 h1)
    simpa using this
  have hsum : ∑ k, c k • Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k) = 0 := by
    rw [← hmk J₂, Ideal.Quotient.eq_zero_iff_mem]; exact h2
  have hc0 : ∀ k, c k = 0 := Fintype.linearIndependent_iff.1 hli c hsum
  have hs0 : s = 0 := by simp [hs, hc0]
  rw [hs0, sub_zero] at h1
  exact h1

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideals_eq_of_span_independent : ∀ (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)), J₁ ≤ J₂ → Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k)) → J₁ = J₂ := by
  first | (exact @GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (exact GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (intros; apply GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_surjective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (U : T.affineOpens) : Function.Surjective (kappa A B g I U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (str A B) g) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hle : (⊤ : Subring Γ(pullback (str A B) g, W)) ≤
      (kappa A B g I U).range.comap (I.subschemeι.app W).hom := by
    rw [← hgen, Subring.closure_le]
    rintro _ (⟨z, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1 ⊗ₜ (Scheme.ΓSpecIso (CommRingCat.of B)).hom z, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, one_mul, Iso.hom_inv_id_apply]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      rfl
    · refine ⟨c ⊗ₜ 1, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, mul_one]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE]
      rfl
  intro y
  obtain ⟨x, hx⟩ := I.subschemeι_app_surjective ⟨W, hW⟩ y
  obtain ⟨w, hw⟩ := hle (Subring.mem_top x)
  exact ⟨w, hw.trans hx⟩

end GlobalTheory.HilbAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.affineOpens), Function.Surjective (GlobalTheory.HilbAff.kappa A B g I U) := by
  first | (exact @GlobalTheory.HilbAff.kappa_surjective) | (exact GlobalTheory.HilbAff.kappa_surjective) | (intros; apply GlobalTheory.HilbAff.kappa_surjective  <;> assumption)
end
end
