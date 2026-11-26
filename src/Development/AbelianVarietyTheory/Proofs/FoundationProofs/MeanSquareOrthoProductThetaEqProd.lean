module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PullNorm

noncomputable def coordLin (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc]

theorem coordLin_apply (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (z : VC D N N') : coordLin D T b j z = coordB D T b j z := rfl

theorem coordB_sum (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h1 : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (u : Fin r → ℂ) (k : Fin r) :
    coordB D T b k (∑ j, u j • embV D T (b j)) = u k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coordLin_apply, map_sum]
  simp [coordLin_apply, h1]

theorem parseval (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (z : VC D N N') (h2 : z = ∑ j, coordB D T b j z • embV D T (b j)) :
    (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (z τ i j)) = ((∑ k, ‖coordB D T b k z‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ c : Fin r → ℂ,
      (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) ((∑ k, c k • embV D T (b k)) τ i j))
        = ∑ k, coordB D T b k z * (starRingEnd ℂ) (c k) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coordB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
      Finset.sum_mul, embV]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have h := key fun k => coordB D T b k z
  rw [← h2] at h
  rw [h]
  push_cast
  exact Finset.sum_congr rfl fun k _ => Complex.mul_conj' _

theorem gaussianWeight_thetaTranslate_normSq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) (ω z : ℂ) :
    ‖U1 Λ ω g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)
      = ‖g (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h2 : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem normSq_pullB : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  intro D T N N' r b hΛ h1 h2 g _ hg
  let eC : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    { LinearMap.pi (fun j => coordLin D T b j) with
      invFun := fun u => ∑ j, u j • embV D T (b j)
      left_inv := fun z => (h2 z).symm
      right_inv := fun u => funext fun k => coordB_sum D T b h1 u k }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := eC.restrictScalars ℝ
  have he : ∀ z k, e z k = coordB D T b k z := fun _ _ => rfl
  have hA : ∀ x, x ∈ LaB D T b ↔ ∀ k, e x k ∈ T.abelian₂ := by
    intro x
    constructor
    · intro hx k
      unfold LaB at hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, j, rfl⟩ := hy
        rw [he, ← coordLin_apply, map_smul, coordLin_apply, h1]
        split_ifs
        · simpa using hw
        · simp
      | zero => simp
      | add y z _ _ hy hz => simpa only [map_add, Pi.add_apply] using add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
    · intro hx
      rw [h2 x]
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨_, hx j, j, rfl⟩
  haveI i1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have main := GlobalTheory.LatticeMean.mean_prod_eq_pow T.abelian₂ hΛ
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area T.abelian₂))
    (fun ω hω z => by rw [← gaussianWeight_thetaTranslate_normSq, hg ω hω]) (VC D N N') MeasureTheory.volume r e (LaB D T b) hA
  unfold normSq nrm1Sq
  simp only []
  rw [← main]
  congr 1
  funext z
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Hf, parseval D T b z (h2 z), Complex.div_ofReal_re,
    Complex.ofReal_re, pullB, norm_prod, ← Finset.prod_pow]
  simp only [he]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

end GlobalTheory.PullNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProdStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanSquare_orthoProductTheta_eq_prod : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  first | exact @GlobalTheory.PullNorm.normSq_pullB | exact GlobalTheory.PullNorm.normSq_pullB | (intros; apply GlobalTheory.PullNorm.normSq_pullB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinates
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.OrthoCoord

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem embT_injective : Function.Injective (embT D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embT_indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, c τ * embT D τ x = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp
    (fun τ : D.what₂.Tau => ((embT D τ : D.host.E →+* ℂ) : D.host.E →* ℂ))
    (fun a b hab => embT_injective (RingHom.coe_monoidHom_injective hab))
  rw [Fintype.linearIndependent_iff] at h1
  refine h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply] using h x

theorem coordB_embV (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (j k : Fin r) :
    coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if j = k then 1 else 0 := by
  have h1 := h (∑ i, ∑ i', b k i i' * D.host.conj (b j i i'))
  have h2 := hb k j
  unfold hYY at h2
  rw [h2] at h1
  have h3 : coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) =
      ∑ τ, embT D τ (∑ i, ∑ i', b k i i' * D.host.conj (b j i i')) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coordB, embV, tor0, map_sum, map_mul, emb_conj]
  rw [h3, h1]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

theorem coordB_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (j : Fin r)
    (c : Fin r → ℂ) (v : Fin r → VC D a d) :
    coordB D T b j (∑ k, c k • v k) = ∑ k, c k * coordB D T b j (v k) := by
  let L : VC D a d →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b j
      map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  change L _ = ∑ k, c k * L (v k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

theorem embV_mem_span (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤)
    (A : Matrix (Fin d) (Fin a) D.host.E) :
    embV D (tor0 D cc δ) A ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => D.host.φ₀ (c k : D.host.E), ?_⟩
  funext τ i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [embV, tor0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← h τ, ← map_mul]
  rfl

theorem span_eq_top (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤) :
    Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  let e : D.what₂.Tau → Fin d → Fin a → VC D a d := fun τ i j => Pi.single τ (Pi.single i (Pi.single j 1))
  have hz : ∀ z : VC D a d, z = ∑ τ, ∑ i, ∑ j, z τ i j • e τ i j := by
    intro z
    funext τ i j
    simp [e, Finset.sum_apply, Pi.single_apply, ite_apply]
  have he : ∀ τ i j, f (e τ i j) = 0 := by
    intro τ i j
    refine embT_indep (fun τ => f (e τ i j)) (fun x => ?_) τ
    have h1 : f (embV D (tor0 D cc δ) (Matrix.single i j x)) = 0 := hf (embV_mem_span h cc δ hb _)
    have h2 : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • e τ i j := by
      funext τ' i' j'
      simp only [e, embV, tor0, Matrix.single_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply,
        smul_eq_mul]
      by_cases hi : i = i'
      · by_cases hj : j = j'
        · subst hi hj; simp
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    rw [h2] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul, mul_comm] using h1
  refine LinearMap.ext fun z => ?_
  rw [hz z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, he]

theorem orthonormal_coord : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  intro D h cc δ N N' r b hb
  refine ⟨coordB_embV h.2 cc δ hb.1, fun z => ?_⟩
  have hz : z ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
    rw [span_eq_top h.1 cc δ hb.2]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordB_sum]
  simp [coordB_embV h.2 cc δ hb.1]

end GlobalTheory.OrthoCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinatesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormal_realBasis_complex_coordinates : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  first | exact @GlobalTheory.OrthoCoord.orthonormal_coord | exact GlobalTheory.OrthoCoord.orthonormal_coord | (intros; apply GlobalTheory.OrthoCoord.orthonormal_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable
open Formalism.BasicNotions.TH

namespace GlobalTheory.ExistsHW

open GlobalTheory.TensorHW

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma inf_eig_ne_bot_iff (f : Module.End ℂ V) (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (t : ℂ) :
    N ⊓ f.eigenspace t ≠ ⊥ ↔ Module.End.HasEigenvalue (f.restrict hf) t := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, hx0⟩
    refine ⟨⟨x, hx1⟩, ?_, fun h => hx0 (congrArg Subtype.val h)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (Module.End.mem_eigenspace_iff.1 hx2)
  · rintro ⟨x, hx, hx0⟩
    refine ⟨x, ⟨x.2, ?_⟩, fun h => hx0 (Subtype.ext h)⟩
    rw [Module.End.mem_eigenspace_iff] at hx
    exact Module.End.mem_eigenspace_iff.2 (congrArg Subtype.val hx)

lemma exists_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥)
    (hf : ∀ x ∈ N, f x ∈ N) : ∃ t, N ⊓ f.eigenspace t ≠ ⊥ := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (f.restrict hf)
  exact ⟨t, (inf_eig_ne_bot_iff f N hf t).2 ht⟩

lemma finite_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
    (hf : ∀ x ∈ N, f x ∈ N) : {t | N ⊓ f.eigenspace t ≠ ⊥}.Finite := by
  simp only [inf_eig_ne_bot_iff f N hf]
  exact Module.End.finite_hasEigenvalue _

lemma exists_common {ι : Type*} (E : ι → Module.End ℂ V) (hE : ∀ a b x, E a (E b x) = E b (E a x))
    (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥) (hst : ∀ a, ∀ x ∈ N, E a x ∈ N)
    (s : Finset ι) : ∃ N' : Submodule ℂ V, N' ≤ N ∧ N' ≠ ⊥ ∧ (∀ a, ∀ x ∈ N', E a x ∈ N') ∧
      ∀ a ∈ s, ∃ t, N' ≤ (E a).eigenspace t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨N, le_rfl, hN, hst, by simp⟩
  | insert b s _ ih =>
    obtain ⟨N', h1, h2, h3, h4⟩ := ih
    haveI : FiniteDimensional ℂ N' := Submodule.finiteDimensional_of_le h1
    obtain ⟨t, ht⟩ := exists_eig (E b) N' h2 (h3 b)
    refine ⟨N' ⊓ (E b).eigenspace t, inf_le_left.trans h1, ht, ?_, ?_⟩
    · rintro a x ⟨hx1, hx2⟩
      refine ⟨h3 a x hx1, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [hE, Module.End.mem_eigenspace_iff.1 hx2, map_smul]
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨t, inf_le_right⟩
      · obtain ⟨u, hu⟩ := h4 a ha
        exact ⟨u, inf_le_left.trans hu⟩

end General

lemma eig_rat {p q : ℕ} (M : GKMod p q) (a : Ix p q) {t : ℂ} {v : M.V} (hv0 : v ≠ 0)
    (hv : v ∈ (M.act (Eab a a)).eigenspace t) : ∃ r : ℚ, (r : ℂ) = t := by
  by_contra hr
  have hd := Module.End.eigenspaces_iSupIndep (M.act (Eab a a)) t
  have hle : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
      ⨆ (j : ℂ) (_ : j ≠ t), (M.act (Eab a a)).eigenspace j := by
    refine iSup_le fun μ => le_iSup₂_of_le ((μ a : ℚ) : ℂ) (fun h => hr ⟨μ a, h⟩) fun x hx => ?_
    exact Module.End.mem_eigenspace_iff.2 (mem_wt.1 hx a)
  exact hv0 (Submodule.disjoint_def.1 hd v hv (hle (M.wts v)))

theorem exists_highestWeight (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V)
    (hfd : FiniteDimensional ℂ W) (hW : KStable M.act W) (h0 : W ≠ ⊥) :
    ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  set c : Ix p q → ℂ := fun a => (grad p q a : ℂ) with hc
  set H : Module.End ℂ M.V := M.act (Matrix.diagonal c) with hH
  have hHW : ∀ x ∈ W, H x ∈ W := hW _ (isKC_diag c)
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image _ Complex.re (finite_eig H W hHW)
    (exists_eig H W h0 hHW)
  set N := W ⊓ H.eigenspace t with hN
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le inf_le_left
  have hkill : ∀ a b, posC a b → ∀ x ∈ N, M.act (Eab a b) x = 0 := by
    intro a b hab x hx
    by_contra hne
    have := hmax (t + (c a - c b)) ((Submodule.ne_bot_iff _).2 ⟨_,
      ⟨hW _ (isKC_Eab (same_of_pos hab)) x hx.1, eig_shift hL c (same_of_pos hab) hx.2⟩, hne⟩)
    simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
    linarith [grad_lt hab]
  have hst : ∀ a, ∀ x ∈ N, M.act (Eab a a) x ∈ N := by
    intro a x hx
    refine ⟨hW _ (isKC_Eab (same_refl a)) x hx.1, ?_⟩
    have := eig_shift hL c (same_refl a) hx.2
    rwa [sub_self, add_zero] at this
  have hcomm : ∀ a b x, M.act (Eab a a) (M.act (Eab b b) x) = M.act (Eab b b) (M.act (Eab a a) x) := by
    intro a b x
    rw [lie_apply hL (isKC_Eab (same_refl a)) (isKC_Eab (same_refl b))]
    have : (Eab a a * Eab b b - Eab b b * Eab a a : Mat p q) = 0 := by
      by_cases hab : a = b
      · rw [hab, sub_self]
      · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ hab,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab), sub_self]
    rw [this, map_zero, LinearMap.zero_apply, add_zero]
  obtain ⟨N', h1, h2, -, h4⟩ := exists_common (fun a => M.act (Eab a a)) hcomm N ht hst Finset.univ
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h2
  have : ∀ a, ∃ r : ℚ, M.act (Eab a a) v = (r : ℂ) • v := by
    intro a
    obtain ⟨u, hu⟩ := h4 a (Finset.mem_univ a)
    obtain ⟨r, rfl⟩ := eig_rat M a hv0 (hu hv)
    exact ⟨r, Module.End.mem_eigenspace_iff.1 (hu hv)⟩
  choose μ hμ using this
  exact ⟨μ, v, (h1 hv).1, hv0, mem_hw.2 ⟨hμ, fun a b hab => hkill a b hab v (h1 hv)⟩⟩

end GlobalTheory.ExistsHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStableStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_vector_of_KStable : ∀ (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V), FiniteDimensional ℂ W → KStable M.act W → W ≠ ⊥ → ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  first | exact @GlobalTheory.ExistsHW.exists_highestWeight | exact GlobalTheory.ExistsHW.exists_highestWeight | (intros; apply GlobalTheory.ExistsHW.exists_highestWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDvdMulInvolutionAddOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NegOneNorm

theorem exists_dvd_mul_involution_add_one {R : Type} [CommRing R] [IsDedekindDomain R] (s : R →+* R)
    (hs : ∀ x, s (s x) = x) (n : R) (hn : n ≠ 0) (hsn : s n = n)
    (hfin : ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P))
    (hne : ∀ P : Ideal R, P.IsMaximal → ∃ x, s x - x ∉ P)
    (h2 : ∀ P : Ideal R, P.IsMaximal → (∀ x ∈ P, s x ∈ P) → (2 : R) ∉ P) :
    ∃ l : R, n ∣ l * s l + 1 := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  have hbot : ∀ P ∈ S, P ≠ ⊥ := fun P hP => by
    rintro rfl
    exact hn (by simpa using ((hS _).1 hP).2)
  have hpr : ∀ P ∈ S, Prime P := fun P hP => Ideal.prime_of_isPrime (hbot P hP) ((hS P).1 hP).1
  have hrad : ∏ P ∈ S, P ≤ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨h1, h3⟩
    exact Ideal.prod_le_inf.trans
      (Finset.inf_le (f := fun P => P) ((hS P).2 ⟨h3, (Ideal.span_singleton_le_iff_mem _).1 h1⟩))
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hcc : ∀ P : Ideal R, (P.comap s).comap s = P := fun P => by
    ext x; simp [Ideal.mem_comap, hs]
  have hz : ∀ P : Ideal R, ∃ z : R, P ∈ S → P.comap s = P → z * s z + 1 ∈ P ^ N := fun P => by
    by_cases h : P ∈ S ∧ P.comap s = P
    · obtain ⟨hP, hfix⟩ := h
      haveI hM : P.IsMaximal := ((hS P).1 hP).1.isMaximal (hbot P hP)
      haveI := hfin P hM
      have hsP : ∀ x ∈ P, s x ∈ P := fun x hx => by rwa [← hfix] at hx
      have : ∀ k : ℕ, ∃ z : R, k = 0 ∨ z * s z + 1 ∈ P ^ k := fun k => by
        induction k with
        | zero => exact ⟨0, Or.inl rfl⟩
        | succ k ih =>
          obtain ⟨z0, hz0⟩ := ih
          obtain ⟨z, hz, -⟩ := GlobalTheory.NormResidue.exists_mul_involution_add_one_mem_pow R s hs P hsP
            (hne P hM) (h2 P hM hsP) k z0 hz0
          exact ⟨z, Or.inr hz⟩
      obtain ⟨z, hz⟩ := this (N + 1)
      exact ⟨z, fun _ _ => Ideal.pow_le_pow_right (Nat.le_succ N) (hz.resolve_left (Nat.succ_ne_zero N))⟩
    · exact ⟨0, fun h1 h3 => (h ⟨h1, h3⟩).elim⟩
  choose z hz using hz
  let a : Ideal R → R := fun P =>
    if P.comap s = P then z P else if WellOrderingRel P (P.comap s) then 1 else -1
  have ha : ∀ P ∈ S, a P * s (a (P.comap s)) + 1 ∈ P ^ N := fun P hP => by
    by_cases hfix : P.comap s = P
    · simp only [a, hfix, if_true]
      exact hz P hP hfix
    · have hfix' : ¬ P = P.comap s := fun h => hfix h.symm
      simp only [a, hcc, if_neg hfix, if_neg hfix']
      rcases trichotomous_of WellOrderingRel P (P.comap s) with h | h | h
      · rw [if_pos h, if_neg (asymm h)]; simp
      · exact (hfix' h).elim
      · rw [if_pos h, if_neg (asymm h)]; simp
  obtain ⟨l, hl⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => N)
    hpr (fun _ _ _ _ h => h) (fun P => a P.1)
  have hmem : ∀ P ∈ S, l * s l + 1 ∈ P ^ N := fun P hP => by
    obtain ⟨h1, h3⟩ := (hS P).1 hP
    have hP' : P.comap s ∈ S := (hS _).2 ⟨Ideal.comap_isPrime s P, by rwa [Ideal.mem_comap, hsn]⟩
    have e1 : l - a P ∈ P ^ N := hl P hP
    have e2 : s (l - a (P.comap s)) ∈ P ^ N := Ideal.le_comap_pow s N (hl _ hP')
    have : l * s l + 1 = s l * (l - a P) + a P * s (l - a (P.comap s)) + (a P * s (a (P.comap s)) + 1) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ e1) (Ideal.mul_mem_left _ _ e2)) (ha P hP)
  refine ⟨l, Ideal.mem_span_singleton.1 (hN ?_)⟩
  rw [← Finset.prod_pow, ← IsDedekindDomain.inf_pow_eq_prod_of_prime S (fun P => P) (fun _ => N) hpr
    (fun _ _ _ _ h => h), Submodule.mem_finsetInf]
  exact hmem

theorem exists_norm_eq_neg_one : ∀ (D : D7) (m : ℕ), 0 < m → ∃ l b : 𝓞 D.host.E, (l : D.host.E) * D.host.conj (l : D.host.E) = -1 + (m : D.host.E) * (b : D.host.E) := by
  intro D m hm
  have hc : ∀ x, D.host.conj (D.host.conj x) = x := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := (Formalism.L2.Pj.barE D).toRingHom
  have hs : ∀ x, ((s x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := Formalism.L2.Pj.barE_eq_conj D
  obtain ⟨l, b, hb⟩ := exists_dvd_mul_involution_add_one s
    (fun x => RingOfIntegers.ext (by rw [hs, hs, hc])) (m : 𝓞 D.host.E) (by exact_mod_cast hm.ne')
    (map_natCast s m)
    (fun P hP => Ideal.finiteQuotientOfFreeOfNeBot P
      (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)))
    (fun P hP => by
      obtain ⟨θ, hθ⟩ := Formalism.L2.Pj.cmUnram_conj D P hP
      exact ⟨θ, fun h => hθ (by
        have h' := P.neg_mem h
        rw [neg_sub] at h'
        exact h')⟩)
    (fun P hP hsP h2 => by
      have hw : s (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := Formalism.L2.Pj.conj_w0E D
      have hsq := Formalism.L2.Pj.w0E_sq D
      obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
        have h1 := D.host.hyp.2.2.2.1
        have h3 := Formalism.L2.Pj.mE_spec D
        exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
      rw [hk] at hsq
      push_cast at hsq
      set w := Formalism.L2.Pj.w0E D
      have hm : w * (1 - w) ∈ P := by
        have : w * (1 - w) = k * 2 := by linear_combination -hsq
        rw [this]; exact P.mul_mem_left _ h2
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      rcases hP.isPrime.mem_or_mem hm with h | h
      · have h' := hsP _ h
        rw [hw] at h'
        simpa using P.add_mem h h'
      · have h' := hsP _ h
        rw [map_sub, map_one, hw] at h'
        simpa using P.add_mem h h')
  refine ⟨l, b, ?_⟩
  have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hb
  simp only [map_add (f := _), map_mul, map_one, map_natCast] at this
  rw [← hs]
  linear_combination this

end GlobalTheory.NegOneNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchMean

theorem sum_comp_algHom (K M : Type) [Field K] [Field M] [Algebra ℚ K] [Algebra ℚ M] [Algebra K M]
    [IsScalarTower ℚ K M] [FiniteDimensional ℚ K] [FiniteDimensional ℚ M]
    (F : (K →ₐ[ℚ] ℂ) → ℝ) :
    ∑ ρ : M →ₐ[ℚ] ℂ, F (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) =
      (Module.finrank K M : ℝ) * ∑ φ : K →ₐ[ℚ] ℂ, F φ := by
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  haveI : CharZero K := algebraRat.charZero K
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun ρ : M →ₐ[ℚ] ℂ => ρ.comp (IsScalarTower.toAlgHom ℚ K M)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F φ)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  letI : Algebra K ℂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (φ.commutes q).symm
  rw [← AlgHom.card K M ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun ψ _ => ψ.restrictScalars ℚ) ?_ ?_ ?_
  · intro ψ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext a
    exact ψ.commutes a
  · intro a _ b _ h
    exact AlgHom.restrictScalars_injective ℚ h
  · intro ρ hρ
    have h := (Finset.mem_filter.1 hρ).2
    exact ⟨{ ρ.toRingHom with commutes' := fun a => DFunLike.congr_fun h a },
      Finset.mem_univ _, rfl⟩

theorem sum_algHom_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (f : InfinitePlace K → ℝ) :
    ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom) = 2 * ∑ v, f v := by
  have h1 : ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom)
      = ∑ φ : K →+* ℂ, f (InfinitePlace.mk φ) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h1, ← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : K →+* ℂ => InfinitePlace.mk φ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f v)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := InfinitePlace.card_filter_mk_eq v
  rw [IsTotallyComplex.mult_eq] at this
  exact_mod_cast this

theorem posLog_sum_le {ι : Type} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℂ) :
    Real.posLog ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      (Real.posLog (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) + Real.posLog (∑ i, (w i : ℝ) * ‖b i‖ ^ 2)) / 2 := by
  have hw' : ∀ i, (0 : ℝ) ≤ w i := fun i => by exact_mod_cast hw i
  have h1 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      ∑ i, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    have h := Real.mul_self_sqrt (hw' i)
    rw [norm_mul, norm_mul, Complex.norm_ratCast, abs_of_nonneg (hw' i)]
    linear_combination (-(‖a i‖ * ‖b i‖)) * h
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i) * ‖a i‖) (fun i => Real.sqrt (w i) * ‖b i‖)
  simp only [mul_pow, Real.sq_sqrt (hw' _)] at h2
  have h3 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ^ 2 ≤
      (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) * ∑ i, (w i : ℝ) * ‖b i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h4 := (Real.posLog_le_posLog (le_trans (by norm_num) (sq_nonneg _)) h3).trans Real.posLog_mul
  rw [Real.posLog_pow] at h4
  push_cast at h4
  linarith

theorem meanInf_posLog_le :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (x : K) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] [IsGalois ℚ M] (ι : Type) [Fintype ι] (w : ι → ℚ) (z : ι → M), (∀ a, σ a ∈ M) → (∀ i, 0 ≤ w i) → σ x = ∑ i, (w i : ℂ) * ((z i : ℂ) * starRingEnd ℂ (z i : ℂ)) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2)) / (Module.finrank ℚ M : ℝ) := by
  intro K _ _ _ σ x M _ _ ι _ w z hσ hw hx
  let σ' : K →+* M := σ.codRestrict M hσ
  letI : Algebra K M := σ'.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let j : M →ₐ[ℚ] ℂ := ((starRingEnd ℂ).toRatAlgHom).comp M.val
  have hj : ∀ y : M, starRingEnd ℂ (y : ℂ) ∈ M := fun y => by
    have : j y ∈ j.fieldRange := ⟨y, rfl⟩
    exact (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ M (IsGalois.to_normal (F := ℚ) (E := M)) j).le this
  let c : M →ₐ[ℚ] M := (j.toRingHom.codRestrict M hj).toRatAlgHom
  have hc : ∀ y : M, (c y : ℂ) = starRingEnd ℂ (y : ℂ) := fun _ => rfl
  have hcc : ∀ y, c (c y) = y := fun y => Subtype.ext (by rw [hc, hc, Complex.conj_conj])
  have hxM : algebraMap K M x = ∑ i, (w i : M) * (z i * c (z i)) := by
    apply Subtype.ext
    change σ x = M.val _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_ratCast]
    rfl
  set A : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2) with hA
  have hinv : Function.Involutive (fun ρ : M →ₐ[ℚ] ℂ => ρ.comp c) := fun ρ => by
    ext y
    simp [hcc]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, A (ρ.comp c) = ∑ ρ, A ρ :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have h1 := sum_comp_algHom K M (fun φ => Real.posLog ‖φ x‖)
  have h2 := sum_algHom_eq K (fun v => Real.posLog ‖v.embedding x‖)
  have h3 : ∑ φ : K →ₐ[ℚ] ℂ, Real.posLog ‖φ x‖ =
      2 * ∑ v : InfinitePlace K, Real.posLog ‖v.embedding x‖ := by
    rw [← h2]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
    rfl
  have h4 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog ‖(ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x‖
      ≤ ∑ ρ, A ρ := by
    calc _ ≤ ∑ ρ : M →ₐ[ℚ] ℂ, (A ρ + A (ρ.comp c)) / 2 := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x
              = ∑ i, (w i : ℂ) * (ρ (z i) * ρ (c (z i))) := by
            change ρ (algebraMap K M x) = _
            set_option synthInstance.maxHeartbeats 100000 in
              rw [hxM, map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_mul, map_ratCast]
          rw [this]
          exact posLog_sum_le w hw _ _
      _ = ∑ ρ, A ρ := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]; ring
  rw [h1, h3] at h4
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hM : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [le_div_iff₀ hM, ← ht]
  refine le_trans (le_of_eq ?_) h4
  field_simp

end GlobalTheory.ArchMean
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SameCharacterCommonExtension
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.Proof.dvr_of_reflects_facts

theorem dvr_of_reflects {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (g : O →+* A) (hg : Function.Injective g)
    (hd : ∀ x y, g x ∣ g y → x ∣ y) (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    IsDiscreteValuationRing O := by
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2
    ⟨fun x y => (ValuationRing.dvd_total (g x) (g y)).imp (hd x y) (hd y x)⟩
  haveI : WfDvdMonoid O := by
    refine Subrelation.wf (r := InvImage DvdNotUnit g) ?_ (InvImage.wf g wellFounded_dvdNotUnit)
    rintro x y ⟨hx, c, hc, rfl⟩
    refine ⟨fun h => hx (hg (by simpa using h)), g c, fun h => hc ?_, by simp⟩
    exact isUnit_of_dvd_one (hd c 1 (by simpa using h.dvd))
  haveI : IsPrincipalIdealRing O := ((IsBezout.tfae (R := O)).out 4 2).1 ‹WfDvdMonoid O›
  refine { not_a_field' := fun h => ht0 ?_ }
  have : t ∈ IsLocalRing.maximalIdeal O := ht
  rw [h] at this
  simpa using this

theorem common_of_field {O₀ A B K : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    (fA : O₀ →+* A) (fB : O₀ →+* B) (hAi : fA.IsIntegral) (hB : Function.Injective fB)
    (hBl : IsLocalHom fB) (f₀ : O₀ →+* K) (jA : K →+* FractionRing A) (jB : K →+* FractionRing B)
    (hjA : ∀ c, jA (f₀ c) = algebraMap A _ (fA c)) (hjB : ∀ c, jB (f₀ c) = algebraMap B _ (fB c)) :
    ∃ (O₁ : Subring K) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B),
      (∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x) ∧
      (∀ x, algebraMap A _ (gA x) = jA x) ∧ (∀ x, algebraMap B _ (gB x) = jB x) ∧
      Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧
      gA.comp f = fA ∧ gB.comp f = fB := by
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  let O₁ : Subring K := (algebraMap A (FractionRing A)).range.comap jA
  have hmem : ∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x := fun x => Iff.rfl
  let f : O₀ →+* O₁ := f₀.codRestrict O₁ (fun c => (hmem _).2 ⟨fA c, (hjA c).symm⟩)
  have hf : ∀ c, (f c : K) = f₀ c := fun c => rfl
  have lift : ∀ {C : Type} [CommRing C] [IsDomain C] (j : K →+* FractionRing C),
      (∀ x : O₁, ∃ a, algebraMap C _ a = j x) → ∃ g : O₁ →+* C, ∀ x, algebraMap C _ (g x) = j x := by
    intro C _ _ j h
    have iC := IsFractionRing.injective C (FractionRing C)
    choose g hg using h
    exact ⟨{ toFun := g
             map_one' := iC (by simp [hg])
             map_mul' := fun x y => iC (by simp [hg])
             map_zero' := iC (by simp [hg])
             map_add' := fun x y => iC (by simp [hg]) }, hg⟩
  obtain ⟨gA, hgA⟩ := lift jA (fun x => (hmem x).1 x.2)
  have gAi : Function.Injective gA := fun x y h =>
    Subtype.ext (jA.injective (by rw [← hgA, ← hgA, h]))
  have cA : gA.comp f = fA := RingHom.ext fun c => iA (by rw [RingHom.comp_apply, hgA, hf, hjA])
  have hint : ∀ x : O₁, ∃ a, algebraMap B _ a = jB x := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hAi (gA x)
    have h1 : p.eval₂ f x = 0 := gAi (by rw [Polynomial.hom_eval₂, cA, hpx, map_zero])
    have h2 := congrArg (jB.comp O₁.subtype) h1
    rw [Polynomial.hom_eval₂, map_zero] at h2
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨p.map fB, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap B (FractionRing B)).comp fB = (jB.comp O₁.subtype).comp f :=
      RingHom.ext fun c => (hjB c).symm
    rw [e]
    exact h2
  obtain ⟨gB, hgB⟩ := lift jB hint
  have gBi : Function.Injective gB := fun x y h =>
    Subtype.ext (jB.injective (by rw [← hgB, ← hgB, h]))
  have cB : gB.comp f = fB := RingHom.ext fun c => iB (by rw [RingHom.comp_apply, hgB, hf, hjB])
  have hd : ∀ x y, gA x ∣ gA y → x ∣ y := by
    rintro x y ⟨c, hc⟩
    by_cases hx : x = 0
    · have : y = 0 := gAi (by rw [hc, hx]; simp)
      simp [this]
    have hx' : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hx'' : jA x ≠ 0 := by simpa using hx'
    refine ⟨⟨y / x, (hmem _).2 ⟨c, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [map_div₀, eq_div_iff hx'', ← hgA, ← hgA, hc, map_mul, mul_comm]
    · simp [mul_div_cancel₀ _ hx']
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  have hcB : ∀ c, gB (f c) = fB c := fun c => by rw [← cB]; rfl
  have hnu : ¬ IsUnit (gB (f ϖ)) := fun h => hϖ.not_isUnit (hBl.map_nonunit _ (hcB ϖ ▸ h))
  have ht0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hB (by rw [← hcB, h, map_zero, map_zero]))
  haveI hD : IsDiscreteValuationRing O₁ :=
    dvr_of_reflects gA gAi hd (f ϖ) ht0 (fun h => hnu (h.map gB))
  refine ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi,
    ⟨fun x h => isUnit_of_dvd_one (hd x 1 (by simpa using h.dvd))⟩, ⟨fun x h => ?_⟩, cA, cB⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O₁
  by_contra hx
  have hπx : π ∣ x := by
    have : x ∈ IsLocalRing.maximalIdeal O₁ := hx
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  have hu : IsUnit (gB π) := isUnit_of_dvd_unit (map_dvd gB hπx) h
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
  apply hnu
  rw [hn, map_mul, map_pow]
  exact (u.isUnit.map gB).mul (hu.pow n)

theorem common : ∀ (Γ O₀ A B : Type) [Group Γ] [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (fA : O₀ →+* A) (fB : O₀ →+* B), Function.Injective fA → fA.IsIntegral → Function.Injective fB → IsLocalHom fB → ∀ (ψA : Γ →* Aˣ) (ψB : Γ →* Bˣ), SameChar fA fB ψA ψB → ∃ (O₁ : Type) (_ : CommRing O₁) (_ : IsDomain O₁) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B) (ψ : Γ →* O₁ˣ), Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧ gA.comp f = fA ∧ gB.comp f = fB ∧ (Units.map gA.toMonoidHom).comp ψ = ψA ∧ (Units.map gB.toMonoidHom).comp ψ = ψB := by
  intro Γ O₀ A B _ _ _ _ _ _ _ _ _ _ fA fB _ hAi hB hBl ψA ψB hS
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  letI : Algebra O₀ A := fA.toAlgebra
  letI : Algebra O₀ B := fB.toAlgebra
  let αA : MonoidAlgebra O₀ Γ →+* A :=
    (MonoidAlgebra.lift O₀ A Γ ((Units.coeHom A).comp ψA)).toRingHom
  let αB : MonoidAlgebra O₀ Γ →+* B :=
    (MonoidAlgebra.lift O₀ B Γ ((Units.coeHom B).comp ψB)).toRingHom
  have hker : ∀ F, αA F = 0 ↔ αB F = 0 := by
    intro F
    simp only [αA, αB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_apply, Algebra.smul_def]
    exact hS _
  have aA : ∀ c, αA (algebraMap O₀ _ c) = fA c := fun c => AlgHom.commutes _ c
  have aB : ∀ c, αB (algebraMap O₀ _ c) = fB c := fun c => AlgHom.commutes _ c
  have oA : ∀ g, αA (MonoidAlgebra.of O₀ Γ g) = ψA g := fun g => MonoidAlgebra.lift_of _ g
  have oB : ∀ g, αB (MonoidAlgebra.of O₀ Γ g) = ψB g := fun g => MonoidAlgebra.lift_of _ g
  let R : Subring A := αA.range
  let q : MonoidAlgebra O₀ Γ →+* R := αA.rangeRestrict
  have hq : Function.Surjective q := αA.rangeRestrict_surjective
  let φ : R →+* B := q.liftOfSurjective hq ⟨αB, fun F hF =>
    (hker F).1 (congrArg Subtype.val (RingHom.mem_ker.1 hF))⟩
  have hφ : ∀ F, φ (q F) = αB F := fun F => RingHom.liftOfRightInverse_comp_apply _ _ _ _ F
  have φi : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨F, rfl⟩ := hq r
    exact Subtype.ext ((hker F).2 (by rw [← hφ, hr]))
  let K := FractionRing R
  let jA : K →+* FractionRing A := IsFractionRing.lift (g := (algebraMap A _).comp R.subtype)
    (iA.comp Subtype.val_injective)
  let jB : K →+* FractionRing B := IsFractionRing.lift (g := (algebraMap B _).comp φ)
    (iB.comp φi)
  let p : MonoidAlgebra O₀ Γ →+* K := (algebraMap R K).comp q
  have pA : ∀ F, jA (p F) = algebraMap A _ (αA F) := fun F => IsFractionRing.lift_algebraMap _ _
  have pB : ∀ F, jB (p F) = algebraMap B _ (αB F) := fun F => by
    rw [← hφ]; exact IsFractionRing.lift_algebraMap _ _
  obtain ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi, lA, lB, cA, cB⟩ :=
    common_of_field fA fB hAi hB hBl (p.comp (algebraMap O₀ _)) jA jB
      (fun c => by rw [RingHom.comp_apply, pA, aA]) (fun c => by rw [RingHom.comp_apply, pB, aB])
  let p₁ : MonoidAlgebra O₀ Γ →+* O₁ := p.codRestrict O₁ (fun F => (hmem _).2 ⟨_, (pA F).symm⟩)
  let ψ : Γ →* O₁ˣ := (p₁.toMonoidHom.comp (MonoidAlgebra.of O₀ Γ)).toHomUnits
  refine ⟨O₁, inferInstance, inferInstance, hD, f, gA, gB, ψ, gAi, gBi, lA, lB, cA, cB, ?_, ?_⟩
  · ext g
    apply iA
    rw [← oA, ← pA]
    exact hgA _
  · ext g
    apply iB
    rw [← oB, ← pB]
    exact hgB _

end GlobalTheory.Proof.dvr_of_reflects_facts
end
