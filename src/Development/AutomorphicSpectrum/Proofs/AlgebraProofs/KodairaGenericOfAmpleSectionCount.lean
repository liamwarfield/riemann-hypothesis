module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuKodaira
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCoords
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @PositivityTheory.HtPt.Siua.siu_kodaira | exact PositivityTheory.HtPt.Siua.siu_kodaira
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCountStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | exact GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | (intros; apply GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoords
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem dualStackedExcCoords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement :=
  GroundTheory.Heights₂.Heights.DualStackedExcCoords.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoordsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_coords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBase
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBase
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

section Scale

variable {T : Type} [Fintype T]

def blockVal {R : Type} (P Q : T → R) : (Σ κ, stackedBlocks T κ) → R
  | ⟨.inl _, t⟩ => P t
  | ⟨.inr _, t⟩ => Q t

def blockEval {R : Type} [CommRing R] (P Q : T → R) : MRing (stackedBlocks T) →+* R :=
  eval₂Hom (Int.castRingHom R) (blockVal P Q)

theorem blockEval_first {R : Type} [CommRing R] (P Q : T → R) (t : T) :
    blockEval P Q (graphFirst t) = P t := by
  simp [blockEval, graphFirst, blockVal]

theorem blockEval_second {R : Type} [CommRing R] (P Q : T → R) (t : T) :
    blockEval P Q (graphSecond t) = Q t := by
  simp [blockEval, graphSecond, blockVal]

theorem ringHom_block_ext {R : Type} [CommRing R] {f g : MRing (stackedBlocks T) →+* R}
    (h1 : ∀ t, f (graphFirst t) = g (graphFirst t)) (h2 : ∀ t, f (graphSecond t) = g (graphSecond t)) :
    f = g := by
  apply MvPolynomial.ringHom_ext
  · intro n
    simp
  · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
    · exact h1 t
    · exact h2 t

theorem blockEval_scale {R : Type} [CommRing R] (P Q : T → R) (l μ : R) {d e : ℕ}
    {f : MRing (stackedBlocks T)} (hf : IsMultiHomog f (bidegree d e)) :
    blockEval (fun t => l * P t) (fun t => μ * Q t) f = l ^ d * μ ^ e * blockEval P Q f := by
  classical
  simp only [blockEval, coe_eval₂Hom]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ t : T, m ⟨Sum.inl (), t⟩ = d := hf m hm (Sum.inl ())
  have h2 : ∑ t : T, m ⟨Sum.inr (), t⟩ = e := hf m hm (Sum.inr ())
  have key : ∏ s, blockVal (fun t => l * P t) (fun t => μ * Q t) s ^ m s =
      l ^ d * μ ^ e * ∏ s, blockVal P Q s ^ m s := by
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique]
    change (∏ t : T, (l * P t) ^ m ⟨Sum.inl (), t⟩) * (∏ t : T, (μ * Q t) ^ m ⟨Sum.inr (), t⟩) =
      l ^ d * μ ^ e * ((∏ t : T, P t ^ m ⟨Sum.inl (), t⟩) * ∏ t : T, Q t ^ m ⟨Sum.inr (), t⟩)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1, h2]
    ring
  rw [key]
  ring

end Scale

section ThetaShiftProofs

variable {K : Type} [Field K] {i m : ℕ}

theorem arc_form (p : K) (y₀ : Fin i → K) (g : Fin m → Fin i → K) (φ : Fin i → K) :
    eval₂Hom (C : K →+* MvPolynomial (Fin (m + 1)) K)
        (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ)) (∑ j, C (φ j) * X j) =
      C p * (C (φ ⬝ᵥ y₀) * X 0 + ∑ l, C (φ ⬝ᵥ g l) * X l.succ) := by
  have hj : ∀ j, eval₂Hom (C : K →+* MvPolynomial (Fin (m + 1)) K)
      (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ)) (C (φ j) * X j) =
      C p * (C (φ j * y₀ j) * X 0 + ∑ l, C (φ j * g l j) * X l.succ) := by
    intro j
    rw [map_mul, eval₂Hom_C, eval₂Hom_X']
    simp only [C_mul, mul_assoc, ← Finset.mul_sum]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, Finset.sum_mul]

end ThetaShiftProofs

section Lead

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem lead_of_coords {b : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F)} {b' : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F')}
    {k : Type} [Field k] {ρ : 𝓞 K →+* k} {π : 𝓞 K} {y₀ : Fin i → K} {m : ℕ} {g : Fin m → Fin i → K}
    {α : T → k} {M : T → Fin (m + 1) → k} (hco : IsExcCoords F F' b b' ρ π y₀ g α M) {d e : ℕ}
    {f : MRing (stackedBlocks T)} (hf : IsMultiHomog f (bidegree d e))
    (h0 : stackedFormEval b b' f = 0) : linPointMap α M f = 0 := by
  obtain ⟨-, hπ, -, hg, hα, hM0, hMj, ⟨t₀, ht₀⟩, -, -, -, -⟩ := hco
  choose cα hcα hcαρ using hα
  choose c0 hc0 hc0ρ using hM0
  choose c1 hc1 hc1ρ using hMj
  have hh : ∀ t l, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ g l :=
    fun t l => (b' t).2 _ (hg l)
  choose h hh using hh
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := by
    intro hp
    apply ht₀
    have hc : cα t₀ = 0 := hinj (by rw [hcα, hp, map_zero, zero_smul, dotProduct_zero])
    rw [← hcαρ t₀, hc, map_zero]

  let A : T → MvPolynomial (Fin (m + 1)) (𝓞 K) :=
    fun t => C (cα t) * X 0 + ∑ l, C (π * h t l) * X l.succ
  let L : T → MvPolynomial (Fin (m + 1)) (𝓞 K) :=
    fun t => C (c0 t) * X 0 + ∑ l, C (c1 t l) * X l.succ
  let ι : MvPolynomial (Fin (m + 1)) (𝓞 K) →+* MvPolynomial (Fin (m + 1)) K :=
    map (algebraMap (𝓞 K) K)
  have hι : Function.Injective ι := map_injective _ hinj
  let p : K := algebraMap (𝓞 K) K π
  let Φ : MvPolynomial (Fin i) K →+* MvPolynomial (Fin (m + 1)) K :=
    eval₂Hom C (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ))
  have hΦ : Φ.comp (stackedFormEval b b') =
      blockEval (fun t => 1 * ι (A t)) (fun t => C p * ι (L t)) := by
    apply ringHom_block_ext
    · intro t
      rw [RingHom.comp_apply, DualStackedExcLeadExample.stackedFormEval_first, blockEval_first]
      refine (arc_form p y₀ g _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [A, ι, map_add (f := _), map_mul, map_C, map_X, map_sum, one_mul]
      rw [hcα, dotProduct_smul, smul_eq_mul, C_mul, mul_add, Finset.mul_sum, mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hh]
      exact (mul_assoc _ _ _).symm
    · intro t
      rw [RingHom.comp_apply, DualStackedExcLeadExample.stackedFormEval_second, blockEval_second]
      refine (arc_form p y₀ g _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [L, ι, map_add (f := _), map_mul, map_C, map_X, map_sum, hc0, hc1]
  have hι2 : blockEval (fun t => ι (A t)) (fun t => ι (L t)) = ι.comp (blockEval A L) := by
    apply ringHom_block_ext
    · intro t
      simp only [RingHom.comp_apply, blockEval_first]
    · intro t
      simp only [RingHom.comp_apply, blockEval_second]
  have e1 : (C p) ^ e * ι (blockEval A L f) = 0 := by
    have h1 := congrArg (fun r => r f) hΦ
    simp only [RingHom.comp_apply, h0, map_zero] at h1
    rw [blockEval_scale _ _ _ _ hf, hι2, one_pow, one_mul, RingHom.comp_apply] at h1
    exact h1.symm
  have e2 : blockEval A L f = 0 := by
    have hCp : (C p : MvPolynomial (Fin (m + 1)) K) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hπ0
    exact hι (by rw [map_zero]; exact (mul_eq_zero.mp e1).resolve_left (pow_ne_zero _ hCp))

  let ψ : MvPolynomial (Fin (m + 1)) (𝓞 K) →+* MvPolynomial (Option (Fin (m + 1))) k :=
    eval₂Hom (C.comp ρ) (fun j => X (some j))
  let ℓ : T → MvPolynomial (Option (Fin (m + 1))) k := fun t => ∑ j, C (M t j) * X (some j)
  have hψ : ψ.comp (blockEval A L) =
      blockEval (fun t => X (some 0) * C (α t)) (fun t => 1 * ℓ t) := by
    apply ringHom_block_ext
    · intro t
      rw [RingHom.comp_apply, blockEval_first, blockEval_first]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [A, ψ, map_add (f := _), map_mul, eval₂Hom_C, eval₂Hom_X', map_sum, RingHom.comp_apply, hcαρ,
        hπ, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
      ring
    · intro t
      rw [RingHom.comp_apply, blockEval_second, blockEval_second]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [L, ψ, ℓ, map_add (f := _), map_mul, eval₂Hom_C, eval₂Hom_X', map_sum, RingHom.comp_apply, hc0ρ,
        hc1ρ, one_mul, Fin.sum_univ_succ]
  have hlin : (linPointMap α M : MRing (stackedBlocks T) →+* _) =
      blockEval (fun t => X none * C (α t)) (fun t => 1 * ℓ t) := by
    apply ringHom_block_ext
    · intro t
      rw [LinPrimeExample.linPointMap_first, blockEval_first, mul_comm]
    · intro t
      rw [LinPrimeExample.linPointMap_second, blockEval_second, one_mul]
  have e3 : blockEval (fun t => C (α t)) ℓ f = 0 := by
    have h1 := congrArg (fun r => r f) hψ
    simp only [RingHom.comp_apply, e2, map_zero] at h1
    rw [blockEval_scale _ _ _ _ hf, one_pow, mul_one] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ (X_ne_zero _))
  rw [hlin, blockEval_scale _ _ _ _ hf, e3, mul_zero]

theorem centre_mem_of_coords {b : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F)} {b' : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k]
    {ρ : 𝓞 K →+* k} {π : 𝓞 K} {y₀ : Fin i → K} {m : ℕ} {g : Fin m → Fin i → K}
    {α : T → k} {M : T → Fin (m + 1) → k} (hco : IsExcCoords F F' b b' ρ π y₀ g α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨-, hπ, -, -, hα, hM0, -⟩ := hco
  obtain ⟨c, hc, hcρ⟩ := hα t
  obtain ⟨c', hc', -⟩ := hM0 t
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have h : ((a t : ℤ) : 𝓞 K) * c = π * c' := by
    apply hinj
    rw [map_mul, map_mul, map_intCast, hc, hc', hab t, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      zsmul_eq_mul]
    ring
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [← hcρ, ← map_intCast ρ, ← map_mul, h, map_mul, hπ, zero_mul]
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end Lead

theorem exc_base : DualStackedExcBase.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ ρ π y₀ m g α M hco
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, G, rfl, hG⟩ := graph_bihomog K i F F' T b b' a hab f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp => lead_of_coords hco (hG p hp).1 (hG p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem_of_coords hab hco

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBaseStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_base : GroundTheory.Heights₂.Heights.DualStackedExcBase.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exc_base | exact GlobalTheory.CompanionTheory.Ar.Giv.exc_base | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exc_base <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHolds
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem isIntegral_pow_mul_of_subring {A Ω : Type*} [CommRing A] [CommRing Ω] [Algebra A Ω] (R : Subring Ω)
    (w : Ω) (hw : ∃ r, algebraMap A Ω r = w)
    (hR : ∀ a ∈ R, ∃ e : ℕ, ∃ r : A, algebraMap A Ω r = w ^ e * a) {u : Ω} (hu : IsIntegral R u) :
    ∃ e : ℕ, IsIntegral A (w ^ e * u) := by
  classical
  obtain ⟨Q, hQm, hQ⟩ := hu
  obtain ⟨r0, hr0⟩ := hw
  have hcommon : ∃ e : ℕ, ∀ k, ∃ r : A, algebraMap A Ω r = w ^ e * (Q.coeff k : Ω) := by
    choose ef rf hf using fun k => hR _ (Q.coeff k).2
    refine ⟨(Finset.range (Q.natDegree + 1)).sup ef, fun k => ?_⟩
    by_cases hk : k ∈ Finset.range (Q.natDegree + 1)
    · have hle := Finset.le_sup (f := ef) hk
      refine ⟨r0 ^ ((Finset.range (Q.natDegree + 1)).sup ef - ef k) * rf k, ?_⟩
      rw [map_mul, map_pow, hr0, hf, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · have : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
        simpa [Nat.lt_succ_iff] using hk)
      exact ⟨0, by simp [this]⟩
  obtain ⟨e, he⟩ := hcommon
  refine ⟨e, ?_⟩
  have hQ'm : (Q.map (algebraMap R Ω)).Monic := hQm.map _
  have hl : (Q.map (algebraMap R Ω)).scaleRoots (w ^ e) ∈ Polynomial.lifts (algebraMap A Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_scaleRoots, Polynomial.coeff_map]
    rcases lt_trichotomy k (Q.map (algebraMap R Ω)).natDegree with h | h | h
    · obtain ⟨r, hr⟩ := he k
      refine ⟨r0 ^ (e * ((Q.map (algebraMap R Ω)).natDegree - k - 1)) * r, ?_⟩
      have h1 : (Q.map (algebraMap R Ω)).natDegree - k = ((Q.map (algebraMap R Ω)).natDegree - k - 1) + 1 := by
        omega
      rw [map_mul, map_pow, hr0, hr]
      conv_rhs => rw [h1]
      rw [pow_succ, ← pow_mul]
      show _ = (Q.coeff k : Ω) * _
      ring
    · have h2 : algebraMap R Ω (Q.coeff k) = 1 := by
        rw [← Polynomial.coeff_map, h]
        exact hQ'm.coeff_natDegree
      exact ⟨1, by rw [h2, h]; simp⟩
    · have h2 : algebraMap R Ω (Q.coeff k) = 0 := by
        rw [← Polynomial.coeff_map]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt h
      exact ⟨0, by rw [h2]; simp⟩
  obtain ⟨Q', hQ', -, hQ'mon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (Polynomial.monic_scaleRoots_iff _ |>.mpr hQ'm)
  refine ⟨Q', hQ'mon, ?_⟩
  rw [← Polynomial.eval_map, hQ']
  have h3 : Polynomial.eval₂ (RingHom.id Ω) u (Q.map (algebraMap R Ω)) = 0 := by
    rw [Polynomial.eval₂_map]
    exact hQ
  have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := w ^ e) h3
  simpa [Polynomial.eval₂_id] using this

theorem normFormGaussBound : NormFormGaussBound.Statement := by
  intro Ω _ _ D l P _ hP hgen p hp j K d x c hchom hcp hint μ
  classical
  have := Fact.mk hp
  have hl := DehomCharpolyForms.ne_zero_of_generic hgen
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω x) with hf

  have h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n) := by
    have := congrArg (fun g => _root_.AddMonoidAlgebra.coeff (M := ℕ) g 0) hcp
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
    rw [this, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have : b < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn
      rw [if_neg (by omega)]
    · intro h
      simp at h

  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω x)
  rw [← Algebra.norm_apply, ← hf] at hdet
  have hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P x := by
    rw [hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

  let V := (Rat.padicValuation p).valuationSubring
  let σ := {i // i ≠ j}
  have hmemP : ∀ i, l i / l j ∈ P := fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩
  let tP : σ → P := fun i => ⟨l i / l j, hmemP i⟩
  let ω : σ → Ω := fun i => l i / l j
  let _ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ) := MvPolynomial.algebraMvPolynomial
  let ψP : MvPolynomial σ V →+* P :=
    (aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))
  let _ : Algebra (MvPolynomial σ V) P := ψP.toAlgebra
  let _ : Algebra (MvPolynomial σ V) Ω := (P.val.toRingHom.comp ψP).toAlgebra
  have _ : IsScalarTower (MvPolynomial σ V) P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω :=
    { (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with
      commutes' := fun r => by
        show aeval ω _ = P.val (aeval tP _)
        exact (DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }
  have hfA : ∀ G, fA G = aeval ω G := fun _ => rfl
  have hinj : Function.Injective fA := by
    intro a b hab
    exact DehomCharpolyForms.injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)
  have halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r =
      aeval ω (map (algebraMap V ℚ) r) := fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl

  let ν₀ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  let W : MvPolynomial σ V := monomial ν₀ 1
  let w : Ω := algebraMap (MvPolynomial σ V) Ω W
  have hwq : aeval ω (monomial ν₀ (1 : ℚ)) = w := by
    show _ = algebraMap (MvPolynomial σ V) Ω W
    rw [halg]
    simp [W, map_monomial]
  have hX : ∀ i : σ, algebraMap (MvPolynomial σ V) Ω (X i) = l i / l j := by
    intro i
    rw [halg]
    simp [ω]
  have hcut : ∀ k : σ, ∃ r, algebraMap (MvPolynomial σ V) Ω r * (l k / l j) = w := by
    intro k
    refine ⟨monomial (ν₀ - Finsupp.single k 1) 1, ?_⟩
    rw [← hX k, ← map_mul]
    show _ = algebraMap (MvPolynomial σ V) Ω W
    congr 1
    have hν : (ν₀ - Finsupp.single k 1) + Finsupp.single k 1 = ν₀ :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by simp [ν₀]))
    show monomial (ν₀ - Finsupp.single k 1) 1 * monomial (Finsupp.single k 1) 1 = monomial ν₀ 1
    rw [monomial_mul, hν, one_mul]
  have hratio : ∀ i, ∃ r, algebraMap (MvPolynomial σ V) Ω r = l i / l j := by
    intro i
    by_cases h : i = j
    · subst h
      exact ⟨1, by rw [map_one, div_self (hl i)]⟩
    · exact ⟨X ⟨i, h⟩, hX ⟨i, h⟩⟩
  have hinv : ∀ k, ∃ r, algebraMap (MvPolynomial σ V) Ω r = w * (l j / l k) := by
    intro k
    by_cases h : k = j
    · subst h
      exact ⟨W, by rw [div_self (hl k), mul_one]⟩
    · obtain ⟨r, hr⟩ := hcut ⟨k, h⟩
      refine ⟨r, ?_⟩
      rw [← hr]
      have h1 := hl k
      have h2 := hl j
      show _ = algebraMap (MvPolynomial σ V) Ω r * (l k / l j) * (l j / l k)
      field_simp

  have hR : ∀ a ∈ Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}),
      ∃ e : ℕ, ∃ r : MvPolynomial σ V, algebraMap (MvPolynomial σ V) Ω r = w ^ e * a := by
    intro a ha
    induction ha using Subring.closure_induction with
    | mem z hz =>
      rcases hz with ⟨i, k, rfl⟩ | ⟨r, hr, rfl⟩
      · obtain ⟨r1, h1⟩ := hratio i
        obtain ⟨r2, h2⟩ := hinv k
        refine ⟨1, r1 * r2, ?_⟩
        rw [map_mul, h1, h2, pow_one]
        have h3 := hl k
        have h4 := hl j
        field_simp
      · refine ⟨0, C ⟨(r : ℚ)⁻¹, DehomNormPIntegral.inv_natCast_mem hr⟩, ?_⟩
        rw [halg]
        simp
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨e1, r1, h1⟩ := ha
      obtain ⟨e2, r2, h2⟩ := hb
      refine ⟨e1 + e2, W ^ e2 * r1 + W ^ e1 * r2, ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, h1, h2]
      show w ^ e2 * _ + w ^ e1 * _ = _
      ring
    | neg a _ ha =>
      obtain ⟨e1, r1, h1⟩ := ha
      exact ⟨e1, -r1, by rw [map_neg, h1]; ring⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e1, r1, h1⟩ := ha
      obtain ⟨e2, r2, h2⟩ := hb
      exact ⟨e1 + e2, r1 * r2, by rw [map_mul, h1, h2]; ring⟩
  obtain ⟨e, hu'⟩ := isIntegral_pow_mul_of_subring (A := MvPolynomial σ V) _ w ⟨W, rfl⟩ hR
    ((mem_integralClosure_iff _ _).mp hint)

  have hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x)))) :=
    (Algebra.isIntegral_norm P hu').algebraMap
  let sP : P := (algebraMap (MvPolynomial σ V) P W) ^ e * (p : P) ^ K
  have hsP : algebraMap P Ω sP = w ^ e * (p : Ω) ^ K := by
    simp only [sP, map_mul, map_pow, map_natCast]
    rfl
  have hnorm : algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x))) =
      (w ^ e * (p : Ω) ^ K) ^ n * algebraMap P Ω (Algebra.norm P x) := by
    rw [← mul_assoc, ← hsP, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
  set G := PullFormsGeneric.dehom j (c n) with hGdef
  have hdeh : aeval ω G = aeval (fun i => l i / l j) (c n) := by
    rw [hGdef, PullFormsGeneric.aeval_dehom]
    refine congrArg (fun g => aeval g (c n)) (funext fun i => ?_)
    split_ifs with h
    · subst h
      exact (div_self (hl _)).symm
    · rfl
  let E : MvPolynomial σ ℚ := monomial ((e * n) • ν₀) ((p : ℚ) ^ (n * K)) * G
  have hEval : fA E = (-1) ^ n * algebraMap P Ω (Algebra.norm P (w ^ e * ((p : Ω) ^ K * x))) := by
    have hmon : (monomial ((e * n) • ν₀) ((p : ℚ) ^ (n * K)) : MvPolynomial σ ℚ) =
        C ((p : ℚ) ^ (n * K)) * (monomial ν₀ (1 : ℚ)) ^ (e * n) := by
      rw [monomial_pow, one_pow, C_mul_monomial, mul_one]
    rw [hfA, map_mul, hmon, map_mul, aeval_C, map_pow (aeval ω), hwq, hdeh, ← h0, hc0, hnorm]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  have hEint : IsIntegral (MvPolynomial σ V) E := by
    refine (isIntegral_algHom_iff fA hinj).mp ?_
    rw [hEval]
    exact (isIntegral_one.neg.pow n).mul hN
  have hEc : ∀ ν, E.coeff ν ∈ V.toSubring := by
    intro ν
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hEint ν)
    rw [← hy]
    exact y.2
  have hF : (C ((p : ℚ) ^ (n * K)) * c n).IsHomogeneous d := by
    simpa using (isHomogeneous_C (Fin (D + 1)) ((p : ℚ) ^ (n * K))).mul hchom
  have hG : ∀ ν, (PullFormsGeneric.dehom j (C ((p : ℚ) ^ (n * K)) * c n)).coeff ν ∈ V.toSubring := by
    intro ν
    have h1 : PullFormsGeneric.dehom j (C ((p : ℚ) ^ (n * K)) * c n) = C ((p : ℚ) ^ (n * K)) * G := by
      simp [PullFormsGeneric.dehom, hGdef]
    have h2 := hEc ((e * n) • ν₀ + ν)
    rw [coeff_monomial_mul] at h2
    rw [h1, coeff_C_mul]
    exact h2
  have hm := DehomNormPIntegral.coeff_mem_of_dehom_coeff_mem hgen j hF V.toSubring hG μ
  rw [coeff_C_mul] at hm
  have hv := DehomNormPIntegral.padicValRat_nonneg_of_mem hm
  by_cases hc : (c n).coeff μ = 0
  · rw [hc, padicValRat.zero]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.mul (pow_ne_zero _ hp0) hc, padicValRat.pow _, padicValRat.self hp.one_lt] at hv
    push_cast at hv ⊢
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_form_gauss_bound_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.NormFormGaussBound.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | exact GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound <;> assumption)
end
end
