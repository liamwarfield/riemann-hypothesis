module

public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsPointHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def latticeValue {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (v : Fin m → K') (b : Fin (N + 1)) : K' :=
  ∑ j, algebraMap K K' (φ b j) * v j

def latticeExtend {K : Type*} [Field K] [NumberField K] (K' : Type*) [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K') (Fin m → K') :=
  Submodule.span (𝓞 K') ((fun w : Fin m → K ↦ fun j ↦ algebraMap K K' (w j)) '' L)

def multiplierIdeal {L : Type*} [Field L] [NumberField L] {ι : Type*} (y : ι → L) :
    Submodule (𝓞 L) L where
  carrier := {a | ∀ i, a * y i ∈ Set.range (algebraMap (𝓞 L) L)}
  add_mem' := by
    intro a a' ha ha' i
    obtain ⟨c, hc⟩ := ha i
    obtain ⟨c', hc'⟩ := ha' i
    exact ⟨c + c', by rw [map_add (f := _), hc, hc', add_mul]⟩
  zero_mem' := fun _ ↦ ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    intro c a ha i
    obtain ⟨d, hd⟩ := ha i
    exact ⟨c * d, by rw [map_mul, hd, Algebra.smul_def, mul_assoc]⟩

def LineIdealDual.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (v : Fin (r + 1) → K') (a : K'),
      a • v ∈ latticeExtend K' F.lattice ↔
        ∀ b, a * latticeValue φ v b ∈ Set.range (algebraMap (𝓞 K') K')

def IdealIndexPlaces.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : Type) [Fintype ι] (y : ι → L), y ≠ 0 →
    genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup *
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) = 1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem exists_int_smul_mem_latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG)
    (v : Fin m → K) : ∃ D : ℤ, D ≠ 0 ∧ D • v ∈ latticeDual L := by
  classical
  obtain ⟨S, hS⟩ := hL
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : K) := fun k ↦ by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K k))
  have h1 : ∀ s : Fin m → K, ∃ D : ℤ, D ≠ 0 ∧ IsIntegral ℤ ((D : K) * (v ⬝ᵥ s)) := by
    intro s
    have halg : IsAlgebraic ℤ (v ⬝ᵥ s) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨D, hD, hD'⟩ := halg.exists_integral_multiple
    exact ⟨D, hD, by rwa [zsmul_eq_mul] at hD'⟩
  choose D hD0 hDint using h1
  refine ⟨∏ s ∈ S, D s, Finset.prod_ne_zero_iff.mpr fun s _ ↦ hD0 s, ?_⟩
  intro u hu
  rw [← hS] at hu
  rw [Set.mem_range, ← IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)]
  induction hu using Submodule.span_induction with
  | mem x hx =>
    rw [smul_dotProduct, zsmul_eq_mul, ← Finset.mul_prod_erase S D hx, Int.cast_mul,
      mul_comm (D x : K), mul_assoc]
    exact (hint _).mul (hDint x)
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add x y _ _ hx hy => rw [dotProduct_add]; exact hx.add hy
  | smul c x _ hx =>
    rw [dotProduct_smul, Algebra.smul_def]
    exact ((IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mpr ⟨c, rfl⟩).mul hx

variable {r N : ℕ}

theorem exists_int_comb {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (v : Fin (r + 1) → K) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = D • v := by
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg v
  have h : D • v ∈ Submodule.span ℤ (Set.range φ) := by rw [hφ.span_eq]; exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
  exact ⟨D, hD, c, hc⟩







end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsConeTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

def ConeTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), Geo.Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Geo.IsHorizontal (Geo.mCoordIdeal y) →
        Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ Ω + Fintype.card K

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DetGramLeProdNormSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace HadamardGramBound

theorem det_gram_le_prod_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    (Matrix.gram ℝ w).det ≤ ∏ i, ‖w i‖ ^ 2 := by
  set K := Submodule.span ℝ (Set.range w)
  have hK : Module.finrank ℝ K = Fintype.card (Fin n) := finrank_span_eq_card hw
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let w' : Fin n → K := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hg : Matrix.gram ℝ w = Matrix.gram ℝ w' := by
    ext i j
    simp [Matrix.gram_apply, w']
  let gb := InnerProductSpace.gramSchmidtOrthonormalBasis hK w'
  have hdet : gb.toBasis.det w' = ∏ i, inner ℝ (gb i) (w' i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hK w'
  rw [hg, Matrix.gram_eq_conjTranspose_mul gb, Matrix.det_mul, Matrix.det_conjTranspose]
  have hM : (Matrix.of fun i j => gb.repr (w' j) i) = gb.toBasis.toMatrix w' := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM, ← Module.Basis.det_apply, hdet, star_trivial, ← sq, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => ?_)
  have h1 := abs_real_inner_le_norm (gb i) (w' i)
  rw [gb.orthonormal.1 i, one_mul] at h1
  have h2 : ‖w' i‖ = ‖w i‖ := rfl
  rw [← h2, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

end HadamardGramBound

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineDegreeBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors

noncomputable section

theorem LineDegreeBundle.sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ ↦ ‖φ x‖)
    (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

theorem LineDegreeBundle.quad_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (u : Fin n → ℂ) :
    star (z • u) ⬝ᵥ (H *ᵥ (z • u)) = (star z * z) * (star u ⬝ᵥ (H *ᵥ u)) := by
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem LineDegreeBundle.quad_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) {u : Fin n → ℂ}
    (hu : u ≠ 0) :
    ‖star u ⬝ᵥ (H *ᵥ u)‖ = (star u ⬝ᵥ (H *ᵥ u)).re ∧ 0 < (star u ⬝ᵥ (H *ᵥ u)).re := by
  have h := hH.dotProduct_mulVec_pos hu
  obtain ⟨hre, him⟩ := Complex.lt_def.mp h
  have hQ : star u ⬝ᵥ (H *ᵥ u) = ((star u ⬝ᵥ (H *ᵥ u)).re : ℂ) :=
    Complex.ext rfl (by simp only [Complex.ofReal_im]; rw [← him]; rfl)
  refine ⟨?_, by simpa using hre⟩
  conv_lhs => rw [hQ]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SectionCycle

section Local

variable {S : Type*} [CommRing S]

theorem length_localized_eq {J J₁ W : Ideal S} [W.IsPrime] (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J₁)) := by
  let q : (S ⧸ J) →ₗ[S] (S ⧸ J₁) := Submodule.mapQ J J₁ LinearMap.id hJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J))
    (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J₁)) q
  have hφ : ∀ (x : S) (s : W.primeCompl), φ (LocalizedModule.mk (Submodule.Quotient.mk x) s) =
      LocalizedModule.mk (Submodule.Quotient.mk x) s := by
    intro x s
    rw [IsLocalizedModule.map_LocalizedModules]
    rfl
  have htW : t ∈ W.primeCompl := ht
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y
    refine LocalizedModule.induction_on (fun m s hy ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J m
    rw [hφ, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    simp only [smul_zero, one_smul] at hu
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul] at hu
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    refine ⟨⟨t, htW⟩ * u, ?_⟩
    simp only [smul_zero, one_smul]
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Submonoid.coe_mul, mul_assoc]
    exact hmul _ hu
  have hsurj : Function.Surjective φ := by
    intro y
    refine LocalizedModule.induction_on (fun m s ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J₁ m
    exact ⟨LocalizedModule.mk (Submodule.Quotient.mk x) s, hφ x s⟩
  exact ((LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

theorem mem_minimalPrimes_iff {J J₁ W : Ideal S} (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) : W ∈ J.minimalPrimes ↔ W ∈ J₁.minimalPrimes := by
  have key : ∀ Q : Ideal S, Q.IsPrime → Q ≤ W → (J ≤ Q ↔ J₁ ≤ Q) := fun Q hQ hQW ↦
    ⟨fun h x hx ↦ (hQ.mem_or_mem (h (hmul x hx))).resolve_left fun htQ ↦ ht (hQW htQ), hJ.trans⟩
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mp hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mpr hQ.2⟩ hQW⟩
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mpr hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mp hQ.2⟩ hQW⟩

end Local

section Cycle

variable {K : Type*} {κ : K → Type*} {R : Type*} [CommRing R]

end Cycle

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

section AddBlock

variable {P : ArithVariety n} (D : AddBlockData P)

variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}


end AddBlock

end SectionCycle

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightedHomogeneousComponentMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumbersDVR

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace WeightedDegree

section Localization

variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']


include M₀ in
theorem ringKrullDim_quotient_map_le (I : Ideal (MRing ι R)) :
    ringKrullDim (MRing ι R' ⧸ I.map (algebraMap (MRing ι R) (MRing ι R'))) ≤
      ringKrullDim (MRing ι R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let f : PrimeSpectrum.zeroLocus (R := MRing ι R') (I.map (algebraMap (MRing ι R) (MRing ι R'))) →
      PrimeSpectrum.zeroLocus (R := MRing ι R) I :=
    fun Q ↦ ⟨PrimeSpectrum.comap (algebraMap (MRing ι R) (MRing ι R')) Q.1, by
      have h := Q.2
      simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h ⊢
      exact Ideal.map_le_iff_le_comap.mp h⟩
  refine Order.krullDim_le_of_strictMono f (Monotone.strictMono_of_injective ?_ ?_)
  · intro Q₁ Q₂ h
    exact Ideal.comap_mono (f := algebraMap (MRing ι R) (MRing ι R')) h
  · intro Q₁ Q₂ h
    apply Subtype.ext
    apply PrimeSpectrum.localization_comap_injective (MRing ι R') (M₀.map (C (σ := Σ k, ι k)))
    exact congrArg Subtype.val h

theorem weightedHomogeneousComponent_map [DecidableEq K] (b : K → ℕ) (y : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) b (map (algebraMap R R') y) =
      map (algebraMap R R') (weightedHomogeneousComponent (blockWeight ι) b y) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp


include M₀ in
theorem isMultiHomogIdeal_map [DecidableEq K] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (algebraMap (MRing ι R) (MRing ι R'))) := by
  classical
  intro z hz b
  obtain ⟨⟨x, m⟩, hxm⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M₀.map (C (σ := Σ k, ι k))) (MRing ι R')).mp hz
  obtain ⟨r, hr, hrm⟩ := Submonoid.mem_map.mp m.2
  have hu : IsUnit (C (algebraMap R R' r) : MRing ι R') :=
    (IsLocalization.map_units R' (⟨r, hr⟩ : M₀)).map C
  have hm : algebraMap (MRing ι R) (MRing ι R') (m : MRing ι R) = C (algebraMap R R' r) := by
    rw [← hrm]
    exact map_C _ _
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, mul_comm, ← weightedHomogeneousComponent_C_mul, mul_comm,
    ← hm, hxm]
  change weightedHomogeneousComponent _ b (map (algebraMap R R') (x : MRing ι R)) ∈ _
  rw [weightedHomogeneousComponent_map]
  exact Ideal.mem_map_of_mem _ (hI x x.2 b)


include M₀ in
theorem cycEval_divCycle_map (P : Ideal (MRing ι R)) (f : MRing ι R)
    (hdisj : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
      Disjoint ((M₀.map (C (σ := Σ k, ι k)) : Submonoid (MRing ι R)) : Set (MRing ι R)) W)
    (n : Ideal (MRing ι R') → ℤ) :
    cycEval (fun W ↦ n (W.map (algebraMap (MRing ι R) (MRing ι R')))) (divCycle P f) =
      cycEval n (divCycle (P.map (algebraMap (MRing ι R) (MRing ι R')))
        (algebraMap (MRing ι R) (MRing ι R') f)) := by
  classical
  set M : Submonoid (MRing ι R) := M₀.map (C (σ := Σ k, ι k)) with hM
  set φ := algebraMap (MRing ι R) (MRing ι R') with hφ
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map φ := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hcorr : ∀ W ∈ J.minimalPrimes, (W.map φ).IsPrime ∧ (W.map φ).comap φ = W := fun W hW ↦
    ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ W hW.1.1 (hdisj W hW),
      IsLocalization.under_map_of_isPrime_disjoint M (MRing ι R') hW.1.1 (hdisj W hW)⟩
  have hmin : ∀ W ∈ J.minimalPrimes, W.map φ ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes := by
    intro W hW
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (W.map φ).comap φ ∈ J.minimalPrimes
    rw [(hcorr W hW).2]
    exact hW
  have hkey : ∀ W ∈ J.minimalPrimes, divCycle P f W = divCycle (P.map φ) (φ f) (W.map φ) := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨hWp', hcomap⟩ := hcorr W hW
    have hrel : IsRelevant (W.map φ) ↔ IsRelevant W := by
      refine forall_congr' fun k ↦ exists_congr fun i ↦ not_congr ?_
      have hX : (X ⟨k, i⟩ : MRing ι R') = φ (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
      rw [hX, ← Ideal.mem_comap, hcomap]
    have hl : ∀ (h₁ : W.IsPrime) (h₂ : (W.map φ).IsPrime),
        @multAt _ _ _ _ J W h₁ = @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f}) (W.map φ) h₂ := by
      intro h₁ h₂
      have := h₂
      unfold multAt
      rw [hJ]
      exact GenericCycleCorresp.length_eq M J W (hdisj W hW)
    unfold divCycle
    by_cases hr : IsRelevant W
    · rw [dite_eq_left ⟨hW, hr⟩, dite_eq_left ⟨hmin W hW, hrel.mpr hr⟩, hl]
    · rw [dite_eq_right (fun h ↦ hr h.2), dite_eq_right (fun h ↦ hr (hrel.mp h.2))]
  have hsupp : ∀ (Q : Ideal (MRing ι R')) (x) (W : Ideal (MRing ι R')),
      divCycle Q x W ≠ 0 → W ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    intro Q x W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  have hsupp0 : ∀ W : Ideal (MRing ι R), divCycle P f W ≠ 0 → W ∈ J.minimalPrimes := by
    intro W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  unfold cycEval
  have hA : (∑ᶠ W, divCycle P f W * n (W.map φ)) =
      ∑ᶠ W ∈ J.minimalPrimes, divCycle P f W * n (W.map φ) := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : divCycle P f W = 0 := by
      by_contra h
      exact hW (hsupp0 W h)
    rw [this, zero_mul]
  have hB : (∑ᶠ W, divCycle (P.map φ) (φ f) W * n W) =
      ∑ᶠ W ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes, divCycle (P.map φ) (φ f) W * n W := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : divCycle (P.map φ) (φ f) W = 0 := by
      by_contra h
      exact hW (hsupp _ _ W h)
    rw [this, zero_mul]
  rw [hA, hB]
  refine finsum_mem_eq_of_bijOn (fun W ↦ W.map φ) ⟨fun W hW ↦ hmin W hW, ?_, ?_⟩ ?_
  · intro W₁ hW₁ W₂ hW₂ h
    rw [← (hcorr W₁ hW₁).2, ← (hcorr W₂ hW₂).2]
    exact congrArg _ h
  · intro W' hW'
    have hW'm := hW'
    rw [hJ, IsLocalization.minimalPrimes_map M] at hW'm
    exact ⟨W'.comap φ, hW'm, IsLocalization.map_under M (MRing ι R') W'⟩
  · intro W hW
    rw [hkey W hW]

end Localization

theorem charZero_fractionRing (O : Type) [CommRing O] [IsDomain O]
    (h : Function.Injective (Int.castRingHom O)) : CharZero (FractionRing O) := by
  apply charZero_of_injective_algebraMap (R := ℤ)
  rw [RingHom.ext_int (algebraMap ℤ (FractionRing O))
    ((algebraMap O (FractionRing O)).comp (Int.castRingHom O))]
  exact (IsFractionRing.injective O (FractionRing O)).comp h

end WeightedDegree

end

end GroundTheory.Heights₂.Heights
end
