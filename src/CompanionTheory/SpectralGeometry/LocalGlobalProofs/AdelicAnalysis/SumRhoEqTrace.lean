module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
public import CompanionTheory.AutomorphicTheory.ThetaDilations.Nuabs

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def toA (x : ι → F) : ι → A F := fun j => algebraMap F (A F) (x j)

theorem oh_add {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F :=
  fun v => add_mem (hx v) (hy v)

theorem oh_zero : (0 : A F) ∈ Oh F := fun _ => zero_mem _

theorem oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v => neg_mem (hx v)


variable (ι F) in
def latN (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨z, hz, e'⟩ := hb i
    exact ⟨y + z, oh_add hy hz, by simp [e, e', mul_add]⟩
  zero_mem' := fun i => ⟨0, oh_zero, by simp⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, oh_neg hy, by simp [e]⟩

def indC (N : ℕ) (a : ι → F) : (ι → A F) → ℂ :=
  Set.indicator {x | x - toA a ∈ latN F ι N} fun _ => 1

def emb (ρ : InfinitePlace F → (F →+* ℝ)) (x : ι → F) : ι × InfinitePlace F → ℝ :=
  fun p => ρ p.2 (x p.1)

def cur (x : ι × InfinitePlace F → ℝ) : InfinitePlace F → ι → ℝ := fun w i => x (i, w)

def DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  blockDiagonal fun w => B.map (ρ w)

def ZM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℂ :=
  blockDiagonal fun w => fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

def EM (ρ : InfinitePlace F → (F →+* ℝ)) (b : InfinitePlace F → 𝓞 F) :
    Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
  fun w v => ρ w (b v : F)

def gM [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  (N : ℝ) • ((1 : Matrix ι ι ℝ) ⊗ₖ EM ρ b)

theorem sum_rho_eq_trace {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (c : F) :
    ∑ w, ρ w c = ((Algebra.trace ℚ F c : ℚ) : ℝ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := c)
  have hb : Function.Bijective
      (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) := by
    constructor
    · intro w v h
      have : w.embedding = v.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding v, this]
    · intro σ
      refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
      have hr : (InfinitePlace.mk σ.toRingHom).IsReal := hT.isReal _
      have he := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp hr)
      ext x
      show ((InfinitePlace.mk σ.toRingHom).embedding) x = σ x
      rw [he]
      rfl
  have h2 : ∑ σ : F →ₐ[ℚ] ℂ, σ c = ∑ w : InfinitePlace F, w.embedding c := by
    rw [← (Equiv.ofBijective _ hb).sum_comp]
    rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [hρ]
  rw [← h2, ← h1]
  simp

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolume
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolume
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FD

open scoped Pointwise

variable {F : Type} [Field F] [NumberField F]

def scaleMap (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : 𝓞 F →+ (InfinitePlace F → ℝ) where
  toFun r := fun w => ρ w ((N : F) * (r : F))
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [mul_add]

theorem latR_eq_range (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) :
    latR ρ N = (scaleMap ρ N).range := by
  have h : {y | ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))}
      = ((scaleMap ρ N).range : Set (InfinitePlace F → ℝ)) := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  rw [latR, h, AddSubgroup.closure_eq]

theorem mem_latR_iff (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) (y : InfinitePlace F → ℝ) :
    y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F)) := by
  rw [latR_eq_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem embedding_bijective (hF : IsTotallyReal F) :
    Function.Bijective (fun w : InfinitePlace F => (w.embedding : F →+* ℂ)) := by
  constructor
  · intro w w' h
    have := congrArg InfinitePlace.mk h
    simpa using this
  · intro φ
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (hF.isReal (InfinitePlace.mk φ))
    exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩

def placeEquiv (hF : IsTotallyReal F) : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective _ (embedding_bijective hF)).trans (RingHom.equivRatAlgHom F ℂ)

theorem card_places (hF : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (placeEquiv hF), AlgHom.card]

theorem exists_integral_basis [DecidableEq (InfinitePlace F)] (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ B : Module.Basis (InfinitePlace F) ℤ (𝓞 F),
      (Matrix.det (Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F))) ^ 2 = (discr F : ℝ) := by
  classical
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F) := by
    rw [card_places hF, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e0 := Fintype.equivOfCardEq hc
  let bq := (integralBasis F).reindex e0
  refine ⟨(RingOfIntegers.basis F).reindex e0, ?_⟩
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bq (placeEquiv hF)
  have hd : Algebra.discr ℚ bq = (discr F : ℚ) := by
    rw [coe_discr]
    have h0 := Algebra.discr_reindex ℚ (integralBasis F) e0
    rwa [← Module.Basis.coe_reindex] at h0
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ bq (placeEquiv hF) =
      (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F)).map
        Complex.ofRealHom := by
    ext i w
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, placeEquiv, bq, hρ,
      integralBasis_apply, Module.Basis.reindex_apply]
  rw [hM, hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : (((discr F : ℝ)) : ℂ) = (((Matrix.det (Matrix.of fun i w =>
      ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F))) ^ 2 : ℝ) : ℂ) := by
    simpa using h
  exact_mod_cast h2.symm

theorem exists_real_basis {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (h : A.det ≠ 0) :
    ∃ b : Module.Basis ι ℝ (ι → ℝ), ∀ i, b i = A i := by
  have hl : LinearIndependent ℝ A.row :=
    Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h))
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl (by simp), fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem sum_places_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : 𝓞 F) :
    ∃ z : ℤ, ∑ w, ρ w (a : F) = (z : ℝ) := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = Algebra.trace ℚ F (a : F) :=
    IsIntegrallyClosed.isIntegral_iff.1
      (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := F) (RingOfIntegers.isIntegral_coe a))
  refine ⟨z, ?_⟩
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := (a : F))
  rw [← (placeEquiv hF).sum_comp, ← hz] at h
  have h2 : ((z : ℝ) : ℂ) = ((∑ w, ρ w (a : F) : ℝ) : ℂ) := by
    push_cast
    simp only [hρ]
    simpa [placeEquiv] using h
  exact_mod_cast h2.symm

theorem integral_char_eq_zero (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (N : ℕ)
    [Countable (latR ρ N)]
    (D : Set (InfinitePlace F → ℝ)) (hD : IsAddFundamentalDomain (latR ρ N) D volume)
    (β : F) (hβ : β ≠ 0) (hint : ∃ r : 𝓞 F, (r : F) = (N : F) * β) :
    ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  classical
  set f : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hf
  have hadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, Complex.exp_add]
  have hper : ∀ (g : latR ρ N) x, f (g +ᵥ x) = f x := by
    rintro ⟨g, hg⟩ x
    obtain ⟨s, rfl⟩ := (mem_latR_iff ρ N g).1 hg
    obtain ⟨r, hr⟩ := hint
    obtain ⟨z, hz⟩ := sum_places_int hF ρ hρ (r * s)
    have hrs : ((r * s : 𝓞 F) : F) = (N : F) * β * (s : F) := by
      rw [← hr]
      rfl
    have h1 : f (fun w => ρ w ((N : F) * (s : F))) = 1 := by
      have : (∑ w, ρ w β * ρ w ((N : F) * (s : F))) = (z : ℝ) := by
        rw [← hz]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← map_mul]
        congr 1
        rw [hrs]
        ring
      simp only [hf, this]
      have := Complex.exp_int_mul_two_pi_mul_I z
      rw [← this]
      congr 1
      push_cast
      ring
    show f ((fun w => ρ w ((N : F) * (s : F))) + x) = f x
    rw [hadd, h1, one_mul]
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hρ0 : ρ w0 β ≠ 0 := by
    simpa using hβ
  let x0 : InfinitePlace F → ℝ := Pi.single w0 (1 / (2 * ρ w0 β))
  have hx0 : f x0 = -1 := by
    have : (∑ w, ρ w β * x0 w) = 1 / 2 := by
      rw [Finset.sum_eq_single w0]
      · simp only [x0, Pi.single_eq_same]
        field_simp
      · intro b _ hb
        simp [x0, Pi.single_eq_of_ne hb]
      · simp
    simp only [hf, this]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hD' : IsAddFundamentalDomain (latR ρ N) (x0 +ᵥ D) volume := hD.vadd_of_comm x0
  have heq : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f x := hD'.setIntegral_eq hD hper
  have htr : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f (x0 + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℝ)) x0).setIntegral_image_emb
      (measurableEmbedding_addLeft x0) f D
    rw [← this, ← Set.image_vadd]
    rfl
  have hmul : ∫ x in D, f (x0 + x) = - ∫ x in D, f x := by
    simp only [hadd, hx0]
    rw [integral_const_mul]
    ring
  have h2 : ∫ x in D, f x = - ∫ x in D, f x := by
    rw [← hmul, ← htr, heq]
  have h3 : (2 : ℂ) * ∫ x in D, f x = 0 := by
    linear_combination h2
  simpa using h3

end GlobalTheory.CompanionTheory.SW.FD

theorem GlobalTheory.CompanionTheory.SW.FD.main : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ N : ℕ, 0 < N → (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume) ∧ Countable (latR ρ N) ∧ (∀ y, y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))) ∧ ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹) ∧ ∀ β : F, β ≠ 0 → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  intro F _ _ hF ρ hρ N hN
  classical
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis hF ρ hρ
  set M : Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
    Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F) with hM
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdisc : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hdet : M.det ≠ 0 := by
    intro h
    apply hdisc
    rw [← hB, h]
    simp
  have hAdet : ((N : ℝ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hN') hdet
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_real_basis _ hAdet
  have hbi : ∀ i, b i = GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N (B i) := by
    intro i
    rw [hb]
    ext w
    simp [GlobalTheory.CompanionTheory.SW.FD.scaleMap, hM]
  have hspan : latR ρ N = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range, Submodule.span_int_eq_addSubgroupClosure]
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← B.sum_repr r, map_sum]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← hbi]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B i, (hbi i).symm⟩
  have hfd : IsAddFundamentalDomain (latR ρ N) (ZSpan.fundamentalDomain b) volume := by
    rw [hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hcount : Countable (latR ρ N) := by
    haveI : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range]
    exact (Set.countable_range (GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N)).to_subtype
  refine ⟨⟨_, hfd⟩, hcount, GlobalTheory.CompanionTheory.SW.FD.mem_latR_iff ρ N, fun D hD => ⟨?_, fun β hβ hint =>
    GlobalTheory.CompanionTheory.SW.FD.integral_char_eq_zero hF ρ hρ N D hD β hβ hint⟩⟩
  rw [hD.measure_eq hfd, ZSpan.volume_fundamentalDomain]
  have hof : Matrix.of (b : InfinitePlace F → InfinitePlace F → ℝ) = (N : ℝ) • M := by
    ext i w
    rw [Matrix.of_apply, hb]
  rw [hof, Matrix.det_smul, GlobalTheory.CompanionTheory.SW.FD.card_places hF, abs_mul, abs_of_nonneg (by positivity)]
  congr 2
  rw [kap, inv_inv, ← hB, abs_of_nonneg (sq_nonneg M.det), Real.sqrt_sq_eq_abs]
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolumeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_fundamental_domain_volume : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ N : ℕ, 0 < N → (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume) ∧ Countable (latR ρ N) ∧ (∀ y, y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))) ∧ ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹) ∧ ∀ β : F, β ≠ 0 → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.FD.main | exact GlobalTheory.CompanionTheory.SW.FD.main | (intros; apply GlobalTheory.CompanionTheory.SW.FD.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailCut

theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a) := by
    intro T
    have hs : Summable fun v => ‖T.mulIndicator a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum
      by_cases hv : v ∈ T
      · simp [Set.mulIndicator_of_mem hv, Real.norm_eq_abs]
      · simp [Set.mulIndicator_of_notMem hv]
    have h := multipliable_one_add_of_summable hs
    simpa using h
  have e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have hsplit : (∏' v, Set.mulIndicator {v | v ∉ S} a v) =
      ∏' v, (Set.mulIndicator (↑(S' \ S) : Set ι) a v * Set.mulIndicator {v | v ∉ S'} a v) := by
    refine tprod_congr fun v => ?_
    by_cases h1 : v ∈ S
    · have h2 : v ∈ S' := hSS' h1
      simp [Set.mulIndicator, h1, h2]
    · by_cases h2 : v ∈ S'
      · simp [Set.mulIndicator, h1, h2]
      · simp [Set.mulIndicator, h1, h2]
  have hfin : (∏' v, Set.mulIndicator (↑(S' \ S) : Set ι) a v) = ∏ v ∈ S' \ S, a v := by
    rw [tprod_eq_prod (s := S' \ S)]
    · exact Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv) a
    · intro v hv
      exact Set.mulIndicator_of_notMem (by rwa [Finset.mem_coe]) a
  rw [e1, e2, hsplit, Multipliable.tprod_mul (hmul _) (hmul _), hfin]

end GlobalTheory.CompanionTheory.SW.TailCut
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinsetStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_complement_split_finset : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι), Summable (fun v => |a v - 1|) → S ⊆ S' → ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | exact GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | (intros; apply GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlane
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlane
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Mobius

theorem den_ne (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (c : ℂ) * τ + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hτ
  · subst hc
    have hd : d = 0 := by simpa using hre
    subst hd
    simp at hdet
  · exact h.ne' hτ

theorem im_frac (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a : ℂ) * τ + b) / ((c : ℂ) * τ + d)).im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq, ← sub_div]
  congr 1
  simp
  linear_combination τ.im * hdet

theorem comp_frac (a b c d a' b' c' d' : ℝ) (hdet : a * d - b * c = 1)
    (hdet' : a' * d' - b' * c' = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) /
        (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) =
      ((a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b) /
        ((c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d) := by
  have h' := den_ne a' b' c' d' hdet' τ h
  have hX : 0 < (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')).im := by
    rw [im_frac a' b' c' d' hdet' τ h]
    have : 0 < ‖(c' : ℂ) * τ + d'‖ := norm_pos_iff.mpr h'
    positivity
  have h2 := den_ne a b c d hdet _ hX
  have e1 : (c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d =
      (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  have e2 : (a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b =
      (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  rw [e1, e2, div_div_div_cancel_right₀ h']

variable {F : Type} [Field F]

theorem det_emb (σ : F →+* ℝ) (γ : SL(2, F)) :
    σ (γ 0 0) * σ (γ 1 1) - σ (γ 0 1) * σ (γ 1 0) = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg σ h
  simpa using this

theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (τ : InfinitePlace F → ℂ), (∀ w, 0 < (τ w).im) → (∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im = (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 ∧ 0 < (mob ρ γ τ w).im) ∧ (∀ γ γ' : SL(2, F), mob ρ (γ * γ') τ = mob ρ γ (mob ρ γ' τ)) ∧ (∀ b : F, mob ρ (nMat b) τ = fun w => τ w + (ρ w b : ℝ)) ∧ (∀ a : Fˣ, mob ρ (mMat a) τ = fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) ∧ mob ρ wMat τ = fun w => -(τ w)⁻¹ := by
  intro F _ _ ρ τ hτ
  have him : ∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im =
      (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 := fun γ w =>
    im_frac _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)
  refine ⟨fun γ w => ⟨him γ w, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [him]
    have h1 := den_ne _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)
    have : 0 < ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ := norm_pos_iff.mpr h1
    have := hτ w
    positivity
  · intro γ γ'
    funext w
    have := comp_frac _ _ _ _ _ _ _ _ (det_emb (ρ w) γ) (det_emb (ρ w) γ') (τ w) (hτ w)
    simp only [mob, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul]
    exact this
  · intro b
    funext w
    simp [mob, nMat]
  · intro a
    funext w
    have ha : (ρ w (a : F) : ℝ) ≠ 0 := by simp
    have hinv : ρ w ((a⁻¹ : Fˣ) : F) = (ρ w (a : F))⁻¹ := by simp
    have hc : ((ρ w (a : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
    simp [mob, mMat, hinv]
    field_simp
  · funext w
    simp [mob, wMat, neg_div, div_neg]

end GlobalTheory.CompanionTheory.SW.Core.Mobius
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlaneStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobius_action_upper_half_plane : ∀ (F : Type) [Field F] [NumberField F], ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (τ : InfinitePlace F → ℂ), (∀ w, 0 < (τ w).im) → (∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im = (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 ∧ 0 < (mob ρ γ τ w).im) ∧ (∀ γ γ' : SL(2, F), mob ρ (γ * γ') τ = mob ρ γ (mob ρ γ' τ)) ∧ (∀ b : F, mob ρ (nMat b) τ = fun w => τ w + (ρ w b : ℝ)) ∧ (∀ a : Fˣ, mob ρ (mMat a) τ = fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) ∧ mob ρ wMat τ = fun w => -(τ w)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Mobius.main | exact GlobalTheory.CompanionTheory.SW.Core.Mobius.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Mobius.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularity
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularity
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThetaUD

variable {F : Type} [Field F] [NumberField F]

theorem form_mulVec {R ι : Type} [CommRing R] [Fintype ι] (G Q : Matrix ι ι R) (h : Gᵀ * Q * G = Q)
    (v : ι → R) : (G *ᵥ v) ⬝ᵥ (Q *ᵥ (G *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by
  conv_rhs => rw [← h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

theorem form_map {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : Matrix ι ι R)
    (x : ι → R) : (fun j => f (x j)) ⬝ᵥ (Q.map f *ᵥ fun j => f (x j)) = f (x ⬝ᵥ (Q *ᵥ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec f Q x i).symm

theorem trace_eq_sum (hT : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (y : F) :
    ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ w, ((ρ w y : ℝ) : ℂ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  have h2 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by simp
  rw [h2, h1]
  symm
  refine Fintype.sum_bijective (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) ?_ _ _ ?_
  · constructor
    · intro w w' h
      have : w.embedding = w'.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', this]
    · intro σ
      have hr : (InfinitePlace.mk (σ : F →+* ℂ)).IsReal := hT.isReal _
      have hc : ComplexEmbedding.IsReal (σ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 hr
      refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
      ext x
      have := InfinitePlace.embedding_mk_eq_of_isReal hc
      simp [this]
  · intro w
    simp [hρ]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_add (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => τ w + (c w : ℝ)) y = gauss B ρ P τ y *
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ∑ w, ((c w : ℂ) * ((y w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
  unfold gauss
  rw [← Complex.exp_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  push_cast
  ring

theorem gauss_sq (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => ((c w : ℝ) : ℂ) ^ 2 * τ w) y = gauss B ρ P τ (fun w => c w • y w) := by
  unfold gauss
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : (((c w : ℝ) : ℂ) ^ 2 * τ w).re = c w ^ 2 * (τ w).re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have him : (((c w : ℝ) : ℂ) ^ 2 * τ w).im = c w ^ 2 * (τ w).im := by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  rw [hre, him]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring

theorem term_U (ψ : AddChar (A F) ℂ) (hψ : IsStdChar F ψ) (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (hQ : QSetup M B ρ P)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (hO : IsOrth B ρ gf gi)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (b : F) (x : ι → F) :
    thTerm B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) x =
      thTerm B ρ P gf gi φ τ x := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  obtain ⟨hOf, hOi⟩ := hO
  set t : F := x ⬝ᵥ (B *ᵥ x) with ht
  have hfin : qf (hf F) (Bf B) (gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      algebraMap F (A F) (1 / 2 * t) := by
    unfold qf
    rw [form_mulVec gf (Bf B) hOf]
    have := form_map (algebraMap F (A F)) B x
    unfold Bf hf
    rw [this, map_mul]
  have hinf : ∀ w, (gi w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (B.map (ρ w) *ᵥ (gi w *ᵥ fun j => ρ w (x j))) =
      ρ w t := by
    intro w
    rw [form_mulVec (gi w) _ (hOi w), form_map]
  have hphase : ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) = 1 := by
    rw [← map_mul, hψ.2, trace_eq_sum hT ρ hρ, ← Complex.exp_add]
    have : ∑ w, ((ρ w (b * (1 / 2 * t)) : ℝ) : ℂ) = (1 / 2) * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [map_mul, map_div₀, map_one, map_ofNat]
      push_cast
      ring
    rw [this]
    have h0 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) +
        (Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  unfold thTerm opU
  rw [gauss_add B ρ P τ (fun w => ρ w b), hfin]
  simp only [hinf]
  calc _ = (ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)))) *
        (φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) *
          gauss B ρ P τ fun w => gi w *ᵥ fun j => ρ w (x j)) := by ring
    _ = _ := by rw [hphase, one_mul]

theorem term_D (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (a : F) (x : ι → F) :
    thTerm B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) x =
      thTerm B ρ P gf gi φ τ (a • x) := by
  unfold thTerm opD
  rw [gauss_sq B ρ P τ (fun w => ρ w a)]
  have h1 : (algebraMap F (A F) a • gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      gf *ᵥ fun j => algebraMap F (A F) ((a • x) j) := by
    rw [← Matrix.mulVec_smul]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  have h2 : (fun w => ρ w a • gi w *ᵥ fun j => ρ w (x j)) =
      fun w => gi w *ᵥ fun j => ρ w ((a • x) j) := by
    funext w
    rw [← Matrix.mulVec_smul]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  intro F _ _ ψ hψ ι _ _ M B ρ P hQ gf gi hO φ τ
  refine ⟨fun b => ?_, fun a ha => ?_, fun c => ?_⟩
  · unfold theta
    exact tsum_congr fun x => term_U ψ hψ M B ρ P hQ gf gi hO φ τ b x
  · unfold theta
    simp only [term_D]
    exact (MulAction.toPerm (Units.mk0 a ha) : Equiv.Perm (ι → F)).tsum_eq (thTerm B ρ P gf gi φ τ)
  · unfold theta
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [thTerm, mul_assoc]

end GlobalTheory.CompanionTheory.SW.ThetaUD
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularityStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_modularity : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaUD.main | exact GlobalTheory.CompanionTheory.SW.ThetaUD.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaUD.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBound
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem integral_fundamentalDomain_le_siegel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact CompanionTheory.PlacePermOperatorBicommutantSpan.cover | exact @CompanionTheory.PlacePermOperatorBicommutantSpan.cover

end GlobalTheory.CompanionTheory.Adelic
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBoundStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_measure_compact_cover_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | exact GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | (intros; apply GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureIwasawaDecomposition
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureIwasawaDecomposition
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem tripleProduct_map_leftInvariant : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  exact CompanionTheory.PlacePermOperatorBicommutantSpan.nuabs

end GlobalTheory.CompanionTheory.Adelic
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureIwasawaDecompositionStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_product_measure_map_mul_left_invariant : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant | exact GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant | (intros; apply GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetReps
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetReps
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem unfold_coset_sum_fundamentalDomain : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.unf

end GlobalTheory.CompanionTheory.Adelic
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetRepsStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | exact GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentities
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentities
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition

private theorem coe_n {R : Type} [CommRing R] (b : R) :
    ((nMat b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl

private theorem coe_m {R : Type} [CommRing R] (a : Rˣ) :
    ((mMat a : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] := rfl

private theorem coe_w {R : Type} [CommRing R] :
    ((wMat : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] := rfl

private theorem SL2_eq_of_entries_eq_matrix {R : Type} [CommRing R] {g : SL(2, R)} {p q r s : R}
    {h : SL(2, R)} (hh : (h : Matrix (Fin 2) (Fin 2) R) = !![p, q; r, s])
    (h0 : g 0 0 = p) (h1 : g 0 1 = q) (h2 : g 1 0 = r) (h3 : g 1 1 = s) : g = h := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) R) = (h : Matrix (Fin 2) (Fin 2) R)
  rw [hh, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R), h0, h1, h2, h3]

theorem decompositions : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  intro R _ g
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hw : (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (((wMat * (wMat * wMat * wMat) : SL(2, R))) : Matrix (Fin 2) (Fin 2) R) = ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_w,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  refine ⟨?_, ?_, ?_, hw⟩
  · intro c hc
    have hu : (c : R) * ((c⁻¹ : Rˣ) : R) = 1 := by simp
    have hinv : ((-c⁻¹ : Rˣ) : R) = -((c⁻¹ : Rˣ) : R) := by simp
    have hinv2 : (((-c⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = -(c : R) := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two, hinv, hinv2]
    generalize ((c⁻¹ : Rˣ) : R) = u at hu
    rw [hc] at hdet ⊢
    congr
    · linear_combination (g 0 0) * hu
    · linear_combination (g 0 0 * g 1 1 * u + g 0 1) * hu + u * hdet
    · ring
    · linear_combination (g 1 1) * hu
  · intro a ha
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    rw [hw]
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · linear_combination (g 1 0) * hu
    · linear_combination (g 1 0 * g 0 1 * u + g 1 1) * hu - u * hdet
  · intro a ha hc
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha, hc] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · ring
    · linear_combination (g 1 1) * hu - u * hdet

end GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentitiesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SL2_bruhat_decompositions_and_w_inv : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | exact GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions <;> assumption)
end
end
