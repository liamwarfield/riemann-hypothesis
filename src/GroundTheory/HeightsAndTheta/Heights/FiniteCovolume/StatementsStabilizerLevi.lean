module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal

noncomputable section

section Radical

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w ∧ ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w}
  one_mem' w := ⟨by simp, fun z _ => ⟨0, by simp⟩⟩
  mul_mem' {a b} ha hb w := by
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, (hb w).1,
        (ha w).1]
    · obtain ⟨c, hc⟩ := (hb w).2 z hz
      obtain ⟨d, hd⟩ := (ha w).2 z hz
      refine ⟨d + c, ?_⟩
      simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hc,
        Matrix.mulVec_add, Matrix.mulVec_smul, hd, (ha w).1, add_smul]
      abel
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hx : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x₀ w = vecAt v x₀ w := by
      conv_lhs => rw [← (ha w).1]
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    refine ⟨hx, fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := (ha w).2 z hz
    refine ⟨-c, ?_⟩
    have := congrArg ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ ·) hc
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hx] at this
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← this]

omit [NumberField E] in
theorem mem_unipRadical {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ unipRadical h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w ∧
        ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w :=
  Iff.rfl


omit [NumberField E] in
theorem unipRadical_le_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    unipRadical h v x₀ ≤ vecFixGroup h v x₀ :=
  fun _ hg w => (hg w).1


omit [NumberField E] in
theorem isClosed_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (unipRadical h v x₀ : Set (archUnitary h v)) := by
  have hc : ∀ w, Continuous fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
  have : (unipRadical h v x₀ : Set (archUnitary h v)) = ⋂ w, ({g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} ∩
      ⋂ z ∈ {z : ι → ℂ | star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0},
        (fun g : archUnitary h v => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z - z) ⁻¹'
          (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ))) := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRadical, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage, Submodule.mem_span_singleton]
    refine forall_congr' fun w => and_congr Iff.rfl (forall_congr' fun z => imp_congr_right
      fun _ => ⟨fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩⟩)
  rw [this]
  refine isClosed_iInter fun w => (isClosed_eq ((hc w).matrix_mulVec continuous_const)
    continuous_const).inter (isClosed_biInter fun z _ => ?_)
  exact (Submodule.closed_of_finiteDimensional _).preimage
    (((hc w).matrix_mulVec continuous_const).sub continuous_const)

instance locallyCompactSpace_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (unipRadical h v x₀) :=
  (isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableTopology_unipRadical (h : HermitianForm F E W) (v : Basis ι E W)
    (x₀ : W) : SecondCountableTopology (unipRadical h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end Radical

section Structure

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def StabilizerLevi.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∀ (n : ℕ) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
    ∃ (i : archUnitary h' v' →* vecFixGroup h v x₀) (q : vecFixGroup h v x₀ →* archUnitary h' v'),
      Continuous i ∧ Continuous q ∧ (∀ m, q (i m) = m) ∧
      (∀ g, q g = 1 ↔ (g : archUnitary h v) ∈ unipRadical h v x₀) ∧
      (∀ m, ((i m : vecFixGroup h v x₀) : archUnitary h v) ∈ vecFixGroup h v w₀) ∧
      ∀ (γ : h.unitaryGroup) (m : h'.unitaryGroup), γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        ((i (archEmbed h' v' m) : vecFixGroup h v x₀) : archUnitary h v) = archEmbed h v γ

def UnipotentModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (μ : Measure (unipRadical h v x₀)) [μ.IsHaarMeasure],
    ∀ g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀,
      μ.map (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) = μ.map Subtype.val

def UnipotentCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ C : Set (unipRadical h v x₀), IsCompact C ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧ δ * n ∈ C

def CongruenceLift.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∃ (D' : ℕ) (La' : AddSubgroup (hypComplement h x₀ w₀)) (G'' : Subgroup h'.unitaryGroup),
      IsDIntegral h' D' La' ∧ G'' ≤ latticeStab h' La' ∧ G''.relIndex (latticeStab h' La') ≠ 0 ∧
      ∀ m ∈ G'', ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        γ ∈ latticeStab h La

end Structure

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

section LineStab

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    c • vecAt v x₀ w}
  one_mem' w := ⟨1, by simp⟩
  mul_mem' {a b} ha hb w := by
    obtain ⟨c, hc⟩ := ha w
    obtain ⟨d, hd⟩ := hb w
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_smul, hc, smul_smul, mul_comm d c]
  inv_mem' {a} ha w := by
    obtain ⟨c, hc⟩ := ha w
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz : vecAt v x₀ w = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ) *ᵥ (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    by_cases hc0 : c = 0
    · have h0 : vecAt v x₀ w = 0 := by
        rw [hz, hc, hc0, zero_smul, Matrix.mulVec_zero]
      exact ⟨0, by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
          = c⁻¹ • ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
              (c • vecAt v x₀ w)) := by
            rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • vecAt v x₀ w := by rw [← hc, ← hz]

omit [NumberField E] in
theorem mem_lineStab {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W} {g : archUnitary h v} :
    g ∈ lineStab h v x₀ ↔ ∀ w, ∃ c : ℂ,
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = c • vecAt v x₀ w :=
  Iff.rfl


omit [NumberField E] in
theorem vecFixGroup_le_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    vecFixGroup h v x₀ ≤ lineStab h v x₀ := fun g hg w => ⟨1, by rw [one_smul]; exact hg w⟩


omit [NumberField E] in
theorem isClosed_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (lineStab h v x₀ : Set (archUnitary h v)) := by
  have : (lineStab h v x₀ : Set (archUnitary h v)) = ⋂ w, (fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) ⁻¹'
        (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_singleton,
      mem_lineStab]
    exact forall_congr' fun w => ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [this]
  refine isClosed_iInter fun w => IsClosed.preimage ?_ (Submodule.closed_of_finiteDimensional _)
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const

instance locallyCompactSpace_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (lineStab h v x₀) :=
  (isClosed_lineStab h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

end LineStab

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ (μP : Measure (lineStab h v x₀)) [μP.IsHaarMeasure],
    ∃ (ν : Measure (vecFixGroup h v x₀)) (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ Measurable τ ∧ (∀ b, τ b ∈ lineStab h v x₀) ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ φ : archUnitary h v → ℝ≥0∞, Measurable φ →
        ∫⁻ p, φ (p : archUnitary h v) ∂μP = ∫⁻ b : InfinitePlace E → ℂ,
          (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
            ∫⁻ x : vecFixGroup h v x₀, φ ((x : archUnitary h v) * τ b) ∂ν

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMahlerCompactness
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem vecAt_unitary (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup) (x : W)
    (w : InfinitePlace E) :
    vecAt v ((γ : W ≃ₗ[E] W) x) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w := by
  have h1 : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  have h2 := LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x
  rw [LinearEquiv.coe_coe] at h2
  rw [h1]
  ext i
  simp only [vecAt]
  rw [← h2, RingHom.map_mulVec]
  rfl

theorem invApply_archEmbed_mul (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (g : archUnitary h v) (x : W) :
    invApply (archEmbed h v γ * g) (vecAt v ((γ : W ≃ₗ[E] W) x)) = invApply g (vecAt v x) := by
  funext w
  simp only [invApply, vecAt_unitary, Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply,
    Matrix.mulVec_mulVec]
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem MahlerCompactness.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hB : BoundedGenerators.Statement h v) (hCS : LenCauchySchwarz.Statement h v)
    (hG : GramDetermines.Statement h) (hK : BoundedInverseCompact.Statement h v) :
    MahlerCompactness.Statement h v := by
  intro M D t ht
  obtain ⟨n, C, hC⟩ := hB M D t ht

  let P : Set (AddSubgroup W × (Fin n → W)) := {p | IsDIntegral h D p.1 ∧
    AddSubgroup.closure (Set.range p.2) = p.1 ∧
      ∃ g : archUnitary h v, ∀ a, M.len (invApply g (vecAt v (p.2 a))) ≤ C}
  let gr : (Fin n → W) → Matrix (Fin n) (Fin n) E := fun e a b => h.toSesq (e a) (e b)
  let T : Set (Matrix (Fin n) (Fin n) E) := (fun p => gr p.2) '' P
  have hT : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C * C})
      fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (C * C)).subset ?_
    rintro _ ⟨p, ⟨hD, hcl, g, hg⟩, rfl⟩
    intro a _ b _
    have hmem : ∀ c, p.2 c ∈ p.1 := fun c => hcl ▸ AddSubgroup.subset_closure ⟨c, rfl⟩
    refine Set.mem_ofPred.2 ⟨(mem_integralClosure_iff ℤ E).1 (hD.integral _ (hmem a) _ (hmem b)), fun φ => ?_⟩
    have h1 := hCS M g (p.2 a) (p.2 b) (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1.trans (mul_le_mul (hg a) (hg b) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hg a)))
  have hrep : ∀ H ∈ T, ∃ p ∈ P, gr p.2 = H := fun H ⟨p, hp, hH⟩ => ⟨p, hp, hH⟩
  choose! rep hrepP hrepG using hrep
  let Kset : (Fin n → W) → Set (archUnitary h v) :=
    fun e => {g | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  refine ⟨(fun H => (rep H).1) '' T, hT.image _, ⋃ H ∈ T, Kset (rep H).2,
    hT.isCompact_biUnion fun H hH => hK M n (rep H).2 ?_ C, ?_⟩
  · obtain ⟨hD, hcl, -⟩ := hrepP H hH
    have hsp := hD.isLattice.span_eq_top
    rw [← hcl] at hsp
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    exact (AddSubgroup.closure_le (Submodule.span E (Set.range (rep H).2)).toAddSubgroup).2
      Submodule.subset_span hx
  · intro La g hLa hmin
    obtain ⟨e, he, heC⟩ := hC La g hLa hmin
    have hH : gr e ∈ T := ⟨(La, e), ⟨hLa, he, g, heC⟩, rfl⟩
    obtain ⟨hD', hcl', -⟩ := hrepP _ hH
    have hgr := hrepG _ hH
    obtain ⟨γ, hγ⟩ := hG n e (rep (gr e)).2 (he ▸ hLa.isLattice) (hcl' ▸ hD'.isLattice)
      fun a b => (congrFun (congrFun hgr a) b).symm
    refine ⟨γ, ⟨gr e, hH, ?_⟩, Set.mem_biUnion hH fun a => ?_⟩
    · show (rep (gr e)).1 = γ • La
      rw [← hcl', ← he, Subgroup.smul_def, AddSubgroup.pointwise_smul_def]
      erw [AddMonoidHom.map_closure]
      rw [← Set.range_comp]
      exact congrArg (fun s => AddSubgroup.closure (Set.range s)) (funext fun a => (hγ a).symm)
    · show M.len (invApply (archEmbed h v γ * g) (vecAt v ((rep (gr e)).2 a))) ≤ C
      rw [← hγ a, invApply_archEmbed_mul]
      exact heC a

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

noncomputable section

def LineIndexNeZero.Statement (E W : Type*) [Field E] [NumberField E] [AddCommGroup W] [Module E W] :
    Prop :=
  ∀ (La : AddSubgroup W) (x : W), IsLattice E La → x ∈ La → x ≠ 0 → lineIndex E La x ≠ 0

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceUnitsFiniteIndex
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem CongruenceUnitsFiniteIndex.proof (E : Type*) [Field E] [NumberField E] :
    CongruenceUnitsFiniteIndex.Statement E := by
  intro N hN
  have hI : Ideal.span {(N : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ :=
    Finite.of_injective _ Units.val_injective
  have : (congruenceUnits E N).FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.FiniteIndex.index_ne_zero

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ArchUnimodular.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure], μ.IsMulRightInvariant

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantStabCompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, IsCompact (M.stab : Set (archUnitary h v))

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerCovolume
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def StabilizerCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∀ (ν : Measure (vecFixGroup h v x₀)), ν.IsHaarMeasure →
    ∃ FD₀ : Set (vecFixGroup h v x₀),
      IsFundamentalDomain ((vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀)) FD₀ ν ∧
      0 < ν FD₀ ∧ ν FD₀ < ⊤

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHyperbolicPairs
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Transitive

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def HyperbolicPairTransitive.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v w v' w' : W, IsHyperbolicPair h v w → IsHyperbolicPair h v' w' →
    ∃ g : h.unitaryGroup, g • v = v' ∧ g • w = w'

end Transitive

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementExtension
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Extension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def ComplementExtension.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w → ∀ h' : HermitianForm F E (hypComplement h v w),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ m : h'.unitaryGroup,
    ∃ g : h.unitaryGroup, g • v = v ∧ g • w = w ∧
      ∀ x : hypComplement h v w, g • (x : W) = ((m • x : hypComplement h v w) : W)

end Extension

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementLattice
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def ComplementLattice.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D n : ℕ, 0 < n → ∃ D' : ℕ,
      ∀ La : AddSubgroup W, IsDIntegral h D La →
        (∀ x ∈ La, ∃ a ∈ lineCoeffs (E := E) La v₀, ∃ b ∈ lineCoeffs (E := E) La w₀,
          n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) →
        IsDIntegral h' D' (La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Complement

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLineNormalForm
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section NormalForm

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def LineNormalForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n : ℕ, 0 < n ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ v w : W, v ∈ l ∧ IsHyperbolicPair h v w ∧
        (lineCoeffs (E := E) La v, lineCoeffs (E := E) La w) ∈ KK ∧
        ∀ x ∈ La, (n : E) * h.toSesq w x ∈ lineCoeffs (E := E) La v ∧
          (n : E) * h.toSesq v x ∈ lineCoeffs (E := E) La w

end NormalForm

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHaarParabolicCoordinates
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HaarParabolicCoordinates.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (x₀ : W), x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ (ν : Measure (vecFixGroup h v x₀)) (κ : Measure M.stab)
      (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧ Measurable τ ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ f : archUnitary h v → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = ∫⁻ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
          ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f (x * (τ b * k)) ∂ν ∂κ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdaptedReduction
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Reduction

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def AdaptedReduction.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D : ℕ,
    ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n D' : ℕ, 0 < n ∧
      ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
        ∃ (g : h.unitaryGroup) (La₁ : AddSubgroup W), g • La₁ = La ∧ g • v₀ ∈ l ∧
          (lineCoeffs (E := E) La₁ v₀, lineCoeffs (E := E) La₁ w₀) ∈ KK ∧
          (∀ x ∈ La₁, ∃ a ∈ lineCoeffs (E := E) La₁ v₀, ∃ b ∈ lineCoeffs (E := E) La₁ w₀,
            n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) ∧
          IsDIntegral h' D' (La₁.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Reduction

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding

noncomputable section

variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

def mixedSpaceEquivPiOfTotallyComplex [_root_.NumberField.IsTotallyComplex E] :
    mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ) where
  toFun p w := p.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun g := (0, fun w => g w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ rfl
    funext w
    exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
  right_inv _ := rfl

def embeddingBasisOfTotallyComplex [_root_.NumberField.IsTotallyComplex E] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ) :=
  (latticeBasis E).map (mixedSpaceEquivPiOfTotallyComplex E)

theorem embeddingBasisOfTotallyComplex_apply [_root_.NumberField.IsTotallyComplex E]
    (j : Free.ChooseBasisIndex ℤ (𝓞 E)) (w : InfinitePlace E) :
    embeddingBasisOfTotallyComplex E j w = w.embedding (integralBasis E j) := by
  rw [embeddingBasisOfTotallyComplex, Basis.map_apply, latticeBasis_apply]
  exact mixedEmbedding_apply_isComplex _ _ ⟨w, IsTotallyComplex.isComplex w⟩

def piSwapEquiv : (ι → InfinitePlace E → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ι → ℂ) :=
  { Equiv.piComm (fun (_ : ι) (_ : InfinitePlace E) => ℂ) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem CoordEmbedBasis.proof [_root_.NumberField.IsTotallyComplex E] : CoordEmbedBasis.Statement E ι := by
  classical
  let B := (Pi.basis fun _ : ι => embeddingBasisOfTotallyComplex E).map (piSwapEquiv E ι)
  have hB : ∀ k, B k = coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) := by
    rintro ⟨i, j⟩
    funext w i'
    simp only [B, Basis.map_apply, Pi.basis_apply, coordEmbed_apply]
    show (Pi.single i (embeddingBasisOfTotallyComplex E j) : ι → InfinitePlace E → ℂ) i' w = _
    by_cases h : i' = i
    · subst h
      simp [embeddingBasisOfTotallyComplex_apply]
    · simp [Pi.single_eq_of_ne h]
  refine ⟨?_, ?_⟩
  · have hli := B.linearIndependent
    rwa [show (⇑B) = fun k => coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) from
      funext hB] at hli
  · rw [finrank_eq_card_basis B, finrank_eq_card_basis (Pi.basis fun _ : ι => integralBasis E)]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Fintype ι]
  [DecidableEq ι] in
theorem two_le_finrank_of_isotropic [FiniteDimensional E W] (h : HermitianForm F E W) {x₀ : W}
    (hne : x₀ ≠ 0) (hiso : h.toSesq x₀ x₀ = 0) : 2 ≤ finrank E W := by
  by_contra hlt
  have hpos : 0 < finrank E W := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x₀, hne⟩
  have h1 : finrank E W = 1 := by omega
  have hspan := (finrank_eq_one_iff_of_nonzero' x₀ hne).mp h1
  apply hne
  apply h.nonsingular.1
  rw [map_zero]
  ext y
  obtain ⟨c, rfl⟩ := hspan y
  rw [LinearMap.zero_apply, map_smul, hiso, smul_zero]


omit [DecidableEq ι] in
theorem re_form_smul (P : Matrix ι ι ℂ) (b : ℂ) (y : ι → ℂ) :
    (star (b • y) ⬝ᵥ (P *ᵥ (b • y))).re = (star y ⬝ᵥ (P *ᵥ y)).re * ‖b‖ ^ 2 := by
  have hb : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, hb, Complex.re_ofReal_mul, mul_comm]

theorem UnfoldingIntegral.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : UnfoldingTorus.Statement h v)
    (h₂ : TorusIntegralHomogeneous.Statement (InfinitePlace E))
    (h₃ : DiscreteFundamentalDomain.Statement (archUnitary h v)) :
    UnfoldingIntegral.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  have : FiniteDimensional E W := v.finiteDimensional_of_finite

  have hdisc : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨FD, -, hFD⟩ := h₃ μ _ hdisc
  obtain ⟨c, hc0, hctop, hc⟩ := h₁ M μ D La x₀ hLa hx₀ hne hiso
  set y := vecAt v x₀ with hy
  set q : InfinitePlace E → ℝ := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re with hq_def
  have hq : ∀ w, 0 < q w := fun w =>
    (Complex.pos_iff.mp ((M.posDef w).dotProduct_mulVec_pos (VecAtNeZero.proof v x₀ hne w))).1
  obtain ⟨C, hC0, hCtop, hC⟩ := h₂ q hq (finrank E W - 2)

  obtain ⟨k, hk⟩ : ∃ k, finrank E W = k + 2 :=
    ⟨finrank E W - 2, by have := two_le_finrank_of_isotropic h hne hiso; omega⟩
  have hcard : Fintype.card (InfinitePlace E) = finrank ℚ F := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h2
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have hexp : (2 * (finrank E W - 2) + 2) * Fintype.card (InfinitePlace E) =
      2 * finrank ℚ F * (finrank E W - 1) := by
    rw [hcard, hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    ring
  refine ⟨FD, hFD, c * C, ENNReal.mul_pos hc0.ne' hC0.ne', ENNReal.mul_lt_top hctop hCtop,
    fun t ht => ?_⟩

  have hset : {b : InfinitePlace E → ℂ | M.len (fun w => b w • y w) < t} =
      {b | ∑ w, q w * ‖b w‖ ^ 2 < t ^ 2} := by
    ext b
    simp only [Set.mem_ofPred_eq, Majorant.len, Real.sqrt_lt' ht, re_form_smul, hq_def,
      mul_comm]
  rw [hc FD hFD t ht, hset, hC t ht, hexp]
  exact (mul_assoc c C _).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
