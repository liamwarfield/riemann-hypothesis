module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticeOrbitsFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem isIsotropicLine_span_singleton (h : HermitianForm F E W) {x : W} (hx : x ≠ 0)
    (hxx : h.toSesq x x = 0) : IsIsotropicLine h (Submodule.span E {x}) := by
  refine ⟨finrank_span_singleton hx, ?_⟩
  intro a ha b hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hb
  simp only [map_smul, LinearMap.map_smulₛₗ₂, hxx, smul_zero]

theorem LatticeOrbitsFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : MahlerCompactness.Statement h v) (h₂ : MajorantExists.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : LinePairOrbitsFinite.Statement h) :
    LatticeOrbitsFinite.Statement h := by
  intro D
  obtain ⟨M⟩ := h₂
  obtain ⟨S₁, hS₁, K, -, hK⟩ := h₁ M D 1 one_pos
  obtain ⟨S₂, hS₂, hP⟩ := h₄ D
  refine ⟨S₁ ∪ Prod.fst '' S₂, hS₁.union (hS₂.image _), ?_⟩
  intro La hLa
  by_cases hshort : ∃ x : W, x ∈ La ∧ x ≠ 0 ∧ M.len (invApply (1 : archUnitary h v) (vecAt v x)) < 1
  · obtain ⟨x, hxL, hx0, hxlt⟩ := hshort
    have hxx : h.toSesq x x = 0 := h₃ M D La 1 x hLa hxL hxlt
    obtain ⟨p, hp, g, hg, -⟩ := hP La (Submodule.span E {x}) hLa
      (isIsotropicLine_span_singleton h hx0 hxx)
    exact ⟨p.1, Or.inr ⟨p, hp, rfl⟩, g, hg⟩
  · push Not at hshort
    obtain ⟨γ, hγ, -⟩ := hK La 1 hLa hshort
    exact ⟨γ • La, Or.inl hγ, γ⁻¹, inv_smul_smul γ La⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PShortestVectorIndex
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [IsTotallyReal F] in
theorem ShortestVectorIndex.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by
  intro M r ha D La g x hD hx hx0 hmin
  set c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc
  have hcpos : ∀ w, 0 < c w := h₄ M g x hx0
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]

  have hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a
    rw [h₃ M g x a]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by
    have := hlen 1
    simpa using this
  have hsub : intSubgroup E ≤ lineCoeffs La x := by
    rintro _ ⟨a, rfl⟩
    exact hD.isLattice.smul_mem a x hx
  have hfg : (lineCoeffs La x).FG := h₂ La x hD.isLattice.fg hx0
  have hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 →
      ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a haA ha0
    have hax : a • x ∈ La := haA
    have hax0 : a • x ≠ 0 := smul_ne_zero ha0 hx0
    have hle := hmin (a • x) hax hax0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  obtain ⟨a, hali, habs⟩ := ha
  have ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩
  have key := h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'
  rw [h₁ La x hx0]
  rw [hdeg] at key
  push_cast at key
  exact key

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldOrbit
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

variable (G : Type*) [Group G]

theorem UnfoldOrbit.bijective_mul_out_inv {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ) :
    Function.Bijective (fun p : (Γ ⧸ Γ₀.subgroupOf Γ) × Γ₀ =>
      (⟨(p.2 : G) * ((Quotient.out p.1 : Γ) : G)⁻¹,
        Γ.mul_mem (hle p.2.2) (Γ.inv_mem (Quotient.out p.1).2)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have hmem : (Quotient.out q' : Γ)⁻¹ * Quotient.out q ∈ Γ₀.subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf]
      have key : (((Quotient.out q' : Γ)⁻¹ * Quotient.out q : Γ) : G) = (h' : G)⁻¹ * h := by
        rw [show (h' : G)⁻¹ * h = (h' : G)⁻¹ * ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) *
          ((Quotient.out q : Γ) : G) by group, heq]
        push_cast
        group
      rw [key]
      exact Γ₀.mul_mem (Γ₀.inv_mem h'.2) h.2
    have hq : q' = q := by
      rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hmem
    subst hq
    have hh : h = h' := Subtype.ext (mul_right_cancel heq)
    rw [hh]
  · intro γ
    have hmem := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk γ⁻¹ :
      Γ ⧸ Γ₀.subgroupOf Γ)).symm
    rw [Subgroup.mem_subgroupOf] at hmem
    refine ⟨⟨QuotientGroup.mk γ⁻¹, ⟨_, hmem⟩⟩, ?_⟩
    apply Subtype.ext
    simp

theorem UnfoldOrbit.proof [MeasurableSpace G] [MeasurableMul G] : UnfoldOrbit.Statement G := by
  intro μ _ Γ Γ₀ _ hle FD FD₀ hFD hFD₀ φ hφ hinv
  have : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  have : Countable (Γ ⧸ Γ₀.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  rw [lintegral_tsum (f := fun (q : Γ ⧸ Γ₀.subgroupOf Γ) g => φ (((Quotient.out q : Γ) : G)⁻¹ * g))
      fun q => (hφ.comp (measurable_const_mul _)).aemeasurable,
    hFD.setLIntegral_eq_tsum φ FD₀,
    ← (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle)).tsum_eq,
    ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  have h1 : ∫⁻ g in FD, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ x in ((Quotient.out q : Γ) : G)⁻¹ • FD, φ x ∂μ := by
    rw [← Set.image_smul]
    exact (measurePreserving_mul_left μ _).setLIntegral_comp_emb (measurableEmbedding_mulLeft _) φ FD
  rw [h1, hFD₀.setLIntegral_eq_tsum' φ]
  refine tsum_congr fun h => ?_
  have hset : h • ((Quotient.out q : Γ) : G)⁻¹ • FD ∩ FD₀ =
      FD₀ ∩ (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle) (q, h)) • FD := by
    rw [Set.inter_comm]
    congr 1
    show (h : G) • ((Quotient.out q : Γ) : G)⁻¹ • FD = ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) • FD
    rw [smul_smul]
  rw [hset]
  exact lintegral_congr fun x => hinv _ (h⁻¹).2 x

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PParabolicDecomposition
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ParabolicDecomposition.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : KTransitive.Statement ι) (h₂ : HermAtPlace.Statement h v)
    (h₃ : GramAtData.Statement h v) (h₄ : ArchInvariant.Statement h v)
    (h₅ : VecAtNeZero.Statement v) : ParabolicDecomposition.Statement h v := by
  intro M x₀ hx₀ hiso g
  have hz : ∀ w, vecAt v x₀ w ≠ 0 := h₅ x₀ hx₀
  have hzi : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← h₂, hiso, map_zero]
  have hzi' : ∀ w, star (invApply g (vecAt v x₀) w) ⬝ᵥ
      (gramAt h v w *ᵥ invApply g (vecAt v x₀) w) = 0 := fun w => by
    rw [h₄, hzi]

  have hginv : ∀ w, (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := fun w => rfl
  have hz' : ∀ w, invApply g (vecAt v x₀) w ≠ 0 := by
    intro w hw
    apply hz w
    have e : ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ invApply g (vecAt v x₀) w =
        vecAt v x₀ w := by
      rw [invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← e, hw, Matrix.mulVec_zero]
  have hmaj : ∀ w, IsMajorantOf (gramAt h v w) (M.P w) := fun w =>
    ⟨M.posDef w, (h₃ w).1, (h₃ w).2, M.siegel w⟩
  choose k hkH hkP c hc using fun w =>
    h₁ _ _ (hmaj w) _ _ (hz w) (hz' w) (hzi w) (hzi' w)
  have hkA : k ∈ archUnitary h v := (Subgroup.mem_pi _).2 fun w _ => hkH w
  set kk : archUnitary h v := ⟨k, hkA⟩ with hkk
  have hkS : kk ∈ M.stab := by
    rw [Majorant.stab, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_pi _).2 fun w _ => hkP w
  refine ⟨g * kk⁻¹, kk, hkS, by group, fun w => ⟨(c w)⁻¹, ?_⟩⟩
  have hcw : c w ≠ 0 := by
    intro h0
    apply hz' w
    have e := congrArg (fun y => (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at e
    exact e

  have hk : (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      (c w)⁻¹ • invApply g (vecAt v x₀) w := by
    have e := congrArg (fun y => (c w)⁻¹ • ((((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y)) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hcw, one_smul] at e
    exact e.symm
  have hp : (((g * kk⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) * (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := rfl
  rw [hp, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, invApply, hginv, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PPhaseOnMinus
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

theorem PhaseOnMinus.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PhaseOnMinus.Statement ι := by
  intro H P hM c hc
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hHi : H⁻¹ * H = 1 := nonsing_inv_mul H hdet

  have hA2 : A * A = 1 := by
    simp only [hAdef, majInvolution]
    calc H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPHP, hHi]

  have hPA : P * A = H := by
    simp only [hAdef, majInvolution]; rw [← Matrix.mul_assoc, hPHP]

  have hAh : Aᴴ = P * H⁻¹ := by
    simp only [hAdef, majInvolution, conjTranspose_mul, conjTranspose_nonsing_inv,
      hH.eq, hP.isHermitian.eq]

  let Dm : ℂ → Matrix ι ι ℂ := fun a => ((1 + a) / 2) • (1 : Matrix ι ι ℂ) + ((1 - a) / 2) • A
  have hD : phaseOnMinus H P c = Dm c := by
    simp only [Dm, phaseOnMinus, ← hAdef]
    module
  have hDD : ∀ a b : ℂ, a * b = 1 → Dm a * Dm b = 1 := by
    intro a b hab
    simp only [Dm, add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hA2]
    have e1 : (1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2) = 1 := by
      linear_combination (1 / 2 : ℂ) * hab
    have e2 : (1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2) = 0 := by
      linear_combination (-1 / 2 : ℂ) * hab
    calc _ = ((1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2)) • (1 : Matrix ι ι ℂ)
          + ((1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2)) • A := by module
      _ = 1 := by rw [e1, e2]; simp
  have hDA : ∀ a : ℂ, Dm a * A = A * Dm a := by
    intro a
    simp only [Dm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one]

  have hDP : (Dm c)ᴴ * P = P * Dm (star c) := by
    simp only [Dm, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hAh, add_mul,
      mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hPA]
    simp only [hPHP, star_div₀, star_add, star_sub, star_one]
    norm_num
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, hDP, Matrix.mul_assoc, hDD _ _ hcc, Matrix.mul_one]
  · rw [hD, ← hPA, ← Matrix.mul_assoc, hDP, Matrix.mul_assoc, ← hDA c, ← Matrix.mul_assoc,
      Matrix.mul_assoc P, hDD _ _ hcc, Matrix.mul_one]
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantExists
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_posDef_mul_inv_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ P : Matrix n n ℂ, P.PosDef ∧ P * H⁻¹ * P = H := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set d : n → ℝ := hH.eigenvalues with hddef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have h0 := hdet.ne_zero
    rw [hH.det_eq_prod_eigenvalues] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hddef, hi]))
  have hinv : H⁻¹ = U * diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    have : (fun i => ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hd i), Complex.ofReal_one]
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨U * diagonal (fun i => ((|d i| : ℝ) : ℂ)) * star U, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosDef :=
      Matrix.posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (abs_pos.mpr (hd i))
    have hinj : Function.Injective U.vecMul := by
      intro x y hxy
      have := congrArg (fun z => z ᵥ* star U) hxy
      simpa only [vecMul_vecMul, hUU', vecMul_one] using this
    simpa only [star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same hinj
  · rw [hinv]
    conv_rhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc |d i| * (d i)⁻¹ * |d i| = |d i| * |d i| * (d i)⁻¹ := by ring
      _ = d i * d i * (d i)⁻¹ := by rw [abs_mul_abs_self]
      _ = d i := mul_inv_cancel_right₀ (hd i) _

section Spaces

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem MajorantExists.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : GramAtData.Statement h v) : MajorantExists.Statement h v := by
  choose P hP hPH using fun w => exists_posDef_mul_inv_mul_eq (h₁ w).1 (h₁ w).2
  exact ⟨⟨P, hP, hPH⟩⟩

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflectionMaps
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_dotProduct_mulVec_of_isHermitian {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (x y : ι → ℂ) : star (star y ⬝ᵥ (P *ᵥ x)) = star x ⬝ᵥ (P *ᵥ y) := by
  have h1 : star y ⬝ᵥ (P *ᵥ x) = star (P *ᵥ y) ⬝ᵥ x := by
    rw [dotProduct_mulVec, star_mulVec, hP.eq]
  rw [h1, star_dotProduct, star_star]

theorem exists_unit_mul_star_eq_norm (s : ℂ) : ∃ α : ℂ, ‖α‖ = 1 ∧ α * star s = ‖s‖ ∧ star α * s = ‖s‖ := by
  by_cases hs : s = 0
  · exact ⟨1, by simp, by simp [hs], by simp [hs]⟩
  · have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hs
    refine ⟨s / ‖s‖, ?_, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr hs)]
    · rw [div_mul_eq_mul_div, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring
    · rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring


variable (ι) in
theorem EigenReflectionMaps.proof (h₁ : EigenReflection.Statement ι)
    (h₂ : EigenspacesOrthogonal.Statement ι) : EigenReflectionMaps.Statement ι := by
  intro H P hMaj ε hε a a' ha ha' hρ
  have hPh : P.IsHermitian := hMaj.1.isHermitian
  obtain ⟨α, hα1, hαs, hαs'⟩ := exists_unit_mul_star_eq_norm (star a ⬝ᵥ (P *ᵥ a'))
  refine ⟨α, hα1, ?_⟩
  set v : ι → ℂ := a' - α • a with hv
  by_cases hv0 : v = 0
  · refine ⟨1, by simp, by simp, ?_, fun u _ => by simp⟩
    rw [one_mulVec]
    exact sub_eq_zero.mp hv0
  have hAv : majInvolution H P *ᵥ v = ε • v := by
    rw [hv, mulVec_sub, mulVec_smul, ha, ha', smul_sub, smul_comm]
  obtain ⟨hRP, hRH, hRv, hRfix⟩ := h₁ H P hMaj ε hε v hv0 hAv
  refine ⟨pReflection P v, hRP, hRH, ?_, ?_⟩
  ·
    have hconj : star a' ⬝ᵥ (P *ᵥ a) = star (star a ⬝ᵥ (P *ᵥ a')) :=
      (star_dotProduct_mulVec_of_isHermitian hPh a' a).symm
    have hαα : star α * α = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα1]; simp
    have hw : star v ⬝ᵥ (P *ᵥ (a' + α • a)) = 0 := by
      rw [hv, star_sub, star_smul, mulVec_add, mulVec_smul, sub_dotProduct, dotProduct_add,
        dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        hconj, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← hρ]
      have e1 : star α * (α * (star a ⬝ᵥ (P *ᵥ a))) = (star α * α) * (star a ⬝ᵥ (P *ᵥ a)) := by
        ring
      rw [e1, hαα, hαs, hαs']
      ring
    have hRw := hRfix _ hw
    have hsplit : a' = (1 / 2 : ℂ) • (a' + α • a) + (1 / 2 : ℂ) • v := by
      rw [hv]; ext i; simp; ring
    rw [hsplit, mulVec_add, mulVec_smul, mulVec_smul, hRw, hRv, hv]
    ext i; simp; ring
  · intro u hu
    apply hRfix
    rcases hε with rfl | rfl
    · have h := h₂ H P hMaj v u (by rw [hAv, one_smul]) (by rw [hu, neg_smul, one_smul])
      exact h
    · have h := h₂ H P hMaj u v (by rw [hu, neg_neg, one_smul]) (by rw [hAv, neg_smul, one_smul])
      rw [← star_dotProduct_mulVec_of_isHermitian hPh, h, star_zero]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedIndexBound
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem WeightedIndexBound.proof (E : Type*) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₅ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      MinkowskiVolumeForm.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E)) :
    WeightedIndexBound.Statement E := by
  intro c hc A hOA hFG hmin r ⟨a, ha, hr⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨h₄⟩
  obtain ⟨e⟩ := h₁ A hOA hFG
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hOA ⟨a i, rfl⟩
  set T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ := fun i j => e.repr ⟨(a i : E), hmem i⟩ j with hT
  have hcoe : ∀ z : Fin (finrank ℚ E) → ℤ, ((∑ j, z j • e j : A) : E) = ∑ j, z j • (e j : E) := by
    intro z
    change A.subtype _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
    rfl
  have haT : ∀ i, (a i : E) = ∑ j, T i j • (e j : E) := by
    intro i
    rw [← hcoe]
    exact (congrArg Subtype.val (e.sum_repr ⟨(a i : E), hmem i⟩)).symm
  have hidx := h₂ A hOA e a T ha haT

  set Φ := weightedEmbed c with hΦ
  have hc0 : ∀ w, 0 ≤ c w := fun w => (hc w).le
  have hS : 0 < ∑ w, c w := Finset.sum_pos (fun w _ => hc w) Finset.univ_nonempty
  set lam := Real.sqrt (∑ w, c w) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hS
  have hlam2 : lam ^ 2 = ∑ w, c w := Real.sq_sqrt hS.le
  have hdpos : 0 < finrank ℚ E := Module.finrank_pos
  have hsd : 0 < Real.sqrt (finrank ℚ E) := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  set o : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E)) :=
    (Module.finBasisOfFinrankEq ℝ _ h₄).orientation
  set b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2) := fun i => Φ (e i : E)

  have hmink : (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E ≤ |o.volumeForm b| := by
    refine h₅ o b lam hlam0 fun z hz => ?_
    have hsum : ∑ i, (z i : ℝ) • b i = Φ ((∑ i, z i • e i : A) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcoe, map_sum]
      simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
    rw [hsum]
    set x : A := ∑ i, z i • e i
    have hx : (x : E) ≠ 0 := by
      intro h0
      have hx0 : x = 0 := Subtype.ext h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
      exact hi (Fintype.linearIndependent_iff.1 e.linearIndependent z hx0 i)
    have hq := hmin x x.2 hx
    rw [hlam, ← Real.sqrt_sq (norm_nonneg (Φ x)), h₃ c hc0]
    exact Real.sqrt_le_sqrt hq

  have hab : (fun i => Φ (a i : E)) = fun i => ∑ j, (T i j : ℝ) • b j := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [haT i, map_sum]
    simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
  have hvol : o.volumeForm (fun i => Φ (a i : E)) = (T.det : ℝ) * o.volumeForm b := by
    rw [hab]; exact h₆ o b T

  have hr0 : 0 ≤ r := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact (norm_nonneg _).trans (hr ⟨0, hdpos⟩ w.embedding)
  have hnorm : ∀ i, ‖Φ (a i : E)‖ ≤ r * lam := by
    intro i
    have h2 : ‖Φ (a i : E)‖ ^ 2 ≤ (r * lam) ^ 2 := by
      rw [h₃ c hc0, mul_pow, hlam2, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hr i w.embedding) 2
      nlinarith [hc0 w]
    nlinarith [norm_nonneg (Φ (a i : E)), mul_nonneg hr0 hlam0.le]
  have hhad : |o.volumeForm (fun i => Φ (a i : E))| ≤ (r * lam) ^ finrank ℚ E := by
    refine (o.abs_volumeForm_apply_le _).trans ?_
    calc ∏ i, ‖Φ (a i : E)‖ ≤ ∏ _i : Fin (finrank ℚ E), r * lam :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hnorm i)
      _ = (r * lam) ^ finrank ℚ E := by simp

  have hpos : 0 < (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := pow_pos (div_pos hlam0 hsd) _
  have hkey : |(T.det : ℝ)| * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E ≤
      (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := by
    calc |(T.det : ℝ)| * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E
        ≤ |(T.det : ℝ)| * |o.volumeForm b| :=
          mul_le_mul_of_nonneg_left hmink (abs_nonneg _)
      _ = |o.volumeForm (fun i => Φ (a i : E))| := by rw [hvol, abs_mul]
      _ ≤ (r * lam) ^ finrank ℚ E := hhad
      _ = (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := by
          rw [← mul_pow]; congr 1; field_simp
  exact hidx.trans (le_of_mul_le_mul_right hkey hpos)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PKTransitive
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Matrix
open scoped ComplexOrder

noncomputable section

theorem KTransitive.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : IsotropicSplit.Statement ι) (h₂ : EigenReflectionMaps.Statement ι)
    (h₃ : PhaseOnMinus.Statement ι) (_h₄ : EigenspacesOrthogonal.Statement ι) :
    KTransitive.Statement ι := by
  intro H P hmaj z z' hz hz' hzH hz'H
  obtain ⟨ha, hb, hab⟩ := h₁ H P hmaj z hzH
  obtain ⟨ha', hb', hab'⟩ := h₁ H P hmaj z' hz'H
  have hsplit : ∀ w : ι → ℂ, plusPart H P w + minusPart H P w = w := by
    intro w; ext i; simp only [plusPart, minusPart, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hPpos := hmaj.1
  have hne : ∀ w : ι → ℂ, w ≠ 0 →
      star (plusPart H P w) ⬝ᵥ (P *ᵥ plusPart H P w) =
        star (minusPart H P w) ⬝ᵥ (P *ᵥ minusPart H P w) → plusPart H P w ≠ 0 := by
    intro w hw heq h0
    apply hw
    rw [h0] at heq
    simp only [star_zero, zero_dotProduct] at heq
    have hm : minusPart H P w = 0 := by
      by_contra hm
      exact (hPpos.dotProduct_mulVec_pos hm).ne heq
    rw [← hsplit w, h0, hm, add_zero]
  set a := plusPart H P z with ha_def
  set b := minusPart H P z with hb_def
  set a' := plusPart H P z' with ha'_def
  set b' := minusPart H P z' with hb'_def
  have ha0 : a ≠ 0 := hne z hz hab
  have ha'0 : a' ≠ 0 := hne z' hz' hab'
  have hp := hPpos.dotProduct_mulVec_pos ha0
  have hq := hPpos.dotProduct_mulVec_pos ha'0
  set p := star a ⬝ᵥ (P *ᵥ a) with hp_def
  set q := star a' ⬝ᵥ (P *ᵥ a') with hq_def
  obtain ⟨hpr, hpi⟩ := Complex.lt_def.mp hp
  obtain ⟨hqr, hqi⟩ := Complex.lt_def.mp hq
  simp only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi
  set t : ℝ := Real.sqrt (p.re / q.re) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hpr hqr)
  have htt : t * t = p.re / q.re := Real.mul_self_sqrt (div_nonneg hpr.le hqr.le)
  have ht2 : (t : ℂ) * t * q = p := by
    have key : t * t * q.re = p.re := by rw [htt, div_mul_cancel₀ _ hqr.ne']
    apply Complex.ext
    · simp [Complex.mul_re, ← hqi, key]
    · simp [Complex.mul_im, ← hqi, ← hpi]
  have hscale : ∀ v : ι → ℂ, star ((t : ℂ) • v) ⬝ᵥ (P *ᵥ ((t : ℂ) • v)) =
      (t : ℂ) * t * (star v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    ring
  have hA1 : majInvolution H P *ᵥ ((t : ℂ) • a') = (1 : ℂ) • ((t : ℂ) • a') := by
    rw [mulVec_smul, ha', one_smul]
  have hAm : majInvolution H P *ᵥ ((t : ℂ) • b') = (-1 : ℂ) • ((t : ℂ) • b') := by
    rw [mulVec_smul, hb', neg_one_smul, smul_neg]
  obtain ⟨α, hα, Rp, hRpP, hRpH, hRpa, hRpfix⟩ := h₂ H P hmaj 1 (Or.inl rfl) a ((t : ℂ) • a')
    (by rw [ha, one_smul]) hA1 (by rw [hscale, ht2])
  obtain ⟨β, hβ, Rm, hRmP, hRmH, hRmb, hRmfix⟩ := h₂ H P hmaj (-1) (Or.inr rfl) b ((t : ℂ) • b')
    (by rw [hb, neg_one_smul]) hAm (by rw [hscale, ← hab', ht2, hab])
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; exact zero_ne_one hβ
  have hc : ‖α / β‖ = 1 := by rw [norm_div, hα, hβ, div_one]
  obtain ⟨hDP, hDH, hDplus, hDminus⟩ := h₃ H P hmaj (α / β) hc
  set D := phaseOnMinus H P (α / β) with hD_def
  set M := D * Rm * Rp with hM_def
  have hunit : ∀ X : Matrix ι ι ℂ, Dᴴ * X * D = X → Rmᴴ * X * Rm = X → Rpᴴ * X * Rp = X →
      Mᴴ * X * M = X := by
    intro X h1 h2 h3
    have e : Mᴴ * X * M = Rpᴴ * (Rmᴴ * (Dᴴ * X * D) * Rm) * Rp := by
      simp only [hM_def, conjTranspose_mul, Matrix.mul_assoc]
    rw [e, h1, h2, h3]
  have hMH : Mᴴ * H * M = H := hunit H hDH hRmH hRpH
  have hMP : Mᴴ * P * M = P := hunit P hDP hRmP hRpP
  have hct : ∀ X : Matrix ι ι ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i j; simp [conjTranspose_apply]
  have hRma : Rm *ᵥ a = a := hRmfix a (by rw [ha, neg_neg, one_smul])
  have hMz : M *ᵥ ((t : ℂ) • z') = α • z := by
    have hz'2 : (t : ℂ) • z' = (t : ℂ) • a' + (t : ℂ) • b' := by rw [← smul_add, hsplit z']
    rw [hz'2, hM_def, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hRpa, hRpfix _ hAm,
      mulVec_add, mulVec_smul, hRma, hRmb, mulVec_add, mulVec_smul, mulVec_smul, hDplus a ha,
      hDminus b hb, smul_smul, mul_div_cancel₀ _ hβ0, ← smul_add, hsplit z]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hdet : IsUnit M.det := isUnit_det_of_unitary (starRingEnd ℂ) hmaj.2.2.1 (by rw [hct]; exact hMH)
  refine ⟨nonsingInvUnit M hdet, ?_, ?_, (t : ℂ)⁻¹ * α, ?_⟩
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * H * M = H
    rw [hct]; exact hMH
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * P * M = P
    rw [hct]; exact hMP
  · show M *ᵥ z' = ((t : ℂ)⁻¹ * α) • z
    rw [mulVec_smul] at hMz
    rw [mul_smul, ← hMz, smul_smul, inv_mul_cancel₀ htc, one_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
