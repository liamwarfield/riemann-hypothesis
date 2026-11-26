module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def hz {m n : ℕ} {G : Type} (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (Q : PX m n) (x : G) : ℂ :=
  ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec Q x

def FarRight : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∃ σ : ℝ, (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
        (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
        ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) (κ : KR n → ℂ) (N : ℕ) (yy : Fin N → GR n)
          (QQ : Fin N → PX m n) (M : ℂ → Matrix (Fin N) (Fin N) ℂ), IsFiniteMeasure ν → Continuous κ →
          (∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
              F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y') →
          ∀ (z : ℂ), σ < z.re → ∀ (g : G) (i : Fin N),
            ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
              ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem nU_mul_nU (b b' : Matrix (Fin n) (Fin n) ℂ) : nU b * nU b' = nU (b + b') := by
  simp only [nU, fromBlocks_multiply]
  congr 1 <;> simp [add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [nU, fromBlocks_one]

def wU (b : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n ⊕ Fin n) ℂ where
  val := JJ n * nU b
  inv := nU (-b) * -JJ n
  val_inv := by
    calc JJ n * nU b * (nU (-b) * -JJ n) = JJ n * (nU b * nU (-b)) * -JJ n := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nU_mul_nU, add_neg_cancel, nU_zero, Matrix.mul_one, Matrix.mul_neg, JJ_mul_self, neg_neg]
  inv_val := by
    calc nU (-b) * -JJ n * (JJ n * nU b) = -(nU (-b) * (JJ n * JJ n) * nU b) := by
          simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      _ = 1 := by
          rw [JJ_mul_self, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, neg_neg, nU_mul_nU, neg_add_cancel, nU_zero]

theorem wU_mem (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : wU b ∈ GR n := by
  change InG (JJ n * nU b)
  have hb' : bᴴ = b := hb
  simp only [InG, JJ, nU, Matrix.conjTranspose_mul, fromBlocks_conjTranspose, fromBlocks_multiply, hb']
  congr 1 <;> simp [hb']

theorem cell_dec (y : GR n) (hc : (mR y).toBlocks₂₁.det ≠ 0) :
    ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧ mR g = JJ n * nU b ∧ y = y₁ * g := by
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hinv : mR y * mR y⁻¹ = 1 := congrArg mR (mul_inv_cancel y)
  have hJ : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have e1 : mR y * JJ n * (mR y)ᴴ * JJ n * mR y = - mR y := by
      calc _ = mR y * JJ n * ((mR y)ᴴ * JJ n * mR y) := by simp only [Matrix.mul_assoc]
        _ = - mR y := by rw [hy, Matrix.mul_assoc, JJ_mul_self, Matrix.mul_neg, Matrix.mul_one]
    have e2 : mR y * JJ n * (mR y)ᴴ * JJ n = -1 := by
      calc _ = mR y * JJ n * (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hinv, Matrix.mul_one]
        _ = -1 := by rw [← Matrix.mul_assoc, e1, Matrix.neg_mul, hinv]
    calc _ = mR y * JJ n * (mR y)ᴴ * (JJ n * -JJ n) := by
          rw [Matrix.mul_neg, JJ_mul_self, neg_neg, Matrix.mul_one]
      _ = JJ n := by rw [← Matrix.mul_assoc, e2, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  have hrel : (mR y).toBlocks₂₁ * ((mR y).toBlocks₂₂)ᴴ = (mR y).toBlocks₂₂ * ((mR y).toBlocks₂₁)ᴴ := by
    have h22 := congrArg toBlocks₂₂ hJ
    rw [← fromBlocks_toBlocks (mR y)] at h22
    simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h22
    simp at h22
    rw [neg_add_eq_zero] at h22
    exact h22.symm
  have hblk : toBlocks₂₁ (mR y * fromBlocks (-((mR y).toBlocks₂₁⁻¹ * (mR y).toBlocks₂₂)) (-1) 1 0) =
      -((mR y).toBlocks₂₁ * ((mR y).toBlocks₂₁⁻¹ * (mR y).toBlocks₂₂)) + (mR y).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
  set C := (mR y).toBlocks₂₁ with hCdef
  set D := (mR y).toBlocks₂₂ with hDdef
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hc
  have hCH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hC.star
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hC, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = C⁻¹ * D := by rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCH, Matrix.mul_one]
  let g : GR n := ⟨wU (C⁻¹ * D), wU_mem _ hb⟩
  refine ⟨y * g⁻¹, g, C⁻¹ * D, ?_, hb, rfl, (inv_mul_cancel_right y g).symm⟩
  have hk : nU (-(C⁻¹ * D)) * -JJ n = fromBlocks (-(C⁻¹ * D)) (-1) 1 0 := by
    simp only [nU, JJ, fromBlocks_neg, fromBlocks_multiply]
    congr 1 <;> simp
  have hm : mR (y * g⁻¹) = mR y * (nU (-(C⁻¹ * D)) * -JJ n) := rfl
  show toBlocks₂₁ (mR (y * g⁻¹)) = 0
  rw [hm, hk, hblk, ← Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.one_mul, neg_add_cancel]

theorem conj_cell {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (g : GR n)
    (b : Matrix (Fin n) (Fin n) ℂ) (hg : mR g = JJ n * nU b) (h : ℝ) :
    mR (a h * g * a h) = JJ n * nU (bS X h b) := by
  have h1 := ha h
  unfold IsDil at h1
  have hm : mR (a h * g * a h) = mR (a h) * mR g * mR (a h) := rfl
  rw [hm, h1, hg]
  simp only [JJ, nU, bS, fromBlocks_multiply]
  congr 1 <;> simp [diagonal_mul_diagonal, ← Complex.ofReal_mul, ← Real.exp_add, Matrix.mul_assoc, ← Complex.exp_add]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem cell_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y : GR n)
    (hc : (mR y).toBlocks₂₁.det ≠ 0) (s : ℝ) : (mR (y * a s)).toBlocks₂₁.det ≠ 0 := by
  have h1 := ha s
  unfold IsDil at h1
  have hm : mR (y * a s) = mR y * mR (a s) := rfl
  rw [hm, h1, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero, det_mul, det_diagonal]
  refine mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

theorem weight_factor_dilation {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (p q : ℕ) (e : ℤ) (h : ℝ) :
    F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ)) := by
  have hm := ha (-h)
  unfold IsDil at hm
  simp only [F0, f0, u1, u2, hm, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, neg_zero, zero_add,
    det_fromBlocks_zero₂₁, det_diagonal, Complex.ofReal_exp]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousOnTwistedSectionCompact
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem cont_KR_mul (n : ℕ) (y k1 : GR n) : Continuous (fun k : KR n => y * (k : GR n) * k1) :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem cont_KR_mul' (n : ℕ) (k1 : GR n) : Continuous (fun k : KR n => (k : GR n) * k1) :=
  continuous_subtype_val.mul continuous_const

theorem spherical_section_eq_extension {n : ℕ} (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g = twistedScalarSection p q e (mR g) := by
  simp only [F0, twistedScalarSection]

theorem inK_mul {n : ℕ} (k : KR n) (k1 : GR n) (hk1 : k1 ∈ KR n) : InK (mR ((k : GR n) * k1)) :=
  (KR n).mul_mem k.2 hk1

theorem continuousOn_twisted_section_compact {n : ℕ} (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (y k1 : GR n) (U : Set ℂ) (κ : KR n → ℂ)
    (hκ : Continuous κ) (C : Set (GR n)) (hC : ∀ k : KR n, y * (k : GR n) * k1 ∈ C)
    (hU2c : ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul n y k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) =
      (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) ∘ (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) hU2c hφ.continuousOn
    (fun yz hyz => ⟨hC yz.1, hyz.2⟩)

theorem contOn_Fid {n : ℕ} (k1 : GR n) (U U1 : Set ℂ) (hUU : U ⊆ U1) (κ : KR n → ℂ) (hκ : Continuous κ)
    (Fid : GR n → ℂ → ℂ) (hFidc : ContinuousOn (fun y : GR n × ℂ => Fid y.1 y.2) (univ ×ˢ U1)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul' n k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => Fid ((yz.1 : GR n) * k1) yz.2) =
      (fun y : GR n × ℂ => Fid y.1 y.2) ∘ (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun y : GR n × ℂ => Fid y.1 y.2) hFidc hφ.continuousOn
    (fun yz hyz => ⟨mem_univ _, hUU hyz.2⟩)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopSing
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G]

def hz (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x

def Top [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ι : GR n →* G) (p q : ℕ) (e : ℤ) (a b : GR n)
    (nb : (Fin n → Fin n → ℝ) → GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (F : G → ℂ) (g : G) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) ∂μ

variable [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_sing [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    (hnb : ∀ x, mR (nb x) = nU (herm x)) (F : G → ℂ) (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hl : ∀ l ∈ Λ, l F = 0) (g : G) : Top μ ι p q e a b nb ψ F g = 0 := by
  unfold Top
  have : ∀ k : KR n, (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) = 0 := fun k =>
    hG.Λsing F hF hinv hl ψ hψ nb hnb g ((k : GR n) * a) b
  simp only [this, mul_zero, integral_zero]

theorem hz_split (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (g : G) :
    ∃ (y : GR n) (K : ℂ) (r : ℝ), 0 < r ∧ ∀ (z : ℂ) (w : GR n), hz Ht sec s₀ z (g * ι w) =
      K * ((r : ℂ) ^ (z - s₀)) * (((hLoc (y * w) : ℝ) : ℂ) ^ (z - s₀) * F0 p q e (y * w)) := by
  obtain ⟨x0, y, S, r, hr, hg, hsp⟩ := hG.split g
  refine ⟨y, S, r, hr, fun z w => ?_⟩
  have h1 := hsp (y * w)
  have e1 : g * ι w = x0 * ι (y * w) := by rw [hg, map_mul, mul_assoc]
  rw [e1]
  simp only [hz]
  rw [h1.1, h1.2 1, hL.vac, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg _)]
  ring

theorem top_hz [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    {ψ : (Fin n → Fin n → ℝ) → ℂ} {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (z : ℂ) (g : G) : Top μ ι p q e a b nb ψ (hz Ht sec s₀ z) g = cz (z - s₀) * hz Ht sec s₀ z g := by
  obtain ⟨y, K, r, hr, hsp⟩ := hz_split hL hG g
  have e1 : ∀ (k : KR n) x, hz Ht sec s₀ z (g * ι ((k : GR n) * a * nb x * b)) * ψ x =
      (K * (r : ℂ) ^ (z - s₀)) * ((((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := by
    intro k x
    rw [hsp]
    simp only [mul_assoc]
  have e2 : hz Ht sec s₀ z g = K * (r : ℂ) ^ (z - s₀) * (((hLoc y : ℝ) : ℂ) ^ (z - s₀) * F0 p q e y) := by
    have := hsp z 1
    rwa [map_one, mul_one, mul_one] at this
  unfold Top
  simp_rw [e1, MeasureTheory.integral_const_mul]
  have e3 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * (K * (r : ℂ) ^ (z - s₀) * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) = (K * (r : ℂ) ^ (z - s₀)) * ((F0 p q e (k : GR n))⁻¹ * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := fun k => by ring
  simp_rw [e3, MeasureTheory.integral_const_mul, hceig, e2]
  ring

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecondUnitaryBlockOfPair
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem shape_mul (A B A' B' : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks A B (-B) A * fromBlocks A' B' (-B') A' =
      fromBlocks (A * A' - B * B') (A * B' + B * A') (-(A * B' + B * A')) (A * A' - B * B') := by
  rw [fromBlocks_multiply]
  congr 1 <;> noncomm_ring

theorem kM_mul (a b a' b' : Matrix (Fin n) (Fin n) ℂ) : kM a b * kM a' b' = kM (a * a') (b * b') := by
  simp only [kM]
  rw [shape_mul]
  congr 1 <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub, smul_neg, neg_add, neg_sub] <;>
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring

theorem kM_one : kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  simp only [kM, sub_self, smul_zero, neg_zero]
  rw [← fromBlocks_one]
  congr 1 <;> rw [← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), smul_smul] <;> norm_num

theorem kM_conjTranspose (a b : Matrix (Fin n) (Fin n) ℂ) : (kM a b)ᴴ = kM aᴴ bᴴ := by
  simp only [kM, fromBlocks_conjTranspose, conjTranspose_smul, conjTranspose_add, conjTranspose_sub,
    conjTranspose_neg]
  congr 1 <;> simp [Complex.conj_ofReal, map_div₀] <;> module

theorem JJ_comm_shape (A B : Matrix (Fin n) (Fin n) ℂ) :
    JJ n * fromBlocks A B (-B) A = fromBlocks A B (-B) A * JJ n := by
  simp only [JJ, fromBlocks_multiply]
  congr 1 <;> simp

theorem JJ_comm_kM (a b : Matrix (Fin n) (Fin n) ℂ) : JJ n * kM a b = kM a b * JJ n := by
  unfold kM
  exact JJ_comm_shape _ _

theorem first_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u1 (kM a b) = a := by
  simp only [u1, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem second_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u2 (kM a b) = b := by
  simp only [u2, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul, neg_neg]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem kM_low (a : Matrix (Fin n) (Fin n) ℂ) : (kM a a).toBlocks₂₁ = 0 := by
  unfold kM
  rw [toBlocks_fromBlocks₂₁]
  simp

theorem kM_of_unitary (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ unitaryGroup (Fin n) ℂ)
    (hb : b ∈ unitaryGroup (Fin n) ℂ) : ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b := by
  have ha1 : aᴴ * a = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp ha
  have ha2 : a * aᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp ha
  have hb1 : bᴴ * b = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hb
  have hb2 : b * bᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hb
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨kM a b, kM aᴴ bᴴ, by rw [kM_mul, ha2, hb2, kM_one], by rw [kM_mul, ha1, hb1, kM_one]⟩
  have hG : u ∈ GR n := by
    show InG (kM a b)
    unfold InG
    rw [kM_conjTranspose, Matrix.mul_assoc, JJ_comm_kM, ← Matrix.mul_assoc, kM_mul, ha1, hb1,
      kM_one, Matrix.one_mul]
  refine ⟨⟨u, hG⟩, ?_, rfl⟩
  show InK (kM a b)
  exact ⟨hG, by rw [kM_conjTranspose, kM_mul, ha1, hb1, kM_one]⟩

theorem KR_shape (k : GR n) (hk : k ∈ KR n) :
    u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
      mR k = kM (u1 (mR k)) (u2 (mR k)) := by
  have hk' : InK (mR k) := hk
  obtain ⟨hG, hU⟩ := hk'
  unfold InG at hG
  set g := mR k with hg
  have hU' : g * gᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hU', Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  have hc' := hc
  rw [← fromBlocks_toBlocks g] at hc'
  simp only [JJ, fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, neg_zero] at hc'
  rw [fromBlocks_inj] at hc'
  obtain ⟨h1, h2, -, -⟩ := hc'
  have hshape : g = kM (u1 g) (u2 g) := by
    conv_lhs => rw [← fromBlocks_toBlocks g]
    simp only [kM, u1, u2, h1, h2]
    congr 1 <;> match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring
  have hx : kM ((u1 g)ᴴ * u1 g) ((u2 g)ᴴ * u2 g) = kM 1 1 := by
    rw [← kM_mul, ← kM_conjTranspose, ← hshape, hU, kM_one]
  have e1 : (u1 g)ᴴ * u1 g = 1 := by
    have := congrArg u1 hx
    rwa [first_unitary_block_of_pair, first_unitary_block_of_pair] at this
  have e2 : (u2 g)ᴴ * u2 g = 1 := by
    have := congrArg u2 hx
    rwa [second_unitary_block_of_pair, second_unitary_block_of_pair] at this
  exact ⟨Matrix.mem_unitaryGroup_iff'.mpr e1, Matrix.mem_unitaryGroup_iff'.mpr e2, hshape⟩

theorem kIso : KIso := by
  intro n
  exact ⟨fun a b ha hb => kM_of_unitary a b ha hb, kM_mul, kM_one, fun a b => ⟨first_unitary_block_of_pair a b, second_unitary_block_of_pair a b⟩,
    kM_low, KR_shape⟩

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DenseCell
noncomputable section

open Matrix Set Filter Topology Polynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def nbU (l : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 ((l : ℂ) • 1) 1
  inv := fromBlocks 1 0 (-((l : ℂ) • 1)) 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

theorem nbU_mem (l : ℝ) : nbU (n := n) l ∈ GR n := by
  change InG (fromBlocks 1 0 ((l : ℂ) • 1) 1)
  simp only [InG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> simp [Matrix.smul_eq_diagonal_mul]

def nbG (l : ℝ) : GR n := ⟨nbU l, nbU_mem l⟩

theorem nbG_zero : nbG (n := n) 0 = 1 := by
  apply ext_mR
  show fromBlocks 1 0 (((0 : ℝ) : ℂ) • 1) 1 = 1
  simp [fromBlocks_one]

theorem cont_nbG : Continuous (nbG (n := n)) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun l : ℝ => (fromBlocks 1 0 ((l : ℂ) • 1) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop
  · show Continuous fun l : ℝ => (fromBlocks 1 0 (-((l : ℂ) • 1)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop

theorem nbG_low (l : ℝ) (y : GR n) :
    (mR (nbG l * y)).toBlocks₂₁ = (l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁ := by
  have hm : mR (nbG l * y) = fromBlocks 1 0 ((l : ℂ) • 1) 1 * mR y := rfl
  rw [hm]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem det_I (y : GR n) : (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : Fin n ⊕ Fin n → ℂ := Sum.elim x 0
  have hYv : mR y *ᵥ v = Sum.elim ((mR y).toBlocks₁₁ *ᵥ x) ((mR y).toBlocks₂₁ *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_mulVec]
    simp [v]
  have hCx : (mR y).toBlocks₂₁ *ᵥ x = -(Complex.I • ((mR y).toBlocks₁₁ *ᵥ x)) := by
    rw [add_mulVec, smul_mulVec] at hx
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hform : star (mR y *ᵥ v) ⬝ᵥ (JJ n *ᵥ (mR y *ᵥ v)) = 0 := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hy,
      ← dotProduct_mulVec]
    simp [v, JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hYv, hCx] at hform
  simp [JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] at hform
  set u := (mR y).toBlocks₁₁ *ᵥ x with hu
  simp only [neg_mulVec, Pi.neg_apply] at hform
  have h3 : (-2 * Complex.I) * ∑ i, starRingEnd ℂ (u i) * u i = 0 := by
    rw [← hform, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : ∑ i, starRingEnd ℂ (u i) * u i = 0 :=
    (mul_eq_zero.mp h3).resolve_left (by simp [Complex.I_ne_zero])
  have hu0 : u = 0 := by
    rw [← dotProduct_star_self_eq_zero]
    simpa [dotProduct] using h2
  have hYv0 : mR y *ᵥ v = 0 := by
    rw [hYv, hCx, hu0]
    ext i
    rcases i with i | i <;> simp
  have hinv : mR y⁻¹ * mR y = 1 := congrArg mR (inv_mul_cancel y)
  have hv : v = 0 := by
    rw [← one_mulVec v, ← hinv, ← mulVec_mulVec, hYv0, mulVec_zero]
  apply hx0
  funext i
  exact congrFun hv (Sum.inl i)

theorem finite_bad (y : GR n) :
    {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0}.Finite := by
  let M : Matrix (Fin n) (Fin n) ℂ[X] :=
    (X : ℂ[X]) • (mR y).toBlocks₁₁.map (Polynomial.C : ℂ →+* ℂ[X]) + (mR y).toBlocks₂₁.map (Polynomial.C : ℂ →+* ℂ[X])
  let p : ℂ[X] := M.det
  have hev : ∀ z : ℂ, p.eval z = (z • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det := by
    intro z
    have h := RingHom.map_det (Polynomial.evalRingHom z) M
    rw [Polynomial.coe_evalRingHom] at h
    rw [h]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : p ≠ 0 := by
    intro h0
    apply det_I y
    rw [← hev, h0, Polynomial.eval_zero]
  apply (p.roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset
  intro l hl
  simp only [Set.mem_setOf_eq] at hl
  rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact (hev _).trans hl

theorem dense_cell : Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hS := finite_bad y
  set S := {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0} with hSdef
  have hT : (S \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hS.diff (s := S) (t := {0})).isClosed.isOpen_compl.mem_nhds (by simp)
  have hcont : Continuous fun t : ℝ => nbG (n := n) t * y := cont_nbG.mul continuous_const
  have htend : Tendsto (fun t : ℝ => nbG (n := n) t * y) (𝓝[≠] 0) (𝓝 y) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa [nbG_zero] using h
  apply mem_closure_of_tendsto htend
  filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with t h1 h2
  simp only [Set.mem_setOf_eq, nbG_low]
  intro hdet
  exact h1 ⟨hdet, h2⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtPhi
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem norm_scal_sq (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖scal (aH X s) y a j‖ ^ 2 = Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 := by
  simp only [scal, aH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]

theorem hasDerivAt_gs (c : ℝ) (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) :
    HasDerivAt (fun s => gs c (scal (aH X s) y))
      (gs c (scal (aH X h) y) * (-(((c * ∑ a, ∑ j, 2 * X j * ‖scal (aH X h) y a j‖ ^ 2) : ℝ) : ℂ))) h := by
  have key : ∀ s : ℝ, gs c (scal (aH X s) y) =
      Complex.exp (-(((c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 : ℝ)) : ℂ)) := by
    intro s
    simp only [gs, norm_scal_sq]
  have hF : HasDerivAt (fun s : ℝ => c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2)
      (c * ∑ a, ∑ j, 2 * X j * (Real.exp (h * X j) ^ 2 * ‖y a j‖ ^ 2)) h := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro j _
    have e : HasDerivAt (fun s : ℝ => Real.exp (s * X j)) (Real.exp (h * X j) * X j) h := by
      simpa using ((hasDerivAt_id h).mul_const (X j)).exp
    exact ((e.pow 2).mul_const (‖y a j‖ ^ 2)).congr_deriv (by
      rw [show (2 : ℕ) - 1 = 1 from rfl]
      push_cast
      ring)
  have hc := (hF.ofReal_comp.neg).cexp
  rw [show (fun s : ℝ => gs c (scal (aH X s) y)) = fun s : ℝ =>
      Complex.exp (-(((c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 : ℝ)) : ℂ)) from funext key]
  refine hc.congr_deriv ?_
  rw [key h]
  simp only [norm_scal_sq, Pi.neg_apply]

theorem hasDerivAt_phi (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (y : Fin m → Fin n → ℂ) (h : ℝ) :
    HasDerivAt (fun s => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y))
      ((evX (dil c X Q) (scal (aH X h) y) - ((m : ℂ) * ∑ j, (X j : ℂ)) * evX Q (scal (aH X h) y)) *
        gs c (scal (aH X h) y)) h := by
  have h1 : HasDerivAt (fun s : ℝ => evX Q (scal (aH X s) y))
      (∑ k, eval (ept (scal (aH X h) y)) (pderiv k Q) * ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k)) h := by
    simp only [evX_eq]
    exact hasDerivAt_eval_curve Q (fun s => ept (scal (aH X s) y)) _ h
      (fun k => hasDerivAt_scal_coord X y h k)
  exact (h1.mul (hasDerivAt_gs c X y h)).congr_deriv (by
    rw [evX_dil]
    push_cast
    ring)

private theorem dom_bound_lemma (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (j : Fin n) :
    Real.exp (-(∑ i, |X i|)) ≤ Real.exp (h * X j) ∧ Real.exp (h * X j) ≤ Real.exp (∑ i, |X i|) := by
  have hj : |X j| ≤ ∑ i, |X i| :=
    Finset.single_le_sum (f := fun i => |X i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hx : |h * X j| ≤ ∑ i, |X i| := by
    rw [abs_mul]
    calc |h| * |X j| ≤ 1 * |X j| := mul_le_mul_of_nonneg_right hh.le (abs_nonneg _)
      _ ≤ ∑ i, |X i| := by simpa using hj
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (h * X j)])
  · exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hx)

private theorem dom_bound_lemma_2 (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (y : Fin m → Fin n → ℂ) :
    ‖scal (aH X h) y‖ ≤ Real.exp (∑ i, |X i|) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  have e := (dom_bound_lemma X h hh j).2
  have hy : ‖y a j‖ ≤ ‖y‖ := (norm_le_pi_norm (y a) j).trans (norm_le_pi_norm y a)
  have hn : ‖scal (aH X h) y a j‖ = Real.exp (h * X j) * ‖y a j‖ := by
    simp only [scal, aH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hn]
  exact mul_le_mul e hy (norm_nonneg _) (Real.exp_pos _).le

private theorem dom_bound_lemma_3 (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (y : Fin m → Fin n → ℂ) :
    Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2 ≤ ∑ a, ∑ j, ‖scal (aH X h) y a j‖ ^ 2 := by
  calc Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2
        ≤ Real.exp (-(∑ i, |X i|)) ^ 2 * ∑ a, ∑ j, ‖y a j‖ ^ 2 := by
          gcongr
          exact sq_norm_le_sum y
    _ = ∑ a, ∑ j, Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y a j‖ ^ 2 := by
          simp only [Finset.mul_sum]
    _ ≤ ∑ a, ∑ j, ‖scal (aH X h) y a j‖ ^ 2 := by
          gcongr with a _ j _
          rw [norm_scal_sq]
          gcongr
          exact Real.exp_le_exp.mp (dom_bound_lemma X h hh j).1

theorem dom_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (scal (aH X h) y) * gs c (scal (aH X h) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨C, k, hC, hP⟩ := poly_bound P
  have hM0 : 0 ≤ ∑ i, |X i| := Finset.sum_nonneg fun i _ => abs_nonneg (X i)
  have hκ : 0 < c * Real.exp (-(∑ i, |X i|)) ^ 2 := by positivity
  obtain ⟨D, hD, hdec⟩ := decay k _ hκ ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)
  refine ⟨C * Real.exp (∑ i, |X i|) ^ k * D, by positivity, fun h hh y => ?_⟩
  have hv := dom_bound_lemma_2 X h hh y
  have hs := dom_bound_lemma_3 X h hh y
  have hg : ‖gs c (scal (aH X h) y)‖ ≤
      Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hc.le]
  have hp : ‖evX P (scal (aH X h) y)‖ ≤ C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k := by
    calc ‖evX P (scal (aH X h) y)‖ ≤ C * (1 + ‖scal (aH X h) y‖) ^ k := hP _
      _ ≤ C * (Real.exp (∑ i, |X i|) * (1 + ‖y‖)) ^ k := by
          gcongr
          have : 1 ≤ Real.exp (∑ i, |X i|) := Real.one_le_exp hM0
          nlinarith [norm_nonneg y]
      _ = C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k := by
          rw [mul_pow, mul_assoc]
  calc ‖evX P (scal (aH X h) y) * gs c (scal (aH X h) y)‖
        = ‖evX P (scal (aH X h) y)‖ * ‖gs c (scal (aH X h) y)‖ := norm_mul _ _
    _ ≤ (C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k) *
          Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2)) := by
          gcongr
    _ = C * Real.exp (∑ i, |X i|) ^ k *
          ((1 + ‖y‖) ^ k * Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2))) := by ring
    _ ≤ C * Real.exp (∑ i, |X i|) ^ k *
          (D * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hdec _ (norm_nonneg y)) (by positivity)
    _ = C * Real.exp (∑ i, |X i|) ^ k * D *
          (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end
