module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportGeo
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.EquivA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.BasePointPsiExpFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmDSingleMulVec

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SIntEquiv
noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ}

def biEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := (a * Matrix.of x * b : Mat k r)
  invFun x := (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * b) * b⁻¹ = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.mul_nonsing_inv _ hb,
      Matrix.mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * b⁻¹) * b = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ ha, Matrix.nonsing_inv_mul _ hb,
      Matrix.mul_one]
  measurable_toFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable
  measurable_invFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable

theorem sInt_equiv {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
    [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Mt k r)} (hB : IsBData z c u π μW μN) (f : Mat k r → ℂ) (ξ : Vp) (g : Mat k r)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ g) := by
  obtain ⟨hz, hT, -, hHC, hW, hN⟩ := hB
  have hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π := hcTypeW_uRep k r z u Vp π hz hT hHC
  have hMP := Mult1.S0.A.shift_measurePreserving Mult1.haarUniqueSF' Formalism.FourierDecayAlt.P.weyl_subgroup_closed
    Formalism.FourierDecayAlt.P.weyl_haar_exists Formalism.FourierDecayAlt.P.unipotent_radical_closed Formalism.FourierDecayAlt.P.unipotent_haar_exists
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof hz hT hW hN hh₀ hm₀
  have hd := TransportGeo.uh_det hh₀.1
  have hdm := TransportGeo.uh_det hm₀.1
  let e := MeasurableEquiv.prodCongr (biEquiv (1 : Mat k r) h₀ (by simp) hd)
    (biEquiv h₀⁻¹ (h₀ * m₀) (TransportGeo.uh_det (TransportGeo.uh_inv hh₀.1))
      (TransportGeo.uh_det (TransportGeo.uh_mul hh₀.1 hm₀.1)))
  have he : (fun p : Mt k r × Mt k r => Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r)
      (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r)) = e := by
    funext p
    refine Prod.ext ?_ ?_
    · show (Matrix.of p.1 * h₀ : Mat k r) = 1 * Matrix.of p.1 * h₀
      rw [Matrix.one_mul]
    · exact Matrix.mul_assoc _ h₀ m₀
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by rw [ae_iff]; simpa using hN.2.2.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  set F : Mt k r × Mt k r → Vp := fun p => f (Matrix.of p.1 * Matrix.of p.2 * g) •
    chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  let L : Vp →ₗᵢ[ℂ] Vp := ⟨(π h₀ : Vp →ₗ[ℂ] Vp), hπ.2.1 h₀ hh₀⟩
  have h1 : sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      ∫ p, Formalism.MainNotions.S.psiGen k r z c m₀ • L (F (e p)) ∂(μW.prod μN) := by
    unfold sInt
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [← he]
    exact Mult1.S0.A.integrand_shift Formalism.FourierDecayAlt.P.weyl_subgroup_closed Formalism.FourierDecayAlt.P.unipotent_radical_closed
      Formalism.QuantumDeterminants.unitary_weyl_normal_holds hz c hπ f ξ hh₀ hm₀ hp.1 hp.2
  rw [he] at hMP
  rw [h1, integral_smul, L.integral_comp_comm (fun p => F (e p)), hMP.integral_comp' F]
  rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HaarRightStatement
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.LFSingleNe
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.BlockEmbeddingSkewHermitian
noncomputable section

open Matrix Finset Filter

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N TransportGeo

variable {k r : ℕ}

def kap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Fin r) : ℝ :=
  if p.val + 1 < r then 1 else Real.sqrt (Tz k r z)

def LF (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Y : Mat k r) : ℂ :=
  ∑ p, c p * (kap k r z p * Y (eI k r p) (nxt k r p))

theorem ellA_frame {z : Fin (2 * r + k + 1) → ℂ} {g₀ : Mat k r} (hg : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hT : 0 < Tz k r z) (m : Mat k r) (p : Fin r) :
    Formalism.MainNotions.S.ellA k r z (g₀ * m * g₀⁻¹) p = kap k r z p * m (eI k r p) (nxt k r p) := by
  have hc := (colStd_iff g₀).mpr hg.2.1
  have hM := hc.midM hg.1
  have hrow : ∀ v : Fin (2 * r + k + 1) → ℂ, (g₀ *ᵥ v) (eI k r p) = v (eI k r p) := fun v => by
    simp only [Matrix.mulVec, dotProduct, fun j => hM (eI k r p) j (Or.inl (Or.inl p.isLt)), ite_mul,
      one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
  have hs : (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne')
  unfold Formalism.MainNotions.S.ellA kap nxt
  split_ifs with h
  · have e1 : ∀ X : Mat k r, X (eI k r p) (eI k r ⟨p.val + 1, h⟩) =
        (X *ᵥ bvec (eI k r ⟨p.val + 1, h⟩)) (eI k r p) := fun X => by simp [bvec]
    rw [e1 (g₀ * m * g₀⁻¹), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hc.inv hg.1 _ (Or.inl h), hrow, ← e1 m, Complex.ofReal_one, one_mul]
    rfl
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      inv_mulVec (uh_det hg.1) hs (frame_mulVec hg hT), inv_inv, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Pi.smul_apply, hrow]
    simp [z0, bvec, wI]

theorem conj_lie {g₀ Y : Mat k r} (hg : g₀ ∈ UH (Hpk k r)) (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) :
    (g₀ * Y * g₀⁻¹)ᴴ * Hpk k r + Hpk k r * (g₀ * Y * g₀⁻¹) = 0 := by
  have h1 : (g₀⁻¹)ᴴ * Hpk k r * g₀⁻¹ = Hpk k r := uh_inv hg
  have hd := uh_det hg
  have e1 : Hpk k r * (g₀ * Y * g₀⁻¹) = (g₀⁻¹)ᴴ * (Hpk k r * Y) * g₀⁻¹ := by
    conv_lhs => rw [← h1]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  have e2 : (g₀ * Y * g₀⁻¹)ᴴ * Hpk k r = (g₀⁻¹)ᴴ * (Yᴴ * Hpk k r) * g₀⁻¹ := by
    have h2 : g₀ᴴ * (g₀⁻¹)ᴴ = 1 := by
      rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hd, conjTranspose_one]
    conv_lhs => rw [← h1]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g₀ᴴ, h2, Matrix.one_mul]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hY, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_frame {g₀ : Mat k r} (hg : g₀ ∈ UH (Hpk k r)) (Y : Mat k r) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (g₀ * Y * g₀⁻¹)) = g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ := by
  rw [← Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det g₀).mpr (uh_det hg)), Matrix.mul_smul,
    Matrix.smul_mul]

open scoped Matrix.Norms.Operator in
theorem lieN_facts {z : Fin (2 * r + k + 1) → ℂ} (c : Fin r → ℂ) {g₀ Y : Mat k r}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g₀) (hT : 0 < Tz k r z) (h1 : Y ∈ levF (levB k r) 0)
    (h2 : Hpk k r * Yᴴ * Hpk k r = -Y) :
    Yᴴ * Hpk k r + Hpk k r * Y = 0 ∧ ∀ t : ℝ,
      g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ ∈ Nset k r ∧
      Formalism.MainNotions.S.psiGen k r z c (g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹) =
        Complex.exp ((t : ℂ) * (Complex.I * ((LF z c Y).re : ℂ))) := by
  have hc := (colStd_iff g₀).mpr hg.2.1
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · have := congrArg (fun X => Hpk k r * X) h2
    simp only [← Matrix.mul_assoc, Hpk_sq, Matrix.one_mul, Matrix.mul_neg] at this
    rw [this, neg_add_cancel]
  · have hY : Y ∈ Formalism.MainNotions.S.lieOf (Nset k r) := by
      rw [lieOf_Nset_eq]; exact mem_lieN.mpr ⟨h1, h2⟩
    exact conj_mem_N hg.1 (hc.midM hg.1).lev0 ((hc.inv hg.1).midM (uh_inv hg.1)).lev0 (hY t)
  · have h3 : (t : ℂ) • Y ∈ levF (levB k r) 0 := fun a b h => by simp [h1 a b h]
    unfold Formalism.MainNotions.S.psiGen
    simp only [ellA_frame hg hT, exp_entry _ h3]
    have : (∑ p, c p * (kap k r z p * ((t : ℂ) • Y) (eI k r p) (nxt k r p))) = t * LF z c Y := by
      simp only [LF, mul_sum, Matrix.smul_apply, smul_eq_mul]
      exact sum_congr rfl fun p _ => by ring
    rw [this, Complex.re_ofReal_mul]
    congr 1; push_cast; ring

def emb0 (k r : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Mat k r where
  toFun A := Formalism.MainNotions.S.blockW k r A - Formalism.MainNotions.S.blockW k r 0
  map_add' A B := by
    ext i j; simp only [Formalism.MainNotions.S.blockW, Matrix.sub_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' t A := by
    ext i j; simp only [Formalism.MainNotions.S.blockW, Matrix.sub_apply, Matrix.smul_apply]; split_ifs <;> simp

theorem block_embedding_single (i j : Fin k) :
    emb0 k r (Matrix.single i j 1) = Matrix.single (StandardBasisEmbedding.eB k r i) (StandardBasisEmbedding.eB k r j) 1 := by
  ext a b
  simp only [emb0, LinearMap.coe_mk, AddHom.coe_mk, Formalism.MainNotions.S.blockW, Matrix.sub_apply,
    Matrix.single_apply, StandardBasisEmbedding.eB, Fin.ext_iff]
  have := i.isLt
  have := j.isLt
  split_ifs <;> first | omega | simp

open scoped Matrix.Norms.Operator in
theorem exp_embed (A : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 k r A) = Formalism.MainNotions.S.blockW k r (NormedSpace.exp A) := by
  set B0 := Formalism.MainNotions.S.blockW k r (0 : Matrix (Fin k) (Fin k) ℂ) with hB0
  have hb : ∀ X, Formalism.MainNotions.S.blockW k r X = emb0 k r X + B0 := fun X => (sub_add_cancel _ _).symm
  have l0 : ∀ X, B0 * Formalism.MainNotions.S.blockW k r X = B0 := fun X => by rw [hB0, ← StandardBasisEmbedding.blockW_mul, zero_mul]
  have r0 : ∀ X, Formalism.MainNotions.S.blockW k r X * B0 = B0 := fun X => by rw [hB0, ← StandardBasisEmbedding.blockW_mul, mul_zero]
  have b0 : B0 * B0 = B0 := l0 0
  let f : Matrix (Fin k) (Fin k) ℂ × ℂ →+* Mat k r :=
    { toFun := fun x => emb0 k r x.1 + x.2 • B0
      map_one' := by
        show emb0 k r 1 + (1 : ℂ) • B0 = 1
        rw [one_smul, ← hb, StandardBasisEmbedding.blockW_one]
      map_mul' := fun x y => by
        show (Formalism.MainNotions.S.blockW k r (x.1 * y.1) - B0) + (x.2 * y.2) • B0 =
          (Formalism.MainNotions.S.blockW k r x.1 - B0 + x.2 • B0) * (Formalism.MainNotions.S.blockW k r y.1 - B0 + y.2 • B0)
        simp only [StandardBasisEmbedding.blockW_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_smul, Matrix.smul_mul, l0, r0, b0, sub_self, smul_smul, zero_add,
          mul_comm y.2 x.2]
        abel
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), add_smul]; abel }
  have hf : Continuous f :=
    ((emb0 k r).continuous_of_finiteDimensional.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have h := NormedSpace.map_exp f hf (A, (0 : ℂ))
  have e1 : f (A, (0 : ℂ)) = emb0 k r A := by simp [f]
  have e2 : f (NormedSpace.exp (A, (0 : ℂ))) = Formalism.MainNotions.S.blockW k r (NormedSpace.exp A) := by
    have a1 := Prod.fst_exp (A, (0 : ℂ))
    have a2 := (Prod.snd_exp (A, (0 : ℂ))).trans NormedSpace.exp_zero
    refine (congrArg₂ (fun (X : Matrix (Fin k) (Fin k) ℂ) (t : ℂ) => emb0 k r X + t • B0) a1 a2).trans ?_
    simp only [one_smul]
    exact (hb _).symm
  exact (congrArg NormedSpace.exp e1.symm).trans (h.symm.trans e2)

theorem block_embedding_skew_hermitian {A : Matrix (Fin k) (Fin k) ℂ} (hA : Aᴴ = -A) :
    (emb0 k r A)ᴴ * Hpk k r + Hpk k r * emb0 k r A = 0 := by
  have h1 : (emb0 k r A)ᴴ = -emb0 k r A := by
    rw [← map_neg, ← hA]
    show (Formalism.MainNotions.S.blockW k r A - Formalism.MainNotions.S.blockW k r 0)ᴴ = _ - _
    rw [conjTranspose_sub, StandardBasisEmbedding.blockW_conjTranspose, StandardBasisEmbedding.blockW_conjTranspose, conjTranspose_zero]
  have h2 : Hpk k r * emb0 k r A = emb0 k r A * Hpk k r := by
    show Hpk k r * (_ - _) = (_ - _) * Hpk k r
    rw [Matrix.mul_sub, Matrix.sub_mul, StandardBasisEmbedding.H_comm, StandardBasisEmbedding.H_comm]
  rw [h1, h2, Matrix.neg_mul, neg_add_cancel]

theorem frame_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g₀ : Mat k r} (hg : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hT : 0 < Tz k r z) {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g₀ * Formalism.MainNotions.S.blockW k r h * g₀⁻¹ ∈ UWset k r z := by
  have hm := StandardBasisEmbedding.mem_UW (r := r) hh
  have hc := (colStd_iff g₀).mpr hg.2.1
  have hs : (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne')
  exact ⟨uh_mul (uh_mul hg.1 hm.1) (uh_inv hg.1),
    (colStd_iff _).mp ((hc.mul ((colStd_iff _).mpr hm.2.1)).mul (hc.inv hg.1)),
    (fix_iff (uh_det hg.1) hs (frame_mulVec hg hT) _).mp hm.2.2⟩

theorem exists_derived {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (ρ : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp)) (hρ : Formalism.MainNotions.S.IsHCTypeU k u ρ) :
    ∃ dρ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Module.End ℂ Vp,
      (∀ A : Matrix (Fin k) (Fin k) ℂ, Aᴴ = -A → ∀ v, HasDerivAt
        (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • A)) v) (dρ A v) 0) ∧
      ∀ (x : ℂ) (ζ : Vp), Capelli.capelliC (fun i j => dρ (Matrix.single i j 1)) x ζ =
        (∏ j : Fin k, (x + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) • ζ := by
  obtain ⟨T, U, hU⟩ := HW.kType_of_hcTypeU ρ hρ
  let dρ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Module.End ℂ Vp :=
    (U.symm.toLinearEquiv.conj : Module.End ℂ T.V →ₗ[ℂ] Module.End ℂ Vp) ∘ₗ
      (ContinuousLinearMap.coeLM ℂ) ∘ₗ T.dτ
  have hd : ∀ A v, dρ A (U.symm v) = U.symm (T.dτ A v) := fun A v => by
    simp [dρ, LinearEquiv.conj_apply]
  refine ⟨dρ, fun A hA v => ?_, fun x ζ => ?_⟩
  · have hK : inK (fun _ : Fin k => true) A := (HW.inK_iff' _ A).mpr ⟨hA, by simp [Jm]⟩
    obtain ⟨γ, hγ⟩ := HW.exists_curve _ hK
    have h1 := (((U.symm.toContinuousLinearEquiv : T.V →L[ℂ] Vp).comp
      (ContinuousLinearMap.apply ℂ T.V (U v))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (T.hasDeriv A hK γ hγ)
    refine HasDerivAt.congr_deriv (h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
    · show ρ _ v = U.symm (T.op (γ t) (U v))
      rw [← hU, hγ, U.symm_apply_apply]
    · have := hd A (U v)
      rw [U.symm_apply_apply] at this
      exact this.symm
  · have hk : ∀ a b v, dρ (Matrix.single a b 1) (U.symm v) = U.symm (HW.kunits T a b v) :=
      fun a b v => hd _ v
    have hE : IsGlRep fun i j => dρ (Matrix.single i j 1) := fun a b c d => by
      ext v
      obtain ⟨v, rfl⟩ := U.symm.surjective v
      have := congrArg U.symm (LinearMap.congr_fun (HW.KType.kRel T a b c d rfl rfl) v)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hk, map_sub] at this ⊢
      rw [this]
      congr 1 <;> split_ifs <;> simp [hk]
    have hw : IsHWVec (fun i j => dρ (Matrix.single i j 1)) (lowK (fun _ : Fin k => true) u)
        (U.symm T.w) := ⟨fun a => by rw [hd, T.w_wt, map_smul], fun a b h => by
      rw [hd, T.w_hw a b h rfl, map_zero]⟩
    have hgen : ζ ∈ genSub (fun i j => dρ (Matrix.single i j 1)) (Submodule.span ℂ {U.symm T.w}) := by
      refine Submodule.mem_sInf.mpr fun S hS => ?_
      have h1 : Formalism.REAL.kSpan (fun _ : Fin k => true) (HW.kunits T) T.w ≤
          S.comap U.symm.toLinearEquiv.toLinearMap :=
        sInf_le ⟨hS.1 (Submodule.subset_span rfl), fun a b _ v hv => by
          show U.symm (HW.kunits T a b v) ∈ S
          rw [← hk]; exact hS.2 a b _ hv⟩
      rw [HW.KType.kSpan_eq_top] at h1
      simpa using h1 (Submodule.mem_top (x := U ζ))
    rw [Capelli.capelliC_genSub _ hE _ _ hw x ζ hgen]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    have h1 : (univ.filter fun b : Fin k => j < b) = Ioi j := by ext; simp
    have h2 : (univ.filter fun b : Fin k => b < j) = Iio j := by ext; simp
    have h3 : j.val + 1 ≤ k := j.isLt
    simp only [lowK, rhoN, rhoC, Pi.sub_apply, Pi.add_apply, and_true, ne_eq, not_true_eq_false,
      and_false, filter_false, card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio, Nat.sub_sub,
      Nat.cast_sub (by omega : 1 + j.val ≤ k)]
    push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

variable {k r : ℕ}

def psiC (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Z : Mat k r) : ℂ :=
  Complex.I / 2 * (LF z c Z - starRingEnd ℂ (LF z c (Hpk k r * Zᴴ * Hpk k r)))

theorem LF_comb (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (s t : ℂ) (X Y : Mat k r) :
    LF z c (s • (X + t • Y)) = s * (LF z c X + t * LF z c Y) := by
  simp only [LF, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun p _ => by ring

theorem parts (Z : Mat k r) :
    let S := Hpk k r * Zᴴ * Hpk k r
    let Y1 := (1 / 2 : ℂ) • (Z + (-1 : ℂ) • S)
    let Y2 := (-Complex.I / 2) • (Z + (1 : ℂ) • S)
    Hpk k r * Y1ᴴ * Hpk k r = -Y1 ∧ Hpk k r * Y2ᴴ * Hpk k r = -Y2 ∧ Z = Y1 + Complex.I • Y2 := by
  intro S Y1 Y2
  have hS : Hpk k r * Sᴴ * Hpk k r = Z := by
    simp only [S, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, ← Matrix.mul_assoc, Hpk_sq,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, Hpk_sq, Matrix.mul_one]
  have hZ : Hpk k r * Zᴴ * Hpk k r = S := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Y1, conjTranspose_smul, conjTranspose_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hS, hZ]
    ext i j; simp; ring
  · simp only [Y2, conjTranspose_smul, conjTranspose_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hS, hZ]
    ext i j; simp; ring
  · ext i j
    simp only [Y1, Y2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (Z i j + S i j) / 2 * Complex.I_mul_I

theorem psiC_parts (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Z S : Mat k r) :
    Complex.I * ((LF z c ((1 / 2 : ℂ) • (Z + (-1 : ℂ) • S))).re : ℂ) +
      Complex.I * (Complex.I * ((LF z c ((-Complex.I / 2) • (Z + (1 : ℂ) • S))).re : ℂ)) =
      Complex.I / 2 * (LF z c Z - starRingEnd ℂ (LF z c S)) := by
  rw [LF_comb, LF_comb]
  apply Complex.ext <;> simp <;> ring

open scoped Matrix.Norms.Operator in
theorem st_mem {Z : Mat k r} (h : Z ∈ levF (levB k r) 0) : Hpk k r * Zᴴ * Hpk k r ∈ levF (levB k r) 0 :=
  isAdjB.mem Z h

theorem nxt_val (p : Fin r) : (nxt k r p).val = if p.val + 1 < r then p.val + 1 else r + k := by
  unfold nxt; split_ifs <;> rfl

theorem LF_single (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (a b : Fin (2 * r + k + 1)) (s : ℂ) :
    LF z c (Matrix.single a b s) =
      ∑ p, if a = eI k r p ∧ b = nxt k r p then c p * (kap k r z p * s) else 0 := by
  refine sum_congr rfl fun p _ => ?_
  rw [Matrix.single_apply]; split_ifs <;> simp

theorem st_single (a b : Fin (2 * r + k + 1)) :
    Hpk k r * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r =
      Matrix.single (flipB k r b) (flipB k r a) (sgnB k r b * sgnB k r a) := by
  ext i j
  rw [mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = flipB k r j ∧ b = flipB k r i
  · obtain ⟨rfl, rfl⟩ := h
    simp [flipB_flipB, sgnB_flip]
  · rw [if_neg h, if_neg, star_zero, mul_zero, zero_mul]
    rintro ⟨rfl, rfl⟩
    exact h ⟨(flipB_flipB a).symm, (flipB_flipB b).symm⟩

def Simple (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Prop :=
  levB k r b = levB k r a + 1 ∧ ¬ (r ≤ a.val ∧ a.val < r + k) ∧ ¬ (r ≤ b.val ∧ b.val < r + k)

theorem simple_of {a b : Fin (2 * r + k + 1)} {p : Fin r} :
    (a = eI k r p ∧ b = nxt k r p → Simple k r a b) ∧
      (flipB k r b = eI k r p ∧ flipB k r a = nxt k r p → Simple k r a b) := by
  have := p.isLt
  have := a.isLt
  have := b.isLt
  simp only [Fin.ext_iff, flipB_val, nxt_val, eI, Simple, levB]
  constructor <;> rintro ⟨h1, h2⟩ <;> split_ifs at h1 h2 ⊢ <;> omega

theorem psiC_zero (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {a b : Fin (2 * r + k + 1)}
    (h : ¬ Simple k r a b) : psiC z c (Matrix.single a b 1) = 0 := by
  rw [psiC, st_single, LF_single, LF_single, sum_eq_zero fun p _ => if_neg fun hp => h (simple_of.1 hp),
    sum_eq_zero fun p _ => if_neg fun hp => h (simple_of.2 hp)]
  simp

theorem LF_single_ne {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} (hc : ∀ p, c p ≠ 0)
    (hT : 0 < Tz k r z) (p : Fin r) {s : ℂ} (hs : s ≠ 0) :
    LF z c (Matrix.single (eI k r p) (nxt k r p) s) ≠ 0 := by
  rw [LF_single, sum_eq_single p (fun q _ hq => if_neg fun h => hq
    (Fin.ext (by have := congrArg Fin.val h.1; exact this.symm))) (by simp), if_pos ⟨rfl, rfl⟩]
  refine mul_ne_zero (hc p) (mul_ne_zero ?_ hs)
  unfold kap
  split_ifs
  · simp
  · exact_mod_cast (Real.sqrt_pos.mpr hT).ne'

theorem psiC_ne {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} (hc : ∀ p, c p ≠ 0) (hT : 0 < Tz k r z)
    {a b : Fin (2 * r + k + 1)} (h : Simple k r a b) : psiC z c (Matrix.single a b 1) ≠ 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have hI : Complex.I / 2 ≠ 0 := div_ne_zero Complex.I_ne_zero two_ne_zero
  rw [psiC, st_single]
  refine mul_ne_zero hI ?_
  unfold Simple levB at h
  by_cases h1 : a.val < r
  · have e1 : a = eI k r ⟨a.val, h1⟩ := rfl
    have e2 : b = nxt k r ⟨a.val, h1⟩ := Fin.ext (by rw [nxt_val]; split_ifs at h ⊢ <;> simp only at * <;> omega)
    rw [LF_single z c (flipB k r b), sum_eq_zero fun p _ => if_neg fun hp => ?_, map_zero, sub_zero]
    · have := LF_single_ne hc hT ⟨a.val, h1⟩ one_ne_zero
      rwa [← e1, ← e2] at this
    · have h2 := congrArg Fin.val hp.2
      have := p.isLt
      rw [flipB_val, nxt_val] at h2
      split_ifs at h2 <;> omega
  · have h3 : r + k ≤ a.val ∧ b.val = a.val + 1 := by split_ifs at h <;> omega
    have hp : 2 * r + k - b.val < r := by omega
    have e1 : flipB k r b = eI k r ⟨_, hp⟩ := Fin.ext (by rw [flipB_val, if_pos (by omega)]; rfl)
    have e2 : flipB k r a = nxt k r ⟨_, hp⟩ := Fin.ext (by
      rw [flipB_val, nxt_val]; split_ifs <;> simp only at * <;> omega)
    rw [LF_single z c a, sum_eq_zero fun p _ => if_neg fun hq => ?_, zero_sub, neg_ne_zero, e1, e2]
    · refine (map_ne_zero _).mpr (LF_single_ne hc hT _ ?_)
      unfold sgnB; split_ifs <;> simp
    · have h2 := congrArg Fin.val hq.1
      have := p.isLt
      simp only [eI] at h2; omega

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FrameForm
noncomputable section

open Matrix MeasureTheory Filter

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
  {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
  [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
  {μW μN : Measure (Mt k r)} {P x₀ g : Mat k r} {w : H} {a : ℝ}

theorem good_bound {m : H} (hm : TmGood ε σ x₀ w a m) :
    ∃ C : ℝ, ∀ y ∈ UJset ε, ‖coefX σ x₀ w m y‖ ≤ C * frob y ^ (1 - a) := by
  obtain ⟨C, hC⟩ := hm.2 []
  refine ⟨|C|, fun y hy => (hC y hy).trans ?_⟩
  have h1 := tmA_one_le_frob hy (0 : Fin (2 * r + k + 1))
  exact mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
    (Real.rpow_nonneg (by linarith) _) (abs_nonneg C)

theorem per_lin (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {m m' : H} (hm : TmGood ε σ x₀ w a m)
    (hm' : TmGood ε σ x₀ w a m') (t : ℂ) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m + t • m')) ξ g =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m) ξ g +
        t • per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m') ξ g := by
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have i1 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm.1) C hC
  have i2 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm'.1) C' hC'
  unfold per sInt
  rw [← integral_smul]
  refine Eq.trans ?_ (integral_add i1 (i2.smul t))
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [coefX, map_add (f := _), map_smul, inner_add_right, inner_smul_right, add_smul, smul_smul,
    Pi.smul_apply]

theorem frame_form (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hg : g ∈ UH (Hpk k r)) :
    IsUnit (g * P⁻¹).det ∧ (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = Jm ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine ⟨by rw [Matrix.det_mul]; exact (TransportGeo.uh_det hg).mul (Matrix.isUnit_nonsing_inv_det P hd),
    ?_⟩
  calc (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * Hpk k r * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * Pᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by rw [hg', ← hP.2]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]; rfl

theorem mul_inUJ (hP : Formalism.MainNotions.S.IsCayley k r ε P) {y : Mat k r} (hy : y ∈ UH (Hpk k r)) :
    P * y * P⁻¹ ∈ UJset ε := by
  show (P * y * P⁻¹)ᴴ * Jm ε * (P * y * P⁻¹) = Jm ε
  have h := (frame_form hP hy).2
  rw [← hP.2] at h
  refine Eq.trans ?_ h
  show (P * y * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * y * P⁻¹) = _
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem per_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hx₀ : x₀ ∈ UJset ε)
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {Y : Mat k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) (m : D)
    (hm : TmGood ε σ x₀ w a (m : H))
    (hm' : TmGood ε σ x₀ w a ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) :
    HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m : H)) ξ
        (NormedSpace.exp ((t : ℂ) • Y) * g))
      (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
        (coefX σ x₀ w ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) ξ g) 0 := by
  obtain ⟨hR, hJ⟩ := frame_form hP hg
  set R := g * P⁻¹ with hRd
  have hX : inG ε (R⁻¹ * Y * R) := by
    have e1 : Jm ε * (R⁻¹ * Y * R) = Rᴴ * (Hpk k r * Y) * R := by
      rw [← hJ]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hR]
    have e2 : (R⁻¹ * Y * R)ᴴ * Jm ε = Rᴴ * (Yᴴ * Hpk k r) * R := by
      have h2 : (R⁻¹)ᴴ * Rᴴ = 1 := by
        rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hR, conjTranspose_one]
      rw [← hJ]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (R⁻¹)ᴴ, h2, Matrix.one_mul]
    show (R⁻¹ * Y * R)ᴴ * Jm ε + Jm ε * (R⁻¹ * Y * R) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hY, Matrix.mul_zero, Matrix.zero_mul]
  have hRd' : ∀ y ∈ UJset ε, Formalism.REAL.Rd (R⁻¹ * Y * R) (coefX σ x₀ w (m : H)) y =
      coefX σ x₀ w ((actM E (R⁻¹ * Y * R) m : D) : H) y := fun y hy =>
    tmB_rd_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hy) hX w m
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have h := (CurveContinuity.deriv_int hP hB hg ξ a hb _ hm.1 C hC _ hX C'
    (fun y hy => by rw [hRd' y hy]; exact hC' y hy)).2
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · have e : NormedSpace.exp ((t : ℂ) • (R⁻¹ * Y * R)) = R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R := by
      rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det R).mpr hR), Matrix.mul_smul,
        Matrix.smul_mul]
    simp only [per, sInt, e]
    congr 1
    funext p
    congr 2
    calc _ = P * (Matrix.of p.1 * Matrix.of p.2) * (NormedSpace.exp ((t : ℂ) • Y) * R) := by
          rw [hRd]; simp only [Matrix.mul_assoc]
      _ = P * (Matrix.of p.1 * Matrix.of p.2) * (R * (R⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * R))) := by
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hR]
      _ = _ := by
          rw [← Matrix.mul_assoc R⁻¹]
          generalize R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R = A
          rw [hRd]; simp only [Matrix.mul_assoc]
  · unfold per sInt
    refine integral_congr_ae ?_
    filter_upwards [CurveContinuity.ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp
    rw [hRd' _ (mul_inUJ hP (TransportGeo.uh_mul (TransportGeo.uh_mul hp.1.1 hp.2.1) hg))]

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def capIdx (k r : ℕ) (i : Fin (k + 2 * r + 1)) : Fin (2 * r + k + 1) := Fin.cast (by omega) i

def coefL {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (ξ : Vp) (g : Mat k r) (m : H) : Vp :=
  per P μW μN ψ π (coefX σ x₀ w m) ξ g

def PerEquivStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), IsBData z c u π μW μN →
    ∀ (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r), ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r,
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ (h * m * x) =
        Formalism.MainNotions.S.psiGen k r z c m • π h (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x)

theorem perEquiv : PerEquivStatement := by
  intro k r u z c Vp _ _ _ π μW μN P hB F ξ x h hh m hm
  exact EvaluationEquivalence.sInt_equiv hB (fun g => F (P * g * P⁻¹)) ξ x hh hm

def FrameLawStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h →
    ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w : V) (ξ : Vp) (g : Mat k r), x₀ ∈ UJset ε → g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      ∃ (g₀ : Mat k r) (Dk : Fin k → Fin k → Module.End ℂ Vp)
        (ψ' : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ),
        Formalism.MainNotions.S.IsFrameW k r z g₀ ∧
        (∀ a b, Capelli.blk k r a < Capelli.blk k r b → ∀ m ∈ genSub E V,
          coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g
              ((frameE (g₀⁻¹ * g * P⁻¹) E (capIdx k r a) (capIdx k r b) m : D) : H) =
            ψ' a b • coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g ((m : D) : H)) ∧
        (∀ a b, Capelli.blk k r a < Capelli.blk k r b → ¬ Capelli.IsSimplePair k r a b → ψ' a b = 0) ∧
        (0 < r → Capelli.kappa k r ψ' ≠ 0) ∧
        (∀ i j, ∀ m ∈ genSub E V,
          coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g
              ((frameE (g₀⁻¹ * g * P⁻¹) E (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) m :
                D) : H) =
            Dk i j (coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g ((m : D) : H))) ∧
        ∀ (x : ℂ) (ζ : Vp), Capelli.capelliC Dk x ζ =
          (∏ j : Fin k, (x + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) • ζ

theorem frameLaw : FrameLawStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD _ _ _ hμ hcoef hp hq hgap hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ g hx₀ hg
  obtain ⟨hq0, hneed⟩ := gapNeed k r ε h hp hq hgap
  have hdd := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ
  have hb := CurveContinuity.per_gap hgap
  have hh0 : 0 ≤ h := by
    have h1 := hgap.1
    have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have ha0 : 0 ≤ aExp ε h := div_nonneg hh0 (by positivity)
  have hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ ((w : D) : H) (aExp ε h) (m : H) :=
    fun m hm => tmC_good_genSub hσ hD hμ hcoef ha0 (fun wd v₁ v₂ => hdd wd v₁ v₂) hx₀ w hm
  have hT := hB.2.1
  obtain ⟨g₀, hg₀, hρ⟩ := hB.2.2.2.1
  obtain ⟨dρ, hdρ, hcap⟩ := EvaluationEquivalence.exists_derived _ hρ
  set l : D → Vp := fun m => coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g (m : H)
    with hl
  have hact : ∀ X : Mat k r, ∀ m ∈ genSub E V, actM E X m ∈ genSub E V := fun X m hm => by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      (Submodule.mem_sInf.mpr fun S hS => hS.2 a b _ (Submodule.mem_sInf.mp hm S hS))
  let Λ : Mat k r → Module.End ℂ D := fun Z => actM E ((g * P⁻¹)⁻¹ * (g₀ * Z * g₀⁻¹) * (g * P⁻¹))
  have hΛ : ∀ Y1 Y2 : Mat k r, ∀ m ∈ genSub E V,
      l (Λ (Y1 + Complex.I • Y2) m) = l (Λ Y1 m) + Complex.I • l (Λ Y2 m) := fun Y1 Y2 m hm => by
    have e : Λ (Y1 + Complex.I • Y2) m = Λ Y1 m + Complex.I • Λ Y2 m := by
      simp only [Λ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, actM,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
        LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [e]
    exact EvaluationEquivalence.per_lin hP hB hg hb ξ (hgood _ (hact _ m hm)) (hgood _ (hact _ m hm)) _
  have hfr : ∀ i j, frameE (g₀⁻¹ * g * P⁻¹) E i j = Λ (Matrix.single i j 1) := fun i j => by
    have e : (g * P⁻¹)⁻¹ * (g₀ * Matrix.single i j 1 * g₀⁻¹) * (g * P⁻¹) =
        (g₀⁻¹ * g * P⁻¹)⁻¹ * Matrix.single i j 1 * (g₀⁻¹ * g * P⁻¹) := by
      rw [Matrix.mul_assoc g₀⁻¹, Matrix.mul_inv_rev g₀⁻¹,
        Matrix.nonsing_inv_nonsing_inv _ (TransportGeo.uh_det hg₀.1)]
      simp only [Matrix.mul_assoc]
    simp only [Λ, e, frameE, actM]
    generalize g₀⁻¹ * g * P⁻¹ = Q
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  have hder : ∀ Y : Mat k r, Yᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * Y = 0 → ∀ m ∈ genSub E V,
      HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ ((w : D) : H) (m : H)) ξ
        (g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ * g)) (l (Λ Y m)) 0 := fun Y hY m hm => by
    have := EvaluationEquivalence.per_deriv hσ hD hx₀ hP hB hg hb ξ (EvaluationEquivalence.conj_lie hg₀.1 hY) m (hgood m hm)
      (hgood _ (hact _ m hm))
    simp only [EvaluationEquivalence.exp_conj_frame hg₀.1] at this
    exact this
  have h1W : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UWset k r z := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).one_mem
  have h1N : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).one_mem
  have hπ := hcTypeW_uRep k r z u Vp π hB.1 hT hB.2.2.2.1
  have hN : ∀ Y : Mat k r, Y ∈ Base.N.levF (Base.levB k r) 0 →
      Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r = -Y → ∀ m ∈ genSub E V,
      l (Λ Y m) = (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) • l m := fun Y h1 h2 m hm => by
    obtain ⟨hY, hf⟩ := EvaluationEquivalence.lieN_facts c hg₀ hT h1 h2
    refine (hder Y hY m hm).unique ?_
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ))))
        (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
        (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) (x := (0 : ℝ))).cexp
    refine (h3.smul_const (l m)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have h4 := perEquiv k r u z c Vp π μW μN P hB (coefX σ x₀ ((w : D) : H) (m : H)) ξ g 1 h1W _ (hf t).1
    rw [Matrix.one_mul, (hf t).2, hπ.1.1] at h4
    exact h4
  have hW : ∀ A : Matrix (Fin k) (Fin k) ℂ, Aᴴ = -A → ∀ m ∈ genSub E V,
      l (Λ (EvaluationEquivalence.emb0 k r A) m) = dρ A (l m) := fun A hA m hm => by
    refine (hder _ (EvaluationEquivalence.block_embedding_skew_hermitian hA) m hm).unique ?_
    refine (hdρ A hA (l m)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hu : NormedSpace.exp ((t : ℂ) • A) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
        conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal, smul_neg,
        ← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • A)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have h4 := perEquiv k r u z c Vp π μW μN P hB (coefX σ x₀ ((w : D) : H) (m : H)) ξ g _
      (EvaluationEquivalence.frame_mem_UW hg₀ hT hu) 1 h1N
    have h5 : Formalism.MainNotions.S.psiGen k r z c (1 : Mat k r) = 1 := by
      have h6 := Mult1.S0.A.psiGen_mul hB.1 c h1N h1N
      have h7 : Formalism.MainNotions.S.psiGen k r z c (1 : Mat k r) ≠ 0 := Complex.exp_ne_zero _
      rw [Matrix.one_mul] at h6
      exact (mul_right_eq_self₀.mp h6.symm).resolve_right h7
    rw [Matrix.mul_one, h5, one_smul] at h4
    simp only []
    rw [← map_smul, EvaluationEquivalence.exp_embed]
    exact h4
  refine ⟨g₀, fun i j => dρ (Matrix.single i j 1),
    fun a b => EvaluationEquivalence.psiC z c (Matrix.single (capIdx k r a) (capIdx k r b) 1), hg₀,
    fun a b hab m hm => ?_, fun a b _ hs => EvaluationEquivalence.psiC_zero z c hs, fun _ => ?_, fun i j m hm => ?_, hcap⟩
  · set Z : Mat k r := Matrix.single (capIdx k r a) (capIdx k r b) 1 with hZ
    have hZ1 : Z ∈ Base.N.levF (Base.levB k r) 0 := fun i j hij => by
      rw [hZ, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      have h8 : Base.levB k r (capIdx k r a) < Base.levB k r (capIdx k r b) := hab
      omega
    have hZ2 : Formalism.QuantumDeterminants.Hpk k r * Zᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Base.N.levF (Base.levB k r) 0 :=
      EvaluationEquivalence.st_mem hZ1
    obtain ⟨p1, p2, p3⟩ := EvaluationEquivalence.parts Z
    have m1 : ∀ s t : ℂ, s • (Z + t • (Formalism.QuantumDeterminants.Hpk k r * Zᴴ * Formalism.QuantumDeterminants.Hpk k r)) ∈
        Base.N.levF (Base.levB k r) 0 := fun s t i j hij => by
      simp only [Matrix.smul_apply, Matrix.add_apply, hZ1 i j hij, hZ2 i j hij, smul_zero, add_zero]
    show l (frameE _ E _ _ m) = _ • l m
    rw [hfr, ← hZ]
    conv_lhs => rw [p3]
    rw [hΛ _ _ m hm, hN _ (m1 _ _) p1 m hm, hN _ (m1 _ _) p2 m hm, smul_smul, ← add_smul,
      EvaluationEquivalence.psiC_parts]
    rfl
  · refine Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b _ => ?_
    split_ifs with hs
    · exact EvaluationEquivalence.psiC_ne hB.2.2.1 hT hs
    · exact one_ne_zero
  · set A : Matrix (Fin k) (Fin k) ℂ := Matrix.single i j 1 with hA
    have e1 : A = (1 / 2 : ℂ) • (A - Aᴴ) + Complex.I • ((-Complex.I / 2) • (A + Aᴴ)) := by
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      linear_combination (A a b + Aᴴ a b) / 2 * Complex.I_mul_I
    have s1 : ((1 / 2 : ℂ) • (A - Aᴴ))ᴴ = -((1 / 2 : ℂ) • (A - Aᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← smul_neg, neg_sub]; simp
    have s2 : ((-Complex.I / 2) • (A + Aᴴ))ᴴ = -((-Complex.I / 2) • (A + Aᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm, ← neg_smul]
      congr 1; simp; ring
    show l (frameE _ E _ _ m) = dρ A (l m)
    have e2 : (Matrix.single (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) 1 : Mat k r) =
        EvaluationEquivalence.emb0 k r A := (EvaluationEquivalence.block_embedding_single i j).symm
    rw [hfr, e2]
    conv_lhs => rw [e1, map_add (f := _), map_smul _ Complex.I]
    rw [hΛ _ _ m hm, hW _ s1 m hm, hW _ s2 m hm]
    conv_rhs => rw [e1, map_add (f := _), map_smul _ Complex.I]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem le_gen {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) : V ≤ genSub E V :=
  le_sInf fun _ hT => hT.1

theorem gen_stable {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (a b : Fin n) {v : M}
    (hv : v ∈ genSub E V) : E a b v ∈ genSub E V :=
  Submodule.mem_sInf.mpr fun T hT => hT.2 a b v (Submodule.mem_sInf.mp hv T hT)

theorem gen_stable_frame {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (Q : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) {v : M} (hv : v ∈ genSub E V) :
    frameE Q E i j v ∈ genSub E V := by
  unfold frameE
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (gen_stable E V a b hv)

theorem isGlRep_reindex {n n' : ℕ} (E : Fin n' → Fin n' → Module.End ℂ M) (e : Fin n → Fin n')
    (he : Function.Injective e) (hE : IsGlRep E) : IsGlRep (fun a b => E (e a) (e b)) := by
  intro a b c d
  have := hE (e a) (e b) (e c) (e d)
  simp only [he.eq_iff] at this
  exact this

theorem sum_beta_nnPlus (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hQ : Q⁻¹ * Q = 1) (c₀ : ℂ) (j₀ : Fin (m + 1)) (om : ℂ) (v : M) :
    ∑ d, (c₀ * Q (Fin.last m) d) • Capelli.nnPlus E (Q⁻¹ *ᵥ Pi.single j₀ 1) om v d =
      (c₀ * (-1 : ℂ) ^ (m + (j₀ : ℕ))) •
        Capelli.cminor (frameE Q E) (Fin.last m).succAbove j₀.succAbove (om - 1) v := by
  have h := congrArg (fun f => f v)
    (capelliCov (Module.End ℂ M) m E Q⁻¹ Q (om - 1) hE hQ (Fin.last m) j₀)
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Fin.val_last] at h
  have hF : (fun a b => ∑ c', ∑ d', (Q⁻¹ c' a * Q b d') • E c' d') = frameE Q E := rfl
  rw [hF] at h
  rw [mul_smul, h, Finset.smul_sum]
  unfold Capelli.nnPlus
  simp_rw [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

variable {k r : ℕ}

theorem frameGl {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (Q : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin n → Fin n → Module.End ℂ M) (hQ : Q * Q⁻¹ = 1) (hQ' : Q⁻¹ * Q = 1) (hE : IsGlRep E) :
    IsGlRep (frameE Q E) :=
  frameE_glRep Q hQ E hE

theorem per_add {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F₁ F₂ : Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (h₁ : Integrable (perI P ψ π F₁ ξ x) (μW.prod μN)) (h₂ : Integrable (perI P ψ π F₂ ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => F₁ G + F₂ G) ξ x = per P μW μN ψ π F₁ ξ x + per P μW μN ψ π F₂ ξ x := by
  rw [per_eq, per_eq, per_eq, ← integral_add h₁ h₂]
  congr 1
  funext p
  simp [perI, add_smul]

theorem hpk_mulVec (i : Fin (2 * r + k + 1)) (u : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ u) i = (if i.val = r + k then -1 else 1) * u (ExponentialSlopeDerivatives.sg k r i) := by
  simp only [Matrix.mulVec, dotProduct, ExponentialSlopeDerivatives.hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem beta_formula (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (z : Fin (2 * r + k + 1) → ℂ)
    (hTz : 0 < Formalism.QuantumDeterminants.Tz k r z) (g g₀ Q : Mat k r) (hg₀ : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hgQ : g * P⁻¹ = g₀ * Q) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ d, cJ ε (xJ P z) (Pi.single d 1) (P * g * P⁻¹) = c₀ * Q (Fin.last (2 * r + k)) d := by
  have hg₀U : g₀ᴴ * Formalism.QuantumDeterminants.Hpk k r * g₀ = Formalism.QuantumDeterminants.Hpk k r := hg₀.1
  have key : ∀ x' : Fin (2 * r + k + 1) → ℂ, g₀ *ᵥ x' = xOne k r z → ∀ d,
      cJ ε (xJ P z) (Pi.single d 1) (P * g * P⁻¹) =
        star x' ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (Q *ᵥ Pi.single d 1)) := by
    intro x' hx' d
    unfold xJ
    rw [cJ_transport ε P hP, Matrix.mulVec_mulVec (Pi.single d 1) g P⁻¹, hgQ,
      ← Matrix.mulVec_mulVec (Pi.single d 1) g₀ Q, ← hx']
    exact ExponentialSlopeDerivatives.herm_UH hg₀U x' _
  have hQe : ∀ d, (Q *ᵥ Pi.single d (1 : ℂ)) (Fin.last (2 * r + k)) = Q (Fin.last (2 * r + k)) d := by
    intro d; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  by_cases hr : r = 0
  · refine ⟨-((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ), ?_, fun d => ?_⟩
    · rw [neg_ne_zero, Complex.ofReal_ne_zero]
      exact (Real.sqrt_pos.mpr hTz).ne'
    · have hx : g₀ *ᵥ (((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) •
          Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))) = xOne k r z := by
        rw [hg₀.2.2]; unfold xOne; rw [if_pos hr]
      rw [key _ hx]
      have hw : Formalism.QuantumDeterminants.wI k r (Fin.last k) = Fin.last (2 * r + k) := Fin.ext (by simp [Formalism.QuantumDeterminants.wI]; omega)
      have hsg : ExponentialSlopeDerivatives.sg k r (Fin.last (2 * r + k)) = Fin.last (2 * r + k) := by
        apply Fin.ext; rw [ExponentialSlopeDerivatives.sg_val]; split_ifs <;> simp <;> omega
      have hst : star (((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Fin.last (2 * r + k))) =
          ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Fin.last (2 * r + k)) := by
        funext i; by_cases hi : i = Fin.last (2 * r + k) <;> simp [Formalism.QuantumDeterminants.bvec, hi]
      rw [hw, hst, smul_dotProduct, Formalism.QuantumDeterminants.bvec, single_dotProduct, one_mul, hpk_mulVec, hsg,
        if_pos (by simp; omega), hQe, smul_eq_mul]
      ring
  · refine ⟨1, one_ne_zero, fun d => ?_⟩
    have hx : g₀ *ᵥ Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) 1 = xOne k r z := by
      have := (hg₀.2.1 ⟨0, by omega⟩).1
      unfold xOne
      rw [if_neg hr]
      exact this
    have hsg : ExponentialSlopeDerivatives.sg k r ⟨0, by omega⟩ = Fin.last (2 * r + k) := by
      apply Fin.ext; rw [ExponentialSlopeDerivatives.sg_val]; simp only [Fin.val_last]; split_ifs <;> omega
    have hst : star (Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) =
        (Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) := by
      funext i; simp [Pi.single_apply]
    rw [key _ hx, hst, single_dotProduct, one_mul, hpk_mulVec, hsg, if_neg (by simp; omega), hQe]

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap
