module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CcARatioZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Weighted
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem cns_data {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)),
      StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
      (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, h1, h2, h3, h4, -, h6, h7, h8⟩ := S7.psiAll ε lam h T hlam hh hq
  have hmax : thrStar ε < h := hth
  delta thrStar at hmax
  rw [max_lt_iff] at hmax
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ (n : ℝ) * S7.q0 ε := by positivity
  have hL2 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith [hmax.2]
  have hw2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith [hmax.2]
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hmax.1⟩
  have hP : IsPsiFor ε lam T Ψ := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 hL2⟩
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have := T.w_norm
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨m, hm⟩ := S7.exists_mu hlam
  refine ⟨T, Ψ, hgap, hP, hv₀, psi_exp_isPositive T Ψ m hm (h8 m hm), ?_, hasGelfandChar_sigLam hgap hP hv₀ h7⟩
  exact weighted_datum hgap hP hv₀ (fun μ hμ => (h6 μ hμ).2.2 2 (by norm_num) hw2)

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section Kfin

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem cns_gen_mem_Hlam {y : smD ε (rreg ε)} (hy : y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    (y : L2 ε) ∈ Hlam ε Ψ v₀ :=
  Submodule.le_topologicalClosure _ ⟨y, hy, rfl⟩

theorem cns_kfin (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {y : smD ε (rreg ε)}
    (hy : y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (x : Hlam ε Ψ v₀) (hx : (x : L2 ε) = y) :
    PI.UpqRep.IsKFin ε (sigLam ε Ψ v₀) x := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hE := hD.glRep
  have hV := datumV_isKIrrHW hP hv₀
  rw [genSub_eq_iSup_layer hE hV.2.1] at hy
  have hdir : Directed (· ≤ ·) (fun k => layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) k) :=
    fun i j => ⟨max i j, layer_mono (le_max_left i j), layer_mono (le_max_right i j)⟩
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
  set S0 := layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) k with hS0
  haveI hS0f : FiniteDimensional ℂ S0 := finiteDimensional_layer hV.1 k
  have hS0K := kStable_of_isKStableSub hσ hD S0 hS0f (layer_kStable hE hV.2.1 k)
  set S : Submodule ℂ (Hlam ε Ψ v₀) := (S0.map (smD ε (rreg ε)).subtype).comap (Hlam ε Ψ v₀).subtype with hS
  have hSf : FiniteDimensional ℂ S := by
    have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
    have hle : S.map (Hlam ε Ψ v₀).subtype ≤ S0.map (smD ε (rreg ε)).subtype := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    haveI : FiniteDimensional ℂ (S0.map (smD ε (rreg ε)).subtype) := Module.Finite.map _ _
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective _ hinj S).symm.finiteDimensional
  refine ⟨S, hSf, ⟨y, hk, hx.symm⟩, ?_⟩
  intro g hg v hv
  obtain ⟨u, hu, huv⟩ := hv
  have hgU : g ∈ UJset ε := cf_kset_sub hg
  obtain ⟨w, hw, hwe⟩ := hS0K g hg u hu
  refine ⟨w, hw, ?_⟩
  show (w : L2 ε) = ((sigLam ε Ψ v₀ g v : Hlam ε Ψ v₀) : L2 ε)
  rw [sigLam_coe hgap hP hv₀ hgU, hwe]
  simp only [Submodule.coe_subtype] at huv
  rw [huv]

end Kfin

section Term

variable {ε : Fin n → Bool}

theorem cns_term (dual : Bool) {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {h h' : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) (hh' : GapAtLeast ε lam' h') (hth' : thrStar ε < h')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε)))
    (hW' : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hG' : HasGelfandChar (smE ε (rreg ε)) lam' (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s)
    {f : Fin n → smD ε (rreg ε)} (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (he : eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f)
    {η : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ x z : Hlam ε Ψ' v₀', PI.UpqRep.IsKFin ε (sigLam ε Ψ' v₀') x ∧ PI.UpqRep.IsKFin ε (sigLam ε Ψ' v₀') z ∧
      ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((f d : smD ε (rreg ε)) : L2 ε)) c) =
        inner ℂ z (sigLam ε Ψ' v₀' g x) := by
  haveI := Hlam_nontrivial hgap hP hv₀
  haveI := Hlam_nontrivial hgap' hP' hv₀'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ v₀)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' v₀')
  obtain ⟨⟨ι, hι, -, hsurj⟩, -⟩ := cc_gk dual hgap hP hv₀ hgap' hP' hv₀' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s hlam' hw hw'
  obtain ⟨x', hx', rfl⟩ := hsurj f hf he
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨z, hz, hzeq⟩ := (coef_of_emb dual hσ hD hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) hgap' (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀')
    (datumV_kStable hP' v₀') hι).1 η hη x' hx'
  refine ⟨⟨(x' : L2 ε), cns_gen_mem_Hlam hx'⟩, ⟨(z : L2 ε), cns_gen_mem_Hlam hz⟩,
    cns_kfin hgap' hP' hv₀' hx' _ rfl, cns_kfin hgap' hP' hv₀' hz _ rfl, fun g hg => ?_⟩
  rw [hzeq g hg, Submodule.coe_inner, sigLam_coe hgap' hP' hv₀' hg]

end Term

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem cns_single_bd (s x : Fin n) : 0 ≤ (Pi.single s (1 : ℝ) : Fin n → ℝ) x ∧
    (Pi.single s (1 : ℝ) : Fin n → ℝ) x ≤ 1 := by
  by_cases h : x = s
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem cns_single_01 (s x : Fin n) : (Pi.single s (1 : ℝ) : Fin n → ℝ) x = 0 ∨
    (Pi.single s (1 : ℝ) : Fin n → ℝ) x = 1 := by
  by_cases h : x = s
  · right; subst h; simp
  · left; simp [Pi.single_eq_of_ne h]

theorem cns_shift_gap (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hh : GapAtLeast ε μ h)
    (s : Fin n) : GapAtLeast ε (shiftF dual μ s) (h - 1) := by
  intro a b hab
  have h0 := hh a b hab
  obtain ⟨a0, a1⟩ := cns_single_bd s a
  obtain ⟨b0, b1⟩ := cns_single_bd s b
  delta shiftF
  cases dual
  · simp only [Bool.cond_false, Pi.add_apply]
    have e : μ a + (Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ b + (Pi.single s (1 : ℝ) : Fin n → ℝ) b) =
        (μ a - μ b) - -((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) := by ring
    rw [e]
    have := abs_sub_abs_le_abs_sub (μ a - μ b)
      (-((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b))
    have hd : |-((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b)| ≤ 1 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  · simp only [Bool.cond_true, Pi.sub_apply]
    have e : μ a - (Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ b - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) =
        (μ a - μ b) - ((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) := by ring
    rw [e]
    have := abs_sub_abs_le_abs_sub (μ a - μ b)
      ((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b)
    have hd : |(Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b| ≤ 1 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith

theorem cns_sing (dual : Bool) {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) {s : Fin n}
    (hns : ¬ S7.IsHCParam (shiftF dual μ s)) : ¬ Function.Injective (shiftF dual μ s) := by
  intro hinj
  apply hns
  constructor
  · intro a b hab
    obtain ⟨ma, hma⟩ := hμ.2 a
    obtain ⟨mb, hmb⟩ := hμ.2 b
    have hlt := hμ.1 hab
    have h1 : μ b + 1 ≤ μ a := by
      have hz : mb < ma := by
        have : (mb : ℝ) < ma := by linarith
        exact_mod_cast this
      have hz' : mb + 1 ≤ ma := Int.add_one_le_iff.mpr hz
      have : ((mb + 1 : ℤ) : ℝ) ≤ (ma : ℝ) := by exact_mod_cast hz'
      push_cast at this
      linarith
    obtain ⟨a0, a1⟩ := cns_single_bd s a
    obtain ⟨b0, b1⟩ := cns_single_bd s b
    have hle : shiftF dual μ s b ≤ shiftF dual μ s a := by
      delta shiftF
      cases dual
      · simp only [Bool.cond_false, Pi.add_apply]; linarith
      · simp only [Bool.cond_true, Pi.sub_apply]; linarith
    exact lt_of_le_of_ne hle (fun e => hab.ne' (hinj e))
  · intro a
    delta shiftF
    obtain ⟨ma, hma⟩ := hμ.2 a
    rcases cns_single_01 s a with h0 | h0
    · refine ⟨ma, ?_⟩
      cases dual
      · simp only [Bool.cond_false, Pi.add_apply, h0]; linarith
      · simp only [Bool.cond_true, Pi.sub_apply, h0]; linarith
    · cases dual
      · refine ⟨ma + 1, ?_⟩
        simp only [Bool.cond_false, Pi.add_apply, h0]; push_cast; linarith
      · refine ⟨ma - 1, ?_⟩
        simp only [Bool.cond_true, Pi.sub_apply, h0]; push_cast; linarith

theorem cns_shift_inj (dual : Bool) (μ : Fin n → ℝ) {s s' : Fin n} (h : shiftF dual μ s = shiftF dual μ s') :
    s = s' := by
  by_contra hne
  have heval : shiftF dual μ s s = shiftF dual μ s' s := congrFun h s
  delta shiftF at heval
  cases dual
  · simp [Pi.single_apply, hne] at heval
  · simp [Pi.single_apply, hne] at heval

theorem cns_coefV {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (a b : H) (x y : Fin n → ℂ) :
    inner ℂ b (σ g a) * (star y ⬝ᵥ (g *ᵥ x)) =
      ∑ c, inner ℂ (y c • b) (tensGrp false σ g (fun d => x d • a) c) := by
  delta tensGrp
  simp only [Bool.cond_false, map_smul, smul_smul, inner_smul_left, inner_sum, inner_smul_right,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem cns_coefVd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (a b : H) (x y : Fin n → ℂ) :
    inner ℂ b (σ g a) * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) =
      ∑ c, inner ℂ (star (x c) • b) (tensGrp true σ g (fun d => star (y d) • a) c) := by
  delta tensGrp
  simp only [Bool.cond_true, map_smul, smul_smul, inner_smul_left, inner_sum, inner_smul_right,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def,
    Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem cns_single_coef (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    star (Pi.single c (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (g *ᵥ Pi.single d 1) = g c d := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem cns_expandV {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (f F : Fin n → H) :
    ∑ c, inner ℂ (f c) (tensGrp false σ g F c) = ∑ p : Fin n × Fin n, inner ℂ (f p.1) (σ g (F p.2)) *
      (star (Pi.single p.1 (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (g *ᵥ Pi.single p.2 1)) := by
  rw [Fintype.sum_prod_type]
  delta tensGrp
  simp only [Bool.cond_false, inner_sum, inner_smul_right, cns_single_coef]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem cns_expandVd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (f F : Fin n → H) :
    ∑ c, inner ℂ (f c) (tensGrp true σ g F c) = ∑ p : Fin n × Fin n, inner ℂ (f p.1) (σ g (F p.2)) *
      (star (Pi.single p.2 (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (g⁻¹ *ᵥ Pi.single p.1 1)) := by
  rw [Fintype.sum_prod_type]
  delta tensGrp
  simp only [Bool.cond_true, inner_sum, inner_smul_right, cns_single_coef]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem cns_tens_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (η : Fin n → H) {β : Type*} (B : Finset β) (F : β → Fin n → D) :
    ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => (((∑ b ∈ B, F b) d : D) : H)) c) =
      ∑ b ∈ B, ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => ((F b d : D) : H)) c) := by
  delta tensGrp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Submodule.coe_sum, map_sum, Finset.smul_sum, inner_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem cns_kfin_map {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] {ε : Fin n → Bool} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) {x : H₁} (hx : PI.UpqRep.IsKFin ε σ₁ x) :
    PI.UpqRep.IsKFin ε σ₂ (U x) := by
  obtain ⟨S, hSf, hxS, hSK⟩ := hx
  refine ⟨S.map U.toLinearIsometry.toLinearMap, Module.Finite.map _ _, ⟨x, hxS, rfl⟩, ?_⟩
  rintro g hg _ ⟨v, hv, rfl⟩
  exact ⟨σ₁ g v, hSK g hg v hv, hU g (cf_kset_sub hg) v⟩

theorem cns_symm_intertw {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] {ε : Fin n → Bool} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ g ∈ UJset ε, ∀ y, U.symm (σ₂ g y) = σ₁ g (U.symm y) := by
  intro g hg y
  have := hU g hg (U.symm y)
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  rw [← this, LinearIsometryEquiv.symm_apply_apply]

section abelian₂

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem cns_kfin_gen (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {x : Hlam ε Ψ v₀}
    (hx : PI.UpqRep.IsKFin ε (sigLam ε Ψ v₀) x) :
    ∃ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), (y : L2 ε) = x := by
  obtain ⟨S, hSf, hxS, hSK⟩ := hx
  have := sigLam_kfin hgap hP hv₀ S hSf hSK hxS
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 this)
  exact ⟨y, hy, hyx⟩

theorem cns_inner_tr (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ x, U (sigLam ε Ψ v₀ g x) = σ g (U x))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (a b : Hlam ε Ψ v₀) :
    inner ℂ (U b) (σ g (U a)) = inner ℂ (b : L2 ε) (rreg ε g (a : L2 ε)) := by
  rw [← hU g hg, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner, sigLam_coe hgap hP hv₀ hg]

end abelian₂

end ReciprocityTheory.ChartRestriction.DS
end
end
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

def cns_Ok (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  (∃ h : ℝ, GapAtLeast ε lam h ∧ thrStar ε < h) ∧ StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
    (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
    HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))

theorem cns_data' {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), cns_Ok ε lam T Ψ := by
  obtain ⟨T, Ψ, h1, h2, h3, h4, h5, h6⟩ := cns_data hq hlam hh hth
  exact ⟨T, Ψ, ⟨h, hh, hth⟩, h1, h2, h3, h4, h5, h6⟩

theorem cns_family (dual : Bool) {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hG : GapAtLeast ε μ h) (hth : thrStar ε + 1 < h) :
    ∃ (lamS : Fin n → Fin n → ℝ) (Ts : ∀ s, S7.KType ε (lowK ε (lamS s)))
      (Ψs : ∀ s, Matrix (Fin n) (Fin n) ℂ → ((Ts s).V →L[ℂ] (Ts s).V)),
      (∀ s, cns_Ok ε (lamS s) (Ts s) (Ψs s)) ∧
      ∀ s, S7.IsHCParam (shiftF dual μ s) → lamS s = shiftF dual μ s := by
  have hth0 : thrStar ε < h := by linarith
  have hdat : ∀ s, ∃ lam' : Fin n → ℝ, ∃ (T' : S7.KType ε (lowK ε lam'))
      (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), cns_Ok ε lam' T' Ψ' ∧
      (S7.IsHCParam (shiftF dual μ s) → lam' = shiftF dual μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF dual μ s)
    · obtain ⟨T', Ψ', hok⟩ := cns_data' hq hs (cns_shift_gap dual hG s) (by linarith)
      exact ⟨_, T', Ψ', hok, fun _ => rfl⟩
    · obtain ⟨T', Ψ', hok⟩ := cns_data' hq hμ hG hth0
      exact ⟨μ, T', Ψ', hok, fun h' => absurd h' hs⟩
  choose lamS Ts Ψs hS hsh using hdat
  exact ⟨lamS, Ts, Ψs, hS, hsh⟩

theorem cns_pole (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ)
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε μ) (hP : IsPsiFor ε μ T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) μ (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    {z : ℂ} {f : Fin n → smD ε (rreg ε)} (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf0 : f ≠ 0) (he : eeF dual (smE ε (rreg ε)) f = z • f) :
    ∃ s, S7.IsHCParam (shiftF dual μ s) ∧ z = poleF dual μ s := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  obtain ⟨s, rfl⟩ := (pole_match dual hσ hD hsm hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) hW hG).1 z f hf hf0 he
  refine ⟨s, ?_, rfl⟩
  by_contra hns
  exact hf0 (cc_gk_singular dual hσ hD hsm hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) hW hG s (cns_sing dual hμ hns) f hf he)

theorem cns_toSum_core (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ)
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hok : cns_Ok ε μ T Ψ)
    (lamS : Fin n → Fin n → ℝ) (Ts : ∀ s, S7.KType ε (lowK ε (lamS s)))
    (Ψs : ∀ s, Matrix (Fin n) (Fin n) ℂ → ((Ts s).V →L[ℂ] (Ts s).V))
    (hS : ∀ s, cns_Ok ε (lamS s) (Ts s) (Ψs s))
    (hsh : ∀ s, S7.IsHCParam (shiftF dual μ s) → lamS s = shiftF dual μ s)
    {η f : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))) :
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hlam ε (Ψs (sI i)) (Ts (sI i)).w),
      (∀ i, S7.IsHCParam (shiftF dual μ (sI i)) ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs (sI i)) (Ts (sI i)).w) (vI i) ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs (sI i)) (Ts (sI i)).w) (wI i)) ∧
      ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((f d : smD ε (rreg ε)) : L2 ε)) c) =
        ∑ i, inner ℂ (wI i) (sigLam ε (Ψs (sI i)) (Ts (sI i)).w g (vI i)) := by
  classical
  obtain ⟨⟨h0, hh0, hth0⟩, hgap, hP, hv, hpos, hW, hG⟩ := hok
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨B, hdec, -⟩ := ee_decomp dual hσ hD hgap (datumV_isKIrrHW hP hv) (datumV_casimir hP T.w)
    (datumV_kStable hP T.w) hW
  obtain ⟨fb, hfb, rfl⟩ := hdec f hf
  have hcomp : ∀ i : {b // b ∈ B.filter (fun b => fb b ≠ 0)}, ∃ s, S7.IsHCParam (shiftF dual μ s) ∧
      ∃ x z : Hlam ε (Ψs s) (Ts s).w, PI.UpqRep.IsKFin ε (sigLam ε (Ψs s) (Ts s).w) x ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs s) (Ts s).w) z ∧
        ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((fb i d : smD ε (rreg ε)) : L2 ε)) c) =
          inner ℂ z (sigLam ε (Ψs s) (Ts s).w g x) := by
    intro i
    have hi := (Finset.mem_filter.1 i.2).2
    obtain ⟨s, hs, hz⟩ := cns_pole dual hμ hgap hP hv hW hG (hfb i).1 hi (hfb i).2
    obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hS s
    have he : eeF dual (smE ε (rreg ε)) (fb i) = poleF dual μ s • fb i := by rw [(hfb i).2, hz]
    exact ⟨s, hs, cns_term dual hgap hP hv hgap' hP' hv' hh0 hth0 hh' hth' hpos hpos' hW hW' hG hG' s
      (hsh s hs) (hfb i).1 he hη⟩
  choose sI hsI xI zI hx hz hEq using hcomp
  refine ⟨{b // b ∈ B.filter (fun b => fb b ≠ 0)}, inferInstance, sI, xI, zI,
    fun i => ⟨hsI i, hx i, hz i⟩, fun g hg => ?_⟩
  have h0 : ∀ b ∈ B, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
      (tensGrp dual (rreg ε) g (fun d => ((fb b d : smD ε (rreg ε)) : L2 ε)) c) ≠ 0 → fb b ≠ 0 := by
    intro b _ hne hb
    apply hne
    delta tensGrp
    simp [hb]
  rw [cns_tens_sum, ← Finset.sum_filter_of_ne h0, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun i _ => hEq i g hg

theorem cns_ofSum_core (dual : Bool) {ε : Fin n → Bool} {μ lam' : Fin n → ℝ}
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hok : cns_Ok ε μ T Ψ)
    {T' : S7.KType ε (lowK ε lam')} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hok' : cns_Ok ε lam' T' Ψ') (s : Fin n) (hlam' : lam' = shiftF dual μ s) {x' z' : smD ε (rreg ε)}
    (hx' : x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' T'.w))
    (hz' : z' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' T'.w)) :
    ∃ f F : Fin n → smD ε (rreg ε), f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) ∧
      F ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) ∧
      ∀ g ∈ UJset ε, inner ℂ ((z' : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x' : smD ε (rreg ε)) : L2 ε)) =
        ∑ c, inner ℂ ((f c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((F d : smD ε (rreg ε)) : L2 ε)) c) := by
  obtain ⟨⟨h, hh, hth⟩, hgap, hP, hv, hpos, hW, hG⟩ := hok
  obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hok'
  haveI := Hlam_nontrivial hgap hP hv
  haveI := Hlam_nontrivial hgap' hP' hv'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ T.w)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  obtain ⟨⟨ι, hι, -, -⟩, -⟩ := cc_gk dual hgap hP hv hgap' hP' hv' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s hlam' hw hw'
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨f, hf, hfe⟩ := (coef_of_emb dual hσ hD hgap (datumV_isKIrrHW hP hv) (datumV_casimir hP T.w)
    (datumV_kStable hP T.w) hgap' (datumV_isKIrrHW hP' hv') (datumV_casimir hP' T'.w)
    (datumV_kStable hP' T'.w) hι).2 z' hz' x' hx'
  exact ⟨f, ι x', hf, hι.1 x' hx', hfe⟩

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem cns_zuck_nc {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) {h : ℝ} (hG : PI.ZuckTensor.GapAtLeast ε μ h)
    (hth : thrStar ε + 1 < h) :
    ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) := by
  classical
  have hμ' : S7.IsHCParam μ := hμ
  have hG' : GapAtLeast ε μ h := hG
  obtain ⟨T, Ψ, hok⟩ := cns_data' hq hμ' hG' (by linarith)
  obtain ⟨lamS, Ts, Ψs, hS, hsh⟩ := cns_family false hq hμ' hG' hth
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hd hok.2.1 hok.2.2.1 hok.2.2.2.1
  have hU' := cns_symm_intertw U hU
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF false μ s))
            Hs := fun s => Hlam ε (Ψs s) (Ts s).w
            σs := fun s => sigLam ε (Ψs s) (Ts s).w
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ + Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact isDS_sigLam (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    have e := sigLam_inj (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 (hS s').2.1 (hS s').2.2.1 (hS s').2.2.2.1 V hV
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e
    exact cns_shift_inj false μ e
  · intro v w x y hv hw
    obtain ⟨a, ha, hav⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hv)
    obtain ⟨b, hb, hbw⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hw)
    obtain ⟨ι, hι, sI, vI, wI, hI, hEq⟩ := cns_toSum_core false hμ' hok lamS Ts Ψs hS hsh
      (η := fun c => y c • b) (f := fun d => x d • a)
      (tset_mem.2 fun c => Submodule.smul_mem _ _ hb) (tset_mem.2 fun d => Submodule.smul_mem _ _ ha)
    refine ⟨ι, hι, sI, vI, wI, fun i => ⟨mem_filter.2 ⟨mem_univ _, (hI i).1⟩, (hI i).2.1, (hI i).2.2⟩,
      fun g hg => ?_⟩
    rw [← hEq g hg]
    simp only [Submodule.coe_smul]
    rw [← cns_coefV (rreg ε) g (a : L2 ε) (b : L2 ε) x y, ← U.apply_symm_apply v, ← U.apply_symm_apply w,
      cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg, ← hav, ← hbw]
  · intro s hs v w hv hw
    have hs' := (mem_filter.1 hs).2
    obtain ⟨x', hx', hxv⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hv
    obtain ⟨z', hz', hzw⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hw
    obtain ⟨f, F, hf, hF, hfe⟩ := cns_ofSum_core false hok (hS s) s (hsh s hs') hx' hz'
    have hfm := tset_mem.1 hf
    have hFm := tset_mem.1 hF
    refine ⟨Fin n × Fin n, inferInstance,
      fun p => U ⟨((F p.2 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hFm p.2)⟩,
      fun p => U ⟨((f p.1 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hfm p.1)⟩,
      fun p => Pi.single p.2 1, fun p => Pi.single p.1 1,
      fun p => ⟨cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hFm p.2) _ rfl),
        cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hfm p.1) _ rfl)⟩, fun g hg => ?_⟩
    dsimp only
    rw [Submodule.coe_inner, sigLam_coe (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hg, ← hxv, ← hzw, hfe g hg,
      cns_expandV]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

theorem cns_zuckd_nc {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) {h : ℝ} (hG : PI.ZuckTensor.GapAtLeast ε μ h)
    (hth : thrStar ε + 1 < h) :
    ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) := by
  classical
  have hμ' : S7.IsHCParam μ := hμ
  have hG' : GapAtLeast ε μ h := hG
  obtain ⟨T, Ψ, hok⟩ := cns_data' hq hμ' hG' (by linarith)
  obtain ⟨lamS, Ts, Ψs, hS, hsh⟩ := cns_family true hq hμ' hG' hth
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hd hok.2.1 hok.2.2.1 hok.2.2.2.1
  have hU' := cns_symm_intertw U hU
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF true μ s))
            Hs := fun s => Hlam ε (Ψs s) (Ts s).w
            σs := fun s => sigLam ε (Ψs s) (Ts s).w
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ - Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact isDS_sigLam (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    have e := sigLam_inj (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 (hS s').2.1 (hS s').2.2.1 (hS s').2.2.2.1 V hV
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e
    exact cns_shift_inj true μ e
  · intro v w x y hv hw
    obtain ⟨a, ha, hav⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hv)
    obtain ⟨b, hb, hbw⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hw)
    obtain ⟨ι, hι, sI, vI, wI, hI, hEq⟩ := cns_toSum_core true hμ' hok lamS Ts Ψs hS hsh
      (η := fun c => star (x c) • b) (f := fun d => star (y d) • a)
      (tset_mem.2 fun c => Submodule.smul_mem _ _ hb) (tset_mem.2 fun d => Submodule.smul_mem _ _ ha)
    refine ⟨ι, hι, sI, vI, wI, fun i => ⟨mem_filter.2 ⟨mem_univ _, (hI i).1⟩, (hI i).2.1, (hI i).2.2⟩,
      fun g hg => ?_⟩
    rw [← hEq g hg]
    simp only [Submodule.coe_smul]
    rw [← cns_coefVd (rreg ε) g (a : L2 ε) (b : L2 ε) x y, ← U.apply_symm_apply v, ← U.apply_symm_apply w,
      cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg, ← hav, ← hbw]
  · intro s hs v w hv hw
    have hs' := (mem_filter.1 hs).2
    obtain ⟨x', hx', hxv⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hv
    obtain ⟨z', hz', hzw⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hw
    obtain ⟨f, F, hf, hF, hfe⟩ := cns_ofSum_core true hok (hS s) s (hsh s hs') hx' hz'
    have hfm := tset_mem.1 hf
    have hFm := tset_mem.1 hF
    refine ⟨Fin n × Fin n, inferInstance,
      fun p => U ⟨((F p.2 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hFm p.2)⟩,
      fun p => U ⟨((f p.1 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hfm p.1)⟩,
      fun p => Pi.single p.1 1, fun p => Pi.single p.2 1,
      fun p => ⟨cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hFm p.2) _ rfl),
        cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hfm p.1) _ rfl)⟩, fun g hg => ?_⟩
    dsimp only
    rw [Submodule.coe_inner, sigLam_coe (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hg, ← hxv, ← hzw, hfe g hg,
      cns_expandVd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

end ReciprocityTheory.ChartRestriction.DS
