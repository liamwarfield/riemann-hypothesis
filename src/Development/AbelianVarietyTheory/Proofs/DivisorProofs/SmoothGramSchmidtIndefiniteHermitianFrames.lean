module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
noncomputable section

open Matrix GlobalTheory.HolDict ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open scoped ContDiff

namespace GlobalTheory.HolDict.GS

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem contDiffOn_det {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) : ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hf _ _

theorem contDiffOn_minv {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, (f x).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((contDiffOn_det f hf).inv hd).mul (contDiffOn_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem contDiffOn_mmul {m : Type} [Fintype m] (f g : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x * g x) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

theorem contDiffOn_Lm {n : ℕ} (f : E → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, ∀ k, lminor (f x) k ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => Lm (f x) i j) s := by
  simp only [Lm, Matrix.of_apply]
  split_ifs with h1 h2
  · refine ContDiffOn.neg ?_
    simp only [wv, vecMul, dotProduct]
    refine ContDiffOn.sum fun k _ => (hf _ _).mul ?_
    exact contDiffOn_minv (fun x => lb (f x) i) (fun a b => hf _ _) (fun x hx => hd x hx (Fin.castSucc i)) _ _
  · exact contDiffOn_const
  · exact contDiffOn_const

end Smooth

variable {n : ℕ}

theorem Lm_conj_diag (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) :
    Lm A * A * (Lm A)ᴴ = diagonal fun a => (Lm A * A) a a := by
  have hU : (Lm A * A).BlockTriangular id := fun a c h => Lm_mul_up A hM a c h
  have hL : ((Lm A)ᴴ).BlockTriangular id := fun a c h => by
    rw [conjTranspose_apply, Lm_up A c a h, star_zero]
  have hD := hU.mul hL
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  ext a c
  rcases lt_trichotomy a c with h | h | h
  · rw [diagonal_apply_ne _ h.ne, ← hH, conjTranspose_apply, hD (show id a < id c from h), star_zero]
  · subst h
    rw [diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [conjTranspose_apply, Lm_diag, star_one, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hU (show id b < id a from h), zero_mul]
      · rw [hL (show id a < id b from h), mul_zero]
    · simp
  · rw [diagonal_apply_ne _ h.ne', hD (show id c < id a from h)]

theorem lminor_succ (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    lminor A a.succ = lminor A a.castSucc * (Lm A * A) a a := by
  have key : ∀ i : Fin (n + 1), lminor A i = ∏ j : Fin i, (Lm A * A) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have hN : ((Lm A)ᵀ).BlockTriangular id := fun a c h => Lm_up A c a h
    have h1 := FrameDegreeData.lminor_conj (A := A) hN i
    have h2 : (Lm A)ᵀᵀ * A * ((Lm A)ᵀ).map (starRingEnd ℂ) = Lm A * A * (Lm A)ᴴ := rfl
    rw [h2, Lm_conj_diag A hA hM] at h1
    simp only [transpose_apply, Lm_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
    rw [← h1, lminor, FrameDegreeData.det_sub_upper _ (blockTriangular_diagonal _)]
    simp only [diagonal_apply_eq]
  rw [key, key]
  exact Fin.prod_univ_castSucc (n := a) _

theorem diag_real (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    (((Lm A * A) a a).re : ℂ) = (Lm A * A) a a := by
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  rw [Lm_conj_diag A hA hM] at hH
  have := congrFun (congrFun hH a) a
  rw [conjTranspose_apply, diagonal_apply_eq] at this
  exact Complex.conj_eq_iff_re.mp this

theorem minor_ne {q : ℕ} {A : Mt n} (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) (k : Fin (n + 1)) :
    lminor A k ≠ 0 := fun h0 => by
  have := h k
  rw [h0] at this
  simp at this

theorem diag_pos {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re)
    (a : Fin n) : 0 < sgn q a * ((Lm A * A) a a).re := by
  have h1 := h a.succ
  have h2 := h a.castSucc
  rw [lminor_succ A hA (minor_ne h) a, ← diag_real A hA (minor_ne h) a, Complex.re_mul_ofReal] at h1
  simp only [Fin.val_succ, psgn, Finset.prod_range_succ, Fin.val_castSucc] at h1 h2
  have e : (∏ x ∈ Finset.range a, sgn q x) * sgn q a * ((lminor A a.castSucc).re * ((Lm A * A) a a).re) =
      ((∏ x ∈ Finset.range a, sgn q x) * (lminor A a.castSucc).re) * (sgn q a * ((Lm A * A) a a).re) := by ring
  rw [e] at h1
  exact (pos_iff_pos_of_mul_pos h1).mp h2

def fac (q : ℕ) (A : Mt n) : Mt n :=
  diagonal (fun a : Fin n => (((Real.sqrt (sgn q a * ((Lm A * A) a a).re))⁻¹ : ℝ) : ℂ)) * (Lm A * A)

theorem fac_spec {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) :
    UpT (fac q A) ∧ ((fac q A)⁻¹)ᴴ * A * (fac q A)⁻¹ = diagonal fun a : Fin n => ((sgn q a : ℝ) : ℂ) := by
  set d : Fin n → ℝ := fun a => ((Lm A * A) a a).re with hd
  set r : Fin n → ℝ := fun a : Fin n => Real.sqrt (sgn q a * d a) with hr
  have hpos : ∀ a : Fin n, 0 < sgn q a * d a := diag_pos A hA h
  have hr0 : ∀ a, r a ≠ 0 := fun a => (Real.sqrt_pos.mpr (hpos a)).ne'
  have hr2 : ∀ a : Fin n, r a * r a = sgn q a * d a := fun a => Real.mul_self_sqrt (hpos a).le
  have hd0 : ∀ a, d a ≠ 0 := fun a h0 => by have := hpos a; rw [h0] at this; simp at this
  have hD : Lm A * A * (Lm A)ᴴ = diagonal fun a => (d a : ℂ) := by
    rw [Lm_conj_diag A hA (minor_ne h)]
    congr 1
    funext a
    exact (diag_real A hA (minor_ne h) a).symm
  have hone : fac q A * ((Lm A)ᴴ * diagonal fun a => ((r a / d a : ℝ) : ℂ)) = 1 := by
    rw [fac, Matrix.mul_assoc, ← Matrix.mul_assoc (Lm A * A), hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    have h1 := hr0 a
    have h2 := hd0 a
    change (((r a)⁻¹ : ℝ) : ℂ) * _ = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  refine ⟨⟨(Matrix.isUnit_det_of_right_inverse hone).ne_zero, fun a c hc => ?_⟩, ?_⟩
  · rw [fac, diagonal_mul, Lm_mul_up A (minor_ne h) a c hc, mul_zero]
  · rw [Matrix.inv_eq_right_inv hone, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    have e : ∀ X Y : Mt n, X * Lm A * A * ((Lm A)ᴴ * Y) = X * (Lm A * A * (Lm A)ᴴ) * Y := fun X Y => by
      simp only [Matrix.mul_assoc]
    rw [e, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    have h2 := hd0 a
    have h3 := hr2 a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    linear_combination h3

theorem contDiffOn_fac {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (q : ℕ) (f : E → Mt n)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hA : ∀ x ∈ s, (f x)ᴴ = f x)
    (h : ∀ x ∈ s, ∀ i : Fin (n + 1), 0 < psgn q i * (lminor (f x) i).re) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fac q (f x) i j) s := by
  have hU := contDiffOn_mmul (fun x => Lm (f x)) f
    (contDiffOn_Lm f hf fun x hx => minor_ne (h x hx)) hf
  simp only [fac, diagonal_mul]
  refine ContDiffOn.mul ?_ (hU i j)
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn
    (f := fun x => (Real.sqrt (sgn q i * ((Lm (f x) * f x) i i).re))⁻¹) ?_
  refine ContDiffOn.inv (ContDiffOn.sqrt (contDiffOn_const.mul
    (Complex.reCLM.contDiff.comp_contDiffOn (hU i i))) fun x hx => (diag_pos _ (hA x hx) (h x hx) i).ne')
    fun x hx => (Real.sqrt_pos.mpr (diag_pos _ (hA x hx) (h x hx) i)).ne'

theorem smooth_gramSchmidt : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ →
    ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧
      ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧
        Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  intro n Hm q x₀ ⟨_, h0⟩
  have hdet : IsUnit x₀.det := by
    have := congrArg Matrix.det h0
    rw [det_mul, det_diagonal] at this
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    rw [hz, mul_zero] at this
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_) this.symm
    unfold sgn
    split_ifs <;> simp
  have hHm : ∀ X : Mt n, X = x₀ᴴ * Hm * x₀ → (x₀⁻¹)ᴴ * X * x₀⁻¹ = Hm := by
    rintro X rfl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv _ hdet, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hH : Hmᴴ = Hm := by
    rw [← hHm _ h0.symm]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    ext a
    simp [sgn]
  have hA : ∀ x : Mt n, (-(xᴴ * Hm * x))ᴴ = -(xᴴ * Hm * x) := fun x => by
    simp only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  refine ⟨fun x i j => fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)) i j, ?_, fun x hx => ?_⟩
  · refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    refine contDiffOn_fac q (fun x => -((Matrix.of x)ᴴ * Hm * Matrix.of x)) (fun a b => ?_) (fun x _ => hA _)
      (fun x (hx : Matrix.of x ∈ frDom Hm q) => hx.2) i j
    simp only [Matrix.neg_apply]
    have hx : ∀ a b : Fin n, ContDiff ℝ ∞ fun x : Fin n → Fin n → ℂ => x a b := fun a b => by fun_prop
    refine (contDiffOn_mmul _ _ (contDiffOn_mmul _ (fun _ => Hm) (fun a b => ?_) fun _ _ => contDiffOn_const)
      (fun a b => (hx a b).contDiffOn) a b).neg
    exact (Complex.conjCLE.contDiff.comp (hx b a)).contDiffOn
  · obtain ⟨h1, h2⟩ := fac_spec _ (hA (Matrix.of x)) hx.2
    refine ⟨h1, ?_⟩
    change (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹)ᴴ * Hm *
      (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹) = Hm
    generalize (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ = γ at h2 ⊢
    have h3 : γᴴ * ((Matrix.of x)ᴴ * Hm * Matrix.of x) * γ = x₀ᴴ * Hm * x₀ := by
      rw [h0, ← diagonal_neg, ← h2]
      simp
    refine Eq.trans ?_ (hHm _ h3)
    simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HolDict.GS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFramesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_gram_schmidt_indefinite_hermitian_frames : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧ ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧ Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  first | exact @GlobalTheory.HolDict.GS.smooth_gramSchmidt | exact GlobalTheory.HolDict.GS.smooth_gramSchmidt | (intros; apply GlobalTheory.HolDict.GS.smooth_gramSchmidt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000

namespace GlobalTheory.LevActInt

theorem fromTest_moved {K : Type} [Field K] {ιB : Type}
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
    {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}
    (hL : ActLaws pts mapR borR actR) (g : G) {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : FromTest pts mapR (mvPt pts actR g y) := by
  obtain ⟨p, φ, z, hz⟩ := hy
  exact ⟨p, φ, _, hL.nat g _ S φ z _ y _ hz (mvPt_spec hL.total g z) (mvPt_spec hL.total g y)⟩

theorem intAll_actLev : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g (f f' : Cu T κ i), (f' : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) → Formalism.IndefR.FWT.IntAll T κ f → Formalism.IndefR.FWT.IntAll T κ f' := by
  intro D G _ T κ i lev h hL g f f' hf hF
  have hj := inR (D := D) i
  have hnat := ((mem_cusp _ _ _ _ _ _).1 f.2).1.1
  rintro la ⟨_, ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total g y.1
  let y' : IntFr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c S io :=
    ⟨_, fromTest_moved hL g y.2.1,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (lev g) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' f.1) := hF la ⟨_, ⟨PtV.mk la ho y' hy () trivial, rfl⟩⟩
  have e1 : evI y f'.1 = evI y' f.1 := by
    rw [hf]
    exact evalAt_actL hL (h.evalWD _ hj) frMap_trans_id g hnat y.1
  show 0 ≤ nval S.V e (evI y f'.1)
  rw [e1]
  exact h0

end GlobalTheory.LevActInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspFormsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_action_preserves_integral_cusp_forms : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g (f f' : Cu T κ i), (f' : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) → Formalism.IndefR.FWT.IntAll T κ f → Formalism.IndefR.FWT.IntAll T κ f' := by
  first | exact @GlobalTheory.LevActInt.intAll_actLev | exact GlobalTheory.LevActInt.intAll_actLev | (intros; apply GlobalTheory.LevActInt.intAll_actLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjoint
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecCalc

theorem smooth_calculus : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  intro n H _ _ J π _ hJ hπ v hv
  have hG : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have hv' : v ∈ GlobalTheory.SmVec.smSub J π := hv
  refine ⟨fun g hg => GlobalTheory.SmVec.rep_mem hG hπ hv' hg, fun w hw c => ?_, fun X hX => ?_⟩
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    exact add_mem hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw')
  have hX' : X ∈ GlobalTheory.SmVec.lieG J := hX
  have hD := GlobalTheory.SmVec.hasDerivAt_dRep hv' hX'
  refine ⟨GlobalTheory.SmVec.dRep_mem hG hπ hv' hX', hD, fun g hg => ?_, fun c => ?_, fun w hw => ⟨?_, fun c => ?_⟩⟩
  · have hd := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
    have hY : g * X * g⁻¹ ∈ GlobalTheory.SmVec.lieG J := by
      have := GlobalTheory.SmVec.conj_mem_lieG hG (GlobalTheory.SmVec.inv_mem_UH hG hg) hX'
      rwa [Matrix.nonsing_inv_nonsing_inv _ hd] at this
    rw [GlobalTheory.SmVec.dRep_rep hG hπ hv' hg hY]
    congr 2
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  · have h1 : HasDerivAt (fun t : ℝ => t * c) c 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    have h2 := HasDerivAt.scomp_of_eq (0 : ℝ) hD h1 (by simp)
    rw [Complex.coe_smul]
    refine Eq.trans ?_ h2.deriv
    unfold dRep
    congr 1
    funext t
    simp [Function.comp_def, smul_smul]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.inner_dRep hG hπ hv' hw' hX', neg_neg]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.dRep_add hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw') hX', GlobalTheory.SmVec.dRep_smul c hw' hX']

end GlobalTheory.SmVecCalc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjointStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  first | exact @GlobalTheory.SmVecCalc.smooth_calculus | exact GlobalTheory.SmVecCalc.smooth_calculus | (intros; apply GlobalTheory.SmVecCalc.smooth_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LevelRows3

theorem eel_eq_typeSp3 : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toCx3 F).EEl false = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P0 F.ψ0 ∧ (R.toCx3 F).EEl true = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P1 F.ψ1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have key : GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R.toRealDat F.lv2 :=
    GlobalTheory.LevelRows.rowsOfLevel_of_models R.toRealDat F.lv2 h.base.models.HE h.base.models.gE
  have aux : ∀ (b : Bool) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      (∀ x : R.HE.H, R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) ↔
        ∀ g : P, R.gE (g : G) x = D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • x) →
      (R.toCx3 F).EEl b = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
    intro b P ψ hx
    ext x
    simp only [typeSp3, Submodule.mem_iInf, LinearMap.mem_ker]
    refine Iff.trans (hx x) (forall_congr' fun g => ?_)
    rw [LinearMap.sub_apply, sub_eq_zero]
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    have e : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((ψ g : D.what₂.LLˣ) : D.what₂.LL)) =
        D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) := by
      simp only [R.emb0, cj_cj]
    have e' : A3.A.fam.v0.embedding ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • x =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
      rw [← e]
      rfl
    rw [e']
    exact Iff.rfl
  exact ⟨aux false _ _ (key false), aux true _ _ (key true)⟩

end GlobalTheory.LevelRows3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_rows_eq_type_vectors_of_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toCx3 F).EEl false = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P0 F.ψ0 ∧ (R.toCx3 F).EEl true = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P1 F.ψ1 := by
  first | exact @GlobalTheory.LevelRows3.eel_eq_typeSp3 | exact GlobalTheory.LevelRows3.eel_eq_typeSp3 | (intros; apply GlobalTheory.LevelRows3.eel_eq_typeSp3 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Northcott

theorem isIntegral_eig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsIntegral ℤ M) {w : ℂ}
    {x : Fin n → ℂ} (hx : x ≠ 0) (hMx : M *ᵥ x = w • x) : IsIntegral ℤ w := by
  obtain ⟨q, hq, hqM⟩ := hM
  refine ⟨q, hq, ?_⟩
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) w x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMx), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap ℤ ℂ)) hv
  have h2 : Polynomial.aeval (Matrix.toLin' M) (q.map (algebraMap ℤ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have e := Polynomial.aeval_algHom_apply
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.restrictScalars ℤ) M q
    have e2 : Polynomial.aeval M q = 0 := hqM
    rw [e2, map_zero] at e
    exact e
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := (smul_eq_zero.1 h1.symm).resolve_right hx
  rwa [Polynomial.eval_map] at h3

theorem norm_le_of_isIntegral_inv (w : ℂ) (c : ℚ) (N : ℕ) (hN : 0 < N) (hw : ‖w‖ ^ 2 = (c : ℝ))
    (hc : (c : ℝ) ≠ 0) (hI : IsIntegral ℤ ((N : ℂ) * w⁻¹)) : ‖w‖ ≤ N := by
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne (hw ▸ sq_nonneg _) (Ne.symm hc)
  have hconj : IsIntegral ℤ (starRingEnd ℂ ((N : ℂ) * w⁻¹)) := hI.map (starRingEnd ℂ).toIntAlgHom
  have hprod := hI.mul hconj
  have e : (N : ℂ) * w⁻¹ * starRingEnd ℂ ((N : ℂ) * w⁻¹) = (((N : ℚ) ^ 2 / c : ℚ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_inv, mul_pow, inv_pow, hw,
      Complex.norm_natCast]
    push_cast
    ring
  rw [e] at hprod
  have hq : IsIntegral ℤ ((N : ℚ) ^ 2 / c) := by
    refine (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective
      (x := (N : ℚ) ^ 2 / c)).1 ?_
    simpa using hprod
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  have hcq : (0 : ℚ) < c := by exact_mod_cast hcpos
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) ^ 2 / c := by positivity
  have hk1 : (1 : ℚ) ≤ (N : ℚ) ^ 2 / c := by
    rw [← hk] at hpos ⊢
    rw [algebraMap_int_eq, eq_intCast] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ k := this
    exact_mod_cast this
  have hcN : (c : ℚ) ≤ (N : ℚ) ^ 2 := by rwa [le_div_iff₀ hcq, one_mul] at hk1
  have hcN' : (c : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcN
  rw [← hw] at hcN'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hcN'

end GlobalTheory.LKMid.Northcott
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory

theorem encard_fibre_eq_encard_ringHom : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U →
    IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U),
    (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard =
      {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  intro k _ X Y p q π hπ U hU hV σ y hy
  have hmem : ∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z = y →
      z ∈ CxPts.ptsIn q σ (π ⁻¹ᵁ U) := by
    intro z hz
    have : PtsOver.map π hπ (spMap σ) z ∈ CxPts.ptsIn p σ U := hz ▸ hy
    exact this
  have hcomp : ∀ (z : CxPts q σ) (hz : PtsOver.map π hπ (spMap σ) z = y) (f : Γ(X, U)),
      CxPts.evHom (hmem z hz) ((π.app U).hom f) = CxPts.evHom hy f := by
    intro z hz f
    rw [← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_app π hπ U f z, hz]
  apply Set.encard_congr
  refine Equiv.ofBijective (fun z => ⟨CxPts.evHom (hmem z.1 z.2), RingHom.ext (hcomp z.1 z.2)⟩)
    ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    have h' : CxPts.evHom (hmem z hz) = CxPts.evHom (hmem w hw) := congrArg Subtype.val h
    refine Subtype.ext (Subtype.ext (ext_of_valR hV (hmem z hz) (hmem w hw) fun f => ?_))
    rw [valR_eq _ _ (hmem z hz), valR_eq _ _ (hmem w hw)]
    exact congrArg (fun φ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ => φ f) h'
  · rintro ⟨ψ, hψ⟩
    have hψ' : ∀ f, ψ ((π.app U).hom f) = CxPts.evHom hy f := fun f => by
      rw [← RingHom.comp_apply, hψ]
    have h₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U) :=
      le_preimage_specMap_fromSpec hV (CommRingCat.ofHom ψ)
    have hv : valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) h₀ =
        CommRingCat.ofHom ψ :=
      valMap_specMap_fromSpec hV (CommRingCat.ofHom ψ) h₀
    have e : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ π = y.1 := by
      refine ext_of_valR hU h₀ hy fun f => ?_
      rw [valR_comp, valR_eq _ _ h₀, hv, valR_eq _ _ hy]
      exact hψ' f
    let z : CxPts q σ := ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, by
      rw [← hπ, ← Category.assoc, e, y.2]⟩
    have hz : PtsOver.map π hπ (spMap σ) z = y := Subtype.ext e
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change (valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) (hmem z hz)).hom = ψ
    rw [hv]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensionsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_complexPointFibre_eq_encard_ringHom_extensions : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U), (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  first | exact @GlobalTheory.encard_fibre_eq_encard_ringHom | exact GlobalTheory.encard_fibre_eq_encard_ringHom | (intros; apply GlobalTheory.encard_fibre_eq_encard_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPlaceActionInjective
open scoped TensorProduct

namespace GlobalTheory.FactorKernel

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def contrML (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (ι → V) →ₘₗ[ℂ] V where
  toFun x := (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀
  map_update_add' := by
    intro inst x i a b
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_add]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c a
    obtain rfl : inst = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_comm c]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul, mul_assoc, smul_smul]

noncomputable def contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (⨂[ℂ] _ : ι, V) →ₗ[ℂ] V :=
  PiTensorProduct.lift (contrML w₀ μ)

theorem contr_tprod (w₀ : ι) (μ : ι → Module.Dual ℂ V) (x : ι → V) :
    contr w₀ μ (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀ := by
  rw [contr, PiTensorProduct.lift.tprod]; rfl

theorem dual_contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) (ν : Module.Dual ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    ν (contr w₀ μ T) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update μ w₀ ν)) T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem contr_atPl (w₀ : ι) (μ : ι → Module.Dual ℂ V) (L : Module.End ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    contr w₀ μ (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ L T) = L (contr w₀ μ T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, contr_tprod, contr_tprod,
      map_smul, Function.update_self, L.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.FactorKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaConjUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramCharUnique

theorem eq_one_of_loc {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

theorem loc_parts {D : D7} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (k : D.host.E)
    (hk : P.valuation D.host.E k ≤ 1) : infPart D (locE D e k) = 1 ∧ finPart D (locE D e k) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), (hint _).2 fun Q => ?_⟩
  have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := hι k
  have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (algebraMap D.host.E _ k - 1) := by
    rw [← h4]
    exact HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel, GlobalTheory.CharLocProd.val_algebraMap]
    exact hk
  · rw [h3 Q hQ, zero_mul, add_zero, map_one]

noncomputable def locHom {D : D7} {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun k => locE D e (k : D.host.E)
      map_one' := by simp [locE]
      map_mul' := fun k l => (locE_mul_locE he k l).symm }

theorem eq_one_of_unif {D : D7} {c : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) (hu : UnramEverywhere D c)
    (h : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ x : (AE D)ˣ,
      (x : AE D) = locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) → c x = 1) (x : (AE D)ˣ) : c x = 1 := by
  refine eq_one_of_loc ⟨hc, fun P e he k y hy => ?_⟩ x
  obtain rfl : y = locHom he.1 k := Units.ext hy
  have hπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) :=
    (GlobalTheory.CharLocProd.val_algebraMap P _).symm.trans (Formalism.L2.Host.unif_spec P)
  have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P.valuation D.host.E (k : D.host.E) = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  let u : D.host.Eˣ := k * Formalism.L2.Host.unif P ^ n
  have hv : P.valuation D.host.E (u : D.host.E) = 1 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hn, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hv' : P.valuation D.host.E ((u⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  have h1 : c (locHom he.1 u) = 1 :=
    hu _ (loc_parts he _ hv.le).1 (loc_parts he _ hv.le).2 (by
      rw [← map_inv]
      exact (loc_parts he _ hv'.le).2)
  rw [map_mul, map_mul, map_zpow, map_zpow, h P e he (locHom he.1 (Formalism.L2.Host.unif P)) rfl, one_zpow, mul_one] at h1
  rw [h1]
  rfl

theorem isEtaConj_unique : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (η η' η'' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η'' → η' = η'' := by
  rintro D σ η η' η'' ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_unif (c := η' * η''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y a b c => mul_inv_eq_one.2 ((h2 y a b c).trans (g2 y a b c).symm))
    (fun P e he y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h3 P e he y hy
  obtain ⟨b, hb, hb'⟩ := g3 P e he y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.trans hb.symm)
  have : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hpos : (0 : ℝ) < (Nat.card (kP P) : ℝ) := Nat.cast_pos.2 Nat.card_pos
  exact Subtype.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 hpos).ne'))
    (ha'.symm.trans hb'))

end GlobalTheory.UnramCharUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfLevelOnObjects
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRowsObj

open GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

variable {D : D7}

theorem not_isConjPl (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {PP PP' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : P.Div k PP) (h' : P.Div k' PP') : ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro hc
  obtain ⟨l, -, hl⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  have hle : ∀ {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.E)}, P.Div k Q → l.Mb ≤ Q.asIdeal := fun {k Q} hQ => by
    rw [hl]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    have e : Q.under (𝓞 D.host.K) = P.pb k := hQ
    rw [Ideal.map_le_iff_le_comap, ← e]
    exact le_rfl
  refine PP'.isPrime.ne_top (top_le_iff.1 (l.coprime.ge.trans (sup_le (hle h') ?_)))
  rw [Ideal.map_le_iff_le_comap]
  intro c hc0
  obtain ⟨c', h1, h2⟩ := hc c (hle h hc0)
  have e : (Formalism.L2.Pj.hostOfRecord D).bar c = c' :=
    RingOfIntegers.ext (((Formalism.L2.Pj.hostOfRecord D).bar_eq c).trans h2.symm)
  show (Formalism.L2.Pj.hostOfRecord D).bar c ∈ PP'.asIdeal
  rwa [e]

theorem liftsExist {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) : LiftsExist (Yc D 0) (L.βY 0) (L.dat0 L.triv) := by
  obtain ⟨c, hc⟩ := hL.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  obtain ⟨k', hk'⟩ := (hL.Pg PP').1 (h'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl _ hk hk'

section Mult

variable {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) :
    HasType V β (flag1L L) F := by
  intro κ hκ h
  have hl := GlobalTheory.FlagAction.isLift_one_of_mem hκ
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hl.2.2]; exact P.H.one_mem
  rw [hF κ ⟨hl.1, hl.2.1, hp⟩ h, GlobalTheory.FlagAction.levChi_flag1]
  congr 1
  unfold levChi
  rw [levFn_withP, extendOne_of_mem _ hp, show (⟨_, hp⟩ : P.H) = 1 from Subtype.ext hl.2.2, map_one, one_mul]

theorem mem_mult_withP_iff (hl : LiftsExist V β L) {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (P : LevelP L.Pg L.r ℂ) (U : MMap M) :
    U ∈ Mult θ M (levS V β (withP L P)) (levChi V β (withP L P)) ↔
      U ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) ∧
        ∀ p : P.H, postOn M (actL V β L p.1) U = ((P.chi p : ℂˣ) : ℂ) • U := by
  rw [GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, HasType V β (withP L P) (U v) := fun v κ hκ y => h.lev v κ hκ y
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ y => hasType_flag1 (hT v) κ hκ y, h.equiv, h.cont⟩, fun p => ?_⟩
    ext v y
    exact congrFun (GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (hT v) p (hl _)) y
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ y => ?_, h.equiv, h.cont⟩
    exact IsPLevel.hasType (V := V) (β := β) (L := L) (P := P)
      ⟨fun κ hκ y => h.lev v κ hκ y, fun p => congrArg (fun W : MMap M => W v) (hP p)⟩ κ hκ y

end Mult

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable {R : RealDat D A Ks}

end GlobalTheory.LevelRowsObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
noncomputable section

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

namespace GlobalTheory.TwistPlacesObj

open GlobalTheory.QPosCompare

section Lin

variable {K X E W : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {σ : K →+* ℂ} {j : X →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)

theorem lin_injective (hj : IsForm j) {n : ℕ} (f : (Fin n → K) →ₗ[K] X) (hf : Function.Injective f)
    (hZ : ∀ y, j (f y) ∈ LinearMap.range (LinearMap.adjoint θ)) :
    Function.Injective (Formalism.IndefR.Cx.lin fun k => θ (j (f (Pi.single k 1)))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  have h1 : LinearIndependent K fun k : Fin n => f (Pi.single k 1) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
    simpa [Function.comp_def] using this
  have h2 := hj.linInd h1
  set u : E := ∑ k, c k • j (f (Pi.single k 1)) with hu
  have h3 : u ∈ LinearMap.ker θ := by
    rw [Formalism.IndefR.Cx.lin_apply] at hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.mem_ker, hu, map_sum]
    simpa only [map_smul] using hc
  have h4 : u ∈ (LinearMap.ker θ)ᗮ := by
    rw [LinearMap.orthogonal_ker]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZ _)
  have h5 : u = 0 := inner_self_eq_zero.1 (h4 u h3)
  funext k
  exact Fintype.linearIndependent_iff.1 h2 c h5 k

variable {G : Type} [Group G] [Fintype G] (r : Representation K G X) (ρ : G → W →ₗ[ℂ] W)

end Lin

section Block

open Formalism.DivisionValues Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)
  {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {j : B.S.Forms →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)
  (ρ : G → W →ₗ[ℂ] W)

theorem toF_mem (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z :=
  (B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y)

end Block

section Content

open Formalism.BasicNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree.DepthCond

end Content

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isForm_tw {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ σ' : K →+* ℂ} (s : Bool) (h : ∀ a, σ' a = cj s (σ a)) {j : X →ₛₗ[σ] E} (hj : IsForm j) :
    IsForm (E := Tw s E) (Tw.semi s h j) := by
  obtain ⟨⟨n, b, h1, h2⟩, h3⟩ := hj
  refine ⟨⟨n, b, (Tw.linInd (E := E) s h1 :), ?_⟩, fun x y => ?_⟩
  · have e : Set.range (Tw.semi s h j) = Tw.mk s '' Set.range j := by rw [← Set.range_comp]; rfl
    rw [e, tw_span, h2]
    rfl
  · obtain ⟨a, ha⟩ := h3 x y
    exact ⟨a, (congrArg (cj s) ha).trans (h a).symm⟩

end Real

end GlobalTheory.TwistPlacesObj

end
end
