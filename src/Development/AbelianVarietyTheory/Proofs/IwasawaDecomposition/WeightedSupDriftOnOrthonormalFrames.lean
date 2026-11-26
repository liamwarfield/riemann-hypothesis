module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesBoundedOfDefinite
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MixedSignature

open GlobalTheory.UnitaryFrames (hermC_eq_dot gram_eq_mul hermC_mulVec col_mul' locallyCompact_GL secondCountable_GL)
open GlobalTheory.FiniteCovolume (inv_keeps_gram embGL embGL_val hermC_eq_dotProduct uStabSubgroup)
open GlobalTheory.UnitaryLift (det_ne_zero_of_diag)
open GlobalTheory.LatFin (exists_common_den exists_int_smul_mem finite_bounded)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Orth {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ)

def Uni {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, ∀ u w, hermC τ.1 G (Matrix.mulVec (n τ) u) (Matrix.mulVec (n τ) w) = hermC τ.1 G u w

lemma det_ne_zero_of_isOrth {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x : Frame X.Ψ r} (hx : Orth X G p x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn
  split_ifs <;> simp

lemma isClosed_unitary {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) :
    IsClosed {g : X.Ψ → GL (Fin r) ℂ | Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)} := by
  simp only [Uni, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun u => isClosed_iInter fun w => ?_
  refine isClosed_eq ?_ continuous_const
  have hc : Continuous fun g : X.Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val.comp (continuous_apply τ)
  simp only [hermC_eq_dot]
  exact (hc.matrix_mulVec continuous_const).dotProduct
    (continuous_const.matrix_mulVec (hc.matrix_mulVec continuous_const).star)

lemma isOrth_lmulC {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hn : Uni X G n) {x : Frame X.Ψ r} (hx : Orth X G p x) : Orth X G p (X.lmulC n x) := by
  intro τ
  rw [← hx τ, show mat (X.lmulC n x) τ = n τ * mat x τ from rfl]
  ext a b
  simp only [gram, Matrix.of_apply, col_mul', hn τ]

noncomputable def toGL {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x : Frame X.Ψ r} (hx : Orth X G p x) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x τ) (det_ne_zero_of_isOrth X hx τ)

lemma val_toGL {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x : Frame X.Ψ r} (hx : Orth X G p x) (τ : X.Ψ) :
    (toGL X hx τ : Matrix (Fin r) (Fin r) ℂ) = mat x τ := rfl

lemma quotient_unitary {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x y : Frame X.Ψ r} (hx : Orth X G p x)
    (hy : Orth X G p y) :
    Uni X G fun τ => ((toGL X hx * (toGL X hy)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  intro τ u w
  have key : ∀ u w, hermC τ.1 G (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      hermC τ.1 G (mat y τ *ᵥ u) (mat y τ *ᵥ w) := by
    intro u w
    rw [hermC_mulVec, hermC_mulVec, hx τ, hy τ]
  have h := key ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
    ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
  rw [← val_toGL X hx, ← val_toGL X hy] at h
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  exact h

lemma continuous_toGL {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) :
    Continuous fun x : {x : Frame X.Ψ r | Orth X G p x} => toGL X x.2 := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun x : {x : Frame X.Ψ r | Orth X G p x} => mat x.1 τ :=
    (continuous_apply τ).comp continuous_subtype_val
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have h : (fun x : {x : Frame X.Ψ r | Orth X G p x} =>
      (((toGL X x.2 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
      fun x => ((mat x.1 τ).det)⁻¹ • (mat x.1 τ).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, val_toGL, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hc.matrix_det.inv₀ fun x => det_ne_zero_of_isOrth X x.2 τ).smul hc.matrix_adjugate

theorem unitary_group_frames :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (p : X.Ψ → ℕ) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, Orth X G p x0 → (∀ g : H, Orth X G p (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | Orth X G p x} ∧ (∀ x, Orth X G p x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g) := by
  classical
  intro r X G p H hH
  haveI := locallyCompact_GL r
  haveI := secondCountable_GL r
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert isClosed_unitary X G using 1
    ext g
    exact hH g
  refine ⟨hcl.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, fun x0 hx0 => ?_⟩
  have horth : ∀ g : H, Orth X G p (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  refine ⟨horth, fun x => if hx : Orth X G p x then
    ⟨toGL X hx * (toGL X hx0)⁻¹, (hH _).2 (quotient_unitary X hx hx0)⟩ else 1, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    refine ((continuous_toGL X G p).mul (continuous_const (y := (toGL X hx0)⁻¹))).congr fun x => ?_
    have hx : Orth X G p x.1 := x.2
    simp only [Function.comp_apply, Set.restrict_apply, dif_pos hx]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    funext τ
    change (((toGL X hx τ * (toGL X hx0 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (toGL X hx0 τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Units.val_mul, inv_mul_cancel_right, val_toGL]
  · intro g
    simp only [dif_pos (horth g)]
    apply Subtype.ext
    change toGL X (horth g) * (toGL X hx0)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    funext τ
    exact Units.ext rfl

theorem isOrth_update_mul_inv :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (τ0 : X.Ψ) (x : Frame X.Ψ r) (a : Matrix (Fin r) (Fin r) ℂ), Orth X G p x → (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → Orth X G p (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X G p τ0 x a hx ha τ
  letI : DecidableEq X.Ψ := Classical.decEq _
  by_cases hτ : τ = τ0
  · subst hτ
    have hm : mat (Function.update x τ (mat x τ * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ * a⁻¹ := by
      unfold mat
      exact Function.update_self _ _ _
    have hJ : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ then (1 : ℂ) else -1)
        = gram τ.1 G (mat x τ) := by
      rw [hx τ]
      congr 1
      funext k
      unfold sgn
      split_ifs <;> simp
    have hdet : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ then (1 : ℂ) else -1).det
        ≠ 0 := by
      rw [Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      split_ifs <;> simp
    have h := inv_keeps_gram hdet ha
    rw [hJ] at h
    rw [hm, ← hx τ, ← h, gram_eq_mul, gram_eq_mul,
      Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  · have hm : mat (Function.update x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ := by
      unfold mat
      exact Function.update_of_ne hτ _ _
    rw [hm]
    exact hx τ

lemma conj_unitary {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x0 : Frame X.Ψ r} (hx0 : Orth X G p x0)
    (c : X.Ψ → GL (Fin r) ℂ)
    (hc : ∀ τ, (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < (p τ) then (1 : ℂ) else -1) *
      (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < (p τ) then (1 : ℂ) else -1)) :
    Uni X G fun τ =>
      ((toGL X hx0 * c * (toGL X hx0)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  have hJ : ∀ τ, (Matrix.diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ)) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < (p τ) then (1 : ℂ) else -1) := by
    intro τ
    congr 1
    funext k
    unfold sgn
    split_ifs <;> simp
  have hy : Orth X G p
      (fun τ => (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
    intro τ
    have h0 := hx0 τ
    rw [gram_eq_mul, hJ] at h0
    change gram τ.1 G (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ)) = _
    rw [gram_eq_mul, hJ, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
          ((mat x0 τ)ᵀ * (G.map τ.1 * (mat x0 τ).map (starRingEnd ℂ))) *
          (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h0, hc τ]
  have he : toGL X hy = toGL X hx0 * c := by
    funext τ
    exact Units.ext rfl
  rw [← he]
  exact quotient_unitary X hy hx0

theorem step_of_right_mul :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, Orth X G p x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X G p H hH x0 hx0 τ0 a s ha hs hsa
  letI : DecidableEq X.Ψ := Classical.decEq _
  have hda := det_ne_zero_of_diag ha
  let A : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a hda
  let S : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero s (det_ne_zero_of_diag hs)
  have hAi : ((A⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = a⁻¹ := by
    rw [Matrix.coe_units_inv]; rfl
  have hSA : S * A = A⁻¹ * S := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAi]
    exact hsa
  have hSA' : S * A⁻¹ = A * S := by
    calc S * A⁻¹ = A * (A⁻¹ * S) * A⁻¹ := by group
      _ = A * S := by rw [← hSA]; group
  have hmem : ∀ b : GL (Fin r) ℂ, (b : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) *
      (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) →
      toGL X hx0 * Pi.mulSingle τ0 b * (toGL X hx0)⁻¹ ∈ H := by
    intro b hb
    refine (hH _).2 (conj_unitary X hx0 _ fun τ => ?_)
    by_cases h : τ = τ0
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hb
    · rw [Pi.mulSingle_eq_of_ne h]
      simp
  refine ⟨(⟨_, hmem A ha⟩ : H)⁻¹, ⟨_, hmem S hs⟩, ?_, fun g => ?_⟩
  · apply Subtype.ext
    have h1 : (Pi.mulSingle τ0 S * (Pi.mulSingle τ0 A)⁻¹ : X.Ψ → GL (Fin r) ℂ) =
        Pi.mulSingle τ0 A * Pi.mulSingle τ0 S := by
      rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul, hSA']
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc _ = toGL X hx0 * (Pi.mulSingle τ0 S * (Pi.mulSingle τ0 A)⁻¹) * (toGL X hx0)⁻¹ := by group
      _ = _ := by rw [h1]; group
  · have key : ((g * (⟨_, hmem A ha⟩ : H)⁻¹ : H) : X.Ψ → GL (Fin r) ℂ) * toGL X hx0 =
        (g : X.Ψ → GL (Fin r) ℂ) * toGL X hx0 * Pi.mulSingle τ0 A⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mulSingle_inv]
      group
    funext τ
    have k1 := congrArg (fun u : X.Ψ → GL (Fin r) ℂ => (u τ : Matrix (Fin r) (Fin r) ℂ)) key
    refine k1.trans ?_
    beta_reduce
    rw [Pi.mul_apply, Pi.mul_apply, Units.val_mul, Units.val_mul]
    by_cases h : τ = τ0
    · subst h
      rw [Pi.mulSingle_eq_same, hAi]
      exact Eq.symm (@Function.update_self X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _)
    · rw [Pi.mulSingle_eq_of_ne h, Units.val_one, Matrix.mul_one]
      exact Eq.symm (@Function.update_of_ne X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _)

theorem isUnitaryC_of_isUStab {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E} (hγ : IsUStab G X.Λ γ) :
    Uni X G fun τ => ((embGL X.Ψ γ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  have h0 : (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
    ext a b
    have h := hγ.1 (Pi.single a 1) (Pi.single b 1)
    simp only [herm, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, one_mul] at h
    have h2 : G a b = ∑ x, ∑ x_1, if x = a then G x x_1 * cc (if x_1 = b then 1 else 0) else 0 := by
      simp [apply_ite cc, cc_one, cc_zero]
    rw [h2, ← h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  intro τ u w
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) E => M.map τ.1) h0
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have e3 : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) := by
    ext a b; simp [emb_cc]
  rw [e3] at h
  simp only [embGL_val]
  set M := (γ : Matrix (Fin r) (Fin r) E).map τ.1
  have e4 : starRingEnd ℂ ∘ (M *ᵥ w) = M.map (starRingEnd ℂ) *ᵥ (starRingEnd ℂ ∘ w) := by
    funext a; exact RingHom.map_mulVec (starRingEnd ℂ) M w a
  rw [hermC_eq_dotProduct, hermC_eq_dotProduct, e4, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X G H _
  refine ⟨((uStabSubgroup G X.Λ).map (embGL X.Ψ)).subgroupOf H, fun g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  refine exists_congr fun γ => and_congr Iff.rfl ⟨fun h τ => ?_, fun h => ?_⟩
  · rw [← h, embGL_val]
  · funext τ
    exact Units.ext ((embGL_val _ _ _).trans (h τ).symm)

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

theorem isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X G p R
  have h1 : IsClosed {x : Frame X.Ψ r | Orth X G p x} := by
    simp only [Orth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)

theorem orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) {p : X.Ψ → ℕ}, (∀ τ, p τ = 0 ∨ p τ = r) →
      ∃ R : ℝ, ∀ x, Orth X G p x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X G p hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a, ‖(G.map τ.1)⁻¹ a a‖, fun x hx τ a b => ?_⟩
  obtain ⟨s, hs, hsa⟩ : ∃ s : ℂ, s * s = 1 ∧ ∀ a : Fin r, ((sgn (p τ) (a : ℕ) : ℝ) : ℂ) = s := by
    rcases hp τ with hp | hp
    · exact ⟨-1, by ring, fun a => by simp [sgn, hp]⟩
    · exact ⟨1, by ring, fun a => by simp [sgn, hp]⟩
  have h : (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) =
      s • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    have h0 := hx τ
    simp only [hsa] at h0
    rw [Matrix.smul_one_eq_diagonal, ← h0]
    ext i j
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have h1 := norm_entry_le_of_gram_eq_smul_one _ _ s hs h a b
  have h2 : ‖(G.map τ.1)⁻¹ a a‖ ≤ ∑ a, ‖(G.map τ.1)⁻¹ a a‖ :=
    Finset.single_le_sum (f := fun a => ‖(G.map τ.1)⁻¹ a a‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h3 : ∑ a, ‖(G.map τ.1)⁻¹ a a‖ ≤ ∑ τ : X.Ψ, ∑ a, ‖(G.map τ.1)⁻¹ a a‖ :=
    Finset.single_le_sum (f := fun τ : X.Ψ => ∑ a, ‖(G.map τ.1)⁻¹ a a‖)
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  have h4 : mat x τ a b = x τ a b := rfl
  rw [h4] at h1
  linarith

theorem compactSpace_unitary_of_definite :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (∀ τ, p τ = 0 ∨ p τ = r) → ∀ x0, Orth X G p x0 → CompactSpace H) := by
  intro r X G p H hH hp x0 hx0
  obtain ⟨R, hR⟩ := orthonormal_frames_bounded_of_definite r X G hp
  obtain ⟨-, -, h⟩ := unitary_group_frames r X p H hH
  obtain ⟨horth, ι, hc, -, hι⟩ := h x0 hx0
  have hK := (isCompact_orth_bounded r X G p R).image_of_continuousOn
    (hc.mono fun x hx => hx.1)
  refine ⟨hK.of_isClosed_subset isClosed_univ fun g _ => ?_⟩
  exact ⟨_, ⟨horth g, hR _ (horth g)⟩, hι g⟩

theorem finite_automorphisms (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab G X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this

theorem gamDisc : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X G H _
  have hS := finite_automorphisms r X G 2
  set S := {γ : GL (Fin r) E | IsUStab G X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.MixedSignature
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MixedSignature

open GlobalTheory.HeightInv (relIndex_span_map)
open GlobalTheory.HeightEnds (gramDet_square)
open GlobalTheory.LineHeight (gramDet_column exists_min_le_of_le_prod nonempty_cmType c_pos)
open GlobalTheory.FiniteCovolume (nonneg_of_isLUB_image)
open GlobalTheory.DriftUnitary (continuous_orbit)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def MinGe {r : ℕ} (X : Data E r) (ε : ℝ) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.Λ, v ≠ 0 → ε ≤ QuadraticLatticeForms.Qy X (mat x) v

theorem height_lact : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0) ∧ ∀ W : Submodule E (Fin r → E), d (lact γ x) (W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin) = d x W) := by
  intro r X G d hd γ hγ x hx
  have hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ :=
    fun τ => rfl
  have hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    have := τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero τ.1).2 hγdet
  have hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 := by
    intro τ
    rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hτdet τ) (hx τ)
  refine ⟨hx', fun W => ?_⟩
  obtain ⟨w, hw, hwΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_isUnit γ.isUnit
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ := hγ.2
  have hw' : LinearIndependent E (fun a => f (w a)) :=
    hw.map' f (LinearMap.ker_eq_bot.2 hinj)
  have hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a)) := by
    conv_lhs => rw [← hsp]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have e1 := hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))
  have e2 := hd x hx _ w hw hwΛ
  have hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) =
      (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)) := by
    intro τ
    have : (Matrix.of fun k a => τ.1 (f (w a) k)) =
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k)) := by
      ext k a
      simp [hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]
  rw [hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]
  rw [hsp] at e2
  rw [e2, hsp]
  simp only [hM]

theorem height_sup_lact_invariant : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  intro r X G d hd δ α hα γ hγ x hx i hi
  obtain ⟨hx', hinv⟩ := height_lact r X d hd γ hγ x hx
  let e : (Fin r → E) ≃ₗ[E] (Fin r → E) := Matrix.GeneralLinearGroup.toLin γ |>.toLinearEquiv
  have he : (e : (Fin r → E) →ₗ[E] (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVecLin := by
    ext1 j
    rfl
  rw [← he] at hinv
  refine (hα i hi _ hx').unique ?_
  suffices hs : (fun W => d (lact γ x) W ^ (-δ)) '' {W | Module.finrank E W = i} =
      (fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i} by
    rw [hs]
    exact hα i hi x hx
  ext t
  constructor
  · rintro ⟨W, hW, rfl⟩
    refine ⟨W.map (e.symm : (Fin r → E) →ₗ[E] (Fin r → E)), ?_, ?_⟩
    · simpa [LinearEquiv.finrank_map_eq] using hW
    · show d x _ ^ (-δ) = d (lact γ x) W ^ (-δ)
      rw [← hinv, ← Submodule.map_comp]
      simp
  · rintro ⟨W, hW, rfl⟩
    refine ⟨W.map (e : (Fin r → E) →ₗ[E] (Fin r → E)), ?_, ?_⟩
    · simpa [LinearEquiv.finrank_map_eq] using hW
    · show d (lact γ x) _ ^ (-δ) = d x W ^ (-δ)
      rw [hinv]

theorem norm_det_orth {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (x : Frame X.Ψ r) (hx : Orth X G p x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 G.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [GlobalTheory.HeightEnds.gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn (p τ) (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring

theorem exists_pos_le_bot_top : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, Orth X G p x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  intro r X G p hG d hd
  obtain ⟨w0, hw0, hΛ0, hsp0⟩ := GlobalTheory.LatBasis.exists_basis_mem r X ⊤
  have hr : r = Module.finrank E (⊤ : Submodule E (Fin r → E)) := by simp
  let w : Fin r → Fin r → E := w0 ∘ finCongr hr
  have hw : LinearIndependent E w := hw0.comp _ (finCongr hr).injective
  have hΛ : ∀ a, w a ∈ X.Λ := fun a => hΛ0 _
  have hsp : Submodule.span E (Set.range w) = ⊤ := by
    rw [(finCongr hr).surjective.range_comp]; exact hsp0
  have hdet : (Matrix.of w).det ≠ 0 := by
    have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X (Fin r) w hw hΛ
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup) with hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hind)
  let c : ℝ := (∏ τ : X.Ψ, ‖τ.1 G.det‖ * ‖τ.1 (Matrix.of w).det‖ ^ 2) / n
  have hc : 0 < c := by
    refine div_pos (Finset.prod_pos fun τ _ => mul_pos ?_ (pow_pos ?_ 2)) hnpos
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hG)
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hdet)
  refine ⟨min 1 c, lt_min one_pos hc, fun x hx => ?_⟩
  have hxd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := by
    intro τ h0
    have := norm_det_orth X x hx τ
    simp [h0] at this
  constructor
  · have h := hd x hxd Empty (fun a => a.elim) linearIndependent_empty_type (fun a => a.elim)
    have hre : Set.range (fun a : Empty => (a.elim : Fin r → E)) = ∅ := Set.range_eq_empty _
    rw [hre] at h
    simp only [Submodule.span_empty, Matrix.det_isEmpty, Complex.one_re, Finset.prod_const_one,
      Submodule.bot_toAddSubgroup, inf_bot_eq, AddSubgroup.relIndex_self, Nat.cast_one,
      div_one] at h
    rw [h]
    exact min_le_left _ _
  · have h := hd x hxd (Fin r) w hw hΛ
    rw [← hn, hsp] at h
    rw [h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    refine congrArg (· / (n : ℝ)) (Finset.prod_congr rfl fun τ _ => ?_)
    have h1 : (Matrix.of fun k a => τ.1 (w a k)).det = τ.1 (Matrix.of w).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
      rfl
    have h2 := norm_det_orth X x hx τ
    have h3 : ‖(mat x τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hxd τ)
    rw [gramDet_square, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h1, norm_mul,
      norm_inv, mul_pow, inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right h2

theorem minGe_of_lines : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → MinGe X ε x) := by
  intro r X d hd m hm
  have := nonempty_cmType X
  obtain ⟨τ0, hτ0⟩ := Finite.exists_min X.c
  have hmin : 0 < min 1 m := lt_min one_pos hm
  refine ⟨X.c τ0 * min 1 m, mul_pos (c_pos X τ0) hmin, ?_⟩
  intro x hdet hW v hv hv0
  unfold QuadraticLatticeForms.Qy
  have hli : LinearIndependent E (fun _ : Unit => v) := by
    rw [linearIndependent_unique_iff]; exact hv0
  have hrank : Module.finrank E (Submodule.span E (Set.range (fun _ : Unit => v))) = 1 := by
    rw [finrank_span_eq_card hli]; simp
  have h1 := hW _ hrank
  rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli (fun _ => hv)
  have hnn : ∀ τ : X.Ψ, 0 ≤ (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) := fun τ => by
    positivity
  have hprod : (∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k (_ : Unit) => τ.1 (v k)))ᴴ *
      ((mat x τ)⁻¹ * (Matrix.of fun k (_ : Unit) => τ.1 (v k)))).det.re))
      = ∏ τ : X.Ψ, (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) :=
    Finset.prod_congr rfl fun τ _ => by
      exact gramDet_column _ (Data.emb τ.1 v)
  have h2 : m ≤ ∏ τ : X.Ψ, (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) := by
    refine h1.trans ?_
    rw [← hprod]
    refine div_le_self ?_ ?_
    · rw [hprod]; exact Finset.prod_nonneg fun τ _ => hnn τ
    · exact_mod_cast Nat.one_le_iff_ne_zero.2 hind
  obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hnn m h2
  calc X.c τ0 * min 1 m ≤ X.c τ * (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) :=
        mul_le_mul (hτ0 τ) hτ hmin.le (c_pos X τ).le
    _ ≤ _ := Finset.single_le_sum (f := fun τ => X.c τ * (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2))
        (fun τ _ => mul_nonneg (c_pos X τ).le (hnn τ)) (Finset.mem_univ τ)

theorem weighted_sup_drift_on_orthonormal_frames :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, Orth X G p x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by
  intro r X G p hG d hd τ0 S hS hirr hU
  obtain ⟨δ, c, Ω, hδ, hc0, hc1, hΩ, hw⟩ := GlobalTheory.height_rpow_neg_distortion_contraction r X d hd τ0 S hS hirr
  refine ⟨δ, hδ, fun α hα => ?_⟩
  have hdet : ∀ y : {x // Orth X G p x}, ∀ τ : X.Ψ, (mat y.1 τ).det ≠ 0 :=
    fun y => det_ne_zero_of_isOrth X y.2
  have hpos : ∀ y : {x // Orth X G p x}, ∀ W, 0 < d y.1 W := fun y W => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.HeightLower.exists_pos_le_height r X d hd y.1 (hdet y)
    exact hm.trans_le (h W)
  let t : S → {x // Orth X G p x} → {x // Orth X G p x} := fun a y =>
    ⟨_, isOrth_update_mul_inv r X τ0 y.1 a.1 y.2 (hU a.1 a.2)⟩
  have hfr : Module.finrank E (Fin r → E) = r := by simp
  obtain ⟨C, hC, halt⟩ := GlobalTheory.subspace_sup_alternative E (Fin r → E) {x // Orth X G p x} S r t
    (fun y W => d y.1 W ^ (-δ)) (fun i y => α i y.1) c Ω hfr hΩ
    (fun y W => Real.rpow_pos_of_pos (hpos y W) _)
    (fun i hi y => hα i hi y.1 (hdet y))
    (fun y W₁ W₂ => by
      have h := GlobalTheory.HeightSubmodular.height_submodular r X d hd y.1 (hdet y) W₁ W₂
      rw [← Real.mul_rpow (hpos y _).le (hpos y _).le, ← Real.mul_rpow (hpos y _).le (hpos y _).le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos (hpos y _) (hpos y _)) h (by linarith))
    (fun s y W => (hw y.1 (hdet y) W).1 s.1 s.2)
    (fun y W h0 h1 => by
      have h := (hw y.1 (hdet y) W).2 h0 h1
      rw [← Finset.sum_coe_sort] at h
      rw [Fintype.card_coe]
      exact h)
  obtain ⟨m, hm, htop⟩ := exists_pos_le_bot_top r X G p hG d hd
  obtain ⟨e, c', b, he, hc'0, hc'1, hb, hdr⟩ := GlobalTheory.weighted_sum_drift_inequality
    {x // Orth X G p x} S r t (fun i y => α i y.1) c C (m ^ (-δ)) hc0 hc1 hC
    (fun i hi y => nonneg_of_isLUB_image (fun W => (Real.rpow_pos_of_pos (hpos y W) _).le)
      (hα i hi y.1 (hdet y)))
    (fun y => by
      constructor
      · refine (hα 0 (Nat.zero_le r) y.1 (hdet y)).2 ?_
        rintro _ ⟨W, hW, rfl⟩
        have hW' : W = ⊥ := Submodule.finrank_eq_zero.1 hW
        subst hW'
        exact Real.rpow_le_rpow_of_nonpos hm (htop y.1 y.2).1 (by linarith)
      · refine (hα r le_rfl y.1 (hdet y)).2 ?_
        rintro _ ⟨W, hW, rfl⟩
        have hW' : W = ⊤ := Submodule.eq_top_of_finrank_eq (hW.trans hfr.symm)
        subst hW'
        exact Real.rpow_le_rpow_of_nonpos hm (htop y.1 y.2).2 (by linarith))
    halt
  refine ⟨e, c', b, he, hc'0, hc'1, hb, fun x hx => ?_⟩
  have h := hdr ⟨x, hx⟩
  rw [Fintype.card_coe] at h
  rw [← Finset.sum_coe_sort]
  exact h

theorem exists_drift_function_orthFrames : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (τ0 : X.Ψ), 0 < p τ0 → p τ0 < r → ∀ (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | Orth X G p x} ∧ (∀ x, Orth X G p x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x, Orth X G p x → f (lact γ x) = f x) ∧ (∀ x, Orth X G p x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, Orth X G p x → f x ≤ M → MinGe X ε x) := by
  intro r X G p hG τ0 hp0 hpr S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.SubspaceHeight.exists_height r X
  obtain ⟨δ, hδ, hdrift⟩ := weighted_sup_drift_on_orthonormal_frames r X G p hG d hd τ0 S hS hirr hU
  obtain ⟨α, hα, hlsc⟩ := GlobalTheory.exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hineq⟩ := hdrift α hα
  have hinv : ∀ x, Orth X G p x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 :=
    fun x hx => det_ne_zero_of_isOrth X hx
  have hdpos : ∀ x, Orth X G p x → ∀ W, 0 < d x W := by
    intro x hx W
    obtain ⟨m, hm, hW⟩ := GlobalTheory.HeightLower.exists_pos_le_height r X d hd x (hinv x hx)
    exact hm.trans_le (hW W)
  have hαnn : ∀ x, Orth X G p x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := E) (M := Fin r → E) (n := i)
      (by simpa using hi)
    have hW : Module.finrank E (Submodule.span E (Set.range v)) = i := by
      simpa using finrank_span_eq_card hv
    exact (Real.rpow_nonneg (hdpos x hx _).le _).trans
      ((hα i hi x (hinv x hx)).1 ⟨_, hW, rfl⟩)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hineq, ?_⟩
  · refine lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi => ?_
    exact (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hinv x hx
  · intro x hx
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [height_sup_lact_invariant r X d hd δ α hα γ hγ x (hinv x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have hM' : 0 < max 1 (M / e 1) := lt_max_of_lt_left one_pos
    obtain ⟨ε, hε, hla⟩ := minGe_of_lines r X d hd ((max 1 (M / e 1)) ^ (-δ)⁻¹)
      (Real.rpow_pos_of_pos hM' _)
    refine ⟨ε, hε, fun x hx hM => hla x (hinv x hx) fun W hW => ?_⟩
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨one_pos, by omega⟩
    have h2 : e 1 * α 1 x ≤ M :=
      (Finset.single_le_sum (f := fun i => e i * α i x) (fun i hi =>
        mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)) h1).trans hM
    have h3 : α 1 x ≤ M / e 1 := by
      rw [le_div_iff₀ (he 1), mul_comm]; exact h2
    have h4 : d x W ^ (-δ) ≤ max 1 (M / e 1) :=
      (((hα 1 (by omega) x (hinv x hx)).1 ⟨W, hW, rfl⟩).trans h3).trans (le_max_right _ _)
    exact (Real.rpow_inv_le_iff_of_neg hM' (hdpos x hx W) (by linarith)).2 h4

theorem exists_drift_function :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (τ0 : X.Ψ) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < p τ0 → p τ0 < r → ∀ x0, Orth X G p x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → MinGe X ε (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  intro r X G p hG τ0 H hH _ _ hp0 hpr x0 hx0
  obtain ⟨S, hSne, hS1, hS2, hS3⟩ := GlobalTheory.gramDet_closed_forms.2.2.2 r (p τ0) hp0 hpr
  obtain ⟨f, c, b, hc0, hc1, hb, hlsc, hf0, hfinv, hdrift, hprop⟩ :=
    exists_drift_function_orthFrames r X G p hG τ0 hp0 hpr S hS1 hS2 (fun a ha => (hS3 a ha).1)
  have horth : ∀ g : H, Orth X G p (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  have hlift := fun a : S => (hS3 a a.2).2.elim fun s hs =>
    step_of_right_mul r X H hH x0 hx0 τ0 a s (hS3 a a.2).1 hs.1 hs.2
  choose h k hk hg using hlift
  refine ⟨S, inferInstance, hSne.coe_sort, h, fun g => f (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0), c, b,
    fun s => ⟨k s, hk s⟩, ?_, fun g => hf0 _ (horth g), ?_, hc0, hc1, hb, ?_, ?_⟩
  · apply LowerSemicontinuous.measurable
    rw [← lowerSemicontinuousOn_univ_iff]
    exact hlsc.comp (continuous_orbit X H x0).continuousOn (fun g _ => horth g)
  · rintro u ⟨γ, hγ, hu⟩ g
    refine Eq.trans (congrArg f ?_) (hfinv γ hγ _ (horth g))
    funext τ
    change ((((u : X.Ψ → GL (Fin r) ℂ) τ * (g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) * mat x0 τ : Matrix (Fin r) (Fin r) ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ) :
        Matrix (Fin r) (Fin r) ℂ)
    rw [Units.val_mul, hu τ, Matrix.mul_assoc]
  · intro g
    have := hdrift _ (horth g)
    rw [← Finset.sum_coe_sort S] at this
    simp only [hg, Fintype.card_coe]
    exact this
  · intro M
    obtain ⟨ε, hε, hM⟩ := hprop M
    exact ⟨ε, hε, fun g hgM => hM _ (horth g) hgM⟩

end GlobalTheory.MixedSignature
