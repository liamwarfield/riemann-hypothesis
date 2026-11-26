module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ImaginaryMajorants
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoostLowerBounds
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RankOneBoostIsometries
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace FlowMatrixMajorants

open MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)

theorem flowMat_add (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a b : ℂ) :
    X.flowMat ξ τ (a + b) = X.flowMat ξ τ a * X.flowMat ξ τ b := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ,
      V = Matrix.of fun a b => τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := ⟨_, rfl⟩
  have hM : ∀ s : ℂ, X.flowMat ξ τ s = 1 - (I * (X.c τ : ℂ) * s) • V := by
    intro s
    ext a b
    simp only [Data.flowMat, hV, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    ring
  have h0 : ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) = 0 := by
    calc _ = hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) := by
          simp only [hermC, Data.emb, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := hiso
  have hVV : V * V = 0 := by
    ext a b
    simp only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ k, τ.1 (ξ a) * (∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m))) *
          (τ.1 (ξ k) * ∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m)))
        = τ.1 (ξ a) * (∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m))) *
          ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  simp only [hM, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hVV, smul_zero, sub_zero, mul_add, add_smul]
  abel

theorem flowMat_zero : X.flowMat ξ τ 0 = 1 := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, mul_zero, zero_mul, sub_zero, Matrix.one_apply]

theorem flow_split (hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0)
    (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s x = X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) := by
  funext τ
  have hs : I * ((s τ).im : ℂ) + ((s τ).re : ℂ) = s τ := by
    rw [add_comm, mul_comm, Complex.re_add_im]
  show X.flowMat ξ τ (s τ) * mat x τ =
    X.flowMat ξ τ (I * ((s τ).im : ℂ)) * (X.flowMat ξ τ ((s τ).re : ℂ) * mat x τ)
  conv_lhs => rw [← hs]
  rw [flowMat_add X ξ τ (hiso τ), mul_assoc]

theorem flowMat_inv (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a : ℂ)
    (w : Fin r → ℂ) : Matrix.mulVec (X.flowMat ξ τ a) (Matrix.mulVec (X.flowMat ξ τ (-a)) w) = w := by
  rw [Matrix.mulVec_mulVec, ← flowMat_add X ξ τ hiso, add_neg_cancel, flowMat_zero,
    Matrix.one_mulVec]

private lemma hermC_sub_smul_left_lemma_8 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (p - a • q) y = hermC σ G p y - a * hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_sub_smul_right_lemma_9 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (p - a • q) = hermC σ G y p - conj a * hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem flowMat_isom_real (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (t : ℝ)
    (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ t) u) (Matrix.mulVec (X.flowMat ξ τ t) v) =
      hermC τ.1 X.Gm u v := by
  have hMv : ∀ w : Fin r → ℂ, Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
    intro w
    funext i
    show ∑ b, X.flowMat ξ τ t i b * w b = _
    simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hermC, Data.emb]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hMv u, hMv v, hermC_sub_smul_left_lemma_8, hermC_sub_smul_right_lemma_9, hermC_sub_smul_right_lemma_9,
    hiso, ← hermC_conj τ.1 X.Gm_herm v (Data.emb τ.1 ξ)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem Hf_add_left (x : Frame X.Ψ r) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u + u') w = X.Hf x τ u w + X.Hf x τ u' w := by
  unfold Data.Hf hermC
  rw [X.ppos_add x τ]
  simp only [smul_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem Hf_add_right (x : Frame X.Ψ r) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w + w') = X.Hf x τ u w + X.Hf x τ u w' := by
  unfold Data.Hf hermC
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC σ G (∑ k, u k • v k) y = ∑ k, u k * hermC σ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC σ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC σ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC σ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC σ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h

private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_smul_sub_right_lemma_4 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) = (X.gramPos x τ)⁻¹ by
      rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma hermC_jp_lemma_6 {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) (X.jp x τ v) = hermC τ.1 X.Gm u v := by
  unfold Data.jp
  rw [hermC_smul_sub_left_lemma_3, hermC_smul_sub_right_lemma_4, hermC_smul_sub_right_lemma_4,
    hermC_ppos_lemma_5 X τ x u (X.ppos x τ v), X.ppos_ppos hx τ v, hermC_ppos_lemma_5 X τ x u v]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  rw [h2]
  ring

private lemma maj_eq_lemma_7 (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    X.maj x τ v = (hermC τ.1 X.Gm (X.jp x τ v) v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.jp
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp

theorem maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  rw [maj_eq_lemma_7 X τ x (X.jp x τ v), maj_eq_lemma_7 X τ x v, X.jp_jp hx τ v,
    ← hermC_conj τ.1 X.Gm_herm v (X.jp x τ v), Complex.conj_re]

theorem herm_eq_Hf_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = X.Hf x τ u (X.jp x τ v) := by
  exact (hermC_jp_lemma_6 X τ hx u v).symm

private lemma flowMat_mulVec_lemma_10 (t : ℝ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext i
  show ∑ b, X.flowMat ξ τ t i b * w b = _
  simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, hermC, Data.emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem maj_flow_le {x : Frame X.Ψ r} (hx : x ∈ X.dom) (t : ℝ) (u : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) ≤
      (1 + X.c τ * |t| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ u := by
  have hHs : ∀ p q, conj (X.Hf x τ p q) = X.Hf x τ q p := by
    intro p q
    unfold Data.Hf
    rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_4, hermC_smul_sub_left_lemma_3,
      hermC_ppos_lemma_5 X τ x q p, map_ofNat]
  have hN : ∀ v, X.maj x τ v = (X.Hf x τ v v).re := fun v => maj_eq_lemma_7 X τ x v
  have hreal : ∀ v, X.Hf x τ v v = ((X.maj x τ v : ℝ) : ℂ) := by
    intro v
    rw [hN]
    exact (Complex.conj_eq_iff_re.mp (hHs v v)).symm
  have hnn : ∀ v, 0 ≤ X.maj x τ v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [hN]
      simp [Data.Hf, hermC]
    · exact (X.maj_pos hx τ hv).le
  have hsl : ∀ (a : ℂ) p q, X.Hf x τ (a • p) q = a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    rw [X.ppos_smul_eq x τ]
    simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsr : ∀ (a : ℂ) p q, X.Hf x τ p (a • q) = conj a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hexp : ∀ (α β : ℂ) p q, X.Hf x τ (α • p + β • q) (α • p + β • q) =
      α * conj α * X.Hf x τ p p + α * conj β * X.Hf x τ p q + β * conj α * X.Hf x τ q p +
        β * conj β * X.Hf x τ q q := by
    intro α β p q
    simp only [Hf_add_left X τ, Hf_add_right X τ, hsl, hsr]
    ring
  have hCS : ∀ p q, Complex.normSq (X.Hf x τ p q) ≤ X.maj x τ p * X.maj x τ q := by
    intro p q
    by_cases hq : q = 0
    · subst hq
      have h0 : X.Hf x τ p 0 = 0 := by simp [Data.Hf, hermC]
      rw [h0, map_zero]
      exact mul_nonneg (hnn p) (hnn 0)
    · have hn := X.maj_pos hx τ hq
      obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ p q := ⟨_, rfl⟩
      have h0 := hnn (((X.maj x τ q : ℝ) : ℂ) • p + (-z) • q)
      rw [hN, hexp, hreal p, hreal q, ← hHs p q, ← hz] at h0
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im,
        map_neg] at h0
      rw [← hz, Complex.normSq_apply]
      nlinarith [h0, hn]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = hermC τ.1 X.Gm u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = I * (X.c τ : ℂ) * (t : ℂ) * ℓ := ⟨_, rfl⟩
  have hMu : Matrix.mulVec (X.flowMat ξ τ t) u = (1 : ℂ) • u + (-β) • Data.emb τ.1 ξ := by
    rw [flowMat_mulVec_lemma_10 X ξ τ t u, ← hℓ, ← hβ, one_smul, neg_smul, sub_eq_add_neg]
  obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  have hval : X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) = X.maj x τ u -
      2 * (conj β * z).re + Complex.normSq β * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hN, hMu, hexp, hreal u, hreal (Data.emb τ.1 ξ), ← hHs u (Data.emb τ.1 ξ), ← hz]
    have e1 : β * conj z = conj (conj β * z) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    have e2 : β * conj β = (Complex.normSq β : ℂ) := Complex.mul_conj β
    simp only [map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg]
    rw [e1, e2]
    simp only [Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hnβ : ‖β‖ = X.c τ * |t| * ‖ℓ‖ := by
    rw [hβ, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, one_mul]
  have hL : ‖ℓ‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hℓ, herm_eq_Hf_jp X τ hx, ← Complex.normSq_eq_norm_sq, ← maj_jp X τ hx (Data.emb τ.1 ξ)]
    exact hCS _ _
  have hZ : ‖z‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hz, ← Complex.normSq_eq_norm_sq]
    exact hCS _ _
  have hre : -(2 * (conj β * z).re) ≤ 2 * ‖β‖ * ‖z‖ := by
    have h1 := Complex.abs_re_le_norm (conj β * z)
    rw [norm_mul, Complex.norm_conj] at h1
    linarith [neg_abs_le (conj β * z).re]
  have hLZ : ‖ℓ‖ * ‖z‖ ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    nlinarith [sq_nonneg (‖ℓ‖ - ‖z‖), norm_nonneg ℓ, norm_nonneg z]
  have hk : 0 ≤ X.c τ * |t| := mul_nonneg hc0 (abs_nonneg t)
  have hb : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := hnn _
  have h1 := mul_le_mul_of_nonneg_left hLZ hk
  have h2 := mul_le_mul_of_nonneg_left hL (mul_nonneg (sq_nonneg (X.c τ * |t|)) hb)
  rw [hval, Complex.normSq_eq_norm_sq, hnβ]
  rw [hnβ] at hre
  nlinarith [h1, h2, hre]

end FlowMatrixMajorants

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace RankOneBoostIsometries

open MajorantConjugateTransfer FlowMatrixMajorants

variable {r : ℕ} (X : Data E r) (τ : X.Ψ)

noncomputable def rk (p w : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i a => p i * ∑ b, τ.1 (X.Gm a b) * conj (w b)

theorem rk_mulVec (p w v : Fin r → ℂ) :
    Matrix.mulVec (rk X τ p w) v = hermC τ.1 X.Gm v w • p := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rk, Matrix.of_apply, hermC, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

noncomputable def boost (e f : Fin r → ℂ) (m σ : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (((σ - 1) / m : ℝ) : ℂ) • rk X τ e f + (((σ⁻¹ - 1) / m : ℝ) : ℂ) • rk X τ f e

theorem boost_mulVec (e f : Fin r → ℂ) (m σ : ℝ) (v : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) v =
      v + ((((σ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v f) • e +
        ((((σ⁻¹ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • f := by
  simp only [boost, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
    smul_smul]

section plane

variable {e f : Fin r → ℂ} {m : ℝ} (hm : 0 < m) (hee : hermC τ.1 X.Gm e e = 0)
  (hff : hermC τ.1 X.Gm f f = 0) (hef : hermC τ.1 X.Gm e f = m) (hfe : hermC τ.1 X.Gm f e = m)

include hm hee hff hef hfe

theorem boost_comp {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) (Matrix.mulVec (boost X τ e f m σ⁻¹) w) = w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, hee, hff, hef, hfe, inv_inv]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem boost_isom {σ : ℝ} (hσ : 0 < σ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (boost X τ e f m σ) u) (Matrix.mulVec (boost X τ e f m σ) v) =
      hermC τ.1 X.Gm u v := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
    ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hee, hff, hef, hfe, map_mul, Complex.conj_ofReal]
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v e, ← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v f]
  push_cast
  field_simp
  ring

end plane

end RankOneBoostIsometries

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace BoostLowerBounds

open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries

variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}

include hz

private theorem hermC_Gm_add_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u + u') v = hermC τ.1 X.Gm u v + hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_Gm_sub_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u - u') v = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hermC_Gm_smul_left (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (c • u) v = c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem hermC_Gm_add_right (u v v' : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v + v') = hermC τ.1 X.Gm u v + hermC τ.1 X.Gm u v' := by
  simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

private theorem hermC_Gm_sub_right (u v v' : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v - v') = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem hermC_Gm_smul_right (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u (c • v) = conj c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem hermC_Gm_sum_left {n : ℕ} (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, f a) v = ∑ a, hermC τ.1 X.Gm (f a) v :=
  map_sum (AddMonoidHom.mk' (fun u => hermC τ.1 X.Gm u v)
    (fun u u' => hermC_Gm_add_left X τ hz u u' v)) f Finset.univ

private theorem det_gramPos_ne_zero : (X.gramPos z τ).det ≠ 0 := by
  have hz' : ∀ ψ : X.Ψ, (mat z ψ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm z ψ i).re := hz
  have h2 := (hz' τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  have hd : dmin X.Gm z τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos z τ).det := rfl
  intro h0
  rw [hd, h0] at h2
  simp at h2

private theorem hermC_ppos_col_castLE (u : Fin r → ℂ) (k : Fin X.p0) :
    hermC τ.1 X.Gm (X.ppos z τ u) (col (mat z τ) (Fin.castLE X.p0_le k)) =
      hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le k)) := by
  have hinv : (X.gramPos z τ)⁻¹ * X.gramPos z τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_gramPos_ne_zero X τ hz))
  have hgk : ∀ a b : Fin X.p0, hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a))
      (col (mat z τ) (Fin.castLE X.p0_le b)) = X.gramPos z τ a b := fun a b => rfl
  rw [Data.ppos, hermC_Gm_sum_left X τ hz]
  simp only [hermC_Gm_smul_left X τ hz, hgk]
  calc ∑ a, (∑ b, hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le b)) *
          (X.gramPos z τ)⁻¹ b a) * X.gramPos z τ a k
      = ∑ b, hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le b)) *
          ((X.gramPos z τ)⁻¹ * X.gramPos z τ) b k := by
        simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = _ := by
        rw [hinv]
        simp [Matrix.one_apply]

private theorem hermC_ppos_right_eq_sum_gramPos_inv (x w : Fin r → ℂ) :
    hermC τ.1 X.Gm x (X.ppos z τ w) = ∑ a, conj (∑ b, hermC τ.1 X.Gm w
      (col (mat z τ) (Fin.castLE X.p0_le b)) * (X.gramPos z τ)⁻¹ b a) *
        hermC τ.1 X.Gm x (col (mat z τ) (Fin.castLE X.p0_le a)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← FD.hermC_conj τ.1 X.Gm_herm (X.ppos z τ w) x, Data.ppos, hermC_Gm_sum_left X τ hz, map_sum]
  simp only [hermC_Gm_smul_left X τ hz, map_mul, FD.hermC_conj τ.1 X.Gm_herm]

private theorem hermC_ppos_ppos (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos z τ u) (X.ppos z τ w) = hermC τ.1 X.Gm u (X.ppos z τ w) := by
  rw [hermC_ppos_right_eq_sum_gramPos_inv X τ hz (X.ppos z τ u) w, hermC_ppos_right_eq_sum_gramPos_inv X τ hz u w]
  simp only [hermC_ppos_col_castLE X τ hz]

private theorem hermC_ppos_self_adjoint (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos z τ u) w = hermC τ.1 X.Gm u (X.ppos z τ w) := by
  rw [← FD.hermC_conj τ.1 X.Gm_herm w (X.ppos z τ u), ← hermC_ppos_ppos X τ hz w u,
    FD.hermC_conj τ.1 X.Gm_herm, hermC_ppos_ppos X τ hz u w]

private theorem hermC_jp_left_eq_hermC_jp_right (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp z τ u) w = hermC τ.1 X.Gm u (X.jp z τ w) := by
  simp only [Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_sub_right X τ hz,
    hermC_Gm_smul_right X τ hz, map_ofNat, hermC_ppos_self_adjoint X τ hz]

private theorem hermC_jp_jp' (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp z τ u) (X.jp z τ w) = hermC τ.1 X.Gm u w := by
  simp only [Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_sub_right X τ hz,
    hermC_Gm_smul_right X τ hz, map_ofNat]
  rw [hermC_ppos_ppos X τ hz u w, hermC_ppos_self_adjoint X τ hz u w]
  ring

private theorem ppos_add' (u w : Fin r → ℂ) :
    X.ppos z τ (u + w) = X.ppos z τ u + X.ppos z τ w := by
  simp only [Data.ppos, hermC_Gm_add_left X τ hz, add_mul, Finset.sum_add_distrib, add_smul]

private theorem ppos_smul_eq_smul_ppos (t : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (t • u) = t • X.ppos z τ u := by
  simp only [Data.ppos, hermC_Gm_smul_left X τ hz, Finset.smul_sum, smul_smul, Finset.mul_sum,
    mul_assoc]

private theorem jp_add' (u w : Fin r → ℂ) :
    X.jp z τ (u + w) = X.jp z τ u + X.jp z τ w := by
  simp only [Data.jp, ppos_add' X τ hz, smul_add]
  abel

private theorem jp_smul' (t : ℂ) (u : Fin r → ℂ) :
    X.jp z τ (t • u) = t • X.jp z τ u := by
  simp only [Data.jp, ppos_smul_eq_smul_ppos X τ hz, smul_sub, smul_smul]
  rw [mul_comm]

private theorem maj_eq_re_hermC_jp (v : Fin r → ℂ) :
    X.maj z τ v = (hermC τ.1 X.Gm (X.jp z τ v) v).re := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ v) v = ∑ a, ∑ b,
      hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    rw [Data.ppos, hermC_Gm_sum_left X τ hz]
    simp only [hermC_Gm_smul_left X τ hz, FD.hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
    exact Finset.sum_comm
  simp only [Data.maj, Data.posPart, Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, ← h1]
  simp [Complex.sub_re, Complex.mul_re]

private theorem eq_zero_of_hermC_Gm_left_eq_zero (w : Fin r → ℂ) (H : ∀ u, hermC τ.1 X.Gm u w = 0) : w = 0 := by
  have hdet : (X.Gm.map τ.1).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ.1).mpr X.Gm_det
  have hmv : (X.Gm.map τ.1).mulVec (fun b => conj (w b)) = 0 := by
    funext a
    have h := H (Pi.single a 1)
    change (∑ b, (X.Gm.map τ.1) a b * conj (w b)) = 0
    simpa [hermC, Pi.single_apply, Matrix.map_apply] using h
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  funext b
  simpa using congrFun h0 b

private theorem maj_add_smul (v u : Fin r → ℂ) (t : ℂ) :
    X.maj z τ (v + t • u) = X.maj z τ v +
      2 * (conj t * hermC τ.1 X.Gm (X.jp z τ v) u).re + Complex.normSq t * X.maj z τ u := by
  have hs : hermC τ.1 X.Gm (X.jp z τ u) v = conj (hermC τ.1 X.Gm (X.jp z τ v) u) := by
    rw [FD.hermC_conj τ.1 X.Gm_herm, hermC_jp_left_eq_hermC_jp_right X τ hz]
  rw [maj_eq_re_hermC_jp X τ hz (v + t • u), maj_eq_re_hermC_jp X τ hz v, maj_eq_re_hermC_jp X τ hz u,
    jp_add' X τ hz, jp_smul' X τ hz, hermC_Gm_add_left X τ hz, hermC_Gm_smul_left X τ hz,
    hermC_Gm_add_right X τ hz, hermC_Gm_add_right X τ hz, hermC_Gm_smul_right X τ hz, hermC_Gm_smul_right X τ hz, hs]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

private theorem hermC_jp_eq_zero_of_maj_eq_zero (u v : Fin r → ℂ) (hu : X.maj z τ u = 0) :
    hermC τ.1 X.Gm (X.jp z τ v) u = 0 := by
  by_contra hw
  have hn := Complex.normSq_pos.mpr hw
  have h1 := MajorantConjugateTransfer.maj_nonneg (X := X) hz τ
    (v + (-(((X.maj z τ v + 1) / (2 * Complex.normSq (hermC τ.1 X.Gm (X.jp z τ v) u)) : ℝ) : ℂ) *
      hermC τ.1 X.Gm (X.jp z τ v) u) • u)
  rw [maj_add_smul X τ hz, hu, mul_zero, add_zero] at h1
  generalize hW : hermC τ.1 X.Gm (X.jp z τ v) u = W at h1 hn
  generalize hM : X.maj z τ v = M at h1
  have hS : Complex.normSq W ≠ 0 := ne_of_gt hn
  have h2 : (conj (-(((M + 1) / (2 * Complex.normSq W) : ℝ) : ℂ) * W) * W).re =
      -((M + 1) / (2 * Complex.normSq W)) * Complex.normSq W := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have h3 : -((M + 1) / (2 * Complex.normSq W)) * Complex.normSq W = -((M + 1) / 2) := by
    rw [neg_mul, div_mul_eq_mul_div, mul_div_mul_right _ _ hS]
  rw [h2, h3] at h1
  linarith

theorem plane_facts (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) :
    0 < X.maj z τ e ∧ hermC τ.1 X.Gm (X.jp z τ e) (X.jp z τ e) = 0 ∧
      hermC τ.1 X.Gm e (X.jp z τ e) = X.maj z τ e ∧
      hermC τ.1 X.Gm (X.jp z τ e) e = X.maj z τ e := by
  have hre : hermC τ.1 X.Gm (X.jp z τ e) e = X.maj z τ e := by
    rw [maj_eq_re_hermC_jp X τ hz e]
    have hc : conj (hermC τ.1 X.Gm (X.jp z τ e) e) = hermC τ.1 X.Gm (X.jp z τ e) e := by
      rw [FD.hermC_conj τ.1 X.Gm_herm, hermC_jp_left_eq_hermC_jp_right X τ hz]
    exact (Complex.conj_eq_iff_re.mp hc).symm
  have hiso : hermC τ.1 X.Gm (X.jp z τ e) (X.jp z τ e) = 0 := by
    rw [hermC_jp_jp' X τ hz, hee]
  have hsym : hermC τ.1 X.Gm e (X.jp z τ e) = X.maj z τ e := by
    rw [← hermC_jp_left_eq_hermC_jp_right X τ hz, hre]
  have hpos : 0 < X.maj z τ e := by
    rcases (MajorantConjugateTransfer.maj_nonneg (X := X) hz τ e).lt_or_eq with h | h
    · exact h
    · exfalso
      have hje : X.jp z τ e = 0 := eq_zero_of_hermC_Gm_left_eq_zero X τ hz _ fun u => by
        rw [← hermC_jp_left_eq_hermC_jp_right X τ hz u e]
        exact hermC_jp_eq_zero_of_maj_eq_zero X τ hz e u h.symm
      exact he0 (eq_zero_of_hermC_Gm_left_eq_zero X τ hz _ fun u => by
        rw [← hermC_jp_jp' X τ hz u e, hje]
        simp [hermC])
  exact ⟨hpos, hiso, hsym, hre⟩

theorem maj_decomp (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) (w0 : Fin r → ℂ)
    (h0e : hermC τ.1 X.Gm w0 e = 0) (h0f : hermC τ.1 X.Gm w0 (X.jp z τ e) = 0) (a b : ℂ) :
    X.maj z τ (w0 + a • e + b • X.jp z τ e) =
      X.maj z τ w0 + (Complex.normSq a + Complex.normSq b) * X.maj z τ e := by
  obtain ⟨-, hff, -, -⟩ := plane_facts X τ hz hee he0
  have hjw : hermC τ.1 X.Gm (X.jp z τ w0) e = 0 := by
    rw [hermC_jp_left_eq_hermC_jp_right X τ hz, h0f]
  have hjf : hermC τ.1 X.Gm (X.jp z τ (w0 + a • e)) (X.jp z τ e) = 0 := by
    rw [jp_add' X τ hz, jp_smul' X τ hz, hermC_Gm_add_left X τ hz, hermC_Gm_smul_left X τ hz,
      hermC_jp_jp' X τ hz w0 e, h0e, hff, mul_zero, add_zero]
  have hmf : X.maj z τ (X.jp z τ e) = X.maj z τ e := by
    rw [maj_eq_re_hermC_jp X τ hz (X.jp z τ e), maj_eq_re_hermC_jp X τ hz e, hermC_jp_jp' X τ hz (X.jp z τ e) e]
  rw [maj_add_smul X τ hz (w0 + a • e), maj_add_smul X τ hz w0, hjw, hjf, hmf]
  simp only [mul_zero, Complex.zero_re, add_zero]
  ring

theorem boost_lower (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (w : Fin r → ℂ) :
    min (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w ≤
      X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) := by
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  have hm0 : ((X.maj z τ e : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = hermC τ.1 X.Gm w (X.jp z τ e) / (X.maj z τ e : ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = hermC τ.1 X.Gm w e / (X.maj z τ e : ℂ) := ⟨_, rfl⟩
  have hwf : hermC τ.1 X.Gm w (X.jp z τ e) = A * X.maj z τ e := by
    rw [hA, div_mul_cancel₀ _ hm0]
  have hwe : hermC τ.1 X.Gm w e = B * X.maj z τ e := by
    rw [hB, div_mul_cancel₀ _ hm0]
  have h0e : hermC τ.1 X.Gm (w - A • e - B • X.jp z τ e) e = 0 := by
    rw [hermC_Gm_sub_left X τ hz, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_smul_left X τ hz, hee, hfe,
      hwe]
    ring
  have h0f : hermC τ.1 X.Gm (w - A • e - B • X.jp z τ e) (X.jp z τ e) = 0 := by
    rw [hermC_Gm_sub_left X τ hz, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_smul_left X τ hz, hef, hff,
      hwf]
    ring
  have hw : w = (w - A • e - B • X.jp z τ e) + A • e + B • X.jp z τ e := by abel
  have hBw : Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w =
      (w - A • e - B • X.jp z τ e) + ((σ : ℂ)⁻¹ * A) • e + ((σ : ℂ) * B) • X.jp z τ e := by
    rw [boost_mulVec, hwf, hwe]
    have c1 : (((σ⁻¹ - 1) / X.maj z τ e : ℝ) : ℂ) * (A * (X.maj z τ e : ℂ)) =
        (σ : ℂ)⁻¹ * A - A := by
      push_cast
      field_simp
    have c2 : (((σ⁻¹⁻¹ - 1) / X.maj z τ e : ℝ) : ℂ) * (B * (X.maj z τ e : ℂ)) =
        (σ : ℂ) * B - B := by
      rw [inv_inv]
      push_cast
      field_simp
    rw [c1, c2, sub_smul, sub_smul]
    abel
  have hmw : X.maj z τ w = X.maj z τ (w - A • e - B • X.jp z τ e) +
      (Complex.normSq A + Complex.normSq B) * X.maj z τ e := by
    rw [← maj_decomp X τ hz hee he0 _ h0e h0f A B, ← hw]
  rw [hBw, maj_decomp X τ hz hee he0 _ h0e h0f, hmw]
  simp only [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal]
  have hM0 := MajorantConjugateTransfer.maj_nonneg (X := X) hz τ (w - A • e - B • X.jp z τ e)
  have hNA := Complex.normSq_nonneg A
  have hNB := Complex.normSq_nonneg B
  have hs0 : 0 < σ * σ := mul_pos hσ hσ
  rw [sq]
  have hk2 : min (σ * σ) (σ * σ)⁻¹ ≤ σ * σ := min_le_left _ _
  have hk3 : min (σ * σ) (σ * σ)⁻¹ ≤ (σ * σ)⁻¹ := min_le_right _ _
  have hk1 : min (σ * σ) (σ * σ)⁻¹ ≤ 1 := by
    rcases le_total (σ * σ) 1 with h | h
    · exact hk2.trans h
    · refine hk3.trans ?_
      have hi : (σ * σ)⁻¹ * (σ * σ) = 1 := inv_mul_cancel₀ hs0.ne'
      have hip : 0 < (σ * σ)⁻¹ := inv_pos.mpr hs0
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hk1 hM0,
    mul_le_mul_of_nonneg_right hk3 (mul_nonneg hNA hm.le),
    mul_le_mul_of_nonneg_right hk2 (mul_nonneg hNB hm.le)]

end BoostLowerBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ImaginaryMajorants

open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds

variable {r : ℕ} (X : Data E r)

theorem jp_col {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.jp z τ (X.colP z τ d) = X.colP z τ d := by
  have hP : X.ppos z τ (X.colP z τ d) = X.colP z τ d := by
    have h := X.ppos_eq_of z τ (X.gramPos_det_ne hz τ) (X.colP z τ d)
      (fun a => if a = d then 1 else 0) (fun b => by
        rw [show (∑ a, (if a = d then (1 : ℂ) else 0) • col (mat z τ) (Fin.castLE X.p0_le a)) =
          X.colP z τ d by simp [Data.colP]]
        rw [sub_self, hermC_zero_left])
    rw [h]
    simp [Data.colP]
  simp only [Data.jp, hP]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem maj_imag_eq {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w = X.maj z τ (Matrix.mulVec
      (boost X τ (Data.emb τ.1 ξ) (X.jp z τ (Data.emb τ.1 ξ)) (X.maj z τ (Data.emb τ.1 ξ))
        (Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)))⁻¹) w) := by
  set e := Data.emb τ.1 ξ with he_def
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  set f := X.jp z τ e with hf_def
  set m := X.maj z τ e with hm_def
  set q := 1 + X.c τ * b τ * m with hq_def
  set σ := Real.sqrt q with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.mpr hq
  have hσ2 : σ ^ 2 = q := Real.sq_sqrt hq.le
  set T := X.flowMat ξ τ (I * (b τ : ℂ))
  have hT : ∀ v, Matrix.mulVec T v = v + (((X.c τ * b τ : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • e := by
    intro v
    rw [Data.flowMat_mulVec]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcb : X.c τ * b τ = (σ ^ 2 - 1) / m := by
    rw [hσ2, hq_def]; field_simp; ring
  set B := boost X τ e f m σ
  set B' := boost X τ e f m σ⁻¹
  set P := X.ppos z τ e with hP_def
  set γ : Fin X.p0 → ℂ := fun j => ∑ b, hermC τ.1 X.Gm e (X.colP z τ b) * (X.gramPos z τ)⁻¹ b j
  have hPsum : P = ∑ j, γ j • X.colP z τ j := rfl
  have hPef : P = (1 / 2 : ℂ) • (e + f) := by
    funext k
    simp only [hf_def, Data.jp, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, ← hP_def]
    ring
  have hPe : hermC τ.1 X.Gm P e = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hee, hfe]; push_cast; ring
  have hPf : hermC τ.1 X.Gm P f = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hef, hff]; push_cast; ring
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hcol : ∀ d, Matrix.mulVec T (X.colP z τ d) = X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d := by
    intro d
    rw [show X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d = col (mat (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ) (Fin.castLE X.p0_le d) from rfl, Data.col_flow]
    rfl
  have hzf : ∀ d, hermC τ.1 X.Gm (X.colP z τ d) f = hermC τ.1 X.Gm (X.colP z τ d) e := by
    intro d; rw [hf_def, ← X.hermC_jp_left hz, jp_col X hz τ d]

  have hi : ∀ d, Matrix.mulVec T (X.colP z τ d) = Matrix.mulVec B (X.colP z τ d) +
      (((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec B P := by
    intro d
    rw [hT, boost_mulVec, boost_mulVec, hzf, hPe, hPf, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hii : ∀ d, Matrix.mulVec B (X.colP z τ d) = Matrix.mulVec T (X.colP z τ d) -
      (((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec T P := by
    intro d
    rw [hT, hT, boost_mulVec, hzf, hPe, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a = ∑ c, L c • Matrix.mulVec B (X.colP z τ c) := by
    intro a
    refine ⟨fun j => (if j = a then 1 else 0) +
      ((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ a) e / m) * γ j, ?_⟩
    rw [← hcol, hi, hPsum, Data.mulVec_lin]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum]
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec B (X.colP z τ c) = ∑ a, K a • X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a := by
    intro c
    refine ⟨fun j => (if j = c then 1 else 0) -
      ((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ c) e / m) * γ j, ?_⟩
    rw [hii, hPsum, Data.mulVec_lin]
    simp only [hcol, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum]
  have hmt := maj_transfer X hz hy τ B B' (boost_comp X τ hm hee hff hef hfe hσ)
    (boost_isom X τ hm hee hff hef hfe hσ) H1 H2 w
  exact hmt

theorem maj_imag_flow {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    min (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ))⁻¹ *
      X.maj z τ w ≤ X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w := by
  rw [maj_imag_eq X hz ξ b hy τ hee he0 hq w]
  have hσ : 0 < Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq
  have h := boost_lower (X := X) (z := z) (τ := τ) (e := Data.emb τ.1 ξ) hz hee he0 hσ w
  rwa [Real.sq_sqrt hq.le] at h

end ImaginaryMajorants

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem majorant_realFlow_transfer {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by

  have hcol : ∀ c, Matrix.mulVec (X.flowMat ξ τ (t τ : ℂ)) (X.colP x τ c) =
      X.colP (X.flow ξ (fun τ => (t τ : ℂ)) x) τ c := by
    intro c
    unfold Data.colP
    rw [Data.col_flow]
  refine maj_transfer (hx := hx) (hy := hz) (τ := τ) (g := X.flowMat ξ τ (t τ : ℂ))
    (g' := X.flowMat ξ τ (-(t τ : ℂ))) (hgg' := fun w => flowMat_inv (hiso := hiso) (a := _) (w := w))
    (hiso := fun u v => flowMat_isom_real (hiso := hiso) (t := t τ) (u := u) (v := v))
    (H1 := ?_) (H2 := ?_) (w := w)
  · intro c
    refine ⟨fun a => if a = c then 1 else 0, ?_⟩
    rw [hcol c]
    simp [ite_smul]
  · intro a
    refine ⟨fun c => if c = a then 1 else 0, ?_⟩
    simp [ite_smul, hcol]

end ReciprocityTheory.ChartRestriction.G.FD
