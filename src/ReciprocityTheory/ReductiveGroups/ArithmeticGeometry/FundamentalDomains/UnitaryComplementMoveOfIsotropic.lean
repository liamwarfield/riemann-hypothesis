module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

section onetau

variable (ξ : Fin r → E) (τ : X.Ψ)

private theorem flowMat_mulVec' (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v - (I * X.c τ * s * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  ext a
  simp only [Matrix.mulVec, dotProduct, flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hermC_sub_const_smul_right (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (w v e : Fin r → ℂ) (k : ℂ) :
    hermC σ G w (v - k • e) = hermC σ G w v - conj k * hermC σ G w e := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  ring

lemma flow_fix (s : ℂ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (emb τ.1 ξ) = 0) :
    Matrix.mulVec (X.flowMat ξ τ s) v = v := by
  rw [flowMat_mulVec', hv, mul_zero, zero_smul, sub_zero]

lemma hC_right_flow (s : ℂ) (y v : Fin r → ℂ) (hy : hermC τ.1 X.Gm y (emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm y (Matrix.mulVec (X.flowMat ξ τ s) v) = hermC τ.1 X.Gm y v := by
  rw [flowMat_mulVec', hermC_sub_const_smul_right, hy, mul_zero, sub_zero]

lemma col_flow (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (a : Fin r) :
    col (mat (X.flow ξ s x) τ) a = Matrix.mulVec (X.flowMat ξ τ (s τ)) (col (mat x τ) a) := by
  ext k
  rfl

lemma mulVec_lin (M : Matrix (Fin r) (Fin r) ℂ) {n : ℕ} (β : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    Matrix.mulVec M (∑ a, β a • v a) = ∑ a, β a • Matrix.mulVec M (v a) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma ppos_flow {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom)
    (u : Fin r → ℂ) (hu : hermC τ.1 X.Gm u (emb τ.1 ξ) = 0)
    (hp : hermC τ.1 X.Gm (X.ppos x τ u) (emb τ.1 ξ) = 0) :
    X.ppos (X.flow ξ s x) τ u = X.ppos x τ u := by
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a with hα
  have hpx : X.ppos x τ u = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hT : ∑ a, α a • col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a) = X.ppos x τ u := by
    simp only [col_flow]
    rw [← mulVec_lin, ← hpx, flow_fix X ξ τ _ _ hp]
  rw [← hT]
  apply ppos_eq_of X (X.flow ξ s x) τ (gramPos_det_ne X hxs τ) u α
  intro b
  rw [hT, col_flow, hC_right_flow]
  · exact ppos_orth X x τ (gramPos_det_ne X hx τ) u b
  · rw [hC_sub_left, hu, hp, sub_zero]

end onetau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma ppos_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma ppos_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.ppos x τ 0 = 0 := by
  have := ppos_smul X x τ 0 0
  simpa using this

lemma ppos_selfadj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hA := gramPos_det_ne X hx τ
  have hsymm : ∀ v v', hermC τ.1 X.Gm v v' = conj (hermC τ.1 X.Gm v' v) := fun v v' =>
    hC_symm τ.1 X.Gm X.Gm_herm v' v

  have hspan : ∀ (y v : Fin r → ℂ), (∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) →
      hermC τ.1 X.Gm (X.ppos x τ v) y = 0 := by
    intro y v hy
    unfold ppos
    rw [hC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hC_smul_left, hsymm, hy a, map_zero, mul_zero]
  have h1 : hermC τ.1 X.Gm (X.ppos x τ u) (w - X.ppos x τ w) = 0 :=
    hspan (w - X.ppos x τ w) u (ppos_orth X x τ hA w)
  have h2 : hermC τ.1 X.Gm (u - X.ppos x τ u) (X.ppos x τ w) = 0 :=
    hspan (u - X.ppos x τ u) w (ppos_orth X x τ hA u) |> fun h => by rw [hsymm, h, map_zero]
  have e1 : hermC τ.1 X.Gm (X.ppos x τ u) w =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : w = X.ppos x τ w + (w - X.ppos x τ w) := by abel
    conv_lhs => rw [this]
    rw [hC_add_right, h1, add_zero]
  have e2 : hermC τ.1 X.Gm u (X.ppos x τ w) =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : u = X.ppos x τ u + (u - X.ppos x τ u) := by abel
    conv_lhs => rw [this]
    rw [hC_add_left, h2, add_zero]
  rw [e1, e2]

lemma Hf_eq (x : Frame X.Ψ r) (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
  have hneg : hermC τ.1 X.Gm u (-w) = - hermC τ.1 X.Gm u w := by
    have := hC_smul_right τ.1 X.Gm (-1) u w
    simpa using this
  calc X.Hf x τ u w = 2 * hermC τ.1 X.Gm u (X.ppos x τ w) - hermC τ.1 X.Gm u w := by
        simp only [Hf]; rw [hC_sub_left, hC_smul_left, ppos_selfadj X hx]
    _ = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
        rw [sub_eq_add_neg ((2 : ℂ) • X.ppos x τ w) w, hC_add_right, hC_smul_right, hneg, map_ofNat]
        ring

section unitary

variable (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
  (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)

include hg

lemma gram_unitary : gram τ.1 X.Gm (g * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

lemma ppos_unitary (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.ppos (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g v) = Matrix.mulVec g (X.ppos x τ v) := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = Matrix.mulVec g (col (mat x τ) a) := by
    intro a; exact col_mul g (mat x τ) a
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    simp only [gramPos]
    rw [show mat (X.lmulC (fun _ => g) x) τ = g * mat x τ from rfl, gram_unitary X x τ g hg]
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a
  have hpx : X.ppos x τ v = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hsum : Matrix.mulVec g (X.ppos x τ v) =
      ∑ a, α a • col (mat (X.lmulC (fun _ => g) x) τ) (Fin.castLE X.p0_le a) := by
    rw [hpx, mulVec_lin]; simp only [hcol]
  rw [hsum]
  apply ppos_eq_of X _ τ (by rw [hgram]; exact gramPos_det_ne X hx τ)
  intro b
  rw [← hsum, hcol, ← Matrix.mulVec_sub, hg]
  exact ppos_orth X x τ (gramPos_det_ne X hx τ) v b

end unitary

theorem unitaryComplementMove_of_isotropic : UnitaryComplementMove (E := E) := by
  intro r X ξ hξ x hx h1 hu hfix _hU
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := fun τ => by
    rw [← emb_herm, hξ.2.1, map_zero]
  set x' := X.lmulC h1 x with hx'
  have hloc : ∀ τ : X.Ψ, X.lmulC h1 x = X.lmulC (fun _ => h1 τ) x ∨ True := fun _ => Or.inr trivial

  have hmat : ∀ τ, mat x' τ = h1 τ * mat x τ := fun τ => rfl
  have hgramτ : ∀ τ, gram τ.1 X.Gm (mat x' τ) = gram τ.1 X.Gm (mat x τ) := fun τ => by
    rw [hmat]; exact gram_unitary X x τ (h1 τ) (hu τ)

  have hfe : ∀ τ, Matrix.mulVec (h1 τ) (emb τ.1 ξ) = emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 1) (fun _ => 0)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, one_smul, zero_smul, ppos_zero, smul_zero,
      sub_zero, add_zero] at h
    exact h
  have hfJ : ∀ τ, Matrix.mulVec (h1 τ) ((2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ) =
      (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 0) (fun _ => -I)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, zero_smul, zero_add, ppos_smul, smul_smul] at h
    have e1 : I • (((2 : ℂ) * -I) • X.ppos x τ (emb τ.1 ξ) - -I • emb τ.1 ξ) =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      rw [smul_sub, smul_smul, smul_smul, show I * (2 * -I) = (2 : ℂ) by
        linear_combination (-2 : ℂ) * Complex.I_mul_I, show I * -I = (1 : ℂ) by
        linear_combination (-1 : ℂ) * Complex.I_mul_I, one_smul]
    rw [e1] at h
    exact h

  have hdom : x' ∈ X.dom := by
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · rw [hmat, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0

      have hrad : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by rw [← hu τ v w, hv]; simp [hermC]
      have hG : (Matrix.map X.Gm τ.1).det ≠ 0 := by
        have h := RingHom.map_det τ.1 X.Gm
        rw [show τ.1.mapMatrix X.Gm = X.Gm.map τ.1 from rfl] at h
        rw [← h]; exact (map_ne_zero _).mpr X.Gm_det
      by_contra hne
      apply hG
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hne, ?_⟩
      funext b
      have := hrad (Pi.single b 1)
      simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.map_apply] using this
    · have : dmin X.Gm x' τ i = dmin X.Gm x τ i := by
        simp only [dmin]; rw [hgramτ]
      rw [this]; exact (hx τ).2 i
  refine ⟨hdom, ?_, ?_, ?_⟩
  ·
    intro u _
    funext τ
    have hJe : (2 : ℂ) • X.ppos x' τ (emb τ.1 ξ) - emb τ.1 ξ =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (emb τ.1 ξ)
      rw [hfe τ] at hp
      rw [show X.ppos x' τ (emb τ.1 ξ) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (emb τ.1 ξ) from rfl, hp]
      rw [← Matrix.mulVec_smul, ← hfe τ, ← Matrix.mulVec_sub, hfe τ, hfJ τ]
    simp only [aproj, lineV]
    rw [Hf_eq X x' hdom, Hf_eq X x' hdom, Hf_eq X x hx, Hf_eq X x hx, hJe]
  · intro τ

    have hpp : X.posPart x' τ (emb τ.1 ξ) = X.posPart x τ (emb τ.1 ξ) := by
      have hgp : X.gramPos x' τ = X.gramPos x τ := by simp only [gramPos]; rw [hgramτ]
      simp only [posPart]
      rw [hgp]
      have hc : ∀ a : Fin X.p0, hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x' τ) (Fin.castLE X.p0_le a)) =
          hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x τ) (Fin.castLE X.p0_le a)) := by
        intro a
        rw [hmat, col_mul]
        conv_lhs => rw [← hfe τ]
        rw [hu τ]
      simp only [hc]
    simp only [maj, hpp]
  · intro u _
    funext τ
    simp only [Jz, applyV]
    have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (u τ)
    rw [show X.ppos x' τ (Matrix.mulVec (h1 τ) (u τ)) =
      X.ppos (X.lmulC (fun _ => h1 τ) x) τ (Matrix.mulVec (h1 τ) (u τ)) from rfl, hp]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]

end Data

theorem unitaryComplementMove : UnitaryComplementMove (E := E) := Data.unitaryComplementMove_of_isotropic

end ReciprocityTheory.ChartRestriction.G.FD
