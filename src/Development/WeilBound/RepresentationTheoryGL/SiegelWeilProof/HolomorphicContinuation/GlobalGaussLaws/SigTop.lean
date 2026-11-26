module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittEq

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtD
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtA
open Matrix NumberField
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_cc (t : E) : FD.cc (FD.cc t) = t := IsCMField.complexConj_apply_apply E t

theorem emb_cc (τ : E →+* ℂ) (t : E) : τ (FD.cc t) = conj (τ t) := IsCMField.complexEmbedding_complexConj E τ t

theorem exists_skew : ∃ θ : E, θ ≠ 0 ∧ FD.cc θ = -θ := by
  by_contra hne
  push Not at hne
  apply IsCMField.complexConj_ne_one E
  ext t
  by_contra ht
  have h1 : t - FD.cc t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply hne _ h1
  show IsCMField.complexConj E (t - FD.cc t) = -(t - FD.cc t)
  rw [map_sub]
  change FD.cc t - FD.cc (FD.cc t) = _
  rw [cc_cc]
  ring

theorem emb_real (τ : E →+* ℂ) {t : E} (ht : FD.cc t = t) : τ t = ((τ t).re : ℂ) := by
  have h := emb_cc τ t
  rw [ht] at h
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem iso_diag {r : ℕ} (g : Fin (r + 1) → E) (hr : 2 ≤ r) (hg : ∀ i, FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ (∃ j, (τ (g j)).re < 0)) :
    ∃ z : Fin (r + 1) → E, z ≠ 0 ∧ z ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ z) = 0 := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_skew (E := E)
  have hF : ∀ t : E, IsCMField.complexConj E t = t ↔ ∃ s : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E s = t :=
    fun t => (IsCMField.complexConj_eq_self_iff E t).trans ⟨fun h => ⟨⟨t, h⟩, rfl⟩, by rintro ⟨s, rfl⟩; exact s.2⟩
  have hne : ∀ (τ : E →+* ℂ) (i : Fin (r + 1)), (τ (g i)).re ≠ 0 := by
    intro τ i h
    have h1 := emb_real τ (hg i)
    rw [h, Complex.ofReal_zero] at h1
    exact hg0 i ((map_eq_zero τ).1 h1)
  obtain ⟨z, hz⟩ := GlobalTheory.HermGlobal.exists_represent (σ := IsCMField.complexConj E) (IsCMField.complexConj_apply_apply E) hF
    hθ0 hθ hr (g := fun i => g i.succ) (fun i => hg _) (fun i => hg0 _) (b := -g 0)
    (by show IsCMField.complexConj E (-g 0) = -g 0; rw [map_neg]; exact congrArg Neg.neg (hg 0))
    (neg_ne_zero.mpr (hg0 0)) (by
      intro τ _
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hs τ
      have hb : (τ (-g 0)).re = -(τ (g 0)).re := by simp
      rcases lt_or_gt_of_ne (hne τ 0) with h0 | h0
      ·
        have hi0 : i ≠ 0 := by rintro rfl; linarith
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
        exact ⟨i', by simp only [hb]; constructor <;> intro _ <;> linarith⟩
      · have hj0 : j ≠ 0 := by rintro rfl; linarith
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
        exact ⟨j', by simp only [hb]; constructor <;> intro h <;> linarith⟩)
  refine ⟨Fin.cons 1 z, fun h => one_ne_zero (congrFun h 0), ?_⟩
  have key : (Fin.cons 1 z : Fin (r + 1) → E) ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ Fin.cons 1 z) =
      g 0 + z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) := by
    simp only [dotProduct, mulVec_diagonal, Fin.sum_univ_succ, Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    have : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
    rw [this]
    ring
  rw [key]
  have hz' : z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) = -g 0 := hz
  rw [hz']
  ring

end PositivityTheory.Rg.Sw.Glob.WLt
end

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev hf {n : Type} [Fintype n] (G : Matrix n n E) (x y : n → E) : E := x ⬝ᵥ G *ᵥ (FD.cc ∘ y)

theorem cc_mulVec {n m : Type} [Fintype n] [Fintype m] (P : Matrix n m E) (y : m → E) :
    FD.cc ∘ (P *ᵥ y) = P.map FD.cc *ᵥ (FD.cc ∘ y) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mulVec, dotProduct, FD.cc, map_sum, map_mul]

theorem hf_congr {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (P : Matrix n m E) (x y : m → E) :
    hf (Pᵀ * G * P.map FD.cc) x y = hf G (P *ᵥ x) (P *ᵥ y) := by
  simp only [hf]
  rw [cc_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem hf_submatrix {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (e : m ≃ n) (x y : m → E) :
    hf (G.submatrix e e) x y = hf G (x ∘ e.symm) (y ∘ e.symm) := by
  simp only [hf, submatrix_mulVec_equiv, Function.comp_def, Equiv.symm_symm]
  rw [dotProduct, dotProduct, ← Equiv.sum_comp e (fun i => x (e.symm i) * _)]
  simp

theorem hf_symm {n : Type} [Fintype n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a) (x y : n → E) :
    hf G y x = FD.cc (hf G x y) := by
  have hc : ∀ s : Finset n, ∀ f : n → E, FD.cc (∑ i ∈ s, f i) = ∑ i ∈ s, FD.cc (f i) :=
    fun s f => map_sum (IsCMField.complexConj E) f s
  have hm : ∀ a b : E, FD.cc (a * b) = FD.cc a * FD.cc b := fun a b => map_mul (IsCMField.complexConj E) a b
  simp only [hf, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, hc, hm, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_left {n : Type} [Fintype n] (G : Matrix n n E) (x x' y : n → E) :
    hf G (x + x') y = hf G x y + hf G x' y := by simp [hf, add_dotProduct]

theorem hf_smul_left {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G (a • x) y = a * hf G x y := by simp [hf, smul_dotProduct]

theorem hf_add_right {n : Type} [Fintype n] (G : Matrix n n E) (x y y' : n → E) :
    hf G x (y + y') = hf G x y + hf G x y' := by
  have h : FD.cc ∘ (y + y') = FD.cc ∘ y + FD.cc ∘ y' :=
    funext fun i => map_add (IsCMField.complexConj E) (y i) (y' i)
  simp only [hf, h, mulVec_add, dotProduct_add]

theorem hf_smul_right {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G x (a • y) = FD.cc a * hf G x y := by
  have h : FD.cc ∘ (a • y) = FD.cc a • (FD.cc ∘ y) :=
    funext fun i => map_mul (IsCMField.complexConj E) a (y i)
  simp only [hf, h, mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem exists_isotropic_of_three_le_of_indefinite {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ m)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : Fin m → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨P, d, hP, hPd, hdr, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hsig : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (d i)).re) ∧ ∃ j, (τ (d j)).re < 0 := by
    intro τ
    obtain ⟨h1, h2⟩ := hs τ
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd] at h1
    have hPd' : Pᵀ * (-G) * P.map FD.cc = diagonal (-d) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hPd, diagonal_neg]
      rfl
    have hneg : (-G).map τ = -(G.map τ) := by
      ext i j
      simp
    have h2' : 1 ≤ posIndex ((-G).map τ) := by
      rwa [hneg, posIndex_neg]
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd'] at h2'
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
    obtain ⟨j, hj⟩ := Finset.card_pos.mp h2'
    refine ⟨⟨i, by simpa using hi⟩, ⟨j, ?_⟩⟩
    simpa using hj
  obtain ⟨z, hz, hz0⟩ := iso_diag d (by omega) hdr (hd0 hd) hsig
  refine ⟨P *ᵥ z, fun h => hz (eq_zero_of_mulVec_eq_zero hP h), ?_⟩
  rw [← hf_congr, hPd]
  exact hz0

theorem iso_gen {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ Fintype.card n)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : n → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card n) ≃ n) := ⟨(Fintype.equivFin n).symm⟩
  obtain ⟨z, hz, hz0⟩ := exists_isotropic_of_three_le_of_indefinite (G.submatrix e e) (fun a b => hG _ _)
    (by rwa [det_submatrix_equiv_self]) h3
    (fun τ => by rw [← submatrix_map, posIndex_submatrix_equiv, negIndex_submatrix_equiv]; exact hs τ)
  refine ⟨z ∘ e.symm, ?_, ?_⟩
  · intro h
    apply hz
    funext i
    simpa using congrFun h (e i)
  · rw [← hf_submatrix]
    exact hz0

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem cc_one : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

theorem cc_zero : FD.cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

theorem cc_neg (t : E) : FD.cc (-t) = -FD.cc t := map_neg (IsCMField.complexConj E) t

theorem cc_div_two (t : E) : FD.cc (t / 2) = FD.cc t / 2 := by
  show IsCMField.complexConj E (t / 2) = _
  rw [map_div₀, map_ofNat]
  rfl

theorem exists_pair {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ w : n → E, hf G z w = 1 ∧ hf G w w = 0 := by
  have hu : z ᵥ* G ≠ 0 := by
    intro h
    apply hz0
    have h1 := congrArg (· ᵥ* G⁻¹) h
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h1
    rwa [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det G).1 ((Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit)),
      Matrix.vecMul_one] at h1
  obtain ⟨b, hb⟩ : ∃ b, (z ᵥ* G) b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  set c := (z ᵥ* G) b with hc
  let v : n → E := c⁻¹ • Pi.single b 1
  let w0 : n → E := FD.cc ∘ v
  have hw0 : hf G z w0 = 1 := by
    have e1 : FD.cc ∘ w0 = v := by ext i; exact cc_cc (v i)
    simp only [hf]
    rw [e1, Matrix.dotProduct_mulVec]
    simp only [v, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hb
  set a := hf G w0 w0 with ha
  have haa : FD.cc a = a := by rw [ha, ← hf_symm hG]
  refine ⟨w0 + (-(a / 2)) • z, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hz, hw0]; ring
  · have hzw : hf G w0 z = 1 := by rw [hf_symm hG, hw0, cc_one]
    rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right, hf_smul_right, hz, hw0, hzw,
      cc_neg, cc_div_two, haa, ← ha]
    ring


set_option maxHeartbeats 1600000 in
theorem split {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ (m : ℕ) (e : Fin 2 ⊕ Fin m ≃ n) (G2 : Matrix (Fin m) (Fin m) E) (P : Matrix n n E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm ∧ (∀ a b, FD.cc (G2 a b) = G2 b a) ∧
        G2.det ≠ 0 := by
  obtain ⟨w, hzw, hww⟩ := exists_pair hG hd hz0 hz
  have hwz : hf G w z = 1 := by rw [hf_symm hG, hzw, cc_one]
  let L : (n → E) →ₗ[E] (Fin 2 → E) :=
    { toFun := fun x => ![hf G x z, hf G x w]
      map_add' := fun x y => by ext i; fin_cases i <;> simp [hf_add_left]
      map_smul' := fun t x => by ext i; fin_cases i <;> simp [hf_smul_left] }
  have hLz : L z = ![0, 1] := by ext i; fin_cases i <;> simp [L, hz, hzw]
  have hLw : L w = ![1, 0] := by ext i; fin_cases i <;> simp [L, hwz, hww]
  have hLs : Function.Surjective L := by
    intro v
    refine ⟨v 0 • w + v 1 • z, ?_⟩
    rw [map_add (f := _), map_smul, map_smul, hLz, hLw]
    ext i; fin_cases i <;> simp
  set K := LinearMap.ker L
  have hrk : Module.finrank E K + 2 = Fintype.card n := by
    show Module.finrank E (LinearMap.ker L) + 2 = _
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLs, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h
    omega
  set m := Module.finrank E K
  let bK : Module.Basis (Fin m) E K := Module.finBasis E K
  have hK : ∀ i, hf G (bK i : n → E) z = 0 ∧ hf G (bK i : n → E) w = 0 := by
    intro i
    have h := (bK i).2
    rw [LinearMap.mem_ker] at h
    exact ⟨congrFun h 0, congrFun h 1⟩
  let cols : Fin 2 ⊕ Fin m → (n → E) := Sum.elim ![z, w] fun i => (bK i : n → E)
  have hcard : Fintype.card (Fin 2 ⊕ Fin m) = Fintype.card n := by simp; omega
  let e : Fin 2 ⊕ Fin m ≃ n := Fintype.equivOfCardEq hcard
  let G2 : Matrix (Fin m) (Fin m) E := fun i j => hf G (bK i : n → E) (bK j : n → E)
  let P : Matrix n n E := fun k j => cols (e.symm j) k
  have hentry : ∀ s t, hf G (cols s) (cols t) = fromBlocks hyp 0 0 G2 s t := by
    rintro (i | i) (j | j)
    · fin_cases i <;> fin_cases j <;> simp [cols, hyp, hz, hzw, hwz, hww]
    · fin_cases i
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) z, (hK j).1, cc_zero]
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) w, (hK j).2, cc_zero]
    · fin_cases j
      · simp [cols, (hK i).1]
      · simp [cols, (hK i).2]
    · rfl
  have hT : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm := by
    ext a b
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply]
    exact hentry (e.symm a) (e.symm b)
  have hlin : ∀ (γ : Fin 2 ⊕ Fin m → E) (y : n → E),
      hf G (∑ s, γ s • cols s) y = ∑ s, γ s * hf G (cols s) y := by
    intro γ y
    let Ly : (n → E) →ₗ[E] E :=
      { toFun := fun x => hf G x y
        map_add' := fun x x' => hf_add_left G x x' y
        map_smul' := fun t x => hf_smul_left G t x y }
    have h1 : hf G (∑ s, γ s • cols s) y = Ly (∑ s, γ s • cols s) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  have hP : P.det ≠ 0 := by
    have hinj : Function.Injective P.mulVec := by
      intro α β hαβ
      have h0 : P *ᵥ (α - β) = 0 := by rw [Matrix.mulVec_sub, hαβ, sub_self]
      set γ : n → E := α - β with hγ
      have hsum : ∑ s, γ (e s) • cols s = 0 := by
        rw [← h0]
        ext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, P]
        rw [← e.sum_comp]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Equiv.symm_apply_apply]
        ring
      have hz1 : γ (e (Sum.inl 1)) = 0 := by
        have h := hlin (fun s => γ (e s)) z
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) z = γ (e (Sum.inl 1)) := by
          have hc : ∀ s, hf G (cols s) z = fromBlocks hyp 0 0 G2 s (Sum.inl 0) := fun s => hentry s (Sum.inl 0)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hw1 : γ (e (Sum.inl 0)) = 0 := by
        have h := hlin (fun s => γ (e s)) w
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) w = γ (e (Sum.inl 0)) := by
          have hc : ∀ s, hf G (cols s) w = fromBlocks hyp 0 0 G2 s (Sum.inl 1) := fun s => hentry s (Sum.inl 1)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hrest : ∑ i, γ (e (Sum.inr i)) • bK i = 0 := by
        apply Subtype.ext
        have := hsum
        simp only [Fintype.sum_sum_type, Fin.sum_univ_two, hz1, hw1, zero_smul, zero_add] at this
        simpa [cols] using this
      have hcoef := (Fintype.linearIndependent_iff.1 bK.linearIndependent) _ hrest
      have hγ0 : γ = 0 := by
        funext k
        obtain ⟨s, rfl⟩ := e.surjective k
        rcases s with i | i
        · fin_cases i
          · exact hw1
          · exact hz1
        · exact hcoef i
      have := congrFun hγ0
      funext k
      have hk := this k
      simp only [hγ, Pi.sub_apply, Pi.zero_apply] at hk
      exact sub_eq_zero.mp hk
    have hu : IsUnit P := Matrix.mulVec_injective_iff_isUnit.1 hinj
    exact ((Matrix.isUnit_iff_isUnit_det P).1 hu).ne_zero
  have hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a := fun a b => (hf_symm hG _ _).symm
  have hdetP : (P.map FD.cc).det ≠ 0 := by
    have : (P.map FD.cc).det = IsCMField.complexConj E P.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) P).symm
    rw [this]
    exact (map_ne_zero _).2 hP
  have hdetT : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).det ≠ 0 := by
    rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hP hd) hdetP
  have hG2d : G2.det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hdetT
    intro h
    rw [h, mul_zero] at hdetT
    exact hdetT rfl
  exact ⟨m, e, G2, P, hP, hT, hG2, hG2d⟩

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hyp_map (τ : E →+* ℂ) : (hyp : Matrix (Fin 2) (Fin 2) E).map τ = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyp]

theorem index_hyp (τ : E →+* ℂ) :
    posIndex ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) = 1 ∧ negIndex ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) = 1 := by
  rw [hyp_map]
  have hP : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    norm_num
  have hD : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * !![0, 1; 1, 0] *
      (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = diagonal ![2, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [posIndex_eq_card_of_congr_diagonal hP hD, Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext k
    fin_cases k <;> simp
  · rw [negIndex_eq_card_of_congr_diagonal hP hD, Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp

theorem hf_blocks {m : ℕ} (G2 : Matrix (Fin m) (Fin m) E) (u u' : Fin 2 ⊕ Fin m → E) :
    hf (fromBlocks hyp 0 0 G2) u u' = hf hyp (u ∘ Sum.inl) (u' ∘ Sum.inl) + hf G2 (u ∘ Sum.inr) (u' ∘ Sum.inr) := by
  simp only [hf]
  rw [fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Function.comp_def]

private theorem posIndex_negIndex_eq_one_add_of_hyperbolic_split {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} {G : Matrix n n E}
    {G2 : Matrix (Fin m) (Fin m) E} {P : Matrix n n E} (e : Fin 2 ⊕ Fin m ≃ n) (hP : P.det ≠ 0)
    (hPG : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm)
    (hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a) (τ : E →+* ℂ) :
    posIndex (G.map τ) = 1 + posIndex (G2.map τ) ∧ negIndex (G.map τ) = 1 + negIndex (G2.map τ) := by
  have hQ : (P.map τ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 hP
  have hmap : (P.map τ)ᵀ * G.map τ * (P.map τ).map (starRingEnd ℂ) =
      ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).map τ := by
    rw [← hPG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext i j
    simp [emb_cc]
  have hH1 : ((hyp : Matrix (Fin 2) (Fin 2) E).map τ).IsHermitian := by
    rw [hyp_map]
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hH2 : (G2.map τ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.map_apply]
    rw [← starRingEnd_apply, ← emb_cc, hG2]
  have hblk : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).map τ =
      (fromBlocks ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) 0 0 (G2.map τ)).submatrix e.symm e.symm := by
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
    simp
  obtain ⟨h1, h2⟩ := index_hyp (E := E) τ
  constructor
  · rw [← posIndex_congr (G.map τ) hQ, hmap, hblk, posIndex_submatrix_equiv,
      posIndex_fromBlocks hH1 hH2, h1]
  · rw [← negIndex_congr (G.map τ) hQ, hmap, hblk, negIndex_submatrix_equiv,
      negIndex_fromBlocks hH1 hH2, h2]


set_option maxHeartbeats 1600000 in
theorem main_iso : ∀ (k : ℕ) {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E),
    (∀ a b, FD.cc (G a b) = G b a) → G.det ≠ 0 → 2 * k < Fintype.card n →
    (∀ τ : E →+* ℂ, k ≤ posIndex (G.map τ) ∧ k ≤ negIndex (G.map τ)) →
    ∃ W : Submodule E (n → E), Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, hf G x y = 0 := fun
  | 0 => by
    intro G _ _ _ _
    refine ⟨⊥, by simp, ?_⟩
    intro x hx y hy
    rw [Submodule.mem_bot] at hx
    subst hx
    simp [hf]
  | k + 1 => by
    rename_i n _ _
    intro G hG hdet hcard hidx
    have h3 : 3 ≤ Fintype.card n := by omega
    obtain ⟨z, hz, hzz⟩ := iso_gen G hG hdet h3 (fun τ =>
      ⟨le_trans (Nat.le_add_left 1 k) (hidx τ).1, le_trans (Nat.le_add_left 1 k) (hidx τ).2⟩)
    obtain ⟨m, e, G2, P, hP, hPG, hG2, hdet2⟩ := split hG hdet hz hzz
    have hm := Fintype.card_congr e
    simp at hm
    obtain ⟨W2, hW2r, hW2⟩ := main_iso k G2 hG2 hdet2 (by simp; omega) (fun τ => by
      obtain ⟨h1, h2⟩ := posIndex_negIndex_eq_one_add_of_hyperbolic_split e hP hPG hG2 τ
      obtain ⟨h4, h5⟩ := hidx τ
      exact ⟨by omega, by omega⟩)
    let ψ : E × W2 →ₗ[E] (Fin 2 ⊕ Fin m → E) :=
      { toFun := fun p => Sum.elim ![p.1, 0] (p.2 : Fin m → E)
        map_add' := by
          intro p q
          ext (i | i)
          · fin_cases i <;> simp
          · simp
        map_smul' := by
          intro c p
          ext (i | i)
          · fin_cases i <;> simp
          · simp }
    let L : (Fin 2 ⊕ Fin m → E) →ₗ[E] (n → E) := P.mulVecLin ∘ₗ LinearMap.funLeft E E e.symm
    have hLapp : ∀ u, L u = P *ᵥ (u ∘ e.symm) := fun u => rfl
    have hψ : Function.Injective ψ := by
      intro p q hpq
      have h1 := congrFun hpq (Sum.inl 0)
      have h2 : ∀ i, (p.2 : Fin m → E) i = (q.2 : Fin m → E) i := fun i => congrFun hpq (Sum.inr i)
      simp [ψ] at h1
      exact Prod.ext h1 (Subtype.ext (funext h2))
    have hL : Function.Injective L := by
      have hu : Function.Injective P.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP))
      exact hu.comp (LinearMap.funLeft_injective_of_surjective E E _ e.symm.surjective)
    have hinj : Function.Injective (L ∘ₗ ψ) := by
      rw [LinearMap.coe_comp]
      exact hL.comp hψ
    have key : ∀ u u' : Fin 2 ⊕ Fin m → E, hf G (L u) (L u') = hf (fromBlocks hyp 0 0 G2) u u' := by
      intro u u'
      have := hf_congr G P (u ∘ e.symm) (u' ∘ e.symm)
      rw [hPG, hf_submatrix] at this
      rw [hLapp, hLapp]
      simpa [Function.comp_def] using this.symm
    refine ⟨LinearMap.range (L ∘ₗ ψ), ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self, hW2r]
      ring
    · intro x hx y hy
      obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
      obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hy
      show hf G (L (ψ p)) (L (ψ q)) = 0
      rw [key, hf_blocks]
      have e1 : ∀ r : E × W2, (ψ r ∘ Sum.inl) = ![r.1, 0] := by
        intro r
        funext i
        simp [ψ]
      have e2 : ∀ r : E × W2, (ψ r ∘ Sum.inr) = (r.2 : Fin m → E) := by
        intro r
        funext i
        simp [ψ]
      rw [e1, e2, e1, e2, hW2 _ p.2.2 _ q.2.2]
      simp [hf, hyp, dotProduct, mulVec, Fin.sum_univ_two]

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

noncomputable section

open scoped Matrix ComplexConjugate
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Inertia NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open ReciprocityTheory.ChartRestriction.G

set_option maxHeartbeats 1600000 in
theorem wittLBlt : WittLBlt := by
  intro D V k hk hS
  letI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hσ : ∀ x : D.host.E, D.sp.cm.sig x = FD.cc x := fun x => rfl
  have hT : ∀ a b, FD.cc (V.gram a b) = V.gram b a := fun a b => by rw [← hσ]; exact hH.1 b a
  have hTt : V.gramᵀ = V.gram.map FD.cc := Matrix.ext fun a b => (hT a b).symm
  have hG : ∀ a b, FD.cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => by
    simp only [transpose_apply]; exact hT b a
  have hd : V.gramᵀ.det ≠ 0 := by rw [det_transpose]; exact hH.2

  have hsigτ : ∀ τ0 : D.what₂.Tau, k ≤ posIndex (V.gram.map (tauE D τ0)) ∧ k ≤ negIndex (V.gram.map (tauE D τ0)) := by
    intro τ0
    obtain ⟨ε, fr, hu, hfr, hp, hq⟩ := hS τ0
    have hP : (fr.map (starRingEnd ℂ)).det ≠ 0 := by
      have : (fr.map (starRingEnd ℂ)).det = starRingEnd ℂ fr.det := (RingHom.map_det (starRingEnd ℂ) fr).symm
      rw [this]
      exact (map_ne_zero _).2 hu.ne_zero
    have hd' : (fr.map (starRingEnd ℂ))ᵀ * V.gram.map (tauE D τ0) * (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
        diagonal (PositivityTheory.Rg.Sw.sgn ε) := by
      have h1 : (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) = fr := by
        ext a b; simp
      rw [h1]
      exact hfr
    rw [posIndex_eq_card_of_congr_diagonal hP hd', negIndex_eq_card_of_congr_diagonal hP hd']
    have e1 : (Finset.univ.filter fun a => 0 < (PositivityTheory.Rg.Sw.sgn ε a).re) = Finset.univ.filter fun a => ε a = true := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    have e2 : (Finset.univ.filter fun a => (PositivityTheory.Rg.Sw.sgn ε a).re < 0) = Finset.univ.filter fun a => ε a = false := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    rw [e1, e2]
    exact ⟨hp, hq⟩
  have hsig : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gram.map φ) ∧ k ≤ negIndex (V.gram.map φ) := by
    intro φ
    obtain ⟨τ0, h | h⟩ := Formalism.L2.Fam.ThC.tauE_or (D := D) φ
    · rw [← h]; exact hsigτ τ0
    · have hφ : φ = ComplexEmbedding.conjugate (tauE D τ0) := by rw [h]; exact (star_star φ).symm
      rw [hφ, posIndex_map_conjugate _ hT, negIndex_map_conjugate _ hT]
      exact hsigτ τ0
  have hsigT : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gramᵀ.map φ) ∧ k ≤ negIndex (V.gramᵀ.map φ) := by
    intro φ
    have hm : V.gramᵀ.map φ = V.gram.map (ComplexEmbedding.conjugate φ) := by
      rw [hTt]
      ext a b
      simp only [Matrix.map_apply]
      exact WLt.emb_cc φ _
    rw [hm]
    exact hsig _
  obtain ⟨W, hWr, hW⟩ := WLt.main_iso k V.gramᵀ hG hd (by simpa using hk) hsigT
  rw [← GlobalTheory.SiegelWeilLitCompare.wittIdx_eq]
  refine le_csSup ⟨V.rank, ?_⟩ ⟨W, fun x hx y hy => ?_, hWr⟩
  · rintro r ⟨W', -, rfl⟩
    exact (Submodule.finrank_le W').trans (by simp)
  · have h := hW y hy x hx
    simp only [WLt.hf, dotProduct, mulVec, Function.comp_apply] at h
    show ∑ i, ∑ j, FD.cc (x i) * V.gram i j * y j = 0
    rw [Finset.sum_comm, ← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show FD.cc (x b) * V.gram b a * y a = y a * (V.gram b a * FD.cc (x b))
    ring

end PositivityTheory.Rg.Sw.Glob

end
end

namespace PositivityTheory.Rg.Sw.Glob

theorem sigOK : SigOK := sigOK_of wittLBlt wittLBeq

end PositivityTheory.Rg.Sw.Glob
