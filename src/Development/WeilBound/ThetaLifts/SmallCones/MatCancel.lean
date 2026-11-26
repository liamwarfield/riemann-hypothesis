module

public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ColsOfMul
set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKCT.Fr

open Matrix

variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

def fr (ι : Matrix d e R) (x y : d → R) : Matrix d (e ⊕ Fin 2) R := fromCols ι (of fun i j => ![x i, y i] j)

def gr (ε : R) (J₁ : Matrix e e R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks J₁ 0 0 !![0, 1; ε, 0]

structure IsFr (c : R →+* R) (ε : R) (J : Matrix d d R) (J₁ : Matrix e e R) (ι : Matrix d e R) (x y : d → R)
    (A' : Matrix (e ⊕ Fin 2) d R) : Prop where
  eps : ε * ε = 1
  gram : (fr ι x y)ᵀ * J * (fr ι x y).map c = gr ε J₁
  inv1 : fr ι x y * A' = 1
  inv2 : A' * fr ι x y = 1

def dg (g : Matrix e e R) (t t' : R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g 0 0 !![t, 0; 0, t']

variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem fr_map (f : R →+* S) : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := by
  ext i j
  rcases j with j | j
  · simp [fr]
  · fin_cases j <;> simp [fr]

omit [Fintype e] [DecidableEq e] in
theorem gr_map (f : R →+* S) : gr (f ε) (J₁.map f) = (gr ε J₁).map f := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [gr]
  · simp [gr]
  · simp [gr]
  · fin_cases i <;> fin_cases j <;> simp [gr]

theorem IsFr.map (h : IsFr c ε J J₁ ι x y A') (f : R →+* S) {c' : S →+* S} (hc : ∀ a, f (c a) = c' (f a)) :
    IsFr c' (f ε) (J.map f) (J₁.map f) (ι.map f) (fun i => f (x i)) (fun i => f (y i)) (A'.map f) := by
  have hfr : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := fr_map f
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h.eps, map_one]
  · have hcm : ((fr ι x y).map f).map c' = ((fr ι x y).map c).map f := by
      ext i j
      simp [hc]
    rw [hfr, gr_map, ← h.gram, hcm, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  · rw [hfr, ← Matrix.map_mul, h.inv1, Matrix.map_one _ f.map_zero f.map_one]
  · rw [hfr, ← Matrix.map_mul, h.inv2, Matrix.map_one _ f.map_zero f.map_one]

theorem IsFr.isUnit_det (h : IsFr c ε J J₁ ι x y A') (hJ : IsUnit J.det) : IsUnit J₁.det := by
  have e1 : (fr ι x y).map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h.inv1, Matrix.map_one _ c.map_zero c.map_one]
  have e2 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have e3 : (fr ι x y)ᵀ * A'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h.inv2, Matrix.transpose_one]
  have hinv : gr ε J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1 := by
    rw [← h.gram]
    calc (fr ι x y)ᵀ * J * (fr ι x y).map c * (A'.map c * J⁻¹ * A'ᵀ)
        = (fr ι x y)ᵀ * (J * (((fr ι x y).map c * A'.map c) * J⁻¹)) * A'ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.one_mul, e2, Matrix.mul_one, e3]
  have hu : IsUnit (gr ε J₁).det := Matrix.isUnit_det_of_right_inverse hinv
  unfold gr at hu
  rw [Matrix.det_fromBlocks_zero₂₁] at hu
  exact isUnit_of_mul_isUnit_left hu

omit [DecidableEq d] [DecidableEq e] in
theorem cols_of_mul {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h i) (Sum.inl j)
    simp [fr, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
  · ext i
    have := congrFun (congrFun h i) (Sum.inr 0)
    simp [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
  · ext i
    have := congrFun (congrFun h i) (Sum.inr 1)
    simp [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this

theorem IsFr.levi (h : IsFr c ε J J₁ ι x y A') (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m = fr ι x y * dg g t (c t') * A' ∧ m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  have hct' : c t' * c t = 1 := by rw [mul_comm]; exact hct
  have hdd : dg g t (c t') * dg g' t' (c t) = 1 := by
    unfold dg
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hg']
    rw [← Matrix.fromBlocks_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hct']
  have hdgT : (dg g t (c t'))ᵀ * gr ε J₁ * (dg g t (c t')).map c = gr ε J₁ := by
    unfold dg gr
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.map_zero _ c.map_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    rw [hg]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hcc, ht] <;>
      linear_combination ε * hct'
  have hmfr : fr ι x y * dg g t (c t') * A' * fr ι x y = fr ι x y * dg g t (c t') := by
    rw [Matrix.mul_assoc, h.inv2, Matrix.mul_one]
  obtain ⟨c1, c2, c3⟩ := cols_of_mul (g := g) (b := 0) (a := 0) (s := !![t, 0; 0, c t']) hmfr
  refine ⟨fr ι x y * dg g t (c t') * A', fr ι x y * dg g' t' (c t) * A', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · calc fr ι x y * dg g t (c t') * A' * (fr ι x y * dg g' t' (c t) * A')
        = fr ι x y * (dg g t (c t') * (A' * fr ι x y) * dg g' t' (c t)) * A' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.inv2, Matrix.mul_one, hdd, Matrix.mul_one, h.inv1]
  · calc (fr ι x y * dg g t (c t') * A')ᵀ * J * (fr ι x y * dg g t (c t') * A').map c
        = A'ᵀ * ((dg g t (c t'))ᵀ * ((fr ι x y)ᵀ * J * (fr ι x y).map c) * (dg g t (c t')).map c) *
            A'.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = A'ᵀ * ((fr ι x y)ᵀ * J * (fr ι x y).map c) * A'.map c := by rw [h.gram, hdgT]
      _ = (fr ι x y * A')ᵀ * J * (fr ι x y * A').map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = J := by
          rw [h.inv1, Matrix.transpose_one, Matrix.map_one _ c.map_zero c.map_one, Matrix.one_mul,
            Matrix.mul_one]
  · rw [c2]
    ext i
    simp [Matrix.mulVec, dotProduct]
  · rw [c3]
    ext i
    simp [Matrix.mulVec, dotProduct]
  · rw [c1]
    simp

private theorem fr_mulVec_sum_elim (u : e → R) (s t : R) :
    fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

private theorem eq_of_iota_mulVec_add_smul_eq (h : IsFr c ε J J₁ ι x y A') {u u' : e → R} {s t s' t' : R}
    (e1 : ι *ᵥ u + s • x + t • y = ι *ᵥ u' + s' • x + t' • y) : u = u' ∧ s = s' ∧ t = t' := by
  rw [← fr_mulVec_sum_elim, ← fr_mulVec_sum_elim] at e1
  have h2 := congrArg (fun v => A' *ᵥ v) e1
  simp only [Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec] at h2
  exact ⟨funext fun j => by simpa using congrFun h2 (Sum.inl j), by simpa using congrFun h2 (Sum.inr 0),
    by simpa using congrFun h2 (Sum.inr 1)⟩

private theorem mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr (h : IsFr c ε J J₁ ι x y A') {p : Matrix d d R} (hp : pᵀ * J * p.map c = J) :
    p * fr ι x y = fr ι x y * Matrix.fromBlocks (A' * p * fr ι x y).toBlocks₁₁ (A' * p * fr ι x y).toBlocks₁₂
      (A' * p * fr ι x y).toBlocks₂₁ (A' * p * fr ι x y).toBlocks₂₂ ∧
    (A' * p * fr ι x y)ᵀ * gr ε J₁ * (A' * p * fr ι x y).map c = gr ε J₁ := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.fromBlocks_toBlocks, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.inv1, Matrix.one_mul]
  · calc (A' * p * fr ι x y)ᵀ * gr ε J₁ * (A' * p * fr ι x y).map c
        = (fr ι x y)ᵀ * (pᵀ * ((fr ι x y * A')ᵀ * J * (fr ι x y * A').map c) * p.map c) *
            (fr ι x y).map c := by
          rw [← h.gram]
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = gr ε J₁ := by
          rw [h.inv1, Matrix.transpose_one, Matrix.map_one _ c.map_zero c.map_one, Matrix.one_mul,
            Matrix.mul_one, hp, h.gram]

theorem IsFr.stab (h : IsFr c ε J J₁ ι x y A') {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), g = (A' * p * fr ι x y).toBlocks₁₁ ∧ gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  obtain ⟨hpf, hQ⟩ := mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr h hp
  have hQ' := hQ
  rw [← Matrix.fromBlocks_toBlocks (A' * p * fr ι x y)] at hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₁ = g0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₁₂ = b0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₂₁ = a0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₂₂ = s0 at hpf hQ' ⊢
  obtain ⟨c1, c2, c3⟩ := cols_of_mul hpf
  obtain ⟨hb0, hs00, hs10⟩ := eq_of_iota_mulVec_add_smul_eq h (u := 0) (s := t) (t := 0) (u' := fun j => b0 j 0)
    (s' := s0 0 0) (t' := s0 1 0) (by rw [← c2, hx]; simp)
  have hb0' : ∀ j, b0 j 0 = 0 := fun j => (congrFun hb0 j).symm
  unfold gr at hQ'
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hQ'
  obtain ⟨e11, e12, -, -⟩ := hQ'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e11 e12
  have ha1 : ∀ i, a0 1 i = 0 := by
    intro i
    have h12 := congrFun (congrFun e12 i) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb0', ← hs00, ← hs10] at h12
    linear_combination (ε * c t') * h12 - a0 1 i * h.eps - a0 1 i * ε * ε * hct
  have haK : a0ᵀ * !![0, 1; ε, 0] * a0.map c = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1]
  rw [haK, add_zero] at e11
  refine ⟨g0, fun j => a0 0 j, rfl, e11, fun z => ?_⟩
  rw [Matrix.mulVec_mulVec, c1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha1] <;> ring

theorem IsFr.ext (h : IsFr c ε J J₁ ι x y A') {m m' : Matrix d d R} (h1 : m *ᵥ x = m' *ᵥ x) (h2 : m *ᵥ y = m' *ᵥ y)
    (h3 : m * ι = m' * ι) : m = m' := by
  have hf : m * fr ι x y = m' * fr ι x y := by
    ext i j
    rcases j with j | j
    · have := congrFun (congrFun h3 i) j
      simpa [fr, Matrix.mul_apply] using this
    · fin_cases j
      · have := congrFun h1 i
        simpa [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      · have := congrFun h2 i
        simpa [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  calc m = m * (fr ι x y * A') := by rw [h.inv1, Matrix.mul_one]
    _ = m' * (fr ι x y * A') := by rw [← Matrix.mul_assoc, hf, Matrix.mul_assoc]
    _ = m' := by rw [h.inv1, Matrix.mul_one]

omit [DecidableEq d] [DecidableEq e] in
theorem fr_mulVec (u : e → R) (s t : R) : fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem IsFr.span (h : IsFr c ε J J₁ ι x y A') (z : d → R) : ∃ (u : e → R) (s t : R), z = ι *ᵥ u + s • x + t • y := by
  refine ⟨fun j => (A' *ᵥ z) (Sum.inl j), (A' *ᵥ z) (Sum.inr 0), (A' *ᵥ z) (Sum.inr 1), ?_⟩
  rw [← fr_mulVec]
  have hw : Sum.elim (fun j => (A' *ᵥ z) (Sum.inl j)) ![(A' *ᵥ z) (Sum.inr 0), (A' *ᵥ z) (Sum.inr 1)] =
      A' *ᵥ z := by
    ext k
    rcases k with k | k
    · rfl
    · fin_cases k <;> rfl
  rw [hw, Matrix.mulVec_mulVec, h.inv1, Matrix.one_mulVec]

theorem IsFr.indep (h : IsFr c ε J J₁ ι x y A') {u u' : e → R} {s t s' t' : R}
    (e1 : ι *ᵥ u + s • x + t • y = ι *ᵥ u' + s' • x + t' • y) : u = u' ∧ s = s' ∧ t = t' := by
  rw [← fr_mulVec, ← fr_mulVec] at e1
  have := congrArg (A' *ᵥ ·) e1
  simp only [mulVec_mulVec, h.inv2, one_mulVec] at this
  exact ⟨funext fun j => congrFun this (Sum.inl j), congrFun this (Sum.inr 0), congrFun this (Sum.inr 1)⟩

theorem IsFr.fix_y (h : IsFr c ε J J₁ ι x y A') (hcc : ∀ a, c (c a) = a) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = x) : ∃ (u : e → R) (s : R), p *ᵥ y = y + ι *ᵥ u + s • x := by
  obtain ⟨hpf, hQ⟩ := mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr h hp
  have hQ' := hQ
  rw [← Matrix.fromBlocks_toBlocks (A' * p * fr ι x y)] at hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₁ = g0 at hpf hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₂ = b0 at hpf hQ'
  generalize (A' * p * fr ι x y).toBlocks₂₁ = a0 at hpf hQ'
  generalize (A' * p * fr ι x y).toBlocks₂₂ = s0 at hpf hQ'
  obtain ⟨c1, c2, c3⟩ := cols_of_mul hpf
  obtain ⟨hb0, hs00, hs10⟩ := eq_of_iota_mulVec_add_smul_eq h (u := 0) (s := 1) (t := 0) (u' := fun j => b0 j 0)
    (s' := s0 0 0) (t' := s0 1 0) (by rw [← c2, hx]; simp)
  have hb0' : ∀ j, b0 j 0 = 0 := fun j => (congrFun hb0 j).symm
  unfold gr at hQ'
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hQ'
  obtain ⟨-, -, -, e22⟩ := hQ'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e22
  have h22 := congrFun (congrFun e22 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb0', ← hs00, ← hs10] at h22
  have hs11 : s0 1 1 = 1 := by rw [← hcc (s0 1 1), h22, map_one]
  refine ⟨fun j => b0 j 1, s0 0 1, ?_⟩
  rw [c3, hs11, one_smul]
  abel

end PositivityTheory.ThKCT.Fr
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Fr

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKG.Tow.Levi (sig_sig cA_cA exists_UA)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_det {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := fun hm => by
  obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hm
  have := h.2.2 (star x) (by simpa using hx)
  rw [star_star, e, dotProduct_zero] at this
  exact lt_irrefl _ this

variable {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem det_ne (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
  rcases hY with h | h
  · intro h0
    refine cartan_det (h.cartan u) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · exact PositivityTheory.ThKG.Tow.Levi.det_ne_zero h

theorem exists_eps (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ε : ℤˣ, (∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j) ∧ Y.L.IsLattice E := by
  rcases hY with h | h
  · exact ⟨1, fun i j => by simp [h.herm], h.lat.toIsLattice⟩
  · exact ⟨-1, fun i j => by simp [h.skew], h.lat.toIsLattice⟩

theorem form_eps (hs : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (x y : Fin n → E) :
    σ (form σ J y x) = ((ε : ℤ) : E) * form σ J x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, hs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hJ]; ring

theorem eps_sq (ε : ℤˣ) : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem isFr (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    ∃ (ε : E) (A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E), IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A' := by
  obtain ⟨ε, hε, hL⟩ := exists_eps hY
  have hsk : ∀ x y, form σ Y.J x y = ((ε : ℤ) : E) * σ (form σ Y.J y x) := fun x y => by
    rw [form_eps (sig_sig hB.cm) hε, ← mul_assoc, eps_sq, one_mul]
  have hFull : Y.L.IsFullLattice E := by
    let := hL
    refine { span_eq_top := ?_ }
    let W := Submodule.span E (Y.L : Set (Fin n → E))
    change W = ⊤
    by_contra hW
    let g : (Fin n → E) →ₗ[E] Module.Dual E W :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin Y.Jᵀ)).domRestrict₂ W
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin n → E) (hx : x ∈ Y.L) : form σ Y.J y x = 0 := by
      have hz' : z ⬝ᵥ Y.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have hzero : form σ Y.J x y = 0 := by
        rw [Matrix.dotProduct_transpose_mulVec] at hz'
        simpa only [form, y, sig_sig hB.cm] using hz'
      rw [hsk, hzero, map_zero, mul_zero]
    have hline (a : E) : a • y ∈ Y.L := by
      have hzform (x : Fin n → E) (hx : x ∈ Y.L) : form σ Y.J (a • y) x = 0 := by
        simpa only [form, smul_dotProduct, smul_eq_mul] using
          (show a * form σ Y.J y x = 0 by rw [horth x hx, mul_zero])
      rcases hY with h | h
      · exact (h.dual _).2 fun x hx => by rw [hzform x hx]; exact isIntegral_zero
      · exact (h.dual _).2 fun x hx o => by rw [hzform x hx, mul_zero, map_zero]; exact isIntegral_zero
    let i : E →ₗ[𝓞 E] Y.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict Y.L hline
    let : Module.Finite (𝓞 E) Y.L := Module.Finite.iff_fg.mpr hL.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have ent : ∀ a b, ((fr H.ι H.x H.y)ᵀ * Y.J * (fr H.ι H.x H.y).map (σ : E →+* E)) a b =
      form σ Y.J (fun i => fr H.ι H.x H.y i a) (fun i => fr H.ι H.x H.y i b) := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have col : ∀ j, (fun i => fr H.ι H.x H.y i (Sum.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    ext i; simp [fr]
  have hs : ∀ z : Fin n → E, z ∈ LinearMap.range (Matrix.toLin' (fr H.ι H.x H.y)) := fun z => by
    have hz : z ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by rw [Submodule.IsFullLattice.span_eq_top]; trivial
    refine (Submodule.span_le.2 fun z hz => ?_) hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    exact ⟨Sum.elim u ![s, t], by rw [Matrix.toLin'_apply, fr_mulVec]; abel⟩
  choose f hf using fun j => hs (Pi.single j 1)
  have h1 : fr H.ι H.x H.y * (Matrix.of fun a j => f j a) = 1 := by
    ext i j
    rw [Matrix.one_apply, ← Pi.single_apply, ← hf j]; rfl
  refine ⟨(ε : ℤ), _, eps_sq ε, ?_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h1⟩
  ext (a | a) (b | b)
  · exact congrFun (congrFun hH.gram a) b
  · rw [ent, col]
    fin_cases b
    exacts [(hH.orth _).1, (hH.orth _).2]
  · rw [ent, col, hsk]
    fin_cases a
    · exact (congrArg (fun z => _ * σ z) (hH.orth _).1).trans (by simp [gr])
    · exact (congrArg (fun z => _ * σ z) (hH.orth _).2).trans (by simp [gr])
  · rw [ent]
    fin_cases a <;> fin_cases b
    exacts [hH.xx, hH.xy, (hsk _ _).trans ((congrArg (fun z => _ * σ z) hH.xy).trans (by simp [gr])), hH.yy]

variable {ε : E} {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E}

theorem IsFr.ad (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') :
    IsFr (cA σ : AE F E →+* AE F E) (inclR (F := F) (AF F) ε) (incM F Y.J) (incM F Y₁.J) (incM F H.ι) (incV F H.x) (incV F H.y)
      (incM F A') :=
  h.map (inclR (F := F) (AF F)) fun _ => rfl

theorem mat_mul {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inj {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_cancel {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) : mat g⁻¹ *ᵥ (mat g *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]

theorem mat_cancel' {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) : mat g *ᵥ (mat g⁻¹ *ᵥ z) = z := by
  simpa using mat_cancel g⁻¹ z

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F ⊗[F] E) := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    infer_instance
  (inclR (F := F) (E := E) (AF F)).injective

theorem mem_ratU {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} : g ∈ ratU σ J ↔ ∃ M, mat g = incM F M := by
  refine ⟨fun h => ?_, fun ⟨M, hM⟩ => ?_⟩
  · obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 h
    exact ⟨u.1, (congrArg Units.val hu).symm⟩
  · haveI : Nontrivial (AE F E) := inclR_inj.nontrivial
    have h1 : IsUnit (mat g).det := (Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit
    have h2 : M.det ≠ 0 := fun h0 => by
      rw [hM, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
      exact not_isUnit_zero h1
    exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M h2, Units.ext hM.symm⟩

theorem mem_unip {u : UA σ Y.J} : u ∈ unip σ Y H ↔ mat u *ᵥ incV F H.x = incV F H.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨Matrix.one_mulVec _, fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  | mul a b _ _ ha hb =>
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hb.1, ha.1], fun z => ?_⟩
    obtain ⟨s, hs⟩ := ha.2 z
    obtain ⟨t, ht⟩ := hb.2 z
    exact ⟨s + t, by rw [mat_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_add, hs, Matrix.mulVec_smul, ha.1, add_smul, add_assoc]⟩
  | inv a _ ha =>
    have e : mat a⁻¹ *ᵥ incV F H.x = incV F H.x := by conv_lhs => rw [← ha.1, mat_cancel]
    refine ⟨e, fun z => ?_⟩
    obtain ⟨s, hs⟩ := ha.2 z
    have := mat_cancel a (incM F H.ι *ᵥ z)
    rw [hs, Matrix.mulVec_add, Matrix.mulVec_smul, e] at this
    exact ⟨-s, by rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]⟩

theorem exists_levi (hσ : IsCMExt F E σ) (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') (t : (AE F E)ˣ) (g : UA σ Y₁.J) :
    ∃ m : UA σ Y.J, IsLevi H t g m ∧
      mat m = fr (incM F H.ι) (incV F H.x) (incV F H.y) * dg (mat g) t.1 (cA σ (t⁻¹).1) * incM F A' := by
  obtain ⟨m, m', e0, e1, e2, e3, e4, e5⟩ := h.ad.levi (cA_cA hσ) t.mul_inv g.1.mul_inv g.2
  obtain ⟨p, rfl⟩ := exists_UA e1 e2
  exact ⟨p, ⟨e3, e4, e5⟩, e0⟩

theorem levi_uniq (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m m' : UA σ Y.J}
    (h1 : IsLevi H t g m) (h2 : IsLevi H t g m') : m = m' :=
  mat_inj (h.ad.ext (h1.1.trans h2.1.symm) (h1.2.1.trans h2.2.1.symm) (h1.2.2.trans h2.2.2.symm))

theorem levi_mul {t t' : (AE F E)ˣ} {g g' : UA σ Y₁.J} {m m' : UA σ Y.J} (h1 : IsLevi H t g m) (h2 : IsLevi H t' g' m') :
    IsLevi H (t * t') (g * g') (m * m') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.1, Matrix.mulVec_smul, h1.1, smul_smul, Units.val_mul, mul_comm]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.2.1, Matrix.mulVec_smul, h1.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [mat_mul, Matrix.mul_assoc, h2.2.2, ← Matrix.mul_assoc, h1.2.2, Matrix.mul_assoc, mat_mul]

theorem levi_one : IsLevi (W := Y) (W₁ := Y₁) (σ := σ) H 1 1 1 :=
  ⟨by simp [mat_one], by simp [mat_one], by simp [mat_one]⟩

theorem levi_inv {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) : IsLevi H t⁻¹ g⁻¹ m⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · have := mat_cancel m (incV F H.x)
    rw [h1.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, Units.inv_mul, one_smul]
  · have := mat_cancel m (incV F H.y)
    rw [h1.2.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, ← map_mul, inv_inv, Units.mul_inv, map_one, one_smul]
  · have : mat m⁻¹ * (incM F H.ι * mat g) = incM F H.ι := by
      rw [← h1.2.2, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    conv_rhs => rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, ← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]

theorem levi_vec {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) (z : Fin n₁ → AE F E) :
    mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, h1.2.2, Matrix.mulVec_mulVec]

theorem levi_conj {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) {u : UA σ Y.J} (hu : u ∈ unip σ Y H) :
    m⁻¹ * u * m ∈ unip σ Y H := by
  obtain ⟨a, b⟩ := mem_unip.1 hu
  have h2 := levi_inv h1
  refine mem_unip.2 ⟨?_, fun z => ?_⟩
  · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1.1, Matrix.mulVec_smul, a, ← h1.1, mat_cancel]
  · obtain ⟨c, hc⟩ := b (mat g *ᵥ z)
    exact ⟨c * (t⁻¹).1, by rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, levi_vec h1, hc,
      Matrix.mulVec_add, levi_vec h2, mat_cancel, Matrix.mulVec_smul, h2.1, smul_smul]⟩

theorem stab_dec (hσ : IsCMExt F E σ) (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') (hd : Y.J.det ≠ 0) (p : UA σ Y.J)
    (t : (AE F E)ˣ) (hp : mat p *ᵥ incV F H.x = t.1 • incV F H.x) :
    ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧
      mat g₁ = (incM F A' * mat p * fr (incM F H.ι) (incV F H.x) (incV F H.y)).toBlocks₁₁ := by
  obtain ⟨g, α, e0, hg, hα⟩ := h.ad.stab t.mul_inv p.2 hp
  have hgu : IsUnit g.det := by
    have e := congrArg Matrix.det hg
    have hd' : IsUnit (incM F Y₁.J).det := by
      have := (h.isUnit_det hd.isUnit).map (inclR (F := F) (AF F))
      rwa [RingHom.map_det] at this
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd'
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')
  obtain ⟨g₁, rfl⟩ := exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg
  obtain ⟨m, hm, -⟩ := exists_levi hσ h t g₁
  have h2 := levi_inv hm
  refine ⟨p * m⁻¹, mem_unip.2 ⟨?_, fun z => ⟨α ⬝ᵥ (mat g₁⁻¹ *ᵥ z), ?_⟩⟩, g₁, m, hm, by group, e0⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.1, Matrix.mulVec_smul, hp, smul_smul, Units.inv_mul, one_smul]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, levi_vec h2]
    exact (hα _).trans (by rw [mat_cancel'])

end PositivityTheory.ThKCT.Fr

end
