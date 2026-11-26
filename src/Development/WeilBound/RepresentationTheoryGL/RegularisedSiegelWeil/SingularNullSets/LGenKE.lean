module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnit

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKD
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKC
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKA
namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

def cj {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : Matrix p m R := (M.map s)ᵀ

theorem cj_apply {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    cj s M i j = s (M j i) := rfl

theorem det_prod_transvec {K : Type} [CommRing K] (L : List (TransvectionStruct n K)) :
    (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det]

theorem fieldB {K : Type} [Field K] (c d X Y : Matrix n n K) (h : c * X + d * Y = 1) :
    ∃ B : Matrix n n K, (d + c * B).det ≠ 0 := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal d
  set P := (L.map TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := det_prod_transvec L
  have hQ : Q.det = 1 := det_prod_transvec L'
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  set E' : Matrix n n K := diagonal fun j => 1 - D j * (D j)⁻¹ with hE'
  set N := P * c * X * P⁻¹ with hNdef
  refine ⟨X * P⁻¹ * E' * Q⁻¹, ?_⟩
  have hM : P * (d + c * (X * P⁻¹ * E' * Q⁻¹)) * Q = diagonal D + N * E' := by
    rw [Matrix.mul_add, Matrix.add_mul, hD]
    congr 1
    simp only [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.mul_one]
  have hPd : P * d = diagonal D * Q⁻¹ := by
    rw [← hD]; simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu]
  have hN : ∀ i j, D i = 0 → N i j = (1 : Matrix n n K) i j := by
    intro i j hi
    have h1 : N + P * d * Y * P⁻¹ = 1 := by
      calc N + P * d * Y * P⁻¹ = P * (c * X + d * Y) * P⁻¹ := by
              simp [hNdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 1 := by rw [h, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
    have h2 : (P * d * Y * P⁻¹) i j = 0 := by
      rw [hPd, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul, hi, zero_mul]
    have := congrFun (congrFun h1 i) j
    rw [Matrix.add_apply, h2, add_zero] at this
    exact this
  intro hdet
  have hM0 : (diagonal D + N * E').det = 0 := by
    rw [← hM, det_mul, det_mul, hdet]; simp
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM0
  apply hp0
  have hME : ∀ i j, (diagonal D + N * E') i j = (if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹) := by
    intro i j
    rw [Matrix.add_apply, hE', Matrix.mul_diagonal, Matrix.diagonal_apply]
  have hpj : ∀ j, ∑ i, p i * ((if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹)) = 0 := by
    intro j
    have := congrFun hp j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [hME]
  have h1 : ∀ j, D j ≠ 0 → p j = 0 := by
    intro j hj
    have := hpj j
    simp only [mul_inv_cancel₀ hj, sub_self, mul_zero, add_zero, mul_ite, mul_zero] at this
    rw [Finset.sum_ite_eq' Finset.univ j] at this
    simpa [hj] using this
  funext j
  by_cases hj : D j = 0
  · have := hpj j
    have e : ∀ i, p i * ((if i = j then D i else 0) + N i j * (1 - D j * (D j)⁻¹)) = p i * (1 : Matrix n n K) i j := by
      intro i
      rw [hj, zero_mul, sub_zero, mul_one]
      by_cases hi : D i = 0
      · rw [hN i j hi]
        split_ifs with hij
        · subst hij; simp [hi]
        · simp
      · rw [h1 i hi]; simp
    rw [Finset.sum_congr rfl fun i _ => e i] at this
    simpa [Matrix.one_apply] using this
  · exact h1 j hj

section Cj

variable {R : Type} [CommRing R] (s : R →+* R)

theorem cj_mul {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) : cj s (M * N) = cj s N * cj s M := by
  ext i j; simp [cj, Matrix.mul_apply, mul_comm]

theorem cj_add {m p : Type} (M N : Matrix m p R) : cj s (M + N) = cj s M + cj s N := by
  ext i j; simp [cj]

theorem cj_sub {m p : Type} (M N : Matrix m p R) : cj s (M - N) = cj s M - cj s N := by
  ext i j; simp [cj]

omit [Fintype n] in
theorem cj_one : cj s (1 : Matrix n n R) = 1 := by
  ext i j; simp [cj, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cj_cj (hs : ∀ x, s (s x) = x) {m p : Type} (M : Matrix m p R) : cj s (cj s M) = M := by
  ext i j; simp [cj, hs]

omit [Fintype n] in
theorem cj_diagonal (f : n → R) : cj s (diagonal f) = diagonal fun i => s (f i) := by
  ext i j; simp [cj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem det_cj (M : Matrix n n R) : (cj s M).det = s M.det := by
  rw [cj, det_transpose, RingHom.map_det]; rfl

end Cj

theorem fieldA {K : Type} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) (c d X Y : Matrix n n K)
    (h : c * X + d * Y = 1) (hl : c * cj s d = d * cj s c) :
    ∃ B : Matrix n n K, cj s B = B ∧ (d + c * B).det ≠ 0 := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal c
  set P := (L.map TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := det_prod_transvec L
  have hQ : Q.det = 1 := det_prod_transvec L'
  have hPu : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQu : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQu
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  set R' := cj s Q⁻¹ with hR'
  have hR1 : cj s Q * R' = 1 := by rw [hR', ← cj_mul, hQQ', cj_one]
  have hR2 : R' * cj s Q = 1 := by rw [hR', ← cj_mul, hQQ, cj_one]
  set d' := P * d * R' with hd'
  set H := diagonal D * cj s d' with hH
  have hH' : H = P * (c * cj s d) * cj s P := by
    rw [hH, hd', ← hD, cj_mul, cj_mul, hR', cj_cj s hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQQ, Matrix.one_mul]
  have hHh : cj s H = H := by
    rw [hH', cj_mul, cj_mul, cj_mul, cj_cj s hs, cj_cj s hs, ← hl]
    simp only [Matrix.mul_assoc]
  have hHij : ∀ i j, H i j = D i * s (d' j i) := by
    intro i j; rw [hH, Matrix.diagonal_mul]; rfl
  have hHsym : ∀ i j, H i j = s (D j) * d' i j := by
    intro i j
    have := congrFun (congrFun hHh i) j
    rw [cj_apply, hHij j i, map_mul, hs] at this
    exact this.symm
  set e : n → K := fun i => D i * (D i)⁻¹ with he
  have hse : ∀ i, s (e i) = e i := by
    intro i; by_cases h0 : D i = 0
    · simp [he, h0]
    · simp [he, h0, mul_inv_cancel₀]
  set E : Matrix n n K := diagonal e with hE
  set Dp : Matrix n n K := diagonal fun i => (D i)⁻¹ with hDp
  obtain ⟨b', hb'⟩ : ∃ b', b' = Dp * (E - E * H * E) * cj s Dp := ⟨_, rfl⟩
  have hcE : cj s E = E := by rw [hE, cj_diagonal]; congr 1; funext i; exact hse i
  have hb'h : cj s b' = b' := by
    rw [hb', cj_mul, cj_mul, cj_sub, cj_mul, cj_mul, cj_cj s hs, hcE, hHh]
    simp only [Matrix.mul_assoc]
  refine ⟨Q * b' * cj s Q, ?_, ?_⟩
  · rw [cj_mul, cj_mul, cj_cj s hs, hb'h, Matrix.mul_assoc]
  have hM : P * (d + c * (Q * b' * cj s Q)) * R' = d' + diagonal D * b' := by
    rw [Matrix.mul_add, Matrix.add_mul, hd', ← hD]
    congr 1
    simp only [Matrix.mul_assoc, hR1, Matrix.mul_one]

  have hcol : ∀ i j, D j ≠ 0 → (d' + diagonal D * b') i j = if i = j then (s (D j))⁻¹ else 0 := by
    intro i j hj
    have hsj : s (D j) ≠ 0 := fun h0 => hj (by rw [← hs (D j), h0, map_zero])
    have hb'ij : b' i j = (D i)⁻¹ * ((if i = j then e i else 0) - e i * H i j * e j) * s ((D j)⁻¹) := by
      rw [hb', cj_diagonal, Matrix.mul_diagonal, hDp, Matrix.diagonal_mul, Matrix.sub_apply, hE,
        Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
    rw [Matrix.add_apply, Matrix.diagonal_mul, hb'ij, map_inv₀]
    have hej : e j = 1 := by simp [he, hj]
    rw [hej, mul_one]
    by_cases hi : D i = 0
    · have hd0 : d' i j = 0 := by
        have := hHsym i j
        rw [hHij, hi, zero_mul] at this
        exact (mul_eq_zero.1 this.symm).resolve_left hsj
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hi, hd0, hij]
    · have hei : e i = 1 := by simp [he, hi]
      rw [hei, hHsym]
      split_ifs with hij
      · subst hij; field_simp; ring
      · field_simp; ring
  intro hdet
  have hM0 : (d' + diagonal D * b').det = 0 := by
    rw [← hM, det_mul, det_mul, hdet]; simp
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM0
  apply hp0
  have h1 : ∀ j, D j ≠ 0 → p j = 0 := by
    intro j hj
    have := congrFun hp j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    rw [Finset.sum_congr rfl fun i _ => by rw [hcol i j hj]] at this
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hsj : s (D j) ≠ 0 := fun h0 => hj (by rw [← hs (D j), h0, map_zero])
    exact (mul_eq_zero.1 this).resolve_right (inv_ne_zero hsj)
  have hpD : p ᵥ* diagonal D = 0 := by
    funext j; rw [Matrix.vecMul_diagonal]
    by_cases hj : D j = 0
    · simp [hj]
    · simp [h1 j hj]
  have hpd' : p ᵥ* d' = 0 := by
    have := hp
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul p (diagonal D) b', hpD, Matrix.zero_vecMul, add_zero] at this
    exact this
  set q := p ᵥ* P with hq
  have hqc : q ᵥ* c = 0 := by
    have e1 : q ᵥ* c ᵥ* Q = 0 := by
      rw [hq, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hD]; exact hpD
    calc q ᵥ* c = q ᵥ* c ᵥ* (Q * Q⁻¹) := by rw [hQQ, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, e1, Matrix.zero_vecMul]
  have hqd : q ᵥ* d = 0 := by
    have e1 : q ᵥ* d ᵥ* R' = 0 := by
      rw [hq, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc]; exact hpd'
    calc q ᵥ* d = q ᵥ* d ᵥ* (R' * cj s Q) := by rw [hR2, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, e1, Matrix.zero_vecMul]
  have hq0 : q = 0 := by
    calc q = q ᵥ* (c * X + d * Y) := by rw [h, Matrix.vecMul_one]
      _ = 0 := by rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hqc, hqd]; simp
  calc p = p ᵥ* (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, ← hq, hq0, Matrix.zero_vecMul]

end PositivityTheory.Rg.Rsw.L.LGenK
end

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_smul {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (r : R) (M : Matrix m p R) :
    cj s (r • M) = s r • cj s M := by
  ext i j; simp [cj]

theorem map_cj {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (s : S →+* S) (π : R →+* S)
    (h : ∀ x, π (σ x) = s (π x)) {m p : Type} (M : Matrix m p R) : (cj σ M).map π = cj s (M.map π) := by
  ext i j; simp [cj, h]

theorem det_jacobi {R : Type} [CommRing R] (σ : R →+* R) (a b0 c d b : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (hb : cj σ b = b) :
    (fromBlocks a (a * b + b0) c (d + c * b)).det * (cj σ (d + c * b)).det = (d + c * b).det := by
  have hu : cj σ (d + c * b) = cj σ d + b * cj σ c := by rw [cj_add, cj_mul, hb]
  have e : fromBlocks a (a * b + b0) c (d + c * b) * fromBlocks (cj σ (d + c * b)) 0 (-cj σ c) 1 =
      fromBlocks 1 (a * b + b0) 0 (d + c * b) := by
    rw [fromBlocks_multiply, hu]
    congr 1
    · rw [← R1]; noncomm_ring
    · simp
    · calc c * (cj σ d + b * cj σ c) + (d + c * b) * -cj σ c = c * cj σ d - d * cj σ c := by noncomm_ring
        _ = 0 := by rw [R2, sub_self]
    · simp
  have := congrArg Matrix.det e
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] at this
  simpa using this

theorem core {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔭 : Ideal R) [h𝔭 : 𝔭.IsMaximal]
    (h2 : IsUnit (2 : R)) (hU : ∀ x, x ∉ 𝔭 → σ x ∉ 𝔭 → IsUnit x) (a b0 c d : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (R3 : d * cj σ a - c * cj σ b0 = 1) :
    ∃ b : Matrix n n R, cj σ b = b ∧ IsUnit (d + c * b).det := by
  letI : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  set π : R →+* R ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  set lift : R ⧸ 𝔭 → R := Function.surjInv hsurj with hlift
  have hl : ∀ y, π (lift y) = y := Function.surjInv_eq hsurj
  have hXY : c * (-cj σ b0) + d * cj σ a = 1 := by rw [← R3]; noncomm_ring
  have hXY' : c.map π * (-cj σ b0).map π + d.map π * (cj σ a).map π = 1 := by
    have := congrArg π.mapMatrix hXY
    simpa only [map_add (f := _), map_mul, map_one, RingHom.mapMatrix_apply] using this
  have key : ∃ b : Matrix n n R, cj σ b = b ∧ (d + c * b).det ∉ 𝔭 := by
    have hdet : ∀ b : Matrix n n R, ((d + c * b).map π).det ≠ 0 → (d + c * b).det ∉ 𝔭 := by
      intro b hb hm
      apply hb
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hm
      rw [← hm, RingHom.map_det]; rfl
    by_cases hst : ∀ x ∈ 𝔭, σ x ∈ 𝔭
    · set s : R ⧸ 𝔭 →+* R ⧸ 𝔭 := Ideal.quotientMap 𝔭 σ (fun x hx => hst x hx) with hs
      have hsπ : ∀ x, π (σ x) = s (π x) := fun x => (Ideal.quotientMap_mk).symm
      have hss : ∀ y, s (s y) = y := by
        intro y; obtain ⟨x, rfl⟩ := hsurj y; rw [← hsπ, ← hsπ, hσ]
      have hlag : c.map π * cj s (d.map π) = d.map π * cj s (c.map π) := by
        rw [← map_cj σ s π hsπ, ← map_cj σ s π hsπ]
        have := congrArg π.mapMatrix R2
        simpa only [map_mul, RingHom.mapMatrix_apply] using this
      obtain ⟨B, hBh, hBd⟩ := fieldA s hss _ _ _ _ hXY' hlag
      set B' := B.map lift with hB'
      refine ⟨(↑h2.unit⁻¹ : R) • (B' + cj σ B'), ?_, hdet _ ?_⟩
      · have hinv : σ (↑h2.unit⁻¹ : R) = ↑h2.unit⁻¹ := by
          have e1 : σ (↑h2.unit⁻¹ : R) * 2 = 1 := by
            have : σ ((↑h2.unit⁻¹ : R) * 2) = 1 := by
              rw [show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl, Units.inv_mul, map_one]
            rwa [map_mul, map_ofNat] at this
          calc σ (↑h2.unit⁻¹ : R) = σ (↑h2.unit⁻¹ : R) * (2 * ↑h2.unit⁻¹) := by
                rw [show (2 : R) * ↑h2.unit⁻¹ = ↑h2.unit * ↑h2.unit⁻¹ from rfl, Units.mul_inv, mul_one]
            _ = ↑h2.unit⁻¹ := by rw [← mul_assoc, e1, one_mul]
        rw [cj_smul, cj_add, cj_cj σ hσ, hinv, add_comm]
      · have hmap : ((↑h2.unit⁻¹ : R) • (B' + cj σ B')).map π = B := by
          ext i j
          have hij := congrFun (congrFun hBh i) j
          rw [cj_apply] at hij
          have h2π : π (↑h2.unit⁻¹ : R) * 2 = 1 := by
            rw [← map_ofNat π 2, ← map_mul, show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl,
              Units.inv_mul, map_one]
          simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add (f := _), cj_apply,
            hB', hsπ, hl, hij]
          linear_combination (B i j) * h2π
        have : (d + c * ((↑h2.unit⁻¹ : R) • (B' + cj σ B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add (f := _), Matrix.map_mul]
        rw [this]; exact hBd
    · push_neg at hst
      obtain ⟨y, hy, hσy⟩ := hst
      obtain ⟨r, i, hi, hri⟩ := h𝔭.exists_inv hσy
      obtain ⟨B, hBd⟩ := fieldB _ _ _ _ hXY'
      set B' := B.map lift with hB'
      set x := r * σ y with hx
      have hπx : π x = 1 := by
        have : π (x + i) = 1 := by rw [hx, hri, map_one]
        rwa [map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hi, add_zero] at this
      have hπσx : π (σ x) = 0 := by
        rw [hx, map_mul, hσ, map_mul, (Ideal.Quotient.eq_zero_iff_mem).2 hy, mul_zero]
      refine ⟨x • B' + cj σ (x • B'), ?_, hdet _ ?_⟩
      · rw [cj_add, cj_cj σ hσ, add_comm]
      · have hmap : (x • B' + cj σ (x • B')).map π = B := by
          ext i j
          simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cj_apply, map_add (f := _), map_mul,
            hπx, hπσx, hB', hl]
          ring
        have : (d + c * (x • B' + cj σ (x • B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add (f := _), Matrix.map_mul]
        rw [this]; exact hBd
  obtain ⟨b, hb, hb𝔭⟩ := key
  refine ⟨b, hb, hU _ hb𝔭 fun hσ𝔭 => hb𝔭 ?_⟩
  rw [← det_jacobi σ a b0 c d b R1 R2 hb, det_cj]
  exact Ideal.mul_mem_left _ _ hσ𝔭

end PositivityTheory.Rg.Rsw.L.LGenK
end

noncomputable section

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, finEmb_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sigR_mem (σ : E →ₐ[F] E) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : sigR (Fv F v) σ y ∈ intLoc F E v := sigR_mem_intLoc σ hy

def sR (σ : E →ₐ[F] E) : intLoc F E v →+* intLoc F E v :=
  ((sigR (Fv F v) σ).comp (intLoc F E v).subtype).codRestrict (intLoc F E v) fun y => sigR_mem v σ y.2

@[simp] theorem coe_sR (σ : E →ₐ[F] E) (y : intLoc F E v) : (sR v σ y : Fv F v ⊗[F] E) = sigR (Fv F v) σ y := rfl

theorem absBar_le_one (τ : E →ₐ[F] FvBar F v) (y : intLoc F E v) : absBar F v (finEmb F v τ y) ≤ 1 := (le_absFin F v τ y).trans (absFin_le_one_of_mem_intLoc y.2)

def p0 (τ : E →ₐ[F] FvBar F v) : Ideal (intLoc F E v) where
  carrier := {y | absBar F v (finEmb F v τ y) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add, map_add (f := _)] at *
    exact (absBar_add_le F v _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
    rw [(absBar_eq_zero F v).2 rfl]; exact zero_lt_one
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul, absBar_mul] at *
    calc absBar F v (finEmb F v τ c) * absBar F v (finEmb F v τ y) ≤ 1 * absBar F v (finEmb F v τ y) :=
          mul_le_mul_of_nonneg_right (absBar_le_one v τ c) zero_le
      _ < 1 := by rw [one_mul]; exact hy

theorem absBar_finEmb_one (τ : E →ₐ[F] FvBar F v) : absBar F v (finEmb F v τ 1) = 1 := by
  rw [map_one]; simpa using absBar_algebraMap F v 1

theorem prime_valuation_ne_top (τ : E →ₐ[F] FvBar F v) : p0 v τ ≠ ⊤ := by
  intro h
  have : (1 : intLoc F E v) ∈ p0 v τ := h ▸ Submodule.mem_top
  change absBar F v (finEmb F v τ ((1 : intLoc F E v) : Fv F v ⊗[F] E)) < 1 at this
  rw [OneMemClass.coe_one, absBar_finEmb_one] at this
  exact lt_irrefl _ this

theorem isUnit_of_absBar (y : intLoc F E v) (h : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ y) = 1) :
    IsUnit y := by
  have hne : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ (y : Fv F v ⊗[F] E) ≠ 0 := by
    intro τ h0
    have h1 := h τ
    rw [h0, (absBar_eq_zero F v).2 rfl] at h1
    exact zero_ne_one h1
  have hinj : Function.Injective (LinearMap.mulLeft (Fv F v) (y : Fv F v ⊗[F] E)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [LinearMap.mulLeft_apply] at hz
    apply absFin_eq_zero_iff.1
    refine le_antisymm (Finset.sup_le fun τ _ => ?_) bot_le
    have h1 := congrArg (finEmb F v τ) hz
    rw [map_mul, map_zero] at h1
    rw [le_zero_iff, absBar_eq_zero]
    exact (mul_eq_zero.1 h1).resolve_left (hne τ)
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  rw [LinearMap.mulLeft_apply] at hz
  have hzmem : z ∈ intLoc F E v := by
    rw [mem_intLoc_iff_absFin_le_one]
    refine Finset.sup_le fun τ _ => ?_
    have e1 := absBar_finEmb_one v τ
    have h1 := congrArg (fun w => absBar F v (finEmb F v τ w)) hz
    simp only [map_mul, absBar_mul, h τ, one_mul] at h1
    rw [h1, e1]
  exact isUnit_iff_exists_inv.2 ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

theorem emb_cases (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) (τ0 τ : E →ₐ[F] FvBar F v) :
    τ = τ0 ∨ τ = τ0.comp σ := by
  classical
  by_contra hne
  push_neg at hne
  have hd : τ0 ≠ τ0.comp σ := by
    intro h
    apply hσ1
    ext x
    have hx : τ0 x = τ0 (σ x) := congrArg (fun g => g x) h
    exact (τ0.injective hx).symm
  have hc := card_algHom_le_finrank F E (FvBar F v)
  rw [h2, ← Fintype.card_eq_nat_card] at hc
  have h3 : ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hd]
    simp [hne.1, hne.2]
  have h4 := Finset.card_le_univ ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v))
  omega

theorem exists_max (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) :
    ∃ 𝔭 : Ideal (intLoc F E v), 𝔭.IsMaximal ∧ ∀ x, x ∉ 𝔭 → sR v σ x ∉ 𝔭 → IsUnit x := by
  have τ0 : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal _ (prime_valuation_ne_top v τ0)
  refine ⟨𝔭, hmax, fun x hx hsx => isUnit_of_absBar v x fun τ => ?_⟩
  have hone : ∀ w : intLoc F E v, w ∉ 𝔭 → absBar F v (finEmb F v τ0 w) = 1 := by
    intro w hw
    exact le_antisymm (absBar_le_one v τ0 w) (not_lt.1 fun hlt => hw (hle (show w ∈ p0 v τ0 from hlt)))
  rcases emb_cases v σ hσ1 h2 τ0 τ with rfl | rfl
  · exact hone x hx
  · have h5 := hone _ hsx
    rwa [coe_sR, finEmb_sigR] at h5

theorem isUnit_two (h : (2 : 𝓞 F) ∉ v.asIdeal) : IsUnit (2 : intLoc F E v) := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = ((2 : F) : Fv F v) := by
      rw [show (2 : F) = 1 + 1 by norm_num, HeightOneSpectrum.adicCompletion.coe_add,
        HeightOneSpectrum.adicCompletion.coe_one]
      norm_num
    have e2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat (algebraMap (𝓞 F) F) 2).symm
    rw [e, HeightOneSpectrum.adicCompletion.valued_coe, e2, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact h
  have hmem : (2 : Fv F v)⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have h0 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have h2 : (2 : Fv F v ⊗[F] E) = (2 : Fv F v) ⊗ₜ[F] (1 : E) := by
    rw [show (2 : Fv F v) = 1 + 1 by norm_num, TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    norm_num
  have hc : ((2 : intLoc F E v) : Fv F v ⊗[F] E) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  refine isUnit_iff_exists_inv.2 ⟨⟨_, tmul_mem_intLoc hmem (1 : 𝓞 E)⟩, Subtype.ext ?_⟩
  push_cast
  rw [hc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ h0, one_mul,
    ← Algebra.TensorProduct.one_def]

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

noncomputable section

open scoped TensorProduct NNReal
open Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_fromBlocks {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R) :
    cj s (fromBlocks a b c d) = fromBlocks (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold cj
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cj_neg {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : cj s (-M) = -cj s M := by
  ext i j; simp [cj]

theorem cj_zero {R : Type} [CommRing R] (s : R →+* R) {m p : Type} : cj s (0 : Matrix m p R) = 0 := by
  ext i j; simp [cj]

theorem unit_rel {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    a * cj s d - b * cj s c = 1 ∧ c * cj s d = d * cj s c ∧ d * cj s a - c * cj s b = 1 := by
  set M := fromBlocks a b c d with hM
  set J : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks 0 1 (-1) 0 with hJ
  have hJJ : J * J = -1 := by
    rw [hJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have h1 : (-(J * cj s M * J)) * M = 1 := by
    calc (-(J * cj s M * J)) * M = -(J * (cj s M * J * M)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJJ, neg_neg]
  have h2 : M * (-(J * cj s M * J)) = 1 := mul_eq_one_comm.mp h1
  have e : M * J * cj s M * J = -1 := by
    rw [Matrix.mul_neg] at h2
    simp only [Matrix.mul_assoc] at h2 ⊢
    exact neg_eq_iff_eq_neg.mp h2
  have h3 : M * J * cj s M = J := by
    calc M * J * cj s M = -(M * J * cj s M * (J * J)) := by rw [hJJ]; simp
      _ = -(M * J * cj s M * J * J) := by simp [Matrix.mul_assoc]
      _ = J := by rw [e]; simp
  rw [hM, hJ, cj_fromBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  simp at h3
  obtain ⟨-, k1, k2, k3⟩ := h3
  rw [neg_add_eq_sub] at k1 k2 k3
  refine ⟨k1, sub_eq_zero.mp k3, ?_⟩
  rw [← neg_sub, k2, neg_neg]

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem local_choice (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E)
    (hfr : Module.finrank F E = 2) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (a b c d : Matrix n n (Fv F v ⊗[F] E))
    (ha : ∀ i j, a i j ∈ intLoc F E v) (hb : ∀ i j, b i j ∈ intLoc F E v) (hc : ∀ i j, c i j ∈ intLoc F E v)
    (hd : ∀ i j, d i j ∈ intLoc F E v)
    (hu : cj (sigR (Fv F v) σ) (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d =
      fromBlocks 0 1 (-1) 0) :
    ∃ x : Matrix n n (Fv F v ⊗[F] E), (∀ i j, x i j ∈ intLoc F E v) ∧ cj (sigR (Fv F v) σ) x = x ∧
      ∃ z ∈ intLoc F E v, (d + c * x).det * z = 1 := by
  have hinv : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => simp [sigR, hσ]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  set s := sR v σ with hs
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply Subtype.ext
    rw [hs, coe_sR, coe_sR, hinv]
  have hπ : ∀ y, (intLoc F E v).subtype (s y) = sigR (Fv F v) σ ((intLoc F E v).subtype y) := by
    intro y
    exact coe_sR v σ y
  let a' : Matrix n n (intLoc F E v) := fun i j => ⟨a i j, ha i j⟩
  let b' : Matrix n n (intLoc F E v) := fun i j => ⟨b i j, hb i j⟩
  let c' : Matrix n n (intLoc F E v) := fun i j => ⟨c i j, hc i j⟩
  let d' : Matrix n n (intLoc F E v) := fun i j => ⟨d i j, hd i j⟩
  have ea : a'.map (intLoc F E v).subtype = a := rfl
  have eb : b'.map (intLoc F E v).subtype = b := rfl
  have ec : c'.map (intLoc F E v).subtype = c := rfl
  have ed : d'.map (intLoc F E v).subtype = d := rfl
  have h1m : (1 : Matrix n n (intLoc F E v)).map (intLoc F E v).subtype = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hJm : (fromBlocks 0 1 (-1) 0 : Matrix (n ⊕ n) (n ⊕ n) (intLoc F E v)).map (intLoc F E v).subtype
      = fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg (intLoc F E v).subtype), h1m]
    simp
  have hu' : cj s (fromBlocks a' b' c' d') * fromBlocks 0 1 (-1) 0 * fromBlocks a' b' c' d' =
      fromBlocks 0 1 (-1) 0 := by
    apply Matrix.map_injective Subtype.val_injective
    have key := hu
    rw [← ea, ← eb, ← ec, ← ed, ← Matrix.fromBlocks_map, ← map_cj s _ _ hπ, ← hJm,
      ← Matrix.map_mul, ← Matrix.map_mul] at key
    exact key
  obtain ⟨k1, k2, k3⟩ := unit_rel s a' b' c' d' hu'
  obtain ⟨𝔭, h𝔭, hloc⟩ := exists_max v σ hσ1 hfr
  obtain ⟨B, hB, hdet⟩ := core s hss 𝔭 (isUnit_two v h2) hloc a' b' c' d' k1 k2 k3
  obtain ⟨w, hw⟩ := hdet.exists_right_inv
  refine ⟨B.map (intLoc F E v).subtype, fun i j => (B i j).2, ?_, w, w.2, ?_⟩
  · rw [← map_cj s _ _ hπ, hB]
  · have hm : (d' + c' * B).map (intLoc F E v).subtype = d + c * B.map (intLoc F E v).subtype := by
      rw [Matrix.map_add _ (map_add (intLoc F E v).subtype), Matrix.map_mul, ec, ed]
    rw [← hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using congrArg Subtype.val hw

end Local

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

section GlobalTheory

variable {R : Type} [CommRing R] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _, fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4; rw [fromBlocks_one, Matrix.submatrix_one_equiv]

theorem conj_block_matrix (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    cj s (blk4 a b c d) = blk4 (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold blk4; rw [← cj_fromBlocks]; rfl

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R} (h : blk4 a b c d = blk4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have : fromBlocks a b c d = fromBlocks a' b' c' d' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
    simpa [blk4, Matrix.submatrix_submatrix] using this
  exact Matrix.fromBlocks_inj.1 this

def bA (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
def bB (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
def bC (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
def bD (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blk4 (bA M) (bB M) (bC M) (bD M) = M := by
  unfold blk4 bA bB bC bD
  rw [fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem unit_fromBlocks (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0) :
    cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0 := by
  rw [conj_block_matrix, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective h
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3, h4]

theorem unit_col (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    cj s a * c = cj s c * a ∧ cj s a * d - cj s c * b = 1 ∧ cj s b * d = cj s d * b := by
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    zero_add, add_zero] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]; noncomm_ring
  · rw [← h2]; noncomm_ring
  · rw [← sub_eq_zero, ← h4]; noncomm_ring

end GlobalTheory

section G

variable {D : D7} {n : ℕ}

abbrev Jm (D : D7) (n : ℕ) : Mx D (n + n) (n + n) := blk4 0 1 (-1) 0

theorem Jst_map : (Jst D n).map (inclR (AF D.host.F)) = Jm D n := by
  rw [Jst, block_matrix_map]
  have e : ((-1 : Matrix (Fin n) (Fin n) D.host.E)).map (inclR (F := D.host.F) (AF D.host.F)) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp [e]

theorem mat_unit (g : G D n) : cj (cA D) (mat g) * Jm D n * mat g = Jm D n := by
  rw [← Jst_map]; exact g.2

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp [mat]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp [mat]

theorem mat_inv_mul (g : G D n) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem mat_inv_eq {g : G D n} {N : Mx D (n + n) (n + n)} (h : mat g * N = 1) : mat g⁻¹ = N := by
  calc mat g⁻¹ = mat g⁻¹ * (mat g * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem Jm_inv : blk4 (0 : Mx D n n) (-1) 1 0 * Jm D n = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem exists_G (M : Mx D (n + n) (n + n)) (hM : cj (cA D) M * Jm D n * M = Jm D n) : ∃ g : G D n, mat g = M := by
  have h1 : (blk4 (0 : Mx D n n) (-1) 1 0 * cj (cA D) M * Jm D n) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cj (cA D) M), hM, Jm_inv]
  have h2 := mul_eq_one_comm.1 h1
  let u : GL (Fin (n + n)) (AE D) := ⟨M, _, h2, h1⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    change cj (cA D) M * (Jst D n).map (inclR (AF D.host.F)) * M = (Jst D n).map (inclR (AF D.host.F))
    rw [Jst_map]; exact hM
  exact ⟨⟨u, hu⟩, rfl⟩

end G

end PositivityTheory.Rg.Rsw.L.LGenK
