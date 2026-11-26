module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.IsoRightInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.FvecCastSucc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermitianXiOrthogonal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInverseBoundOf
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness.CA

theorem ut_conjT {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : uᴴ ∈ LTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conjTranspose_apply, hu.1 j i hij, star_zero]
  · rw [conjTranspose_apply, hu.2 i, star_one]

theorem isMonomial_conjT {m : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} (h : IsMonomial P) : IsMonomial Pᴴ := by
  obtain ⟨w, d, hd, rfl⟩ := h
  refine ⟨w.symm, fun a => star (d (w.symm a)), fun a => by simpa using hd (w.symm a), ?_⟩
  ext i a
  simp only [monoP, conjTranspose_apply, of_apply]
  by_cases h : a = w i
  · have h' : i = w.symm a := by rw [h, Equiv.symm_apply_apply]
    rw [if_pos h, if_pos h', h']
  · have h' : ¬ i = w.symm a := by
      intro h'; apply h; rw [h', Equiv.apply_symm_apply]
    rw [if_neg h, if_neg h', star_zero]

theorem mx_inv_conjT {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx (Mᴴ)⁻¹ = mx M⁻¹ := by
  rw [← conjTranspose_nonsing_inv, GN.mx_conjTranspose]

theorem finish_bound {M C0 X A G : ℝ} (e : ℕ) (hm : M ≤ C0 * X ^ e) (hX : 0 ≤ X) (hXY : X ≤ A * G) :
    M ≤ max C0 0 * A ^ e * G ^ e := by
  calc M ≤ C0 * X ^ e := hm
    _ ≤ max C0 0 * X ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX e)
    _ ≤ max C0 0 * (A * G) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hXY e) (le_max_right _ _)
    _ = max C0 0 * A ^ e * G ^ e := by rw [mul_pow]; ring

theorem exp_eq (r : ℕ) : (r + 1 - 1) * (r + 1) = r * (r + 1) := by
  rw [Nat.add_sub_cancel]

end PI.PolynomialProperness.CA

namespace PI.PolynomialProperness

open CA in
theorem unitriangular_inverse_bound_of (h : MonomialFactorizationBound) (hZ : ZhatBound) : UnitriangularInversePolynomialBound := by
  intro k r z z' γ hmono
  obtain ⟨C1, h1⟩ := h (r + 1) (Zhat k r z z' γ) hmono
  obtain ⟨C2, h2⟩ := h (r + 1) (Zhat k r z z' γ)ᴴ (isMonomial_conjT hmono)
  obtain ⟨CZ, hCZ⟩ := hZ k r z z'
  set A : ℝ := 1 + max CZ 0 with hA
  set e : ℕ := r * (r + 1) with he
  have hzg : ∀ g : B.Mat k r, 1 ≤ B.gN g → 1 + mx (Zhat k r z z' g) ≤ A * B.gN g := by
    intro g hg
    have h3 := hCZ g
    have h4 : CZ * B.gN g ≤ max CZ 0 * B.gN g :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    rw [hA]; nlinarith
  have hX : ∀ g : B.Mat k r, 0 ≤ 1 + mx (Zhat k r z z' g) := fun g => by
    have := GN.mx_nonneg (Zhat k r z z' g); linarith
  have hApos : 0 ≤ A ^ e := pow_nonneg (by rw [hA]; have := le_max_right CZ 0; linarith) e
  refine ⟨max (max C1 0) (max C2 0) * A ^ e, ?_, ?_⟩
  · intro v hv hvl u' hu' g hg hZg
    have hb := h1 vᴴ hvl u' hu'
    rw [← hZg, exp_eq] at hb
    have hmax : max C1 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hApos
    have hG : 0 ≤ B.gN g ^ e := pow_nonneg (by linarith) e
    constructor
    · rw [← mx_inv_conjT]
      exact (finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
    · exact (finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
  · intro u hu v' hv' hPv g hg hZg
    have hl : v'ᴴ ∈ LPg (Zhat k r z z' γ)ᴴ := by
      refine ⟨ut_conjT hv', ?_⟩
      have e1 : ((Zhat k r z z' γ)ᴴ)⁻¹ * v'ᴴ * (Zhat k r z z' γ)ᴴ =
          (Zhat k r z z' γ * v' * (Zhat k r z z' γ)⁻¹)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
      rw [e1]
      exact ut_conjT hPv
    have hb := h2 v'ᴴ hl u hu
    have e2 : v'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' g)ᴴ := by
      rw [hZg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e2, GN.mx_conjTranspose (Zhat k r z z' g), exp_eq] at hb
    have hmax : max C2 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hApos
    have hG : 0 ≤ B.gN g ^ e := pow_nonneg (by linarith) e
    constructor
    · exact (finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
    · rw [← mx_inv_conjT]
      exact (finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)

theorem unitriangular_inverse_bound (h : MonomialFactorizationBound) : UnitriangularInversePolynomialBound := unitriangular_inverse_bound_of h zhatBound

end PI.PolynomialProperness
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.SecondOrderNormBound
open Matrix Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness.CB

theorem sum_castLE {m n : ℕ} (h : n ≤ m) (f : Fin m → ℂ) (hf : ∀ l : Fin m, n ≤ l.val → f l = 0) :
    ∑ l, f l = ∑ t : Fin n, f (Fin.castLE h t) := by
  have hs := Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb h))) (f := f)
    (fun x _ hx => hf x (by
      by_contra hlt
      rw [not_le] at hlt
      exact hx (Finset.mem_map.2 ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)))
  rw [← hs, Finset.sum_map]
  rfl

def rws {m : ℕ} (i : Fin m) : Fin (i.val + 1) → Fin m := Fin.castLE (Nat.succ_le_of_lt i.isLt)

def cls {m : ℕ} (i j : Fin m) : Fin (i.val + 1) → Fin m := fun t =>
  if t.val < i.val then Fin.castLE (Nat.succ_le_of_lt i.isLt) t else j

theorem rws_val {m : ℕ} (i : Fin m) (t : Fin (i.val + 1)) : (rws i t).val = t.val := rfl

theorem det_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A.det‖ ≤ (Fintype.card ι).factorial * c ^ Fintype.card ι := by
  have h' : ∀ i j, NormedField.toAbsoluteValue ℂ (A i j) ≤ c := h
  have := Matrix.det_le h'
  rw [nsmul_eq_mul] at this
  exact this

theorem ut_entry_eq_det {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : U i j = ((L * U).submatrix (rws i) (cls i j)).det := by
  have hfac : (L * U).submatrix (rws i) (cls i j) =
      L.submatrix (rws i) (rws i) * U.submatrix (rws i) (cls i j) := by
    ext a b
    simp only [submatrix_apply, Matrix.mul_apply]
    refine sum_castLE (Nat.succ_le_of_lt i.isLt) _ fun l hl => ?_
    have h0 : L (rws i a) l = 0 := hL.1 _ _ (by rw [Fin.lt_def, rws_val]; omega)
    rw [h0, zero_mul]
  have hlo : (L.submatrix (rws i) (rws i)).IsLowerTriangular := by
    intro a b hab
    have hab' : a < b := hab
    exact hL.1 _ _ hab'
  have hup : (U.submatrix (rws i) (cls i j)).IsUpperTriangular := by
    intro a b hab
    have hab' : b < a := hab
    have hb : b.val < i.val := by
      have := a.isLt; rw [Fin.lt_def] at hab'; omega
    show U (rws i a) (cls i j b) = 0
    simp only [cls, if_pos hb]
    exact hU.1 _ _ hab'
  rw [hfac, det_mul, det_of_isLowerTriangular _ hlo]
  have hl1 : ∀ t : Fin (i.val + 1), L.submatrix (rws i) (rws i) t t = 1 := fun t => hL.2 _
  have hcs : ∀ t : Fin i.val, U.submatrix (rws i) (cls i j) t.castSucc t.castSucc = 1 := by
    intro t
    have h2 : cls i j t.castSucc = rws i t.castSucc := by
      have ht : (t.castSucc : Fin (i.val + 1)).val < i.val := t.isLt
      simp only [cls, if_pos ht]; rfl
    show U (rws i t.castSucc) (cls i j t.castSucc) = 1
    rw [h2]; exact hU.2 _
  have hlast1 : rws i (Fin.last i.val) = i := Fin.ext rfl
  have hlast2 : cls i j (Fin.last i.val) = j := by
    simp only [cls, Fin.val_last, lt_irrefl, if_false]
  rw [Finset.prod_eq_one (fun t _ => hl1 t), one_mul, det_of_isUpperTriangular hup,
    Fin.prod_univ_castSucc, Finset.prod_eq_one (fun t _ => hcs t), one_mul]
  show U i j = U (rws i (Fin.last i.val)) (cls i j (Fin.last i.val))
  rw [hlast1, hlast2]

theorem mx_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx Mᵀ = mx M := by
  apply le_antisymm
  · refine (GN.mx_le_iff _ (GN.mx_nonneg M)).2 fun i j => ?_
    rw [transpose_apply]; exact GN.entry_le_mx M j i
  · refine (GN.mx_le_iff _ (GN.mx_nonneg Mᵀ)).2 fun i j => ?_
    have := GN.entry_le_mx Mᵀ j i
    rwa [transpose_apply] at this

theorem ut_entry_bound {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : ‖U i j‖ ≤ m.factorial * (1 + mx (L * U)) ^ m := by
  rw [ut_entry_eq_det hL hU i j]
  have hd := det_norm_le ((L * U).submatrix (rws i) (cls i j)) (c := mx (L * U))
    (fun a b => GN.entry_le_mx (L * U) (rws i a) (cls i j b))
  rw [Fintype.card_fin] at hd
  have hx := GN.mx_nonneg (L * U)
  have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
  have h1 : ((i.val + 1).factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : mx (L * U) ^ (i.val + 1) ≤ (1 + mx (L * U)) ^ m :=
    (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  exact hd.trans (mul_le_mul h1 h2 (pow_nonneg hx _) (by positivity))

theorem lt_entry_bound {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : ‖L i j‖ ≤ m.factorial * (1 + mx (L * U)) ^ m := by
  have hUt : Uᵀ ∈ LTset m :=
    ⟨fun a b hab => by rw [transpose_apply]; exact hU.1 _ _ hab, fun a => hU.2 a⟩
  have hLt : Lᵀ ∈ UTset m :=
    ⟨fun a b hab => by rw [transpose_apply]; exact hL.1 _ _ hab, fun a => hL.2 a⟩
  have h := ut_entry_bound hUt hLt j i
  rwa [← transpose_mul, mx_transpose, transpose_apply] at h

theorem det_ut {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ UTset m) : U.det = 1 := by
  have h : U.IsUpperTriangular := fun a b hab => hU.1 _ _ hab
  rw [det_of_isUpperTriangular h]
  exact Finset.prod_eq_one fun t _ => hU.2 t

theorem det_lt {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m) : L.det = 1 := by
  have h : L.IsLowerTriangular := fun a b hab => hL.1 _ _ hab
  rw [det_of_isLowerTriangular _ h]
  exact Finset.prod_eq_one fun t _ => hL.2 t

theorem inv_entry_bound {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hM : M.det = 1) {c : ℝ}
    (hc : ∀ i j, ‖M i j‖ ≤ c) (i j : Fin (n + 1)) : ‖M⁻¹ i j‖ ≤ n.factorial * c ^ n := by
  rw [inv_def, hM, Ring.inverse_one, one_smul, adjugate_fin_succ_eq_det_submatrix, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := det_norm_le (M.submatrix j.succAbove i.succAbove) (fun a b => hc _ _)
  rwa [Fintype.card_fin] at this

theorem mx_of_entry {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : mx M ≤ c := (GN.mx_le_iff M hc).2 h

theorem isUnit_det_monomialMatrix' {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    IsUnit (monoP w d).det := by
  have hQ : monoP w d * monoP w.symm (fun j => (d (w.symm j))⁻¹) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, monoP, of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (w.symm j)]
    · simp only [if_true, Equiv.apply_symm_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (hd _)
      · exact zero_mul _
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact isUnit_det_of_right_inverse hQ

def kap (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : ℝ := 1 + m * mx P⁻¹

def Kc (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  m.factorial * kap m P ^ m * (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹)

theorem kap_ge (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : 1 ≤ kap m P := by
  unfold kap; have := GN.mx_nonneg P⁻¹; have : (0 : ℝ) ≤ m := by positivity
  nlinarith

theorem factors_bound {m : ℕ} {P l u : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det)
    (hl : l ∈ LPg P) (hu : u ∈ UTset m) :
    (∀ i j, ‖u i j‖ ≤ Kc m P * (1 + mx (l * P * u)) ^ m) ∧
    (∀ i j, ‖l i j‖ ≤ Kc m P * (1 + mx (l * P * u)) ^ m) := by
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hX := GN.mx_nonneg (l * P * u)
  have hmP := GN.mx_nonneg P
  have hmPi := GN.mx_nonneg P⁻¹
  have hm : (0 : ℝ) ≤ m := by positivity
  have hκ := kap_ge m P
  have hA : P⁻¹ * l * P * u = P⁻¹ * (l * P * u) := by simp only [Matrix.mul_assoc]
  have hmxA : 1 + mx (P⁻¹ * l * P * u) ≤ kap m P * (1 + mx (l * P * u)) := by
    rw [hA]
    have h1 := GN.mx_mul_le P⁻¹ (l * P * u)
    unfold kap
    have : (m : ℝ) * mx P⁻¹ * mx (l * P * u) ≥ 0 := by positivity
    nlinarith
  have hA1 : 0 ≤ 1 + mx (P⁻¹ * l * P * u) := by have := GN.mx_nonneg (P⁻¹ * l * P * u); linarith
  have hpow : (1 + mx (P⁻¹ * l * P * u)) ^ m ≤ kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hA1 hmxA m
  have hfac : (0 : ℝ) ≤ m.factorial := by positivity
  have hK1 : ∀ i j, ‖u i j‖ ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m ∧
      ‖(P⁻¹ * l * P) i j‖ ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    intro i j
    constructor
    · refine (ut_entry_bound hl.2 hu i j).trans ?_
      exact (mul_le_mul_of_nonneg_left hpow hfac).trans_eq (by ring)
    · refine (lt_entry_bound hl.2 hu i j).trans ?_
      exact (mul_le_mul_of_nonneg_left hpow hfac).trans_eq (by ring)
  have hY : 0 ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    have : 0 ≤ kap m P := by linarith
    positivity
  have hext : 1 ≤ 1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by
    have : 0 ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
    linarith
  have hKeq : Kc m P * (1 + mx (l * P * u)) ^ m =
      (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) * (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹) := by
    unfold Kc; ring
  constructor
  · intro i j
    rw [hKeq]
    exact (hK1 i j).1.trans (le_mul_of_one_le_right hY hext)
  · have hlt : mx (P⁻¹ * l * P) ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m :=
      mx_of_entry _ hY fun i j => (hK1 i j).2
    have hl_eq : l = P * (P⁻¹ * l * P) * P⁻¹ := by
      rw [show P * (P⁻¹ * l * P) * P⁻¹ = (P * P⁻¹) * l * (P * P⁻¹) by simp only [Matrix.mul_assoc],
        hPP', Matrix.one_mul, Matrix.mul_one]
    have hml : mx l ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := by
      have h1 := GN.mx_mul_le (P * (P⁻¹ * l * P)) P⁻¹
      have h2 := GN.mx_mul_le P (P⁻¹ * l * P)
      rw [← hl_eq] at h1
      have := GN.mx_nonneg (P * (P⁻¹ * l * P))
      have := GN.mx_nonneg (P⁻¹ * l * P)
      calc mx l ≤ m * mx (P * (P⁻¹ * l * P)) * mx P⁻¹ := h1
        _ ≤ m * (m * mx P * mx (P⁻¹ * l * P)) * mx P⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ hmPi
            exact mul_le_mul_of_nonneg_left h2 hm
        _ = (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := by ring
    intro i j
    rw [hKeq]
    have hc : 0 ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
    calc ‖l i j‖ ≤ mx l := GN.entry_le_mx l i j
      _ ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := hml
      _ ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) :=
          mul_le_mul_of_nonneg_left hlt hc
      _ ≤ (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) *
            (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹) := by nlinarith

end PI.PolynomialProperness.CB

namespace PI.PolynomialProperness


open CB in
theorem second_order_norm_bound : MonomialFactorizationBound := open CB in by
  intro m P hP
  obtain ⟨w, d, hd, hPeq⟩ := hP
  have hPu : IsUnit P.det := by rw [hPeq]; exact isUnit_det_monomialMatrix' w d hd
  cases m with
  | zero =>
    refine ⟨0, fun l _ u' _ => ?_⟩
    have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, mx M ≤ 0 :=
      fun M => (GN.mx_le_iff M le_rfl).2 fun i => i.elim0
    simp only [zero_mul]
    exact ⟨h0 _, h0 _, h0 _, h0 _⟩
  | succ n =>
    have hK0 : 0 ≤ Kc (n + 1) P := by
      unfold Kc
      have := kap_ge (n + 1) P
      have := GN.mx_nonneg P; have := GN.mx_nonneg P⁻¹
      have : (0 : ℝ) ≤ 1 + ((n + 1 : ℕ) : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
      have : (0 : ℝ) ≤ kap (n + 1) P := by linarith
      positivity
    refine ⟨n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P, fun l hl u' hu' => ?_⟩
    obtain ⟨hbu, hbl⟩ := factors_bound hPu hl hu'
    set X := mx (l * P * u') with hXdef
    have hX : 0 ≤ X := GN.mx_nonneg _
    have hY : 0 ≤ Kc (n + 1) P * (1 + X) ^ (n + 1) := by positivity
    have hfn : (0 : ℝ) ≤ n.factorial * Kc (n + 1) P ^ n := by positivity
    have hCge : Kc (n + 1) P ≤ n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P := by linarith
    have hmain : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        (∀ i j, ‖M i j‖ ≤ Kc (n + 1) P * (1 + X) ^ (n + 1)) →
        mx M ≤ (n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P) * (1 + X) ^ (n + 1) := by
      intro M hM
      refine mx_of_entry M (by positivity) fun i j => (hM i j).trans ?_
      exact mul_le_mul_of_nonneg_right hCge (by positivity)
    have hinv : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M.det = 1 →
        (∀ i j, ‖M i j‖ ≤ Kc (n + 1) P * (1 + X) ^ (n + 1)) →
        mx M⁻¹ ≤ (n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P) * (1 + X) ^ ((n + 1 - 1) * (n + 1)) := by
      intro M hdet hM
      have e : (1 + X) ^ ((n + 1 - 1) * (n + 1)) = ((1 + X) ^ (n + 1)) ^ n := by
        rw [Nat.add_sub_cancel, ← pow_mul, mul_comm]
      rw [e]
      refine mx_of_entry _ (by positivity) fun i j => (inv_entry_bound M hdet hM i j).trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine ⟨hmain l hbl, hmain u' hbu, hinv l (det_lt hl.1) hbl, hinv u' (det_ut hu') hbu⟩

end PI.PolynomialProperness
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.CoreInst
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

theorem coreInst_of (hC : IsoCore) (hI : HpkInvol) (hN : GNFacts) (h1 : Formalism.FourierDecayAlt.C2.GramIndependentSignature) :
    CoreInst := by
  intro k r z z' γ hstd hpos
  obtain ⟨_, ⟨Q, _, hQG⟩, hpd, _⟩ := h1 k r z z' γ hstd hpos
  obtain ⟨hH1, hH2⟩ := hI k r
  have hG : gramOf (Hpk k r) (gramVec k r z z' γ) = gramM k r z z' γ := by
    ext i j
    rfl
  have hunit : IsUnit (gramOf (Hpk k r) (gramVec k r z z' γ)).det := by
    rw [hG]
    set M0 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
      Matrix.fromBlocks 1 0 0 (-1) with hM0
    have hsq : M0 * M0 = 1 := by
      rw [hM0, Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    have hM0u : IsUnit M0.det :=
      IsUnit.of_mul_eq_one (b := M0.det) (by rw [← Matrix.det_mul, hsq, Matrix.det_one])
    rw [← hQG, Matrix.det_mul, Matrix.det_mul] at hM0u
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hM0u)
  have hcond : ∀ x, (∀ i, herm (Hpk k r) x (gramVec k r z z' γ i) = 0) →
      0 ≤ (herm (Hpk k r) x x).re := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [herm]
    · have hxU : x ∈ Uperp k r z z' γ := by
        rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
        ext i
        have h2 := hx i
        simp only [herm] at h2
        simpa [Matrix.mulVec, dotProduct] using h2
      exact (hpd x hxU hx0).le
  obtain ⟨C0, hC0⟩ := hC _ (Hpk k r) _ (gramVec k r z z' γ) hH1 hH2 hunit hcond
  obtain ⟨_, _, _, hgn⟩ := hN k r
  refine ⟨C0 * ∑ j : Fin (2 * r + k + 1), nsq (bvec j : Fin (2 * r + k + 1) → ℂ), fun s hs K hK hsm => ?_⟩
  rw [hgn s]
  calc ∑ j, nsq (s *ᵥ bvec j) ≤ ∑ j : Fin (2 * r + k + 1), C0 * (1 + K) ^ 2 * nsq (bvec j : Fin (2 * r + k + 1) → ℂ) :=
        Finset.sum_le_sum fun j _ => hC0 s hs K hK hsm (bvec j)
    _ = C0 * (∑ j : Fin (2 * r + k + 1), nsq (bvec j : Fin (2 * r + k + 1) → ℂ)) * (1 + K) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

end PI.PolynomialProperness
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.AddLeMulPowOfSqLeOfLeMul
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

lemma fmul_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) :
    fmul k r z 1 b = fvec k r z b := by
  simp [fmul, Matrix.one_apply]

lemma frame_mulVec_fmul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {σ : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    σ *ᵥ fmul k r z c b = fmul k r z (v * c) b := by
  show σ *ᵥ (∑ a, c a b • fvec k r z a) = ∑ a, (v * c) a b • fvec k r z a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.mulVecLin_apply, map_sum]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, fmul, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (c a b)]

lemma ut_det {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v.det = 1 := by
  rw [Matrix.det_of_upperTriangular hv.1]
  simp [hv.2]

lemma ut_mul_inv {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v (by rw [ut_det hv]; exact isUnit_one)

lemma mx_nonneg {m : ℕ} (v : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ mx v := norm_nonneg _

lemma real_sq_bound {C CA m n x : ℝ} {e : ℕ} (hm : 0 ≤ m) (hmx : m ≤ CA * x ^ e) (hx : 1 ≤ x)
    (hn : n ≤ C * m ^ 2) : n ≤ |C| * CA ^ 2 * x ^ (2 * e) := by
  have h1 : m ^ 2 ≤ (CA * x ^ e) ^ 2 := pow_le_pow_left₀ hm hmx 2
  have h2 : C * m ^ 2 ≤ |C| * m ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg m)
  calc n ≤ C * m ^ 2 := hn
    _ ≤ |C| * m ^ 2 := h2
    _ ≤ |C| * (CA * x ^ e) ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * CA ^ 2 * x ^ (2 * e) := by ring

lemma add_le_mul_pow_of_sq_le_of_le_mul {Cc D a s sp x : ℝ} {e N : ℕ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hs1 : 1 ≤ s) (hx : 1 ≤ x)
    (hs : s ^ 2 ≤ Cc * (1 + D * x ^ (2 * e + 2)) ^ 2) (hsp : sp ≤ a * s * x) (hN : 4 * e + 5 ≤ N) :
    s + sp ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ s := by linarith
  set K := 2 * e + 2 with hK
  have hxK : 1 ≤ x ^ K := one_le_pow₀ hx
  have hA : 1 + D * x ^ K ≤ (1 + D) * x ^ K := by nlinarith
  have hA0 : 0 ≤ 1 + D * x ^ K := by nlinarith
  have hs_le : s ≤ s ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 := by
    calc s ^ 2 ≤ Cc * (1 + D * x ^ K) ^ 2 := hs
      _ ≤ |Cc| * (1 + D * x ^ K) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA 2) (abs_nonneg _)
  have hsx : s ≤ |Cc| * (1 + D) ^ 2 * x ^ (2 * K) := by
    have e2 : ((1 + D) * x ^ K) ^ 2 = (1 + D) ^ 2 * x ^ (2 * K) := by ring
    rw [e2] at hs2
    nlinarith
  have hxN : x ^ (2 * K + 1) ≤ x ^ N := pow_le_pow_right₀ hx (by omega)
  have hB0 : 0 ≤ |Cc| * (1 + D) ^ 2 := by positivity
  calc s + sp ≤ s + a * s * x := by linarith
    _ ≤ (1 + a) * x * s := by nlinarith
    _ ≤ (1 + a) * x * (|Cc| * (1 + D) ^ 2 * x ^ (2 * K)) :=
        mul_le_mul_of_nonneg_left hsx (mul_nonneg (by linarith) hx0)
    _ = (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ (2 * K + 1) := by ring
    _ ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N :=
        mul_le_mul_of_nonneg_left hxN (mul_nonneg (by linarith) hB0)

theorem bound_core (hG : GVGroup) (hN : NormInv) (hNF : GNFacts)
    {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {Cf Cf' CA Cc : ℝ}
    (hCf : ∀ c b, nsq (fmul k r z c b) ≤ Cf * mx c ^ 2)
    (hCf' : ∀ c b, nsq (fmul k r z' c b) ≤ Cf' * mx c ^ 2)
    (hCc : ∀ s ∈ B.GV k r, ∀ K : ℝ, 0 ≤ K → (∀ i, nsq (s *ᵥ gramVec k r z z' γ i) ≤ K) →
      B.gN s ^ 2 ≤ Cc * (1 + K) ^ 2)
    (σ s' : B.Mat k r) (v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hσ : σ ∈ B.GV k r) (hs' : s' ∈ B.GV k r) (hv : v ∈ UTset (r + 1)) (hu : u' ∈ UTset (r + 1))
    (hσf : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (hsf : ∀ b, s' *ᵥ fvec k r z' b = fmul k r z' u' b)
    (hbv : mx v⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1)))
    (hbu : mx u'⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1))) :
    B.gN σ + B.gN s' ≤ (1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2) *
      B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2) := by
  obtain ⟨hmul, hinv⟩ := hG k r
  obtain ⟨hnn, hsub, hvec, -⟩ := hNF k r
  have hσi := hinv σ hσ
  have hγi := hinv γ hγ
  have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ hσi.2.1 _ hγ) _ hs'
  have hx1 : 1 ≤ B.gN (σ⁻¹ * γ * s') := (hN k r _ hg).2

  have hσinv_f : ∀ b, σ⁻¹ *ᵥ fvec k r z b = fmul k r z v⁻¹ b := by
    intro b
    have h1 : σ *ᵥ fmul k r z v⁻¹ b = fvec k r z b := by
      rw [frame_mulVec_fmul hσf, ut_mul_inv hv, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, hσi.2.2.2, Matrix.one_mulVec]

  have hσinv_f' : ∀ b, σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b) =
      (σ⁻¹ * γ * s') *ᵥ fmul k r z' u'⁻¹ b := by
    intro b
    have h1 : s' *ᵥ fmul k r z' u'⁻¹ b = fvec k r z' b := by
      rw [frame_mulVec_fmul hsf, ut_mul_inv hu, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hgv : ∀ i, nsq (σ⁻¹ *ᵥ gramVec k r z z' γ i) ≤
      (|Cf| + |Cf'|) * CA ^ 2 * B.gN (σ⁻¹ * γ * s') ^ (2 * (r * (r + 1)) + 2) := by
    intro i
    generalize hxg : B.gN (σ⁻¹ * γ * s') = x at hx1 hbv hbu
    have hx0 : 0 ≤ x := by linarith
    have hxp : x ^ (2 * (r * (r + 1))) ≤ x ^ (2 * (r * (r + 1)) + 2) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hc0 : 0 ≤ CA ^ 2 := sq_nonneg _
    cases i with
    | inl a =>
      show nsq (σ⁻¹ *ᵥ fvec k r z a) ≤ _
      rw [hσinv_f]
      have h1 := real_sq_bound (mx_nonneg _) hbv hx1 (hCf v⁻¹ a)
      have h2 : |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1))) ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) :=
        mul_le_mul_of_nonneg_left hxp (by positivity)
      have h3 : 0 ≤ |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
    | inr b =>
      show nsq (σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [hσinv_f']
      have h0 := hvec (σ⁻¹ * γ * s') (fmul k r z' u'⁻¹ b)
      rw [hxg] at h0
      have h1 := real_sq_bound (mx_nonneg _) hbu hx1 (hCf' u'⁻¹ b)
      have h2 : x ^ 2 * nsq (fmul k r z' u'⁻¹ b) ≤ x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) =
          |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by ring
      have h4 : 0 ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
  have hD : 0 ≤ (|Cf| + |Cf'|) * CA ^ 2 := by positivity
  have hcore := hCc σ⁻¹ hσi.2.1 _ (by positivity) hgv
  have hNσ := hN k r σ hσ
  rw [hNσ.1] at hcore
  have hs'eq : s' = γ⁻¹ * σ * (σ⁻¹ * γ * s') := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc γ⁻¹ σ σ⁻¹, hσi.2.2.1,
      Matrix.mul_one, hγi.2.2.2, Matrix.one_mul]
  have hs'b : B.gN s' ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') := by
    conv_lhs => rw [hs'eq]
    calc B.gN (γ⁻¹ * σ * (σ⁻¹ * γ * s')) ≤ B.gN (γ⁻¹ * σ) * B.gN (σ⁻¹ * γ * s') := hsub _ _
      _ ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') :=
        mul_le_mul_of_nonneg_right (hsub _ _) (hnn _)
  have hN5 : 4 * (r * (r + 1)) + 5 ≤ 5 * (r + 1) ^ 2 := by nlinarith
  exact add_le_mul_pow_of_sq_le_of_le_mul hD (hnn γ⁻¹) hNσ.2 hx1 hcore hs'b hN5

theorem polyProper_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper := by
  refine ⟨5, fun k r z z' γ hstd hpos hmono => ?_⟩
  obtain ⟨CA, hA1, hA2⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩
  · intro σ hσ s' hs'
    obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
    obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
    have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
    obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu
  · intro s hs σ' hσ'
    obtain ⟨hsG, u, hu, hsf⟩ := hS k r z hstd.2.1 s hs
    obtain ⟨hσG, v', hv', hPv, hσf⟩ := hSg' k r z z' γ hstd σ' hσ'
    have hg : s⁻¹ * γ * σ' ∈ B.GV k r := hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ s σ' u v' hsG hσG hsf hσf
    obtain ⟨hbu, hbv⟩ := hA2 u hu v' hv' hPv _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv

end PI.PolynomialProperness
end
end

namespace PI.PolynomialProperness

theorem polyProper_of_mx (hMX : MXFacts) : Formalism.FourierDecayAlt.C2.PolyProper := by
  have hT := tauMem_of hMX TauN.neFacts
  have hU := Formalism.FourierDecayAlt.P.unipotent_map_frame
  exact polyProper_of_steps gvGroup normInv gnFacts fmulBound zhatMove
    (frameS_of hU gvGroup) (frameSg_of hU hT gvGroup) (frameSg'_of hU hT gvGroup) (unitriangular_inverse_bound second_order_norm_bound)
    (coreInst_of isoCore hpkInvol gnFacts frameInd)

end PI.PolynomialProperness
