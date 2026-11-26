module

public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePLogSt
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePLogExSt
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

def LinN {C : Type} [CommRing C] {dd : ℕ} (f : Pt C 1 dd) : Prop :=
  ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (f i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)

section Gen

variable {C : Type} [CommRing C] {dd : ℕ}

theorem linN_const {f : Pt C 1 dd} (hf : LinN f) (i : Fin dd) : constantCoeff (f i) = 0 := by
  have h := hf i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h, MvPowerSeries.coeff_zero_X]

end Gen

end LogEx

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval

section Law

variable {C : Type} [Field C] [CharZero C] {d : ℕ} (G : FGLaw C d)

theorem constant_zero_zero_point {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) :
    Z0 (![0, P] : Fin 2 → Pt C n d) := by
  intro k i; fin_cases k
  · simp
  · exact hP i

theorem coordinate_point_constantCoeff {n : ℕ} (k : Fin n) : ∀ j, constantCoeff (pt C d k j) = 0 := fun j => z0_pt k j

theorem eval_eval_pair {m n : ℕ} {a b : Pt C m d} (hab : Z0 (![a, b] : Fin 2 → Pt C m d)) {E : Fin m → Pt C n d}
    (hE : Z0 E) {a' b' : Pt C n d} (ha : ∀ i, ev E (a i) = a' i) (hb : ∀ i, ev E (b i) = b' i) (f : PS C 2 d) :
    ev E (ev ![a, b] f) = ev ![a', b'] f := by
  rw [ev_ev hab hE]
  congr 1
  funext k i
  fin_cases k
  · exact ha i
  · exact hb i

theorem eval_eval_single {m n : ℕ} {a : Pt C m d} (ha0 : Z0 (![a] : Fin 1 → Pt C m d)) {E : Fin m → Pt C n d} (hE : Z0 E)
    {a' : Pt C n d} (ha : ∀ i, ev E (a i) = a' i) (f : PS C 1 d) : ev E (ev ![a] f) = ev ![a'] f := by
  rw [ev_ev ha0 hE]
  congr 1
  funext k i
  fin_cases k
  exact ha i

theorem ev_self1 (g : PS C 1 d) : ev (n := 1) ![pt C d 0] g = g := by
  unfold ev
  have h : (fun p : Fin 1 × Fin d => (![pt C d 0] : Fin 1 → Pt C 1 d) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [h, subst_self]
  rfl

theorem F_0P {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (a : Fin d) :
    ev ![0, P] (G.F a) = P a := by
  have h := congrArg (ev (![P] : Fin 1 → Pt C n d)) (G.unit a)
  rw [ev_ev (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0)) (z0_1 P hP), ev_X (z0_1 P hP)] at h
  have e : (fun k i => ev (![P] : Fin 1 → Pt C n d) ((![0, pt C d 0] : Fin 2 → Pt C 1 d) k i)) =
      (![0, P] : Fin 2 → Pt C n d) := by
    funext k i
    fin_cases k
    · exact ev_zero (z0_1 P hP)
    · exact ev_X (z0_1 P hP) 0 i
  rw [e] at h
  exact h

theorem group_law_zero_right {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (a : Fin d) :
    ev ![P, 0] (G.F a) = P a := by
  rw [← G.comm a, eval_eval_pair (z0_pp 1 0) (z0_p0 P hP) (a' := 0) (b' := P)
    (fun i => ev_X (z0_p0 P hP) 1 i) (fun i => ev_X (z0_p0 P hP) 0 i)]
  exact F_0P G P hP a

def Mm (j k : Fin d) : PS C 1 d :=
  ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F j))

theorem constant_zero_first_zero : Z0 (![pt C d 0, 0] : Fin 2 → Pt C 1 d) := z0_p0 _ (coordinate_point_constantCoeff 0)

theorem cc_Mm (j k : Fin d) : constantCoeff (Mm G j k) = if j = k then 1 else 0 := by
  rw [Mm, constantCoeff_ev constant_zero_first_zero]
  have h := congrArg (pderiv (R := C) ((0 : Fin 1), k)) (G.unit j)
  have hchain := Formalism.G.LogCR.pderiv_subst
    (a := fun p : Fin 2 × Fin d => (![0, pt C d 0] : Fin 2 → Pt C 1 d) p.1 p.2)
    (fun p => constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0) p.1 p.2)
    (G.F j) ((0 : Fin 1), k)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hchain
  unfold ev at h
  rw [hchain] at h
  rw [Finset.sum_eq_zero (fun c _ => by
      rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 0 c) = 0 from rfl, map_zero, mul_zero]), zero_add,
    Finset.sum_eq_single k] at h
  · rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 1 k) = X ((0 : Fin 1), k) from rfl, pderiv_X_self,
      mul_one] at h
    change ev ![0, pt C d 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F j)) = _ at h
    have h2 := congrArg constantCoeff h
    rw [constantCoeff_ev (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0))] at h2
    rw [h2]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [pderiv_X_of_ne (by simp [hjk]), if_neg hjk, map_zero]
  · intro c _ hc
    rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 1 c) = X ((0 : Fin 1), c) from rfl,
      pderiv_X_of_ne (by simp [hc]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

def MM : Matrix (Fin d) (Fin d) (PS C 1 d) := Matrix.of fun j k => Mm G j k

theorem MM_cc : (constantCoeff : PS C 1 d →+* C).mapMatrix (MM G) = 1 := by
  ext j k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, MM, Matrix.of_apply, cc_Mm, Matrix.one_apply]

theorem MM_det : IsUnit (MM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, MM_cc, Matrix.det_one]
  exact isUnit_one

def NN : Matrix (Fin d) (Fin d) (PS C 1 d) := (MM G)⁻¹

theorem MM_NN : MM G * NN G = 1 := Matrix.mul_nonsing_inv _ (MM_det G)

theorem pderiv_eval_single {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (g : PS C 1 d) (q : Fin n × Fin d) :
    pderiv (R := C) q (ev ![P] g) =
      ∑ b, ev ![P] (pderiv (R := C) ((0 : Fin 1), b) g) * pderiv (R := C) q (P b) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin d => (![P] : Fin 1 → Pt C n d) p.1 p.2)
    (fun p => z0_1 P hP p.1 p.2) g q, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem sum_d_pt_self {n : ℕ} (k : Fin n) (f : Fin d → PS C n d) (q : Fin d) :
    ∑ b, f b * pderiv (R := C) (k, q) (pt C d k b) = f q := by
  rw [Finset.sum_eq_single q]
  · show f q * pderiv (R := C) _ (X (k, q)) = _
    rw [pderiv_X_self, mul_one]
  · intro b _ hb
    show f b * pderiv (R := C) _ (X (k, b)) = 0
    rw [pderiv_X_of_ne (by simp [hb]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem sum_d_pt_other {n : ℕ} (k k' : Fin n) (hk : k ≠ k') (f : Fin d → PS C n d) (q : Fin d) :
    ∑ b, f b * pderiv (R := C) (k', q) (pt C d k b) = 0 :=
  Finset.sum_eq_zero fun b _ => by
    show f b * pderiv (R := C) _ (X (k, b)) = 0
    rw [pderiv_X_of_ne (by simp [hk]), mul_zero]

theorem eval_group_law_at_zero (h : PS C 1 d) : ev (n := 1) ![pt C d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [eval_eval_single (z0_1 G.F G.const) constant_zero_first_zero (a' := pt C d 0) (fun b => group_law_zero_right G (pt C d 0) (coordinate_point_constantCoeff 0) b), ev_self1]

theorem vec_cancel (u : Fin d → PS C 1 d) (a : Fin d) :
    ∑ k, (∑ c, Mm G c k * u c) * NN G k a = u a := by
  have h : ∀ c, ∑ k, Mm G c k * NN G k a = if c = a then 1 else 0 := fun c => by
    have := congrFun (congrFun (MM_NN G) c) a
    simp only [Matrix.mul_apply, Matrix.one_apply, MM, Matrix.of_apply] at this
    exact this
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ c, ∑ k, Mm G c k * u c * NN G k a = u c * ∑ k, Mm G c k * NN G k a := fun c => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e, h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Law

end LogEx

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActLog

open PartialDerivEval LogEx

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem ev_zero_pt {n : ℕ} (g : PS C 1 d) : ev (n := n) ![(0 : Pt C n d)] g = MvPowerSeries.C (constantCoeff g) := by
  have hz : (fun p : Fin 1 × Fin d => (![0] : Fin 1 → Pt C n d) p.1 p.2) = 0 := by
    funext p
    obtain ⟨k, b⟩ := p
    fin_cases k
    rfl
  rw [ev, hz, subst_zero_eq_C_constantCoeff, map_C]
  simp

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv (R := C) i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem add_zero_of (G : FGLaw C d) (Q : PS C 1 d)
    (hQ : ev (n := 2) ![G.F] Q = ev (n := 2) ![pt C d 0] Q + ev (n := 2) ![pt C d 1] Q)
    (hlin : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) Q = 0) (hc : constantCoeff Q = 0) : Q = 0 := by
  classical
  let A : Matrix (Fin d) (Fin d) (PS C 1 d) := Matrix.of fun k b =>
    ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F b))
  let u : Fin d → PS C 1 d := fun b => pderiv (R := C) ((0 : Fin 1), b) Q
  have hX (k b : Fin d) :
      pderiv (R := C) ((0 : Fin 1), k) (pt C d 0 b) = if k = b then 1 else 0 := by
    by_cases h : k = b
    · subst b
      simp [pt]
    · rw [ite_eq_right h]
      exact pderiv_X_of_ne (by simpa using Ne.symm h)
  have hA : (constantCoeff : PS C 1 d →+* C).mapMatrix A = 1 := by
    ext k b
    have hz := constant_zero_zero_point (pt C (n := 1) d 0) (coordinate_point_constantCoeff 0)
    have h := congrArg (pderiv (R := C) ((0 : Fin 1), k)) (G.unit b)
    change pderiv ((0 : Fin 1), k) (ev ![0, pt C d 0] (G.F b)) =
      pderiv ((0 : Fin 1), k) (pt C d 0 b) at h
    rw [ev, Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 2 × Fin d => (![0, pt C d 0] : Fin 2 → Pt C 1 d) p.1 p.2)
      (fun p => hz p.1 p.2),
      Fintype.sum_prod_type, Fin.sum_univ_two] at h
    change (∑ j, ev ![0, pt C d 0] (pderiv ((0 : Fin 2), j) (G.F b)) *
        pderiv ((0 : Fin 1), k) (0 : PS C 1 d)) +
      (∑ j, ev ![0, pt C d 0] (pderiv ((1 : Fin 2), j) (G.F b)) *
        pderiv ((0 : Fin 1), k) (pt C d 0 j)) = _ at h
    simp only [map_zero, mul_zero, Finset.sum_const_zero, zero_add, hX, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    have hcc := congrArg constantCoeff h
    rw [constantCoeff_ev hz, apply_ite constantCoeff, map_one, map_zero] at hcc
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, A, Matrix.of_apply, Matrix.one_apply,
      constantCoeff_ev constant_zero_first_zero] using hcc
  have hdet : IsUnit A.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hA, Matrix.det_one]
    exact isUnit_one
  have hchain (P : Pt C 2 d) (hP : ∀ j, constantCoeff (P j) = 0) (q : Fin 2 × Fin d) :
      pderiv q (ev ![P] Q) = ∑ b, ev ![P] (u b) * pderiv q (P b) := by
    unfold ev
    rw [Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 1 × Fin d => (![P] : Fin 1 → Pt C 2 d) p.1 p.2)
      (fun p => z0_1 P hP p.1 p.2) Q q,
      Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  have hrow : A.mulVec u = 0 := by
    funext k
    have h0 : pderiv ((1 : Fin 2), k) (ev ![pt C d 0] Q) = 0 := by
      rw [hchain _ (coordinate_point_constantCoeff 0)]
      exact Finset.sum_eq_zero fun b _ => by simp [pt]
    have h1 : pderiv ((1 : Fin 2), k) (ev ![pt C d 1] Q) = ev ![pt C d 1] (u k) := by
      rw [hchain _ (coordinate_point_constantCoeff 1), Finset.sum_eq_single k]
      · simp [pt]
      · intro b _ hb
        rw [show pt C d 1 b = X ((1 : Fin 2), b) from rfl, pderiv_X_of_ne (by simp [hb]), mul_zero]
      · simp
    have D := congrArg (fun g => ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) g)) hQ
    rw [map_add (f := _), h0, h1, zero_add, hchain G.F G.const] at D
    rw [ev_sum constant_zero_first_zero] at D
    simp only [PartialDerivEval.ev_mul constant_zero_first_zero, eval_group_law_at_zero G] at D
    rw [eval_eval_single (z0_1 (pt C d 1) (coordinate_point_constantCoeff 1)) constant_zero_first_zero (a' := (0 : Pt C 1 d)) (fun j => ev_X constant_zero_first_zero 1 j), ev_zero_pt,
      show u k = pderiv ((0 : Fin 1), k) Q from rfl, cc_pderiv, hlin k, map_zero] at D
    change (∑ b, A k b * u b) = 0
    change (∑ b, u b * A k b) = 0 at D
    simpa only [mul_comm (A k _) (u _)] using D
  have hd : u = 0 := by
    have h := congrArg (fun v => (A⁻¹).mulVec v) hrow
    change (A⁻¹).mulVec (A.mulVec u) = (A⁻¹).mulVec 0 at h
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  apply pderiv.ext
  · intro q
    obtain ⟨q1, q2⟩ := q
    fin_cases q1
    rw [map_zero]
    exact congrFun hd q2
  · rw [hc, map_zero]

def linM (φ : Pt C 1 d) (i j : Fin d) : C := coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linN_coeff {lg : Pt C 1 d} (hlin : LinN lg) (j b : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), b) 1) (lg j) = if b = j then 1 else 0 := by
  rw [hlin j _ (by rw [Finsupp.degree_single]), coeff_X]
  by_cases h : b = j
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd ((Finsupp.single_left_inj one_ne_zero).mp e))

theorem log_endo (G : FGLaw C d) (lg : Pt C 1 d) (hlin : LinN lg)
    (hadd : ∀ i, ev (n := 2) ![addOf G.F (pt C d 0) (pt C d 1)] (lg i) =
      ev (n := 2) ![pt C d 0] (lg i) + ev (n := 2) ![pt C d 1] (lg i))
    (φ : Pt C 1 d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hφ : comp1 φ (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1)))
    (i : Fin d) : comp1 lg φ i = ∑ j, MvPowerSeries.C (linM φ i j) * lg j := by
  have haddF : addOf G.F (pt C d 0) (pt C d 1) = (G.F : Pt C 2 d) := funext fun j => eval_points_two (G.F j)
  have hF : ∀ j, ev (n := 2) ![G.F] (lg j) = ev (n := 2) ![pt C d 0] (lg j) + ev (n := 2) ![pt C d 1] (lg j) := by
    intro j; rw [← haddF]; exact hadd j
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C 1 d) := z0_1 φ hφ0
  have hFz : Z0 (![G.F] : Fin 1 → Pt C 2 d) := z0_1 G.F G.const
  have hP0 : Z0 (![pt C d 0] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 0)
  have hP1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 1)
  set A : Pt C 2 d := comp1 φ (pt C (n := 2) d 0) with hA
  set B : Pt C 2 d := comp1 φ (pt C (n := 2) d 1) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => const_ev hP0 (hφ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j => const_ev hP1 (hφ0 j)
  have hAB : Z0 (![A, B] : Fin 2 → Pt C 2 d) := by
    intro k j; fin_cases k
    · exact hA0 j
    · exact hB0 j

  have hlgAB : ∀ j, ev (n := 2) ![addOf G.F A B] (lg j) = ev (n := 2) ![A] (lg j) + ev (n := 2) ![B] (lg j) := by
    intro j
    have h := congrArg (ev (n := 2) ![A, B]) (hF j)
    have hFc : ∀ k, constantCoeff (G.F k) = 0 := G.const
    rw [ev_add hAB, eval_eval_single hFz hAB (a' := addOf G.F A B) (fun k => rfl),
      eval_eval_single hP0 hAB (a' := A) (fun k => ev_X hAB 0 k),
      eval_eval_single hP1 hAB (a' := B) (fun k => ev_X hAB 1 k)] at h
    exact h

  have hcomp : ev (n := 2) ![G.F] (comp1 lg φ i) =
      ev (n := 2) ![pt C d 0] (comp1 lg φ i) + ev (n := 2) ![pt C d 1] (comp1 lg φ i) := by
    have e1 : ev (n := 2) ![G.F] (comp1 lg φ i) = ev (n := 2) ![comp1 φ G.F] (lg i) :=
      eval_eval_single hφ1 hFz (a' := comp1 φ G.F) (fun k => rfl) (lg i)
    have e2 : comp1 φ G.F = addOf G.F A B :=
      calc comp1 φ G.F = comp1 φ (addOf G.F (pt C d 0) (pt C d 1)) := by rw [haddF]
        _ = addOf G.F A B := hφ
    have e3 : ev (n := 2) ![pt C d 0] (comp1 lg φ i) = ev (n := 2) ![A] (lg i) :=
      eval_eval_single hφ1 hP0 (a' := A) (fun k => rfl) (lg i)
    have e4 : ev (n := 2) ![pt C d 1] (comp1 lg φ i) = ev (n := 2) ![B] (lg i) :=
      eval_eval_single hφ1 hP1 (a' := B) (fun k => rfl) (lg i)
    rw [e1, e2, e3, e4, hlgAB]
  have hQ := add_zero_of G (comp1 lg φ i - ∑ j, MvPowerSeries.C (linM φ i j) * lg j) (by
      rw [ev_sub hFz, ev_sub hP0, ev_sub hP1, ev_sum hFz, ev_sum hP0, ev_sum hP1, hcomp]
      simp only [PartialDerivEval.ev_mul hFz, PartialDerivEval.ev_mul hP0, PartialDerivEval.ev_mul hP1, PartialDerivEval.ev_C, hF, mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [coeff_C_mul, linN_coeff hlin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← cc_pderiv, show comp1 lg φ i = ev ![φ] (lg i) from rfl]
      have hchain :
          pderiv ((0 : Fin 1), k) (ev ![φ] (lg i)) =
            ∑ b, ev ![φ] (pderiv ((0 : Fin 1), b) (lg i)) * pderiv ((0 : Fin 1), k) (φ b) := by
        unfold ev
        rw [Formalism.G.LogCR.pderiv_subst
          (a := fun p : Fin 1 × Fin d => (![φ] : Fin 1 → Pt C 1 d) p.1 p.2)
          (fun p => hφ1 p.1 p.2),
          Fintype.sum_prod_type, Fin.sum_univ_one]
        rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hchain, map_sum]
      simp only [map_mul, constantCoeff_ev hφ1, cc_pderiv, linN_coeff hlin, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      unfold linM
      ring)
    (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, show comp1 lg φ i = ev ![φ] (lg i) from rfl, constantCoeff_ev hφ1, linN_const hlin]
      simp [linN_const hlin])
  exact sub_eq_zero.mp hQ

end OActLog

end Formalism.L2.FormalSeriesBounds
