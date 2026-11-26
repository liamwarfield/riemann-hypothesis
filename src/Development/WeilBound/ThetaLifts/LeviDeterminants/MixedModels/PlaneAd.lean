module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneGen
noncomputable section

namespace PositivityTheory.Mix

open Matrix

variable {R : Type} [CommRing R] {n k : ℕ}

def bf (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ fun i => c (v i)

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}

theorem bf_add_l (u u' v) : bf c J (u + u') v = bf c J u v + bf c J u' v := by
  simp [bf, add_dotProduct]
theorem bf_smul_l (a : R) (u v) : bf c J (a • u) v = a * bf c J u v := by
  simp [bf, smul_dotProduct]
theorem bf_add_r (u v v') : bf c J u (v + v') = bf c J u v + bf c J u v' := by
  have e : (fun i => c ((v + v') i)) = (fun i => c (v i)) + (fun i => c (v' i)) := by
    funext i
    simp
  simp only [bf, e, mulVec_add, dotProduct_add]
theorem bf_smul_r (a : R) (u v) : bf c J u (a • v) = c a * bf c J u v := by
  have e : (fun i => c ((a • v) i)) = c a • (fun i => c (v i)) := by
    funext i
    simp
  simp only [bf, e, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bf_mulVec (M : Matrix (Fin n) (Fin n) R) (u v) : bf c J (M *ᵥ u) (M *ᵥ v) = bf c (Mᵀ * J * M.map c) u v := by
  have hc : (fun i => c ((M *ᵥ v) i)) = M.map c *ᵥ fun i => c (v i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  simp only [bf]
  rw [hc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Mᵀ, vecMul_transpose]

theorem bf_single (i j : Fin n) : bf c J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have e : (fun l => c ((Pi.single j 1 : Fin n → R) l)) = (Pi.single j 1 : Fin n → R) := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  simp only [bf, e, mulVec_single_one, single_one_dotProduct]
  rfl

structure PlaneOK (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x y : Fin n → R) (ι : Matrix (Fin n) (Fin k) R) : Prop where
  cc : ∀ a, c (c a) = a
  ee : ε * ε = 1
  ce : c ε = ε
  herm : ∀ i j, c (J j i) = ε * J i j
  xx : bf c J x x = 0
  yy : bf c J y y = 0
  xy : bf c J x y = 1
  ix : ∀ z, bf c J (ι *ᵥ z) x = 0
  iy : ∀ z, bf c J (ι *ᵥ z) y = 0
  span : ∀ v, ∃ (s t : R) (z : Fin k → R), v = s • x + ι *ᵥ z + t • y
  nd : ∀ v, (∀ w, bf c J v w = 0) → v = 0

namespace PlaneOK

variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h

theorem symm (u v) : bf c J v u = ε * c (bf c J u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bf, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, h.cc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.herm]
  linear_combination (-(v i * J i j * c (u j))) * h.ee

theorem yx : bf c J y x = ε := by rw [h.symm, h.xy, map_one, mul_one]
theorem xi (z) : bf c J x (ι *ᵥ z) = 0 := by rw [h.symm, h.ix, map_zero, mul_zero]
theorem yi (z) : bf c J y (ι *ᵥ z) = 0 := by rw [h.symm, h.iy, map_zero, mul_zero]

theorem ext {A B : Matrix (Fin n) (Fin n) R} (hx : A *ᵥ x = B *ᵥ x) (hy : A *ᵥ y = B *ᵥ y)
    (hi : ∀ z, A *ᵥ (ι *ᵥ z) = B *ᵥ (ι *ᵥ z)) : A = B := by
  have hv : ∀ v, A *ᵥ v = B *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := h.span v
    simp only [mulVec_add, mulVec_smul, hx, hy, hi]
  ext i j
  have e := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using e


omit h in
def lev (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) + ((s - 1) * ε) • vecMulVec y (J *ᵥ fun i => c (x i))

omit h in
theorem lev_apply (t s : R) (v) : lev c J ε x y t s *ᵥ v = v + ((t - 1) * bf c J v y) • x + ((s - 1) * ε * bf c J v x) • y := by
  have vm : ∀ p q w : Fin n → R, vecMulVec p q *ᵥ w = (q ⬝ᵥ w) • p := by
    intro p q w
    ext i
    simp only [vecMulVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [lev, add_mulVec, one_mulVec, smul_mulVec, vm, smul_smul]
  rw [dotProduct_comm (J *ᵥ fun i => c (y i)) v, dotProduct_comm (J *ᵥ fun i => c (x i)) v]
  rfl

theorem levi_element_fixes_first_vector (t s : R) : lev c J ε x y t s *ᵥ x = t • x := by
  rw [lev_apply, h.xy, h.xx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]
  abel
theorem lev_y (t s : R) : lev c J ε x y t s *ᵥ y = s • y := by
  rw [lev_apply, h.yy, h.yx]
  have e : (s - 1) * ε * ε = s - 1 := by rw [mul_assoc, h.ee, mul_one]
  rw [e]
  simp only [mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]
  abel
theorem lev_i (t s : R) (z) : lev c J ε x y t s *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
  rw [lev_apply, h.iy, h.ix]
  simp

theorem lev_mul {t t' s s' : R} (h1 : t * t' = 1) (h2 : s * s' = 1) : lev c J ε x y t s * lev c J ε x y t' s' = 1 := by
  apply h.ext
  · rw [← mulVec_mulVec, h.levi_element_fixes_first_vector, mulVec_smul, h.levi_element_fixes_first_vector, smul_smul, mul_comm, h1, one_smul, one_mulVec]
  · rw [← mulVec_mulVec, h.lev_y, mulVec_smul, h.lev_y, smul_smul, mul_comm, h2, one_smul, one_mulVec]
  · intro z
    rw [← mulVec_mulVec, h.lev_i, h.lev_i, one_mulVec]

theorem lev_unit {t s : R} (h1 : t * c s = 1) : (lev c J ε x y t s)ᵀ * J * (lev c J ε x y t s).map c = J := by
  have hcs : s * c t = 1 := by
    have e := congrArg c h1
    rw [map_mul, h.cc, map_one] at e
    rw [mul_comm]
    exact e
  have key : ∀ u v, bf c J (lev c J ε x y t s *ᵥ u) (lev c J ε x y t s *ᵥ v) = bf c J u v := by
    intro u v
    obtain ⟨a, b, z, rfl⟩ := h.span u
    obtain ⟨a', b', z', rfl⟩ := h.span v
    simp only [mulVec_add, mulVec_smul, h.levi_element_fixes_first_vector, h.lev_y, h.lev_i, bf_add_l, bf_add_r, bf_smul_l, bf_smul_r,
      h.xx, h.yy, h.xy, h.yx, h.ix, h.iy, h.xi, h.yi, map_mul, smul_smul]
    linear_combination (a * c b') * h1 + (b * c a' * ε) * hcs
  ext i j
  have e := key (Pi.single i 1) (Pi.single j 1)
  rw [bf_mulVec, bf_single, bf_single] at e
  exact e

theorem exists_lev (t : Rˣ) : ∃ m : GL (Fin n) R, m.1ᵀ * J * m.1.map c = J ∧ m.1 *ᵥ x = t.1 • x ∧ m.1 *ᵥ y = c (t⁻¹).1 • y ∧
    ∀ z, m.1 *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
  have hc1 : c (t⁻¹ : Rˣ).1 * c t.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hc2 : c t.1 * c (t⁻¹ : Rˣ).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨lev c J ε x y t.1 (c (t⁻¹ : Rˣ).1), lev c J ε x y (t⁻¹ : Rˣ).1 (c t.1),
    h.lev_mul (Units.mul_inv t) hc1, h.lev_mul (Units.inv_mul t) hc2⟩, ?_, h.levi_element_fixes_first_vector _ _, h.lev_y _ _, fun z => h.lev_i _ _ z⟩
  apply h.lev_unit
  rw [h.cc, Units.mul_inv]

end PlaneOK

end PositivityTheory.Mix
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.Mix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n k : ℕ}

theorem det_ne_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hr, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hr.symm).trans finSumFinEquiv.symm
  have h1 : (A.submatrix id e)ᵀ * M * (A.submatrix id e).map star = (Aᵀ * M * A.map star).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  intro h0
  have h2 := congrArg Matrix.det h1
  rw [hA, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_neg] at h2
  simp at h2
  exact pow_ne_zero s (neg_ne_zero.2 one_ne_zero) h2.symm

theorem conj_conj {B : Base F E} (h : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact φ.injective (by rw [h.cm.2.2.2, h.cm.2.2.2, star_star])

theorem cA_inc (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := rfl

theorem bf_inc (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E) :
    bf (cA σ).toRingHom (incM F J) (incV F u) (incV F v) = inclR (F := F) (AF F) (form σ J u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bf, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  rfl

theorem inc_mulVec {m : ℕ} (A : Matrix (Fin n) (Fin m) E) (u : Fin m → E) : incM F A *ᵥ incV F u = incV F (A *ᵥ u) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) A u i).symm

theorem vec_eq {m : ℕ} (z : Fin m → AE F E) : z = ∑ j, z j • incV F (Pi.single j 1) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, incV, Pi.single_apply, apply_ite, map_one, map_zero, smul_eq_mul, mul_one, mul_zero]
  simp

theorem bf_sum_l {R : Type} [CommRing R] {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {m : ℕ} (u : Fin m → Fin n → R) (v) :
    bf c J (∑ j, u j) v = ∑ j, bf c J (u j) v := sum_dotProduct _ _ _

theorem planeOK {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E k} {H : Plane E n k} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (ε : ℤˣ) (hJ : ∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j) (hd : Y.J.det ≠ 0)
    (hL : Y.L.IsFullLattice E) :
    PlaneOK (cA σ).toRingHom (incM F Y.J) ((ε : ℤ) : AE F E) (incV F H.x) (incV F H.y) (incM F H.ι) := by
  have cc : ∀ a : AE F E, cA σ (cA σ a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a e =>
      change a ⊗ₜ σ (σ e) = _
      rw [conj_conj hB]
  have orth : ∀ w : Fin n → E, (∀ u, form σ Y.J (H.ι *ᵥ u) w = 0) → ∀ z,
      bf (cA σ).toRingHom (incM F Y.J) (incM F H.ι *ᵥ z) (incV F w) = 0 := fun w hw z => by
    rw [vec_eq z, Matrix.mulVec_sum, bf_sum_l]
    exact Finset.sum_eq_zero fun j _ => by rw [Matrix.mulVec_smul, bf_smul_l, inc_mulVec, bf_inc, hw, map_zero, mul_zero]
  have sp : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin k → E), v = s • H.x + H.ι *ᵥ u + t • H.y := fun v => by
    have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := Submodule.IsFullLattice.span_eq_top (A := E) (M := Y.L) ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, e⟩ := hH.split z hz
      exact ⟨s, t, u, e⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, t, u, rfl⟩ := ha
      obtain ⟨s', t', u', rfl⟩ := hb
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a b _ hb =>
      obtain ⟨s, t, u, rfl⟩ := hb
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  refine ⟨cc, by rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp, map_intCast _ _, fun i j => ?_,
    by rw [bf_inc, hH.xx, map_zero], by rw [bf_inc, hH.yy, map_zero], by rw [bf_inc, hH.xy, map_one],
    orth _ fun u => (hH.orth u).1, orth _ fun u => (hH.orth u).2, fun v => ?_, fun v hv => ?_⟩
  · change inclR (F := F) (AF F) (σ (Y.J j i)) = _ * inclR (F := F) (AF F) (Y.J i j)
    rw [hJ, map_mul, map_intCast]
  · choose s t u e using fun j : Fin n => sp (Pi.single j 1)
    refine ⟨∑ j, v j * inclR (F := F) (AF F) (s j), ∑ j, v j * inclR (F := F) (AF F) (t j), ∑ j, v j • incV F (u j), ?_⟩
    conv_lhs => rw [vec_eq v]
    rw [Finset.sum_smul, Finset.sum_smul, Matrix.mulVec_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, inc_mulVec, e j]
    funext i
    simp only [incV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    ring
  · have hu : IsUnit (incM F Y.J).det := by
      have := (isUnit_iff_ne_zero.2 hd).map (inclR (F := F) (E := E) (AF F))
      rwa [RingHom.map_det] at this
    have h0 : v ᵥ* incM F Y.J = 0 := funext fun j => by
      have := hv (Pi.single j 1)
      have e : (fun l => (cA σ).toRingHom ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := funext fun l => by
        by_cases h : l = j <;> simp [Pi.single_apply, h]
      rw [bf, e, Matrix.dotProduct_mulVec] at this
      simpa using this
    have := congrArg (· ᵥ* (incM F Y.J)⁻¹) h0
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu] using this

theorem full_of_dual_zero {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n}
    (ε : ℤˣ) (hJ : ∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j)
    (hL : Y.L.IsLattice E)
    (hdual : ∀ y, (∀ x ∈ Y.L, form σ Y.J y x = 0) → y ∈ Y.L) :
    Y.L.IsFullLattice E := by
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
      simpa only [form, y, conj_conj hB] using hz'
    have hs : σ (form σ Y.J y x) = ((ε : ℤ) : E) * form σ Y.J x y := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, conj_conj hB, hJ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hzero, mul_zero] at hs
    exact (map_eq_zero σ).1 hs
  have hline (a : E) : a • y ∈ Y.L := hdual _ fun x hx => by
    simpa only [form, smul_dotProduct, smul_eq_mul] using
      (show a * form σ Y.J y x = 0 by rw [horth x hx, mul_zero])
  let i : E →ₗ[𝓞 E] Y.L :=
    ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict Y.L hline
  let : Module.Finite (𝓞 E) Y.L := Module.Finite.iff_fg.mpr hL.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E hy₀ (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem planeOK_herm {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E k} {H : Plane E n k} {i₀ i₁ r s : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsHerm σ B r s) :
    ∃ ε, PlaneOK (cA σ).toRingHom (incM F Y.J) ε (incV F H.x) (incV F H.y) (incM F H.ι) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨_, planeOK hB hH 1 (fun i j => by simp [hY.herm]) (fun h0 => det_ne_of_sig (hY.sig w) ?_) hY.lat⟩
  have := RingHom.map_det (B.emb w).1 Y.J
  rw [h0, map_zero] at this
  exact this.symm

theorem planeOK_skew {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E k} {H : Plane E n k} {i₀ i₁ r s : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsSkew σ B r s) :
    ∃ ε, PlaneOK (cA σ).toRingHom (incM F Y.J) ε (incV F H.x) (incV F H.y) (incM F H.ι) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨_, planeOK hB hH (-1) (fun i j => by simp [hY.skew]) (fun h0 => det_ne_of_sig (hY.sig w) ?_) hY.lat⟩
  have := RingHom.map_det (B.emb w).1 Y.J
  rw [h0, map_zero] at this
  rw [Matrix.det_smul]
  exact mul_eq_zero_of_right _ this.symm

def matH (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : UA σ J →* Matrix (Fin n) (Fin n) (AE F E) :=
  (Units.coeHom _).comp (Subgroup.subtype _)

theorem matH_inj (J : Matrix (Fin n) (Fin n) E) : Function.Injective (matH σ J) := fun _ _ h => Subtype.ext (Units.ext h)

variable {Y : Spc F E n} {H : Plane E n k} {ε : AE F E}

theorem exists_scale (h : PlaneOK (cA σ).toRingHom (incM F Y.J) ε (incV F H.x) (incV F H.y) (incM F H.ι)) (t : ℕ) (ht : t ≠ 0) :
    ∃ m : UA σ Y.J, mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
      (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin k → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  have hu : IsUnit (t : AE F E) := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 ht : (t : E) ≠ 0)).map (inclR (F := F) (E := E) (AF F))
    rwa [map_natCast] at this
  obtain ⟨u, hu⟩ := hu
  obtain ⟨m, h0, h1, h2, h3⟩ := h.exists_lev u
  refine ⟨⟨m, h0⟩, hu ▸ h1, ?_, h3⟩
  change (t : AE F E) • (m.1 *ᵥ _) = _
  rw [h2, smul_smul, ← map_natCast (cA σ).toRingHom t, ← map_mul, ← hu, u.mul_inv, map_one, one_smul]

end PositivityTheory.Mix
