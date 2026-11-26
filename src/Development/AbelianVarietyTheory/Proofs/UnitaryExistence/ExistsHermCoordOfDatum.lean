module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumCoord

variable {E : Type} [Field E] [NumberField E]

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.DatumCoord.eq_of_trace_int {c d : E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * c) = Algebra.trace ℚ E ((a : E) * d)) :
    c = d := by
  by_contra hcd
  have hne : c - d ≠ 0 := sub_ne_zero.2 hcd
  have halg : IsAlgebraic ℤ (c - d)⁻¹ :=
    IsFractionRing.isAlgebraic_iff ℤ ℚ _ |>.mpr (.of_finite ℚ _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have key := h ⟨y • (c - d)⁻¹, hint⟩
  rw [← sub_eq_zero, ← map_sub, ← mul_sub] at key
  change Algebra.trace ℚ E (y • (c - d)⁻¹ * (c - d)) = 0 at key
  rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one,
    show (y : E) = algebraMap ℚ E y by simp, Algebra.trace_algebraMap] at key
  simp [hy, Module.finrank_pos.ne'] at key

variable [IsCMField E]

end GlobalTheory.DatumCoord

namespace GlobalTheory

open DatumCoord

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
private lemma exists_trace_mul_eq_of_addMonoidHom (f : 𝓞 E →+ ℤ) :
    ∃ z : E, ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * z) = (f a : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => (f (RingOfIntegers.basis E i) : ℚ))
  have hnd := traceForm_nondegenerate ℚ E
  obtain ⟨z, hz⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective g
  refine ⟨z, fun a => ?_⟩
  have h1 : ∀ b : E, Algebra.trace ℚ E (b * z) = g b := fun b => by
    rw [← hz]; simp [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
  let u : 𝓞 E →ₗ[ℤ] ℚ :=
    (g.restrictScalars ℤ).comp ((algebraMap (𝓞 E) E : 𝓞 E →+* E).toIntAlgHom.toLinearMap)
  let v : 𝓞 E →ₗ[ℤ] ℚ := (Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp f.toIntLinearMap
  have huv : u = v := (RingOfIntegers.basis E).ext fun i => by
    simp [u, v, g, ← integralBasis_apply]
  rw [h1]
  exact congrArg (fun w : 𝓞 E →ₗ[ℤ] ℚ => w a) huv


open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
theorem _root_.GlobalTheory.exists_herm_coord_of_datum :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (ξ : E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → ξ ≠ 0 → ∀ r : ℕ, r = D.p + D.q →
      ∃ (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)),
        (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
          (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
          ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) := by
  intro E _ _ _ H D ξ hξ hξ0 r hr
  have hz : ∀ x y : D.La, ∃ z : E, ∀ a : 𝓞 E,
      Algebra.trace ℚ E ((a : E) * z) = (D.EF (a • x) y : ℚ) := fun x y =>
    exists_trace_mul_eq_of_addMonoidHom (AddMonoidHom.mk' (fun a => D.EF (a • x) y) fun a b => by simp [add_smul])
  choose h0 hh0 using hz
  have huniq := fun c d h => _root_.GlobalTheory.DatumCoord.eq_of_trace_int (E := E) (c := c) (d := d) h
  have hsmul : ∀ (b : 𝓞 E) x y, h0 (b • x) y = b * h0 x y := fun b x y => huniq _ _ fun a => by
    rw [hh0, ← mul_assoc, ← map_mul, hh0, smul_smul]
  have hadd : ∀ x x' y, h0 (x + x') y = h0 x y + h0 x' y := fun x x' y => huniq _ _ fun a => by
    rw [hh0, mul_add, map_add (f := _), hh0, hh0]; simp [smul_add]
  have hadd' : ∀ x y y', h0 x (y + y') = h0 x y + h0 x y' := fun x y y' => huniq _ _ fun a => by
    rw [mul_add, map_add (f := _), hh0, hh0, hh0, map_add (f := _), Int.cast_add]
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσ : ∀ e, σ e = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc e := fun e => rfl
  have hσσ : ∀ e, σ (σ e) = e := fun e => by simp [σ]
  have hbar : ∀ b, ((H.bar b : 𝓞 E) : E) = σ b := fun b => H.bar_eq b
  have hbb : ∀ b, H.bar (H.bar b) = b := fun b => RingOfIntegers.ext (by rw [hbar, hbar, hσσ])
  have htr : ∀ e, Algebra.trace ℚ E (σ e) = Algebra.trace ℚ E e := fun e =>
    Algebra.trace_eq_of_algEquiv σ e
  have hanti : ∀ u v, D.EF u v = - D.EF v u := fun u v => by
    have h := D.alt (u + v)
    simp only [map_add (f := _), LinearMap.add_apply, D.alt u, D.alt v] at h
    omega
  have hsmul' : ∀ (b : 𝓞 E) x y, h0 x (b • y) = σ b * h0 x y := fun b x y => huniq _ _ fun a => by
    rw [hh0, ← hbb b, ← D.adj, smul_smul, ← hh0, hbb]
    congr 1
    push_cast [hbar]
    ring
  have hherm : ∀ x y, h0 y x = - σ (h0 x y) := fun x y => huniq _ _ fun a => by
    rw [hh0, hanti, ← hbb a, ← D.adj, Int.cast_neg, ← hh0, hbb, hbar, ← htr (σ a * h0 x y),
      map_mul, hσσ, mul_neg, map_neg]
  haveI := D.fin
  have hrk : Module.finrank (𝓞 E) D.La = r := hr ▸ D.rank
  obtain ⟨l, hl⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := D.La) hrk.ge
  have hmax : ∀ x : D.La, ∃ t : 𝓞 E, t ≠ 0 ∧ ∃ c : Fin r → 𝓞 E, ∑ i, c i • l i = t • x := by
    intro x
    have hnot : ¬ LinearIndependent (𝓞 E) (Fin.snoc l x : Fin (r + 1) → D.La) := fun h => by
      have := h.fintype_card_le_finrank
      simp [hrk] at this
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    refine ⟨g (Fin.last r), fun hg0 => hi ?_, fun j => -g j.castSucc, ?_⟩
    · rw [hg0, zero_smul, add_zero] at hg
      have := Fintype.linearIndependent_iff.1 hl _ hg
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact this j
      · exact hg0
    · simp only [neg_smul, Finset.sum_neg_distrib]
      exact neg_eq_of_add_eq_zero_right hg
  have hz0 : ∀ y, h0 0 y = 0 := fun y => by simpa using hadd 0 0 y
  have hz0' : ∀ x, h0 x 0 = 0 := fun x => by simpa using hadd' x 0 0
  have hsumL : ∀ (c : Fin r → 𝓞 E) y, h0 (∑ i, c i • l i) y = ∑ i, (c i : E) * h0 (l i) y := by
    intro c y
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  have hsumR : ∀ (d : Fin r → 𝓞 E) x, h0 x (∑ j, d j • l j) = ∑ j, σ (d j) * h0 x (l j) := by
    intro d x
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [hz0']
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd', hsmul', ih]
  have hσ0 : ∀ s : 𝓞 E, s ≠ 0 → σ s ≠ 0 := fun s hs => by simpa using hs
  have hnd : ∀ x, (∀ y, h0 x y = 0) → x = 0 := fun x hx => D.unimod.1 (LinearMap.ext fun y => by
    have := hh0 x y 1
    rw [hx, mul_zero, map_zero, one_smul] at this
    simp only [map_zero, LinearMap.zero_apply]
    exact_mod_cast this.symm)
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) :=
    { toFun := fun x j => h0 x (l j)
      map_add' := fun x y => funext fun j => hadd _ _ _
      map_smul' := fun b x => funext fun j => by simp [hsmul, Algebra.smul_def] }
  have hψ : ∀ x j, ψ x j = h0 x (l j) := fun x j => rfl
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx => hnd x fun y => by
    obtain ⟨s, hs, d, hd⟩ := hmax y
    have h1 : σ s * h0 x y = 0 := by
      rw [← hsmul', ← hd, hsumR]
      exact Finset.sum_eq_zero fun j _ => by rw [← hψ, hx]; simp
    exact (mul_eq_zero.1 h1).resolve_left (hσ0 s hs)
  let gram : Matrix (Fin r) (Fin r) E := Matrix.of fun i j => h0 (l i) (l j)
  have hgramσ : ∀ i j, σ (gram i j) = - gram j i := fun i j => by
    simp [gram, hherm (l i) (l j), hσσ]
  have hdet : gram.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨⟨m, hm⟩, hmv⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ v
    choose c hc using fun i => hmv i (Finset.mem_univ i)
    have hx : ∑ i, c i • l i = 0 := hinj <| funext fun j => by
      rw [map_zero, Pi.zero_apply, hψ, hsumL]
      have := congrFun hv j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, gram, Matrix.of_apply] at this
      simp only [hc, Submonoid.smul_def, Algebra.smul_def, mul_assoc, ← Finset.mul_sum, this,
        mul_zero]
    have hc0 := Fintype.linearIndependent_iff.1 hl c hx
    apply hv0
    funext i
    have := hc i
    rw [hc0 i, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by simpa using nonZeroDivisors.ne_zero hm)
  refine ⟨-ξ⁻¹ • gram⁻¹, ψ, hinj, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro w _
    have hw : w = ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) := by
      have hsum : ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) = (w ᵥ* gram⁻¹) ᵥ* gram := by
        funext j
        simp [Matrix.vecMul, dotProduct, Finset.sum_apply, hψ, gram]
      rw [hsum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.vecMul_one]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l i, rfl⟩)
  · have hu : IsUnit gram.det := isUnit_iff_ne_zero.2 hdet
    have h1 : gram.map σ = -gramᵀ := by
      ext i j
      simp [hgramσ]
    have e1 : (gram⁻¹).map σ * gram.map σ = 1 := by
      have h3 : (gram⁻¹ * gram).map (σ : E →+* E) = (gram⁻¹).map σ * gram.map σ := Matrix.map_mul
      rw [← h3, Matrix.nonsing_inv_mul _ hu]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : -(gram⁻¹)ᵀ * gram.map σ = 1 := by
      rw [h1, neg_mul_neg, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    have hinvσ : (gram⁻¹).map σ = -(gram⁻¹)ᵀ :=
      (Matrix.inv_eq_left_inv e1).symm.trans (Matrix.inv_eq_left_inv e2)
    intro a b
    have h2 := congrFun (congrFun hinvσ a) b
    have hξσ : σ ξ = -ξ := hξ
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply] at h2
    rw [← hσ]
    simp [Matrix.smul_apply, map_inv₀, hξσ, h2]
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hξ0)))
      (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hdet)).ne_zero
  · have hu : IsUnit gram.det := isUnit_iff_ne_zero.2 hdet
    intro x y
    obtain ⟨t, ht, c, hc⟩ := hmax x
    obtain ⟨s, hs, d, hd⟩ := hmax y
    have ht' : (t : E) ≠ 0 := by simpa using ht
    let cv : Fin r → E := fun i => c i
    let dv : Fin r → E := fun j => σ (d j)
    have hA : (fun j => (t : E) * ψ x j) = cv ᵥ* gram := funext fun j => by
      rw [hψ, ← hsmul, ← hc, hsumL]
      simp [Matrix.vecMul, dotProduct, cv, gram]
    have hB : (fun b => -(σ (s : E) * σ (ψ y b))) = gram *ᵥ dv := funext fun b => by
      rw [hψ, hherm (l b) y, map_neg, hσσ, mul_neg, neg_neg, ← hsmul', ← hd, hsumR]
      simp [Matrix.mulVec, dotProduct, dv, gram, mul_comm]
    have hC : (t : E) * σ s * h0 x y = cv ⬝ᵥ (gram *ᵥ dv) := by
      rw [mul_assoc, ← hsmul', ← hsmul, ← hc, ← hd, hsumL]
      simp only [hsumR, Matrix.mulVec, dotProduct, Finset.mul_sum, cv, dv, gram, Matrix.of_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have key : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (-ξ⁻¹ • gram⁻¹) (ψ x) (ψ y) = h0 x y := by
      apply mul_left_cancel₀ (mul_ne_zero ht' (hσ0 s hs))
      rw [hC, ← vecMul_one cv, ← Matrix.mul_nonsing_inv _ hu, ← vecMul_vecMul, ← dotProduct_mulVec,
        ← hA, ← hB]
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
      simp only [← hσ, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    have h1 := hh0 x y 1
    rw [one_smul] at h1
    rw [key, ← h1]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
noncomputable section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LevelExist

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_mem_adjoin (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    H.bar a ∈ Algebra.adjoin ℤ {H.w0} := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (Algebra.self_mem_adjoin_singleton ℤ _)
  | algebraMap r =>
    rw [eq_intCast, map_intCast]
    exact intCast_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem map_bar_span_bar (H : Host E) (al : 𝓞 E) :
    (Ideal.span {H.bar al}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {al} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  exact bar_bar H al

def levelOfSplit (H : Host E) (al : 𝓞 E) (M A : ℕ) (hal : al ∈ Algebra.adjoin ℤ {H.w0})
    (hM : al * H.bar al = (M : 𝓞 E)) (hc : IsCoprime al (H.bar al)) (h3 : 3 ≤ M) (ho : Odd M)
    (hA : 0 < A) : Level H where
  M := M
  three_le := h3
  odd := ho
  Mb := Ideal.span {H.bar al}
  fromK := by
    apply le_antisymm
    · apply Ideal.span_mono
      rintro a rfl
      exact ⟨Ideal.mem_span_singleton_self _, bar_mem_adjoin H hal⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [map_bar_span_bar, Ideal.span_singleton_mul_span_singleton, mul_comm, hM]
  coprime := by
    rw [map_bar_span_bar, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact hc.symm
  A := A
  A_pos := hA

theorem M'_pos {H : Host E} (l : Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

theorem zeta_eq_pow_of_dvd {a n : ℕ} (hn : 0 < n) (h : a ∣ n) : ∃ k : ℕ, zeta a = zeta n ^ k := by
  obtain ⟨k, rfl⟩ := h
  have ha : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  have hk : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  refine ⟨k, ?_⟩
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem isIntegral_zeta {n : ℕ} (hn : 0 < n) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top

theorem hostRootValue_eq_or_neg_embedding (H : Host E) (τ : E →+* ℂ) : H.rt0 = τ (H.rt : E) ∨ H.rt0 = -τ (H.rt : E) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [H.sqrt_neg_disc_sq, ← map_pow, coe_rt_sq]
  simp

def minCoeff {H : Host E} (l : Level H) : Coeff l :=
  have hconj : ∀ (τ : E →+* ℂ) (a : E), τ a ∈
      IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} := fun τ a =>
    (le_sup_left : IntermediateField.normalClosure ℚ E ℂ ≤ _)
      (AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩)
  have hz : zeta l.M' ∈
      IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} :=
    (le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  { F := IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'}
    fin := by
      have := IntermediateField.adjoin.finiteDimensional (isIntegral_zeta (M'_pos l))
      infer_instance
    conj := hconj
    zeta_mem := hz
    le := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        rcases hostRootValue_eq_or_neg_embedding H τ with h | h <;> rw [h]
        · exact hconj τ _
        · exact neg_mem (hconj τ _)
      · obtain ⟨k, hk⟩ := zeta_eq_pow_of_dvd (M'_pos l) (Nat.dvd_lcm_right l.M l.A)
        rw [hk]
        exact pow_mem hz k }

instance instNonemptyCoeff {H : Host E} (l : Level H) : Nonempty (Coeff l) := ⟨minCoeff l⟩

end GlobalTheory.LevelExist

namespace GlobalTheory

theorem level_of_split_and_level_coeff_exist :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (al : 𝓞 E) (M A : ℕ),
      al ∈ Algebra.adjoin ℤ {H.w0} → al * H.bar al = (M : 𝓞 E) → IsCoprime al (H.bar al) → 3 ≤ M →
      Odd M → 0 < A → ∃ l : Level H, l.M = M ∧ l.A = A ∧ l.Mb = Ideal.span {H.bar al}) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Nonempty (Level H)) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H),
      Nonempty (Coeff l) :=
  ⟨fun _ _ _ _ H al M A h1 h2 h3 h4 h5 h6 =>
      ⟨LevelExist.levelOfSplit H al M A h1 h2 h3 h4 h5 h6, rfl, rfl, rfl⟩,
    fun _ _ _ _ H => HostModel.instNonemptyLevel H,
    fun _ _ _ _ _ l => ⟨LevelExist.minCoeff l⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LevelHalf


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        ∃ e, gam a = a + l.M • e) → ∀ a, ∃ e, gam a = a + l.M • e := by
  intro E _ _ _ H D l gam hiso hhalf x
  cases D with
  | mk La _ _ EF _ hbij hbar _ _ _ _ => ?_
  obtain ⟨M, _, _, Mb, _, _, hsup, _, _⟩ := l
  dsimp only at *
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  set y := gam x - x with hy
  obtain ⟨e₁, he₁⟩ := hhalf (j • x) (Submodule.smul_mem_smul hj Submodule.mem_top)
  have hjy : j • y = M • e₁ := by
    rw [hy, smul_sub, ← LinearEquiv.map_smul, he₁]
    abel
  have hdiv : ∀ z, (M : ℤ) ∣ EF (i • y) z := by
    intro z
    rw [hbar]
    have hmem : H.bar i ∈ Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hi
    obtain ⟨e₂, he₂⟩ := hhalf (H.bar i • z) (Submodule.smul_mem_smul hmem Submodule.mem_top)
    refine ⟨-EF (gam x) e₂, ?_⟩
    rw [hy, map_sub, LinearMap.sub_apply, ← hiso x (H.bar i • z), he₂, map_add (f := _), map_nsmul,
      nsmul_eq_mul]
    ring
  let ψ : La →ₗ[ℤ] ℤ :=
    { toFun := fun z => EF (i • y) z / M
      map_add' := fun a b => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hdiv a)
      map_smul' := fun c a => by
        simp only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_id]
        exact Int.mul_ediv_assoc _ (hdiv a) }
  obtain ⟨w, hw⟩ := hbij.2 ψ
  have hiy : i • y = M • w := by
    apply hbij.1
    ext z
    rw [map_nsmul, LinearMap.smul_apply, hw]
    simp [ψ, nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv z)]
  refine ⟨e₁ + w, ?_⟩
  calc gam x = x + y := by rw [hy]; abel
    _ = x + M • (e₁ + w) := by
      rw [smul_add, ← hjy, ← hiy, add_comm (j • y), ← add_smul, hij, one_smul]

end GlobalTheory.LevelHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HermModel


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.HermModel.finrank_eq_of_injective_of_span {R K M V : Type} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module R V] [Module K V] [IsScalarTower R K V] (f : M →ₗ[R] V) (hf : Function.Injective f)
    (hspan : Submodule.span K (Set.range f) = ⊤) :
    Module.finrank R M = Module.finrank K V := by
  have hle : Module.rank R M ≤ Module.rank K V := by
    rw [Module.rank_def]
    refine ciSup_le' fun s => ?_
    have hs : LinearIndependent R (f ∘ ((↑) : s.1 → M)) :=
      s.2.map' f (LinearMap.ker_eq_bot.mpr hf)
    exact ((LinearIndependent.iff_fractionRing R K).mp hs).cardinal_le_rank
  have hge : Module.rank K V ≤ Module.rank R M := by
    obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
    have hrank : Module.rank K V = Cardinal.mk s := by
      rw [← rank_top, ← hspan, ← hs_span, rank_span_set hs_li]
    have hpre : ∀ x : s, ∃ m, f m = x.1 := fun x => hs_sub x.2
    choose g hg using hpre
    have hli : LinearIndependent R (f ∘ g) := by
      have : f ∘ g = ((↑) : s → V) := funext hg
      rw [this]
      exact (LinearIndependent.iff_fractionRing R K).mpr hs_li
    rw [hrank]
    exact (LinearIndependent.of_comp f hli).cardinal_le_rank
  unfold Module.finrank
  rw [le_antisymm hle hge]

section Trace

variable {E : Type} [Field E] [NumberField E]


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.HermModel.eq_zero_of_trace_mul_integer {t : E}
    (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E (t * a) = 0) : t = 0 := by
  classical
  have h0 : Algebra.traceForm ℚ E t = 0 := (NumberField.integralBasis E).ext fun i => by
    rw [NumberField.integralBasis_apply, Algebra.traceForm_apply, LinearMap.zero_apply]
    exact ht _
  exact (traceForm_nondegenerate ℚ E).1 t fun y => by rw [h0]; rfl

end Trace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (x - x') y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y - _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x' y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x (y + y') = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y + _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y' := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x (c • y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc c := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_zero_right (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x 0 = 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.eq_zero_of_herm_eq_zero {G : Matrix (Fin r) (Fin r) E}
    (hG : G.det ≠ 0) {w : Fin r → E} (hw : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G w u = 0) : w = 0 := by
  refine Matrix.eq_zero_of_vecMul_eq_zero hG (funext fun b => ?_)
  have h := hw (Pi.single b 1)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa [Matrix.vecMul, dotProduct] using h

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.rank_integral_selfDual (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (_hξ : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) :
    r = D.p + D.q ∧ (LinearMap.range φ).FG ∧
      (∀ x y, IsIntegral ℤ ((NumberField.discr E : E) * (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y)))) ∧
      ∀ v : Fin r → E, (∀ y, ∃ n : ℤ, Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm v (φ y)) = n) ↔
        v ∈ LinearMap.range φ := by
  classical
  obtain ⟨hinj, hspan, -, hdet, hEF⟩ := h
  have hsmul : ∀ (c : 𝓞 E) (x : D.La), φ (c • x) = (c : E) • φ x := fun c x => by
    rw [map_smul]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr := _root_.GlobalTheory.HermModel.finrank_eq_of_injective_of_span (R := 𝓞 E) (K := E) φ hinj hspan
    rw [Module.finrank_fin_fun] at hr
    rw [← hr, D.rank]
  · haveI := D.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  · intro x y
    have hmem : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp ha
      refine ⟨D.EF (c • x) y, ?_⟩
      rw [eq_intCast, hEF, hsmul, _root_.GlobalTheory.HermModel.herm_smul_left, Algebra.traceForm_apply]
      change _ = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y) * (c : E))
      congr 1
      ring
    have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
      rw [NumberField.integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) 1 hb
      (Submodule.one_le.mp le_rfl) hmem
    rw [← NumberField.coe_discr] at hint
    convert hint using 1
    rw [Algebra.smul_def, mul_one]
    simp
  · intro v
    constructor
    · intro hv
      by_cases hξ0 : ξ = 0
      · have hsub : ∀ x : D.La, x = 0 := fun x => D.unimod.1 <| by
          refine LinearMap.ext fun y => ?_
          have := hEF x y
          rw [hξ0, zero_mul, map_zero] at this
          simp [map_zero, Int.cast_eq_zero.mp this]
        have hbot : Submodule.span E (Set.range φ) ≤ ⊥ := by
          rw [Submodule.span_le]
          rintro _ ⟨x, rfl⟩
          rw [hsub x, map_zero]
          exact Submodule.zero_mem _
        have hv0 : v = 0 := by
          have : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
          simpa using hbot this
        rw [hv0]
        exact Submodule.zero_mem _
      · choose n hn using hv
        let ℓ : D.La →+ ℤ := AddMonoidHom.mk' n fun y y' => by
          apply Int.cast_injective (α := ℚ)
          rw [Int.cast_add, ← hn, ← hn, ← hn, map_add (f := _), _root_.GlobalTheory.HermModel.herm_add_right, mul_add,
            map_add]
        obtain ⟨x, hx⟩ := D.unimod.2 ℓ.toIntLinearMap
        have htr : ∀ y, Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y)) = 0 := by
          intro y
          have h1 : (D.EF x y : ℚ) = n y := by
            rw [hx]
            rfl
          rw [_root_.GlobalTheory.HermModel.herm_sub_left, mul_sub, map_sub, hn, ← hEF, h1, sub_self]
        have hzero : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y) = 0 := by
          intro y
          have : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y) = 0 := by
            refine _root_.GlobalTheory.HermModel.eq_zero_of_trace_mul_integer fun a => ?_
            have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((H.bar.symm a : 𝓞 E) : E) = (a : E) := by
              unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
              rw [← H.bar_eq, RingEquiv.apply_symm_apply]
            have := htr (H.bar.symm a • y)
            rw [hsmul, _root_.GlobalTheory.HermModel.herm_smul_right, hc, ← mul_assoc] at this
            exact this
          exact (mul_eq_zero.mp this).resolve_left hξ0
        have hall : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) u = 0 := by
          intro u
          have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
          induction hu using Submodule.span_induction with
          | mem w hw =>
            obtain ⟨y, rfl⟩ := hw
            exact hzero y
          | zero => exact _root_.GlobalTheory.HermModel.herm_zero_right _ _
          | add w w' _ _ hw hw' => rw [_root_.GlobalTheory.HermModel.herm_add_right, hw, hw', add_zero]
          | smul c w _ hw => rw [_root_.GlobalTheory.HermModel.herm_smul_right, hw, zero_mul]
        have hw := _root_.GlobalTheory.HermModel.eq_zero_of_herm_eq_zero hdet hall
        exact ⟨x, (sub_eq_zero.mp hw).symm⟩
    · rintro ⟨x, rfl⟩ y
      exact ⟨D.EF x y, (hEF x y).symm⟩

end GlobalTheory.HermModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CongruenceDet


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.CongruenceDet.isIntegral_root {R E K : Type} [CommRing R] [Field E]
    [Field K] [CharZero K]
    [Algebra R E] [Algebra R K] [Algebra E K] [IsScalarTower R E K] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) (μ : K)
    (hμ : (g.map (algebraMap E K)).charpoly.IsRoot μ) :
    IsIntegral R ((μ - 1) / M) := by
  classical
  have hdet : (scalar (Fin r) μ - g.map (algebraMap E K)).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hμ
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hug : u ᵥ* g.map (algebraMap E K) = μ • u := by
    rw [Matrix.vecMul_sub, sub_eq_zero] at hu
    rw [← hu]
    ext i
    simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
  let ℓE : (Fin r → E) →ₗ[E] K :=
    ∑ i, u i • ((Algebra.linearMap E K).comp (LinearMap.proj i))
  have hℓE : ∀ v, ℓE v = u ⬝ᵥ (algebraMap E K ∘ v) := by
    intro v
    simp [ℓE, dotProduct]
  let ℓ : (Fin r → E) →ₗ[R] K := ℓE.restrictScalars R
  have hℓ : ∀ v, ℓ v = u ⬝ᵥ (algebraMap E K ∘ v) := hℓE
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM
  have hstep : ∀ v ∈ Λ, ∃ w ∈ Λ, ((μ - 1) / M) * ℓ v = ℓ w := by
    intro v hv
    obtain ⟨w, hw, hgv⟩ := hg v hv
    refine ⟨w, hw, ?_⟩
    have hmap : algebraMap E K ∘ (g *ᵥ v) = g.map (algebraMap E K) *ᵥ (algebraMap E K ∘ v) := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    have h1 : ℓ (g *ᵥ v) = μ * ℓ v := by
      rw [hℓ, hℓ, hmap, Matrix.dotProduct_mulVec, hug, smul_dotProduct, smul_eq_mul]
    have h2 : ℓ (g *ᵥ v) = ℓ v + M * ℓ w := by
      rw [hgv, map_add (f := _), map_nsmul, nsmul_eq_mul]
    field_simp
    linear_combination h1.symm.trans h2
  let N : Submodule R K := Λ.map ℓ
  have hN : N ≠ ⊥ := by
    intro hbot
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker ℓE := by
      rw [Submodule.span_le]
      intro v hv
      have : ℓ v ∈ N := Submodule.mem_map_of_mem hv
      rw [hbot, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    apply hu0
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker, hℓE] at this
    simpa [dotProduct, Pi.single_apply] using this
  refine isIntegral_of_smul_mem_submodule N hN (hfg.map ℓ) _ ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hvw⟩ := hstep v hv
  rw [smul_eq_mul, hvw]
  exact Submodule.mem_map_of_mem hw


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.CongruenceDet.isIntegral_det_sub_one {R E : Type} [CommRing R] [Field E]
    [CharZero E]
    [Algebra R E] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) :
    IsIntegral R ((g.det - 1) / M) := by
  classical
  let K := AlgebraicClosure E

  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral R ((μ - 1) / M) :=
    fun μ hμ => _root_.GlobalTheory.CongruenceDet.isIntegral_root hM Λ g hfg hspan hg μ
      (Polynomial.isRoot_of_mem_roots hμ)
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM
  have hMint : IsIntegral R (M : K) := by
    simpa using isIntegral_algebraMap (R := R) (A := K) (x := (M : R))
  have hprod : ∀ s : Multiset K, (∀ μ ∈ s, IsIntegral R ((μ - 1) / M)) →
      IsIntegral R ((s.prod - 1) / M) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simpa using isIntegral_zero
    | cons a s ih =>
      intro hs
      have ha := hs a (Multiset.mem_cons_self a s)
      have hb := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
      have key : ((a ::ₘ s).prod - 1) / M =
          (a - 1) / M * (M * ((s.prod - 1) / M) + 1) + (s.prod - 1) / M := by
        rw [Multiset.prod_cons, mul_div_cancel₀ _ hMK]
        ring
      rw [key]
      exact (ha.mul ((hMint.mul hb).add isIntegral_one)).add hb
  have h1 : algebraMap E K g.det = (g.map (algebraMap E K)).det := by
    rw [RingHom.map_det]
    rfl
  have hK := hprod _ hroots
  rw [← Matrix.det_eq_prod_roots_charpoly, ← h1] at hK
  have hK' : IsIntegral R (IsScalarTower.toAlgHom R E K ((g.det - 1) / M)) := by
    simpa [map_div₀, map_sub, map_one, map_natCast] using hK
  exact (isIntegral_algHom_iff _ (algebraMap E K).injective).1 hK'


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.CongruenceDet.det_mul_conj {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (G g : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (g *ᵥ x) (g *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    g.det * IsCMField.complexConj E g.det = 1 := by
  classical
  let c : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hherm : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ (c ∘ y)) := by
    intro x y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, c]
  have hmat : gᵀ * G * g.map c = G := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    have hcs : c ∘ (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j <;> simp [Pi.single_apply, hk]
    have hgs : c ∘ (g *ᵥ Pi.single j 1) = g.map c *ᵥ (c ∘ Pi.single j 1) := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    rw [hherm, hherm, hgs, hcs, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [Matrix.mul_assoc] using this
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at hdet
  have e : c g.det = IsCMField.complexConj E g.det := rfl
  apply mul_right_cancel₀ hG
  rw [← e]
  linear_combination hdet


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.CongruenceDet.det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), Gm.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M Gm Λ γ hG hfg hspan hM hU hγ
  have hM0 : M ≠ 0 := by omega
  have hUisom : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm x y := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at hU
    exact hU.1
  set d := (γ : Matrix (Fin r) (Fin r) E).det with hd
  have hint : IsIntegral ℤ ((d - 1) / M) :=
    isIntegral_trans _ (_root_.GlobalTheory.CongruenceDet.isIntegral_det_sub_one hM0 Λ _ hfg hspan hγ)
  have hconj : d * IsCMField.complexConj E d = 1 :=
    _root_.GlobalTheory.CongruenceDet.det_mul_conj Gm _ hG hUisom
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have habs : ∀ φ : E →+* ℂ, ‖φ ((d - 1) / M)‖ ≤ 2 / 3 := by
    intro φ
    have h1 : ‖φ d‖ = 1 := by
      have := congrArg φ hconj
      rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj, map_one] at this
      have h2 : Complex.normSq (φ d) = 1 := by exact_mod_cast this
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (φ d)]
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast]
    have h3 : ‖φ d - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [h1, norm_one]; norm_num)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  by_contra hne
  have hx : (d - 1) / M ≠ 0 := by
    intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hne (sub_eq_zero.1 h0)
    · exact hM0 (by exact_mod_cast h0)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ hint)
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hx
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hn
    exact hn
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ ((d - 1) / M)
  rw [← hn] at hprod
  have hle : ‖∏ σ : E →ₐ[ℚ] ℂ, σ ((d - 1) / M)‖ ≤ (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [norm_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun σ _ => habs σ.toRingHom)
  have hcard : 0 < Fintype.card (E →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.2 ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ)⟩
  have hlt : (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hcard.ne'
  rw [← hprod] at hle
  have hge : (1 : ℝ) ≤ ‖(algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n)‖ := by
    have hcast : (algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n) = (n : ℂ) := by simp
    rw [hcast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hn0
  linarith

end GlobalTheory.CongruenceDet
end
