module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FinrankHomComplex
noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex

def sesq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (hermForm Hm)
    (fun _ _ _ => by simp [hermForm]) (fun _ _ _ => by simp [hermForm])
    (fun _ _ _ => by simp [hermForm, Matrix.mulVec_add]) (fun _ _ _ => by simp [hermForm, Matrix.mulVec_smul])

theorem sesq_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq Hm z w = hermForm Hm z w := rfl

theorem sesq_conj {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    starRingEnd ℂ (sesq Hm z w) = sesq Hm w z := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sesq_apply, hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem sesq_of {n : ℕ} (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ) (z w : Fin n → ℂ) :
    hermForm (Matrix.of fun i j => S (Pi.single i 1) (Pi.single j 1)) z w = S z w := by
  conv_rhs => rw [pi_eq_sum_univ' z, pi_eq_sum_univ' w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

def imForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).im) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)

def reForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).re) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)

@[simp] theorem reForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : reForm S x y = (S x y).re := rfl

theorem sesq_ext {ι : Type} {v : ι → W} (hv : Submodule.span ℝ (Set.range v) = ⊤) {S S' : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ}
    (h : ∀ i k, (S (v i) (v k)).im = (S' (v i) (v k)).im) (x y : W) : S x y = S' x y := by
  have h1 : imForm S = imForm S' := LinearMap.ext_on_range hv fun i => LinearMap.ext_on_range hv fun k => h i k
  have h2 : ∀ x y, (S x y).im = (S' x y).im := fun x y => congr($h1 x y)
  exact Complex.ext (by simpa using h2 (I • x) y) (h2 x y)

variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}

theorem exists_imPart [FiniteDimensional ℝ W] (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) :
    ∃ b : W →ₗ[ℝ] W, (∀ w, b w ∈ R) ∧ ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im := by
  have hnd : ((reForm S).restrict R).Nondegenerate := by
    constructor
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
  refine ⟨R.subtype ∘ₗ (LinearMap.BilinForm.toDual _ hnd).symm.toLinearMap ∘ₗ (imForm S).domRestrict₂ R,
    fun w => Subtype.property _, fun w r hr => Complex.ext ?_ ?_⟩
  · exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) ((imForm S).domRestrict₂ R w) ⟨r, hr⟩
  · exact hR _ (Subtype.property _) r hr

section

variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)


omit [IsScalarTower ℝ ℂ W] in
include hpos hb hb' in
theorem imPart_eq {w c : W} (hc : c ∈ R) (h : ∀ r ∈ R, (S c r).re = (S w r).im) : b w = c := by
  by_contra hne
  have h1 := hpos _ (sub_ne_zero.2 hne)
  have h2 := R.sub_mem (hb w) hc
  rw [map_sub S, LinearMap.sub_apply, hb' w _ h2, Complex.sub_re, h _ h2] at h1
  simp at h1


omit [IsScalarTower ℝ ℂ W] in
include hconj hb' in
theorem apply_imPart (w : W) {r : W} (hr : r ∈ R) : S r (b w) = (S w r).im := by
  rw [← hconj, hb' w r hr, Complex.conj_ofReal]

variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)


omit [IsScalarTower ℝ ℂ W] in
include hpos hb hb' hρ hρR in
theorem imPart_act (a : O) (w : W) : b (ρ a w) = ρ a (b w) :=
  imPart_eq hpos hb hb' (hρR _ _ (hb w)) fun r hr => by
    rw [hρ, hρ, hb' _ _ (hρR _ _ hr), Complex.ofReal_re]


include hpos hb hb' hρ hρR in
theorem exists_compl [FiniteDimensional ℂ W] (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (n : ℕ) (q : W →ₗ[ℂ] (Fin n → ℂ)) (j : (Fin n → ℂ) →ₗ[ℂ] W) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧
      (∀ z, q (j z) = z) ∧ (∀ z, ∀ r ∈ R, S (j z) r = 0) ∧ (∀ w, w = b (I • w) + I • b w + j (q w)) ∧
      (∀ w, (∀ r ∈ R, S w r = 0) → j (q w) = w) ∧ ∀ a z, j (F a z) = ρ a (j z) := by
  let U : Submodule ℂ W :=
    { carrier := {u | ∀ r ∈ R, S u r = 0}
      zero_mem' := fun r _ => by simp
      add_mem' := fun {u u'} hu hu' r hr => by simp [hu r hr, hu' r hr]
      smul_mem' := fun c u hu r hr => by simp [hu r hr] }
  have hII : ∀ w : W, I • I • w = -w := fun w => by rw [smul_smul, I_mul_I, neg_smul, one_smul]
  have hsm : ∀ (c : ℂ) (w : W), c • w = c.re • w + c.im • I • w := fun c w => by
    rw [← algebraMap_smul ℂ c.re, ← algebraMap_smul ℂ c.im, smul_smul, ← add_smul]
    congr 1
    exact (re_add_im c).symm
  let p₀ : W →ₗ[ℝ] W := LinearMap.id - b ∘ₗ (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ -
    (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ ∘ₗ b
  have hp₀ : ∀ w, p₀ w = w - b (I • w) - I • b w := fun _ => rfl
  have hpI : ∀ w, p₀ (I • w) = I • p₀ w := fun w => by
    simp only [hp₀, hII, smul_sub, map_neg]; abel
  have hpU : ∀ w, p₀ w ∈ U := fun w r hr => by
    simp only [hp₀, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hb' _ r hr, smul_eq_mul]
    apply Complex.ext <;> simp
  let p : W →ₗ[ℂ] U :=
    { toFun := fun w => ⟨p₀ w, hpU w⟩
      map_add' := fun w w' => Subtype.ext (map_add p₀ w w')
      map_smul' := fun c w => Subtype.ext (by
        show p₀ (c • w) = c • p₀ w
        rw [hsm c w, hsm c (p₀ w), map_add (f := _), map_smul, map_smul, hpI]) }
  have hb0 : ∀ u ∈ U, b u = 0 := fun u hu => imPart_eq hpos hb hb' R.zero_mem fun r hr => by simp [hu r hr]
  have hpu : ∀ u : U, p u = u := fun u => Subtype.ext (by
    show p₀ u = u
    rw [hp₀, hb0 _ u.2, hb0 _ (U.smul_mem _ u.2), smul_zero, sub_zero, sub_zero])
  have hρU : ∀ a, ∀ u ∈ U, ρ a u ∈ U := fun a u hu r hr => by rw [hρ]; exact hu _ (hρR _ _ hr)
  let σ : O →+* Module.End ℂ U :=
    { toFun := fun a => (ρ a).restrict (hρU a)
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  obtain ⟨n, k, F, hF, hk⟩ := hQ U σ
  refine ⟨n, k.toLinearMap ∘ₗ p, U.subtype ∘ₗ k.symm.toLinearMap, F, hF, fun z => ?_, fun z => (k.symm z).2,
    fun w => ?_, fun w hw => ?_, fun a z => ?_⟩
  · simp [hpu]
  · have : (U.subtype ∘ₗ k.symm.toLinearMap) ((k.toLinearMap ∘ₗ p) w) = p₀ w := by simp [p]
    rw [this, hp₀]; abel
  · have := hpu ⟨w, hw⟩
    simp only at this
    simp [this]
  · obtain ⟨u, rfl⟩ := k.surjective z
    rw [← hk]
    simp [σ]


omit [IsScalarTower ℝ ℂ W] in
include hconj hR hb in
theorem sub_swap {w w' u u' : W} (hu : ∀ r ∈ R, S u r = 0) (hu' : ∀ r ∈ R, S u' r = 0)
    (h : w = b (I • w) + I • b w + u) (h' : w' = b (I • w') + I • b w' + u') :
    S w (b w') - S u u' / (2 * I) = S w' (b w) - S u' u / (2 * I) - (S w w').im := by
  have hv : ∀ r ∈ R, S r u' = 0 := fun r hr => by rw [← hconj, hu' r hr, map_zero]
  have hre : ∀ z z', (S z z').re = (S z' z).re := fun z z' => by rw [← hconj z z', conj_re]
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  generalize b (I • w) = a, hb (I • w) = ha at h
  generalize b (I • w') = a', hb (I • w') = ha' at h'
  generalize b w = c, hb w = hc at h ⊢
  generalize b w' = c', hb w' = hc' at h' ⊢
  subst h h'
  simp only [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu _ ha', hu _ hc',
    hu' _ hc, hv _ ha, hv _ hc, AnArc.div_two_I]
  apply Complex.ext <;>
    simp [hR _ ha _ ha', hR _ ha _ hc', hR _ hc _ ha', hR _ hc _ hc', hR _ ha' _ hc, hR _ hc' _ hc, hre a' c, hre c' c,
      hre u' u, him u' u]
  ring

end


open NumberField in
theorem exists_diag {E : Type} [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : 𝓞 E →+* Module.End ℂ U) :
    ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : 𝓞 E →+* Module.End ℂ (Fin n → ℂ)),
      (∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) ∧ ∀ a u, k (σ a u) = F a (k u) := by
  classical
  let T₀ : Set U := {v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, σ a v = φ (a : E) • v}
  have hS : Submodule.span ℂ T₀ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) σ v]
    refine Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩
    exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) σ φ v)
  obtain ⟨T, hT, hspan, hli⟩ := exists_linearIndependent ℂ T₀
  let b : Module.Basis T ℂ U := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have : Finite T := Module.Finite.finite_basis b
  have : Fintype T := Fintype.ofFinite T
  choose s hs using fun v : T => hT v.2
  have hb : ∀ a v, σ a (b v) = s v (a : E) • b v := fun a v => by
    simp only [b, Module.Basis.mk_apply]; exact hs v a
  let e := Fintype.equivFin T
  obtain ⟨k, hk⟩ := PeriodNonempty.exists_diag σ (fun i => s (e.symm i)) fun a => by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, e.symm.sum_comp fun v => s v (a : E)]
    simp [Matrix.trace, LinearMap.toMatrix_apply, hb]
  refine ⟨_, k, k.conjRingEquiv.toRingHom.comp σ, ⟨fun i => s (e.symm i), fun a z i => ?_⟩, fun a u => ?_⟩
  · obtain ⟨u, rfl⟩ := k.surjective z
    simpa using hk a u i
  · simp

section Hom

variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

theorem finrank_hom_complex : Module.finrank ℂ (Y →+ ℂ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).finrank_eq, Module.finrank_linearMap, Module.finrank_self, mul_one]

theorem finrank_hom_int : Module.finrank ℤ (Y →+ ℤ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).finrank_eq]
  simp [Module.finrank_linearMap]

theorem span_intHom :
    Submodule.span ℂ (Set.range fun n : Y →+ ℤ => (Int.castAddHom ℂ).comp n) = ⊤ := by
  refine eq_top_iff.2 fun l _ => ?_
  let b := Module.Free.chooseBasis ℤ Y
  have : l = ∑ i, l (b i) • (Int.castAddHom ℂ).comp (b.coord i).toAddMonoidHom := by
    ext x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Hom

theorem zsmul_mem_Lam {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℤ) (z : Fin A.gB → ℂ)
    (h : ∀ l : A.abelian₂, ∃ n : ℤ, k * (A.H l z).im = n) : k • z ∈ A.abelian₂ := by
  choose n hn using h
  let φ : A.abelian₂ →+ ℤ := AddMonoidHom.mk' (fun l => -n l) fun l l' => by
    have : ((n (l + l') : ℤ) : ℝ) = n l + n l' := by
      rw [← hn, ← hn, ← hn, Submodule.coe_add, A.H_add_left, add_im, mul_add]
    have : n (l + l') = n l + n l' := by exact_mod_cast this
    simp only [this]; ring
  obtain ⟨l₀, hl₀⟩ := A.Ef_bij.2 φ.toIntLinearMap
  have h1 : ∀ l : A.abelian₂, imForm (sesq A.Hm) (l₀ - k • z) l = 0 := fun l => by
    have h2 : (A.Ef l₀ l : ℝ) = -n l := by rw [hl₀]; simp [φ]
    rw [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    change (A.H l₀ l).im - k • (A.H z l).im = 0
    rw [← A.Ef_eq_im, h2, ← hn, A.H_im_symm z l]
    simp
  have h3 : imForm (sesq A.Hm) (l₀ - k • z) = 0 := LinearMap.ext_on A.full fun l hl => h1 ⟨l, hl⟩
  have h4 : (l₀ : Fin A.gB → ℂ) - k • z = 0 := by
    by_contra hne
    have h5 := A.H_pos hne
    have h6 : (A.H (l₀ - k • z) (I • (l₀ - k • z))).im = 0 := congr($h3 (I • (l₀ - k • z)))
    rw [A.H_smul_right] at h6
    generalize A.H (l₀ - k • z) (l₀ - k • z) = c at h5 h6
    simp at h6
    linarith
  rw [← sub_eq_zero.1 h4]
  exact l₀.2

end GlobalTheory.OfPeriod
end
end

noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, mul_comm]; simp

variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {O : Type} [CommRing O] [StarRing O]
  {Y M : Type} [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
  [AddCommGroup M] [Module O M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem exists_arc {w : O} (hw : w + star w = 1) (EM : LinearMap.BilinForm ℤ M) (hEM : Function.Bijective EM)
    (P : Y × (Y →+ ℤ) × M →+ W) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (hrk : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ W)
    (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hS : ∀ v v', (S (P v) (P v')).im = (v'.2.1 v.1 - v.2.1 v'.1 + EM v.2.2 v'.2.2 : ℤ))
    (ρ : O →+* Module.End ℂ W) (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w))
    (hP : ∀ (a : O) v, P (a • v.1, v.2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • v.2.2) = ρ a (P v))
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x y, be x y = be y x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)) (be_even : ∀ x, (2 : ℤ) ∣ be x x)
    (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (A : AnArc O) (e : A.X ≃ₗ[O] Y) (f : M ≃+ A.abelian₂) (h : W ≃ₗ[ℂ] A.V),
      (∀ x y, A.be x y = be (e x) (e y)) ∧ (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam w l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (w • x))) ∧ Q A.gB A.F ∧ (∀ (a : O) m, f (a • m) = A.FLam a (f m)) ∧
      (∀ m m', A.Ef (f m) (f m') = EM m m') ∧ (∀ a z, h (ρ a z) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (AnArc.La.mk (e.symm v.1) (v.2.1.comp e.toAddEquiv.toAddMonoidHom) (f v.2.2))) ∧
      (A.BwMat 0).PosDef := by
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  let R : Submodule ℝ W := Submodule.span ℝ (Set.range fun n => P (0, n, 0))
  have hmem : ∀ n, P (0, n, 0) ∈ R := fun n => Submodule.subset_span ⟨n, rfl⟩
  have hRind : ∀ z, (∀ n, (S z (P (0, n, 0))).im = 0) → ∀ r ∈ R, (S z r).im = 0 := fun z hz r hr =>
    LinearMap.eqOn_span (f := imForm S z) (g := 0) (by rintro _ ⟨n, rfl⟩; exact hz n) hr
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0 := fun r hr => hRind r fun n => by
    rw [him, hRind _ (fun n' => by simp [hS]) r hr, neg_zero]
  have hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R := fun a r hr => by
    refine Submodule.span_le (p := R.comap ((ρ a).restrictScalars ℝ)).2 ?_ hr
    rintro _ ⟨n, rfl⟩
    show ρ a (P (0, n, 0)) ∈ R
    rw [← hP]
    simpa using hmem _
  obtain ⟨b, hb, hb'⟩ := exists_imPart hpos hR
  obtain ⟨n, q, j, F, hF, hqj, hj, hdec, hjq, hjF⟩ := exists_compl hpos hb hb' hρ hρR Q hQ
  have hjinj : Function.Injective j := Function.LeftInverse.injective hqj
  have hj' : ∀ z, ∀ r ∈ R, S r (j z) = 0 := fun z r hr => by rw [← hconj, hj z r hr, map_zero]
  have hbR : ∀ r ∈ R, b r = 0 := fun r hr =>
    imPart_eq hpos hb hb' R.zero_mem fun r' hr' => by simp [hR r hr r' hr']
  have hbI : ∀ r ∈ R, b (I • r) = r := fun r hr => imPart_eq hpos hb hb' hr fun r' hr' => by simp
  have hqR : ∀ r ∈ R, q r = 0 := fun r hr => hjinj (by simpa [hbR r hr, hbI r hr] using hdec r)
  have hqρ : ∀ a z, q (ρ a z) = F a (q z) := fun a z => by
    conv_lhs => rw [hdec z]
    simp only [map_add (f := _), map_smul, hqR _ (hρR _ _ (hb _)), ← hjF, hqj, smul_zero, zero_add]
  have hSq : ∀ z z', S z (j z') = S (j (q z)) (j z') := fun z z' => by
    conv_lhs => rw [hdec z]
    simp [hj' _ _ (hb _)]
  have hbm : ∀ v : Y × (Y →+ ℤ) × M, v.1 = 0 → b (P v) = 0 := fun v hv =>
    imPart_eq hpos hb hb' R.zero_mem fun r hr => by
      rw [hRind _ (fun n => by simp [hS, hv]) r hr]; simp

  let Φ : W → W → ℂ := fun z z' => S z (b z') - S (j (q z)) (j (q z')) / (2 * I)
  have hΦ : ∀ z z', Φ z z' = Φ z' z - (S z z').im := fun z z' =>
    sub_swap hconj hR hb (hj _) (hj _) (hdec z) (hdec z')
  have hΦρ : ∀ a z z', Φ (ρ a z) z' = Φ z (ρ (star a) z') := fun a z z' => by
    simp only [Φ, hqρ, hjF, hρ, imPart_act hpos hb hb' hρ hρR]
  let s : Y →+ W := P.comp (AddMonoidHom.inl _ _)
  have hs : ∀ y, s y = P (y, 0, 0) := fun _ => rfl
  have hsρ : ∀ (a : O) y, s (a • y) = ρ a (s y) := fun a y => by rw [hs, hs, ← hP]; simp
  let φ : W →ₗ[ℂ] (Y →+ ℂ) :=
    { toFun := fun z => AddMonoidHom.mk' (fun x => Φ z (s x)) fun x x' => by simp only [Φ, map_add (f := _)]; ring
      map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [Φ]; ring
      map_smul' := fun c z => AddMonoidHom.ext fun x => by simp [Φ]; ring }
  have hφ : ∀ z x, φ z x = Φ z (s x) := fun _ _ => rfl
  have hPv : ∀ v : Y × (Y →+ ℤ) × M, P v = s v.1 + P (0, v.2.1, 0) + P (0, 0, v.2.2) := fun v => by
    rw [hs, ← map_add (f := _), ← map_add (f := _)]; simp
  have hφP : ∀ v x, φ (P v) x = φ (s v.1) x + v.2.1 x - S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I) :=
    fun v x => by
      have h1 : φ (P (0, v.2.1, 0)) x = v.2.1 x := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm, hqR _ (hmem _)]
      have h2 : φ (P (0, 0, v.2.2)) x = -(S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I)) := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm]
      rw [hPv v, map_add (f := _), map_add (f := _), AddMonoidHom.add_apply, AddMonoidHom.add_apply, h1, h2]; ring
  have hr0 : ∀ r ∈ R, (∀ x, (S (s x) r).im = 0) → r = 0 := fun r hr h0 => by
    have h1 : (imForm S).flip r = 0 := LinearMap.ext_on_range hspan fun v => by
      show (S (P v) r).im = 0
      have h2 := congrArg Complex.re (hb' (P (0, 0, v.2.2)) r hr)
      rw [hbm _ rfl] at h2
      rw [hPv]
      simp only [map_add (f := _), LinearMap.add_apply, add_im, h0, hR _ (hmem _) r hr, zero_add]
      simpa using h2.symm
    by_contra hne
    have h3 : (S (I • r) r).im = 0 := congr($h1 (I • r))
    exact (hpos r hne).ne' (by simpa using h3)
  have hbij : Function.Bijective (φ.prod q) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      have h1 : q z = 0 := congrArg Prod.snd hz
      have h2 : ∀ x, S z (b (s x)) = 0 := fun x => by
        have : φ z x = 0 := congr(($hz).1 x)
        simpa [hφ, Φ, h1] using this
      have h3 : ∀ x, (S (s x) (b (I • z))).im = 0 ∧ (S (s x) (b z)).im = 0 := fun x => by
        have := h2 x
        rw [hdec z, h1] at this
        simp only [map_add (f := _), map_smul, map_zero, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
          apply_imPart hconj hb' _ (hb _), smul_eq_mul] at this
        simpa [Complex.ext_iff] using this
      rw [hdec z, h1, hr0 _ (hb _) fun x => (h3 x).1, hr0 _ (hb _) fun x => (h3 x).2]
      simp
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨l, z⟩ -
      have h1 : ∀ l : Y →+ ℂ, (l, (0 : Fin n → ℂ)) ∈ LinearMap.range (φ.prod q) := fun l => by
        have : l ∈ (LinearMap.range (φ.prod q)).comap (LinearMap.inl ℂ _ _) := by
          refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := l)))
          rintro _ ⟨k, rfl⟩
          refine ⟨P (0, k, 0), Prod.ext (AddMonoidHom.ext fun x => ?_) (hqR _ (hmem k))⟩
          show φ _ x = _
          rw [hφP]
          simp [← Prod.zero_eq_mk]
        exact this
      have h2 : (l, z) = (l - φ (j z), 0) + φ.prod q (j z) := by simp [hqj]
      rw [h2]
      exact Submodule.add_mem _ (h1 _) ⟨_, rfl⟩
  let h : W ≃ₗ[ℂ] (Y →+ ℂ) × (Fin n → ℂ) := LinearEquiv.ofBijective _ hbij
  have hrk' : Module.finrank ℤ M = Module.finrank ℝ (Fin n → ℂ) := by
    have : Module.Finite ℂ (Y →+ ℂ) := Module.Finite.equiv (addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).symm
    have h1 := h.finrank_eq
    rw [Module.finrank_prod, finrank_hom_complex, Module.finrank_fin_fun] at h1
    rw [finrank_real_of_complex, Module.finrank_fin_fun]
    omega
  let SB : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ := (S ∘ₗ j).compl₂ j
  have hSB : ∀ z z', SB z z' = S (j z) (j z') := fun _ _ => rfl
  let Hm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => SB (Pi.single i 1) (Pi.single k 1)
  have hHm : ∀ z z', hermForm Hm z z' = S (j z) (j z') := sesq_of SB
  let p : M →+ (Fin n → ℂ) :=
    q.toAddMonoidHom.comp (P.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)))
  have hp : ∀ m, p m = q (P (0, 0, m)) := fun _ => rfl
  have hpE : ∀ m m', (S (j (p m)) (j (p m'))).im = EM m m' := fun m m' => by
    have h1 := hΦ (P (0, 0, m)) (P (0, 0, m'))
    simp only [Φ, hbm (0, 0, _) rfl, map_zero, hS, ← hp, AnArc.div_two_I] at h1
    have h2 := congrArg Complex.re h1
    simp [him (j (p m')) (j (p m))] at h2
    linarith
  have hpF : ∀ (a : O) m, p (a • m) = F a (p m) := fun a m => by
    rw [hp, hp, ← hqρ, ← hP]; simp
  obtain ⟨hpi, hpd, hps⟩ := PolarisedLattice.lattice_of_im EM hEM.1 p (fun z => SB.flip z) hpE hrk'
  let f : M ≃ₗ[ℤ] LinearMap.range p.toIntLinearMap := LinearEquiv.ofInjective p.toIntLinearMap hpi
  have hf : ∀ m, (f m : Fin n → ℂ) = p m := fun _ => rfl
  let Ef := LinearMap.BilinForm.congr f EM
  have hEf : ∀ m m', Ef (f m) (f m') = EM m m' := fun m m' => by
    rw [LinearMap.BilinForm.congr_apply, f.symm_apply_apply, f.symm_apply_apply]
  have hEadj : ∀ (a : O) m m', EM (a • m) m' = EM m (star a • m') := fun a m m' => by
    have : (EM (a • m) m' : ℝ) = EM m (star a • m') := by rw [← hpE, ← hpE, hpF, hpF, hjF, hjF, hρ]
    exact_mod_cast this
  have hEalt : ∀ m m', EM m m' = -EM m' m := fun m m' => by
    have : (EM m m' : ℝ) = -EM m' m := by rw [← hpE, ← hpE, him]
    exact_mod_cast this
  have hTs : ∀ x y, φ (s x) y = φ (s y) x := fun x y => by rw [hφ, hφ, hΦ, hs, hs, hS]; simp
  have hTa : ∀ (a : O) y x, φ (s (a • y)) x = φ (s y) (star a • x) := fun a y x => by
    rw [hφ, hφ, hsρ, hsρ, hΦρ]
  let A : AnArc O :=
    { gB := n
      abelian₂ := LinearMap.range p.toIntLinearMap
      discrete := hpd
      full := hps
      Hm := Hm
      Hm_herm := by ext i k; exact hconj _ _
      Hm_pos := fun z hz => by rw [hHm]; exact hpos _ fun h0 => hz (hjinj (by rw [h0, map_zero]))
      Ef := Ef
      Ef_eq := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        rw [hEf, hHm, hf, hf, hpE]
      Ef_bij := by
        have : (Ef : _ → _) = f.symm.dualMap ∘ EM ∘ f.symm := rfl
        rw [this]
        exact f.symm.dualMap.bijective.comp (hEM.comp f.symm.bijective)
      chi := fun l => (-1) ^ EM (w • f.symm l) (f.symm l)
      chi_norm := fun l => by simp
      chi_add := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        have h1 : EM (w • (l + m)) (l + m) =
            EM (w • l) l + EM (w • m) m + EM l m + 2 * (EM (w • l) m - EM l m) := by
          have h2 : EM (w • l) m + EM (star w • l) m = EM l m := by
            rw [← LinearMap.add_apply, ← map_add (f := _), ← add_smul, hw, one_smul]
          have h3 : EM (w • m) l = -EM (star w • l) m := by rw [hEadj, hEalt]
          simp only [smul_add, map_add (f := _), LinearMap.add_apply]
          linarith
        rw [hHm, hf, hf, hpE, exp_pi_I_int, ← map_add f]
        simp only [LinearEquiv.symm_apply_apply, h1, zpow_add₀ (neg_ne_zero.2 (one_ne_zero (α := ℂ))), zpow_mul]
        simp
      chi_neg := fun l => by simp only [map_neg, smul_neg, LinearMap.neg_apply, neg_neg]
      F := F
      F_mem := by rintro a _ ⟨m, rfl⟩; exact ⟨a • m, hpF a m⟩
      F_adj := fun a z z' => by rw [hHm, hHm, hjF, hjF, hρ]
      X := Y
      ct := q.toAddMonoidHom.comp s
      ct_smul := fun a x => by
        show q (s (a • x)) = F a (q (s x))
        rw [hsρ, hqρ]
      T := φ.toAddMonoidHom.comp s
      T_symm := hTs
      T_adj := hTa
      psi := fun x => Units.mk0 (eTwoPi (φ (s x) (w • x))) (AnArc.e_ne_zero _)
      psi_neg := fun x => by simp
      psi_add := fun x y => by
        have h2 : φ (s x) (w • y) + φ (s y) (w • x) = φ (s x) y := by
          rw [hTs y, hTa, ← map_add (f := _), ← add_smul, hw, one_smul]
        change eTwoPi _ = eTwoPi _ * eTwoPi _ * eTwoPi (φ (s x) y)
        simp only [← AnArc.e_add, smul_add, map_add (f := _), AddMonoidHom.add_apply]
        congr 1
        linear_combination h2
      be := be
      be_symm := be_symm
      be_pos := be_pos
      be_adj := be_adj
      be_even := be_even }
  have hfF : ∀ (a : O) m, f (a • m) = A.FLam a (f m) := fun a m => Subtype.ext (hpF a m)
  refine ⟨A, LinearEquiv.refl O Y, f.toAddEquiv, h, fun _ _ => rfl, fun l => ?_, fun _ => rfl, hF, hfF, hEf,
    fun a z => ?_, fun v => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := f.surjective l
    rw [← hfF]
    show (-1 : ℂ) ^ EM (w • f.symm (f l)) (f.symm (f l)) = (-1) ^ Ef (f (w • l)) (f l)
    rw [hEf, f.symm_apply_apply]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) (hqρ a z)
    show φ (ρ a z) x = φ z (star a • x)
    rw [hφ, hφ, hΦρ, hsρ]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · show φ (P v) x = φ (s v.1) x + v.2.1 x - hermForm Hm (q (s x)) (p v.2.2) / (2 * I)
      rw [hφP, hHm, hp]
    · show q (P v) = q (s v.1) + p v.2.2
      rw [hPv, map_add (f := _), map_add (f := _), hqR _ (hmem _), add_zero, hp]
  · have hB : ∀ y x : Y, A.Bw 0 y x = (S (b (s y)) (b (s x))).re := fun y x => by
      show (φ (s y) x + 0 * (be y x : ℂ) + hermForm Hm (q (s y)) (q (s x)) / (2 * I)).im = _
      rw [hφ, hHm, hb' _ _ (hb _)]
      simp [Φ]
    let c := Module.Free.chooseBasis ℤ A.X
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext i k; simp [AnArc.BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]
    · have h1 : ∑ i, x i • b (s (c i)) ≠ 0 := fun h0 => hx (funext fun k => by
        have h2 := congrArg (fun z => reForm S z (P (0, (c.coord k).toAddMonoidHom, 0))) h0
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, hb' _ _ (hmem _), hs,
          hS] at h2
        simpa [Finsupp.single_apply] using h2)
      refine (hpos _ h1).trans_eq ?_
      rw [← reForm_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, ← hB, dotProduct,
        Matrix.mulVec, AnArc.BwMat_apply, Finset.mul_sum, smul_eq_mul, star_trivial]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp only [c]; ring

end GlobalTheory.OfPeriod
