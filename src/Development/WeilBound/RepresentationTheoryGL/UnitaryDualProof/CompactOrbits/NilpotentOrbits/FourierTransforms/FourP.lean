module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceNilpotentConeProjection

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ReflH
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourierTransformInvolution
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourierTransformPreservesCompact
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.CharacteristicFunctionIntegralApply
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.DistribHaarCharAdU
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.RealTestFunctionApply
noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

def Dl : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (d Z) → k) where
  toFun := D Z
  map_add' := D_add Z
  map_smul' := D_smul Z

abbrev TT : Type := ↥(LinearMap.ker (Dl Z)) × (Fin n → k)

theorem continuous_E : Continuous (E Z) := by
  have e : E Z = fun u => ∑ j, u j • ee Z j := funext (E_apply Z)
  rw [e]
  fun_prop

theorem continuous_D : Continuous (D Z) :=
  continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_trace

theorem continuous_Pr : Continuous (Pr Z) :=
  (continuous_E Z).comp (continuous_const.matrix_mulVec (continuous_D Z))

variable {Z}
variable (hZ : CR Z) (h : Hyp Z)

def Hb : Sp k n ≃ₜ TT Z × (Fin (d Z) → k) where
  toFun p := ((⟨p.1 - Pr Z p.1, by show D Z _ = 0; exact D_sub_Pr hZ h _⟩, p.2), D Z p.1)
  invFun q := (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ q.2), q.1.2)
  left_inv p := by
    ext1
    · show p.1 - Pr Z p.1 + E Z ((G Z)⁻¹ *ᵥ D Z p.1) = p.1
      rw [← Pr, sub_add_cancel]
    · rfl
  right_inv q := by
    obtain ⟨⟨⟨y, hy⟩, v⟩, w⟩ := q
    have hy' : D Z y = 0 := hy
    have hPy : Pr Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = E Z ((G Z)⁻¹ *ᵥ w) := by
      rw [Pr_add, Pr_of_D hZ h hy', Pr_E hZ h, zero_add]
    have hDx : D Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = w := by
      rw [D_add, hy', zero_add, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]
    refine Prod.ext (Prod.ext (Subtype.ext ?_) rfl) hDx
    show y + E Z ((G Z)⁻¹ *ᵥ w) - Pr Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = y
    rw [hPy, add_sub_cancel_right]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd)
      ((continuous_D Z).comp continuous_fst)
    exact continuous_fst.sub ((continuous_Pr Z).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_fst)
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).add
      ((continuous_E Z).comp (continuous_const.matrix_mulVec continuous_snd))

def Gm : (Fin (d Z) → k) ≃ₜ (Fin (d Z) → k) where
  toFun u := G Z *ᵥ u
  invFun u := (G Z)⁻¹ *ᵥ u
  left_inv u := by
    show (G Z)⁻¹ *ᵥ (G Z *ᵥ u) = u
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]
  right_inv u := by
    show G Z *ᵥ ((G Z)⁻¹ *ᵥ u) = u
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def F1 : TT Z × (Fin (d Z) → k) ≃ₜ Sp k n := ((Homeomorph.refl (TT Z)).prodCongr (Gm hZ h)).trans (Hb hZ h).symm

theorem real_test_function_apply (q : TT Z × (Fin (d Z) → k)) : F1 hZ h q = (q.1.1.1 + E Z q.2, q.1.2) := by
  show (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ (G Z *ᵥ q.2)), q.1.2) = _
  rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (Fin (d Z) → k) →ₗ[k] (Fin (d Z) → k) where
  toFun u := (bas Z).equivFun ⟨g.val * E Z u * g⁻¹.val, conj_mem_nilpotent_cone hg (E_mem Z u)⟩
  map_add' u u' := by
    rw [← map_add (f := _)]
    congr 1
    ext1
    simp [E_add, mul_add, add_mul]
  map_smul' c u := by
    rw [← map_smul]
    congr 1
    ext1
    simp [E_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) :
    E Z (adL hg u) = g.val * E Z u * g⁻¹.val := by
  simp [adL, E]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem trace_conj (g : GL (Fin n) k) (A : Matrix (Fin n) (Fin n) k) : trace (g.val * A * g⁻¹.val) = trace A := by
  rw [trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem dot_conj {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) (x : Matrix (Fin n) (Fin n) k) :
    adL hg u ⬝ᵥ D Z (g.val * x * g⁻¹.val) = u ⬝ᵥ D Z x := by
  rw [dot_D, dot_D, E_adL]
  have : g.val * E Z u * g⁻¹.val * (g.val * x * g⁻¹.val) = g.val * (E Z u * x) * g⁻¹.val := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [this, trace_conj]

def adM {g : GL (Fin n) k} (hg : g ∈ Gz Z) : Matrix (Fin (d Z)) (Fin (d Z)) k := LinearMap.toMatrix' (adL hg)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem adM_mulVec {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) : adM hg *ᵥ u = adL hg u :=
  LinearMap.toMatrix'_mulVec _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem dot_G (u u' : Fin (d Z) → k) : u ⬝ᵥ (G Z *ᵥ u') = trace (E Z u * E Z u') := by
  rw [← D_E, dot_D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gram_adM {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg)ᵀ * G Z * adM hg = G Z := by
  have key : ∀ u u', u ⬝ᵥ (((adM hg)ᵀ * G Z * adM hg) *ᵥ u') = u ⬝ᵥ (G Z *ᵥ u') := by
    intro u u'
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, adM_mulVec, adM_mulVec, dot_G,
      dot_G, E_adL, E_adL]
    have : g.val * E Z u * g⁻¹.val * (g.val * E Z u' * g⁻¹.val) = g.val * (E Z u * E Z u') * g⁻¹.val := by
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, trace_conj]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single_one] using this

variable (hZ : CR Z) (h : Hyp Z)
include hZ h

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_adM_sq {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg).det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det (gram_adM hg)
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : ((adM hg).det ^ 2 - 1) * (G Z).det = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linear_combination h3
  · exact absurd h3 (G_det hZ h)

def adU {g : GL (Fin n) k} (hg : g ∈ Gz Z) : GL (Fin (d Z)) k :=
  Matrix.nonsingInvUnit (adM hg) (Ne.isUnit fun h0 => by
    have := det_adM_sq hZ h hg
    rw [h0] at this
    norm_num at this)

theorem distribHaarChar_adU {g : GL (Fin n) k} (hg : g ∈ Gz Z) :
    (distribHaarChar k (Matrix.GeneralLinearGroup.det (adU hZ h hg)) : NNReal) = 1 := by
  set u := Matrix.GeneralLinearGroup.det (adU hZ h hg)
  have hu : u ^ 2 = 1 := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_adM_sq hZ h hg)
  have h2 : (distribHaarChar k u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

def phi0 (f : Sp k n → ℂ) : Sp k n → ℂ :=
  fun p => GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (d Z) => ν) (fun q => f (F1 hZ h q)) (Hb hZ h p)

theorem characteristic_function_integral_apply (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h f p = ∫ u, f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ) ∂(Measure.pi fun _ => ν) := by
  have key : ∀ x : Fin (d Z) → k, ((G Z)⁻¹ * G Z) *ᵥ x = x := fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (Gm hZ h).symm_apply_apply x
  simp [phi0, GlobalTheory.SplitDict.pf, F1, Hb, Gm, key]

theorem test_vector_mem_schwartz_bruhat {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) :
    phi0 ψ ν hZ h f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  have hg : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    ⟨hf.1.1.comp_continuous (F1 hZ h).continuous, hf.1.2.comp_homeomorph (F1 hZ h)⟩
  have hpf := GlobalTheory.SplitDict.pf_mem_SB (Measure.pi fun _ : Fin (d Z) => ν) hc hg
  refine ⟨⟨?_, ?_⟩, Set.subset_univ _⟩
  · exact hpf.1.comp_continuous (Hb hZ h).continuous
  · exact hpf.2.comp_homeomorph (Hb hZ h)

theorem integrable_slice (hψ : Continuous ψ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (p : Sp k n) :
    Integrable (fun u => f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ)) (Measure.pi fun _ => ν) := by
  have key : ∀ x : Fin (d Z) → k, ((G Z)⁻¹ * G Z) *ᵥ x = x := fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (Gm hZ h).symm_apply_apply x
  have hslice : (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) = fun x => (f ∘ F1 hZ h) ((Hb hZ h p).1, x) := by
    funext x
    simp [F1, Hb, Gm, key]
  have hg : HasCompactSupport (f ∘ F1 hZ h) := hf.1.2.comp_homeomorph _
  have hfc : Continuous f := hf.1.1.continuous
  have hcs : HasCompactSupport (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) := by
    refine HasCompactSupport.intro (hg.isCompact.image continuous_snd) ?_
    intro x hx
    rw [congrFun hslice x]
    by_contra hne
    exact hx ⟨((Hb hZ h p).1, x), subset_tsupport _ hne, rfl⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (hcs.mul_right (f' := fun u => (ψ (u ⬝ᵥ D Z p.1) : ℂ)))
  have h1 : Continuous (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) := by
    rw [hslice]
    exact (hfc.comp (F1 hZ h).continuous).comp (Continuous.prodMk_right _)
  have h2 : Continuous (fun u : Fin (d Z) → k => (ψ (u ⬝ᵥ D Z p.1) : ℂ)) := by
    fun_prop
  exact h1.mul h2

def phiS (hψ : Continuous ψ) : (supportedIn (Set.univ : Set (Sp k n))) →ₗ[ℂ] (Sp k n → ℂ) where
  toFun f := phi0 ψ ν hZ h f.1
  map_add' f g := by
    funext p
    simp only [Submodule.coe_add, Pi.add_apply, characteristic_function_integral_apply, add_mul]
    exact integral_add (integrable_slice ψ ν hZ h hψ f.2 p) (integrable_slice ψ ν hZ h hψ g.2 p)
  map_smul' c f := by
    funext p
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, characteristic_function_integral_apply, mul_assoc, RingHom.id_apply]
    exact integral_const_mul _ _

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_mem (x : Matrix (Fin n) (Fin n) k) : Pr Z x ∈ B0 Z := E_mem Z _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem quadratic_form_vanishes_nilpotent {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) : qL Z w = 0 := LinearMap.mem_ker.1 hw.2

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

theorem fourier_transform_vanishes_on_fibre (f : Sp k n → ℂ) {y : Fin (Module.finrank k Z) → k} (hf0 : ∀ q ∈ Fib Z y, f q = 0) {p : Sp k n}
    (hp : p ∈ Fib Z y) : phi0 ψ ν hZ h f p = 0 := by
  rw [characteristic_function_integral_apply]
  have hz : ∀ u, f (p.1 - Pr Z p.1 + E Z u, p.2) = 0 := by
    intro u
    apply hf0
    obtain ⟨⟨hB, hq⟩, -⟩ := hp
    have hw : E Z u - Pr Z p.1 ∈ B0 Z := Submodule.sub_mem _ (E_mem Z u) (Pr_mem _)
    have hw1 : E Z u - Pr Z p.1 ∈ BzL Z := (Submodule.mem_inf.mp hw).1
    have hw2 : qL Z (E Z u - Pr Z p.1) = 0 := quadratic_form_vanishes_nilpotent hw
    have heq : p.1 - Pr Z p.1 + E Z u = p.1 + (E Z u - Pr Z p.1) := by abel
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · show p.1 - Pr Z p.1 + E Z u ∈ BzL Z
      rw [heq]
      exact (BzL Z).add_mem hB hw1
    · have hadd := (qL Z).map_add p.1 (E Z u - Pr Z p.1)
      rw [hw2, add_zero] at hadd
      show qZ Z (p.1 - Pr Z p.1 + E Z u) = y
      rw [heq]
      exact hadd.trans hq
  simp [hz]

theorem fourier_transform_equivariant {g : GL (Fin n) k} (hg : g ∈ Gz Z) (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h (fun q => f (act g q)) p = phi0 ψ ν hZ h f (act g p) := by
  have hdet : (adM hg).det ≠ 0 := by
    intro h0
    have := det_adM_sq hZ h hg
    rw [h0] at this
    simp at this
  have hU : IsUnit (adM hg).det := isUnit_iff_ne_zero.mpr hdet
  let e : (Fin (d Z) → k) ≃ᵐ (Fin (d Z) → k) :=
    { toFun := fun u => adM hg *ᵥ u
      invFun := fun u => (adM hg)⁻¹ *ᵥ u
      left_inv := fun u => by simp [mulVec_mulVec, nonsing_inv_mul _ hU]
      right_inv := fun u => by simp [mulVec_mulVec, mul_nonsing_inv _ hU]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have hmap : Measure.map e (Measure.pi fun _ : Fin (d Z) => ν) = Measure.pi fun _ => ν := by
    have := GlobalTheory.WeilM.smul_map_mulVec_pi ν (adM hg) (GeneralLinearGroup.det (adU hZ h hg)) rfl
    rw [distribHaarChar_adU] at this
    show Measure.map (fun u => adM hg *ᵥ u) _ = _
    simpa using this
  rw [characteristic_function_integral_apply, characteristic_function_integral_apply]
  conv_rhs => rw [← hmap, e.measurableEmbedding.integral_map]
  congr 1
  funext u
  have he : e u = adL hg u := adM_mulVec hg u
  simp only [act]
  rw [he, E_adL, Pr_conj hZ h hg, dot_conj]
  congr 3
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem fourier_transform_preserves_compact {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) :
    phi0 ψ ν hZ h f ∈ supportedIn (UU : Set (Sp k n)) := by
  have hm := test_vector_mem_schwartz_bruhat ψ ν hZ h hc (f := f) ⟨hf.1, Set.subset_univ _⟩
  refine ⟨hm.1, ?_⟩
  intro p hp
  by_contra hp2
  apply hp
  have h0 : p.2 = 0 := by
    by_contra hne
    exact hp2 hne
  rw [characteristic_function_integral_apply]
  have hz : ∀ u, f (p.1 - Pr Z p.1 + E Z u, p.2) = 0 := by
    intro u
    by_contra hne
    exact hf.2 hne h0
  simp [hz]

def Refl (p : Sp k n) : Sp k n := (p.1 - (2 : k) • Pr Z p.1, p.2)

omit [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Refl_Refl (p : Sp k n) : Refl (Z := Z) (Refl (Z := Z) p) = p := by
  have hPP : Pr Z (Pr Z p.1) = Pr Z p.1 := Pr_E hZ h _
  have hP : Pr Z (p.1 - (2 : k) • Pr Z p.1) = - Pr Z p.1 := by
    rw [sub_eq_add_neg, Pr_add, ← neg_smul, Pr_smul, hPP]
    module
  obtain ⟨x, v⟩ := p
  simp only [Refl] at hP ⊢
  rw [hP]
  ext <;> simp

theorem partial_fourier_first_coordinates (q : TT Z × (Fin (d Z) → k)) : Hb hZ h (F1 hZ h q) = (q.1, G Z *ᵥ q.2) := by
  simp only [F1, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

def Gu : GL (Fin (d Z)) k := Matrix.nonsingInvUnit (G Z) (Ne.isUnit (G_det hZ h))

theorem pf_G (F : TT Z × (Fin (d Z) → k) → ℂ) (z : TT Z × (Fin (d Z) → k)) :
    ∫ u, F (z.1, G Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) ∂(Measure.pi fun _ => ν) =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F (z.1, (G Z)⁻¹ *ᵥ z.2) := by
  have hU : IsUnit (G Z).det := isUnit_iff_ne_zero.mpr (G_det hZ h)
  set c := distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) with hcdef
  have hc : c ≠ 0 := by
    intro h0
    have := map_mul (distribHaarChar k) (Matrix.GeneralLinearGroup.det (Gu hZ h))
      (Matrix.GeneralLinearGroup.det (Gu hZ h))⁻¹
    rw [mul_inv_cancel, map_one, ← hcdef, h0, zero_mul] at this
    exact zero_ne_one this.symm
  let e : (Fin (d Z) → k) ≃ᵐ (Fin (d Z) → k) :=
    { toFun := fun u => G Z *ᵥ u
      invFun := fun u => (G Z)⁻¹ *ᵥ u
      left_inv := fun u => by simp [mulVec_mulVec, nonsing_inv_mul _ hU]
      right_inv := fun u => by simp [mulVec_mulVec, mul_nonsing_inv _ hU]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have hsm := GlobalTheory.WeilM.smul_map_mulVec_pi ν (G Z) (Matrix.GeneralLinearGroup.det (Gu hZ h)) rfl
  rw [← hcdef] at hsm
  have hc0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
  have hct : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hmap : Measure.map e (Measure.pi fun _ : Fin (d Z) => ν) = (c : ENNReal)⁻¹ • Measure.pi fun _ => ν := by
    show Measure.map (G Z).mulVec _ = _
    conv_rhs => rw [← hsm]
    rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  let H : (Fin (d Z) → k) → ℂ := fun x => F (z.1, x) * (ψ (x ⬝ᵥ (G Z)⁻¹ *ᵥ z.2) : ℂ)
  have hH : ∀ u, F (z.1, G Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) = H (e u) := by
    intro u
    show _ = F (z.1, G Z *ᵥ u) * (ψ ((G Z *ᵥ u) ⬝ᵥ (G Z)⁻¹ *ᵥ z.2) : ℂ)
    rw [dotProduct_mulVec, vecMul_mulVec, ← Matrix.mulVec_transpose, G_symm, mul_nonsing_inv _ hU,
      transpose_one, one_mulVec]
  rw [integral_congr_ae (ae_of_all _ hH), ← e.measurableEmbedding.integral_map, hmap, integral_smul_measure]
  simp [GlobalTheory.SplitDict.pf, H]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

theorem fourier_transform_involution {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (p : Sp k n) :
    phi0 ψ ν hZ h (phi0 ψ ν hZ h f) p =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ (d Z) : ℝ)) : ℂ) * f (Refl (Z := Z) p) := by
  have h1 : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 hZ h)).1 hf.1
  have e : ∀ q, phi0 ψ ν hZ h f (F1 hZ h q) =
      GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) (q.1, G Z *ᵥ q.2) := by
    intro q
    show GlobalTheory.SplitDict.pf _ _ _ (Hb hZ h (F1 hZ h q)) = _
    rw [partial_fourier_first_coordinates]
  show GlobalTheory.SplitDict.pf ψ _ (fun q => phi0 ψ ν hZ h f (F1 hZ h q)) (Hb hZ h p) = _
  simp only [e]
  show ∫ u, GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) ((Hb hZ h p).1, G Z *ᵥ u) *
      (ψ (u ⬝ᵥ (Hb hZ h p).2) : ℂ) ∂(Measure.pi fun _ => ν) = _
  rw [pf_G ψ ν hZ h, GlobalTheory.SplitDict.pf_pf ν hc h1]
  simp only [real_test_function_apply, Fintype.card_fin]
  have e2 : ((Hb hZ h p).1.1 : Matrix (Fin n) (Fin n) k) + E Z (-((G Z)⁻¹ *ᵥ (Hb hZ h p).2)) =
      p.1 - (2 : k) • Pr Z p.1 := by
    rw [E_neg]
    show p.1 - Pr Z p.1 + -(E Z ((G Z)⁻¹ *ᵥ D Z p.1)) = _
    rw [← Pr, two_smul]
    abel
  have e3 : (Hb hZ h p).1.2 = p.2 := rfl
  rw [e2, e3]
  simp only [Refl]
  ring

def Tu (t : kˣ) : GL (Fin (d Z)) k := Units.map (Matrix.scalar (Fin (d Z)) : k →+* Matrix (Fin (d Z)) (Fin (d Z)) k) t

omit hZ h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Tu_mulVec (t : kˣ) (u : Fin (d Z) → k) : (Tu (Z := Z) t).val *ᵥ u = (t : k) • u := by
  funext i
  simp [Tu, Matrix.scalar_apply, mulVec_diagonal]

omit hZ h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Tu_det (t : kˣ) : Matrix.GeneralLinearGroup.det (Tu (Z := Z) t) = t ^ d Z := by
  ext
  simp [Tu, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

theorem fourier_transform_scaling (t : kˣ) (f : Sp k n → ℂ) {p : Sp k n} (hp : p ∈ Bz Z ×ˢ Set.univ) :
    phi0 ψ ν hZ h f (sig Z t p) =
      ((((nabs k t)⁻¹ ^ d Z : ℝ)) : ℂ) * phi0 ψ ν hZ h (fun q => f (sig Z t⁻¹ q)) p := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp.1
  have hDy : D Z (x - Pr Z x) = 0 := D_sub_Pr hZ h x
  have hPy : Pr Z (x - Pr Z x) = 0 := Pr_of_D hZ h hDy
  have hpi : piZ Z x = x - Pr Z x := piZ_eq_sub hZ h hx
  have hsig : (sig Z t (x, v)) = (x - Pr Z x + (t : k) • Pr Z x, v) := by
    simp only [sig, hpi, sub_sub_cancel]
  rw [hsig, characteristic_function_integral_apply, characteristic_function_integral_apply]
  have hP : Pr Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • Pr Z x := by
    rw [Pr_add, hPy, Pr_smul, show Pr Z (Pr Z x) = Pr Z x from Pr_E hZ h _, zero_add]
  have hD : D Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • D Z x := by
    rw [D_add, hDy, D_smul, D_Pr hZ h, zero_add]
  simp only [hP, hD, add_sub_cancel_right]
  have hyB : ∀ u, x - Pr Z x + E Z u ∈ Bz Z := fun u =>
    (BzL Z).add_mem ((BzL Z).sub_mem hx (Pr_mem x).1) (E_mem Z u).1
  have hpi2 : ∀ u, piZ Z (x - Pr Z x + E Z u) = x - Pr Z x := fun u => by
    rw [piZ_eq_sub hZ h (hyB u), Pr_add, hPy, Pr_E hZ h, zero_add, add_sub_cancel_right]
  have hs : ∀ u, sig Z t⁻¹ (x - Pr Z x + E Z u, v) = (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) := fun u => by
    simp only [sig, hpi2, add_sub_cancel_left, E_smul, Units.val_inv_eq_inv_val]
  simp only [hs]
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν (Tu (Z := Z) t)
    (fun u => f (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) * (ψ (u ⬝ᵥ D Z x) : ℂ))
  have ht : (t : k) ≠ 0 := t.ne_zero
  simp only [Tu_mulVec, Tu_det, map_pow, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_dotProduct,
    ← dotProduct_smul] at key
  rw [← key]
  have hn : (nabs k t : ℝ) = ((distribHaarChar k t : NNReal) : ℝ) := rfl
  have hpos : (nabs k t : ℝ) ≠ 0 := by rw [hn]; exact_mod_cast (distribHaarChar_pos).ne'
  rw [NNReal.coe_pow, ← hn]
  push_cast
  have hposC : ((nabs k t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hposC, one_pow, one_mul]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def ReflH (hZ : CR Z) (h : Hyp Z) : Sp k n ≃ₜ Sp k n where
  toFun := Refl (Z := Z)
  invFun := Refl (Z := Z)
  left_inv := Refl_Refl hZ h
  right_inv := Refl_Refl hZ h
  continuous_toFun := by
    show Continuous fun p : Sp k n => (p.1 - (2 : k) • Pr Z p.1, p.2)
    exact (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd
  continuous_invFun := by
    show Continuous fun p : Sp k n => (p.1 - (2 : k) • Pr Z p.1, p.2)
    exact (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd

theorem d_eq [CharZero k] (hZ : CR Z) : d Z = dB0 Z := by
  classical
  have hsurj : LinearMap.range ((qL Z).domRestrict (BzL Z)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨c, hc, rfl⟩ := PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_surj hZ y
    exact ⟨⟨c, Z_le_Bz Z hZ hc⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker ((qL Z).domRestrict (BzL Z))
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hker : LinearMap.ker ((qL Z).domRestrict (BzL Z)) = (B0 Z).comap (BzL Z).subtype := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.subtype_apply, B0, Submodule.mem_inf, x.2, true_and]
  have e : Module.finrank k (LinearMap.ker ((qL Z).domRestrict (BzL Z))) =
      Module.finrank k (B0 Z) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : B0 Z ≤ BzL Z)).finrank_eq
  have hS : Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      BzL Z := by
    ext x
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rfl
  have hC : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      Module.finrank k (BzL Z) := by
    rw [← Subalgebra.finrank_toSubmodule, hS]
  show Module.finrank k (B0 Z) = Module.finrank k _ - Module.finrank k _
  rw [hC]
  omega

theorem phiP [CharZero k] : PhiP (k := k) := by
  intro n Z hZ
  borelize k
  have h : Hyp Z := ⟨PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_mem hZ, PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_piZ hZ,
    fun x c hc hq => PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_eq hZ hc hq,
    fun w hw hb => PositivityTheory.RgUd.T.Nil.Four.Alg.trB_nondeg hZ hw hb⟩
  obtain ⟨ψ, hψ⟩ := exists_hasConductor_one k
  let ν : Measure k := Measure.addHaar
  have hcomp : ∀ (U : Set (Sp k n)) (e : Sp k n ≃ₜ Sp k n), (∀ x, e x ∈ U → x ∈ U) →
      ∀ f : Sp k n → ℂ, f ∈ supportedIn U → (fun p => f (e p)) ∈ supportedIn U := by
    intro U e he f hf
    rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
    obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
    refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact he x (hsu hx)
  have hU : ∀ (e : Sp k n ≃ₜ Sp k n) (f : Sp k n → ℂ), f ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun e => hcomp Set.univ e (fun _ _ => Set.mem_univ _)
  have hRf : ∀ f : Sp k n → ℂ, f ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun p => f (Refl (Z := Z) p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => hU (ReflH hZ h) f hf
  have hRU : ∀ f : Sp k n → ℂ, f ∈ supportedIn (UU : Set (Sp k n)) →
      (fun p => f (Refl (Z := Z) p)) ∈ supportedIn (UU : Set (Sp k n)) :=
    fun f hf => hcomp UU (ReflH hZ h) (fun _ hx => hx) f hf
  obtain ⟨q, hq⟩ := (supportedIn (Set.univ : Set (Sp k n))).exists_isCompl
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    (phiS ψ ν hZ h hψ.continuous).comp ((supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq)
  have hΦ : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f = phi0 ψ ν hZ h f := by
    intro f hf
    have e1 : (supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq f = ⟨f, hf⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩
    simp only [Φ, LinearMap.comp_apply, e1]
    rfl
  let κ : ℂ := (((distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) : ℝ) : ℂ)⁻¹ *
    (((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ d Z : ℝ) : ℂ)
  have hχ : (distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) ≠ 0 := by
    have e2 := map_mul_eq_one (distribHaarChar k)
      (mul_inv_cancel (GeneralLinearGroup.det (Gu hZ h)))
    exact left_ne_zero_of_mul_eq_one e2
  have hO : IsOpen ((𝒪[k] : Set k)) := (ValuativeRel.valuation k).isOpen_integer
  have hC : IsCompact ((𝒪[k] : Set k)) :=
    isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])
  have hν : 0 < ν.real (𝒪[k] : Set k) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hO.measure_ne_zero ν ⟨0, zero_mem _⟩) hC.measure_lt_top.ne
  have hn1 : nabs k 1 = 1 := by
    simp [nabs]
  have hκ : κ ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) ?_
    · exact_mod_cast hχ
    · rw [hn1, mul_one]
      exact_mod_cast pow_ne_zero _ (pow_pos hν 2).ne'
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    κ⁻¹ • (Φ.comp (LinearMap.funLeft ℂ ℂ (Refl (Z := Z))))
  have hΦ' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
      Φ' f = κ⁻¹ • phi0 ψ ν hZ h (fun p => f (Refl (Z := Z) p)) := by
    intro f hf
    show κ⁻¹ • Φ (fun p => f (Refl (Z := Z) p)) = _
    rw [hΦ _ (hRf f hf)]
  refine ⟨Φ, Φ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hΦ f hf]
    exact test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hf
  · intro f hf
    rw [hΦ' f hf]
    exact Submodule.smul_mem _ _ (test_vector_mem_schwartz_bruhat ψ ν hZ h hψ (hRf f hf))
  · intro f hf y hy p hp
    rw [hΦ f hf]
    exact fourier_transform_vanishes_on_fibre ψ ν hZ h f hy hp
  · intro g hg f hf p hp
    have hA : (fun p => f (act g p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      hU (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g) f hf
    rw [hΦ f hf, hΦ _ hA]
    exact fourier_transform_equivariant ψ ν hZ h hg f p
  · intro f hf
    have hf' := supportedIn_mono (Set.subset_univ _) hf
    rw [hΦ f hf']
    exact fourier_transform_preserves_compact ψ ν hZ h hψ hf
  · intro f hf
    have hf' := supportedIn_mono (Set.subset_univ _) hf
    rw [hΦ' f hf']
    exact Submodule.smul_mem _ _ (fourier_transform_preserves_compact ψ ν hZ h hψ (hRU f hf))
  · intro f hf p hp
    have hR := hRf f hf
    have hm := test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hR
    rw [hΦ' f hf, map_smul, hΦ _ hm, Pi.smul_apply, fourier_transform_involution ψ ν hZ h hψ hR p,
      Refl_Refl hZ h, smul_eq_mul, ← mul_assoc]
    change κ⁻¹ * κ * f p = f p
    rw [inv_mul_cancel₀ hκ, one_mul]
  · intro t f hf p hp
    have hS : (fun p => f (sig Z t⁻¹ p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      hU (PositivityTheory.RgUd.T.Nil.Four.Alg.sigH hZ t⁻¹) f hf
    rw [hΦ f hf, hΦ _ hS, ← d_eq hZ]
    exact fourier_transform_scaling ψ ν hZ h t f hp

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.SuppCongr
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem supp_congr {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ}
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) {f g : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (hg : g ∈ supportedIn (Set.univ : Set (Sp k n))) (e : ∀ p ∈ Bz Z ×ˢ Set.univ, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn (Set.univ : Set (Sp k n))).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

theorem fourP_of (hΦ : PhiP (k := k)) (hC : CompP (k := k)) : FourP (k := k) := by
  intro n Z hZ
  obtain ⟨Φ, Φ', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hΦ n Z hZ
  obtain ⟨hCs, hCa, -, -⟩ := hC n Z hZ
  have hUU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => ⟨hf.1, Set.subset_univ _⟩
  let F : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] (Sp k n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun a b => by ext; simp
      map_smul' := fun a b => by ext; simp }
  have hF : ∀ ξ f, F ξ f = ξ (Φ f) := fun _ _ => rfl
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf hz
    rw [hF]
    refine hξ _ (h1 f hf) fun p hp => ?_
    have hpF : p ∈ Fib Z (qZ Z p.1) := ⟨⟨hp.1, rfl⟩, Set.mem_univ _⟩
    exact h3 f hf (qZ Z p.1) (fun q hq => hz q ⟨hq.1.1, Set.mem_univ _⟩) p hpF
  · intro ξ y hξ f hf hz
    rw [hF]
    exact hξ _ (h1 f hf) (h3 f hf y hz)
  · intro ξ hξ hinv g hg f hf
    rw [hF, hF]
    have hfg : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCa g f hf
    rw [supp_congr hξ (h1 _ hfg) (hCa g _ (h1 f hf)) (fun p hp => h4 g hg f hf p hp)]
    exact hinv g hg _ (h1 f hf)
  · intro ξ hξ
    constructor
    · intro hk f hf
      rw [hF]
      exact hk _ (h5 f hf)
    · intro hk f hf
      have hfu := hUU f hf
      rw [← supp_congr hξ (h1 _ (h2 f hfu)) hfu (fun p hp => h7 f hfu p hp)]
      exact hk _ (h6 f hf)
  · intro ξ hξ f hf
    rw [hF]
    exact hξ _ (h1 f hf)
  · intro t ξ hξ f hf
    rw [hF]
    show ξ (fun q => Φ f (sig Z t q)) = _ * ξ (Φ (fun q => f (sig Z t⁻¹ q)))
    have hsf : (fun q => f (sig Z t⁻¹ q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCs t⁻¹ f hf
    rw [← smul_eq_mul, ← map_smul]
    exact supp_congr hξ (hCs t _ (h1 f hf)) (Submodule.smul_mem _ _ (h1 _ hsf))
      (fun p hp => by rw [Pi.smul_apply, smul_eq_mul]; exact h8 t f hf p hp)

end PositivityTheory.RgUd.T.Nil.Four
end
end

namespace PositivityTheory.RgUd.T.Nil.Four.Final

open PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fourP [CharZero k] : FourP (k := k) :=
  PositivityTheory.RgUd.T.Nil.Four.fourP_of PositivityTheory.RgUd.T.Nil.Four.Phi2.phiP PositivityTheory.RgUd.T.Nil.Four.Alg.compP

theorem locQ : LocQ (k := k) := PositivityTheory.RgUd.T.Nil.Four.locQ_pf

end PositivityTheory.RgUd.T.Nil.Four.Final
