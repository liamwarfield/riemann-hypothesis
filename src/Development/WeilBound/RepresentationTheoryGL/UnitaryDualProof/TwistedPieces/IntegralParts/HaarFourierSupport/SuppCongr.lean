module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceNilpotentConeProjection

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.FourierTransformTranslationInvariant
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.PartialFourierFirstCoordinates
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.DistribHaarCharAdU
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

structure Hyp : Prop where
  symm : ∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)
  nondeg : ∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0
  nil : ∀ x ∈ NB Z, τ x = 0

abbrev dd : ℕ := Module.finrank k (PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z)

def bas : Module.Basis (Fin (dd Z)) k (PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z) := Module.finBasis k _

def ee (j : Fin (dd Z)) : Matrix (Fin n) (Fin n) k := (bas Z j : PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z)

def E (u : Fin (dd Z) → k) : Matrix (Fin n) (Fin n) k := ((bas Z).equivFun.symm u : PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z)

def D (x : Matrix (Fin n) (Fin n) k) : Fin (dd Z) → k := fun j => τ (ee Z j * x)

def G : Matrix (Fin (dd Z)) (Fin (dd Z)) k := Matrix.of fun i j => τ (ee Z i * ee Z j)

theorem dd_eq : dd Z = dB Z := by
  have e : PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z =
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    ext x
    simp only [PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL, Bz, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff,
      SetLike.mem_coe]
  unfold dd dB
  rw [e, Subalgebra.finrank_toSubmodule]

theorem E_apply (u : Fin (dd Z) → k) : E Z u = ∑ j, u j • ee Z j := by
  simp [E, ee, Module.Basis.equivFun_symm_apply]

theorem E_mem (u : Fin (dd Z) → k) : E Z u ∈ Bz Z := ((bas Z).equivFun.symm u).2

theorem ee_mem (j : Fin (dd Z)) : ee Z j ∈ Bz Z := (bas Z j).2

theorem E_add (u u' : Fin (dd Z) → k) : E Z (u + u') = E Z u + E Z u' := by
  simp only [E, map_add (f := _), Submodule.coe_add]

theorem E_smul (c : k) (u : Fin (dd Z) → k) : E Z (c • u) = c • E Z u := by
  simp only [E, map_smul, Submodule.coe_smul]

theorem E_neg (u : Fin (dd Z) → k) : E Z (-u) = -E Z u := by
  simp only [E, map_neg, Submodule.coe_neg]

theorem E_injective : Function.Injective (E Z) := fun u u' h =>
  (bas Z).equivFun.symm.injective (Subtype.ext h)

theorem E_zero : E Z 0 = 0 := by simp [E]

theorem exists_E {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ Bz Z) : ∃ u, E Z u = w :=
  ⟨(bas Z).equivFun ⟨w, hw⟩, by simp [E]⟩

theorem dot_D (u : Fin (dd Z) → k) (x : Matrix (Fin n) (Fin n) k) : u ⬝ᵥ D τ Z x = τ (E Z u * x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [E_apply, D, dotProduct, Finset.sum_mul, map_sum, smul_mul_assoc]

theorem D_E (u : Fin (dd Z) → k) : D τ Z (E Z u) = G τ Z *ᵥ u := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [D, G, E_apply, mulVec, dotProduct, Finset.mul_sum, map_sum, mul_smul_comm, mul_comm]

theorem D_add (x y : Matrix (Fin n) (Fin n) k) : D τ Z (x + y) = D τ Z x + D τ Z y := by
  funext j; simp [D, mul_add]

theorem D_sub (x y : Matrix (Fin n) (Fin n) k) : D τ Z (x - y) = D τ Z x - D τ Z y := by
  funext j; simp [D, mul_sub]

theorem D_smul (c : k) (x : Matrix (Fin n) (Fin n) k) : D τ Z (c • x) = c • D τ Z x := by
  funext j; simp [D]

theorem mul_mem_Bz {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) (hy : y ∈ Bz Z) : x * y ∈ Bz Z := by
  intro a ha
  rw [← mul_assoc, hx a ha, mul_assoc, hy a ha, mul_assoc]

theorem val_mem_Bz {g : GL (Fin n) k} (hg : g ∈ Gz Z) : g.val ∈ Bz Z := fun a ha => hg a ha

variable {τ Z}

theorem G_symm (h : Hyp τ Z) : (G τ Z)ᵀ = G τ Z := by
  ext i j
  simp only [G, transpose_apply, of_apply]
  exact h.symm _ (ee_mem Z j) _ (ee_mem Z i)

theorem G_inj (h : Hyp τ Z) {u : Fin (dd Z) → k} (hu : G τ Z *ᵥ u = 0) : u = 0 := by
  have hw : E Z u = 0 := by
    refine h.nondeg _ (E_mem Z u) fun y hy => ?_
    obtain ⟨u', rfl⟩ := exists_E Z hy
    rw [h.symm _ (E_mem Z u) _ (E_mem Z u'), ← dot_D, D_E, hu, dotProduct_zero]
  exact E_injective Z (by rw [hw, E_zero])

theorem G_det (h : Hyp τ Z) : (G τ Z).det ≠ 0 := by
  intro h0
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  exact hu0 (G_inj h hu)

variable (τ Z)

def Pr (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := E Z ((G τ Z)⁻¹ *ᵥ D τ Z x)

variable {τ Z}

theorem D_Pr (h : Hyp τ Z) (x : Matrix (Fin n) (Fin n) k) : D τ Z (Pr τ Z x) = D τ Z x := by
  rw [Pr, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det h)), one_mulVec]

theorem Pr_E (h : Hyp τ Z) (u : Fin (dd Z) → k) : Pr τ Z (E Z u) = E Z u := by
  rw [Pr, D_E, mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]

theorem D_sub_Pr (h : Hyp τ Z) (x : Matrix (Fin n) (Fin n) k) : D τ Z (x - Pr τ Z x) = 0 := by
  rw [D_sub, D_Pr h, sub_self]

theorem Pr_add (x y : Matrix (Fin n) (Fin n) k) : Pr τ Z (x + y) = Pr τ Z x + Pr τ Z y := by
  simp [Pr, D_add, mulVec_add, E_add]

theorem Pr_smul (c : k) (x : Matrix (Fin n) (Fin n) k) : Pr τ Z (c • x) = c • Pr τ Z x := by
  simp [Pr, D_smul, mulVec_smul, E_smul]

theorem Pr_of_D {x : Matrix (Fin n) (Fin n) k} (hx : D τ Z x = 0) : Pr τ Z x = 0 := by
  simp [Pr, hx, E]

theorem Pr_of_mem (h : Hyp τ Z) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : Pr τ Z x = x := by
  obtain ⟨u, rfl⟩ := exists_E Z hx
  exact Pr_E h u

theorem tau_conj (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) {y : Matrix (Fin n) (Fin n) k} (hy : y ∈ Bz Z) :
    τ (g.val * y * g⁻¹.val) = τ y := by
  have hgi : g⁻¹.val ∈ Bz Z := val_mem_Bz Z (PositivityTheory.RgUd.T.Nil.Four.Phi2.inv_mem_Gz hg)
  rw [h.symm _ (mul_mem_Bz Z (val_mem_Bz Z hg) hy) _ hgi, ← mul_assoc, Units.inv_mul, one_mul]

def adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (Fin (dd Z) → k) →ₗ[k] (Fin (dd Z) → k) where
  toFun u := (bas Z).equivFun ⟨g.val * E Z u * g⁻¹.val, PositivityTheory.RgUd.T.Nil.Four.Phi2.conj_mem_Bz hg (E_mem Z u)⟩
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

theorem E_adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (dd Z) → k) :
    E Z (adL hg u) = g.val * E Z u * g⁻¹.val := by
  simp [adL, E]

theorem conj_mul (g : GL (Fin n) k) (A B : Matrix (Fin n) (Fin n) k) :
    g.val * A * g⁻¹.val * (g.val * B * g⁻¹.val) = g.val * (A * B) * g⁻¹.val := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem dot_conj (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (dd Z) → k)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) :
    adL hg u ⬝ᵥ D τ Z (g.val * x * g⁻¹.val) = u ⬝ᵥ D τ Z x := by
  rw [dot_D, dot_D, E_adL, conj_mul, tau_conj h hg (mul_mem_Bz Z (E_mem Z u) hx)]

def adM {g : GL (Fin n) k} (hg : g ∈ Gz Z) : Matrix (Fin (dd Z)) (Fin (dd Z)) k := LinearMap.toMatrix' (adL hg)

theorem adM_mulVec {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (dd Z) → k) : adM hg *ᵥ u = adL hg u :=
  LinearMap.toMatrix'_mulVec _ _

theorem dot_G (u u' : Fin (dd Z) → k) : u ⬝ᵥ (G τ Z *ᵥ u') = τ (E Z u * E Z u') := by
  rw [← D_E, dot_D]

theorem gram_adM (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg)ᵀ * G τ Z * adM hg = G τ Z := by
  have key : ∀ u u', u ⬝ᵥ (((adM hg)ᵀ * G τ Z * adM hg) *ᵥ u') = u ⬝ᵥ (G τ Z *ᵥ u') := by
    intro u u'
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, adM_mulVec, adM_mulVec, dot_G,
      dot_G, E_adL, E_adL, conj_mul, tau_conj h hg (mul_mem_Bz Z (E_mem Z u) (E_mem Z u'))]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single_one] using this

theorem det_adM_sq (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg).det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det (gram_adM h hg)
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : ((adM hg).det ^ 2 - 1) * (G τ Z).det = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linear_combination h3
  · exact absurd h3 (G_det h)

def adU (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : GL (Fin (dd Z)) k :=
  Matrix.nonsingInvUnit (adM hg) (Ne.isUnit fun h0 => by
    have := det_adM_sq h hg
    rw [h0] at this
    norm_num at this)

theorem distribHaarChar_adU (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) :
    (distribHaarChar k (Matrix.GeneralLinearGroup.det (adU h hg)) : NNReal) = 1 := by
  set u := Matrix.GeneralLinearGroup.det (adU h hg)
  have hu : u ^ 2 = 1 := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_adM_sq h hg)
  have h2 : (distribHaarChar k u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end PositivityTheory.RgUd.TP.Nil.Four
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

theorem tau_sum (x : Matrix (Fin n) (Fin n) k) : τ x = ∑ i, ∑ j, x i j * τ (Matrix.single i j 1) := by
  have e : ∀ i j, Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : k) := fun i j => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_sum, map_smul, smul_eq_mul]

theorem continuous_tau : Continuous τ := by
  rw [show (⇑τ) = fun x => ∑ i, ∑ j, x i j * τ (Matrix.single i j 1) from funext (tau_sum τ)]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const

def Dl : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (dd Z) → k) where
  toFun := D τ Z
  map_add' := D_add τ Z
  map_smul' := D_smul τ Z

abbrev TT : Type := ↥(LinearMap.ker (Dl τ Z)) × (Fin n → k)

theorem continuous_E : Continuous (E Z) := by
  have e : E Z = fun u => ∑ j, u j • ee Z j := funext (E_apply Z)
  rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const

theorem continuous_D : Continuous (D τ Z) :=
  continuous_pi fun j => (continuous_tau τ).comp (continuous_const.matrix_mul continuous_id)

theorem continuous_Pr : Continuous (Pr τ Z) :=
  (continuous_E Z).comp (continuous_const.matrix_mulVec (continuous_D τ Z))

variable {τ Z}
variable (h : Hyp τ Z)

def Hb : Sp k n ≃ₜ TT τ Z × (Fin (dd Z) → k) where
  toFun p := ((⟨p.1 - Pr τ Z p.1, by show D τ Z _ = 0; exact D_sub_Pr h _⟩, p.2), D τ Z p.1)
  invFun q := (q.1.1.1 + E Z ((G τ Z)⁻¹ *ᵥ q.2), q.1.2)
  left_inv p := by
    ext1
    · show p.1 - Pr τ Z p.1 + E Z ((G τ Z)⁻¹ *ᵥ D τ Z p.1) = p.1
      rw [← Pr, sub_add_cancel]
    · rfl
  right_inv q := by
    obtain ⟨⟨⟨y, hy⟩, v⟩, w⟩ := q
    have hy' : D τ Z y = 0 := hy
    have hPy : Pr τ Z (y + E Z ((G τ Z)⁻¹ *ᵥ w)) = E Z ((G τ Z)⁻¹ *ᵥ w) := by
      rw [Pr_add, Pr_of_D hy', Pr_E h, zero_add]
    have hDx : D τ Z (y + E Z ((G τ Z)⁻¹ *ᵥ w)) = w := by
      rw [D_add, hy', zero_add, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det h)), one_mulVec]
    refine Prod.ext (Prod.ext (Subtype.ext ?_) rfl) hDx
    show y + E Z ((G τ Z)⁻¹ *ᵥ w) - Pr τ Z (y + E Z ((G τ Z)⁻¹ *ᵥ w)) = y
    rw [hPy, add_sub_cancel_right]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd)
      ((continuous_D τ Z).comp continuous_fst)
    exact continuous_fst.sub ((continuous_Pr τ Z).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_fst)
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).add
      ((continuous_E Z).comp (continuous_const.matrix_mulVec continuous_snd))

def Gm : (Fin (dd Z) → k) ≃ₜ (Fin (dd Z) → k) where
  toFun u := G τ Z *ᵥ u
  invFun u := (G τ Z)⁻¹ *ᵥ u
  left_inv u := by
    show (G τ Z)⁻¹ *ᵥ (G τ Z *ᵥ u) = u
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]
  right_inv u := by
    show G τ Z *ᵥ ((G τ Z)⁻¹ *ᵥ u) = u
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det h)), one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def F1 : TT τ Z × (Fin (dd Z) → k) ≃ₜ Sp k n := ((Homeomorph.refl (TT τ Z)).prodCongr (Gm h)).trans (Hb h).symm

theorem real_test_function_apply (q : TT τ Z × (Fin (dd Z) → k)) : F1 h q = (q.1.1.1 + E Z q.2, q.1.2) := by
  show (q.1.1.1 + E Z ((G τ Z)⁻¹ *ᵥ (G τ Z *ᵥ q.2)), q.1.2) = _
  rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]

theorem partial_fourier_first_coordinates (q : TT τ Z × (Fin (dd Z) → k)) : Hb h (F1 h q) = (q.1, G τ Z *ᵥ q.2) := by
  simp only [F1, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

def Gu : GL (Fin (dd Z)) k := Matrix.nonsingInvUnit (G τ Z) (Ne.isUnit (G_det h))

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]

theorem pf_G (F : TT τ Z × (Fin (dd Z) → k) → ℂ) (z : TT τ Z × (Fin (dd Z) → k)) :
    ∫ u, F (z.1, G τ Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) ∂(Measure.pi fun _ => ν) =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
        GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F (z.1, (G τ Z)⁻¹ *ᵥ z.2) := by
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν (Gu h)
    (fun w => F (z.1, w) * (ψ (((G τ Z)⁻¹ *ᵥ w) ⬝ᵥ z.2) : ℂ))
  have hc : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos).ne'
  have e1 : ∀ u, (Gu h).val *ᵥ u = G τ Z *ᵥ u := fun u => rfl
  have e2 : ∀ u, (G τ Z)⁻¹ *ᵥ (G τ Z *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]
  simp only [e1, e2] at key
  have e3 : ∀ w, ((G τ Z)⁻¹ *ᵥ w) ⬝ᵥ z.2 = w ⬝ᵥ ((G τ Z)⁻¹ *ᵥ z.2) := fun w => by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, G_symm h, dotProduct_comm]
  simp only [e3] at key
  rw [eq_inv_mul_iff_mul_eq₀ hc, key]
  rfl

end PositivityTheory.RgUd.TP.Nil.Four
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Tm (m : ℕ) (t : kˣ) : GL (Fin m) k := Units.map (Matrix.scalar (Fin m) : k →+* Matrix (Fin m) (Fin m) k) t

theorem Tm_mulVec {m : ℕ} (t : kˣ) (u : Fin m → k) : (Tm m t).val *ᵥ u = (t : k) • u := by
  funext i
  simp [Tm, Matrix.scalar_apply, mulVec_diagonal]

theorem Tm_det {m : ℕ} (t : kˣ) : Matrix.GeneralLinearGroup.det (Tm m t) = t ^ m := by
  ext
  simp [Tm, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

variable {τ : Matrix (Fin n) (Fin n) k →ₗ[k] k} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (h : Hyp τ Z)

include h

def phi0 (f : Sp k n → ℂ) : Sp k n → ℂ :=
  fun p => GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (dd Z) => ν) (fun q => f (F1 h q)) (Hb h p)

theorem characteristic_function_integral_apply (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν h f p = ∫ u, f (p.1 - Pr τ Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D τ Z p.1) : ℂ) ∂(Measure.pi fun _ => ν) := by
  simp only [phi0, GlobalTheory.SplitDict.pf, real_test_function_apply]
  rfl

theorem fourier_transform_on_base (f : Sp k n → ℂ) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) (v : Fin n → k) :
    phi0 ψ ν h f (x, v) = ∫ u, f (E Z u, v) * (ψ (u ⬝ᵥ D τ Z x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [characteristic_function_integral_apply]
  simp only [Pr_of_mem h hx, sub_self, zero_add]

theorem test_vector_mem_schwartz_bruhat {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) :
    phi0 ψ ν h f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  have h1 : (fun q => f (F1 h q)) ∈ SB (TT τ Z × (Fin (dd Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 h)).1 hf.1
  have h2 := GlobalTheory.SplitDict.pf_mem_SB (Measure.pi fun _ : Fin (dd Z) => ν) hc h1
  exact ⟨(GlobalTheory.SplitDict.bijOn_comp (Hb h)).1 h2, Set.subset_univ _⟩

theorem integrable_slice (hψ : Continuous ψ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (p : Sp k n) :
    Integrable (fun u => f (p.1 - Pr τ Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D τ Z p.1) : ℂ)) (Measure.pi fun _ => ν) := by
  obtain ⟨⟨hl, hcs⟩, -⟩ := hf
  have hf' : f ∈ SB (Sp k n) := ⟨hl, hcs⟩
  have h1 : (fun q => f (F1 h q)) ∈ SB (TT τ Z × (Fin (dd Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 h)).mapsTo hf'
  have h2 : (fun u : Fin (dd Z) → k => f (p.1 - Pr τ Z p.1 + E Z u, p.2)) ∈ SB (Fin (dd Z) → k) := by
    have := GlobalTheory.SplitDict.slice_mem_SB h1 (Hb h p).1
    convert this using 1
    funext u
    rw [real_test_function_apply]
    rfl
  obtain ⟨hl2, hcs2⟩ := h2
  have hc2 : Continuous fun u : Fin (dd Z) → k => (ψ (u ⬝ᵥ D τ Z p.1) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  exact (hl2.continuous.mul hc2).integrable_of_hasCompactSupport hcs2.mul_right

def phiS (hψ : Continuous ψ) : (supportedIn (Set.univ : Set (Sp k n))) →ₗ[ℂ] (Sp k n → ℂ) where
  toFun f := phi0 ψ ν h f.1
  map_add' f g := by
    funext p
    simp only [Submodule.coe_add, Pi.add_apply, characteristic_function_integral_apply, add_mul]
    exact integral_add (integrable_slice ψ ν h hψ f.2 p) (integrable_slice ψ ν h hψ g.2 p)
  map_smul' c f := by
    funext p
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, characteristic_function_integral_apply, mul_assoc, RingHom.id_apply]
    exact integral_const_mul _ _

theorem fourier_transform_support (f : Sp k n → ℂ) (hf0 : ∀ q ∈ Bz Z ×ˢ (Set.univ : Set (Fin n → k)), f q = 0) {p : Sp k n}
    (hp : p ∈ Bz Z ×ˢ (Set.univ : Set (Fin n → k))) : phi0 ψ ν h f p = 0 := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp.1
  rw [fourier_transform_on_base ψ ν h f hx]
  have h0 : ∀ u, f (E Z u, v) = 0 := fun u => hf0 _ ⟨E_mem Z u, Set.mem_univ _⟩
  simp [h0]

theorem fourier_transform_equivariant {g : GL (Fin n) k} (hg : g ∈ Gz Z) (f : Sp k n → ℂ) {p : Sp k n} (hp : p.1 ∈ Bz Z) :
    phi0 ψ ν h (fun q => f (act g q)) p = phi0 ψ ν h f (act g p) := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp
  obtain ⟨u0, rfl⟩ := exists_E Z hx
  have hy : (g : Matrix (Fin n) (Fin n) k) * E Z u0 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Bz Z := by
    rw [← E_adL hg]
    exact E_mem Z _
  change _ = phi0 ψ ν h f ((g : Matrix (Fin n) (Fin n) k) * E Z u0 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
    (g : Matrix (Fin n) (Fin n) k) *ᵥ v)
  rw [fourier_transform_on_base ψ ν h _ (E_mem Z u0), fourier_transform_on_base ψ ν h f hy]
  have key := GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν (adU h hg)
    (fun u => f (E Z u, (g : Matrix (Fin n) (Fin n) k) *ᵥ v) *
      (ψ (u ⬝ᵥ D τ Z ((g : Matrix (Fin n) (Fin n) k) * E Z u0 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) : ℂ))
  have hn : nabs k (Matrix.GeneralLinearGroup.det (adU h hg)) = 1 := by
    simp [nabs, distribHaarChar_adU h hg]
  rw [hn, inv_one, one_smul] at key
  rw [← key]
  congr 1
  funext u
  have hv : ((adU h hg : GL (Fin (dd Z)) k) : Matrix (Fin (dd Z)) (Fin (dd Z)) k) *ᵥ u = adL hg u := adM_mulVec hg u
  simp only [hv, E_adL hg, dot_conj h hg u (E_mem Z u0)]
  rfl

theorem fourier_transform_preserves_compact {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) :
    phi0 ψ ν h f ∈ supportedIn (UU : Set (Sp k n)) := by
  refine ⟨(test_vector_mem_schwartz_bruhat ψ ν h hc ⟨hf.1, Set.subset_univ _⟩).1, fun p hp => ?_⟩
  by_contra h0
  have h0' : p.2 = 0 := by simpa [UU] using h0
  apply hp
  rw [characteristic_function_integral_apply]
  have : ∀ u, f (p.1 - Pr τ Z p.1 + E Z u, p.2) = 0 := fun u => by
    by_contra hne
    exact (hf.2 hne) h0'
  simp [this]


omit h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
def Refl (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n) : Sp k n :=
  (p.1 - (2 : k) • Pr τ Z p.1, p.2)

omit [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Refl_Refl (p : Sp k n) : Refl τ Z (Refl τ Z p) = p := by
  obtain ⟨x, v⟩ := p
  have hP : Pr τ Z (Pr τ Z x) = Pr τ Z x := Pr_E h _
  have hs : Pr τ Z (x - (2 : k) • Pr τ Z x) = Pr τ Z x - (2 : k) • Pr τ Z (Pr τ Z x) := by
    rw [sub_eq_add_neg, Pr_add, ← neg_smul, Pr_smul, neg_smul, ← sub_eq_add_neg]
  simp only [Refl, Prod.mk.injEq, and_true]
  rw [hs, hP]
  module

theorem fourier_transform_involution {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (p : Sp k n) :
    phi0 ψ ν h (phi0 ψ ν h f) p =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
        ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ (dd Z) : ℝ)) : ℂ) * f (Refl τ Z p) := by
  obtain ⟨⟨hl, hcs⟩, -⟩ := hf
  have hf' : f ∈ SB (Sp k n) := ⟨hl, hcs⟩
  have h1 : (fun q => f (F1 h q)) ∈ SB (TT τ Z × (Fin (dd Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 h)).mapsTo hf'
  have e1 : ∀ q, phi0 ψ ν h f (F1 h q) =
      GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (dd Z) => ν) (fun q => f (F1 h q)) (q.1, G τ Z *ᵥ q.2) := by
    intro q
    simp only [phi0, partial_fourier_first_coordinates]
  have e2 := pf_G h ψ ν (GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (dd Z) => ν) (fun q => f (F1 h q))) (Hb h p)
  have e3 := GlobalTheory.SplitDict.pf_pf (ψ := ψ) ν hc h1 ((Hb h p).1, (G τ Z)⁻¹ *ᵥ (Hb h p).2)
  have e4 : F1 h ((Hb h p).1, -((G τ Z)⁻¹ *ᵥ (Hb h p).2)) = Refl τ Z p := by
    rw [real_test_function_apply]
    show (p.1 - Pr τ Z p.1 + E Z (-((G τ Z)⁻¹ *ᵥ D τ Z p.1)), p.2) = (p.1 - (2 : k) • Pr τ Z p.1, p.2)
    rw [E_neg]
    show (p.1 - Pr τ Z p.1 + -Pr τ Z p.1, p.2) = _
    congr 1
    module
  show GlobalTheory.SplitDict.pf ψ _ (fun q => phi0 ψ ν h f (F1 h q)) (Hb h p) = _
  simp only [e1]
  calc _ = _ := e2
    _ = _ := by
      rw [e3]
      simp only [e4, Fintype.card_fin]
      ring

theorem fourier_transform_homothety (t : kˣ) (f : Sp k n → ℂ) {p : Sp k n} (hp : p.1 ∈ Bz Z) :
    phi0 ψ ν h f (PositivityTheory.RgUd.TP.Nil.hom t p) =
      ((((nabs k t)⁻¹ ^ dd Z : ℝ)) : ℂ) * phi0 ψ ν h (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q)) p := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp
  have htx : (t : k) • x ∈ Bz Z := by
    intro a ha
    rw [mul_smul_comm, smul_mul_assoc, hx a ha]
  change phi0 ψ ν h f ((t : k) • x, v) = _
  rw [fourier_transform_on_base ψ ν h f htx, fourier_transform_on_base ψ ν h _ hx]
  have key := GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν (Tm (dd Z) t)
    (fun u => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ (E Z u, v)) * (ψ (u ⬝ᵥ D τ Z x) : ℂ))
  rw [Tm_det] at key
  simp only [Tm_mulVec] at key
  have hn : nabs k (t ^ dd Z) = nabs k t ^ dd Z := by
    simp [nabs, map_pow]
  have hl : ∀ u : Fin (dd Z) → k, f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ (E Z ((t : k) • u), v)) * (ψ (((t : k) • u) ⬝ᵥ D τ Z x) : ℂ) =
      f (E Z u, v) * (ψ (u ⬝ᵥ D τ Z ((t : k) • x)) : ℂ) := by
    intro u
    simp only [PositivityTheory.RgUd.TP.Nil.hom, E_smul, smul_smul, Units.inv_mul, one_smul, D_smul, smul_dotProduct,
      dotProduct_smul]
  simp only [hl] at key
  rw [key, hn, Complex.real_smul, inv_pow]

theorem fourier_transform_translation_invariant (hZ : CR Z) (f : Sp k n → ℂ) {z : Matrix (Fin n) (Fin n) k} (hz : z ∈ Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) (hzx : τ (z * x) = 0) (v : Fin n → k) :
    phi0 ψ ν h (fun q => f (q.1 + z, q.2)) (x, v) = phi0 ψ ν h f (x, v) := by
  have hzB : z ∈ Bz Z := fun a ha => hZ.1 a ha z hz
  obtain ⟨uz, rfl⟩ := exists_E Z hzB
  rw [fourier_transform_on_base ψ ν h _ hx, fourier_transform_on_base ψ ν h f hx]
  have h0 : uz ⬝ᵥ D τ Z x = 0 := by
    rw [dot_D]
    exact hzx
  have key := MeasureTheory.integral_add_right_eq_self (μ := Measure.pi fun _ : Fin (dd Z) => ν)
    (fun w => f (E Z w, v) * (ψ ((w - uz) ⬝ᵥ D τ Z x) : ℂ)) uz
  simp only [add_sub_cancel_right, sub_dotProduct, h0, sub_zero, E_add] at key
  exact key

end PositivityTheory.RgUd.TP.Nil.Four
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem supp_congr' {C : Set (Sp k n)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Supp ξ C) {f g : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (hg : g ∈ supportedIn (Set.univ : Set (Sp k n)))
    (e : ∀ p ∈ C, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn (Set.univ : Set (Sp k n))).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := PositivityTheory.RgUd.TP.Nil.hom t
  invFun := PositivityTheory.RgUd.TP.Nil.hom t⁻¹
  left_inv p := by
    simp [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  right_inv p := by
    simp [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  continuous_toFun := (continuous_fst.const_smul ((t : kˣ) : k)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.const_smul ((t⁻¹ : kˣ) : k)).prodMk continuous_snd

def trH (z : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 + z, p.2)
  invFun p := (p.1 - z, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.add continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub continuous_const).prodMk continuous_snd

variable (k) in
theorem fourQ : FourQ k := by
  intro hT n Z hZ
  obtain ⟨τ, hs, hnd, hnil⟩ := hT n Z hZ
  have h : Hyp τ Z := ⟨hs, hnd, hnil⟩
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (k := k)
  have hψc : Continuous ψ := (GlobalTheory.T.addChar_conductor_integers_continuous_ne_one k ψ hψ).1
  let ν : Measure k := Measure.addHaar
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (supportedIn (Set.univ : Set (Sp k n)))
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := LinearMap.ofIsCompl hC (phiS ψ ν h hψc) 0
  have hΦ : ∀ f (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))), Φ f = phi0 ψ ν h f := fun f hf =>
    LinearMap.ofIsCompl_left_apply hC (⟨f, hf⟩ : supportedIn (Set.univ : Set (Sp k n)))
  have h1 : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => by rw [hΦ f hf]; exact test_vector_mem_schwartz_bruhat ψ ν h hψ hf
  set K : ℂ := ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
    ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ (dd Z) : ℝ)) : ℂ) with hKdef
  have hK : K ≠ 0 := by
    have h1 : 0 < ν.real (𝒪[k] : Set k) :=
      ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero ν ⟨0, zero_mem _⟩) (isCompact_int k).measure_lt_top.ne
    have h2 : 0 < nabs k 1 := by
      show (0 : ℝ) < ((distribHaarChar k 1 : NNReal) : ℝ)
      exact_mod_cast distribHaarChar_pos
    have h3 : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (distribHaarChar_pos).ne'
    refine mul_ne_zero (inv_ne_zero h3) ?_
    exact_mod_cast (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := K⁻¹ • (Φ ∘ₗ LinearMap.funLeft ℂ ℂ (Refl τ Z))
  have hR : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), (fun q => f (Refl τ Z q)) ∈
      supportedIn (Set.univ : Set (Sp k n)) := fun f hf => by
    have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf
      { toFun := Refl τ Z, invFun := Refl τ Z, left_inv := Refl_Refl h, right_inv := Refl_Refl h,
        continuous_toFun := (continuous_fst.sub (((continuous_Pr τ Z).comp continuous_fst).const_smul (2 : k))).prodMk
          continuous_snd
        continuous_invFun := (continuous_fst.sub (((continuous_Pr τ Z).comp continuous_fst).const_smul (2 : k))).prodMk
          continuous_snd : Sp k n ≃ₜ Sp k n }
    exact this
  have hRU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), (fun q => f (Refl τ Z q)) ∈ supportedIn (UU : Set (Sp k n)) :=
    fun f hf => ⟨(hR f ⟨hf.1, Set.subset_univ _⟩).1, fun q hq => by
      have := hf.2 (show Refl τ Z q ∈ Function.support f from hq)
      exact this⟩
  have h1' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ' f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
    intro f hf
    show K⁻¹ • Φ (fun q => f (Refl τ Z q)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    exact h1 _ (hR f hf)
  have hU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ f ∈ supportedIn (UU : Set (Sp k n)) := by
    intro f hf
    rw [hΦ f ⟨hf.1, Set.subset_univ _⟩]
    exact fourier_transform_preserves_compact ψ ν h hψ hf
  have hU' : ∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ' f ∈ supportedIn (UU : Set (Sp k n)) := by
    intro f hf
    show K⁻¹ • Φ (fun q => f (Refl τ Z q)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    exact hU _ (hRU f hf)
  have hinv : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ p, Φ (Φ' f) p = f p := by
    intro f hf p
    show Φ (K⁻¹ • Φ (fun q => f (Refl τ Z q))) p = f p
    rw [map_smul, hΦ _ (hR f hf), hΦ _ (test_vector_mem_schwartz_bruhat ψ ν h hψ (hR f hf)), Pi.smul_apply,
      fourier_transform_involution ψ ν h hψ (hR f hf), Refl_Refl h, ← hKdef, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK,
      one_mul]
  have cs : ∀ (s : kˣ) (g : Sp k n → ℂ), g ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun q => g (PositivityTheory.RgUd.TP.Nil.hom s q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := fun s g hg => by
    have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hg (homH s)
    exact this
  let 𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨𝓕, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf h0
    refine hξ _ (h1 f hf) fun p hp => ?_
    rw [hΦ f hf]
    exact fourier_transform_support ψ ν h f h0 hp
  · intro ξ hξ hi g hg f hf
    have ca : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g)
      exact this
    have ca' : (fun q => Φ f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem (h1 f hf) (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g)
      exact this
    show ξ (Φ fun q => f (act g q)) = ξ (Φ f)
    refine (supp_congr' hξ (h1 _ ca) ca' fun p hp => ?_).trans (hi g hg _ (h1 f hf))
    rw [hΦ _ ca, hΦ f hf]
    exact fourier_transform_equivariant ψ ν h hg f hp.1
  · intro ξ hξ
    constructor
    · intro hk f hf
      exact hk _ (hU f hf)
    · intro hk f hf
      have hf' : f ∈ supportedIn (Set.univ : Set (Sp k n)) := supportedIn_mono (Set.subset_univ _) hf
      rw [← supp_congr' hξ (h1 _ (h1' f hf')) hf' fun p _ => hinv f hf' p]
      exact hk _ (hU' f hf)
  · intro ξ h0 f hf
    exact h0 _ (h1 f hf)
  · intro t ξ hξ f hf
    have hc1 := cs t _ (h1 f hf)
    have hc2 : ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) • Φ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q)) ∈
        supportedIn (Set.univ : Set (Sp k n)) :=
      (supportedIn Set.univ).smul_mem _ (h1 _ (cs t⁻¹ f hf))
    have e := supp_congr' hξ hc1 hc2 fun p hp => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hΦ f hf, hΦ _ (cs t⁻¹ f hf), fourier_transform_homothety ψ ν h t f hp.1, dd_eq]
    change ξ (fun q => Φ f (PositivityTheory.RgUd.TP.Nil.hom t q)) = _ * ξ (Φ fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q))
    rw [e, map_smul, smul_eq_mul]
  · intro ξ hξ z hz f hf
    have ct : (fun p : Sp k n => f (p.1 + z, p.2)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf (trH z)
      exact this
    show ξ (Φ fun p => f (p.1 + z, p.2)) = ξ (Φ f)
    refine supp_congr' hξ (h1 _ ct) (h1 f hf) fun p hp => ?_
    obtain ⟨x, v⟩ := p
    obtain ⟨⟨hxB, hxn⟩, -⟩ := hp
    rw [hΦ _ ct, hΦ f hf]
    refine fourier_transform_translation_invariant ψ ν h hZ f hz hxB ?_ v
    exact h.nil _ ⟨mul_mem_Bz Z (PositivityTheory.RgUd.T.Nil.Four.Phi2.Z_le_Bz Z hZ hz) hxB,
      Commute.isNilpotent_mul_left (hxB z hz) hxn⟩

end PositivityTheory.RgUd.TP.Nil.Four
