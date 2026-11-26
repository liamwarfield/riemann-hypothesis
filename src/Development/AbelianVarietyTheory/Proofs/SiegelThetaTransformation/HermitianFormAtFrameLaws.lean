module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplecticStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem form_eq_zero_of_im {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → V → ℂ)
    (h1 : ∀ w, IsLinearMap ℂ (fun z => f z w)) (h2 : ∀ z, IsLinearMap ℝ (f z)) (S : Set V)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ u ∈ S, ∀ v ∈ S, (f u v).im = 0) (z w : V) : f z w = 0 := by
  have key : ∀ z w, (f z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem u hu =>
      induction hw using Submodule.span_induction with
      | mem v hv => exact h u hu v hv
      | zero => rw [(h2 u).map_zero, zero_im]
      | add a b _ _ ha hb => rw [(h2 u).map_add (f := _), add_im, ha, hb, add_zero]
      | smul t a _ ha => rw [(h2 u).map_smul, smul_im, ha, smul_zero]
    | zero => rw [(h1 w).map_zero, zero_im]
    | add a b _ _ ha hb => rw [(h1 w).map_add (f := _), add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [← Complex.coe_smul, (h1 w).map_smul, smul_eq_mul, im_ofReal_mul, ha, mul_zero]
  have h3 := key (I • z) w
  rw [(h1 w).map_smul, smul_eq_mul, I_mul_im] at h3
  exact Complex.ext h3 (key z w)

theorem hermForm_eq_of_im {g : ℕ} (M M' : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ u ∈ S, ∀ v ∈ S, (hermForm M (a * u) v).im = (hermForm M' u (b * v)).im) (z w : Fin g → ℂ) :
    hermForm M (a * z) w = hermForm M' z (b * w) := by
  refine sub_eq_zero.1 (form_eq_zero_of_im (fun z w => hermForm M (a * z) w - hermForm M' z (b * w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) S hS
    (fun u hu v hv => by rw [sub_im, h u hu v hv, sub_self]) z w)
  · simp only [hermForm, mul_add, add_dotProduct]; ring
  · simp only [hermForm, mul_smul_comm, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hermForm, mul_add, star_add, mulVec_add, dotProduct_add]; ring
  · simp only [hermForm, mul_smul_comm, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_eq_hermForm (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hx X bas idx x z w = hermForm (ThFr.Hm X bas idx x) z w := (hermForm_Hm bas idx x z w).symm

theorem span_range_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range (pv X idx x)) = ⊤ := by
  have col (s : Fin g → Fin g ⊕ Fin g) (t : Fin g → ℝ) :
      perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) ∈ Submodule.span ℝ (Set.range (pv X idx x)) := by
    have : perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) =
        ∑ k, t k • pv X idx x (bas (Pi.single (s k) 1)) := by
      funext i
      simp [mulVec, dotProduct, pv, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine eq_top_iff.2 fun z _ => ?_
  have hu := isUnit_det_perMat idx hs hx
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  set τ := tauMat X bas idx x with hτ
  set y := hMat X bas idx x *ᵥ z with hy
  obtain ⟨t, ht⟩ : ∃ t : Fin g → ℝ, τ.map Complex.im *ᵥ t = fun k => (y k).im :=
    ⟨(τ.map Complex.im)⁻¹ *ᵥ _, by rw [mulVec_mulVec, mul_nonsing_inv _ hY, one_mulVec]⟩
  have h1 : y = (fun k => (((y - τ *ᵥ fun k => (t k : ℂ)) k).re : ℂ)) + τ *ᵥ fun k => (t k : ℂ) := by
    funext k
    apply Complex.ext
    · simp
    · have := congrFun ht k
      simp only [mulVec, dotProduct, map_apply] at this
      simp [mulVec, dotProduct, this]
  have hAB : perMat X bas idx Sum.inl x * τ = perMat X bas idx Sum.inr x :=
    mul_nonsing_inv_cancel_left _ _ hu
  have h2 : z = perMat X bas idx Sum.inl x *ᵥ y := by
    rw [hy, mulVec_mulVec, hMat, mul_nonsing_inv _ hu, one_mulVec]
  rw [h2, h1, mulVec_add, mulVec_mulVec, hAB]
  exact add_mem (col _ _) (col _ _)

theorem span_image_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L : Lt E r)
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ := by
  rw [eq_top_iff, ← span_range_pv idx hs hx, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem L hL v
  have : pv X idx x v = (k : ℝ)⁻¹ • pv X idx x (k • v) := by
    funext i
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [pv, pv, per_zsmul]
    simp only [Function.comp_apply, Pi.smul_apply, zsmul_eq_mul, real_smul, ofReal_inv, Pi.mul_apply, Pi.intCast_apply,
      ofReal_intCast]
    rw [inv_mul_cancel_left₀ hk']
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hv, rfl⟩)

theorem pv_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) :
    pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
  funext fun _ => per_smul X x a v _

theorem EF_smul_left (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) := by
  have h (b : E) : IsCMField.complexConj E (IsCMField.complexConj E a * b) = a * IsCMField.complexConj E b := by
    rw [map_mul, IsCMField.complexConj_apply_apply]
  simp only [EF_def, herm, cc, Pi.smul_apply, smul_eq_mul, h]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hx_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  intro E _ _ _ r X g bas idx n hs _ x hx
  have him {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v) :
      (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    im_hermForm_Hm idx hs hx u v
  simp only [hx_eq_hermForm]
  refine ⟨fun z w => ?_, fun z hz => hermForm_Hm_pos idx hs hx hz, him hx, fun a z w => ?_,
    pv_smul idx x, fun u v h => ?_, fun L hL => ⟨span_image_pv idx hs hx L hL, fun M _ h z w => ?_⟩,
    fun ga hga => ⟨hga.lact_mem hx, fun v => ?_, fun h τ i => ?_, fun z w => ?_⟩⟩
  · have hH := Hm_isHermitian idx hs hx
    rw [hermForm, hermForm, ← RCLike.star_def, ← star_dotProduct_star, star_mulVec, star_star, hH.eq,
      dotProduct_mulVec]
  · refine hermForm_eq_of_im _ _ (fun j => rowType X (idx j) a) (fun j => rowType X (idx j) (cc a)) _
      (span_range_pv idx hs hx) ?_ z w
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have h1 := him hx (a • u) v
    have h2 := him hx u (cc a • v)
    rw [pv_smul] at h1 h2
    rw [EF_smul_left] at h1
    exact h1.trans h2.symm
  · obtain ⟨m, rfl⟩ := vecQ_surjective X bas u
    obtain ⟨m', rfl⟩ := vecQ_surjective X bas v
    have h' (t) : EF X (vecQ X bas m) (vecQ X bas t) = EF X (vecQ X bas m') (vecQ X bas t) := by
      have := (him hx (vecQ X bas m) (vecQ X bas t)).symm.trans (h ▸ him hx (vecQ X bas m') (vecQ X bas t))
      exact_mod_cast this
    simp only [EF_vecQ hs] at h'
    congr 1
    funext j
    rcases j with j | j
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)
  · have := hermForm_eq_of_im M (ThFr.Hm X bas idx x) 1 1 _ (span_image_pv idx hs hx L hL) (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [_root_.one_mul, _root_.one_mul, h u hu v hv, him hx]) z w
    rwa [_root_.one_mul, _root_.one_mul] at this
  · rw [pv, per_lact x hga, pv]
  · have e1 : mat (lact ga x) τ = (ga : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have e2 : FD.gram τ.1 X.Gm (mat (lact ga x) τ) = FD.gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hga]
    have h' := h τ i
    unfold dmin at h' ⊢
    rwa [e2]
  · have := hermForm_eq_of_im (ThFr.Hm X bas idx (lact ga x)) (ThFr.Hm X bas idx x) 1 1 _
      (span_range_pv idx hs hx) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      have h1 := him (hga.lact_mem hx) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v)
      rw [pv, pv, per_lact x hga, per_lact x hga, EF_def, hga, ← EF_def] at h1
      rw [_root_.one_mul, _root_.one_mul, him hx]
      exact h1) z w
    rwa [_root_.one_mul, _root_.one_mul] at this

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLawsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFormAtFrame_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  first | exact @GlobalTheory.Dict.hx_laws | exact GlobalTheory.Dict.hx_laws | (intros; apply GlobalTheory.Dict.hx_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Letters

theorem rename_place_mem {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ}
    (hP : P ∈ Harm.rowHighest R c c') :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' := by
  obtain ⟨h₁, h₂, h₃⟩ := Harm.mem_rowHighest_iff_rowAdd.1 hP
  set F := f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ)) with hF
  have hFa (t : T) (v : (Fin p ⊕ Fin q) × κ) : F (t, v) = (f t, v) := rfl
  refine Harm.mem_rowHighest_iff_rowAdd.2 ⟨fun t a b => ?_, fun t ρ => ?_, fun t ρ ρ' hρ s => ?_⟩ <;>
    obtain ⟨t, rfl⟩ := f.surjective t
  · have := congrArg (MvPolynomial.rename F) (h₁ t a b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, Harm.laplacian_apply, map_sum] at this
    rw [Harm.laplacian_apply, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Harm.xVar, Harm.yVar, ← hFa, ← hFa, MvPolynomial.pderiv_rename F.injective,
      MvPolynomial.pderiv_rename F.injective]
  · rw [Harm.isWeightedHomogeneous_rename_iff F.injective, h, h']
    convert h₂ t ρ using 1
    funext ⟨t', ρ', k⟩
    simp [hFa, Harm.rowInd_apply]
  · conv_rhs => rw [← h₃ t ρ ρ' hρ s]
    refine DFunLike.congr_fun (?_ : (Harm.rowAdd (f t) ρ ρ' (s : R)).comp (MvPolynomial.rename F) =
      (MvPolynomial.rename F).comp (Harm.rowAdd t ρ ρ' (s : R))) P
    refine MvPolynomial.algHom_ext fun ⟨t', ρ'', k⟩ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, hFa, Harm.rowAdd_X, Harm.rowAdd_X]
    simp only [f.injective.eq_iff]
    split_ifs <;> simp [hFa]

theorem rename_place_mem_iff {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ} :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' ↔
      P ∈ Harm.rowHighest R c c' := by
  refine ⟨fun hP => ?_, rename_place_mem f h h'⟩
  have := rename_place_mem f.symm (d := c) (d' := c') (fun t => by rw [← h, f.apply_symm_apply])
    (fun t => by rw [← h', f.apply_symm_apply]) hP
  rw [MvPolynomial.rename_rename] at this
  convert this
  rw [show (f.symm.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) ∘
    (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) = id from
      (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))).symm_comp_self, MvPolynomial.rename_id_apply]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem exists_isSympl (X : Data E r) (hL : SelfD X X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) :
    ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ, IsSympl X bas := by
  obtain ⟨h1, h2, h3⟩ := ThetaHol.finrank_lattice X
  have hg : g = X.Ψ.card * r := by simpa using Fintype.card_congr idx
  have hκ : X.κ0 / 2 ≠ 0 := by rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  have hlat : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  obtain ⟨B, hB⟩ : ∃ B : LinearMap.BilinForm ℚ (Fin r → E), ∀ u v, EF X u v = B u v :=
    ⟨_, TensLat.EF_eq_bilin X⟩
  choose k hk using fun u v : X.Λ => (hL.2 u).1 u.2 v v.2
  have hk' (u v : X.Λ) : (k u v : ℚ) = B u v := (hk u v).symm.trans (hB _ _)
  let β : LinearMap.BilinForm ℤ X.Λ := LinearMap.mk₂ ℤ k
    (fun x x' y => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
    (fun x y y' => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
  have hβ (u v : X.Λ) : (β u v : ℚ) = EF X u v := (hk u v).symm
  have halt : β.IsAlt := fun x => by
    have := TensLat.EF_swap X x x
    apply Int.cast_injective (α := ℚ)
    rw [hβ, Int.cast_zero]
    linarith
  have hbij : Function.Bijective β := by
    constructor
    · intro x x' h
      refine Subtype.ext (eq_of_EFf_eq hκ X.Gm_det hlat fun y hy => ?_)
      exact (hβ x ⟨y, hy⟩).symm.trans (h ▸ hβ x' ⟨y, hy⟩)
    · intro φ
      obtain ⟨x, hx, hφ⟩ := exists_traceFormDual_eq hκ X.Gm_det hlat φ.toAddMonoidHom
      refine ⟨⟨x, (hL.2 x).2 hx⟩, LinearMap.ext fun y => Int.cast_injective (α := ℚ) ?_⟩
      exact (hβ _ _).trans (hφ y).symm
  obtain ⟨g', bas, S, hs, -, hr⟩ := exists_symplectic_coordinates_adapted halt hbij (I := ⊥)
    (fun m x hm hx => by simpa [hm] using hx) (by simp) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  exact ⟨bas, fun a b => by rw [← hβ, hs]; simp⟩

end GlobalTheory.Dict.Letters


open GlobalTheory.Dict.Letters GlobalTheory.Harm in
theorem GlobalTheory.Dict.exists_dic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  intro E _ _ _ H Dw l c σ r g n X a e hσ hr hp0 hΨ hL hD
  obtain ⟨hbij, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hr' : X.p0 + Dw.p = r := by omega
  have i1 := ComplexEmbedding.involutive_conjugate E
  have i2 : ∀ τ, ¬ InPsi H τ ↔ InPsi H (ComplexEmbedding.conjugate τ) := not_mem_hostType_iff H
  have i3 : ∀ τ, InPsi H τ → Dw.mult τ = Dw.p := fun _ => mult_of_mem Dw
  have i4 : ∀ τ, InPsi H τ → Dw.mult (ComplexEmbedding.conjugate τ) = X.p0 := fun _ h =>
    (mult_conjEmb_of_mem Dw h).trans hp0.symm
  let f : {τ // InPsi H τ} ≃ X.Ψ := (Equiv.ofBijective _ hbij).subtypeEquiv fun τ =>
    ((hΨ _).trans (hrt τ)).symm
  have hf (t : {τ // InPsi H τ}) : (f t).1 = relab c σ t.1 := rfl
  let ρ : Lt1 Dw ≃ X.Ψ × (Fin Dw.p ⊕ Fin X.p0) :=
    (halfRowEquiv i1 i2 i3 i4).trans (f.prodCongr (Equiv.refl _))
  let idx : Fin g ≃ X.Ψ × Fin r := e.trans (ρ.trans (rowOf X hr'))
  have hidx (j) : (∃ t : {τ // InPsi H τ}, ∃ i : Fin Dw.p, (e j).1 = t.1 ∧ ((e j).2 : ℕ) = i ∧
      idx j = (f t, rowIdx hr' (Sum.inl i))) ∨
      ∃ t : {τ // InPsi H τ}, ∃ i : Fin X.p0, (e j).1 = ComplexEmbedding.conjugate t.1 ∧ ((e j).2 : ℕ) = i ∧
        idx j = (f t, rowIdx hr' (Sum.inr i)) := by
    obtain ⟨⟨t, i | i⟩, h⟩ := (halfRowEquiv i1 i2 i3 i4).symm.surjective (e j)
    · refine Or.inl ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
    · refine Or.inr ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
  obtain ⟨bas, hbas⟩ := exists_isSympl X hL idx
  let k₀ : {τ // InPsi H τ} → Fin Dw.p → ℕ := fun t => diffOf fun i => a (t.1, i)
  let k₀' : {τ // InPsi H τ} → Fin X.p0 → ℕ := fun t => diffOf fun i => a (ComplexEmbedding.conjugate t.1, i)
  have hx (t) : partOf (k₀ t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  have hy (t) : partOf (k₀' t) = fun i : Fin X.p0 => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  let eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n) :=
    (typeLetterEquiv i1 i2 i3 i4 n).trans (f.prodCongr (Equiv.refl _))
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        MvPolynomial.rename eL P ∈ rowHighest c.F (k₀ ∘ f.symm) (k₀' ∘ f.symm) := by
    rw [Equiv.coe_trans, ← MvPolynomial.rename_rename,
      rename_place_mem_iff f (c := k₀) (c' := k₀') (fun t => by simp) (fun t => by simp)]
    simp only [mem_HHa_iff_rename i1 i2 i3 i4, mem_rowHighest_iff_rowAdd, hx, hy]
  have hinv (τ) : Function.invFun (relab c σ) (relab c σ τ) = τ := Function.leftInverse_invFun hbij.1 τ
  refine ⟨⟨hr', bas, idx, hbas, e, eL, k₀ ∘ f.symm, k₀' ∘ f.symm, fun x v j => ?_, fun j => ?_,
    fun ℓ => ?_, ?_, fun P hP => ?_, ?_⟩, rfl, fun hpos hp => ?_⟩
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · have hi := i.isLt
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_le _ _ _ _ (by simp), perFr,
        dite_eq_left (show relab c σ t.1 ∈ X.Ψ from (f t).2), dite_eq_left (by omega)]
      rfl
    · have hi := i.isLt
      have h4 : relab c σ (ComplexEmbedding.conjugate t.1) = ComplexEmbedding.conjugate (f t).1 := hcj t.1
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_lt _ _ _ _ (by rw [rowIdx_inr]; omega), h4]
      have h5 : rowIdx hr' (Sum.inr i) = ⟨X.p0 - 1 - i, by omega⟩ := Fin.ext (rowIdx_inr hr' i)
      rw [h5]
      generalize f t = u
      obtain ⟨τ, hτ⟩ := u
      obtain ⟨τ, rfl⟩ := i1.surjective τ
      rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from i1 τ, perFr,
        dite_eq_right (fun h => (X.cmType τ).1 h hτ), dite_eq_left (show conjEmb τ ∈ X.Ψ from hτ), dite_eq_left (by omega)]
      rfl
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · rw [h3, h1]
      exact rowType_rowOf_inl X hr' (f t) i
    · rw [h3, h1]
      exact (rowType_rowOf_inr X hr' (f t) i).trans (hcj t.1).symm
  · have : idx.symm (rowOf X hr' ((eL ℓ).1, (eL ℓ).2.1)) = e.symm ⟨ℓ.1, ℓ.2.1⟩ := by
      rw [Equiv.symm_apply_eq]
      simp only [idx, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    rw [letterDir, this]
    rfl
  · funext τ j
    obtain ⟨t, rfl⟩ := f.surjective τ
    obtain ⟨i | i, rfl⟩ := (rowIdx hr').surjective j
    · rw [wtOf_inl, wtX, if_pos (by simp), hf, hinv, Function.comp_apply, f.symm_apply_apply, hx]
      simp
    · have hi := i.isLt
      rw [wtOf_inr, wtX, if_neg (by rw [rowIdx_inr]; omega), hf, ← hcj, hinv, Function.comp_apply,
        f.symm_apply_apply, hy, rowIdx_inr, show X.p0 - 1 - (X.p0 - 1 - i) = i by omega]
      rfl
  · rw [← MvPolynomial.map_rename]
    exact map_mem_rowHighest _ ((hmem P).1 hP)
  · letI := σ.toAlgebra
    rw [← span_map_rowHighest c.F ℂ]
    refine Submodule.span_mono ?_
    rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨P, rfl⟩ := MvPolynomial.rename_surjective _ eL.surjective Q
    exact ⟨P, (hmem P).2 hQ, (MvPolynomial.map_rename _ _ _).symm⟩
  · obtain ⟨t⟩ : Nonempty {τ // InPsi H τ} := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : InPsi H τ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, (i2 τ).1 h⟩⟩
    refine ⟨f t, ⟨Dw.p - 1, by omega⟩, by simp only; omega, ?_⟩
    have := hpos t.1 t.2 (by rw [i3 _ t.2]; exact hp)
    rw [i3 _ t.2] at this
    simp only [Function.comp_apply, Equiv.symm_apply_apply, k₀, diffOf]
    rw [dite_eq_right (by omega)]
    exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_letterRowWeightDictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  first | exact @GlobalTheory.Dict.exists_dic | exact GlobalTheory.Dict.exists_dic | (intros; apply GlobalTheory.Dict.exists_dic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.UnAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem exists_mem_dom (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show FD.gram τ.1 X.Gm (mat (fun τ => P τ) τ) = FD.gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0


omit [NumberField E] [IsCMField E] in
theorem lact_one' {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]


omit [NumberField E] [IsCMField E] in
theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

theorem isUn_mul {γ' γ : GL (Fin r) E} (h' : IsUn X γ') (h : IsUn X γ) : IsUn X (γ' * γ) := by
  intro u v
  rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, h', h]

theorem tauMat_mem (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    tauMat X bas idx x ∈ Siegel (Fin g) :=
  ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩

theorem eq_of_thA_eq (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) (h : thA X bas idx φ x = thA X bas idx ψ x) : φ = ψ := by
  refine eq_of_thS_eq _ _ φ ψ hφ hψ _ (tauMat_mem idx hs hx) fun ζ => ?_
  have h1 := congrFun h fun k => perMat X bas idx Sum.inl x *ᵥ ζ k
  simp only [thA, mulVec_mulVec, hMat_mul_perMat idx hs hx, one_mulVec] at h1
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (isUnit_det_hMat idx hs hx).ne_zero)
    (Complex.exp_ne_zero _)) h1

theorem thA_add (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) :
    thA X bas idx (φ + ψ) x = thA X bas idx φ x + thA X bas idx ψ x := by
  funext z
  have h1 := (SiegelSum.summable_norm_thetaTerm _ _ φ hφ _ (tauMat_mem idx hs hx)
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  have h2 := (SiegelSum.summable_norm_thetaTerm _ _ ψ hψ _ (tauMat_mem idx hs hx)
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  simp only [thA, thS, Pi.add_apply, add_mul]
  rw [h1.tsum_add h2, mul_add]

theorem thA_smul (x : Frame X.Ψ r) (a : ℂ) (φ : TF n g) :
    thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
  funext z
  simp only [thA, thS, Pi.smul_apply, smul_eq_mul, mul_assoc a, tsum_mul_left]
  ring

theorem exists_weil (hs : IsSympl X bas) (hn : Even n) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    ∃ ω : TF n g → TF n g, ∀ φ, IsSB φ → IsSB (ω φ) ∧
      (∀ x ∈ X.dom, thA X bas idx (ω φ) (lact γ x) = thA X bas idx φ x) ∧
      ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨σ, hσ, h⟩ := periods_lact_symplectic E r X g bas idx n hs hn γ hγ
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (Fin g) σ (by simpa using hn) hσ
  refine ⟨ω, fun φ hφ => ⟨(hω φ hφ).1, fun x hx => ?_, (hω φ hφ).2.2⟩⟩
  obtain ⟨-, hτ, h1, h2⟩ := h x hx
  funext z
  have h3 := (hω φ hφ).2.1 _ hτ fun k => hMat X bas idx x *ᵥ z k
  have h4 := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
    GlobalTheory.T.canonicalThetaExponent_symplectic_invariant _ σ hσ _ hτ (hMat X bas idx x *ᵥ z k)
  have hd := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle _ σ hσ _ hτ).1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h4
  have h5 (k) : hMat X bas idx (lact γ x) *ᵥ z k =
      (hMat X bas idx x *ᵥ z k) ᵥ* (spDen σ (tauMat X bas idx x))⁻¹ := by
    rw [h2, ← mulVec_mulVec, mulVec_transpose]
  have h6 : (hMat X bas idx (lact γ x)).det =
      (spDen σ (tauMat X bas idx x)).det⁻¹ * (hMat X bas idx x).det := by
    rw [h2, det_mul, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv']
  simp only [thA, h5, imInv_eq, h1, h6]
  rw [h3, ← h4, Fintype.card_fin, mul_add, Complex.exp_add, mul_pow, inv_pow]
  have h7 := pow_ne_zero (n / 2) hd
  rw [show ∀ t : ℂ, (π : ℂ) / 2 * (2 * I * t) = π * I * t from fun t => by ring]
  field_simp

theorem wG_eq (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) {φ ψ : TF n g}
    (hψ : IsSB ψ) (h : ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x) :
    wG X bas idx γ φ = ψ := by
  have he : ∃ ψ : TF n g, IsSB ψ ∧ ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x :=
    ⟨ψ, hψ, h⟩
  obtain ⟨x, hx⟩ := exists_mem_dom X
  rw [wG, dite_eq_left he]
  exact eq_of_thA_eq idx hs (hγ.lact_mem hx) he.choose_spec.1 hψ
    ((he.choose_spec.2 x hx).trans (h x hx).symm)

theorem herm_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (u v : Fin g → ℂ) :
    (hMat X bas idx (lact γ x) *ᵥ u) ⬝ᵥ imInv X bas idx (lact γ x) *ᵥ
        star (hMat X bas idx (lact γ x) *ᵥ v) =
      (hMat X bas idx x *ᵥ u) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ v) := by
  obtain ⟨σ, hσ, h⟩ := periods_lact_symplectic E r X g bas idx 0 hs Even.zero γ hγ
  obtain ⟨hx', hτ, h1, h2⟩ := h x hx
  obtain ⟨hd, -, -, h3, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle _ σ hσ _ hτ
  have h4 : imInv X bas idx x = (spDen σ (tauMat X bas idx x))⁻¹ * imInv X bas idx (lact γ x) *
      ((spDen σ (tauMat X bas idx x))⁻¹)ᴴ := by
    rw [← (imInv_isSymm idx hs hx).eq, ← (imInv_isSymm idx hs hx').eq, imInv_eq, imInv_eq, ← h3, h1,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, transpose_mul, transpose_mul,
      ← transpose_nonsing_inv (spDen _ _), transpose_transpose, conjTranspose_nonsing_inv,
      transpose_nonsing_inv (Matrix.map (spDen _ _) _)]
    rfl
  rw [h4, h2, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, mulVec_transpose, star_vecMul,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (spDen _ _)⁻¹]

end GlobalTheory.SW.UnAct

namespace GlobalTheory.SW

open UnAct

theorem wG_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧ (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧ (∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ ∧ wG X bas idx γ (φ + ψ) = wG X bas idx γ φ + wG X bas idx γ ψ ∧ ∀ x ∈ X.dom, thA X bas idx φ x = thA X bas idx ψ x → φ = ψ) ∧ (∀ a : ℂ, wG X bas idx γ (a • φ) = a • wG X bas idx γ φ) ∧ wG X bas idx 1 φ = φ ∧ (∀ γ', IsUn X γ' → wG X bas idx (γ' * γ) φ = wG X bas idx γ' (wG X bas idx γ φ)) ∧ ∀ y : Matrix (Fin n) (Fin r) E, wG X bas idx γ (heisG X bas y φ) = heisG X bas (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ φ) := by
  intro E _ _ _ r X g bas idx n hs hn
  have key : ∀ γ, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧
      (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧
      ∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ := by
    intro γ hγ φ hφ
    obtain ⟨ω, hω⟩ := exists_weil idx hs hn hγ
    have e : ∀ ψ, IsSB ψ → wG X bas idx γ ψ = ω ψ := fun ψ hψ =>
      wG_eq idx hs hγ (hω ψ hψ).1 (hω ψ hψ).2.1
    rw [e φ hφ]
    exact ⟨(hω φ hφ).1, (hω φ hφ).2.1, fun ψ hψ => by rw [e ψ hψ]; exact (hω φ hφ).2.2 ψ hψ⟩
  intro γ hγ φ hφ
  obtain ⟨k1, k2, k3⟩ := key γ hγ φ hφ
  refine ⟨k1, k2, fun ψ hψ => ⟨k3 ψ hψ, ?_, fun x hx => eq_of_thA_eq idx hs hx hφ hψ⟩,
    fun a => ?_, ?_, fun γ' hγ' => ?_, fun y => ?_⟩
  · obtain ⟨l1, l2, -⟩ := key γ hγ ψ hψ
    refine wG_eq idx hs hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ k1 l1).1 fun x hx => ?_
    rw [thA_add idx hs (hγ.lact_mem hx) k1 l1, thA_add idx hs hx hφ hψ, k2 x hx, l2 x hx]
  · refine wG_eq idx hs hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ k1 k1).2.1 a) fun x hx => ?_
    rw [thA_smul, thA_smul, k2 x hx]
  · exact wG_eq idx hs (fun u v => by simp) hφ fun x _ => by rw [lact_one']
  · obtain ⟨l1, l2, -⟩ := key γ' hγ' _ k1
    refine wG_eq idx hs (isUn_mul hγ' hγ) l1 fun x hx => ?_
    rw [lact_mul', l2 _ (hγ.lact_mem hx), k2 x hx]
  · obtain ⟨-, -, -, hH⟩ := heisG_laws E r X g bas idx n hs hn
    refine wG_eq idx hs hγ (hH _ _ k1).1 fun x hx => ?_
    funext z
    have hy (k) : per X (lact γ x) ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) = per X x (y k) := by
      rw [← per_lact x hγ]
      congr 1
      ext j
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [(hH _ _ k1).2.2.2.2 _ (hγ.lact_mem hx), (hH _ _ hφ).2.2.2.2 _ hx, k2 x hx]
    simp only [hy, herm_lact idx hs hγ hx]

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProductStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_preserves_theta_and_inner_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧ (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧ (∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ ∧ wG X bas idx γ (φ + ψ) = wG X bas idx γ φ + wG X bas idx γ ψ ∧ ∀ x ∈ X.dom, thA X bas idx φ x = thA X bas idx ψ x → φ = ψ) ∧ (∀ a : ℂ, wG X bas idx γ (a • φ) = a • wG X bas idx γ φ) ∧ wG X bas idx 1 φ = φ ∧ (∀ γ', IsUn X γ' → wG X bas idx (γ' * γ) φ = wG X bas idx γ' (wG X bas idx γ φ)) ∧ ∀ y : Matrix (Fin n) (Fin r) E, wG X bas idx γ (heisG X bas y φ) = heisG X bas (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ φ) := by
  first | exact @GlobalTheory.SW.wG_laws | exact GlobalTheory.SW.wG_laws | (intros; apply GlobalTheory.SW.wG_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GenLatCmp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_std (v : Fin n → E) : v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff (v i)

theorem std_eq : Formalism.L2.Pj.stdLat E n = stdL E n := by
  apply le_antisymm
  · intro v hv
    rw [mem_std] at hv
    have : v = ∑ i, (⟨v i, hv i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_std]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

theorem span_smul_le (k : ℕ) (A B : Lt E n) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (k : E) • v ∈ B := by
  have e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← e]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [e]; exact h v hv

theorem natCast_smul_mem (k : ℕ) {A : Lt E n} {v : Fin n → E} (hv : v ∈ A) : (k : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.toAddSubgroup.nsmul_mem hv k

theorem fg_of_smul_le {Λ : Lt E n} {s : ℕ} (hs : 0 < s) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ.FG := by
  have h0 : (stdL E n).FG := Submodule.fg_span (Set.finite_range _)
  have h1 := h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))
  refine h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩
  have : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  simp [smul_smul, this]

variable [IsCMField E]

theorem herm_one_eq (x y : Fin n → E) :
    herm 1 x y = cc (∑ j, IsCMField.complexConj E (x j) * y j) := by
  simp [herm, cc, Matrix.one_apply]

theorem unimod_iff (Λ : Lt E n) : (⟨Λ⟩ : GenLat E n).Unimod ↔
    ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  rw [mem_range_iff, herm_one_eq]
  refine ⟨Base.isIntegral_cc, fun h => ?_⟩
  simpa [cc] using Base.isIntegral_cc h

theorem smul_mem_std {Λ : Lt E n} (hU : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {s : ℕ}
    (h : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n := by
  intro v hv
  rw [← std_eq, mem_std]
  intro i
  have := (hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))
  convert this using 1
  simp [herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]

theorem genLat_vset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Lt E n), (∀ bad M : ℕ, 0 < bad → Odd M → Λ ∈ Vset E n (2 * bad * M) → (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt bad ∧ (⟨Λ⟩ : GenLat E n).TrivAt M ∧ ∃ N, NOK Λ N M) ∧ (∀ M N : ℕ, 0 < M → (⟨Λ⟩ : GenLat E n).Unimod → (⟨Λ⟩ : GenLat E n).TrivAt M → NOK Λ N M → Λ ∈ Vset E n M) ∧ (∀ M M' : ℕ, M ∣ M' → Λ ∈ Vset E n M' → Λ ∈ Vset E n M) ∧ stdLat E n = stdL E n := by
  intro E _ _ _ n Λ
  refine ⟨?_, ?_, ?_, std_eq⟩
  · rintro bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩
    have t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m := fun m hm =>
      ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩
    refine ⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right,
      t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩
    · exact (Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM
    · rw [span_smul_le]
      intro v hv
      refine ⟨?_, natCast_smul_mem _ hv⟩
      rw [std_eq] at hv
      rw [mul_comm, Nat.cast_mul, mul_smul]
      exact natCast_smul_mem M (h2 v hv)
  · rintro M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩
    rw [unimod_iff] at hU
    rw [std_eq, span_smul_le] at h1 h2 h3
    have h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := fun v hv => (h3 v hv).1
    have h5 := smul_mem_std hU h4
    refine ⟨fg_of_smul_le hN.pos h5, hU, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      exact ⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩
    · exact ⟨k, hk0, hk, h1, h2⟩
  · rintro M M' hM ⟨a, b, s, hs, hc, h⟩
    exact ⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩

end GlobalTheory.Dict.GenLatCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.Dict

theorem isHolFam_fibrePoint {S : Scheme.{0}} (G : Over S) [GrpObj G] {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (ex : (Fin g → ℂ) → (Over.mk x0 ⟶ G)) (hol : IsHolTo Set.univ (fun z => (ex z).left)) :
    IsHolFam (fun z => (vtfQ G (ex z)).left) := by
  have hol' : IsHolFam (fun z => (ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and] using hol U f
  have he : ∀ z, (ex z).left ≫ G.hom = x0 := fun z => Over.w (ex z)
  have h := isHolFam_vtfLift G.hom x0 (fun z => (ex z).left) he hol'
  let σ : pullback G.hom x0 ⟶ (Over.mk x0 ⊗ G).left := (pullbackSymmetry G.hom x0).hom
  have hσ : ∀ z, vtfLift G.hom x0 (fun z => (ex z).left) he z ≫ σ = (vtfQ G (ex z)).left := fun z => by
    refine vtf_pt_uniq G (ex z) _ ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_snd G.hom x0)).trans
        (pullback.lift_fst _ _ _))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_fst G.hom x0)).trans
        (pullback.lift_snd _ _ _))
  intro U f
  have h2 := h (σ ⁻¹ᵁ U) ((σ.app U).hom f)
  simp only [← hσ]
  exact ⟨h2.1, h2.2.congr fun z _ => (valAt'_comp _ σ U f).symm⟩

theorem hx_add_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (z a w : Fin g → ℂ) (t : ℂ) :
    hx X bas idx x (z + t • a) w = hx X bas idx x z w + t * hx X bas idx x a w := by
  simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem reads_existsUnique_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))), (∃! θ, A.Reads k F θ) ∧ ∀ θ, A.Reads k F θ → Differentiable ℂ θ ∧ ∀ v ∈ L, (A.χ v)⁻¹ ^ k • fock X bas idx x k (pv X idx x v) θ = θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A _ _ _ k F
  have hcov : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (A.ex z).left cpt ∈ (⨆ i, Xo.univ.t.PP.L.U i) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, top_le_of_mem hj⟩
  have hrd : ∀ θ, A.Reads k F θ → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' (vtfQ Xo.univ.t.G (A.ex z)).left
        ((LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * A.fr j z ^ (k : ℤ) := fun θ h j z hj =>
    h j z _ (vtfQ_snd _ _) (vtfQ_fst _ _) hj
  have hne : ∀ j z (m : ℤ), ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A.fr j z ^ m ≠ 0 :=
    fun j z m hj => zpow_ne_zero m (A.fr_ne j z hj)
  refine ⟨?_, fun θ h => ⟨fun z => ?_, fun v hv => ?_⟩⟩
  · choose ch hch using hcov
    refine ⟨fun z => valAt' (vtfQ Xo.univ.t.G (A.ex z)).left
        ((LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x)).U (fun _ => ch z)) (F.f (fun _ => ch z)) /
        A.fr (ch z) z ^ (k : ℤ), ?_, fun θ h => ?_⟩
    · intro j z pt h1 h2 hj
      obtain rfl := vtf_pt_uniq Xo.univ.t.G (A.ex z) pt h1 h2
      exact vtf_read Xo.univ.t.G Xo.univ.t.PP.L F (A.ex z) (fun j => A.fr j z) (fun j j' => A.fr_g j j' z)
        (ch z) j (hch z) hj _ (div_mul_cancel₀ _ (hne _ _ _ (hch z))).symm
    · funext z
      rw [hrd θ h _ z (hch z), mul_div_cancel_right₀ _ (hne _ _ _ (hch z))]
  · obtain ⟨j, hj⟩ := hcov z
    have ho : IsOpen {w | ⊤ ≤ (A.ex w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      simpa only [Set.mem_univ, true_and] using (A.hol (Xo.univ.t.PP.L.U j) 0).1
    have hn := ho.mem_nhds hj
    have hd := (isHolFam_fibrePoint Xo.univ.t.G A.ex A.hol _ (F.f (fun _ => j))).2.mono
      (fun w (hw : w ∈ {w | ⊤ ≤ (A.ex w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) =>
        vtf_chart Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (A.ex w) (fun _ => j) hw)
    have hq := (hd.differentiableAt hn).mul (((A.fr_hol j).differentiableAt hn).zpow (m := -(k : ℤ))
      (Or.inl (A.fr_ne j z hj)))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    have h1 := hrd θ h j w hw
    refine Eq.trans ?_ (congrArg (· * A.fr j w ^ (-(k : ℤ))) h1.symm)
    rw [_root_.zpow_neg, mul_inv_cancel_right₀ (hne _ _ _ hw)]
  · funext z
    obtain ⟨j, hj⟩ := hcov z
    have hex : A.ex (z + pv X idx x v) = A.ex z := by
      rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
    have hj' : ⊤ ≤ (A.ex (z + pv X idx x v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
      rw [hex]; exact hj
    have h2 := hrd θ h j _ hj'
    rw [hex, hrd θ h j z hj, A.fr_per v hv j z hj, mul_zpow, ← _root_.mul_assoc] at h2
    have h3 := mul_right_cancel₀ (hne _ _ _ hj') h2
    have hχ : A.χ v ≠ 0 := fun h0 => by simpa [h0] using A.χ_norm v hv
    simp only [Pi.smul_apply, fock, smul_eq_mul]
    rw [← h3, hx_add_smul, zpow_natCast, mul_pow, ← Complex.exp_nat_mul]
    set a := hx X bas idx x z (pv X idx x v)
    set b := hx X bas idx x (pv X idx x v) (pv X idx x v)
    have h4 : cexp (-((k : ℂ) * Real.pi * (a + 1 / 2 * b))) * cexp (k * (Real.pi * a + Real.pi / 2 * b)) = 1 := by
      rw [← Complex.exp_add]
      refine Eq.trans (congrArg cexp ?_) Complex.exp_zero
      ring
    have h5 : (A.χ v)⁻¹ ^ k * A.χ v ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hχ, one_pow]
    linear_combination (θ z * ((A.χ v)⁻¹ ^ k * A.χ v ^ k)) * h4 + θ z * h5

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjProjOfGood
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ProjProj

open GlobalTheory.SW.TensVac

theorem proj_proj_of_good {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A₁ A₂ A₃ : AddSubgroup (Matrix (Fin n) (Fin r) E)} (h₂ : Good X w A₂) (h₃ : Good X w A₃)
    (hle : A₂ ≤ (A₂ ⊓ A₁) ⊔ (A₂ ⊓ A₃)) {v : TF n g} (hv : IsVac X bas w A₁ v) :
    projA X bas w A₃ (projA X bas w A₂ v) = projA X bas w A₃ v := by
  obtain ⟨v₂, hv₂, -⟩ := h₂.vac hs
  obtain ⟨v₃, hv₃, -⟩ := h₃.vac hs
  have hsb₂ := (h₂.proj idx hs hn hv.1 hv₂).1
  rw [(h₃.proj idx hs hn hsb₂ hv₃).2, (h₃.proj idx hs hn hv.1 hv₃).2]
  congr 1
  have hfin := h₂.finite idx hs hn hv.1
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hv.1
  have hpos : (((fun y => epsW X w y • heisG X bas y v) '' A₂).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 ((Set.ncard_pos hfin).2 ⟨_, 0, A₂.zero_mem, rfl⟩).ne'
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv₃.1
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv₃.1, h2,
    Finset.sum_congr rfl (g := fun _ => SW.ip v v₃), Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul, inv_mul_cancel_left₀ hpos]
  intro ψ hψ
  obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hψ
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
  show SW.ip (epsW X w (a + b) • heisG X bas (a + b) v) v₃ = SW.ip v v₃
  rw [add_comm a b, ← h₂.rho_rho idx hs hn hb.1 ha.1 hv.1, hv.2.2 a ha.2,
    ← rho_ip (w := w) idx hs hn b hv.1 hv₃.1, hv₃.2.2 b hb.2]

theorem proj_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ L₃ : Lt E r, SelfD X L₁ → SelfD X L₂ → SelfD X L₃ → ∀ Λ₁ ∈ Vset E n 1, ∀ Λ₂ ∈ Vset E n 1, ∀ Λ₃ ∈ Vset E n 1, tens Λ₂ L₂ ≤ (tens Λ₂ L₂ ⊓ tens Λ₁ L₁) ⊔ (tens Λ₂ L₂ ⊓ tens Λ₃ L₃) → ∀ v : TF n g, IsVac X bas w (tens Λ₁ L₁) v → projA X bas w (tens Λ₃ L₃) (projA X bas w (tens Λ₂ L₂) v) = projA X bas w (tens Λ₃ L₃) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L₁ L₂ L₃ _ hL₂ hL₃ Λ₁ _ Λ₂ hΛ₂ Λ₃ hΛ₃ hle v hv
  have good (L) (hL : SelfD X L) (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  exact proj_proj_of_good idx hs hn (good L₂ hL₂ Λ₂ hΛ₂) (good L₃ hL₃ Λ₃ hΛ₃) hle hv

end GlobalTheory.Dict.ProjProj
end
