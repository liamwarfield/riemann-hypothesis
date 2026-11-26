module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section RationalPoints

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem cap_fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
theorem cap_fv_neg (x : Fin n → E) : fv F (-x) = - fv F x := by
  funext i
  simp [fv, TensorProduct.tmul_neg]

omit [NumberField E] in
theorem cap_fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i
  simp [fv]

omit [NumberField E] in
theorem cap_fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [cap_fv_zero]
  | succ d ih => rw [succ_nsmul, succ_nsmul, cap_fv_add, ih]

omit [NumberField E] in
theorem cap_gen_mem (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : Fin n → E) (hx : x ∈ L) :
    (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) ∈ hat F L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

omit [NumberField E] in
theorem cap_fv_mem (L : Set (Fin n → E)) (x : Fin n → E) (hx : x ∈ L) : fv F x ∈ hat F L :=
  cap_gen_mem F L 1 (fun v => (v.adicCompletionIntegers F).one_mem) x hx

omit [NumberField E] in
theorem cap_split (r : F) (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (algebraMap F (FiniteAdeleRing (𝓞 F) F) r + d • a) ⊗ₜ[F] x i : Fin n → RA F E)
      = fv F (algebraMap F E r • x) + d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, algebraMap_smul]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

omit [NumberField E] in
theorem cap_tmul_nsmul (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => a ⊗ₜ[F] (d • x) i : Fin n → RA F E)
      = d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [Pi.smul_apply]
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.tmul_add, ih]

theorem cap_exists_denom (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | (apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target ..)

end RationalPoints

theorem hat_rational_points_and_approx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L hfg hsp
  have h3 : ∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
    have hadd : ∀ z w : Fin n → RA F E, (∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, w - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, z + w - fv F x ∈ (hat F (L : Set (Fin n → E)))) := by
      rintro z w ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      have := add_mem hx hy
      rw [cap_fv_add]
      convert this using 1
      abel
    have hzero : ∃ x : Fin n → E, (0 : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) :=
      ⟨0, by rw [cap_fv_zero, sub_zero]; exact zero_mem _⟩
    have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (y : Fin n → E), ∃ x : Fin n → E,
        (fun i => a ⊗ₜ[F] y i : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro a y
      obtain ⟨d, hd, hy⟩ := cap_exists_denom L hsp y
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F d hd).1 a
      refine ⟨algebraMap F E r • y, ?_⟩
      rw [cap_split, add_sub_cancel_left, ← cap_tmul_nsmul]
      exact cap_gen_mem F _ a' ha' _ hy
    have hsingle : ∀ (i : Fin n) (t : RA F E), ∃ x : Fin n → E,
        (Pi.single i t : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro i t
      induction t using TensorProduct.induction_on with
      | zero => simpa using hzero
      | tmul a y =>
        have := hgen a (Pi.single i y)
        convert this using 4
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      | add s t hs ht =>
        rw [Pi.single_add]
        exact hadd _ _ hs ht
    intro z
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ (fun z => ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))))
      hadd hzero (fun i _ => hsingle i (z i))
  refine ⟨?_, ?_, h3, ?_⟩
  · intro v
    obtain ⟨s, e, c, -, hc, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
    have hv : fv F v = ∑ a, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e.repr v a) : RA F E) • fv F (e a) := by
      funext i
      have h := congrFun (e.sum_repr v) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp only [fv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul]
      rw [← TensorProduct.tmul_sum, h]
    rw [hv, GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff F E n L e c hc, hc]
    exact forall_congr' fun a => (GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt F E).2.1 (c a) _
  · intro N hN z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F N hN).2 a ha
      refine ⟨algebraMap F E (r : F) • x, ?_, _, cap_gen_mem F _ a' ha' x hx, cap_split F _ _ _ _⟩
      exact L.smul_mem (algebraMap (𝓞 F) (𝓞 E) r) hx
    | zero => exact ⟨0, L.zero_mem, 0, zero_mem _, by simp [cap_fv_zero]⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      obtain ⟨x', hx', w', hw', rfl⟩ := hz'
      refine ⟨x + x', L.add_mem hx hx', w + w', add_mem hw hw', ?_⟩
      rw [cap_fv_add, smul_add]
      abel
    | neg z _ hz =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      refine ⟨-x, L.neg_mem hx, -w, neg_mem hw, ?_⟩
      rw [cap_fv_neg, smul_neg]
      abel
  · intro z
    obtain ⟨x, hx⟩ := h3 z
    obtain ⟨d, hd, hdx⟩ := cap_exists_denom L hsp x
    refine ⟨d, hd, ?_⟩
    have := add_mem (nsmul_mem hx d) (cap_fv_mem F (L : Set (Fin n → E)) _ hdx)
    rw [cap_fv_nsmul, ← smul_add, sub_add_cancel] at this
    exact this

end GlobalTheory.AdLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximationStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_rational_points_and_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  first | exact @GlobalTheory.AdLat.hat_rational_points_and_approx | exact GlobalTheory.AdLat.hat_rational_points_and_approx | (intros; apply GlobalTheory.AdLat.hat_rational_points_and_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodExists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
lemma card_cmType (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Ψ.card = Module.finrank ℚ E / 2 := by
  classical
  have h1 : Ψ.card = Ψᶜ.card := by
    refine Finset.card_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simpa using (h σ).mp hσ
    · intro σ hσ
      have := h (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at this
      exact this.mpr (by simpa using hσ)
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
  have h2 := Finset.card_add_card_compl Ψ
  rw [NumberField.Embeddings.card E ℂ] at h2
  omega

lemma exists_equiv_of_isTypeFn {H : Host E} {p q g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (h : IsTypeFn H p q ty) (h' : IsTypeFn H p q ty') :
    ∃ e : Fin g ≃ Fin g', ∀ k, ty' (e k) = ty k := by
  have hc : ∀ τ, Nonempty ({i // ty i = τ} ≃ {i // ty' i = τ}) := by
    intro τ
    rw [← Finite.card_eq]
    by_cases hτ : τ (H.rt : E) = H.rt0
    · rw [(h τ).1 hτ, (h' τ).1 hτ]
    · rw [(h τ).2 hτ, (h' τ).2 hτ]
  exact ⟨Equiv.ofFiberEquiv fun τ => (hc τ).some, Equiv.ofFiberEquiv_map _⟩

lemma exists_isPeriod_of_equiv {H : Host E} {D : Datum H} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (e : Fin g ≃ Fin g') (he : ∀ k, ty' (e k) = ty k)
    {P : D.La →+ (Fin g' → ℂ)} (hP : IsPeriod D ty' P) : ∃ P', IsPeriod D ty P' := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  let L : (Fin g' → ℂ) ≃L[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL : ∀ z k, L z k = z (e k) := fun _ _ => rfl
  have hF : ∀ z w, hermForm (Hm.submatrix e e) (L z) (L w) = hermForm Hm z w := by
    intro z w
    simp only [hermForm, dotProduct, mulVec, submatrix_apply, Pi.star_apply, hL]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp]
  let P' : D.La →+ (Fin g → ℂ) := L.toLinearEquiv.toLinearMap.toAddMonoidHom.comp P
  have hP' : ∀ x, P' x = L (P x) := fun _ => rfl
  refine ⟨P', ?_, ?_, ?_, ?_, Hm.submatrix e e, hH.submatrix e, ?_, ?_⟩
  · intro a x k
    rw [hP', hP', hL, hL, h1, he]
  · intro x y hxy
    exact h2 (L.injective hxy)
  · let f : P'.range → P.range := fun z => ⟨L.symm z.1, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨x, by simp [hP']⟩⟩
    have hf : Continuous f := (L.symm.continuous.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hf fun z w hzw =>
      Subtype.ext (L.symm.injective (congrArg Subtype.val hzw))
  · have : Set.range P' = L.toLinearEquiv.toLinearMap '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h4, Submodule.map_top, LinearEquiv.range]
  · intro z hz
    obtain ⟨w, rfl⟩ := L.surjective z
    rw [hF]
    exact hpos w fun h => hz (by rw [h, map_zero])
  · intro x y
    rw [hP', hP', hF, hE]

lemma exists_imaginary (H : Host E) : ∃ ξ : E, FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ ξ).im := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have him : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.im ≠ 0 := by
    intro z hz h0
    have := congrArg Complex.re hz
    simp [sq, h0] at this
    nlinarith [mul_self_nonneg z.re]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : (σ (H.rt : E)).im ≠ 0 := him _ (by rw [← map_pow, hsq]; simp)
  have hne : (H.rt : E) ≠ 0 := fun h => hσ (by rw [h]; simp)
  have hcc : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, hsq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 := congrArg Complex.im (FD.emb_cc σ (H.rt : E))
      rw [h, Complex.conj_im] at h3
      exact hσ (by linarith)
    · exact h
  rcases lt_or_gt_of_ne (him _ H.sqrt_neg_disc_sq) with h | h
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩
    · unfold FD.cc at hcc ⊢
      rw [map_neg, hcc]
    · rw [map_neg, hτ, Complex.neg_im]; linarith
  · exact ⟨_, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩

lemma exists_typeFn_period (H : Host E) (D : Datum H) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty ∧
      g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  classical
  obtain ⟨ξ, hξ, hξ0, hpos⟩ := exists_imaginary H
  obtain ⟨Gm, φ, hm⟩ := exists_herm_coord_of_datum E H D ξ hξ hξ0 _ rfl
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  let idx := (Fintype.equivFin (Ψ × Fin (D.p + D.q))).symm
  obtain ⟨h1, h2⟩ := FramePeriod.isPeriod_frame E H D _ ξ Gm φ Ψ hΨ _ idx _ (fun _ => rfl) hξ
    (fun τ hτ => hpos τ ((hΨ τ).1 hτ)) hm rfl
  choose Q hQ hG using fun τ : Ψ =>
    (GlobalTheory.T.signature_hermitian_model_of_datum E H D _ ξ Gm φ hξ hm τ.1 ((hΨ _).1 τ.2)).1 (hpos _ ((hΨ _).1 τ.2))
  have hx : (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) ∈ FD.GG Ψ Gm D.q := by
    intro τ
    refine ⟨hQ τ, fun i => ?_⟩
    have h3 : FD.dmin Gm (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) τ i = ((FD.psgn D.q i : ℝ) : ℂ) := by
      change FD.lminor (FD.gram τ.1 Gm (Q τ)) i = _
      rw [hG, FD.FrameDegreeData.lminor_diagonal, FD.psgn, ← Fin.prod_univ_eq_prod_range]
      push_cast
      rfl
    rw [h3, Complex.ofReal_re]
    refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    unfold FD.sgn
    split_ifs <;> norm_num
  obtain ⟨⟨P, hP⟩, h4⟩ := h2 _ hx
  refine ⟨_, _, h1, ?_, P, h4 P hP⟩
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
    card_cmType Ψ (FramePeriod.cmType H Ψ hΨ)]

lemma period_of_isTypeFn (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (h : IsTypeFn H D.p D.q ty) :
    g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  obtain ⟨g', ty', h', hg, P, hP⟩ := exists_typeFn_period H D
  obtain ⟨e, he⟩ := exists_equiv_of_isTypeFn h h'
  exact ⟨(Fin.equiv_iff_eq.1 ⟨e⟩).trans hg, exists_isPeriod_of_equiv e he hP⟩

theorem typeFn_period_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  intro E _ _ _ H D
  obtain ⟨g, ty, h, -⟩ := exists_typeFn_period H D
  refine ⟨⟨g, ty, h⟩, period_of_isTypeFn H D, fun hN hr l Xo c => ?_⟩
  obtain ⟨U⟩ := hN E H D l Xo (KA l).val.toRingHom g ty hr rfl h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨-, P, hP⟩ := period_of_isTypeFn H (U.Di i) g ty (by rw [(U.sig i).1, (U.sig i).2]; exact h)
  have hw : CategoryTheory.CategoryStruct.comp (U.u i P) Xo.s =
      CategoryTheory.CategoryStruct.comp (spMap c.F.val.toRingHom)
        (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    rw [U.over_σ i P hP]
    exact AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom)
      (CommRingCat.ofHom c.F.val.toRingHom)
  exact ⟨(CategoryTheory.Limits.pullback.lift _ _ hw).base (IsLocalRing.closedPoint ℂ)⟩

end GlobalTheory.PeriodExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonemptyStatement
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.typeFn_period_exist_moduli_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  first | exact @GlobalTheory.PeriodExists.typeFn_period_exist | exact GlobalTheory.PeriodExists.typeFn_period_exist | (intros; apply GlobalTheory.PeriodExists.typeFn_period_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_mem_adelicCompletionOfElementSet {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (x : ι → RA F E) (h : ∀ i ∈ s, x i ∈ hat1 F (I i : Set E)) :
    ∏ i ∈ s, x i ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Algebra.TensorProduct.one_def]
    exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (h a (Finset.mem_insert_self _ _)) _
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem det_mem_adelicCompletionOfElementSet {n : ℕ} (r s : Fin n → FractionalIdeal (𝓞 E)⁰ E)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((r i * s j : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    M.det ∈ hat1 F (((∏ i, r i) * ∏ j, s j : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  have := prod_mem_adelicCompletionOfElementSet F Finset.univ (fun j => r (σ j) * s j) (fun j => M (σ j) j)
    (fun j _ => h _ _)
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ r] at this
  rw [Units.smul_def]
  exact zsmul_mem this _

theorem cramer_mem_adelicCompletionOfElementSet {n : ℕ} (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
    (w : Fin n → RA F E) (hw : ∀ i, w i ∈ hat1 F (cI i : Set E)) (a : Fin n) :
    M.cramer w a ∈ hat1 F (cI a : Set E) := by
  rw [Matrix.cramer_apply]
  have := det_mem_adelicCompletionOfElementSet F cI (Function.update (fun j => (cI j)⁻¹) a 1) (M.updateCol a w) (by
    intro i j
    by_cases hj : j = a
    · subst hj
      simpa using hw i
    · simpa [hj] using h i j)
  have e : (∏ i, cI i) * ∏ j, Function.update (fun j => (cI j)⁻¹) a 1 j = cI a := by
    rw [← Finset.prod_mul_distrib, Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb, hc b]
    · simp
  rwa [e] at this

theorem algEquiv_mem_one (c : E ≃ₐ[F] E) (x : E) (hx : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩

end

theorem inv_mulVec_mem_hat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (c : E ≃ₐ[F] E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ z ∈ (hat F (L : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E)))) → (g : Matrix (Fin n) (Fin n) (RA F E)).det * sg (FiniteAdeleRing (𝓞 F) F) c (g : Matrix (Fin n) (Fin n) (RA F E)).det = 1 → ∀ z ∈ (hat F (L : Set (Fin n → E))), ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g c hfg hsp hg hdet z hz
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hPk : P * k = G * P := by
    simp only [k, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hg _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  have hd : G.det ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    have := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
    rwa [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i),
      hkdet] at this
  have hd' := galoisAut_mem_adelicCompletionOfElementSet F c (algEquiv_mem_one F c) hd
  have hw : ∀ a, (Q *ᵥ z) a ∈ hat1 F (cI a : Set E) := by
    rw [← key', Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hz
  have hu : P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z)) ∈
      hat F (L : Set (Fin n → E)) := by
    rw [key']
    intro a
    have := (adelicCompletion_fractionalIdeal_properties F E).1 1 (cI a) _ hd' _ (cramer_mem_adelicCompletionOfElementSet F cI hc k hk _ hw a)
    rwa [one_mul] at this
  have hz' : G *ᵥ (P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z))) = z := by
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_cramer, smul_smul, hkdet, mul_comm, hdet, one_smul, Matrix.mulVec_mulVec, hPQ,
      Matrix.one_mulVec]
  rw [← hz', Matrix.mulVec_mulVec, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]
  exact hu

end GlobalTheory.AdLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
open MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaMean

theorem mean_image {ι κ : Type} [Fintype ι] [Fintype κ] (L : (ι → ℝ) ≃L[ℝ] (κ → ℂ))
    {s : Set (ι → ℝ)} (hs : volume s = 1) (f : (κ → ℂ) → ℝ) :
    (∫ z in L '' s, f z) / (volume (L '' s)).toReal = ∫ p in s, f (L p) := by
  have hL : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have : (Measure.map L (volume : Measure (ι → ℝ))).IsAddHaarMeasure := L.isAddHaarMeasure_map _
  set c := Measure.addHaarScalarFactor (volume : Measure (κ → ℂ)) (Measure.map L volume) with hc_def
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hvol : (volume : Measure (κ → ℂ)) = c • Measure.map L volume :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hpre : L ⁻¹' (L '' s) = s := Set.preimage_image_eq s L.injective
  have h1 : (volume (L '' s)).toReal = c := by
    rw [hvol, Measure.smul_apply, hL.map_apply, hpre, hs]
    simp
  have h2 : ∫ z in L '' s, f z = c * ∫ p in s, f (L p) := by
    rw [hvol, Measure.restrict_smul, integral_smul_nnreal_measure, hL.restrict_map, hpre,
      hL.integral_map, NNReal.smul_def, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [h2, h1, mul_div_cancel_left₀ _ hc']

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ))
  map_add' p q := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    periodMap τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ)) := rfl

theorem im_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    (fun i => (periodMap τ p i).im) = τ.map Complex.im *ᵥ fun i => p (.inr i) := by
  funext i
  simp [periodMap_apply, mulVec, dotProduct, Complex.im_sum]

theorem periodMap_bijective {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hp : (τ.map Complex.im).PosDef) : Function.Bijective (periodMap τ) := by
  have hinj : Function.Injective (periodMap τ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have him := im_periodMap τ p
    rw [hp0] at him
    have h2 : (fun i => p (.inr i)) = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hp.det_pos.ne' ?_
      rw [← him]
      rfl
    have h1 : (fun i => (p (.inl i) : ℂ)) = 0 := by
      have := hp0
      rw [periodMap_apply] at this
      have h2' : (fun i => (p (.inr i) : ℂ)) = 0 := by
        funext i
        simp [show p (.inr i) = 0 from congrFun h2 i]
      rw [h2', mulVec_zero, add_zero] at this
      exact this
    funext x
    rcases x with i | i
    · simpa using congrFun h1 i
    · exact congrFun h2 i
  have hrank : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

theorem exists_fundamentalDomain_mean_norm_sq_thetaChar :
    ∀ (g : ℕ) (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ)
      (Λ : AddSubgroup (Fin g → ℂ)), τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
      (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) →
      (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ,
        h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) →
      ∃ Fd : Set (Fin g → ℂ), MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧
        (∫ z in Fd, ‖thetaChar τ c₁ c₂ (h *ᵥ z)‖ ^ 2 * Real.exp (-2 * Real.pi *
          ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) /
          (MeasureTheory.volume Fd).toReal =
          (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h c₁ c₂ Λ hsym hY hh hc₁ hc₂ hΛ
  obtain ⟨a, rfl⟩ : ∃ a : Fin g → ℝ, (fun i => (a i : ℂ)) = c₁ := by
    refine ⟨fun i => (c₁ i).re, funext fun i => ?_⟩
    show ((c₁ i).re : ℂ) = c₁ i
    rcases hc₁ i with e | e <;> rw [e] <;> norm_num
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℝ, (fun i => (b i : ℂ)) = c₂ := by
    refine ⟨fun i => (c₂ i).re, funext fun i => ?_⟩
    show ((c₂ i).re : ℂ) = c₂ i
    rcases hc₂ i with e | e <;> rw [e] <;> norm_num
  have hcancel : ∀ x : Fin g → ℂ, h⁻¹ *ᵥ (h *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  let Pe : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (periodMap τ) (periodMap_bijective hY)
  let Hinv : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' h⁻¹) (Matrix.toLin' h)
      (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hh, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hh, Matrix.toLin'_one])
  let Φ : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (Pe.trans (Hinv.restrictScalars ℝ)).toContinuousLinearEquiv
  have F1 : ∀ p, h *ᵥ Φ p = periodMap τ p := by
    intro p
    show h *ᵥ (h⁻¹ *ᵥ periodMap τ p) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hh, one_mulVec]
  let B : Module.Basis (Fin g ⊕ Fin g) ℝ (Fin g → ℂ) :=
    (Pi.basisFun ℝ (Fin g ⊕ Fin g)).map Φ.toLinearEquiv
  have hrepr : ∀ z i, B.repr z i = Φ.symm z i := by
    intro z i
    simp [B]
  have hΛeq : Λ = (Submodule.span ℤ (Set.range B)).toAddSubgroup := by
    ext lam
    rw [hΛ lam, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem]
    simp only [hrepr, Set.mem_range, algebraMap_int_eq, eq_intCast]
    constructor
    · rintro ⟨m, n, hmn⟩ i
      have hPq : periodMap τ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) =
          (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
        rw [periodMap_apply]
        simp
      have hΦq : Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = lam := by
        have e : h *ᵥ Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = h *ᵥ lam := by
          rw [F1, hPq, hmn]
        rw [← hcancel (Φ _), e, hcancel]
      rw [← hΦq, Φ.symm_apply_apply]
      rcases i with i | i
      · exact ⟨m i, by simp⟩
      · exact ⟨n i, by simp⟩
    · intro hk
      choose k hk using hk
      refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
      rw [← Φ.apply_symm_apply lam, F1, periodMap_apply]
      simp_rw [← hk, Complex.ofReal_intCast]
  have hFd : ZSpan.fundamentalDomain B = Φ '' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    ext z
    simp [ZSpan.mem_fundamentalDomain, hrepr]
  have hcube : volume (Set.univ.pi fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) = 1 := by
    simpa using Real.volume_pi_Ico (a := fun _ : Fin g ⊕ Fin g => (0 : ℝ)) (b := fun _ => 1)
  have hYu : IsUnit (τ.map Complex.im).det := hY.det_pos.ne'.isUnit
  refine ⟨ZSpan.fundamentalDomain B, by rw [hΛeq]; exact ZSpan.isAddFundamentalDomain' B _, ?_⟩
  rw [hFd, mean_image Φ hcube, ← GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hsym hY]
  congr 1
  funext p
  rw [F1, im_periodMap, mulVec_mulVec, nonsing_inv_mul _ hYu, one_mulVec, dotProduct_comm,
    periodMap_apply]

end GlobalTheory.ThetaMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_sq_transform_level_eight :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ),
      γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
      (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) →
      (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
        theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 =
          ((ZMod.χ₄ ((γ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut γ τ).det *
            eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) := by
  intro g γ hγ h τ hτ z
  have h48 : (4 : ℤ) ∣ 8 := by norm_num
  exact theta_halfVec_sq_transform hγ (fun i j => h48.trans (h i j).1)
    (fun i j => h48.trans (h i j).2) (k := 0) (k' := 0) (m := 0) (m' := 0)
    (fun i => by rw [mulVec_zero]) (fun i => by rw [mulVec_zero]) hτ z

end GlobalTheory
end
