module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

namespace GlobalTheory.EtaSelfDual

theorem ordF_unif {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : ordF w (unif w) = 1 := by
  have h := unif_spec w
  have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (unif w : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (unif w : K)
  have h0 : w.valuation K (unif w : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (unif w).ne_zero
  unfold IsUnifAt at h
  rw [h1, ← WithZero.exp_log h0, WithZero.exp_inj] at h
  unfold ordF
  omega

theorem ordF_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') (k : H.Eˣ) :
    ordF w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = ordF w k := by
  have hc := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').1 h (k : H.E)
  unfold ordF
  congr 2

theorem val_mul_val {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : IsEtaT H χ)
    {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : χ.val w * χ.val w' = 1 := by
  classical
  obtain ⟨c, hc, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hC : GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').1 h
  have hC' : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w' := fun x => by
    have := hC x
    simpa [hc] using this
  set v := w.under (𝓞 H.F) with hv
  have hmem : ∀ P, P ∈ aboveF (L := H.E) H.F v ↔ P = w ∨ P = w' := by
    intro P
    rw [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv w).unique h1 hC')
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (h1 ▸ hC')
  have hab : aboveF (L := H.E) H.F v = insert w {w'} := by
    ext P
    rw [hmem P, Finset.mem_insert, Finset.mem_singleton]
  have hloc : ∀ P ∈ aboveF (L := H.E) H.F v, χ.locK P (upF H.F (unif v)) = χ.val P := fun P hP => by
    have hPv : P.under (𝓞 H.F) = v := by
      rw [aboveF, Set.Finite.mem_toFinset] at hP
      exact hP
    rw [GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr P), ho, hPv, ordF_unif, zpow_one]
  have hwm : w ∈ aboveF (L := H.E) H.F v := (hmem w).2 (Or.inl rfl)
  have hwm' : w' ∈ aboveF (L := H.E) H.F v := (hmem w').2 (Or.inr rfl)
  have hr := hχ.res.1 v (unif v)
  simp only [HChar.resFin] at hr
  by_cases hw : w = w'
  · subst hw
    rw [hab, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.prod_singleton, etaFin, hab,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _), if_pos (Finset.card_singleton _), ordF_unif, zpow_one] at hr
    change χ.locK w (upF H.F (unif v)) = -1 at hr
    rw [hloc w hwm] at hr
    rw [hr]
    simp
  · rw [hab, Finset.prod_insert (by simpa using hw), Finset.prod_singleton, etaFin, hab,
      if_neg (by rw [Finset.card_insert_of_notMem (by simpa using hw), Finset.card_singleton]; omega)] at hr
    change χ.locK w (upF H.F (unif v)) * χ.locK w' (upF H.F (unif v)) = 1 at hr
    rw [hloc w hwm, hloc w' hwm'] at hr
    exact hr

theorem isCSD_of_isEtaT : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → IsCSD H χ := by
  intro R H χ hχ
  refine ⟨fun w w' h k => ?_, fun k => ?_⟩
  · rw [GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr w'), GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr w), ordF_conj H h,
      eq_inv_of_mul_eq_one_left (val_mul_val H χ hχ h), inv_zpow, inv_inv]
  · refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [Units.val_mul, Units.val_one, hχ.inf, hχ.inf, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun g _ => ?_
    have hz : embPsi H g (k : H.E) ≠ 0 := (_root_.map_ne_zero _).2 k.ne_zero
    have e1 : embPsi H g ((Units.map (MonoidHomClass.toMonoidHom H.conj) k : H.Eˣ) : H.E) =
        starRingEnd ℂ (embPsi H g (k : H.E)) := H.conjE_apply _ _
    rw [e1, Complex.norm_conj, zpow_one, zpow_one, div_mul_div_comm, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← sq, div_self]
    exact Complex.ofReal_ne_zero.2 (pow_ne_zero _ (norm_ne_zero_iff.2 hz))

end GlobalTheory.EtaSelfDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContra
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem invT_invT_gl {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g := by
  apply Units.ext
  change ((invT a R g)⁻¹).valᵀ = g.val
  rw [← map_inv]
  change ((g⁻¹)⁻¹).valᵀᵀ = g.val
  rw [inv_inv, Matrix.transpose_transpose]

theorem map_invT_gl {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  change p.mapMatrix ((g⁻¹).valᵀ) = ((GeneralLinearGroup.map p g)⁻¹).valᵀ
  rw [← map_inv]
  ext i j
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) : invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) := by
  apply ga_ext
  · rw [map_invT_gl, pInf_infGL, pInf_infGL]
  · rw [map_invT_gl, pFin_infGL, pFin_infGL, map_one]

theorem norm_toL_transpose (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL xᵀ‖ = ‖toL x‖ := by
  have key : ∀ y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL yᵀ‖ ≤ ‖toL y‖ := fun y =>
    pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j =>
      (norm_le_pi_norm (toL y j) i).trans (norm_le_pi_norm (toL y) j)
  refine le_antisymm (key x) ?_
  simpa using key xᵀ

theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((invT a (Cinf E) y)⁻¹).val‖ = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  rw [← map_inv]
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((y⁻¹)⁻¹).valᵀ‖ = _
  rw [inv_inv, norm_toL_transpose, norm_toL_transpose]
  ring

theorem isRapidInf_invT {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : IsRapidInf ν k γ) : IsRapidInf ν k (fun x => invT a (Cinf E) (γ x)) := by
  refine ⟨hk.1, ?_, fun N => ?_⟩
  · refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
    set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
    have e : (fun x => ((invT a (Cinf E) (γ x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w) =
        fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i := by
      funext x
      rw [← map_inv]; rfl
    rw [e]
    have hγ : ∀ i' j', Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i' j' := fun i' j' =>
      (measurable_pi_apply j').comp ((measurable_pi_apply i').comp hk.2.1)
    exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i)
      ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
        ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem j i)
      fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
  · simp only [height_invT]
    exact hk.2.2 N

theorem kerInf_comp_invT {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) :
    kerInf ν k γ F (invT a (Ad E) g) =
      kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) g := by
  unfold kerInf
  congr 1
  funext x
  show k x * F (invT a (Ad E) g * infGL E a (γ x)) =
    k x * F (invT a (Ad E) (g * infGL E a (invT a (Cinf E) (γ x))))
  rw [map_mul, invT_infGL, invT_invT_gl]

theorem comp_invT_mem_mspanR (π : CuspSub E a) (F : GA E a → ℂ) (hF : F ∈ mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ mspanR π.contra := by
  let T : Submodule ℂ (GA E a → ℂ) :=
    (rspan π.contra).comap (LinearMap.funLeft ℂ ℂ (invT a (Ad E)))
  have memT : ∀ G : GA E a → ℂ, G ∈ T ↔ (fun g => G (invT a (Ad E) g)) ∈ rspan π.contra := fun G =>
    Submodule.mem_comap
  have hle : rspan π ≤ T := by
    refine rspan_le (fun φ hφ => ?_) (fun F hF h => ?_) fun F hF X _ ν _ k γ hk => ?_
    · rw [memT]
      have h1 : UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V := Submodule.mem_map_of_mem hφ
      exact mem_rspan h1
    · rw [memT] at hF ⊢
      have h2 := rt_mem_rspan hF (invT a (Ad E) h)
      have e : (fun g => F (invT a (Ad E) g * h)) = fun g => F (invT a (Ad E) (g * invT a (Ad E) h)) := by
        funext g; rw [map_mul, invT_invT_gl]
      rw [e]; exact h2
    · rw [memT] at hF ⊢
      have h3 := kerInf_mem_rspan hF ν (isRapidInf_invT hk)
      have e : (fun g => kerInf ν k γ F (invT a (Ad E) g)) =
          kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) :=
        funext fun g => kerInf_comp_invT ν k γ F g
      rw [e]; exact h3
  rw [← rspan_eq_mspanR] at hF ⊢
  exact (memT F).1 (hle hF)

theorem invT_mem_mspanR_contra : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  fun _ _ _ _ _ π F hF => comp_invT_mem_mspanR π F hF

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContraStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra := by
  first | exact @GlobalTheory.JSW.invT_mem_mspanR_contra | exact GlobalTheory.JSW.invT_mem_mspanR_contra | (intros; apply GlobalTheory.JSW.invT_mem_mspanR_contra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictEqInvLocalArtinMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfPowEqSelf
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDict


open Polynomial in
theorem exists_eq_of_pow_eq_self {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Field L] (j : Ω →+* L) {N : ℕ}
    (hN : 2 ≤ N) {ζ : L} (hζ : ζ ^ N = ζ) : ∃ z, j z = ζ := by
  have hmon : (X ^ N - X : Polynomial Ω).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hb : ζ ∈ ((X ^ N - X : Polynomial Ω).map j).roots := by
    rw [mem_roots (hmon.map j).ne_zero]
    simp [hζ]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem isFrob_iff_of_lifts (h : IsPlaceOver A w) {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ : G E Ω}
    (hσ : σ ∈ Dec (F := E) A) (H : Lifts ι g σ) :
    IsFrob (F := E) A (normV w) σ ↔
      ∀ (ζ : Kbar w) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → g ζ = ζ ^ normV w := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rw [GlobalTheory.FrobTeich.isFrob_iff_teichmuller E Ω A w h σ]
  constructor
  · rintro ⟨-, hT⟩ ζ m hm hζ
    obtain ⟨z, rfl⟩ := exists_eq_of_pow_eq_self (ι : Ω →+* Kbar w)
      (Nat.one_lt_pow hm.ne' (ReciprocityTheory.Gal.one_lt_normV w)) hζ
    have hz : z ^ normV w ^ m = z := (ι : Ω →+* Kbar w).injective (by rw [map_pow]; exact hζ)
    change g (ι z) = ι z ^ normV w
    rw [H z, hT z m hm hz, map_pow]
  · intro hT
    refine ⟨hσ, fun z m hm hz => (ι : Ω →+* Kbar w).injective ?_⟩
    change ι (σ z) = ι (z ^ normV w)
    rw [← H z, map_pow]
    exact hT _ m hm (by rw [← map_pow, hz])

end GlobalTheory.WeilDict
end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
open GroundTheory.LocalField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompare

theorem restrict_eq_inv_localArtinMap : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
        (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
  have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
  obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
  have e2 : ψ σ = g := by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
  have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
      (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
    restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
  have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
      [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
      a τ ∈ (normUnits (w.adicCompletion E) L).range →
        restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
    have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
    rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
    exact this
  let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
  have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
  have hker : a'.ker ≤ r.ker := fun τ hτ => by
    have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
    refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
    rw [map_one]
    exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
  let b := a'.liftOfSurjective ha' ⟨r, hker⟩
  have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
    MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
  have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
    refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
    · obtain ⟨τ, rfl⟩ := ha' π
      have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
      rw [ha.ord_eq, deg_inv, neg_neg] at h1
      have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb, hr]
      refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
      rw [unramifiedDegree_eq_ofAdd_one_iff]
      rintro ξ ⟨n, hn, hξ⟩
      have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := resCard_eq_normV w
      rw [hq] at hξ ⊢
      refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
      have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (ReciprocityTheory.Gal.one_lt_normV w)))).symm
      rw [h2, pow_succ, hξ, one_mul]
    · obtain ⟨τ, rfl⟩ := ha' x
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb]
      exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
  rw [← map_inv, ← hbφ, hb, ← e2]
  rfl

theorem restrict_eq_inv_reciprocity : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (Ω' : Type) [Field Ω'] [Algebra (w.adicCompletion E) Ω'] [IsSepClosure (w.adicCompletion E) Ω'] (j : Ω →+* Ω'),
    (∀ x : E, j (algebraMap E Ω x) = algebraMap (w.adicCompletion E) Ω' (algebraMap E (w.adicCompletion E) x)) →
    (∀ z : Ω, z ∈ A ↔ ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).IsIntegralElem (j z)) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ (σ : Weil h) (g : Ω' ≃ₐ[w.adicCompletion E] Ω'), (∀ z : Ω, g (j z) = j ((σ : G E Ω) z)) →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
        (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ ∧
      ∀ (M : IntermediateField (w.adicCompletion E) Ω') [FiniteDimensional (w.adicCompletion E) M]
        [IsAbelianGalois (w.adicCompletion E) M],
        AlgEquiv.restrictNormalHom M g =
          ((localReciprocityAbelian M).symm
            (a σ : (w.adicCompletion E)ˣ ⧸ (normUnits (w.adicCompletion E) M).range))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h Ω' _ _ _ j hj hA a ha σ g hg
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : IsSepClosure (w.adicCompletion E) (Kbar w) := ⟨inferInstance, inferInstance⟩
  let ε : Ω' ≃ₐ[w.adicCompletion E] Kbar w := IsSepClosure.equiv (w.adicCompletion E) Ω' (Kbar w)
  let ι : Ω →ₐ[E] Kbar w :=
    { (ε : Ω' →+* Kbar w).comp j with
      commutes' := fun x => by
        change ε (j (algebraMap E Ω x)) = _
        rw [hj, ε.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)] }
  have hιz : ∀ z, ι z = ε (j z) := fun _ => rfl
  have hc : (ε : Ω' →+* Kbar w).comp ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) =
      algebraMap (w.adicCompletionIntegers E) (Kbar w) := RingHom.ext fun x => by
    rw [IsScalarTower.algebraMap_apply (w.adicCompletionIntegers E) (w.adicCompletion E) (Kbar w)]
    exact ε.commutes _
  have hι : IsLocEmb A w ι := fun z => by
    rw [hA, hιz]
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      rw [← hc]
      have := congrArg (ε : Ω' →+* Kbar w) hp'
      rwa [Polynomial.hom_eval₂, map_zero] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (ε : Ω' →+* Kbar w).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hc]
      exact hp'
  let g' : GalLoc w := ε.symm.trans (g.trans ε)
  have hg' : Lifts ι g' σ := fun z => by
    change ε (g (ε.symm (ε (j z)))) = ε (j _)
    rw [ε.symm_apply_apply, hg]
  have H := restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ g' hg'
  have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
      (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ := by
    rw [← map_inv] at H ⊢
    ext y
    have h1 := localArtinMap_transport (RingEquiv.refl (w.adicCompletion E)) (fun _ _ => Iff.rfl)
      (ε : Ω' ≃+* Kbar w) (fun x => ε.commutes x) (a σ)⁻¹ y.2
    have h2 : Units.map (RingEquiv.refl (w.adicCompletion E)).toRingHom.toMonoidHom (a σ)⁻¹ = (a σ)⁻¹ :=
      Units.ext rfl
    rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
    rw [AlgEquiv.restrictNormalHom_apply]
    apply ε.injective
    refine Eq.trans ?_ h1.symm
    change _ = ε (g (ε.symm (ε y)))
    rw [ε.symm_apply_apply]
  refine ⟨H1, fun M _ _ => ?_⟩
  rw [← restrictAb_localArtinMap, ← map_inv, ← H1]
  exact (restrictAb_topologicalAbelianizationEquiv M (le_maximalAbelianExtension M) g).symm

end GlobalTheory.ArtinCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOne
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilCharKer

open GlobalTheory.LocDict GlobalTheory.HeckeGal
open Neutral.B1 hiding IsPlaceOver G

theorem commutator_le_of_dense {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [Group W] (ψ : W →* Γ) (hd : ∀ (g : Γ) (H : Subgroup Γ), IsOpen (H : Set Γ) → ∃ σ : W, g⁻¹ * ψ σ ∈ H)
    (F : Subgroup Γ) (hF : IsOpen (F : Set Γ)) (hc : ∀ σ τ : W, ψ (σ * τ * σ⁻¹ * τ⁻¹) ∈ F) :
    commutator Γ ≤ F := by
  have : Finite (Γ ⧸ F) := Subgroup.quotient_finite_of_isOpen F hF
  have : F.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (F.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (F.normalCore_isClosed (F.isClosed_of_isOpen hF))
  rw [commutator, Subgroup.commutator_le]
  intro g _ k _
  obtain ⟨σ, hσ⟩ := hd g _ hN
  obtain ⟨τ, hτ⟩ := hd k _ hN
  have e1 : QuotientGroup.mk' F.normalCore g = QuotientGroup.mk' F.normalCore (ψ σ) := QuotientGroup.eq.2 hσ
  have e2 : QuotientGroup.mk' F.normalCore k = QuotientGroup.mk' F.normalCore (ψ τ) := QuotientGroup.eq.2 hτ
  have e3 : QuotientGroup.mk' F.normalCore (ψ (σ * τ * σ⁻¹ * τ⁻¹)) =
      QuotientGroup.mk' F.normalCore (g * k * g⁻¹ * k⁻¹) := by
    simp only [map_mul, map_inv, e1, e2]
  have e4 := F.mul_mem (hc σ τ) (F.normalCore_le (QuotientGroup.eq.1 e3))
  rw [mul_inv_cancel_left] at e4
  exact e4

theorem index_normGroup {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsAbelianGalois K L] :
    (normGroup K L).index = Nat.card (L ≃ₐ[K] L) := by
  have e : normGroup K L = (GroundTheory.LocalField.normUnits K L).range := rfl
  rw [e, ← GroundTheory.LocalField.ker_restrictAb_localArtinMap (Ω := AlgebraicClosure K) L, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (GroundTheory.LocalField.surjective_restrictAb_localArtinMap L), Subgroup.card_top]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem art_inj {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    Function.Injective fun x : (w.adicCompletion E)ˣ => art (localIdele E w x) :=
  GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w

theorem exists_inverse (h : IsPlaceOver A w) {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧
      ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LocNormGrp.art_range_weil E Ω A w h art ha
  choose a ha' using h1
  refine ⟨MonoidHom.mk' a fun σ τ => art_inj ha ?_, fun y => ?_, ha'⟩
  · simp only [map_mul, ha', Subgroup.coe_mul]
  · obtain ⟨τ, hτ⟩ := h2 y
    exact ⟨τ, art_inj ha ((ha' τ).trans hτ.symm)⟩

theorem mem_of_toAb_eq_one (h : IsPlaceOver A w) (H : Subgroup (Weil h)) (hfin : H.FiniteIndex)
    (hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H}) (hcomm : ∀ σ τ : Weil h, σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (σ : Weil h) (hσ : toAb E Ω σ = 1) : σ ∈ H := by
  obtain ⟨K, hK, hloc, hHK⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hfin hop
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  obtain ⟨W, h'⟩ := GlobalTheory.LocNormGrp.exists_place h K
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb E Ω A w h
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb K Ω A W h'
  obtain ⟨f, b, hf, hb1, hb2, hfE, -, -, -, hNc, hNg⟩ := GlobalTheory.T.local_embeddings_tower_compatible E K Ω A w W h h' hloc ι ι' hι hι'
  letI := f.toAlgebra
  have hN := GlobalTheory.T.completion_embedding_compatible_closures E K w W (fun x : K => ι (algebraMap K Ω x)) f b hf hb1
    (fun x => by rw [hb2, ι'.commutes, IsScalarTower.algebraMap_apply K (W.adicCompletion K)]) hfE
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨artK, hartK⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  obtain ⟨a, hasurj, ha⟩ := exists_inverse h hart
  let N := Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)
  have key := GlobalTheory.LocNormGrp.art_norm_eq_res E K Ω art artK hart hartK w W
    (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h') N (Continuous.units_map _ hNc) fun z => Units.ext (hNg z)
  obtain ⟨h1, -⟩ := GlobalTheory.LocNormGrp.art_range_weil K Ω A W h' artK hartK
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set L := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hL

  have hHN : H ≤ (normGroup Kw L).comap a := fun s hs => by
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_weil_of_fixes' E K Ω A w W h h' s ((hHK s).1 hs)
    obtain ⟨y, hy⟩ := h1 τ
    rw [Subgroup.mem_comap, hN]
    exact ⟨y, art_inj hart ((key y τ s hτ hy).trans (ha s).symm)⟩

  have hfd : FiniteDimensional Kw L := by
    let pb := Field.powerBasisOfFiniteOfSeparable E K
    let j : K →ₐ[E] Kbar w := ι.comp K.val
    have hfd0 : FiniteDimensional Kw (IntermediateField.adjoin Kw {j pb.gen}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    have hle : L ≤ IntermediateField.adjoin Kw {j pb.gen} := by
      rw [hL, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨p, rfl⟩ := pb.exists_eq_aeval' x
      show j (aeval pb.gen p) ∈ IntermediateField.adjoin Kw {j pb.gen}
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap Kw]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  obtain ⟨θ, hθ, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ s : Weil h, Lifts ι (ψ s) (s : G E Ω) := fun s => hl _
  have hψ' : ∀ (s : Weil h) (g : GalLoc w), Lifts ι g s → ψ s = g := fun s g hg => by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) s := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  have hHL : ∀ s : Weil h, s ∈ H ↔ ψ s ∈ L.fixingSubgroup := fun s => by
    rw [hHK, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, hL, IntermediateField.adjoin_le_iff]
    constructor
    · rintro hs _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      refine (Subgroup.zpowers_le (H := MulAction.stabilizer (GalLoc w) (ι (algebraMap K Ω x)))).2 ?_ hg
      show ψ s (ι x) = ι x
      rw [hψ, hs]
    · intro hs x
      have := (IntermediateField.mem_fixedField_iff _ _).1 (hs ⟨x, rfl⟩) _ (Subgroup.mem_zpowers _)
      rw [hψ] at this
      exact ι.toRingHom.injective this
  have hLo : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := L.fixingSubgroup_isOpen
  have hcl : commutator (GalLoc w) ≤ L.fixingSubgroup :=
    commutator_le_of_dense ψ (fun g U hU => by
      obtain ⟨s, g', h1, h2⟩ := GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl g U hU
      exact ⟨s, by rwa [hψ' s g' h1]⟩) _ hLo fun s t => (hHL _).1 (hcomm s t)
  have hnorm : L.fixingSubgroup.Normal := Subgroup.Normal.of_commutator_le _ hcl
  have hgal : IsGalois Kw L := (InfiniteGalois.normal_iff_isGalois L).1 hnorm
  have hab : IsAbelianGalois Kw L := GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension L (by
    rw [GroundTheory.LocalField.maximalAbelianExtension, IntermediateField.le_iff_le]
    exact Subgroup.topologicalClosure_minimal _ hcl (Subgroup.isClosed_of_isOpen _ hLo))

  have hHker : H = ((AlgEquiv.restrictNormalHom L).comp ψ).ker := by
    ext s
    rw [hHL, ← IntermediateField.restrictNormalHom_ker]; rfl
  have i1 : H.index ≤ Nat.card (L ≃ₐ[Kw] L) := by
    rw [hHker, Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  have i2 : ((normGroup Kw L).comap a).index = Nat.card (L ≃ₐ[Kw] L) := by
    rw [Subgroup.index_comap_of_surjective _ hasurj, index_normGroup]
  have i3 := Subgroup.relIndex_mul_index hHN
  have i4 : H.relIndex ((normGroup Kw L).comap a) = 1 := by
    have := hfin.index_ne_zero
    rw [i2] at i3
    have hp : 0 < Nat.card (L ≃ₐ[Kw] L) := Nat.card_pos
    generalize H.relIndex ((normGroup Kw L).comap a) = r at i3
    rcases r with _ | _ | r
    · omega
    · rfl
    · nlinarith
  refine Subgroup.relIndex_eq_one.1 i4 ?_
  have : a σ = 1 := art_inj hart (by simp only [ha, hσ, map_one])
  rw [Subgroup.mem_comap, this]
  exact Subgroup.one_mem _

theorem deg_eq_zero_of_toAb_eq_one (h : IsPlaceOver A w) (σ : Weil h) (hσ : toAb E Ω σ = 1) : deg σ = 0 := by
  let n := (deg σ).natAbs + 1
  let r : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hr : ∀ s, s ∈ r.ker ↔ (n : ℤ) ∣ deg s := fun s => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl
  have := mem_of_toAb_eq_one h r.ker inferInstance
    (by simp [hr]) (fun s t => by simp [hr]) σ hσ
  rw [hr] at this
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by simp only [Int.natAbs_natCast]; omega)

theorem apply_eq_one_of_toAb_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ), GlobalTheory.WeilDeligne.IsSmooth ξ → ∀ σ : Weil h, GlobalTheory.HeckeGal.toAb E Ω σ = 1 → ξ σ = 1 := by
  intro E Ω _ _ _ _ _ A w h ξ hξ σ hσ
  let ξ' : Weil h →* ℂˣ := ξ * unrChar h (ξ (frob h))⁻¹
  have h0 : ∀ s, deg s = 0 → ξ' s = ξ s := fun s hs => by simp [ξ', hs]
  have h1 : ξ' (frob h) = 1 := by simp [ξ']
  have hop : IsOpen {s : Ine (F := E) A | ineIncl h s ∈ ξ'.ker} := by
    simp only [MonoidHom.mem_ker, h0 _ (deg_ineIncl _)]
    exact hξ
  have := compactSpace_Ine (E := E) A
  have hq : Finite (Ine (F := E) A ⧸ (ξ'.comp (ineIncl h)).ker) := Subgroup.quotient_finite_of_isOpen _ hop
  have hr : Finite (ξ'.comp (ineIncl h)).range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hle : ξ'.range ≤ (ξ'.comp (ineIncl h)).range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
    refine ⟨t, ?_⟩
    conv_rhs => rw [ht, map_mul, map_zpow, h1, _root_.one_zpow, one_mul]
    rfl
  have hr' : Finite ξ'.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have := mem_of_toAb_eq_one h ξ'.ker inferInstance hop (fun s t => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (ξ' s) (ξ' t)]
    group) σ hσ
  rw [← h0 σ (deg_eq_zero_of_toAb_eq_one h σ hσ)]
  exact this

end GlobalTheory.WeilCharKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOneStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothWeilChar_eq_one_of_toAbsGaloisAb_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ), GlobalTheory.WeilDeligne.IsSmooth ξ → ∀ σ : Weil h, GlobalTheory.HeckeGal.toAb E Ω σ = 1 → ξ σ = 1 := by
  first | exact @GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one | exact GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one | (intros; apply GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerUnramifiedOfVanishInertiaGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerUnramifiedOfVanishInertiaGenerators
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeUnr

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem vanish (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hρ : ∀ g ∈ DecV N p, ∀ m, ρ g m = m) (z : Z1 ρ)
    (hz : z.1 γ = 0) : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), z.1 τ = 0 := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ, hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ R W ρ 0 0 h4 (mul_zero _)
    (fun τ hτ m => by rw [mul_zero, zero_smul, add_zero]; exact hρ τ (Ine_le_Dec _ hτ) m)
    (fun m => by rw [zero_smul, add_zero]; exact hρ σ hσ.1 m) z).2 rfl hz

theorem selC_of_vanish : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → ∀ (Q Q' : Finset (PlE D.host)), (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (two X γ b) = 0) → SelC bkP i s κ Y Q f := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp A _ _ κ hK hκ hκp Q Q' hQ Y _ _ _ _ f hf hγ
  obtain ⟨z, rfl, hz⟩ := hf
  refine ⟨z, rfl, ?_⟩
  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul A]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL A κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have a1 := vanish hT.1 hl hM hp (repOn (Tgl i s) κ Y) h4
    (fun g hg m => by rw [htr g (hdec hg), hκp g hg, Units.val_one, one_smul]) z (hγ false)
  have a2 := vanish hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) h4
    (fun g hg m => by
      change repOn (Tgl i s) κ Y (cConj X g) m = m
      rw [htr _ ((hL.1.2.2.1 g _ (cConj_apply X g)).1 (hdec hg)), antiHom_cConj X hκ, hκp g hg, inv_one, Units.val_one,
        one_smul])
    ⟨fun g => z.1 (cConj X g), z.2.1.comp (GlobalTheory.ResConjTriv.continuous_cConj X), fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩ (hγ true)
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hz v
  refine GlobalTheory.Growth.mem_bkCond_of hv fun _ h3 => ?_
  by_cases h2 : v ∈ Spl i ∪ (Q' : Set (PlE D.host))
  · rcases h2 with h2 | h2
    · exact absurd (Or.inl h2) h3
    · rcases (hQ v).1 h2 with h5 | rfl | h5
      · exact absurd (Or.inr h5) h3
      · exact Or.inr (GlobalTheory.ResUnr.res_mem_unrAt _ z _ 0 fun τ hτ => by rw [a1 τ hτ, map_zero, sub_self])
      · exact Or.inr (GlobalTheory.ResUnr.res_mem_unrAt_of_conj X h5 _ z a2)
  · exact Or.inl h2

end GlobalTheory.NewPrimeUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerUnramifiedOfVanishInertiaGeneratorsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmer_unramified_of_vanish_inertia_generators : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → ∀ (Q Q' : Finset (PlE D.host)), (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (two X γ b) = 0) → SelC bkP i s κ Y Q f := by
  first | exact @GlobalTheory.NewPrimeUnr.selC_of_vanish | exact GlobalTheory.NewPrimeUnr.selC_of_vanish | (intros; apply GlobalTheory.NewPrimeUnr.selC_of_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOdd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponents
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel.OddBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem residual_bound_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → ResBound bkP i s) → ResidualBoundOddPrimes bkP := by
  intro D N X bkP hAB hCh hRB i hl T hT
  obtain ⟨R, hR⟩ := hCh i T hT
  refine ⟨R, 4 * D.R.r * R, 4 * D.R.r * R + 2, fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hlt : 4 * D.R.r * R + 2 < X.l i ^ M := lt_of_le_of_lt hM (Nat.lt_pow_self hp.one_lt)
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, -⟩ := GlobalTheory.T.exists_open_normal_subgroup_under_inertia D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A R h
    (fun a => ⟨hLH (hh a), hLζ _ (hh a)⟩)
  choose φ g hφ hg using hFr
  have mono : ∀ V : Subgroup (GE N), U ⊓ H' ≤ V → Steps X i M V z P (fun q => d (P q)) := fun V hV =>
    ⟨fun a σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hV hg, hSt.2⟩
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  refine ⟨P, hAux, mono H' inf_le_right, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hPos : Position i s M P (fun q => d (P q)) φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) := by
    refine ⟨⟨fun q v hv => ?_, hAux.2⟩, ⟨z, L, hz, hLs s hs, mono L hUL'⟩, fun a => ⟨fun k hk => ?_, hφ a, hcj a⟩⟩
    · obtain ⟨h1, h2, h3, h4, -, h6⟩ := hAux.1 q v hv
      exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩
    · exact (hLs s hs).2.2.2.2 k (dec_le_of_frob_mem (N.plOm.2 _) (hφ a) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL a) hk)
  have hc := hco φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) (fun a => ⟨hcj a, g a, (hg a).1⟩) s hs
  rw [if_pos hl] at hc
  obtain ⟨m, hm, hu⟩ := (hRB i s (hT s hs) M R P _ φ _ Q hlt hPos hQ a Φ hΦ).1 hc F hF
  exact ⟨m, hm, (IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu).le⟩

end GlobalTheory.ResSel.OddBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponentsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_bound_of_components : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → ResBound bkP i s) → ResidualBoundOddPrimes bkP := by
  first | exact @GlobalTheory.ResSel.OddBound.residual_bound_of_parts | exact GlobalTheory.ResSel.OddBound.residual_bound_of_parts | (intros; apply GlobalTheory.ResSel.OddBound.residual_bound_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem residual_bound_of_parts : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  intro hC hPT hCD hT hLF hLT hLE hGF hGE hU hA _ D N X bkP
  have hgw : ∀ i s, GalHyp bkP i s → EqDim bkP i s := fun i s h =>
    GlobalTheory.T.residual_selmer_finrank_eq_dual hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h
  refine GlobalTheory.T.residual_bound_of_components D N X bkP (fun i => GlobalTheory.T.exists_auxiliary_primes_prescribed_frobenius hC D N X i)
    (fun i => GlobalTheory.T.exists_elements_selmerForms_small_corank hGF D N X bkP i fun s h =>
      ⟨GlobalTheory.T.cocycleFormsSpan_oddResidueChar D N X bkP i s h, GlobalTheory.T.span_two_of_galois_hypothesis D N X bkP i s h, hgw i s h⟩)
    (fun i s h => ?_)
  have hk := GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems hLF hLT hLE hT D N X bkP i s h
  exact GlobalTheory.T.residual_selmer_determinant_order_bound hT D N X bkP i s h hk
    (GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h hk) (hgw i s h)

end GlobalTheory.ResSel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOddStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualSelmerBound_of_auxiliaryPrimes_odd : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  first | exact @GlobalTheory.ResSel.residual_bound_of_parts | exact GlobalTheory.ResSel.residual_bound_of_parts | (intros; apply GlobalTheory.ResSel.residual_bound_of_parts <;> assumption)
end
end
