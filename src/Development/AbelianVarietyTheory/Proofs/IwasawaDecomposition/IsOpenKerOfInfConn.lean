module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
public import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

theorem lPow_diagUnits (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    lPow ι n (diagUnits E k) = ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ := by
  classical
  let J : HeightOneSpectrum (𝓞 E) → Type := fun v => {j : v.adicCompletion E →+* Qbar l // Continuous j}
  let res : (Σ v, J v) → (E →+* ℂ) := fun p =>
    (ι.toRingHom.comp p.2.1).comp (algebraMap E (p.1.adicCompletion E))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    have h1 : j.1.comp (algebraMap E (v.adicCompletion E)) = j'.1.comp (algebraMap E (v'.adicCompletion E)) := by
      ext a
      exact ι.injective (DFunLike.congr_fun h a)
    obtain rfl := GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq E l v v' j.1 j'.1 j.2 j'.2 h1
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap E v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h1 a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp φ)
    obtain ⟨j, hj, e⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l _ v hv
    refine ⟨⟨v, j, hj⟩, ?_⟩
    ext a
    have := DFunLike.congr_fun e a
    show ι (j (algebraMap E _ a)) = φ a
    rw [show j (algebraMap E _ a) = ι.symm (φ a) from this, ι.apply_symm_apply]
  haveI : Fintype (Σ v, J v) := Fintype.ofInjective res hinj
  haveI : ∀ v, Fintype (J v) := fun v => @Fintype.ofFinite _ (finite_contEmb (l := l) v)
  let F : (Σ v, J v) → Qbar l := fun p => ι.symm (res p (k : E)) ^ n (res p)
  have h1 : ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ = ∏ p, F p :=
    (Fintype.prod_bijective res ⟨hinj, hsurj⟩ F _ fun _ => rfl).symm
  have h2 : ∀ v, locPow ι n v (((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).2 v) = ∏ j : J v, F ⟨v, j⟩ := by
    intro v
    unfold locPow
    rw [finprod_eq_prod_of_fintype]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact (ι.symm_apply_apply _).symm
  rw [h1, ← Finset.prod_fiberwise_of_maps_to (t := Finset.univ.image Sigma.fst) (g := Sigma.fst)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  unfold lPow
  simp only [h2]
  rw [finprod_eq_prod_of_mulSupport_subset (s := Finset.univ.image (Sigma.fst : (Σ v, J v) → _))]
  · refine Finset.prod_congr rfl fun v _ => ?_
    refine Finset.prod_bij (fun j _ => (⟨v, j⟩ : Σ v, J v)) (fun j _ => by simp) (fun a _ b _ h => ?_) ?_
      (fun _ _ => rfl)
    · exact eq_of_heq (Sigma.mk.inj h).2
    · rintro ⟨w, j⟩ hp
      obtain rfl : w = v := (Finset.mem_filter.mp hp).2
      exact ⟨j, Finset.mem_univ _, rfl⟩
  · intro v hv
    obtain ⟨j, -, -⟩ := Finset.exists_ne_one_of_prod_ne_one hv
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨v, j⟩, Finset.mem_univ _, rfl⟩)

abbrev inlInf (E : Type) [Field E] [NumberField E] : (InfiniteAdeleRing E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))

abbrev inrFin (E : Type) [Field E] [NumberField E] : (FiniteAdeleRing (𝓞 E) E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))

theorem continuous_inlInf : Continuous (inlInf E) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem continuous_inrFin : Continuous (inrFin E) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

theorem infDiag_eq (k : Eˣ) :
    infDiag k = inlInf E (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) := by
  classical
  have h : ∀ y : (InfiniteAdeleRing E)ˣ, inlInf E y = ∏ w : InfinitePlace E,
      infIdele E w (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) := by
    intro y
    have : y = ∏ w : InfinitePlace E, (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) w)
        (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) : (InfiniteAdeleRing E)ˣ) := by
      apply Units.ext
      rw [Units.coe_prod]
      exact (Finset.univ_prod_mulSingle (y : InfiniteAdeleRing E)).symm
    exact (congrArg (inlInf E) this).trans (map_prod (inlInf E) _ _)
  rw [h, infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem IsAlgPos.eq_infPow {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) {x : Ideles E}
    (hx : x ∈ infConn E) : ((χ.1 x : ℂˣ) : ℂ) = infPow n x := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  have hcl : IsClosed {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)} :=
    isClosed_eq (χ.2.1.comp continuous_inlInf) (hf.comp continuous_inlInf)
  have hmem := (denseRange_units_inf E).open_subset_closure_inter (isOpen_connectedComponentOfOne_inf E) hy
  have : y ∈ {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)} := by
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hk, k, rfl⟩
    apply Units.ext
    show ((χ.1 (inlInf E _) : ℂˣ) : ℂ) = ((f (inlInf E _) : ℂˣ) : ℂ)
    rw [hfe, ← infDiag_eq]
    have h1 := h k (pos_of_mem_connectedComponentOfOne E k hk)
    rw [← infPow_diagUnits E n k] at h1
    refine Eq.trans h1 ?_
    rw [infDiag_eq]
    rfl
  rw [← hfe]
  exact congrArg Units.val this

theorem isOpen_ker_of_infConn (θ : Ideles E →* ℂˣ) (hθ : Continuous θ) (h : ∀ x ∈ infConn E, θ x = 1) :
    IsOpen (θ.ker : Set (Ideles E)) := by
  let p : Ideles E →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  let q : Ideles E →* (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hp : Continuous p := Continuous.units_map _ continuous_fst
  have hq : Continuous q := Continuous.units_map _ continuous_snd
  have ho := ((isOpen_connectedComponentOfOne_inf E).preimage hp).inter
    ((show IsOpen ((θ.comp (inrFin E)).ker : Set (FiniteAdeleRing (𝓞 E) E)ˣ) from
      GlobalTheory.CuspRep.isOpen_ker_finIdele E (θ.comp (inrFin E)) (hθ.comp continuous_inrFin)).preimage hq)
  refine θ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨?_, ?_⟩) ?_)
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rintro x ⟨h1, h2⟩
    have e : x = inlInf E (p x) * inrFin E (q x) :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h3 : θ (inrFin E (q x)) = 1 := h2
    show θ x = 1
    rw [e, map_mul, h3, mul_one]
    exact h _ ⟨_, h1, rfl⟩

theorem lPow_of_mem_infConn (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) {x : Ideles E} (hx : x ∈ infConn E) :
    lPow ι n x = 1 := by
  obtain ⟨y, -, rfl⟩ := hx
  exact finprod_eq_one_of_forall_eq_one fun v => locPow_one ι n v

theorem IsGlobalArtin.exists_isLAdicOf {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) :
    ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r := by
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  obtain ⟨g, hg, hge⟩ := exists_lPow_hom E l ι n
  let θ : Ideles E →* ℂˣ := χ.1 * f⁻¹
  have hθ : Continuous θ := χ.2.1.mul hf.inv
  have hθe : ∀ x, ((θ x : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹ := fun x => by
    rw [← hfe, ← Units.val_inv_eq_inv_val]
    rfl
  have hθ1 : ∀ x ∈ infConn E, θ x = 1 := fun x hx => by
    have : χ.1 x = f x := Units.ext (by rw [hfe, h.eq_infPow hx])
    show χ.1 x * (f x)⁻¹ = 1
    rw [this, mul_inv_cancel]
  let θ' : Ideles E →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp θ
  have hθ' : Continuous θ' := continuous_of_isOpen_ker' θ' (Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) (isOpen_ker_of_infConn θ hθ hθ1))
  let ψ : Ideles E →* (Qbar l)ˣ := θ' * g
  have hψ : Continuous ψ := hθ'.mul hg
  have hψe : ∀ x, ((ψ x : (Qbar l)ˣ) : Qbar l) =
      ι.symm (((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹) * lPow ι n x := fun x => by
    rw [← hθe, ← hge]
    rfl
  have hker : art.ker ≤ ψ.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_singleton.preimage hψ)
    · rintro _ ⟨k, rfl⟩
      apply Units.ext
      rw [hψe, χ.2.2 k, infPow_diagUnits, lPow_diagUnits, Units.val_one, one_mul, map_inv₀, map_prod]
      simp only [map_zpow₀]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ ?_)
      simp
    · intro x hx
      apply Units.ext
      rw [hψe, ← hθe, hθ1 x hx, lPow_of_mem_infConn ι n hx]
      simp
  let ρ : Gab E Ω →* (Qbar l)ˣ := art.liftOfSurjective ha.quot.surjective ⟨ψ, hker⟩
  have hρ : ∀ x, ρ (art x) = ψ x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨ψ, hker⟩ x
  have hρc : Continuous ρ := ha.quot.isQuotientMap.continuous_iff.mpr (hψ.congr fun x => (hρ x).symm)
  refine ⟨ρ.comp (toAb E Ω), hρc.comp QuotientGroup.continuous_mk, fun x σ hx => ?_⟩
  rw [MonoidHom.comp_apply, ← hx, hρ, hψe]

end GlobalTheory.HeckeGal

namespace GlobalTheory.Published

open GlobalTheory.HeckeGal

theorem GlobalArtinReciprocity.heckeLAdicCharacter : GlobalArtinReciprocity → HeckeLAdicCharacter := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  refine ⟨art, ha, fun l _ ι χ n h => ?_⟩
  obtain ⟨r, hr, hf⟩ := ha.exists_isLAdicOf ι h
  exact ⟨r, ⟨hr, hf⟩, fun r' h' => h'.2.unique ha.quot.surjective hf⟩

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal
open GlobalTheory.AntiRamConj GlobalTheory.Mem.Chr
open scoped Pointwise

namespace GlobalTheory.AntiLAdic

section Galois

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (cc : Ω ≃+* Ω)
  (hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y)

def conjHom : Formalism.ConjugateSelfDual.G E Ω →* Formalism.ConjugateSelfDual.G E Ω where
  toFun := conjAut cc hc
  map_one' := by
    ext x
    exact cc.apply_symm_apply x
  map_mul' g h := by
    ext x
    change cc (g (h (cc.symm x))) = cc (g (cc.symm (cc (h (cc.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem conjHom_apply (g : Formalism.ConjugateSelfDual.G E Ω) (x : Ω) : conjHom cc hc g x = cc (g (cc.symm x)) := rfl

theorem _root_.GlobalTheory.AntiLAdic.isFrob_conjHom [NumberField E] {B : ValuationSubring Ω} {q : ℕ} {σ : _root_.Formalism.ConjugateSelfDual.G E Ω} (hσ : _root_.Formalism.ConjugateSelfDual.IsFrob (F := E) B q σ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob (F := E) (_root_.GlobalTheory.AntiRamConj.moveVal cc B) q (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) := by
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, _root_.GlobalTheory.AntiRamConj.mem_moveVal,
      ← map_inv, AlgEquiv.smul_def, _root_.GlobalTheory.AntiLAdic.conjHom_apply,
      RingEquiv.symm_apply_apply, _root_.GlobalTheory.AntiRamConj.mem_moveVal]
    conv_rhs => rw [← hdec]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  · intro x hx
    rw [ValuationSubring.valuation_le_one_iff, _root_.GlobalTheory.AntiRamConj.mem_moveVal] at hx
    rw [_root_.GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_pow,
      _root_.GlobalTheory.AntiLAdic.conjHom_apply, RingEquiv.symm_apply_apply]
    exact hval _ ((ValuationSubring.valuation_le_one_iff _ _).mpr hx)

theorem _root_.GlobalTheory.AntiLAdic.continuous_conjHom [Algebra.IsAlgebraic E Ω] : Continuous (_root_.GlobalTheory.AntiLAdic.conjHom cc hc) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro s hs
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).mp hs
  let b := Module.finBasis E L
  let S : Set Ω := Set.range (fun i => cc.symm (b i : Ω))
  refine (krullTopology_mem_nhds_one_iff E Ω _).mpr ⟨IntermediateField.adjoin E S, ?_, ?_⟩
  · haveI : Finite S := Set.finite_range _ |>.to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  · intro σ hσ
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
    show _root_.GlobalTheory.AntiLAdic.conjHom cc hc σ ∈ s
    apply hLs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [_root_.GlobalTheory.AntiLAdic.conjHom_apply]
    suffices h : cc.symm x ∈ IntermediateField.adjoin E S by
      rw [hσ _ h, RingEquiv.apply_symm_apply]
    have hsum : x = ∑ i, algebraMap E Ω (b.repr ⟨x, hx⟩ i) * (b i : Ω) := by
      have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, Algebra.smul_def] at h
      exact h.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine sum_mem (fun i _ => ?_)
    rw [map_mul]
    obtain ⟨y, hy⟩ := hc (b.repr ⟨x, hx⟩ i)
    rw [hy]
    exact mul_mem (IntermediateField.algebraMap_mem _ y)
      (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)

end Galois

section Places

variable {E : Type} [Field E] [NumberField E]

theorem _root_.GlobalTheory.AntiLAdic.conjPl_symm {c : E ≃+* E} (hcc : ∀ x, c (c x) = x) {v v' : HeightOneSpectrum (𝓞 E)} (h : _root_.GlobalTheory.Mem.Chr.ConjPl c v v') :
    _root_.GlobalTheory.Mem.Chr.ConjPl c v' v := by
  intro x
  rw [← h (c x), hcc]

theorem _root_.GlobalTheory.AntiLAdic.normV_conjPl {c : E ≃+* E} {v v' : HeightOneSpectrum (𝓞 E)} (h : _root_.GlobalTheory.Mem.Chr.ConjPl c v v') : _root_.Formalism.ConjugateSelfDual.normV v' = _root_.Formalism.ConjugateSelfDual.normV v := by
  rw [_root_.GlobalTheory.Mem.Chr.conjPl_iff_comap] at h
  have hmap : v'.asIdeal = v.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv c) := by
    rw [h, Ideal.map_comap_of_surjective _ (RingEquiv.surjective _)]
  unfold _root_.Formalism.ConjugateSelfDual.normV
  exact (Nat.card_congr
    (Ideal.quotientEquiv v.asIdeal v'.asIdeal (NumberField.RingOfIntegers.mapRingEquiv c) hmap).toEquiv).symm

theorem _root_.GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl {Ω : Type} [Field Ω] [Algebra E Ω] {c : E ≃+* E} {cc : Ω ≃+* Ω}
    (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : _root_.GlobalTheory.Mem.Chr.ConjPl c v v') {B : ValuationSubring Ω} (hB : _root_.Formalism.ConjugateSelfDual.IsPlaceOver B v) : _root_.Formalism.ConjugateSelfDual.IsPlaceOver (_root_.GlobalTheory.AntiRamConj.moveVal cc B) v' := by
  intro x
  rw [_root_.GlobalTheory.AntiRamConj.moveVal_lt_one]
  have hx : cc.symm (algebraMap E Ω x) = algebraMap E Ω (c.symm x) := by
    rw [RingEquiv.symm_apply_eq, hcc, RingEquiv.apply_symm_apply]
  rw [hx]
  let y : 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv c.symm x
  have hy : (y : E) = c.symm x := rfl
  have key := (_root_.GlobalTheory.Mem.Chr.conjPl_iff_mem c v v').mp h y x
    (by rw [hy, RingEquiv.apply_symm_apply])
  rw [← key, ← hB y, hy]

theorem _root_.GlobalTheory.AntiLAdic.val_mul_val_conj {F : Type} [Field F] [NumberField F] [Algebra F E] (c : E ≃ₐ[F] E)
    (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 F)) k)
    (χ : _root_.Formalism.L2.Host.HChar E) (ht : χ.TrivOn F) {v v' : HeightOneSpectrum (𝓞 E)} (h : _root_.GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv v v')
    (hu : χ.UnrAt v) (hu' : χ.UnrAt v') : χ.val v * χ.val v' = 1 := by
  classical
  obtain ⟨u, hvu⟩ : ∃ u, HeightOneSpectrum.under (𝓞 F) v = u := ⟨_, rfl⟩
  have hv'u : HeightOneSpectrum.under (𝓞 F) v' = u :=
    ((_root_.GlobalTheory.Mem.Chr.under_eq_iff_conjPl c h2 hne v v').mpr (Or.inr h)).trans hvu
  have hmem : ∀ P, P ∈ _root_.Formalism.L2.Host.aboveF (L := E) F u ↔ P = v ∨ P = v' := by
    intro P
    unfold _root_.Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ← hvu,
      _root_.GlobalTheory.Mem.Chr.under_eq_iff_conjPl c h2 hne v P]
    constructor
    · rintro (hP | hP)
      · exact Or.inl hP
      · exact Or.inr ((_root_.GlobalTheory.Mem.Chr.existsUnique_conjPl _ v).unique hP h)
    · rintro (hP | hP)
      · exact Or.inl hP
      · exact Or.inr (hP ▸ h)
  have hloc : ∀ P, HeightOneSpectrum.under (𝓞 F) P = u → χ.UnrAt P →
      χ.locK P (_root_.Formalism.L2.Host.upF F (_root_.Formalism.L2.Host.unif u)) = χ.val P := by
    intro P hP hPu
    rw [_root_.GlobalTheory.HeckeProduct.locK_unr χ hPu, hr, hP, _root_.GlobalTheory.Mem.Chr.ordF_unif_self,
      zpow_one]
  have hprod := ht.1 u (_root_.Formalism.L2.Host.unif u)
  rw [_root_.Formalism.L2.Host.HChar.resFin_apply] at hprod
  by_cases hvv : v = v'
  · subst hvv
    have hset : _root_.Formalism.L2.Host.aboveF (L := E) F u = {v} := by
      ext P
      rw [hmem, Finset.mem_singleton, or_self]
    rw [hset, Finset.prod_singleton, hloc v hvu hu] at hprod
    rw [hprod, one_mul]
  · have hset : _root_.Formalism.L2.Host.aboveF (L := E) F u = {v, v'} := by
      ext P
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
    rw [hset, Finset.prod_pair hvv, hloc v hvu hu, hloc v' hv'u hu'] at hprod
    exact hprod

end Places

theorem _root_.GlobalTheory.AntiLAdic.antiHom_of_trivOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ x, c (c x) = x) → (∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 F)) k) → ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (cc : Ω ≃+* Ω), (∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) → ∀ (art : _root_.Neutral.B1.Ideles E →* _root_.GlobalTheory.HeckeGal.Gab E Ω), _root_.GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (l : ℕ) [Fact l.Prime] (ι : _root_.Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ) (χ : _root_.Formalism.L2.Host.HChar E) (n : (E →+* ℂ) → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* (_root_.Formalism.ConjugateSelfDual.Qbar l)ˣ), Continuous r → _root_.GlobalTheory.HeckeGal.IsLAdicOf art ι χ n r → χ.TrivOn F → _root_.Formalism.BasicNotions.AntiHom cc r := by
  intro F E _ _ _ _ _ c h2 hne hinv hr Ω _ _ _ cc hcc art hart l _ ι χ n r hrc hlad ht
  classical
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x =>
    ⟨c.symm x, by rw [RingEquiv.symm_apply_eq, hcc, AlgEquiv.apply_symm_apply]⟩
  have hinv' : ∀ x, c.toRingEquiv (c.toRingEquiv x) = x := fun x => hinv x
  have hex := _root_.GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv
  choose conjPrime₂ hconjP using fun w => (hex w).exists
  have hconj2 : ∀ w, conjPrime₂ (conjPrime₂ w) = w := fun w =>
    (hex (conjPrime₂ w)).unique (hconjP (conjPrime₂ w)) (_root_.GlobalTheory.AntiLAdic.conjPl_symm hinv' (hconjP w))
  have hlfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hI : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors hI).subset (fun w hw => Ideal.dvd_span_singleton.mpr hw)
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ χ.UnrAt w ∨ (l : 𝓞 E) ∈ w.asIdeal}.Finite :=
    (_root_.GlobalTheory.Mem.UnrAe.finite_ramified χ).union hlfin
  set T := hfin.toFinset with hT
  have hgood : ∀ w ∉ T, χ.UnrAt w ∧ (l : 𝓞 E) ∉ w.asIdeal := by
    intro w hw
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hw
    exact hw
  let φ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (_root_.Formalism.ConjugateSelfDual.Qbar l)ˣ := (r.comp (_root_.GlobalTheory.AntiLAdic.conjHom cc hc)) * r
  have hφc : Continuous φ := by
    show Continuous (fun g => r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc g) * r g)
    exact (hrc.comp (_root_.GlobalTheory.AntiLAdic.continuous_conjHom cc hc)).mul hrc
  have hφ : φ = 1 := by
    refine _root_.GlobalTheory.FrobDense.eq_one_of_frob E Ω art hart _ φ hφc
      (T ∪ T.image conjPrime₂) ?_
    intro v hv A hA σ hσ
    rw [Finset.mem_union, not_or] at hv
    have hv' : conjPrime₂ v ∉ T := by
      intro hmemT
      exact hv.2 (Finset.mem_image.mpr ⟨conjPrime₂ v, hmemT, hconj2 v⟩)
    obtain ⟨hU, hl⟩ := hgood v hv.1
    obtain ⟨hU', hl'⟩ := hgood (conjPrime₂ v) hv'
    have hA' := _root_.GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl hcc (hconjP v) hA
    have hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob (F := E) (_root_.GlobalTheory.AntiRamConj.moveVal cc A) (_root_.Formalism.ConjugateSelfDual.normV (conjPrime₂ v))
        (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) := by
      rw [_root_.GlobalTheory.AntiLAdic.normV_conjPl (hconjP v)]
      exact _root_.GlobalTheory.AntiLAdic.isFrob_conjHom cc hc hσ
    have r1 := hlad.frob_unr hart (Or.inl hl) hU hA hσ
    have r2 := hlad.frob_unr hart (Or.inl hl') hU' hA' hσ'
    have hval := _root_.GlobalTheory.AntiLAdic.val_mul_val_conj c h2 hne hr χ ht (hconjP v) hU hU'
    show r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc σ) * r σ = 1
    apply Units.ext
    rw [Units.val_mul, r1, r2, Units.val_one, ← mul_inv, ← map_mul, ← Units.val_mul,
      mul_comm (χ.val (conjPrime₂ v)), hval, Units.val_one, map_one, inv_one]
  intro g g' hg'
  have hgg : g' = _root_.GlobalTheory.AntiLAdic.conjHom cc hc g :=
    AlgEquiv.ext fun x => by rw [hg', _root_.GlobalTheory.AntiLAdic.conjHom_apply]
  have h1 : r (_root_.GlobalTheory.AntiLAdic.conjHom cc hc g) * r g = 1 := DFunLike.congr_fun hφ g
  rw [hgg]
  exact eq_inv_of_mul_eq_one_left h1

end GlobalTheory.AntiLAdic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag OverP

namespace GlobalTheory.Mem.KerDet

variable {L : Type} [Field L] [NumberField L]

theorem finPartI_localIdele (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    finPartI L (localIdele L v x) = localIdele L v x :=
  finPartI_eq_self fun _ => rfl

theorem map_finPartI_locF {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (locF F v k)) = 1 := by
  have h1 := h.1 v k
  unfold GlobalTheory.Mem.Chr.HChar.resFin at h1
  rw [MonoidHom.finsetProd_apply] at h1
  unfold locF
  rw [map_prod, map_prod, ← h1]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (finPartI_localIdele Q _)

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

open Classical in
theorem kernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (Ideles H.E)) ∧ (∀ w y, infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, diagUnits H.E (upF H.F k) ∈ KD H) ∧ ∀ χ : HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  intro R H
  refine ⟨KDq_empty H ▸ isOpen_KDq H ∅, fun w y => KDq_le_KD H ∅ (infIdele_mem_KDq H ∅ w y),
    fun k => KDq_le_KD H ∅ (diag_upF_mem_KDq H ∅ k), fun χ hT hta hu => (Subgroup.closure_le _).2 ?_⟩
  rintro a (ha | ⟨v, k, rfl⟩)
  · refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 (finPartI H.E a) (finPartI_mem_unitIdl.2 ha.1) (fun _ => rfl) fun v x hx => ?_
    have hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v := hx
    have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx']
      exact ha.1 v
    by_cases hv : ∃ k, OverP H (H.g k) v
    · obtain ⟨k, hk⟩ := hv
      refine hta v x hxu (le_exp_neg_one ?_)
      rw [hx']
      exact ha.2 k v hk
    · exact hu v (not_exists.1 hv) x hxu
  · exact map_finPartI_locF hT v k

end GlobalTheory.Mem.KerDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactorStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag OverP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDeterminantKernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (Ideles H.E)) ∧ (∀ w y, infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, diagUnits H.E (upF H.F k) ∈ KD H) ∧ ∀ χ : HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  first | exact @GlobalTheory.Mem.KerDet.kernel_open_and_factor | exact GlobalTheory.Mem.KerDet.kernel_open_and_factor | (intros; apply GlobalTheory.Mem.KerDet.kernel_open_and_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits
open GlobalTheory.Mem.Chr hiding HChar
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding IsUnitAt ordF upF aboveF atFin atInf infDiag OverP

namespace GlobalTheory.Mem.FrameVal

theorem exists_galois_ge (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ M ≤ N := by
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  exact ⟨IntermediateField.normalClosure ℚ M ℂ, inferInstance, {}, IntermediateField.le_normalClosure M⟩

theorem exists_roots (n : ℕ) (hn : 0 < n) :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ ∀ x : ℂ, x ^ n = 1 → x ∈ N := by
  have hfin : {x : ℂ | x ^ n = 1}.Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => ?_
    simpa [Polynomial.mem_nthRoots hn] using hx
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ {x : ℂ | x ^ n = 1}, IntermediateField.finiteDimensional_adjoin fun x hx => ?_,
    fun x hx => IntermediateField.subset_adjoin _ _ hx⟩
  exact IsIntegral.of_pow hn (by rw [show x ^ n = 1 from hx]; exact isIntegral_one)

theorem valuesIn_mono {L : Type} [Field L] [NumberField L] {χ : HChar L} {s : ℝ} {M N : IntermediateField ℚ ℂ}
    (h : χ.ValuesIn s M.val.toRingHom) (hMN : M ≤ N) : χ.ValuesIn s N.val.toRingHom := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨⟨y, hMN y.2⟩, hy⟩

theorem exists_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn 0 M.val.toRingHom := by
  obtain ⟨n, hn, ho⟩ := h
  obtain ⟨N, hN, hr⟩ := exists_roots n hn
  refine ⟨N, hN, fun v _ => ⟨⟨(χ.val v : ℂ), hr _ ?_⟩, by simp [Formalism.L2.Host.HChar.valTw]⟩⟩
  have h1 : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) ho
  have h2 : χ.val v ^ n = 1 := h1 _
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem exists_of_emb {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ x, φ x ∈ M :=
  ⟨φ.toRatAlgHom.fieldRange, (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional, fun x => ⟨x, rfl⟩⟩

open Classical in
theorem frame_values : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : HFrame H e), (∀ j τ, ∃ z : ℤ, e j τ = z) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧ (∀ g x, H.emb g x ∈ M) ∧ (∀ j, (C.mu0 j).ValuesIn 0 M.val.toRingHom) ∧ C.eta.ValuesIn (1 / 2) M.val.toRingHom ∧ C.chiPsi.ValuesIn 0 M.val.toRingHom ∧ C.del.ValuesIn 0 M.val.toRingHom ∧ C.del'.ValuesIn 0 M.val.toRingHom ∧ ∀ k a, ((C.W.om k a : ℂˣ) : ℂ) ∈ M := by
  intro R H e C he
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have alg := GlobalTheory.T.algebraicHeckeChar_values_in_numberField H.F H.E c (R.Psi) (Formalism.L2.Host.embPsi H) hcm
  choose Me hMe hMe' using fun φ : H.E →+* ℂ => exists_of_emb φ
  have hmu : ∀ j, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C.mu0 j).ValuesIn 0 M.val.toRingHom := by
    intro j
    obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have := alg (C.mu0 j) n 0 hi fun i => by
      obtain ⟨z, hz⟩ := he j i
      have h1 : (n i : ℚ) = 2 * -e j i := hn i
      rw [hz] at h1
      have h2 : n i = 2 * -z := by exact_mod_cast h1
      exact ⟨-z, by rw [h2]; ring⟩
    simpa using this
  choose Mm hMm hMm' using hmu
  obtain ⟨M1, hM1, hM1'⟩ := alg C.eta (fun _ => 1) 1 C.isEta.inf fun _ => by simp
  obtain ⟨M2, hM2, hM2'⟩ := alg C.chiPsi (fun _ => 2) 0 C.isChi.inf fun _ => by simp
  rw [Int.cast_one] at hM1'
  rw [Int.cast_zero, zero_div] at hM2'
  obtain ⟨M3, hM3, hM3'⟩ := exists_of_order C.isDel.fin
  obtain ⟨M4, hM4, hM4'⟩ := exists_of_order C.isDel'.fin
  choose Mo hMo hMo' using fun k : Fin 2 => exists_roots (Nat.card (ZMod (H.g k))ˣ) Nat.card_pos
  obtain ⟨N, hN, hG, hle⟩ := exists_galois_ge ((⨆ φ, Me φ) ⊔ (⨆ j, Mm j) ⊔ (⨆ k, Mo k) ⊔ M1 ⊔ M2 ⊔ M3 ⊔ M4)
  simp only [sup_le_iff, iSup_le_iff] at hle
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hle
  refine ⟨N, hN, hG, fun g x => h1 _ (hMe' _ x), fun j => valuesIn_mono (hMm' j) (h2 j), valuesIn_mono hM1' h4,
    valuesIn_mono hM2' h5, valuesIn_mono hM3' h6, valuesIn_mono hM4' h7, fun k a => h3 k (hMo' k _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

end GlobalTheory.Mem.FrameVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag

namespace GlobalTheory.Mem.Chr

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem IsTwist.mul_twist {S : Set ℕ} {ξ ξ' : HChar H.E} (h : IsTwist H S ξ) (h' : IsTwist H S ξ') :
    IsTwist H S (ξ * ξ') := by
  obtain ⟨⟨n, hn, ho⟩, ht, hl, hr⟩ := h
  obtain ⟨⟨n', hn', ho'⟩, ht', hl', hr'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ht.mul ht', fun v => HChar.LevelLe.mul (hl v) (hl' v), fun v hv => ?_⟩
  · change (ξ * ξ') ^ (n * n') = 1
    change ξ ^ n = 1 at ho
    change ξ' ^ n' = 1 at ho'
    rw [mul_pow, pow_mul, ho, one_pow, one_mul, mul_comm n n', pow_mul, ho', one_pow]
  · by_cases h1 : ξ.UnrAt v
    · exact hr' v fun h2 => hv (fun x hx => by change ξ.loc v x * Formalism.L2.Host.HChar.loc ξ' v x = 1; rw [h1 x hx, one_mul]; exact h2 x hx)
    · exact hr v h1

theorem isTwist_of_isDelta {S : Set ℕ} {p : ℕ} {δ : HChar H.E} (hp : p.Prime) (hs : SplitsC H.E p) (hS : p ∉ S)
    (h : IsDelta (H := H) p δ) : IsTwist H S δ := by
  refine ⟨h.fin, h.triv, h.tame, fun v hv => ?_⟩
  have hv' : OverP H p v := by
    by_contra hn
    exact hv (h.unr v hn)
  obtain ⟨h1, h2, h3, -⟩ := splitsC_main R H p hp hs v hv'
  rw [h1]
  exact ⟨h3, hp, h2, hS⟩

end GlobalTheory.Mem.Chr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissible
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.IsCond
open NumberField

namespace UpperTheory.Ram

open Formalism.L2.Host Formalism.HC Formalism.HC.Der Formalism.FrobeniusOrbits

private theorem exists_aut_pow (N : ℕ) (hN : 0 < N) (u : ℕ) (hu : u.Coprime N) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, ∀ z ∈ mus N, s z = z ^ u := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨w, hw⟩ : ∃ w : Qb, IsPrimitiveRoot w N := HasEnoughRootsOfUnity.exists_primitiveRoot Qb N
  have hw' : IsPrimitiveRoot (w ^ u) N := hw.pow_of_coprime u hu
  have hc : IsConjRoot ℚ (w ^ u) w := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hw hN, ← Polynomial.cyclotomic_eq_minpoly_rat hw' hN]
  haveI : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
  obtain ⟨s, hs⟩ := hc.exists_algEquiv
  refine ⟨s, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
  rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]

private theorem exists_aut_fix (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (u : ℕ) (hu : u.Coprime N)
    (hu1 : u ≡ 1 [MOD M]) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, (∀ z ∈ mus N, s z = z ^ u) ∧ ∀ x ∈ cycQ M, s x = x := by
  have huM : u.Coprime M := by
    unfold Nat.Coprime
    rw [hu1.gcd_eq, Nat.gcd_one_left]
  obtain ⟨s, hs⟩ := exists_aut_pow (N * M) (Nat.mul_pos hN hM) u (Nat.Coprime.mul_right hu huM)
  refine ⟨s, fun z hz => hs z ?_, fun x hx => ?_⟩
  · show z ^ (N * M) = 1
    rw [pow_mul, show z ^ N = 1 from hz, one_pow]
  · unfold cycQ at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem z hz =>
      have hz' : z ^ M = 1 := hz
      rw [hs z (by show z ^ (N * M) = 1; rw [mul_comm, pow_mul, hz', one_pow]),
        pow_eq_pow_of_modEq hu1 hz', pow_one]
    | algebraMap r => exact s.commutes r
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

private theorem aut_art {φ : Frame} (H : HostRaw φ) (j : H.E →ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (s : Qb ≃ₐ[ℚ] Qb)
    (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) (x : H.E) :
    s (j x) = j (H.gal.symm (H.art u) x) := by
  let _ : Algebra H.E (Cond.Cyc H.condN) := (emb H).toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (Cond.Cyc H.condN) := IsScalarTower.of_algebraMap_eq fun x => ((emb H).commutes x).symm
  have : Algebra.IsAlgebraic H.E (Cond.Cyc H.condN) := Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let _ : Algebra H.E Qb := j.toRingHom.toAlgebra
  let Ψ0 : Cond.Cyc H.condN →ₐ[H.E] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let Ψ : Cond.Cyc H.condN →+* Qb := Ψ0.toRingHom
  have h1 : ∀ y, Ψ (emb H y) = j y := fun y => Ψ0.commutes y
  have key : (Ψ.comp (tauN H.condN u : Cond.Cyc H.condN →+* Cond.Cyc H.condN)).toRatAlgHom =
      ((s : Qb →+* Qb).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec H.condN)) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Ψ (tauN H.condN u (Cond.z H.condN)) = s (Ψ (Cond.z H.condN))
    have hz := (Cond.z_spec H.condN).pow_eq_one
    rw [tauN_root H.condN _ _ hz, map_pow, hs _ (show _ ^ H.condN = 1 by rw [← map_pow, hz, map_one])]
  rw [← h1, ← h1, emb_art]
  exact (DFunLike.congr_fun key (emb H x)).symm

private theorem exists_exact {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  rcases (H.toHostRaw.dvd_condN_iff hl).1 hd with h | rfl | rfl
  · exact H.QS_exact l hl h
  · have hN : H.condN = H.QS * H.d * H.q := mul_right_comm _ _ _
    obtain ⟨b, hb, hj⟩ := D7.exists_sign H.q_prime H.q_mod_four (-1)
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder H.toHostRaw.coprime_QSd_q 1 b
    obtain ⟨u, hu⟩ := exists_unit_modEq (dvd_refl H.condN) n
      (hN ▸ Nat.Coprime.mul_right (hn1.gcd_eq.trans (Nat.coprime_one_left _)) (hn2.gcd_eq.trans hb))
    refine ⟨u, ?_, fun h3 => ?_⟩
    · rw [show H.condN / H.q = H.QS * H.d by rw [hN, Nat.mul_div_cancel _ hl.pos]]
      exact (hu.of_dvd ⟨H.q, hN⟩).trans hn1
    · have h4 := H.flPS u
      rw [h3, D7.jac_congr ((hu.of_dvd H.toHostRaw.q_dvd_condN).trans hn2), hj] at h4
      exact absurd h4 (show ¬ ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) by decide)
  · obtain ⟨u, h1, h2⟩ := exists_art_iod H.toHostRaw
    refine ⟨u, ?_, fun h3 => R.toFrame.iod_ne_one (h2.symm.trans h3)⟩
    rwa [show H.condN / H.d = H.QS * H.q from Nat.mul_div_cancel _ hl.pos]

end UpperTheory.Ram

theorem UpperTheory.Ram.isCond_condN :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (j : H.E →ₐ[ℚ] Formalism.L2.Host.Qb),
      Formalism.L2.Host.IsCond j.fieldRange H.condN := by
  intro R H j
  have hN : 0 < H.condN := Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero
  refine ⟨?_, fun M hM hle => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact H.toHostRaw.image_mem_of_roots j.toRingHom (Formalism.L2.Host.cycQ H.condN).toSubfield
      (fun y hy => IntermediateField.subset_adjoin ℚ _ hy) x
  · by_contra hn
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left H.condN M
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hn (hk ▸ Nat.gcd_dvd_right _ _)
    obtain ⟨l, hl, m, rfl⟩ := Nat.exists_prime_and_dvd hk1
    have hld : l ∣ H.condN := ⟨Nat.gcd H.condN M * m, hk.trans (by ring)⟩
    have hg : Nat.gcd H.condN M ∣ H.condN / l :=
      ⟨m, Nat.div_eq_of_eq_mul_right hl.pos (hk.trans (by ring))⟩
    obtain ⟨u, hu1, hu2⟩ := exists_exact H hl hld
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder' (hu1.of_dvd hg)
    obtain ⟨s, hs1, hs2⟩ := exists_aut_fix H.condN M hN hM n
      (hn1.gcd_eq.trans (ZMod.val_coe_unit_coprime u)) hn2
    apply hu2
    rw [← H.gal.symm.map_eq_one_iff]
    refine AlgEquiv.ext fun x => j.injective ?_
    have h := aut_art H.toHostRaw j u s (fun z hz => by rw [hs1 z hz, pow_eq_pow_of_modEq hn1 hz]) x
    exact h.symm.trans (hs2 _ (hle ⟨x, rfl⟩))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldsIsConductorPrimesModulus
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem Base.fields_isCond : ∀ (B : Base) (X : PreX B.toPre), B.fields.IsCond (B.primes X).cond := by
  intro B X j
  exact UpperTheory.Ram.isCond_condN B.host j

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissible
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.DatLaws

theorem _root_.GlobalTheory.Mem.DatLaws.dat_ok : ∀ (B : _root_.GlobalTheory.Mem.Base)
    (X : _root_.GlobalTheory.Mem.PreX B.toPre)
    (Ch : _root_.Formalism.L2.Col.Chars B.fields (B.primes X) B.R.m),
    Ch.Ok → Ch.FromHecke B.wts B.embLL →
      (B.dat X Ch).Ok := by
  intro B X Ch hCh hH
  constructor
  case fields => exact _root_.GlobalTheory.Mem.FieldsLaws.fields_ok B
  case fieldsConditions => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  case embeddingStarConj => exact _root_.GlobalTheory.Mem.Base.baseData_embedding_conj B X Ch
  case f_eq => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  case primes => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).1
  case piG_cong => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).2
  case cond => exact _root_.GlobalTheory.Mem.Base.fields_isCond B X
  case chars => exact hCh
  case hecke => exact hH
  case wts => exact _root_.GlobalTheory.Mem.Base.wts_isOk B
  case e_even => exact _root_.GlobalTheory.Mem.Base.dat_e_even B X Ch
  case sizes => exact _root_.GlobalTheory.Mem.Base.primes_sizes B X

end GlobalTheory.Mem.DatLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissibleStatement
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBaseData_admissible : ∀ (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m), Ch.Ok → Ch.FromHecke B.wts B.embLL → (B.dat X Ch).Ok := by
  first | exact @GlobalTheory.Mem.DatLaws.dat_ok | exact GlobalTheory.Mem.DatLaws.dat_ok | (intros; apply GlobalTheory.Mem.DatLaws.dat_ok <;> assumption)
end
end
