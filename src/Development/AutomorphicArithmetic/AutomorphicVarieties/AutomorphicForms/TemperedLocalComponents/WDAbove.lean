module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneCharacterTwistPeriod

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallinePeriodRingProperties
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp

theorem UpperTheory.crystalline_period_ring_properties :
    UpperTheory.V.Af.Wd.BrFacts := by
  classical
  intro F Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hj
  refine ⟨fun c => ?_, fun L s => ?_, fun M hM => ?_⟩
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_one_iff.2 isFrob_frob) c
    simpa using h1
  · have h2 := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (UpperTheory.V.Loc.PP l) Bw.j _ _ (Bw.e_comm s)
    exact (congrArg (algebraMap ℚ_[l] (Om l)) h2)
  · have hM0 : M ≠ 0 := by omega
    have hfin : ({x : Om l | x ^ M = 1}).Finite := by
      refine (Polynomial.nthRoots M (1 : Om l)).toFinset.finite_toSet.subset fun x hx => ?_
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hM0)] using hx
    haveI := hfin.to_subtype
    have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    refine ⟨⟨_, hfd⟩, fun s hs ζ hζ => Bw.j.injective ?_⟩
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _
      (IntermediateField.subset_adjoin _ _ (show Bw.j ζ ^ M = 1 by rw [← map_pow, hζ, map_one]))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationModelOverFiniteExtension
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem exists_lift {Γ k K : Type} [Group Γ] [Field k] [Field K] [Algebra k K] (L : IntermediateField k K)
    (ψ : Γ →* Kˣ) (hψ : ∀ g, (ψ g : K) ∈ L) : ∃ ψL : Γ →* (↥L)ˣ, ∀ g, ((ψL g : ↥L) : K) = ψ g :=
  ⟨MonoidHom.toHomUnits (((Units.coeHom K).comp ψ).codRestrict L hψ), fun _ => rfl⟩

private theorem toMatrix_repE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} (L : FinExt l) (r : ↥Gw →* GL (Fin m) ↥L.1) (g : ↥(GK Bw.Kw)) :
    LinearMap.toMatrix (Pi.basisFun ↥L.1 (Fin m)) (Pi.basisFun ↥L.1 (Fin m)) (Bw.repE L r g) =
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) := by
  have e : Bw.repE L r g = Matrix.toLin' (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) :=
    LinearMap.ext fun _ => rfl
  rw [e, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem UpperTheory.galois_representation_model_over_finite_extension :
    UpperTheory.V.Af.Wd.Model := by
  intro F Ω _ _ _ _ _ l _ ι n r w A h O _ _ _ Bw hj κ χ hχ hfl hr
  obtain ⟨p, hp⟩ := hfl
  let r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l) :=
    (MulAut.conj p).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)
  have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun _ => rfl
  have hc := GlobalTheory.T.fontaineParameter_invariant_under_conjugation F Ω l ι n (Loc.PP l) (Loc.AIP l) (Loc.tiedP l) w A h O Bw hj
    (r.comp (Dec (F := F) A).subtype) r' p hr' hr
  obtain ⟨hpst, hwd⟩ := hc
  have hm := wdAt_of_isPstAt ι Bw h hj hpst
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := hm
  have hL : ∃ L : FinExt l, L₁.1 ≤ L.1 ∧ ∀ i s, (χ i s : Om l) ∈ L.1 := by
    have hfin : (⋃ i, Units.val '' Set.range (χ i)).Finite := Set.finite_iUnion fun i => (hχ i).image _
    haveI : Finite ↥(⋃ i, Units.val '' Set.range (χ i)) := hfin
    refine ⟨supExt L₁ ⟨IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩,
      le_sup_left, fun i s => ?_⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)) ≤ _)
      (IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨i, _, ⟨s, rfl⟩, rfl⟩))
  obtain ⟨L, h₁, hχL⟩ := hL
  have hm₂ := hm₁.enlarge h₁
  have hp₂ := GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge (Loc.PP l) Bw h₁ r₁ hp₁
  have e₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge (Loc.PP l) ι Bw h hj h₁ r₁ hp₁
  generalize mapRep (IntermediateField.inclusion h₁).toRingHom r₁ = r₂ at hm₂ hp₂ e₂
  have er : ∀ s i j, (p * r (s : ↥(Dec (F := F) A)) * p⁻¹ : GL (Fin n) (Qbar l)) i j =
      (((r₂ s : Matrix (Fin n) (Fin n) ↥L.1) i j : ↥L.1) : Om l) :=
    fun s i j => by rw [← hr', ← hm₂.2]; rfl
  have hκL : ∀ i s, (κ i s : Om l) ∈ L.1 := fun i s => by
    rw [← (hp s).2 i, er]; exact SetLike.coe_mem _
  choose κL hκ using fun i => exists_lift L.1 ((κ i).comp Bw.e.symm.toMonoidHom) fun g => hκL i _
  choose χL hχ' using fun i => exists_lift L.1
    (((χ i).comp (Dec (F := F) A).subtype).comp Bw.e.symm.toMonoidHom) fun g => hχL i _
  refine ⟨L, Bw.repE L r₂, κL, χL, hp₂, hwd.symm.trans (e₁.trans e₂.symm),
    ⟨Pi.basisFun _ _, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s => ?_, fun i s => ?_⟩
  · rw [toMatrix_repE]
    exact Subtype.ext ((er _ i j).symm.trans ((hp _).1 i j hij))
  · rw [toMatrix_repE]
    exact Subtype.ext (((er _ i i).symm.trans ((hp _).2 i)).trans (hκ i g).symm)
  · rw [hκ]
    exact congrArg (fun t => (κ i t : Qbar l)) (Bw.e.symm_apply_apply s)
  · rw [hχ']
    exact congrArg (fun t : ↥(Dec (F := F) A) => (χ i t : Qbar l)) (Bw.e.symm_apply_apply s)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousCharacterCompactUnitValues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem norm_le_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
  have := hC ⟨s ^ n, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hn (not_lt.2 this)

private theorem norm_eq_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  refine le_antisymm (norm_le_one ψ hψ s) ?_
  have h := norm_le_one ψ hψ s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h

theorem UpperTheory.continuous_character_compact_unit_values :
    UpperTheory.V.Af.Wd.CharEnd := by
  intro F Ω _ _ _ _ _ l hl ι w A h hw ψ a hψ hσ
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hq1 : 1 < normV w := GlobalTheory.WeilDeligne.one_lt_normV w
  have hpow := normV_eq_pow (l := l) hw
  have hf : resDeg l w ≠ 0 := by
    intro h0
    rw [hpow, h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  have hl1 : ‖(l : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hlt : ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
    rw [hpow, Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 hf
  have hpos : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega))
  have ha : a = 0 := by
    have h1 := hσ (frob h)
    rw [deg_frob, mul_one, ← map_natCast ι, ← map_zpow₀] at h1
    have h2 := norm_eq_one ψ hψ (Subgroup.inclusion (Weil_le_Dec h) (frob h))
    rw [ι.injective h1, norm_zpow] at h2
    exact (zpow_eq_one_iff_right₀ hpos.le hlt.ne).1 h2
  refine ⟨ha, ?_⟩
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have he : (fun s => (ψ s : Qbar l)) = fun _ => 1 := by
    refine hd.equalizer hψ continuous_const (funext fun σ => ?_)
    have h1 := hσ σ
    rw [ha, zero_mul, zpow_zero, ← map_one ι] at h1
    exact ι.injective h1
  ext s
  simpa using congrFun he s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicWeilCharProperties
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneRankOneLine
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem zpow_apply_eig {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (x : M) (c : F)
    (hc : c ≠ 0) (hx : (u : End F M) x = c • x) (n : ℤ) : ((u ^ n : (End F M)ˣ) : End F M) x = c ^ n • x := by
  have hi : ((u⁻¹ : (End F M)ˣ) : End F M) x = c⁻¹ • x := by
    rw [eq_inv_smul_iff₀ hc, ← map_smul, ← hx, ← End.mul_apply, Units.inv_mul, End.one_apply]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, End.mul_apply, hx, map_smul, ih, smul_smul,
      zpow_add_one₀ hc, mul_comm]
  | pred n ih => rw [zpow_sub_one, Units.val_mul, End.mul_apply, hi, map_smul, ih, smul_smul,
      zpow_sub_one₀ hc, mul_comm]

private theorem key {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (φ a : End F M)
    (hu : (u : End F M) = φ) (hcm : φ * a = a * φ) (x : M) (c s : F) (hc : c ≠ 0) (f : ℕ) (hφ : (φ ^ f) x = c • x)
    (hs : a x = s • x) (n : ℕ) (d : ℤ) :
    (a * ((u ^ (-((f : ℤ) * d)) : (End F M)ˣ) : End F M)) ((φ ^ n) x) = (c ^ (-d) * s) • (φ ^ n) x := by
  have hφ' : (φ ^ f) ((φ ^ n) x) = c • (φ ^ n) x := by
    rw [← End.mul_apply, ← pow_add, add_comm, pow_add, End.mul_apply, hφ, map_smul]
  have hs' : a ((φ ^ n) x) = s • (φ ^ n) x := by
    have hcm' : Commute φ a := hcm
    rw [← End.mul_apply, ← (hcm'.pow_left n).eq, End.mul_apply, hs, map_smul]
  have hz := zpow_apply_eig (u ^ f) _ c hc (by rw [Units.val_pow_eq_pow_val, hu]; exact hφ') (-d)
  rw [End.mul_apply, ← mul_neg, zpow_mul, zpow_natCast, hz, map_smul, hs', mul_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem UpperTheory.weil_deligne_rank_one_line :
    UpperTheory.V.Af.Wd.Line := by
  intro F Ω _ _ _ _ _ l _ P ι w A h O _ _ _ Bw hj L V _ _ _ _ _ ρ h1 hV x hx0 c hc hφ σ s hs y
  have hfin := hV.finite
  have hd : finrank ℂ (WDSpace P ι ρ) = 1 := by
    rw [LetterDim.finrank_wdSpace l P ι _ L _ _ hV, h1]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) ≠ 0 := by
    by_contra hh
    exact hx0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => by_contra fun h0 => hh ⟨n, h0⟩)
  have hw : weilD Bw h P ρ σ ((phiD P ρ ^ n) x) = (c ^ (-deg σ) * s) • (phiD P ρ ^ n) x := by
    rw [weilD_apply]
    exact key (phiU P ρ) (phiD P ρ) _ (coe_phiU P ρ) (phiD_actD P ρ _) x c s hc _ hφ hs n _
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ hn).mp hd y
  rw [map_smul, wdRho_mk, hw]
  change d • wdMk P ι ρ ((Dpst P ρ).module.toSMul.smul (c ^ (-deg σ) * s) ((phiD P ρ ^ n) x)) = _
  rw [wdMk_smul, smul_comm]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem cw_cyc {l : ℕ} [Fact l.Prime] (L : FinExt l) (n : ℤ) :
    Continuous fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l) := by
  have h0 := UpperTheory.V.Loc.cycFacts l l
  have h1 : Continuous fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) := by
    have : (fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l)) =
        fun g => algebraMap ℚ_[l] (Om l) (((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      funext g
      rw [← h0.2.2 g]
      rfl
    rw [this]
    have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
    exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h2.comp (Units.continuous_val.comp h0.1))
  have : (fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l)) =
      fun g => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) ^ n := by
    funext g
    rw [Units.val_zpow_eq_zpow_val]
    exact map_zpow₀ L.1.val _ _
  rw [this]
  exact h1.zpow₀ n fun g => Or.inl ((map_ne_zero L.1.val).2 (Units.ne_zero (cycL L g)))

private theorem cw_lc {l : ℕ} [Fact l.Prime] (K K' : FinExt l) {C : Type} [Group C] (χ : ↥(GK K) →* C)
    (hχ : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) : IsLocallyConstant χ := by
  have := K'.2
  have ho : IsOpen ((GK K' : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen K'.1
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨{y | ((x⁻¹ * y : ↥(GK K)) : GQ l) ∈ GK K'}, ?_, ?_, fun y hy => ?_⟩
  · exact ho.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  · simp
  · have := hχ _ hy
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm

private theorem cw_eta {l : ℕ} [Fact l.Prime] (K K' L : FinExt l) (κ χ : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ)
    (hκc : Continuous (fun g => ((κ g : ↥L.1) : Om l)))
    (hK' : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) :
    ∃ η : ↥(GK K) →* (↥L.1)ˣ, (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) ∧
      Continuous (fun g => ((η g : ↥L.1) : Om l)) := by
  let ε : ↥(GK K) →* (↥L.1)ˣ := (cycL L).comp (GK K).subtype
  refine ⟨κ * ε ^ (-m) * χ⁻¹, fun g => ?_, ?_⟩
  · change κ g = _ * (κ g * cycL L (g : GQ l) ^ (-m) * (χ g)⁻¹)
    rw [zpow_neg]
    generalize cycL L (g : GQ l) ^ m = a
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_comm (κ g), mul_inv_cancel_left]
  · have h3 : Continuous fun g => ((((χ g)⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l) :=
      ((cw_lc K K' χ hK').comp fun u => (((u⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l)).continuous
    exact (hκc.mul ((cw_cyc L (-m)).comp continuous_subtype_val)).mul h3

private theorem cw_line {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ)
    (u : V ⊗[ℚ_[l]] Bst P) (hmem : u ∈ Dpst P ρ) (hu0 : u ≠ 0) (e : ↥L.1) (he0 : e ≠ 0)
    (hu : e • (phiV P ↥L.1 V ^ resDeg l w) u = u) (σ : ↥(Weil h)) (s : ↥L.1)
    (hs : stRep P ρ (weilToGK Bw h σ) u = s • u) (y : WDSpace P ι ρ) :
    haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((e⁻¹ ^ (-deg σ) * s : ↥L.1) : Om l) • y := by
  refine UpperTheory.weil_deligne_rank_one_line F Ω l P ι w A h O Bw hj L V ρ h1 hV ⟨u, hmem⟩ (fun h0 => hu0 (congrArg Subtype.val h0)) e⁻¹
    (inv_ne_zero he0) (Subtype.ext ?_) σ s (Subtype.ext hs) y
  have h1 : ((phiD P ρ ^ resDeg l w) ⟨u, hmem⟩).1 = (phiV P ↥L.1 V ^ resDeg l w) u := by
    rw [phiD, Module.End.pow_restrict]
    rfl
  rw [h1]
  change (phiV P ↥L.1 V ^ resDeg l w) u = e⁻¹ • u
  exact (eq_inv_smul_iff₀ he0).2 hu

private theorem cw_calc {k : Type} [Field k] (a κ c χ η : kˣ) (l : k) (m d : ℤ) (f : ℕ) (h1 : κ = c ^ m * χ * η)
    (h2 : η = a ^ d) :
    ((a : k) * l ^ (m * (f : ℕ)))⁻¹ ^ (-d) * (χ : k) = (l ^ f) ^ (m * d) * ((κ * c ^ (-m) : kˣ) : k) := by
  have h3 : κ * c ^ (-m) = a ^ d * χ := by
    rw [h1, h2, zpow_neg, mul_comm, mul_assoc (c ^ m), inv_mul_cancel_left, mul_comm]
  rw [h3, inv_zpow', neg_neg, mul_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_mul, Units.val_mul,
    Units.val_zpow_eq_zpow_val, show m * (f : ℕ) * d = (f : ℕ) * (m * d) by ring]
  ring

private theorem cw_fin {l : ℕ} [Fact l.Prime] (ι : Om l ≃+* ℂ) (L : FinExt l) (f : ℕ) (n : ℤ) (x : ↥L.1) :
    ι (((((l : ↥L.1) ^ f) ^ n * x : ↥L.1)) : Om l) = ((l ^ f : ℕ) : ℂ) ^ n * ι (x : Om l) := by
  have h1 : L.1.val (((l : ↥L.1) ^ f) ^ n * x) = ((l : Om l) ^ f) ^ n * L.1.val x := by
    rw [map_mul, map_zpow₀, map_pow, map_natCast]
  refine (congrArg ι h1).trans ?_
  rw [map_mul, map_zpow₀, map_pow, map_natCast, Nat.cast_pow]
  rfl

private theorem cw_unr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : Induces Bw) {C : Type} [Group C] (η : ↥(GK Bw.Kw) →* C)
    (hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1) (σ : ↥(Weil h)) :
    η (weilToGK Bw h σ) = η (weilToGK Bw h (frob h)) ^ deg σ := by
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hτI : (weilToGK Bw h (ineIncl h τ) : GQ l) ∈ Loc.Iq l := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have := weilToGK_frobUr hj (ineIncl h τ) (a := 0) (b := 0) (actsAs_zero_iff.mpr τ.2) ⟨x, hx⟩
    simpa using this
  conv_lhs => rw [hτ]
  rw [map_mul, map_mul, hηI _ hτI, mul_one, map_zpow, map_zpow]

theorem UpperTheory.cyclotomicWeilChar_properties :
    UpperTheory.V.Af.Wd.CharWD := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L κ χ m hκc hχ hI hκ σ y
  obtain ⟨K', hK'⟩ := hχ
  obtain ⟨η, hκη, hηc⟩ := cw_eta Bw.Kw K' L κ χ m hκc hK'
  have hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1 := fun g hg =>
    mul_left_cancel ((hκη g).symm.trans ((hI g hg).trans (mul_one _).symm))
  obtain ⟨u, hu0, hu1, hu2⟩ := UpperTheory.weilDeligne_character_twist_period l Bw.Kw L κ χ η m hκη hηc hηI
  have hF := (UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj).1
  have hmem : u ∈ Dpst (Loc.PP l) (Loc.chRep κ) :=
    (mem_Dpst _ _).2 ⟨K', fun g hg => by rw [hu1, hK' g hg, Units.val_one, one_smul]⟩
  have hl : (l : ↥L.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have he0 : (η (weilToGK Bw h (frob h)) : ↥L.1) * (l : ↥L.1) ^ (m * (resDeg l w : ℕ)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ hl)
  have key := cw_line (Loc.PP l) ι h Bw hj L ↥L.1 (Loc.chRep κ) (Module.finrank_self _) hκ u hmem hu0 _ he0
    (hu2 _ _ hF) σ _ (hu1 _) y
  have h3 := cw_calc _ _ _ _ _ (l : ↥L.1) m (deg σ) (resDeg l w) (hκη (weilToGK Bw h σ)) (cw_unr h Bw hj η hηI σ)
  have h4 := (congrArg (fun x : ↥L.1 => ι (x : Om l)) h3).trans (cw_fin ι L _ _ _)
  rw [← normV_eq_pow (hj.mem_placesOver h)] at h4
  exact key.trans (congrArg (fun z : ℂ => z • y) h4)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularizable
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbelianFieldWindowTripleSnoc
open Module in
theorem UpperTheory.abelianField_window_triple_snoc :
    UpperTheory.V.Af.Wd.TriSnoc := by
  unfold UpperTheory.V.Af.Wd.TriSnoc
  intro k W' W W'' ι _ _ _ _ _ _ _ n T' T T'' f p hf hp hex h1 hT' hT'' d hd hd''
  unfold UpperTheory.V.Af.Wd.IsTri at hd ⊢
  obtain ⟨b', hb'⟩ := hd
  obtain ⟨y, hy0, hyspan⟩ := (finrank_eq_one_iff').1 h1
  obtain ⟨s, hs⟩ := hp y
  have hrange : Submodule.span k (Set.range fun i => f (b' i)) ≤ LinearMap.ker p := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hex _).2 ⟨_, rfl⟩
  have hli : LinearIndependent k (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W) := by
    rw [linearIndependent_finSnoc]
    refine ⟨b'.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
    intro hmem
    have h0 : p s = 0 := LinearMap.mem_ker.1 (hrange hmem)
    rw [hs] at h0
    exact hy0 h0
  have hsp : ⊤ ≤ Submodule.span k (Set.range (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W)) := by
    intro w _
    obtain ⟨c, hc⟩ := hyspan (p w)
    have hker : p (w - c • s) = 0 := by rw [map_sub, map_smul, hs, hc, sub_self]
    obtain ⟨x, hx⟩ := (hex _).1 hker
    have hw : w = f x + c • s := by rw [hx]; abel
    rw [hw]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last n, by simp⟩))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)
  set b := Module.Basis.mk hli hsp with hbdef
  have hbc : ∀ i, b i.castSucc = f (b' i) := fun i => by simp [b]
  have hbl : b (Fin.last n) = s := by simp [b]
  have hfx : ∀ x : W', f x = ∑ i, (b'.repr x i) • b i.castSucc := by
    intro x
    conv_lhs => rw [← b'.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hbc]
  have hrepr1 : ∀ (x : W') (i : Fin n), b.repr (f x) i.castSucc = b'.repr x i := by
    intro x i
    rw [hfx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.single_apply, Fin.castSucc_inj]
  have hrepr2 : ∀ x : W', b.repr (f x) (Fin.last n) = 0 := by
    intro x
    rw [hfx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  refine ⟨b, fun a => ⟨?_, ?_⟩⟩
  · intro i j hji
    rw [LinearMap.toMatrix_apply]
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.le_last i))
    | cast j =>
      rw [hbc, ← hT']
      induction i using Fin.lastCases with
      | last => exact hrepr2 _
      | cast i =>
        rw [hrepr1]
        have := (hb' a).1 i j (Fin.castSucc_lt_castSucc_iff.1 hji)
        rwa [LinearMap.toMatrix_apply] at this
  · intro i
    rw [LinearMap.toMatrix_apply]
    induction i using Fin.lastCases with
    | last =>
      rw [hbl]
      have hker : p (T a s - d a (Fin.last n) • s) = 0 := by
        rw [map_sub, map_smul, hT'', hs, hd'', sub_self]
      obtain ⟨x, hx⟩ := (hex _).1 hker
      have hTs : T a s = f x + d a (Fin.last n) • s := by rw [hx]; abel
      rw [hTs, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, hrepr2, ← hbl, b.repr_self]
      simp
    | cast i =>
      rw [hbc, ← hT', hrepr1]
      have := (hb' a).2 i
      rwa [LinearMap.toMatrix_apply] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularInitialSegment
open Module

theorem UpperTheory.weilDeligne_triangular_initial_segment :
    UpperTheory.V.Af.Wd.TriInit := by
  intro k W ι _ _ _ n T d hT
  obtain ⟨b, hb⟩ := hT
  have hp : ∀ a x, b.coord (Fin.last n) (T a x) = d a (Fin.last n) * b.coord (Fin.last n) x := by
    intro a x
    have h : (b.coord (Fin.last n)) ∘ₗ (T a) = d a (Fin.last n) • b.coord (Fin.last n) := by
      refine b.ext fun j => ?_
      have h1 := (hb a).1 (Fin.last n) j
      have h2 := (hb a).2 (Fin.last n)
      rw [LinearMap.toMatrix_apply] at h1 h2
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]
      by_cases hj : j = Fin.last n
      · subst hj
        rw [h2]; simp
      · rw [h1 (lt_of_le_of_ne (Fin.le_last j) hj), Finsupp.single_apply, if_neg hj, mul_zero]
    simpa using LinearMap.congr_fun h x
  have hS : ∀ a, ∀ x ∈ LinearMap.ker (b.coord (Fin.last n)), T a x ∈ LinearMap.ker (b.coord (Fin.last n)) := by
    intro a x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hp, hx, mul_zero]
  refine ⟨LinearMap.ker (b.coord (Fin.last n)), hS, b.coord (Fin.last n), ?_, rfl, hp, ?_⟩
  · intro c
    exact ⟨c • b (Fin.last n), by simp⟩
  · let v : Fin n → LinearMap.ker (b.coord (Fin.last n)) := fun i =>
      ⟨b (Fin.castSucc i), by
        rw [LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
          if_neg (Fin.castSucc_lt_last i).ne]⟩
    have hv : LinearIndependent k v := by
      apply LinearIndependent.of_comp (LinearMap.ker (b.coord (Fin.last n))).subtype
      exact b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)
    have key : ∀ x : LinearMap.ker (b.coord (Fin.last n)),
        x = ∑ i, b.repr (x : W) (Fin.castSucc i) • v i := by
      intro x
      apply Subtype.ext
      have hx : b.repr (x : W) (Fin.last n) = 0 := x.2
      have h := b.sum_repr (x : W)
      rw [Fin.sum_univ_castSucc, hx, zero_smul, add_zero] at h
      rw [Submodule.coe_sum]
      exact h.symm
    have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
      intro x _
      rw [key x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let b' := Basis.mk hv hsp
    have hb' : ∀ i, b' i = v i := fun i => Basis.mk_apply hv hsp i
    have hr : ∀ (x : LinearMap.ker (b.coord (Fin.last n))) i, b'.repr x i = b.repr (x : W) (Fin.castSucc i) := by
      intro x i
      have h := congrFun (b'.repr_sum_self fun i => b.repr (x : W) (Fin.castSucc i)) i
      simp only [hb'] at h
      rw [← key x] at h
      exact h
    have hm : ∀ a i j, LinearMap.toMatrix b' b' ((T a).restrict (hS a)) i j =
        LinearMap.toMatrix b b (T a) (Fin.castSucc i) (Fin.castSucc j) := by
      intro a i j
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hr, hb']
      rfl
    refine ⟨b', fun a => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · exact (hm a i j).trans ((hb a).1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij))
    · exact (hm a i i).trans ((hb a).2 _)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap UpperTheory.V UpperTheory.V.Af.Wd

private theorem nil_line {k W : Type} [Field k] [AddCommGroup W] [Module k W] (h1 : finrank k W = 1) {N : End k W}
    (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨y, hy0, hy⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hy (N y)
  obtain ⟨n, hn⟩ := hN
  have hp : ∀ m : ℕ, (N ^ m) y = c ^ m • y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h2 := hp n
  rw [hn, LinearMap.zero_apply] at h2
  have hc0 : c = 0 := by
    rcases smul_eq_zero.1 h2.symm with h | h
    · exact (pow_eq_zero_iff'.1 h).1
    · exact absurd h hy0
  ext x
  obtain ⟨a, rfl⟩ := hy x
  rw [map_smul, ← hc, hc0]
  simp

private theorem snoc_ops {k W' W W'' Γ : Type} [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W]
    [AddCommGroup W''] [Module k W''] {n : ℕ} {N' : End k W'} {N : End k W} {N'' : End k W''} {R' : Γ → End k W'}
    {R : Γ → End k W} {R'' : Γ → End k W''} {f : W' →ₗ[k] W} {p : W →ₗ[k] W''} (hf : Function.Injective f)
    (hp : Function.Surjective p) (hex : Function.Exact f p) (h1 : finrank k W'' = 1) (hfN : ∀ x, f (N' x) = N (f x))
    (hfR : ∀ a x, f (R' a x) = R a (f x)) (hpN : ∀ x, p (N x) = N'' (p x)) (hpR : ∀ a x, p (R a x) = R'' a (p x))
    {μ : Γ → Fin (n + 1) → k} (hI : IsTri (ops N' R') (ops 0 fun a i => μ a (Fin.castSucc i))) (hN : IsNilpotent N'')
    (hl : ∀ a y, R'' a y = μ a (Fin.last n) • y) : IsTri (ops N R) (ops 0 μ) := by
  refine UpperTheory.abelianField_window_triple_snoc k _ _ _ _ n (ops N' R') _ (ops N'' R'') f p hf hp hex h1 ?_ ?_ _ ?_ ?_
  · rintro (_ | σ) x
    · exact hfN x
    · exact hfR σ x
  · rintro (_ | σ) x
    · exact hpN x
    · exact hpR σ x
  · convert hI using 1
    funext a i
    cases a <;> rfl
  · rintro (_ | σ) y
    · rw [ops_none, ops_none, nil_line h1 hN]
      simp
    · exact hl σ y

theorem UpperTheory.weilDeligne_triangularizable :
    UpperTheory.V.Af.Wd.WdTri := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L n
  induction n with
  | zero =>
    intro V _ _ _ _ _ ρ κ μ ⟨b, _⟩ _ hV
    haveI := hV.finite
    have h0 : finrank ℂ (WDSpace (Loc.PP l) ι ρ) = 0 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L V ρ hV, finrank_eq_card_basis b, Fintype.card_fin]
    exact ⟨finBasisOfFinrankEq ℂ _ h0, fun a => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro V _ _ _ _ _ ρ κ μ hT hκ hV
    obtain ⟨S, hS, p, hp, hker, hpT, hT'⟩ := UpperTheory.weilDeligne_triangular_initial_segment _ _ _ n _ _ hT
    let ρ' : Representation ↥L.1 ↥(GK Bw.Kw) ↥S := ρ.subrepresentation S fun g x hx => hS g x hx
    have hf : ∀ g v, S.subtype (ρ' g v) = ρ g (S.subtype v) := fun _ _ => rfl
    have hpe : ∀ g v, p (ρ g v) = Loc.chRep (κ (Fin.last n)) g (p v) := fun g v => hpT g v
    have hex : Function.Exact S.subtype p := by
      rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
    obtain ⟨h', h'', hinj, hsurj, hexW⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L ↥S V ↥L.1 ρ' ρ (Loc.chRep (κ (Fin.last n)))
      S.subtype p hf hpe S.subtype_injective hp hex hV
    haveI := hV.finite
    haveI := h'.finite
    haveI := h''.finite
    have h1 : finrank ℂ (WDSpace (Loc.PP l) ι (Loc.chRep (κ (Fin.last n)))) = 1 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L _ _ h'', finrank_self]
    have hI := ih ↥S ρ' (fun i => κ (Fin.castSucc i)) (fun σ i => μ σ (Fin.castSucc i)) hT'
      (fun i => hκ (Fin.castSucc i)) h'
    exact snoc_ops hinj hsurj hexW h1 (wdLin_wdN _ ι hf) (wdLin_wdRho _ ι Bw h hj hf) (wdLin_wdN _ ι hpe)
      (wdLin_wdRho _ ι Bw h hj hpe) hI (isNilpotent_wdN _ ι _) (hκ (Fin.last n) h'')
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TridiagonalWeilDeligne
noncomputable section

open Module

namespace UpperTheory

private theorem tri_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k i h, mul_zero]

private theorem tri_avg {G : Type} [Group G] [Finite G] {n : ℕ} (R : G →* Matrix (Fin n) (Fin n) ℂ)
    (hR : ∀ g i j, j < i → R g i j = 0) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧ ∀ g, R g * P = P * Matrix.diagonal (fun i => R g i i) := by
  classical
  letI := Fintype.ofFinite G
  have hm : ∀ g h i, R (g * h) i i = R g i i * R h i i := fun g h i => by
    rw [map_mul]; exact tri_mul_diag _ _ (hR g) (hR h) i
  refine ⟨∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i), ?_, fun g => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro i _
      have : (∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = (Fintype.card G : ℂ) := by
        rw [Matrix.sum_apply]
        have : ∀ h : G, (R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = 1 := fun h => by
          rw [Matrix.mul_diagonal, ← hm, mul_inv_cancel, map_one, Matrix.one_apply_eq]
        simp [this]
      rw [this]
      exact_mod_cast Fintype.card_ne_zero
    · intro i j hij
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun h _ => ?_
      rw [Matrix.mul_diagonal, hR h i j hij, zero_mul]
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
    rw [Equiv.coe_mulLeft, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, map_mul, Matrix.mul_assoc]
    congr 3
    funext i
    rw [← hm]
    congr 2
    group

theorem tridiagonal_weil_deligne : UpperTheory.V.Af.Wd.TriDiag := by
  intro W I _ _ _ n ρ d hfin ⟨b, hb⟩
  let G := ρ.toHomUnits.range
  haveI : Finite G := by
    haveI : Finite (Set.range ρ) := hfin
    refine Finite.of_injective (fun g : G => (⟨(g.1 : End ℂ W), ?_⟩ : Set.range ρ)) ?_
    · obtain ⟨s, hs⟩ := g.2
      exact ⟨s, by rw [← hs]; rfl⟩
    · intro x y h
      exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  let R : G →* Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp (Units.coeHom _)).comp G.subtype
  have hRs : ∀ s, R (ρ.toHomUnits.rangeRestrict s) = LinearMap.toMatrix b b (ρ s) := fun s => rfl
  obtain ⟨P, hP, hRP⟩ := tri_avg R (fun g i j hij => by
    obtain ⟨s, rfl⟩ := ρ.toHomUnits.rangeRestrict_surjective g
    rw [hRs]; exact (hb s).1 i j hij)
  let e := Matrix.toLinearEquiv b P hP
  have he : ∀ x, e x = Matrix.toLin b b P x := fun x => rfl
  refine ⟨b.map e, fun s => ?_⟩
  have h1 := hRP (ρ.toHomUnits.rangeRestrict s)
  rw [hRs] at h1
  have h2 : (fun i => LinearMap.toMatrix b b (ρ s) i i) = d s := funext (hb s).2
  rw [h2] at h1
  have h3 : ∀ j, ρ s (b.map e j) = d s j • b.map e j := fun j => by
    have h4 := congrArg (fun M => Matrix.toLin b b M (b j)) h1
    simp only [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, LinearMap.comp_apply] at h4
    rw [Basis.map_apply, he, h4, ← map_smul]
    congr 1
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply, ite_smul, Finset.sum_ite_eq']
  ext i j
  rw [LinearMap.toMatrix_apply, h3, map_smul, Basis.repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Finsupp.single_apply, Ne.symm h]

end UpperTheory
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneMonodromyUpperTriangular
theorem UpperTheory.weilDeligne_monodromy_upperTriangular :
    UpperTheory.V.Af.Wd.TriMono := by
  intro k W Γ _ _ _ n N ρ c μ hcomm hT hN
  obtain ⟨b, hb⟩ := hT
  set B := LinearMap.toMatrix b b N with hBdef
  have hAlow : ∀ σ (i j : Fin n), j < i → LinearMap.toMatrix b b (ρ σ) i j = 0 := fun σ => (hb (some σ)).1
  have hAdiag : ∀ σ (i : Fin n), LinearMap.toMatrix b b (ρ σ) i i = μ σ i := fun σ => (hb (some σ)).2
  have hB0 : B ≠ 0 := by
    intro h
    apply hN
    apply (LinearMap.toMatrix b b).injective
    rw [← hBdef, h, map_zero]
  have hex : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hB0 (Matrix.ext h)
  classical
  have hJ : (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).Nonempty := by
    obtain ⟨i, j, h⟩ := hex
    exact ⟨j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩⟩
  set j := (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).min' hJ with hjdef
  have hjmem := Finset.min'_mem _ hJ
  rw [← hjdef] at hjmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  have hjmin : ∀ i l, l < j → B i l = 0 := by
    intro i l hl
    by_contra h
    have : j ≤ l := Finset.min'_le _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩)
    exact absurd hl (not_lt.mpr this)
  have hI : (Finset.univ.filter fun i => B i j ≠ 0).Nonempty := by
    obtain ⟨i, h⟩ := hjmem
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩
  set i := (Finset.univ.filter fun i => B i j ≠ 0).max' hI with hidef
  have himem := Finset.max'_mem _ hI
  rw [← hidef] at himem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at himem
  have himax : ∀ l, i < l → B l j = 0 := by
    intro l hl
    by_contra h
    have : l ≤ i := Finset.le_max' _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
    exact absurd hl (not_lt.mpr this)
  refine ⟨i, j, fun σ => ?_⟩
  set A := LinearMap.toMatrix b b (ρ σ) with hAdef
  have hmat : A * B = c σ • (B * A) := by
    rw [hAdef, hBdef, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, ← map_smul, hcomm]
  have h1 : (A * B) i j = μ σ i * B i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hAdef, hAlow σ i l h, zero_mul]
      · rw [himax l h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (B * A) i j = B i j * μ σ j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hjmin i l h, zero_mul]
      · rw [hAdef, hAlow σ l j h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h3 := congrFun (congrFun hmat i) j
  rw [Matrix.smul_apply, h1, h2, smul_eq_mul] at h3
  have : (μ σ i - c σ * μ σ j) * B i j = 0 := by rw [sub_mul, h3]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h himem
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

