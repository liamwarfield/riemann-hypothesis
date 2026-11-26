module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweLine
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.GalIsom
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.galIsom :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (x : E), valuation E (σ x) = valuation E x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ x
  exact GroundTheory.LocalField.valuation_algEquiv_apply k E σ x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.PsiInv
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private theorem UpperTheory.V.Z.Tf.L4.psiInv_exists_zpow (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (ϖ : Eˣ) (hϖ : valuation E (ϖ : E) = uniformizer E) (x : Eˣ) :
    ∃ d : ℤ, valuation E (x : E) = valuation E (ϖ : E) ^ d := by
  have h1 : ord E ϖ = 1 := GlobalTheory.SmGL.ord_eq_one hϖ
  have hz : ∀ d : ℤ, ord E (ϖ ^ d) = d := by
    intro d
    cases d with
    | ofNat n => simp [DiscreteGroups.sglob.DzType.ord_pow_bis, h1]
    | negSucc n =>
      rw [zpow_negSucc, DiscreteGroups.sglob.DzType.ord_inv_eq_neg_ord, DiscreteGroups.sglob.DzType.ord_pow_bis, h1, Int.negSucc_eq]
      push_cast; ring
  refine ⟨ord E x, ?_⟩
  rw [← map_zpow₀, ← Units.val_zpow_eq_zpow_val]
  exact le_antisymm ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
    ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))

private theorem UpperTheory.V.Z.Tf.L4.psiInv_shift {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {ψ : AddChar E Circle} {c c' : Eˣ} (h : HasConductor ψ c) (s : E) (hs : s ≠ 0)
    (hc : valuation E s * valuation E (c' : E) = valuation E (c : E)) : HasConductor (ψ.mulShift s) c' := by
  intro x
  have hv : 0 < valuation E s := by simpa [zero_lt_iff] using hs
  have h2 : valuation E x ≤ valuation E (c' : E) ↔ valuation E (s * x) ≤ valuation E (c : E) := by
    rw [← hc, map_mul, mul_le_mul_iff_right₀ hv]
  rw [h2, ← h (s * x)]
  constructor
  · intro H y hy
    have := H (s⁻¹ * y) (by
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ hv, ← map_mul]; exact hy)
    simpa [AddChar.mulShift_apply, hs] using this
  · intro H y hy
    rw [AddChar.mulShift_apply]
    apply H
    rw [map_mul, map_mul]
    gcongr

theorem UpperTheory.V.Z.Tf.L4.psiInv :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∃ c : ℤ, ∀ a₀ : ℤ, ∃ a ≥ a₀, ∃ ψ : AddChar E Circle,
      HasConductor ψ (ϖ ^ (2 * a - c)) ∧ ∀ (σ : E ≃ₐ[k] E) (x : E), ψ (σ x) = ψ x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one k
  let Ψ : AddChar E Circle := ψ₀.compAddMonoidHom (Algebra.trace k E).toAddMonoidHom
  have hΨ : ∀ x, Ψ x = ψ₀ (Algebra.trace k E x) := fun _ => rfl
  have hle : ∀ a b : k, valuation k a ≤ valuation k b ↔
      valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) := fun a b => by
    rw [← Valuation.vle_iff_le, ← Valuation.vle_iff_le, ValuativeExtension.vle_iff_vle]
  have htriv : ∀ y : E, valuation E y ≤ 1 → Ψ y = 1 := fun y hy => by
    rw [hΨ]
    refine (hψ₀ 1).2 (by simp) _ ?_
    rw [hle, map_one, map_one, trace_eq_sum_automorphisms]
    refine Valuation.map_sum_le _ fun σ _ => ?_
    rw [UpperTheory.V.Z.Tf.L4.galIsom k E σ y]
    exact hy
  have hcont : Continuous Ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_)
    have : (fun z => -x + z) ⁻¹' cball (1 : Eˣ) ∈ nhds x :=
      ((isOpen_cball (1 : Eˣ)).preimage (by fun_prop)).mem_nhds (by simp [cball])
    filter_upwards [this] with z hz
    have h1 : Ψ (-x + z) = 1 := htriv _ (by simpa [cball] using hz)
    calc Ψ z = Ψ (x + (-x + z)) := by simp
      _ = Ψ x := by rw [AddChar.map_add_eq_mul, h1, mul_one]
  have hne : Ψ ≠ 1 := by
    intro h
    apply hψ₀.ne_one
    ext y
    obtain ⟨x, rfl⟩ := Algebra.trace_surjective k E y
    rw [← hΨ, h]; simp
  obtain ⟨c₀, hc₀⟩ := DiscreteGroups.sglob.DzType.exists_hasConductor_of_continuous_ne_one Ψ hcont hne
  obtain ⟨d, hd⟩ := psiInv_exists_zpow E ϖ hϖ c₀
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have hR0 : algebraMap k E r ≠ 0 := by simpa using hr0
  have hR1 : valuation E (algebraMap k E r) < 1 := by
    have := (hle 1 r).not
    simp only [map_one, not_le] at this
    exact this.1 hr1
  obtain ⟨e, he⟩ := psiInv_exists_zpow E ϖ hϖ (Units.mk0 _ hR0)
  rw [Units.val_mk0] at he
  have hϖ0 : 0 < valuation E (ϖ : E) := by simp [zero_lt_iff]
  have hϖ1 : valuation E (ϖ : E) < 1 := hϖ ▸ uniformizer_lt_one
  have he0 : 0 < e := by
    rw [he] at hR1
    exact (zpow_lt_one_iff_right_of_lt_one₀ hϖ0 hϖ1).1 hR1
  refine ⟨-d, fun a₀ => ⟨e * |a₀|, ?_, Ψ.mulShift (algebraMap k E (r ^ (-(2 * |a₀|)))), ?_, ?_⟩⟩
  · have := le_abs_self a₀
    have := abs_nonneg a₀
    nlinarith
  · refine psiInv_shift hc₀ _ (by simp [zpow_ne_zero, hr0]) ?_
    rw [hd, map_zpow₀, map_zpow₀, he, Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul, ← zpow_add₀ hϖ0.ne']
    congr 1
    ring
  · intro σ x
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, hΨ, hΨ, ← σ.commutes, ← map_mul, σ.commutes,
      Algebra.trace_eq_of_algEquiv]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv
open GlobalTheory.SplitWeil

theorem UpperTheory.ConvolutionTheory.Loc.sbInv :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], ∀ φ ∈ SB G, ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → TotallyDisconnectedSpace G →
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ U ≤ K ∧ ∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g := by
  intro G _ _ _ φ hφ K hKo hKc hG
  obtain ⟨hl, hc⟩ := hφ
  have key : ∀ ψ : G × G → G, Continuous ψ → (∀ g, ψ (1, g) = g) → ∀ᶠ u in nhds (1 : G), ∀ g ∈ tsupport φ, φ (ψ (u, g)) = φ g := by
    intro ψ hψ h1
    apply IsCompact.eventually_forall_of_forall_eventually hc
    intro g _
    have a := (hl.comp_continuous hψ).eventually_eq (1, g)
    have b := (hl.comp_continuous continuous_snd).eventually_eq ((1 : G), g)
    filter_upwards [a, b] with z ha hb
    simp only [Function.comp, h1] at ha hb
    rw [ha, hb]
  have a := key (fun p => p.1 * p.2) (by fun_prop) (by simp)
  have b := key (fun p => p.2 * p.1) (by fun_prop) (by simp)
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (a.and b)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := K) (U := Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hW1
  have hU : ∀ u ∈ N.toSubgroup.map K.subtype, u ∈ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN hx
  refine ⟨N.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, fun u hu g => ⟨?_, ?_⟩⟩
  · exact hKo.isOpenMap_subtype_val _ N.isOpen
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).1 g h
    · by_cases h' : u * g ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).1 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).2 g h
    · by_cases h' : g * u ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).2 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweBall
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeBall :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (c : ℤ) (ρ : ValueGroupWithZero E), 0 < ρ →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSet n ϖ a c ⊆ ball n ρ := by
  intro E _ _ _ _ n ϖ hϖ c ρ hρ
  have h1 : valuation E (ϖ : E) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have h0 : 0 < valuation E (ϖ : E) := by rw [hϖ]; exact uniformizer_pos
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 ρ hρ.ne')
  refine ⟨N + |c| * n, fun a ha g hg i j => (hg i j).trans ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  refine le_trans ?_ hN.le
  rw [← zpow_natCast]
  refine zpow_le_zpow_right_of_le_one₀ h0 h1.le ?_
  have hi := i.2
  have hj := j.2
  have h2 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ n := by
    rw [abs_le]; constructor <;> omega
  have h3 : |c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))| ≤ |c| * n := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 := (abs_le.1 h3).1
  linarith
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.HoweType
open MeasureTheory NumberField IsDedekindDomain ValuativeRel GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

private theorem ball_sub_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (N : Set (GL (Fin n) k)) (hN : N ∈ nhds (1 : GL (Fin n) k)) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ball n ρ ⊆ N := by
  obtain ⟨d, -, h⟩ := GlobalTheory.GamMul.NearOne.one_add_small_near_one k n N hN
  refine ⟨valuation k (d : k), ?_, fun g hg => ?_⟩
  · exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 d.ne_zero)
  · obtain ⟨A, hA, hAN, -⟩ := h ((g : Matrix (Fin n) (Fin n) k) - 1) (fun i j => hg i j)
    have e : A = g := Units.ext (by rw [hA]; simp)
    exact e ▸ hAN

private theorem local_type (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E)
    (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) E) W) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hg : GlobalTheory.LocGL.IsGeneric π) (N : Set (GL (Fin n) E)) (hN : N ∈ nhds (1 : GL (Fin n) E)) :
    ∃ (J : Subgroup (GL (Fin n) E)) (χ : GL (Fin n) E → ℂ) (e : W), CO J ∧ IsChr J χ ∧ (J : Set (GL (Fin n) E)) ⊆ N ∧
      e ≠ 0 ∧ (∀ g ∈ J, π g e = χ g • e) ∧ (∀ x : W, (∀ g ∈ J, π g x = χ g • x) → ∃ c : ℂ, x = c • e) ∧
      ∀ y ∈ J, Matrix.GeneralLinearGroup.map (s : E →+* E) y ∈ J ∧
        χ (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = χ y := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := E) (uniformizer E)
    exact ⟨Units.mk0 x fun h => uniformizer_ne_zero (R := E) (by rw [← hx, h, map_zero]), hx⟩
  obtain ⟨ρ, hρ, hρN⟩ := ball_sub_nhds E n N hN
  obtain ⟨c, hc⟩ := psiInv k E ϖ hϖ
  obtain ⟨a₁, h₁⟩ := howeLine E n W π hs hi hg ϖ hϖ c
  obtain ⟨a₂, h₂⟩ := howeBall E n ϖ hϖ c ρ hρ
  obtain ⟨a, ha, ψ, hψ, hinv⟩ := hc (max 1 (max a₁ a₂))
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  obtain ⟨J, hJ, ho, hk⟩ := howeGroup E n ϖ hϖ a c ha1
  obtain ⟨hlc, hmul⟩ := howeChar E n ϖ hϖ a c ha1 ψ hψ
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  have hline := h₁ a (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha) ψ hψ
  obtain ⟨⟨e, he⟩, he0, hspan⟩ := finrank_eq_one_iff'.1 hline
  refine ⟨J, fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ), e, ⟨hk, ho⟩, ⟨hlc, fun x _ => Circle.norm_coe _, fun x hx y hy => ?_⟩, ?_,
    fun h => he0 (Subtype.ext h), fun g hgJ => he g ((hmem g).1 hgJ), fun x hx => ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]
  · rw [hJ]
    exact (h₂ a (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha)).trans hρN
  · obtain ⟨t, ht⟩ := hspan ⟨x, fun g hg => hx g ((hmem g).2 hg)⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  · have hy' := (hmem y).1 hy
    have hent : ∀ i j, ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
        s ((y : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
    refine ⟨(hmem _).2 fun i j => ?_, ?_⟩
    · have e1 : ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j -
          (1 : Matrix (Fin n) (Fin n) E) i j = s ((y : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [hent, map_sub, Matrix.one_apply, apply_ite s, map_one, map_zero]
      rw [e1, galIsom k E]
      exact hy' i j
    · have hsd : GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = s (GlobalTheory.Whittaker.superDiag y) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [GlobalTheory.Whittaker.superDiag, map_sum, hent]
      change ((ψ (GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y)) : Circle) : ℂ) = _
      rw [hsd, hinv]

theorem UpperTheory.ConvolutionTheory.T.howeType :
    UpperTheory.ConvolutionTheory.T.HoweType := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ μ _ V hV v w hw N hN
  obtain ⟨iA, iV, iFD, iG, s, -, -, -, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨π, hπ, -⟩ : ∃! π : GlobalTheory.CuspRep.CuspSub E n,
      UpperTheory.ConvolutionTheory.Dp.Carries μ π V :=
    UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV
  obtain ⟨hl, -, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n
  letI : MeasurableSpace (Gw n w.1) := borel _
  haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
  obtain ⟨⟨τ, hτ⟩, -, -⟩ := occursBasics E n μ V w.1 MeasureTheory.Measure.haar hV
  have hloc : (UpperTheory.CBC.Cusp.cx π).locComp w.1 τ :=
    (UpperTheory.ConvolutionTheory.Dp.locIff E n μ π V hπ w.1 τ).2 ((occursIff E n μ V hV w.1 τ).1 hτ)
  have hgen : GlobalTheory.LocGL.IsGeneric τ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w.1 τ hloc
  obtain ⟨J, χ, e, hCO, hchr, hJN, he0, heJ, hline, hst⟩ :=
    local_type (v.adicCompletion F) (w.1.adicCompletion E) s n τ.V τ.ρ τ.smooth τ.irred hgen N hN
  have hrank := lineRank E n μ V hV w.1 τ hτ J χ hCO hchr ⟨e, hline⟩
  obtain ⟨f, hf0, hfV, hfe⟩ := hτ
  have hinj : Function.Injective f := by
    let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hfe, hx, map_zero]⟩
    haveI := τ.irred
    rcases eq_bot_or_eq_top K with h | h
    · refine LinearMap.ker_eq_bot.1 ?_
      exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hf0
      have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_top.1 h'
  refine ⟨J, χ, hCO, hchr, hJN, hrank, fun h => ?_, fun x hx => ?_⟩
  · have hm : f e ∈ V ⊓ eigL μ w.1 J χ := by
      refine ⟨hfV e, ?_⟩
      simp only [eigL, SetLike.mem_coe, Submodule.mem_iInf]
      intro x hx
      change rhoL μ w.1 x (f e) = χ x • f e
      rw [← hfe, heJ x hx, map_smul]
    rw [h, Submodule.mem_bot] at hm
    exact he0 (hinj (by rw [hm, map_zero]))
  · have hcm : UpperTheory.ConvolutionTheory.GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.galFin σ v) x) =
        Matrix.GeneralLinearGroup.map (s : w.1.adicCompletion E →+* w.1.adicCompletion E) (UpperTheory.ConvolutionTheory.GM.cmp w x) :=
      Units.ext (Matrix.ext fun i j => hgal _)
    rw [hcm]
    exact hst _ hx
end

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc GlobalTheory.SplitWeil
open Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped ComplexConjugate

private theorem lc_ind {G : Type} [TopologicalSpace G] {U : Set G} (hU : IsClopen U) {h : G → ℂ}
    (hh : IsLocallyConstant h) : IsLocallyConstant (U.indicator h) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx, hh.eventually_eq x] with y hy e
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
  · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem td_gl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    TotallyDisconnectedSpace (GL (Fin n) k) := by
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem cmp_homeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) {v : HeightOneSpectrum (𝓞 F)}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    ∃ e : GL (Fin n) (CompletionsOver E v) ≃ₜ GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = UpperTheory.ConvolutionTheory.GM.cmp w g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let r : CompletionsOver E v ≃+* w.1.adicCompletion E :=
    RingEquiv.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)
  have hr : Continuous r := continuous_apply _
  have hs : Continuous r.symm :=
    (Homeomorph.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)).symm.continuous
  refine ⟨{ toEquiv := (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) r).toMulEquiv).toEquiv
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun g => ?_⟩
  · exact Continuous.units_map _ (continuous_id.matrix_map hr)
  · exact Continuous.units_map _ (continuous_id.matrix_map hs)
  · exact Units.ext (Matrix.ext fun i j => rfl)

theorem UpperTheory.ConvolutionTheory.T.inertData :
    UpperTheory.ConvolutionTheory.T.InertData := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hns
  obtain ⟨-, -, hne, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨w⟩ := hne v
  have hw : ∀ w' : PlacesOver E v, w' = w := huniq v hns w
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  obtain ⟨ρ, hρ, hdown⟩ := UpperTheory.ConvolutionTheory.Loc.atDown F E σ hσ v w hw n
  have hN : ball n ρ ∈ nhds (1 : Gw n w.1) :=
    (UpperTheory.ConvolutionTheory.Loc.BallG.isOpen_ball hρ.ne').mem_nhds (fun i j => by simp)
  obtain ⟨J, χ, hCO, hchr, hJN, hrank, hne0, hst⟩ := UpperTheory.ConvolutionTheory.T.howeType F E σ hσ hp n hn μ V hV v w hw _ hN
  haveI : T2Space (Gw n w.1) := (UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n).2.2.1
  haveI : T2Space (Gw n v) := (UpperTheory.V.Z.Tf.Orb.gLTop (v.adicCompletion F) n).2.2.1
  have hJc : IsClopen (J : Set (Gw n w.1)) := ⟨hCO.1.isClosed, hCO.2⟩
  let φ : Gw n w.1 → ℂ := (J : Set (Gw n w.1)).indicator fun x => conj (χ x)
  have hφl : IsLocallyConstant φ := lc_ind hJc (hchr.1.comp fun z => conj z)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hCO.1 fun x hx => Set.indicator_of_notMem hx _
  have hφS : φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)) := ⟨hφl, hφc⟩
  have hsupp : Function.support φ ⊆ ball n ρ := fun x hx => hJN (Set.mem_of_indicator_ne_zero hx)
  obtain ⟨f, hfS, hmatch⟩ := hdown φ hφS hsupp
  obtain ⟨e, he⟩ := cmp_homeo (F := F) n w hw
  have hec : (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) = φ ∘ e := funext fun g => by simp [he]
  have hTE : Test (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) := by
    rw [hec]
    exact ⟨hφl.comp_continuous e.continuous, hφc.comp_homeomorph e⟩
  have hTF : Test f := hfS
  obtain ⟨U₁, hU₁o, hU₁K, hU₁⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n w.1) φ hφS (GLnLocal.integralGL (w.1.adicCompletion E) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  obtain ⟨U₂, hU₂o, hU₂K, hU₂⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n v) f hfS (GLnLocal.integralGL (v.adicCompletion F) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  let J' : ∀ u : PlacesOver E v, Subgroup (Gw n u.1) := fun u => (hw u).symm ▸ J
  let χ' : ∀ u : PlacesOver E v, Gw n u.1 → ℂ := fun u => (hw u).symm ▸ χ
  have all : ∀ P : PlacesOver E v → Prop, P w → ∀ u, P u := fun P h u => (hw u).symm ▸ h
  have hprod : (UpperTheory.ConvolutionTheory.GM.prodFn fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator fun x => conj (χ' u x)) =
      fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g) := funext fun g => by
    unfold UpperTheory.ConvolutionTheory.GM.prodFn
    exact finprod_unique (fun u : PlacesOver E v =>
      (J' u : Set (Gw n u.1)).indicator (fun x => conj (χ' u x)) (UpperTheory.ConvolutionTheory.GM.cmp u g))
  refine ⟨J', χ', f, U₁.comap (UpperTheory.ConvolutionTheory.GM.cmp w), U₂, ?_, ?_, by rw [hprod]; exact hmatch, by rw [hprod]; exact hTE, hTF, ?_, ?_, hU₂o, hU₂K, ?_, ?_⟩
  · exact all _ ⟨hCO, hchr, hrank, hne0⟩
  · intro x hx
    have hxw : UpperTheory.ConvolutionTheory.GM.cmp w x ∈ J := hx w
    obtain ⟨h1, h2⟩ := hst x hxw
    refine ⟨all _ h1, ?_⟩
    rw [finprod_unique, finprod_unique]
    exact h2
  · have : (UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) = e := funext fun g => (he g).symm
    change IsOpen ((UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) ⁻¹' (U₁ : Set (Gw n w.1)))
    rw [this]
    exact hU₁o.preimage e.continuous
  · intro g hg u
    have hu := hw u
    subst hu
    exact hU₁K hg
  · intro y hy g
    rw [hprod]
    change φ (UpperTheory.ConvolutionTheory.GM.cmp w (y * g)) = φ (UpperTheory.ConvolutionTheory.GM.cmp w g)
    rw [map_mul]
    exact (hU₁ _ hy _).1
  · intro y hy g
    exact (hU₂ y hy g).1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

open scoped ComplexConjugate

theorem tyEx_of (hLev : SplitLev) (hSt : SplitStable) (hMa : SplitMatch) (hIn : InertData) (hOff : OffStable)
    (hTyp : TypedEx) (hEig : EigBasic) : TyEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV q w₀ hq S hqS hunr hsph mk
  have h1 : ∀ {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G), IsChr J 1 := fun J =>
    ⟨IsLocallyConstant.const 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm⟩
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  have key : ∀ v : Pl F, ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ)
      (c : ℂ) (f₀ : Gw n v → ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
      (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
      (GM.Split E v → ∀ u, χ u = 1) ∧
      (v ∉ S → v ≠ q → (∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ χ u = 1) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧ UF = GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v = q → (∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        UF = GLnLocal.iwahori (v.adicCompletion F) n) ∧
      (v ∈ S → IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧ IsOpen (UF : Set (Gw n v)) ∧
        UF ≤ GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v ∈ S → ¬ GM.Split E v → (∀ u, RankOne μ V u.1 (J u) (χ u)) ∧
        GM.MatchAt σ v c (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f₀ ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f₀ ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f₀ (y * g) = f₀ g) ∧
      (v ∈ S → GM.Split E v → (∀ g, g ∈ UF ↔ mapGL n (completionMap v (mk v).1) g ∈ J (mk v)) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
        ∀ ψ : Gw n (mk v).1 → ℂ, Test ψ → (∀ u ∈ J (mk v), ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ))
          (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) g) ∧
        ∀ y ∈ UF, ∀ g, ψ (mapGL n (completionMap v (mk v).1) (y * g)) = ψ (mapGL n (completionMap v (mk v).1) g)) := by
    intro v
    obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := hOff F E σ hσ hp n hn v
    by_cases hvS : v ∈ S
    · have hvq : v ≠ q := fun h => hqS (h ▸ hvS)
      by_cases hv : GM.Split E v
      · obtain ⟨U, J, hU, hUle, hJ⟩ := hLev F E σ hσ hp n hn μ V hV v hv
        obtain ⟨s1, s2⟩ := hSt F E σ hσ hp n hn v hv U J fun u => (hJ u).2.1
        obtain ⟨UE, e1, e2, e3⟩ := s2 hU hUle
        obtain ⟨c, hc⟩ := hMa F E σ hσ hp n hn v (mk v) hv U J hU fun u => ⟨(hJ u).1, (hJ u).2.1⟩
        refine ⟨J, fun _ => 1, c, 0, UE, U, fun u => ⟨(hJ u).1, h1 _, ?_⟩, fun x hx => ⟨s1 x hx, rfl⟩, fun _ _ => rfl,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨e2, e3, hU.2, hUle⟩, fun _ h => absurd hv h,
          fun _ _ => ⟨(hJ _).2.1, e1, hc⟩⟩
        rw [(hEig E n μ u.1 _ _ (hJ u).1 (h1 _)).2.1]; exact (hJ u).2.2
      · obtain ⟨J, χ, f, UE, UF, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hIn F E σ hσ hp n hn μ V hV v hv
        exact ⟨J, χ, 1, f, UE, UF, fun u => ⟨(i1 u).1, (i1 u).2.1, (i1 u).2.2.2⟩, i2, fun h => absurd h hv,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨i6, i7, i8, i9⟩,
          fun _ _ => ⟨fun u => (i1 u).2.2.1, i3, i4, i5, i10, i11⟩, fun _ h => absurd h hv⟩
    · have hs : ∀ u : PlacesOver E v, V ⊓ fixL μ u.1 (GLnLocal.integralGL (u.1.adicCompletion E) n) ≠ ⊥ := fun u =>
        hsph u.1 (by rw [show u.1.under (𝓞 F) = v from hu v u]; exact hvS)
      by_cases hvq : v = q
      · refine ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U2, GLnLocal.iwahori (v.adicCompletion F) n,
          fun u => ⟨(o5 u.1).2.1, h1 _, ?_⟩, fun x hx => ⟨o2 x hx, rfl⟩, fun _ _ => rfl, fun _ h => absurd hvq h,
          fun _ => ⟨fun _ => rfl, o4, rfl⟩, fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).2.1 (h1 _)).2.1]
        refine fun h => hs u (eq_bot_iff.2 (h ▸ inf_le_inf_left _ ?_))
        exact biInf_mono fun y hy => Subgroup.map_mono (o5 u.1).2.2 hy
      · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U1,
          GLnLocal.integralGL (v.adicCompletion F) n, fun u => ⟨(o5 u.1).1, h1 _, ?_⟩, fun x hx => ⟨o1 x hx, rfl⟩,
          fun _ _ => rfl, fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, o3, rfl⟩, fun h => absurd h hvq,
          fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).1 (h1 _)).2.1]; exact hs u
  choose J χ c f₀ UE UF k1 k2 k3 k4 k5 k6 k7 k8 using key
  let J' : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  let χ' : ∀ w : Pl E, Gw n w → ℂ := fun w => χ (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), J' u.1 = J v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  have eχ : ∀ v (u : PlacesOver E v), χ' u.1 = χ v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  let T : Ty σ n q w₀ :=
    { S := S, q_not := hqS, J := J', χ := χ', mk' := mk
      co := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).1
      chr := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.1
      off := fun w a b => (k4 _ a b).1 ⟨w, ⟨rfl⟩⟩
      at_q := fun w => (eJ q w).trans ((k5 q rfl).1 w)
      triv := fun v hv w => (eχ v w).trans (k3 v hv w)
      stable := fun v x hx => by simp only [eJ, eχ] at hx ⊢; exact k2 v x hx }
  have hsp : ∀ v, v ∈ T.sp ↔ v ∈ S ∧ GM.Split E v := fun v => Finset.mem_filter
  refine ⟨T, rfl, rfl, hTyp E n μ V hV J' χ' (fun w => ⟨T.co w, T.chr w⟩) ?_ (fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.2),
    fun v hv hn u => ?_, c, f₀, UF, fun v hv g => ?_, fun ψ hψ => ?_⟩
  · have hf : {w : Pl E | w.under (𝓞 F) ∈ insert q S}.Finite := by
      refine ((insert q S).finite_toSet.biUnion fun v _ => Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
      exact Set.mem_biUnion hw ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
    refine Filter.mem_of_superset hf.compl_mem_cofinite fun w hw => ?_
    have hw' : w.under (𝓞 F) ∉ insert q S := hw
    rw [Finset.mem_insert, not_or] at hw'
    exact T.off w hw'.2 hw'.1
  · change RankOne μ V u.1 (J' u.1) (χ' u.1)
    rw [eJ, eχ]; exact (k7 v hv hn).1 u
  · change _ ↔ _ ∈ J' (mk v).1
    rw [eJ]; exact (k8 v ((hsp v).1 hv).1 ((hsp v).1 hv).2).1 g
  · have hψ' : ∀ v ∈ S, GM.Split E v → _ := fun v a b => (k8 v a b).2.2 (ψ v) (hψ v ((hsp v).2 ⟨a, b⟩)).1 (by
      have := (hψ v ((hsp v).2 ⟨a, b⟩)).2
      change ∀ u ∈ J' (mk v).1, _ at this
      rw [eJ] at this; exact this)
    let φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then GM.prodFn (Function.update
          (fun u : PlacesOver E v => ((J v u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) (ψ v))
        else GM.prodFn fun u : PlacesOver E v => (J v u : Set (Gw n u.1)).indicator fun x => conj (χ v u x))
      else if h : v = q then GM.iwFn (h ▸ w₀) 0 else (unitSet E n v).indicator 1
    let f : ∀ v : Pl F, Gw n v → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then fun g => ψ v (mapGL n (completionMap v (mk v).1) g) else f₀ v)
      else if v = q then (GM.iwCoset v 0).indicator 1 else (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1
    let L : GM.Loc σ n q w₀ :=
      { S := S, q_not := hqS, unr := hunr, φ := φ, f := f, c := c, UE := UE, UF := UF
        test := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨(hψ' v hv b).2.1.1, (hψ' v hv b).2.1.2, (hψ' v hv b).2.2.1.1, (hψ' v hv b).2.2.1.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact ⟨(k7 v hv b).2.2.1.1, (k7 v hv b).2.2.1.2, (k7 v hv b).2.2.2.1.1, (k7 v hv b).2.2.2.1.2⟩
        lev := k6
        inv := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨fun y hy => (hψ' v hv b).2.2.2.1 y (((k8 v hv b).2.1 y).1 hy), (hψ' v hv b).2.2.2.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.2.2.2
        mat := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact (hψ' v hv b).1
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.1
        at_q := ⟨by simp only [φ, if_neg hqS, dif_pos], by simp only [f, if_neg hqS, if_pos], (k5 q rfl).2⟩
        off := fun v a b => ⟨by simp only [φ, if_neg a, dif_neg b], by simp only [f, if_neg a, if_neg b], (k4 v a b).2⟩ }
    refine ⟨L, ⟨rfl, hψ, fun v hv => ?_, fun v a b => ?_⟩, fun _ _ => ⟨rfl, rfl⟩, fun v hv => ?_, fun v a b => ?_⟩
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change φ v = GM.prodFn (Function.update (fun u : PlacesOver E v => ((J' u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ))
        (mk v) (ψ v)) ∧ ∀ g, g ∈ UE v ↔ ∀ u, GM.cmp u g ∈ J' u.1
      simp only [eJ, φ, if_pos a, if_pos b, true_and]
      exact (k8 v a b).2.1
    · change φ v = GM.prodFn fun u : PlacesOver E v => (J' u.1 : Set (Gw n u.1)).indicator fun x => conj (χ' u.1 x)
      have a' : v ∈ S := a
      simp only [eJ, eχ, φ, if_pos a', if_neg b]
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change f v = _
      simp only [f, if_pos a, if_pos b]
      rfl
    · change f v = _
      simp only [f, if_pos a, if_neg b]

end UpperTheory.ConvolutionTheory.T
end
end

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.tyEx :
    UpperTheory.ConvolutionTheory.T.TyEx :=
  tyEx_of splitLev splitStable splitMatch inertData offStable L1.typedEx L1.eigBasic
