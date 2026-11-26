module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
open MeasureTheory NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem pow_val {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-s) := by
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · have hx' : Valued.v (x : v.adicCompletion K) = 1 := hx
    rw [pow_loc h, FinitePlace.norm_def, hx']
    simp
  · have hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      unif_spec v
    refine (pow_loc h v (atFin v (unif v))).trans ?_
    rw [FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have e' : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [WithZero.log_exp, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

private theorem bc_twist {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [_root_.NumberField.IsTotallyComplex K]
    [_root_.NumberField.IsTotallyComplex M] {ν : HChar K} {ν' : HChar M} {z : ℂ} (hν : IsPow ν z) (hν' : IsPow ν' z) {n : ℕ} (π : CG K n)
    {ι : Type} [Fintype ι] {m : ι → ℕ} (P : ∀ i, CG M (m i)) (h : WeakBC π.HasSat (R.sumSat P)) :
    WeakBC (π.twist ν).HasSat (R.sumSat fun i => (P i).twist ν') := by
  refine Filter.Eventually.mono h fun w hw f hf => ?_
  obtain ⟨B, hB, B', hB', e⟩ := hw f hf
  have hv : ν'.val w = ν.val (w.under (𝓞 K)) ^ f := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (pow_val hν _).2, (pow_val hν' _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul]
  refine ⟨_, satake_twist_holds K n π ν _ B (pow_val hν _).1 hB, fun i => (B' i).map (· * ν'.val w),
    fun i => satake_twist_holds M _ (P i) ν' w _ (pow_val hν' _).1 (hB' i), ?_⟩
  refine Eq.trans ?_ (map_sum (Multiset.mapAddMonoidHom (· * ν'.val w)) B' Finset.univ)
  rw [← e]
  simp [Multiset.map_map, hv, mul_pow]

theorem UpperTheory.ConvolutionTheory.T.liftStep :
    UpperTheory.ConvolutionTheory.T.CoreLift → UpperTheory.ConvolutionTheory.T.LiftStep := by
  intro hC F E _ _ _ _ _ _ _ _ σ hσ hp n hn hlow π
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  have htw : ∃ χ : HChar F, (∃ s : ℂ, IsPow χ s) ∧
      ∃ V, Dp.Carries μF (π.twist χ) V := Dp.exTwist F n μF π hn
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ := htw
  obtain ⟨hex, hpw⟩ := powTwist F E
  obtain ⟨χ', hχ'⟩ := (hex s).2
  obtain ⟨hi, hi', hrest⟩ := hpw s χ χ' hχ hχ'
  have hback := (hrest n hn).1 π
  obtain ⟨-, -, hrest'⟩ := hpw (-s) χ⁻¹ χ'⁻¹ hi hi'
  obtain ⟨-, -, hL, hCj, -⟩ := hrest' n hn
  obtain ⟨c1, -, c3, c4, -, θ, hθ, c6⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hAt⟩ := c1 V hV.summand
  by_cases hO : OffAll F n (bcInf (K := E) Λ) (bcSat t)
  · obtain ⟨V', hV', hst, hAt'⟩ := hC F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hAt hO
    obtain ⟨P, hP, -⟩ := Dp.exCusp E n μE V' hV'
    have h1 := hL _ _ (c3 _ P V V' Λ t _ _ hV hP hAt hAt' rfl (Filter.Eventually.of_forall fun _ => rfl))
    rw [hback] at h1
    exact Or.inr ⟨_, h1, fun g => hCj _ _ ((c6 P V' hP).2 hst g)⟩
  · obtain ⟨ι, _, m, Q, hm, hι, hW⟩ := c4 _ V Λ t hV hAt (famParts F E σ hσ hp n hn hlow _ _ hO)
    refine Or.inl ⟨ι, inferInstance, m, fun i => (Q i).twist χ'⁻¹, hm, hι, ?_⟩
    have h1 := bc_twist hi hi' _ Q hW
    have e : (CG.mk (π.twist χ)).twist χ⁻¹ = CG.mk π := congrArg CG.mk hback
    rwa [e] at h1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
theorem UpperTheory.ConvolutionTheory.T.liftAll :
    UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll := by
  intro h F E _ _ _ _ _ _ _ _ σ hσ hp n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn π
    induction π using Quotient.inductionOn with
    | _ π =>
      rcases h F E σ hσ hp n hn (fun m h1 h2 => ih m h2 h1) π with ⟨ι, hι, m, Q, hm, hc, hw⟩ | ⟨P, hP, -⟩
      · exact ⟨ι, hι, m, Q, hm, Fintype.card_pos_iff.1 (by omega), hw⟩
      · refine ⟨Unit, inferInstance, fun _ => n, fun _ => GlobalTheory.CuspRep.CG.mk P, fun _ => hn, ⟨()⟩, ?_⟩
        rw [UpperTheory.ConvolutionTheory.R.sumSat_unit]
        exact hP.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong
theorem UpperTheory.ConvolutionTheory.T.splitStrong :
    UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong := by
  intro hD F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hc hw v w i hi hcomp τ τ' hτ hτ'
  obtain ⟨-, -, -, -, -, hpl⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨hs, u, rfl, hiu⟩ := hpl v w i hi hcomp
  obtain ⟨π', hl, hloc⟩ := hD F E σ hσ hp n hn P hc v u hs
  obtain ⟨η, hη, hiso⟩ := (UpperTheory.ConvolutionTheory.R.fibre_holds F E hp n hn (.cx π') (.cx P) hl.1).2 (.cx π) hw
  have he : π'.twist η = π := (UpperTheory.ConvolutionTheory.Dp.isoEq F n (π'.twist η) π).1 hiso
  subst he
  have hτ₀ : (UpperTheory.CBC.Cusp.cx π').locComp v τ := by
    rcases hη with rfl | hη
    · simpa [GlobalTheory.CuspRep.CuspSub.twist_one] using hτ
    · exact (UpperTheory.ConvolutionTheory.T.normCharSplit F E σ hσ hp n hn η hη v hs π' τ).1 hτ
  obtain ⟨e, he⟩ := hloc τ τ' hτ₀ hτ'
  have hm : i.toRingHom = GroundTheory.Global.SemiLocal.completionMap v u.1 := RingHom.ext hiu
  refine ⟨e, fun g x => ?_⟩
  rw [hm]
  exact he g x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.CBC

private theorem occ_basic {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    (∃ σ, Occurs μ V w σ) ∧ (∀ σ σ', Occurs μ V w σ → Occurs μ V w σ' → Nonempty (σ.ρ.Equiv σ'.ρ)) := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  have h := occursBasics K n μ V w Measure.haar hV
  exact ⟨h.1, h.2.1⟩

private theorem loc_iff {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (μ : Measure (normOneGL (K := E) (n := n)))
    [μ.IsHaarMeasure] (π : CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Dp.Carries μ π V) (w : Pl E) (σ : SmIrr (Gw n w)) :
    (Cusp.cx π).locComp w σ ↔ Occurs μ V w σ :=
  (Dp.locIff E n μ π V h w σ).trans (occursIff E n μ V h.summand w σ).symm

private theorem locIso_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {v : Pl F} (w : PlacesOver E v) {τ τ₁ : SmIrr (Gw n v)} {τ' τ₁' : SmIrr (Gw n w.1)} (a : τ₁.ρ.Equiv τ.ρ)
    (b : τ'.ρ.Equiv τ₁'.ρ) (h : LocIso w τ τ') : LocIso w τ₁ τ₁' := by
  obtain ⟨e, he⟩ := h
  refine ⟨a.toLinearEquiv.trans (e.trans b.toLinearEquiv), fun g x => ?_⟩
  have ha : a.toLinearEquiv (τ₁.ρ g x) = τ.ρ g (a.toLinearEquiv x) :=
    Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g x
  have hb : ∀ g y, b.toLinearEquiv (τ'.ρ g y) = τ₁'.ρ g (b.toLinearEquiv y) := fun g y =>
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap g y
  simp only [LinearEquiv.trans_apply]
  rw [ha, he, hb]

theorem UpperTheory.ConvolutionTheory.T.descStep :
    UpperTheory.ConvolutionTheory.T.CoreDesc → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep := by
  intro hD hL F E _ _ _ _ _ _ _ _ σ hσ hp n hn P hP v w hv
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  obtain ⟨χ', hχ', V, hV⟩ := Dp.exTwist E n μE P hn
  obtain ⟨s, hs'⟩ := hχ'
  obtain ⟨hex, htw⟩ := powTwist F E
  obtain ⟨χ, hs⟩ := (hex s).1
  obtain ⟨hi, hi', h1⟩ := htw s χ χ' hs hs'
  obtain ⟨-, hPP, -, hconj, -⟩ := h1 n hn
  obtain ⟨-, -, h2⟩ := htw (-s) χ⁻¹ χ'⁻¹ hi hi'
  obtain ⟨-, -, hlift, -, hloc⟩ := h2 n hn
  obtain ⟨-, hAt, hcl, -, hnp, θ, hθ, hst⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hΛ⟩ := hAt V hV.summand
  have hstab := (hst _ V hV).1 fun g => hconj P _ (hP g)
  have hoff : OffAll F n Λ t := by
    by_contra hc
    exact hnp _ V Λ t hV hΛ (famParts F E σ hσ hp n hn (fun m hm _ => hL F E σ hσ hp m hm) Λ t hc)
  obtain ⟨⟨τ', hτ'⟩, huE⟩ := occ_basic μE V hV.summand w.1
  obtain ⟨V₀, Λ₀, t₀, hV₀, hAt₀, hΛ₀, ht₀, τ, hτ, hiso⟩ :=
    hD F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hstab hΛ hoff v w hv τ' hτ'
  obtain ⟨π, hπ, -⟩ := Dp.exCusp F n μF V₀ hV₀
  obtain ⟨-, huF⟩ := occ_basic μF V₀ hV₀ v
  have hl := hlift π _ (hcl π _ V₀ V Λ₀ t₀ Λ t hπ hV hAt₀ hΛ hΛ₀ ht₀)
  have hl2 := hloc π (P.twist χ') v w (hv w) fun τ₁ τ₁' h₁ h₁' => by
    obtain ⟨a⟩ := huF τ₁ τ ((loc_iff μF π V₀ hπ v τ₁).1 h₁) hτ
    obtain ⟨b⟩ := huE τ' τ₁' hτ' ((loc_iff μE _ V hV w.1 τ₁').1 h₁')
    exact locIso_congr w a b hiso
  rw [hPP] at hl hl2
  exact ⟨π.twist χ⁻¹, hl, hl2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc
open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

open NumberField in
theorem UpperTheory.ConvolutionTheory.T.cbcc :
    UpperTheory.ConvolutionTheory.T.Places → UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong → UpperTheory.V.Z.Bc.CBCc := by
  intro hPl hLS hLA hDS hSS K M _ _ _ _ _ _ hp hK n hn
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  refine ⟨fun π => ?_, fun P hP => ?_, fun π P _ hw => UpperTheory.ConvolutionTheory.R.fibre_holds K M hp n hn π P hw⟩
  · rcases π with @⟨_, π⟩ | @⟨hR, π⟩
    swap
    · exact (not_both K hR hK).elim
    rcases hLS K M σ hσ hp n hn (fun m hm _ => hLA K M σ hσ hp m hm) π with ⟨ι, _, m, Q, hm, h2, hw⟩ | ⟨P, ⟨h1, h2⟩, h3⟩
    · obtain ⟨η, hη, e⟩ := UpperTheory.ConvolutionTheory.R.twoParts_holds K M hp n _ ι m Q hn hm h2 hw
      exact Or.inl ⟨η, hη, Quotient.exact e⟩
    · exact Or.inr ⟨.cx P, h1, fun τ m h => (h2 τ m).1 h, hSS K M σ hσ hp n hn π P h3 h1⟩
  · rcases P with @⟨_, P⟩ | @⟨hR, P⟩
    swap
    · exact (not_both M hR hM).elim
    obtain ⟨hinf, -, hne, -⟩ := hPl K M hp
    obtain ⟨v, hv⟩ := hinf.nonempty
    obtain ⟨w⟩ := hne v
    obtain ⟨π, ⟨h1, h2⟩, -⟩ := hDS K M σ hσ hp n hn P hP v w hv
    exact ⟨.cx π, h1, fun τ m h => (h2 τ m).2 h, hSS K M σ hσ hp n hn π P hP h1⟩
end

theorem UpperTheory.ConvolutionTheory.T.cbcc_of_core (hC : UpperTheory.ConvolutionTheory.CI) (hG : UpperTheory.ConvolutionTheory.GM.GM) : UpperTheory.V.Z.Bc.CBCc :=
  have a := liftStep (coreLift hC hG)
  have b := liftAll a
  have c := descStep (coreDesc hC hG) b
  cbcc places a b c (splitStrong c)
