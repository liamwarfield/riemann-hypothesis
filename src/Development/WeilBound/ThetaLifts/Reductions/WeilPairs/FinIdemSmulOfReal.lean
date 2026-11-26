module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsCompactOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FinIdemSmulOfReal
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem beta_iota_right (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) :=
  TauSpanIdentities.beta_iota_right C x v

theorem beta_iota_left (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) :=
  TauSpanIdentities.beta_iota_left C v x

theorem piWF_iotaVF (hι : IsChartF θ ι) (v : IxF F nS nT → ℂ) : piWF θ (iotaVF ι v) = v :=
  TauSpanIdentities.piWF_iotaVF hι v

theorem piWF_ratWF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y :=
  TauSpanIdentities.piWF_ratWF C y

theorem finIdem_add_iota (hι : IsChartF θ ι) (x : WOF F E nS nT) : x = finIdem F E • x + iotaVF ι (piWF θ x) :=
  TauSpanIdentities.finIdem_add_iota hι x

theorem finIdem_smul_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : finIdem F E • u = u :=
  TauSpanIdentities.finIdem_smul_of_fin hu

theorem finIdem_smul_of_real {u : WOF F E nS nT} (hu : u.map (finPartF F E) = 0) : finIdem F E • u = 0 :=
  TauSpanIdentities.finIdem_smul_of_real hu

theorem continuous_piWF (C : Ctx σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  TauSpanIdentities.continuous_piWF C

theorem piWF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x :=
  TauSpanIdentities.piWF_actOF C g h x

theorem symplOF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y :=
  TauSpanIdentities.symplOF_actOF C g h x y

theorem psi_rat (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 :=
  TauSpanIdentities.psi_rat C x y

theorem rhoFF_finRatF {g : GAF σ JS} {h : GAF σ JT} {a b} (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) : rhoFF σ JS JT (g⁻¹, h⁻¹) (finRatF F y) = finRatF F (b * y * a) :=
  TauSpanIdentities.rhoFF_finRatF ha hb y

theorem gamQF_eq_one_iff (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z :=
  TauSpanIdentities.gamQF_eq_one_iff C x y

theorem gamQF_eq_one_iff' (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n :=
  TauSpanIdentities.gamQF_eq_one_iff' C x y

theorem infRatF_injective (B : Base F E) : Function.Injective (infRatF (nS := nS) (nT := nT) (tauB B)) :=
  TauSpanIdentities.infRatF_injective B

theorem span_infRatF (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ :=
  TauSpanIdentities.span_infRatF hB

theorem omV_laws {κ : Type} [Fintype κ] [DecidableEq κ] {H s : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) :
    (∀ x y, omV H x y = -omV H y x) ∧ (∀ v, jV s (jV s v) = -v) ∧ (∀ x y, omV H x (jV s y) = omV H y (jV s x)) ∧
      ∀ v, v ≠ 0 → 0 < omV H v (jV s v) :=
  TauSpanIdentities.omV_laws hH hs hQ

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilOrthogonalFiniteCover
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem PositivityTheory.ThKW.exists_finite_lattice_cover_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U :=
  GlobalTheory.SplitLagrF.exists_finset_ann_le
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SchAFacts
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schA_facts {B : Base F E} {σ : E →ₐ[F] E} (hB : B.IsGood σ) (N : ℕ) (μN : Measure (Fin N → AF F))
    (hμN : μN.IsAddHaarMeasure) (Φ : (Fin N → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin N)) :
    Continuous Φ ∧ Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μN ∧
      ∀ b : Fin N → AF F, (fun x => B.ψ (x ⬝ᵥ b) * Φ x) ∈ schA F (Fin N) := by
  refine ⟨GlobalTheory.ThKOp.continuous_of_mem_schA hΦ, ?_, fun b => ?_⟩
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : BorelSpace (AF F) := ⟨rfl⟩
    have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
    have key : ∀ (m : MeasurableSpace (Fin N → AF F)), m = borel _ → ∀ μ : @Measure _ m,
        @Measure.IsAddHaarMeasure _ _ _ m μ → Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μ := by
      rintro m rfl μ hμ
      have hm := GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ
      have hi := (hm.integrable_norm_pow two_ne_zero).ofReal (𝕜 := ℂ)
      refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    exact key _ hb μN hμN
  · have h := GlobalTheory.WeylFour.SchrKeep.schr_mem_schA F B.ψ hB.std (Fin N) (0, b) Φ hΦ
    convert h using 1
    funext x
    simp [GlobalTheory.WeilM.schr]

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalPol
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped Pointwise in
theorem parseval_pol {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (N : ℕ)
    (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N) (hec : Continuous e) (hes : Continuous e.symm)
    (hrat : ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z))
    (hrat' : ∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) :
    ∃ (μN : Measure (Fin N → AF F)) (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (c : ℝ),
      μN.IsAddHaarMeasure ∧ μW.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < c ∧
      ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
        ∫ w in 𝓕W, thV B.ψ Φ₁ (e w) * starRingEnd ℂ (thV B.ψ Φ₂ (e w)) ∂μW =
          (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μN := by
  obtain ⟨μW, 𝓕W, hμW, h𝓕W⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)
  obtain ⟨i1, i2, -, -, -, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS (nT + nT)
  haveI := i1
  haveI := i2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
  letI mP : MeasurableSpace (VA F N) := borel _
  haveI : BorelSpace (VA F N) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  let ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N :=
    { e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }
  let me : WOF F E nS (nT + nT) ≃ᵐ VA F N := ca.toHomeomorph.toMeasurableEquiv
  have hme : ∀ w, me w = e w := fun _ => rfl
  have into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT) := by
    intro p hp
    obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    obtain ⟨x, hx⟩ := hrat' y z
    have : e.symm (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    rw [show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) =
      (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) from rfl, this]
    exact ⟨x, rfl⟩
  have hν : (μW.map me).IsAddHaarMeasure := ca.isAddHaarMeasure_map μW
  have h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me) := by
    refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (μW.map me) μW :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕W.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS (nT + nT) := ⟨e.symm p, onto' p p.2⟩
      let h : ratLF F E nS (nT + nT) := ⟨e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro eq
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)),
          (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕W.aedisjoint hgh
  have key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ →
      ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
    rintro m rfl
    exact PositivityTheory.ThKW.ParsevalPolarization.parseval_adelic_pair_fundamental hB N (μW.map me) hν (me '' 𝓕W) h𝓕
  obtain ⟨μN, c, hμN, hc, hK⟩ := key _ hb
  refine ⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  rw [← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]
  rfl

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep
section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integral_trace_one (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ w : 𝓞 E, w + sgOF σ w = 1 :=
  LatB.exists_w hB.cm hB.unram

theorem exists_good_norm_character (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  haveI := hB.galois
  exact LatB.exists_goodNorm hB.cm hB.unram

theorem lattice_stable_under_idempotents (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ := by
  intro e he a ha
  obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
  exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

theorem lattice_index_prime_to_inert (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) :=
  LatB.idx_main hB.cm hfin

end PositivityTheory.ThKW

end
end

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

theorem symplOHF_two (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x (2 • y) = symplOF σ JS JT ξ₀ x y := by
  rw [two_nsmul, GlobalTheory.HeisLineF.symplOHF_add_right, symplOHF_add_self]

theorem phase_two (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)) (w : 𝓞 E) {u : XFF F E nS nT}
    (hu : u ∈ latF F E nS nT Λ) : phaseF σ JS JT ξ₀ ψ w (2 • u) = 1 := by
  have h : ψ (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u) = 1 :=
    (hA _).1 ((latF F E nS nT Λ).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
    (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phaseF, h2, ← symplOHF_two]
  rfl

theorem smooth_theta (hg : GoodLat Λ) {hc : HeisClosedF σ JS JT ξ₀ ψ} {w : 𝓞 E}
    (H : IsHeis (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w)) (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ))
    (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    ∃ B : Submodule (𝓞 E) (XFF F E nS nT), idx (latF F E nS nT Λ) B ≠ 0 ∧
      ∀ a ∈ latF F E nS nT Λ, (∀ t ∈ B, gamFF σ JS JT ξ₀ ψ a t = 1) → opFF hc w a f = f := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨U, hU, hf⟩ := IsThetaFunOF.level f.2
  obtain ⟨N, hN, hNU⟩ := lat_lev hg U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XFF F E nS nT, (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • x) = x := nsmul_inv_smul hN2
  refine ⟨(latF F E nS nT Λ).comap ((2 * N) • LinearMap.id), idx_ne_zero hg _
    (DistribSMul.toAddMonoidHom _ (incAF F E ((2 * N : ℕ) : E)⁻¹)) (continuous_const_smul (incAF F E ((2 * N : ℕ) : E)⁻¹))
    (fun l hl => fin_smul _ (lat_fin hl)) (fun b hb => ⟨(2 * N) • (b : WOF F E nS nT), hb, ?_⟩), fun a _ ha => ?_⟩
  · show incAF F E ((2 * N : ℕ) : E)⁻¹ • ((2 * N) • (b : WOF F E nS nT)) = b
    rw [smul_comm, nsmul_inv_smul hN2]
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF F E nS nT Λ := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • t) ∈ latF F E nS nT Λ
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opFF, hf _ (by rw [XFF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XFF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end LatC

theorem latRep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ hc : HeisClosedF σ JS JT ξ₀ B.ψ, ∃ (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ Λ hg hsd hc
  have hσ := LatA.sig_sig hB
  obtain ⟨w, hw⟩ := exists_integral_trace_one σ B hB
  obtain ⟨lam, hlam, hsq⟩ := exists_good_norm_character σ B hB
  have H := isHeis_opFF hσ hS hT hξ hc hw
  have hA := LatC.lat_sd hσ hB.std hg hsd
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (LatC.smooth_theta hg H hA)
  have hidx : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0 := fun p => by
    refine LatC.idx_ne_zero hg _ (AddMonoidHom.mk' (actOF σ JS JT p.1 p.2) (actOF_add _ _))
      (LatC.continuous_act_right p.1 p.2) (fun l hl => actOF_mem_finSubF _ _ (lat_fin hl)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨Om, h1, h2⟩ := GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoFF σ JS JT) (LatA.gamFF_rhoFF hS) hidx
  refine ⟨w, lam, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2, hlam, hsq, fun x => ?_,
    LatC.near hg, LatC.near' hg, lattice_stable_under_idempotents σ B hB Λ, lattice_index_prime_to_inert σ B hB JS JT Λ hidx⟩
  obtain ⟨M, hM, hx⟩ := lat_den hg (x : WOF F E nS nT) x.fin
  refine ⟨2 * M, by omega, fun l hl => ?_⟩
  have h3 : gamFF σ JS JT ξ₀ B.ψ x (M • l) = 1 := by
    rw [H.nsmul_right, ← H.nsmul_left]
    exact H.iso hA hx hl
  rw [mul_smul, LatC.symplOHF_two]
  exact h3

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralCompAddEquiv
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF

theorem integral_comp_addEquiv {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  have : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

theorem integral_mul_left (e : AEF F E) [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)]
    (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure] (M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E))
    (hM : IsUnit M.det) : ∃ r : ℝ, 0 < r ∧ ∀ φ : WOF F E nS nT → ℂ,
      ∫ x : conjHalf σ e nS nT, φ (M * x.1) ∂μ = r * ∫ x : conjHalf σ e nS nT, φ x.1 ∂μ := by
  obtain ⟨-, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : LocallyCompactSpace (conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (conjHalf σ e nS nT) := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : conjHalf σ e nS nT ≃+ conjHalf σ e nS nT :=
    { toFun := fun x => ⟨M * x.1, mul_mem_conjHalf M x.2⟩
      invFun := fun x => ⟨M⁻¹ * x.1, mul_mem_conjHalf M⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (Matrix.nonsing_inv_mul_cancel_left M x.1 hM)
      right_inv := fun x => Subtype.ext (Matrix.mul_nonsing_inv_cancel_left M x.1 hM)
      map_add' := fun x y => Subtype.ext (Matrix.mul_add M x.1 y.1) }
  have hc : Continuous T := by
    show Continuous fun x : conjHalf σ e nS nT => (⟨M * x.1, mul_mem_conjHalf M x.2⟩ : conjHalf σ e nS nT)
    exact Continuous.subtype_mk (continuous_const.matrix_mul continuous_subtype_val) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : conjHalf σ e nS nT => (⟨M⁻¹ * x.1, mul_mem_conjHalf M⁻¹ x.2⟩ : conjHalf σ e nS nT)
    exact Continuous.subtype_mk (continuous_const.matrix_mul continuous_subtype_val) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv μ T hc hc'
  exact ⟨r, hr, fun φ => hφ fun x => φ x.1⟩

variable {B : Base F E}

theorem prof_level (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) {e : AEF F E} (he : IsSplitIdemF σ e)
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    ∃ U : AddSubgroup (conjHalf σ e nS nT), IsOpen (U : Set (conjHalf σ e nS nT)) ∧
      ∀ t : conjHalf σ e nS nT, ∀ l ∈ U, prof σ JS JT ξ₀ B.ψ ν 𝓕 f (t + l : conjHalf σ e nS nT) =
        prof σ JS JT ξ₀ B.ψ ν 𝓕 f t := by
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨U, hU, hUf⟩ := hf.level
  let m : conjHalf σ e nS nT →+ WOF F E nS (nT + nT) :=
    AddMonoidHom.mk' (fun y => aC F E nT * y.1) fun a b => Matrix.mul_add _ a.1 b.1
  have hm : Continuous m := continuous_const.matrix_mul continuous_subtype_val
  refine ⟨U.comap m, hU.preimage hm, fun t l hl => ?_⟩
  rw [AddSubgroup.coe_add, ← prof_heis_aC ν 𝓕 he f t.2 l.2,
    hUf (aC F E nT * l.1) hl (GlobalTheory.SplitVacF.fin_of_mem he (mul_mem_conjHalf _ l.2))]

theorem prof_support (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ t : conjHalf σ e nS nT, t ∉ K → prof σ JS JT ξ₀ B.ψ ν 𝓕 f t = 0 := by
  obtain ⟨K, hK, hKs⟩ := exists_compact_ann (JS := JS) hB hS hT hξ hσξ he
    (fun g => heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f = f) (fun g hg => by
      obtain ⟨k, hk, h⟩ := exists_nsmul_fix (GlobalTheory.SplitVacF.isSplitIdemF_conj he)
        (mul_mem_conjHalf (dC F E nT) (smul_mem_conjHalf (-hlf F E) hg)) hf
      refine ⟨k, hk, ?_⟩
      rwa [smul_comm, Matrix.mul_smul])
  refine ⟨K, hK, fun t ht => ?_⟩
  by_contra hne
  refine ht (hKs t fun g hg => ?_)
  have h := prof_heis_lift hB hS hT hξ hσξ hν h𝓕 hf g t
  rw [hg] at h
  exact (mul_eq_right₀ hne).1 h.symm

theorem prof_integrable (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    Integrable (fun t : conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) μ := by
  obtain ⟨-, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : T2Space (conjHalf σ e nS nT) := inferInstance
  have : R1Space (conjHalf σ e nS nT) := T2Space.r1Space
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := prof_support hB hS hT hξ hσξ hν h𝓕 he hf
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK hKs)
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hn : {s : conjHalf σ e nS nT | s - t ∈ U} ∈ nhds t := by
    refine IsOpen.mem_nhds (hU.preimage (continuous_id.sub continuous_const)) ?_
    show t - t ∈ U
    rw [sub_self]; exact U.zero_mem
  filter_upwards [hn] with s hs
  have h1 := hUf t _ hs
  rwa [add_sub_cancel] at h1

theorem commF_eventually (hB : B.IsGood σ) {e : AEF F E} (he : IsSplitIdemF σ e) (g : WOF F E nS nT) :
    ∀ᶠ y : conjHalf σ e nS nT in nhds 0, commF σ JS JT ξ₀ B.ψ g y = 1 := by
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨K, hK⟩ := GlobalTheory.HeisThetaF.exists_openAddSubgroup_psi_fin B.ψ hψ
  let φ : WOF F E nS nT → AF F := fun u => symplOHF σ JS JT ξ₀ g u - symplOHF σ JS JT ξ₀ u g
  have hφ : Continuous φ :=
    (GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g)
  let ρ : conjHalf σ e nS nT → Af F := fun u => (φ u.1).2
  have hρ : Continuous ρ := continuous_snd.comp (hφ.comp continuous_subtype_val)
  have h0 : ρ 0 = 0 := by
    show (symplOHF σ JS JT ξ₀ g 0 - symplOHF σ JS JT ξ₀ 0 g).2 = 0
    rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero]
    rfl
  have hn : ρ ⁻¹' (K : Set (Af F)) ∈ nhds (0 : conjHalf σ e nS nT) :=
    (K.isOpen.preimage hρ).mem_nhds (by rw [Set.mem_preimage, h0]; exact K.zero_mem)
  filter_upwards [hn] with u hu
  have h1 : pairA F 1 0 • u.1 = 0 :=
    GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (GlobalTheory.SplitVacF.fin_of_mem he u.2)
  have hfst : fstA F (φ u.1) = 0 := by
    rw [← GlobalTheory.HeisThetaF.fstA_mul_idem]
    show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ g u.1 - symplOHF σ JS JT ξ₀ u.1 g)) = 0
    rw [mul_sub, ← GlobalTheory.HeisThetaF.symplOHF_smul_left (pairA F 1 0) u.1 g,
      ← GlobalTheory.HeisThetaF.symplOHF_smul_right (pairA F 1 0) g u.1, h1, GlobalTheory.HeisThetaF.symplOHF_zero_left,
      GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, map_zero]
  have hφu : φ u.1 = pairA F 0 (ρ u) := Prod.ext hfst rfl
  show B.ψ (φ u.1) = 1
  rw [hφu]
  exact hK _ hu

theorem lagrInt_eq_zero (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f)
    (hall : ∀ u, ∫ t : conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ u f) t ∂μ = 0) :
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f = 0 := by
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := prof_support hB hS hT hξ hσξ hν h𝓕 he hf
  obtain ⟨G, -, hG⟩ := exists_open_sep (JS := JS) hB hS hT hξ hσξ he U hU
  let L : AddSubgroup (conjHalf σ e nS nT) :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, GlobalTheory.SplitVacF.commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => GlobalTheory.SplitVacF.commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := GlobalTheory.SplitVacF.commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g
          (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hL : IsOpen (L : Set (conjHalf σ e nS nT)) := by
    refine AddSubgroup.isOpen_of_mem_nhds L (g := 0) ?_
    exact (Filter.eventually_all_finset G).2 fun g _ => commF_eventually hB he g
  have hφ := GlobalTheory.fourier_uniqueness_of_openSubgroup μ
    (fun (a : WOF F E nS nT) (t : conjHalf σ e nS nT) => commF σ JS JT ξ₀ B.ψ a t)
    (fun a s t => GlobalTheory.SplitVacF.commF_add_right a s.1 t.1)
    (fun a => GlobalTheory.SplitVacF.commF_zero_right a) (fun t => GlobalTheory.SplitVacF.commF_zero_left t.1)
    (fun a b t => GlobalTheory.SplitVacF.commF_add_left a b t.1) L hL
    (fun x hx => by
      have hx' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (x : WOF F E nS nT) = 1 := hx
      push_neg at hx'
      obtain ⟨g, hg, hne⟩ := hx'
      exact ⟨g, fun l hl => hl g hg, hne⟩)
    (fun t => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) K hK hKs (fun t l hl => hUf t l (hG l hl))
    (fun a _ => by
      rw [← hall (dC F E nT * ((-hlf F E) • a : WOF F E nS nT))]
      simp only [prof_heis_lift hB hS hT hξ hσξ hν h𝓕 hf])
  rw [← prof_zero (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (ψ := B.ψ)]
  exact congrFun hφ 0

end GlobalTheory.SplitLagrF

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ProjFacts
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity GlobalTheory.ThetaTransform GlobalTheory.RatDarboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT N : ℕ}

def adB (b : Module.Basis (Fin N) F (Matrix (Fin nT) (Fin nS) E)) : Module.Basis (Fin N) (AF F) (WOF F E nS nT) :=
  (b.baseChange (AF F)).map (matBC (AF F))

theorem adB_apply (b : Module.Basis (Fin N) F (Matrix (Fin nT) (Fin nS) E)) (i : Fin N) : adB b i = ratWF (b i) := by
  rw [adB, Module.Basis.map_apply, Module.Basis.baseChange_apply, matBC_one]; rfl

theorem adB_rat (b : Module.Basis (Fin N) F (Matrix (Fin nT) (Fin nS) E)) (x : Matrix (Fin nT) (Fin nS) E) :
    (adB b).equivFun (ratWF x) = GlobalTheory.SWQ.rat (b.equivFun x) := by
  funext i
  have e : (ratWF x : WOF F E nS nT) = matBC (AF F) ((1 : AF F) ⊗ₜ[F] x) := (matBC_one (AF F) x).symm
  rw [Module.Basis.equivFun_apply, adB, Module.Basis.map_repr, LinearEquiv.trans_apply, e, LinearEquiv.symm_apply_apply,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

theorem aC_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : (aC R n).map φ = aC S n := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases p with p | p <;> simp [Matrix.one_apply, apply_ite φ]

theorem dCdE_eq (J : Matrix (Fin nT) (Fin nT) E) : dCdE J = aC E nT * ((1 / 2 : E) • J⁻¹) := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  simp only [dCdE, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases p with p | p <;> simp [Matrix.one_apply]

theorem dCd_eq (J : Matrix (Fin nT) (Fin nT) E) :
    dCd F J = aC (AF F ⊗[F] E) nT * ((1 / 2 : E) • J⁻¹).map (incAF F E) := by
  rw [dCd, dCdE_eq, Matrix.map_mul, aC_map]

theorem dbl_map (J : Matrix (Fin nT) (Fin nT) E) : (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J).map (incAF F E) =
    (dbl (J.map (incAF F E))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Matrix.map_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases r with r | r <;> simp

theorem h_CC (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (u u' : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (dC (AF F ⊗[F] E) nT * u) (dC (AF F ⊗[F] E) nT * u') = 0 := by
  rw [hOF_eq_trace, Matrix.map_mul, dC_map, Matrix.transpose_mul, dbl_map, Matrix.mul_assoc _ (dC _ nT)ᵀ, C_D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (aC _ nT)ᵀ, A_C]
  simp

theorem h_AA (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (u u' : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (aC (AF F ⊗[F] E) nT * u) (aC (AF F ⊗[F] E) nT * u') = 0 := by
  rw [hOF_eq_trace, Matrix.map_mul, aC_map, Matrix.transpose_mul, dbl_map, Matrix.mul_assoc _ (aC _ nT)ᵀ, A_D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dC _ nT)ᵀ, C_A]
  simp

theorem C_C {R : Type} [CommRing R] {n : ℕ} : (dC R n)ᵀ * dC R n = (2 : R) • 1 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, diagCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp [two_smul]

theorem proj_facts (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) :
    ∃ U V : Matrix (Fin nT) (Fin (nT + nT)) E, U * dC E nT = 1 ∧ U * dCdE J = 0 ∧ V * dC E nT = 0 ∧ V * dCdE J = 1 ∧
      dC E nT * U + dCdE J * V = 1 := by
  refine ⟨(1 / 2 : E) • (dC E nT)ᵀ, J * (aC E nT)ᵀ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, C_C, smul_smul]; norm_num
  · rw [dCdE_eq, ← Matrix.mul_assoc, Matrix.smul_mul, C_A]; simp
  · rw [Matrix.mul_assoc, A_C, Matrix.mul_zero]
  · rw [← C_D]; exact dC_dual J hJ
  · rw [dCdE_eq, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ),
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_smul, ← smul_add, CC_add, smul_smul]
    norm_num

theorem rat_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) E) (x : Matrix (Fin b) (Fin c) E) :
    (M.map (incAF F E) * (ratWF x : WOF F E c b) : Matrix (Fin a) (Fin c) (AF F ⊗[F] E)) = ratWF (M * x) :=
  Matrix.map_mul.symm

theorem pairing {B : Base F E} (hB : B.IsGood σ) {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (a b : Matrix (Fin nT) (Fin nS) E ≃ₗ[F] (Fin N → F)),
      (∀ v u, symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dC (AF F ⊗[F] E) nT * u) =
        α v ⬝ᵥ β u) ∧ (∀ x, α (ratWF x) = GlobalTheory.SWQ.rat (a x)) ∧ ∀ x, β (ratWF x) = GlobalTheory.SWQ.rat (b x) := by
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  have hbij := bijective_sympBil σ hinv (JA := (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (JB := -(ξ₀ • JS⁻¹)) (by simp)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  let b := Module.finBasis F (Matrix (Fin nT) (Fin nS) E)
  let b' := b.dualBasis.map (LinearEquiv.ofBijective _ hbij).symm
  have hb : ∀ i j, symp σ (-1) (1 : Matrix (Fin nT) (Fin nT) E)ᵀ (-(ξ₀ • JS⁻¹)) (b' i) (b j) = if j = i then 1 else 0 :=
    fun i j => by
      have h1 := (LinearEquiv.ofBijective _ hbij).apply_symm_apply (b.dualBasis i)
      have h2 := LinearMap.congr_fun h1 (b j)
      rw [Module.Basis.dualBasis_apply_self] at h2
      exact h2
  let P : LinearMap.BilinForm (AF F) (WOF F E nS nT) :=
    sympBil (cA σ) (-1) (incM F (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (incM F (-(ξ₀ • JS⁻¹)))
  have hP : ∀ v u, P v u = (adB b').equivFun v ⬝ᵥ (adB b).equivFun u := fun v u => by
    have h0 : ∀ i j, P (adB b' i) (adB b j) = if j = i then 1 else 0 := fun i j => by
      rw [adB_apply, adB_apply]
      refine (symp_map (AF F) σ _ _ (b' i) (b j)).trans ?_
      rw [hb]
      split_ifs <;> simp
    conv_lhs => rw [← (adB b').sum_repr v, ← (adB b).sum_repr u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h0, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct, Module.Basis.equivFun_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨_, (adB b').equivFun, (adB b).equivFun, b'.equivFun, b.equivFun, fun v u => ?_, adB_rat b', adB_rat b⟩
  rw [← hP]
  refine Eq.trans ?_ (GlobalTheory.TransportF.symplOF_eq_symp (JT := 1) rfl eB v u)
  unfold symplOF
  rw [hOF_dual JS JT hT.2, hOF_eq_trace, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

theorem split (JT : Matrix (Fin nT) (Fin nT) E) (hT : IsHermND σ JT) :
    ∃ (d : WOF F E nS (nT + nT) ≃ₗ[AF F] WOF F E nS nT × WOF F E nS nT) (U V : Matrix (Fin nT) (Fin (nT + nT)) E),
      (∀ w, d w = (V.map (incAF F E) * w, U.map (incAF F E) * w)) ∧
      ∀ p, d.symm p = dC (AF F ⊗[F] E) nT * p.2 + dCd F JT * p.1 := by
  obtain ⟨U, V, p1, p2, p3, p4, p5⟩ := proj_facts JT hT.2
  have m := fun {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) E} (h : X = Y) =>
    congrArg (fun M : Matrix (Fin a) (Fin b) E => M.map (incAF F E)) h
  have q1 := m p1
  have q2 := m p2
  have q3 := m p3
  have q4 := m p4
  have q5 := m p5
  simp only [Matrix.map_mul, dC_map, Matrix.map_add _ (map_add (incAF F E)), Matrix.map_one _ (map_zero (incAF F E))
    (map_one (incAF F E)), Matrix.map_zero _ (map_zero (incAF F E))] at q1 q2 q3 q4 q5
  rw [show (dCdE JT).map (incAF F E) = dCd F JT from rfl] at q2 q4 q5
  let d : WOF F E nS (nT + nT) ≃ₗ[AF F] WOF F E nS nT × WOF F E nS nT :=
    { toFun := fun w => (V.map (incAF F E) * w, U.map (incAF F E) * w)
      invFun := fun p => dC (AF F ⊗[F] E) nT * p.2 + dCd F JT * p.1
      map_add' := fun x y => Prod.ext (Matrix.mul_add _ _ _) (Matrix.mul_add _ _ _)
      map_smul' := fun a x => Prod.ext (Matrix.mul_smul _ _ _) (Matrix.mul_smul _ _ _)
      left_inv := fun w => by
        simp only [← Matrix.mul_assoc]
        rw [← Matrix.add_mul, q5, Matrix.one_mul]
      right_inv := fun p => by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, q1, q2, q3, q4, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add] }
  exact ⟨d, U, V, fun _ => rfl, fun _ => rfl⟩

theorem modTop (a c : ℕ) : IsModuleTopology (AF F) (WOF F E a c) := by
  have i0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact inferInstanceAs (IsModuleTopology (AF F) (Fin c → Fin a → AF F ⊗[F] E))

theorem cont2 {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module (AF F) M] [Module (AF F) M'] [TopologicalSpace M]
    [TopologicalSpace M'] (h : IsModuleTopology (AF F) M) (h' : IsModuleTopology (AF F) M') (e : M ≃ₗ[AF F] M') :
    Continuous e ∧ Continuous e.symm := by
  have := IsModuleTopology.toContinuousAdd (AF F) M
  have := IsModuleTopology.toContinuousAdd (AF F) M'
  have := IsModuleTopology.toContinuousSMul (AF F) M
  have := IsModuleTopology.toContinuousSMul (AF F) M'
  exact ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap, IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap⟩

theorem coords {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσ : σ ξ₀ = -ξ₀) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F))
      (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N),
      (∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u)) ∧
      (∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w')) ∧
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) ∧
      (∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) ∧
      Continuous e ∧ Continuous e.symm ∧
      Continuous α ∧ Continuous α.symm ∧ Continuous β ∧ Continuous β.symm ∧
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y) ∧
      (∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) := by
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  obtain ⟨N, α, β, a, b, hP, ha, hb⟩ := pairing hB hS hT hξ
  obtain ⟨d, U, V, hd, hd'⟩ := split (nS := nS) JT hT
  obtain ⟨e, he0⟩ : ∃ e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N, ∀ w, e w = (α (d w).1, β (d w).2) :=
    ⟨d.trans (α.prodCongr β), fun _ => rfl⟩
  have he : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u) := fun u v => by
    rw [he0, ← hd' (v, u), d.apply_symm_apply]
  have j1 : IsModuleTopology (AF F) (Fin N → AF F) := inferInstance
  have j2 : IsModuleTopology (AF F) (VA F N) := inferInstance
  have c1 := cont2 (modTop _ _) j2 e
  have c2 := cont2 (modTop _ _) j1 α
  have c3 := cont2 (modTop _ _) j1 β
  refine ⟨N, α, β, e, he, fun w w' => ?_, fun x => ?_, fun y z => ?_, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2,
    fun x => ⟨_, hb x⟩, fun y => ⟨b.symm y, by rw [hb, LinearEquiv.apply_symm_apply]⟩⟩
  · obtain ⟨⟨v, u⟩, rfl⟩ := d.symm.surjective w
    obtain ⟨⟨v', u'⟩, rfl⟩ := d.symm.surjective w'
    have s1 : symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC (AF F ⊗[F] E) nT * u)
        (dC (AF F ⊗[F] E) nT * u') = 0 := by rw [symplOF, h_CC, mul_zero, map_zero]
    have s2 : symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dCd F JT * v') = 0 := by
      rw [symplOF, dCd_eq, Matrix.mul_assoc, Matrix.mul_assoc, h_AA, mul_zero, map_zero]
    have s3 := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv _ _ JS _ hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hσ
      (dCd F JT * v') (dC (AF F ⊗[F] E) nT * u)
    rw [hd', hd', he, he, GlobalTheory.ThetaSchurF.symplOF_add_left, GlobalTheory.ThetaSchurF.symplOF_add_right,
      GlobalTheory.ThetaSchurF.symplOF_add_right, s1, s2, s3, hP, hP, symV]
    ring
  · refine ⟨a (V * x), b (U * x), ?_⟩
    rw [he0, hd, rat_mul, rat_mul, ha, hb]
  · refine ⟨dC E nT * b.symm z + dCdE JT * a.symm y, ?_⟩
    have : (ratWF (dC E nT * b.symm z + dCdE JT * a.symm y) : WOF F E nS (nT + nT)) =
        dC (AF F ⊗[F] E) nT * (ratWF (b.symm z) : WOF F E nS nT) + dCd F JT * (ratWF (a.symm y) : WOF F E nS nT) := by
      rw [← dC_map (incAF F E), dCd, rat_mul, rat_mul]
      exact Matrix.map_add _ (map_add _) _ _
    rw [this, he, ha, hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end
