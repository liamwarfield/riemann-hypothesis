module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsFurther
namespace GlobalTheory.IsolatedTheoremFour

open IsDedekindDomain

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {l : ℕ}, Nat.Prime l → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), (↑l : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  intro K _ _ l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int (algebraMap ℤ (NumberField.RingOfIntegers K)))]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlQ : ((l : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
    have h1 : (l : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  exact ⟨⟨Q, hQ.isPrime, fun h => hl0 (Ideal.mem_bot.mp (h ▸ hlQ))⟩, hlQ⟩

end GlobalTheory.IsolatedTheoremFour
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TwFin

theorem exists_over {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremFour.main
  | exact _root_.GlobalTheory.IsolatedTheoremFour.main
  | (apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremFour.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremFour.main ..)

theorem finite_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact hv

theorem mul_ne_one {R : Ranks} {H : Formalism.BasicNotions.Host R} {S : Set ℕ} {p : ℕ} {δ ψ : HChar H.E} (hp : p.Prime) (hS : p ∈ S)
    (hδ : IsDelta (H := H) p δ) (hψ : Chr.IsTwist H S ψ) : δ * ψ ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_over (K := H.E) hp
  have hu : ψ.UnrAt v := by
    by_contra hn
    obtain ⟨-, hq, -, hnS⟩ := hψ.2.2.2 v hn
    have := Examples₂.PlacesToy.prime_mem_unique v hq hp (Ideal.absNorm_mem _) hv
    exact hnS (this ▸ hS)
  have h1 := (hδ.ine v hv 1).1 fun x hx => by
    have h2 : (δ * ψ).loc v x = 1 := by
      rw [h]
      rfl
    change δ.loc v x * ψ.loc v x = 1 at h2
    rw [hu x hx, mul_one] at h2
    simpa only [pow_one] using h2
  omega

theorem resChar_conj (B : Base) (w : B.places.Pl) : B.places.resChar (B.places.conj w) = B.places.resChar w := by
  refine Examples₂.PlacesToy.prime_mem_unique (B.places.conj w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) ?_
  have h := (Examples₂.PlacesToy.mem_conjW_pow w ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) 1).2
    (by rw [pow_one, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)
  rw [pow_one] at h
  exact h

theorem finite_pl (B : Base) (s : Finset ℕ) : {w : B.places.Pl | B.places.resChar w ∈ s}.Finite := by
  refine ((s.finite_toSet.subset (s := (s : Set ℕ)) (t := {p | p ∈ s ∧ p ≠ 0}) fun p hp => hp.1).biUnion
    fun p hp => finite_mem (K := B.LL) hp.2).subset fun w hw => ?_
  simp only [Set.mem_iUnion]
  exact ⟨B.places.resChar w, ⟨hw, (B.places.resChar_prime w).ne_zero⟩, Examples₂.PlacesToy.resCharW_mem w⟩

theorem tw_fin : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B), (T.set f).Finite ∧ (∀ w, T.xiTw f w ≠ 1) ∧ (∀ w, T.xiTw f (B.places.conj w) = T.xiTw f w) ∧ {w : B.places.Pl | B.places.resChar w ∈ T.pl}.Finite := by
  intro B f T
  refine ⟨?_, fun w => ?_, fun w => ?_, finite_pl B T.pl⟩
  · have h3 : ({1, f.del, f.del'} : Set (HChar B.host.E)).Finite := Set.toFinite _
    refine (h3.union ((finite_pl B T.pl).image (T.xiTw f))).subset ?_
    rintro ξ (h | ⟨w, rfl⟩)
    · exact Or.inl h
    · by_cases hw : B.places.resChar w ∈ T.pl
      · exact Or.inr ⟨w, hw, rfl⟩
      · left
        unfold TwDat.xiTw
        rw [(T.off w hw).1, mul_one]
        split_ifs
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
  · unfold TwDat.xiTw
    split_ifs
    · exact mul_ne_one B.host.pde'_prime (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f.isDel' (T.psi_tw w)
    · exact mul_ne_one B.host.pde_prime (Or.inr (Or.inr (Or.inl rfl))) f.isDel (T.psi_tw w)
  · unfold TwDat.xiTw
    rw [resChar_conj, (T.conj w).1]

end GlobalTheory.Mem.Top.TwFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

theorem _root_.GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice : ∀ (D : _root_.Formalism.BasicNotions.D7) (c : _root_.Formalism.BasicNotions.NChoice D),
    _root_.Formalism.BasicNotions.NChTie D c → IsGalois ℚ ↥D.LL0 →
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (c.twI w) := by
  intro D c hc hG w hw
  unfold _root_.Formalism.BasicNotions.NTw.NonzeroIndexPlace
  refine ⟨if c.sd w = true then w else D.what₂.places.conj w, ?_, ?_⟩
  · split_ifs
    · exact hw
    · rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]
      exact hw
  · have h := _root_.GlobalTheory.TwistGoodCompare.liesUnder_of_tie hG hc w
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder at h
    exact h

end GlobalTheory.Mem.Top
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem Ev.mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

theorem large₂.and {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) (hq : large₂ K q) :
    large₂ K fun B f T => p B f T ∧ q B f T :=
  large₂.inter hp hq

theorem large₂.mono {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop}
    (h : ∀ B f T, K.Over B.toPre → p B f T → q B f T) (hp : large₂ K p) : large₂ K q :=
  large₂.imp hp h

end GlobalTheory.Mem.Top
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdComp

theorem eq_zero_of_valued_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (x : P.adicCompletion E) (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
  have h1 := h (m.natAbs + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_eps_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) : adAt F w (afsplitEps E v) = 1 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 1))
    (fun n => by
      rw [he]
      exact hspec _ 1 w n (by rw [h, afsplitI_self, map_one, sub_self, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_one, map_one] at h0
  exact h0

theorem adAt_eps_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) : adAt F w (afsplitEps E v) = 0 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 0))
    (fun n => by
      rw [he]
      exact hspec _ 0 w n (by rw [afsplitI_ne v _ h, map_zero, sub_zero, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_zero, map_zero] at h0
  exact h0

theorem adAt_eps_mul_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = adAt F w z := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_under v w h, one_mul]

theorem adAt_eps_mul_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = 0 := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_ne v w h, zero_mul]

theorem prV_zero_int_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  intro F E _ _ _ _ _ v z
  classical
  have hinj : ∀ x y : E ⊗[F] v.adicCompletion F, afsplitIE v x = afsplitIE v y → x = y := by
    intro x y hxy
    rw [← afsplit_prV_IE v x, hxy, afsplit_prV_IE]
  have hdec : afsplitIE v (prV (E := E) v z) = afsplitEps E v * z := afsplit_decomp v z
  have hz : ∀ w : HeightOneSpectrum (𝓞 E), adAt F w (0 : AfE F E) = 0 := by
    intro w; unfold adAt; exact map_zero _
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 E),
      adAt F w (afsplitEps E v * z) = if w.under (𝓞 F) = v then adAt F w z else 0 := by
    intro w
    split_ifs with hw
    · exact adAt_eps_mul_of_under v w hw z
    · exact adAt_eps_mul_of_ne v w hw z
  refine ⟨⟨fun h0 w hw => ?_, fun h => ?_⟩, ⟨fun hint w hw => ?_, fun h => ?_⟩⟩
  · rw [← adAt_eps_mul_of_under v w hw z, ← hdec, h0, map_zero, hz]
  · apply hinj
    rw [hdec, map_zero]
    apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [hcomp, hz]
    split_ifs with hw
    · exact h w hw
    · rfl
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [← hdec]; exact afsplit_IE_int v _ hint
    rw [← adAt_eps_mul_of_under v w hw z]
    exact (mem_rInt_iff F E _).mp h1 w
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [mem_rInt_iff]
      intro w
      change Valued.v (adAt F w (afsplitEps E v * z)) ≤ 1
      rw [hcomp]
      split_ifs with hw
      · exact h w hw
      · rw [map_zero]; exact zero_le'
    have h2 := afsplit_prV_int v _ h1
    rwa [← hdec, afsplit_prV_IE] at h2

end GlobalTheory.Mem.Col2.AdComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAboveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeProjection_zero_integral_iff_components_above : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  first | exact @GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | exact GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | (intros; apply GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenReadsOfUnfBC
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem genReads_of_unfBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r g : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((U (σ'.comp (incF c c' hle))).X k).Λ)
    (idx : Fin g ≃ ((U (σ'.comp (incF c c' hle))).X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : ((U (σ'.comp (incF c c' hle))).X k).dom) (ϑ : (Fin g → ℂ) → ℂ)
    (h : GenReads (unfBC hle U σ') k bas idx e x ϑ) : GenReads (U (σ'.comp (incF c c' hle))) k bas idx e x ϑ := by
  obtain ⟨B, hB⟩ := h
  letI : Algebra c.F ℂ := (σ'.comp (incF c c' hle)).toAlgebra
  letI : Algebra c'.F ℂ := σ'.toAlgebra
  exact ⟨⟨B.ex, B.ex_add, B.ex_onto, B.ex_ker, B.ex_lin, B.hol, B.der, B.fr, B.fr_hol, B.fr_ne, B.fr_g, B.fr_0, B.χ,
    B.χ_norm, B.fr_per⟩, hB⟩

theorem CcIs.unfBC {D : D7} (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ)
    (dict : GA D W → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D W → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ)
    (h : CcIs θ V W hr (U (σ'.comp (incF c c' hle))) dict mu x₀ om f₀ cc) :
    CcIs θ V W hr (Formalism.L2.Pj.unfBC hle U σ') dict mu x₀ om f₀ cc := by
  refine ⟨h.1, fun a γ hA hx' g bas idx e hs hi ϑ hϑ w hw => ?_⟩
  have hrel : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  have hi' : IdxIs c (σ'.comp (incF c c' hle)) ((U (σ'.comp (incF c c' hle))).X (dict a).1) idx e := by
    unfold IdxIs at hi ⊢
    rw [hrel] at hi
    exact hi
  exact h.2 a γ hA hx' g bas idx e hs hi' ϑ (genReads_of_unfBC hle U σ' _ bas idx e ⟨_, hx'⟩ ϑ hϑ) w hw

end GlobalTheory.AdTh
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

theorem mem_HHa_of_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun σ i i' hi t => by rw [map_add (f := _), hx.2.1 σ i i' hi t, hy.2.1 σ i i' hi t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx.2.2 m h
    · exact hy.2.2 m h
  | smul c x _ hx =>
    exact ⟨Submodule.smul_mem _ c hx.1, fun σ i i' hi t => by rw [map_smul, hx.2.1 σ i i' hi t],
      fun m hm => hx.2.2 m (MvPolynomial.support_smul hm)⟩

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : RowDeg r n k a P) : P.IsHomogeneous (∑ σ, ∑ j : Fin (r σ), a σ j) := by
  intro m hm
  have h1 := h m (MvPolynomial.mem_support_iff.2 hm)
  rw [show Finsupp.weight 1 m = Finsupp.degree m from (DFunLike.congr_fun Finsupp.degree_eq_weight_one m).symm,
    Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => h1 σ j

theorem exists_isVarOf {D : D7} (V W : HSp D) {r : ℕ} (hr : W.rank = r) (X : Data D.host.E r) (hX : IsMod W hr X) (q0 : ℕ)
    (hq : X.p0 + q0 = r) : ∃ vr, IsVarOf V W X q0 vr := by
  let e1 : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hX.psi _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hX.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  let e2 : Fin q0 ⊕ Fin X.p0 ≃ Fin W.rank := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨e1.symm.prodCongr (e2.prodCongr (Equiv.refl _)), fun l => ⟨?_, rfl, ?_⟩⟩
  · exact (congrArg Subtype.val (e1.apply_symm_apply l.1)).symm
  · obtain ⟨τ, j | j, b⟩ := l <;> rfl

theorem exists_isDetAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    ∃ y, IsDetAt e V g y := by
  obtain ⟨ι, Q, es, h1, h2, h3⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum h
  have he : e * e = e := by
    conv_lhs => rw [h3, Finset.sum_mul]
    rw [h3]
    exact Finset.sum_congr rfl fun i hi => GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi
  obtain ⟨u, hu⟩ : IsUnit (Formalism.L2.Theta.mt V g).det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨(matHom V g), rfl⟩
  have k1 : (e * (u : AE D) + (1 - e)) * (e * (u⁻¹ : (AE D)ˣ) + (1 - e)) = 1 := by
    have := u.mul_inv
    linear_combination (e * e) * this + ((2 : AE D) - u - (u⁻¹ : (AE D)ˣ)) * he
  exact ⟨⟨_, _, k1, (mul_comm _ _).trans k1⟩, by rw [IsDetAt, ← hu]⟩

theorem exists_point {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1)
    (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hmk : ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧
      ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1))
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (hD : Dom a V.rank) (mu : GA D W → ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cst : U.Comp → ℂ)
    (hcc : CcIs θ V W hr U dict mu x₀ om f₀ cst) (h : GA D W) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (Dc : Dic Dw c σ (U.X (dict h).1) g Dw.p V.rank a) (γ : GA D W)
      (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (v : TF V.rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
      (B : AnFib (U.X (dict h).1) Dc.bas Dc.idx Dc.e (dict h).2 (U.X (dict h).1).Λ
        (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩)),
      AtComp θ W hr U.X dict x₀ h γ ∧ SelfD (U.X (dict h).1) (U.X (dict h).1).Λ ∧ IsMark l (U.X (dict h).1).Λ mk ∧
      B.Marked mk ∧ MarkAd l W hr ι (γ * h) mk ∧
      B.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩).s ϑ ∧
      IsVac (U.X (dict h).1) Dc.bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (U.X (dict h).1).Λ) v ∧
      (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA (U.X (dict h).1) Dc.bas Dc.idx v (dict h).2 z) ∧
      Reads θ V W hr (U.X (dict h).1) Dc.bas Dc.idx (om (1, γ * h) f₀) ((cst (dict h).1 * mu h * κ') • v) (dict h).2 := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨hon, γ, hat, hma⟩ := hmk Wt h
  have hn : Even V.rank := hD.2
  obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1
  obtain ⟨Dc, hDe, -⟩ := exists_dic _ H Dw l c σ r Wt.g V.rank (U.X (dict h).1) a Wt.e hσ hU.1 (hU.2.1 _).1 (hU.2.1 _).2 hsd hD
  obtain ⟨hx, hux, -⟩ := hx_of_isONFr _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hon
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset V.rank 1)).1
  have key := uw_anFib _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1 Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx⟩ hux
  rw [← hDe] at key
  obtain ⟨B, hBm, ϑ, hϑ, -⟩ := key
  have hT := isTheta1_of_reads_generator _ H Dw l Xo c _ _ _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd ϑ hϑ
  obtain ⟨κ', hκ⟩ := VacProd.prod_eq_mul_thA _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd v hv _ hx ϑ hT
  refine ⟨hx, Wt.g, Dc, γ, Wt.mark (dict h).1, v, ϑ, κ', B, hat, hsd, hmark, hBm, hma, hϑ, hv, hκ, ?_⟩
  obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hx v hv.1).2.2 v hv.1).1
    (cst (dict h).1 * mu h * κ') 0
  rw [zero_smul, add_zero] at s1 s2
  rw [zero_smul, add_zero] at s2
  refine ⟨s1, fun w hw0 => ?_⟩
  rw [hcc.2 h γ hat hx Wt.g Dc.bas Dc.idx Dc.e Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ ϑ ⟨B, hϑ⟩ w hw0, hκ, s2, Pi.smul_apply, smul_eq_mul]
  ring

theorem dict_cast {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    LatIsom W (T.Q.Dw j).EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    (∀ g : GA D W, ∃ x, IsDetRoot W g x) ∧
    ∀ θ : InfFam D, IsInfFam θ → (∀ k, IsMod W hr ((T.U j σ).X k)) → 1 ≤ D.R.r →
      ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))) (h : GA D W),
        IsONFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2 ∧
        ∃ γ, AtComp θ W hr (T.U j σ).X (castDict hV (T.dict j σ)) (T.x₀ j σ) h γ ∧
          MarkAd T.Q.l W hr (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (γ * h)
            (Wt.mark (castDict hV (T.dict j σ) h).1) := by
  subst hV
  obtain ⟨_, g, e, F, ik, φ, th, h1, h2, h3, h4⟩ := hL.adPin j hj σ hσ
  refine ⟨h1, h2, (hL.muVal j hj σ hσ).1, fun θ hθ hm h0 Wt h => ?_⟩
  obtain ⟨k1, γ, k2, k3, -⟩ := dict_atComp_markAd D _ _ _ _ _ σ _ (T.U j σ) hσ (hL.unf j hj σ hσ) h0 hL.pins.2.1.2 θ _ hr
    (T.dict j σ) _ g e F ik φ th _ hθ hm (hL.familyUniformisationBasePointOrthogonal j hj σ hσ) h3 h4 Wt h
  exact ⟨k1, γ, k2, k3⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

abbrev unfO (O : OMDat T.toCore R i Tp tup) : Unf (T.Q.Xo ((i : ℕ) + 1)) O.c' (inC O.c') D.R.r :=
  unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')

set_option maxHeartbeats 1000000 in
theorem geo_value (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {c0 : ℂ} (hc : CovAt O c0) (t : Tp)
    (X : Data D.host.E D.R.r) (g : ℕ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (k : GA D (Wc D i)) (xk : (AE D)ˣ) (hk : IsDetRoot (Wc D i) k xk) (hX : IsMod (Wc D i) (rank_Wc i) X)
    (hp : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q) (hpq : (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q)
    (hrk : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) (hn : Even (Vc D i).rank)
    (hΛ : latR (rank_Wc i) (latG (Wc D i) k) = X.Λ) (hsd : SelfD X X.Λ) (x : Frame X.Ψ D.R.r) (hx : x ∈ X.dom)
    (hxk : x = frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1))
    (mk mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (hm : IsMark T.Q.l X.Λ mk)
    (hm₂ : IsMark (O.dδ t).l₂ X.Λ mk₂) (ha₂ : MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk₂)
    (hov : MarkOver T.Q.l (O.dδ t).l₂ X.Λ mk mk₂) (v : TF (Vc D i).rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
    (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    (hκ : ∀ z : Fin (Vc D i).rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X Dc.bas Dc.idx v x z)
    (Y : O.Cl' t → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E)
    (hY : ∀ j, IsRoots (O.dδ t).l₂ X.Λ mk₂ (O.Nc t j) (Y j)) (xs : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) :
    letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
    ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ) (B : AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ →
      evR (T.Q.Xo ((i : ℕ) + 1)) O.c' f y = c0 * ((R.xi (tup t) xk : Circle) : ℂ) * κ' *
        clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
          (fun j => O.io (xs j)) X.Λ v Y x := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra
  intro y B hB hϑ
  have halg : ∀ s : O.c'.F, algebraMap (O.dδ t).c₂.F ℂ ((O.dδ t).eF s) = algebraMap O.c'.F ℂ s := fun s => rfl
  obtain ⟨hlev, hA₂, hnab⟩ := hP.cov t
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := MarkLift.exists_lift_marked _ _ _ _ _ O.c' _ (O.dδ t) halg hlev hT.laws.pins.2.1.2 hA₂
    (fun h => absurd h hpq) _ g X Dc.bas Dc.idx Dc.e x X.Λ y B Dc.sympl hx hsd mk mk₂ hm hB hm₂ hov
  obtain ⟨-, cga, hio⟩ := hP.io
  have h1 := evR_eq_clsSum GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) halg hnab _ g X Dc.bas Dc.idx Dc.e x X.Λ y y₂ B₂ hov₂
    Dc.sympl hx hsd _ Dc.hr Dc.eL hrk hn Dc.dir_eq ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂ (O.Cl' t) (O.w t) (O.La t) (O.Nc t)
    (O.gam t) (O.vol t) (O.ep t) _ O.io xs (wtA (κ i))
    (fun j => ⟨((hP.reps t).1 j).1, ((hP.reps t).1 j).2.2.1, ((hP.reps t).1 j).2.2.2.1⟩)
    (fun j => mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self _ _)) Y hY f hf
  subst hxk
  rw [h1, hc t X g Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂]
  rfl

end GlobalTheory.PtId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem underQ_notMem {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : I.UnderQ a v) :
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  obtain ⟨P, hP, rfl⟩ := hv
  have key : ∀ p : ℕ, p.Prime → p ∈ I.S → ((p : ℕ) : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
    intro p hp hS hm
    apply GlobalTheory.KFormsCmp.notMem_of_QE hI.sel_ok (I.tup a) hP hp hS
    have := Ideal.mem_comap.1 hm
    simpa using this
  exact ⟨key _ (l.pr.T_prime u) (hI.T_mem u), fun j => key _ (l.pr.g_prime j) (hI.g_mem j)⟩

theorem underQ_prime_to_bad : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v →
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
  fun I hI l u a v hv => underQ_notMem I hI l u a v hv

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | exact GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | (intros; apply GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open scoped TensorProduct

def chartWiden {D : D7} {T : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))} (hb : bad ⊆ bad') {i : ℕ} {hi : i ≤ D.R.m}
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) : LevelChart D T bad' i hi stab lat where
  lev :=
    { K.lev with
      Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (hb h)) hT
      chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (hb hv)) }
  y := K.y
  y_bij := K.y_bij
  y_lat := K.y_lat
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

def chartAll {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m}
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (β : Unit) :
    LevelChart D T bad i hi (fun c : {c : cl // (fun _ : cl => ()) c = β} => stab c.1) (fun c => lat c.1) where
  lev := K.lev
  y c := K.y c.1
  y_bij := by
    have e : Function.Bijective (fun c : {c : cl // (fun _ : cl => ()) c = β} => c.1) :=
      ⟨Subtype.val_injective, fun c => ⟨⟨c, rfl⟩, rfl⟩⟩
    exact K.y_bij.comp e
  y_lat c := K.y_lat c.1
  stabI c := K.stabI c.1
  stabI_inj c := K.stabI_inj c.1
  stabI_range c := K.stabI_range c.1

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

set_option maxHeartbeats 4000000 in
structure TwLevJ {Ch0 : B.Word → ℕ → Type} {chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i}
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)))
    (u : B.Word) (a : I.ι) {Ch : Type} (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _)
      (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1)
      (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) where

  levJ : Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f Q

  Yb : Type
  [YbFin : Finite Yb]
  [YbAct : MulAction levJ.U Yb]

  yb : Ch → Yb
  yb_orbit : ∀ y : Yb, ∃! β, ∃ κ : levJ.U, κ • yb β = y

  lb : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) levJ.Lb
  le : ∀ β, (K β).lev.U ≤ levJ.U.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom
  stab : ∀ β (κ : levJ.U), reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 ∈ (K β).lev.U ↔ κ • yb β = yb β

  chiJ : levJ.U →* ℂˣ
  chiJ_eq : ∀ β (κ : levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (K β).lev.chi κ' = chiJ κ

  J_g : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
    ∀ x ∈ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v levJ.Lb,
      x ∈ levJ.Uloc v ↔ ∃ M ∈ HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v,
        (M : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) (kv (I.rec7 l Z).host.F v)) = redJS F u j v hv x

  J_off : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Q → v ∉ badG (I.rec7 l Z) →
    (levJ.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom = (F u).levJ.Uloc v

  yG : Yb → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)),
    ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v
  yG_smul : ∀ (κ : levJ.U) y j v hv,
    yG (κ • y) j v hv = redJS F u j v hv (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) *ᵥ yG y j v hv

  YQ : Type
  yQ : Yb → YQ
  y_inj : ∀ y y', yG y = yG y' → yQ y = yQ y' → y = y'
  yQ_off : ∀ (κ : levJ.U) y, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → yQ (κ • y) = yQ y

attribute [instance] TwLevJ.YbFin TwLevJ.YbAct

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
noncomputable section

namespace GlobalTheory.Mem.Col2.MetricTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.DivisionValues Matrix
open scoped ComplexOrder

theorem majAt_classSum {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K) (hb : C.HasRatBasis) (v : InfinitePlace K)
    (hH : (C.H.map v.embedding).PosDef) {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (ψ : C.V →ₛₗ[v.embedding] W)
    (hs : ∀ x y, (∀ i, C.bV.repr x i ∈ cmMax K) → v.embedding (C.pair x y) = B (ψ x) (ψ y)) (x : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x x = ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ (x.1 c)) (ψ (x.1 c)) := by
  have h1 : Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x x =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin C.dim)) (stdFrame C.H) v (C.basis.equivFun x) (C.basis.equivFun x) := by
    have h2 : ∀ z : C.Forms, Formalism.HermitianLatticesTheory.vecAt C.basis v z =
        Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin C.dim)) v (C.basis.equivFun z) := by
      intro z; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h2]
  have hm : metOf (stdFrame C.H v) = C.H.map v.embedding := (frameOfSpec _ _ hH).2
  have hI : x.1 = ∑ i, C.basis.equivFun x i • (C.basis i : C.Cl → C.V) := by
    rw [← C.I_eq_sum]; simp [CSD.I_apply]
  have hc : ∀ i j, v.embedding (C.H i j) =
      ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ ((C.basis i : C.Cl → C.V) c)) (ψ ((C.basis j : C.Cl → C.V) c)) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CSD.H, Matrix.of_apply, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
    exact Finset.sum_congr rfl fun c _ => congrArg _ (hs _ _ (C.basis_rat hb i c))
  rw [h1, Formalism.L2.DIV.majAt_eq, hm, hI]
  generalize C.basis.equivFun x = a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, hc, map_sum, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Pi.star_apply,
    starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  ring

section Pol

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fockF_conj {τ : Type} (f g : MvPolynomial τ ℂ) :
    Formalism.REAL.fockF (MvPolynomial.map (starRingEnd ℂ) f) (MvPolynomial.map (starRingEnd ℂ) g) =
      starRingEnd ℂ (Formalism.REAL.fockF f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockF_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), Formalism.REAL.fockF, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, map_mul, map_mul, map_natCast]
  rfl

theorem nfAll_conj (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = starRingEnd ℂ (nfAll lam p q) := by
  rw [nfAll, nfAll, map_div₀, fockF_conj, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← fockF_conj, Formalism.L2.Col.map_extremal]

theorem nfAll_shift (lam lam' : ι → DomWeight n) (c : ℤ) (h : ∀ τ i, (lam' τ).w i = (lam τ).w i + c) :
    nfAll lam' = nfAll lam := by
  have e : ∀ τ, (lam' τ).natW = (lam τ).natW := fun τ => by
    funext i
    have hn : 0 < n := i.pos
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn, h]
    congr 1
    ring
  funext p q
  simp only [nfAll, extremal, e]

theorem fnOf_congr {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (sh : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) (y' : Frames G') (h : y'.1 = y.1) :
    fnOf G' sh M P y' = fnOf G sh M P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, h]

theorem unitary_of_isON {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, G τ = 1) (o : Frames G) (ho : o.IsON) (τ : ι) :
    (o.1 τ)ᴴ * o.1 τ = 1 := by
  have h := frame_pos o ho τ (by rw [hG]; exact PosSemidef.one)
  rwa [hG, Matrix.mul_one] at h

end Pol

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

omit [NumberField E] [StarRing E] [NumberField K] in
theorem map_pairVr_rat (s : K →+* ℂ) (F F' : VV K lam) (hF : ∀ i, (bVV K lam).repr F i ∈ cmMax K) :
    s (pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) F F') = nfL lam (MvPolynomial.map s F.1) (MvPolynomial.map s F'.1) := by
  have hc : ∀ m, F.1.coeff m ∈ cmMax K := fun m => by
    have h := congrArg Subtype.val ((bVV K lam).sum_repr F)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at h
    rw [← h, MvPolynomial.coeff_sum]
    refine Subfield.sum_mem _ fun i _ => ?_
    obtain ⟨P, hP⟩ := bVVfun_int K lam i
    rw [MvPolynomial.coeff_smul, hP, MvPolynomial.coeff_map, smul_eq_mul]
    exact mul_mem (hF i) (intCast_mem _ _)
  have h := pairVr_nfAll emb (1 : Matrix (Fin n) (Fin n) E) lam s (stdFrC (embAt s emb))
    (fun τ => by simp [stdFrC, gramC]) F F' (fun m => hc m s)
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (stdFrC (n := n) (embAt s emb)).1 = AlgHom.id ℂ _ := blockAct_one
  rw [h, e, nfL_apply]
  simp [stdFrC]

theorem majAt_step (S : GStep E K n) (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) [inst : Fintype S.Cl] (s : K →+* ℂ)
    (x : (S.hlat emb lam h).V) :
    (Formalism.HermitianLatticesTheory.majAt (S.hlat emb lam h).b (S.hlat emb lam h).X (InfinitePlace.mk s) x x).re =
      ∑ c : S.Cl, (((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹).re *
        (nfAll lam (MvPolynomial.map s (x.1 c).1) (MvPolynomial.map s (x.1 c).1)).re := by
  have h1 := majAt_classSum (S.csd emb lam h) (LatGood.hasRatBasis S emb σ lam hF hS h) (InfinitePlace.mk s)
    (LatGood.step_gram_posDef S emb σ lam hF hS h _) (nfL lam) ((mapS _).domRestrict (VV K lam))
    (fun F F' hr => map_pairVr_rat emb lam _ F F' hr) x
  refine (congrArg Complex.re h1).trans ?_
  have hi : inst = (S.csd emb lam h).finCl := Subsingleton.elim _ _
  subst hi
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 : (S.csd emb lam h).wt c = Nat.card (S.Stab c) := (@Nat.card_eq_fintype_card _ (_)).symm
  rw [h2, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.ofReal_re]
  congr 1
  show (nfAll lam (MvPolynomial.map (InfinitePlace.mk s).embedding (x.1 c).1)
    (MvPolynomial.map (InfinitePlace.mk s).embedding (x.1 c).1)).re = _
  rcases InfinitePlace.embedding_mk_eq s with e | e
  · rw [e]
  · have e' : ComplexEmbedding.conjugate s = (starRingEnd ℂ).comp s := RingHom.ext fun _ => rfl
    rw [e, e', ← MvPolynomial.map_map, nfAll_conj, Complex.conj_re]

theorem norm_step (S : GStep E K n) (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) [Fintype S.Cl]
    {lam' : ι → DomWeight n} (hl : nfAll lam = nfAll lam') {sh : ι → ℤ} (hsh : sh = shiftOf lam)
    {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (hG' : ∀ τ, G' τ = 1) (eY : Fr emb σ n → Frames G) (hY : ∀ y, (eY y).1 = y.1)
    (s : K →+* ℂ) (x : (S.hlat emb lam h).V) (Pc : S.Cl → MvPolynomial (ι × Fin n × Fin n) K)
    (hP : ∀ c z, S.embF emb σ lam h x c z = fnOf G sh 1 (MvPolynomial.map σ (Pc c)) (eY z))
    (o : Frames G') (ho : o.IsON) :
    (Formalism.HermitianLatticesTheory.majAt (S.hlat emb lam h).b (S.hlat emb lam h).X (InfinitePlace.mk s) x x).re =
      ∑ c : S.Cl, (((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * sh τ)) *
        (nfAll lam' (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re := by
  subst hsh
  rw [majAt_step emb σ lam S hF hS h s x]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : (x.1 c).1 = Pc c := by
    refine evFr_injective (Gr emb σ n) (shiftOf lam) σ (fr0 emb σ n) (funext fun z => ?_)
    exact (hP c z).trans (fnOf_congr _ _ _ z (eY z) (hY z))
  have hd : ∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) = 1 := Finset.prod_eq_one fun τ _ => by
    have h1 : ‖(o.1 τ).det‖ = 1 := norm_deFr o ho τ (by rw [hG']; simp)
    rw [h1, _root_.one_zpow]
  have hu := nfAll_blockAct lam' o.1 (fun τ => mul_eq_one_comm.mp (unitary_of_isON hG' o ho τ))
    (MvPolynomial.map s (Pc c)) (MvPolynomial.map s (Pc c))
  rw [hd, mul_one, e, hl, ← hu]
  rfl

omit [NumberField E] [StarRing E] [NumberField K] [StarRing K] in
theorem ipVal_step {lam' : ι → DomWeight n} (hl : nfAll lam = nfAll lam') {sh : ι → ℤ} (hsh : sh = shiftOf lam)
    {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, G τ = 1) (eY : Fr emb σ n → Frames G) (hY : ∀ y, (eY y).1 = y.1)
    (o : Frames G) (ho : o.IsON) (P Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    ipVal emb σ lam (fun z => fnOf G sh (fun τ => (o.1 τ)⁻¹) P (eY z)) (fun z => fnOf G sh (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
      nfAll lam' Q P := by
  subst hsh
  have hG0 : ∀ τ, Gr emb σ n τ = 1 := fun τ => by simp [gramC]
  simp only [fun P z => fnOf_congr (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P z (eY z) (hY z)]
  rw [← hl]
  exact ipFr_fnOf (Gr emb σ n) lam (fr0 emb σ n) ⟨o.1, o.2⟩ (fun τ => by simp [fr0, stdFrC, gramC])
    (fun τ => by rw [hG0, Matrix.mul_one]; exact unitary_of_isON hG o ho τ) P Q

end Step

theorem shiftOf_lamT {R : Ranks} {ι : Type} [Fintype ι] (hc : ι → HCParam R) (j : ℕ) :
    shiftOf (fun τ => Formalism.L2.Forms.shW (Examples₂.lamOf (hc τ) j) ((j * (R.t + 1) / 2 : ℕ) : ℤ)) =
      shiftOf (GlobalTheory.Mem.Col2.lamT hc j) := by
  refine congrArg shiftOf (funext fun τ => ?_)
  obtain ⟨a, ha⟩ := R.t_odd
  have e1 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  have e2 : (R.t + 1) / 2 = a + 1 := by omega
  simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.lamT, GlobalTheory.Mem.Col2.shW, e1, e2]
  congr 1

theorem nfAll_lamT {R : Ranks} {ι : Type} [Fintype ι] (hc : ι → HCParam R) (j : ℕ) :
    nfAll (GlobalTheory.Mem.Col2.lamT hc j) = nfAll fun τ => Examples₂.lamOf (hc τ) j :=
  nfAll_shift _ _ _ fun _ _ => rfl

end GlobalTheory.Mem.Col2.MetricTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → IpVTieG (D := (I.rec7 l Z)) (I.fm l u a) eY ∧ NormTieG (D := (I.rec7 l Z)) (I.fm l u a) eY := by
  intro B X I hI hp l Z u a i hi eY hY
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hp l Z).2.2.2 i hi).1
  have hG : ∀ (e : (I.rec7 l Z).what₂.Tau → (I.rec7 l Z).host.E →+* ℂ) τ, gramC (gramN (I.rec7 l Z) i hi) e τ = 1 := fun e τ => by
    rw [hg, gramC_one]
  refine ⟨fun c o ho P _ Q _ => ?_, fun s x Pc hP o ho => ?_⟩
  · exact MetricTie.ipVal_step B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) (MetricTie.nfAll_lamT _ _)
      (MetricTie.shiftOf_lamT (B.hcW u) i) (hG _) eY hY o ho P Q
  · exact @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) (I.stp u a i) (base_fOk B)
      ((l.ch u a).step i) ((l.fmL u a).fam i) ((I.chIn u a).clFin (l.ch u a) i) _ (MetricTie.nfAll_lamT _ _) _
      (MetricTie.shiftOf_lamT (B.hcW u) i) _ _ (hG _) eY hY s x Pc hP o ho

end
end
