module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupActionLiftFormsRightTranslation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorsLiftsDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLattices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg

set_option maxHeartbeats 4000000 in
theorem exists_liftSide : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 → Seed.FrmC.StdLat (Vc X.toD7 i) → ∃ s : ∀ t, Seed.LiftSideT (famR X I hX U Xg tr) L cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) i t, (∀ t,       (∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG ((s t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _))) ∧
      Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef (s t).pres (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) (s t).pres ((famR X I hX U Xg tr).heckeLI i t)
        (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
        (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
        fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1)) ∧ BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (s t).pres.extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i c0L hcV hmap hin hβ hg _
  obtain ⟨c, hc, hP⟩ := GlobalTheory.T.exists_common_coefficientMap_liftPresentation X px I hX U Xg tr L eG hI hV hL hG cV i c0L hcV hmap hin hβ hg
  choose P hR hco hC using hP
  have hF : ∀ t, FrameOK X I U i t 1 1 := fun t => GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram X px I U i t hg
  choose a ha using fun t => GlobalTheory.T.exists_finiteGroupAction_liftForms_rightTranslation X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  have hk := fun t => GlobalTheory.T.splitHecke_operators_lifts_doubleCoset X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  have hki := fun t => GlobalTheory.T.exists_inertHecke_doubleCosetOperators_lifts X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  exact ⟨fun t => Bridge.SideRealG.mk (P t) (a t) (Classical.choice (hk t)), fun t => ⟨ha t, hC t, hki t⟩,
    GlobalTheory.T.standardLiftReading_of_decoratedLatticePresentations X px I hX U Xg tr L eG hI hV hL hG cV i hβ hg c hc P hR hco⟩

end GlobalTheory.Mem.R3.LiftBrg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLatticesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_liftForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 → Seed.FrmC.StdLat (Vc X.toD7 i) → ∃ s : ∀ t, Seed.LiftSideT (famR X I hX U Xg tr) L cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) i t, (∀ t,       (∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG ((s t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _))) ∧
      Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef (s t).pres (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) (s t).pres ((famR X I hX U Xg tr).heckeLI i t)
        (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
        (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
        fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1)) ∧ BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (s t).pres.extL φ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.exists_liftSide | exact GlobalTheory.Mem.R3.LiftBrg.exists_liftSide | (intros; apply GlobalTheory.Mem.R3.LiftBrg.exists_liftSide <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlacesAllStates
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypePlacesCover

variable {D : D7}

theorem isConjPl_conjPlE (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE (D := D) P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE (D := D)]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
    show IsCMField.complexConj D.host.E (D.host.conj (x : D.host.E)) = _
    have h : D.host.conj (x : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) :=
      D.host.φ₀.injective (by
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
    rw [h]; exact IsCMField.complexConj_apply_apply D.host.E _
  rw [this]

theorem conjPlE_conjPlE (P : PlE D.host) : GlobalTheory.SplitConjPlace.conjPlE (D := D) (GlobalTheory.SplitConjPlace.conjPlE (D := D) P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), GlobalTheory.SplitConjPlace.cO_cO (D := D)]

theorem comap_conjPlE (P : PlE D.host) :
    (GlobalTheory.SplitConjPlace.conjPlE (D := D) P).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), GlobalTheory.SplitConjPlace.cO_algebraMap (D := D)]

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

theorem cover (k : Fin 2) (w : PlE D.host) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = GlobalTheory.SplitConjPlace.conjPlE (D := D) (D.naut.plGw k v) := by
  let T : Set (PlE D.host) := {u | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal}
  have hg : ∀ v, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := fun v => D.naut.plGw_over k v
  let f : D.nd.PlG k ⊕ D.nd.PlG k → T :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, hg v⟩) fun v => ⟨GlobalTheory.SplitConjPlace.conjPlE (D := D) (D.naut.plGw k v), by
      show _ ∈ (GlobalTheory.SplitConjPlace.conjPlE (D := D) _).asIdeal
      rw [GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), map_natCast]; exact hg v⟩
  have hne : ∀ a b, D.naut.plGw k a ≠ GlobalTheory.SplitConjPlace.conjPlE (D := D) (D.naut.plGw k b) := fun a b e =>
    D.naut.plGw_nconj k b a (e ▸ isConjPl_conjPlE _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · exact congrArg Sum.inl (D.naut.plGw_inj k e')
    · exact absurd e' (hne a b)
    · exact absurd e'.symm (hne b a)
    · have := congrArg (GlobalTheory.SplitConjPlace.conjPlE (D := D)) e'
      simp only [f, Sum.elim_inr, conjPlE_conjPlE] at this
      exact congrArg Sum.inr (D.naut.plGw_inj k this)
  have hT : T.ncard = 2 * D.R.f := by
    rw [← finrank_E D]; exact D.nd.g_split k
  have hc : Nat.card T = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, hT, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite T := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, hT]
    have : 0 < D.R.f := by show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos
    omega
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · exact ⟨v, Or.inr (congrArg Subtype.val hx).symm⟩

theorem gPlaces (D : D7) : GPlaces D := by
  refine ⟨fun k v => ⟨D.naut.plGw_over k v, GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩⟩, ?_, ?_⟩
  · rintro u ⟨w, hwu, k, hwk⟩
    obtain ⟨v, hv⟩ := cover k w hwk
    obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩
    refine ⟨k, v, s, HeightOneSpectrum.ext ?_, hs⟩
    have hu : u.asIdeal = (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [← hwu]
      rcases hv with rfl | rfl
      · rfl
      · exact comap_conjPlE _
    rw [hu, ← s.w_under, hs]
  · refine ⟨0, ?_⟩
    rw [← Fintype.card_pos_iff, D.nd.card_PlG 0]
    show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos

end GlobalTheory.TypePlacesCover

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.CompAtUniq

open Topology
open scoped WithZero

theorem ball_mem_nhds' {K : Type} [Field K] [Valued K ℤᵐ⁰] (x r : K) (hr : r ≠ 0) :
    {y | Valued.v (y - x) < Valued.v r} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation K ℤᵐ⁰).restrict r ≠ 0 := by simp [hr]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem val_div_sub_one_lt {K : Type} [Field K] [Valued K ℤᵐ⁰] {u y : K} {c : ℤᵐ⁰} (hu : u ≠ 0)
    (hc : c ≤ 1) (h : Valued.v (y - u) < Valued.v u * c) : y ≠ 0 ∧ Valued.v (u * y⁻¹ - 1) < c := by
  have hvu : Valued.v u ≠ 0 := by simpa using hu
  have hlt : Valued.v (y - u) < Valued.v u := lt_of_lt_of_le h (mul_le_of_le_one_right' hc)
  have hvy : Valued.v y = Valued.v u := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvy; exact hvu hvy.symm
  refine ⟨hy, ?_⟩
  have : u * y⁻¹ - 1 = -((y - u) * y⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hvy]
  have hpos : (0 : ℤᵐ⁰) < Valued.v u := pos_iff_ne_zero.2 hvu
  calc Valued.v (y - u) * (Valued.v u)⁻¹ < Valued.v u * c * (Valued.v u)⁻¹ :=
        mul_lt_mul_of_pos_right h (inv_pos.2 hpos)
    _ = c := by field_simp

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  intro L _ _ _ χ s ξ ξ' hξ hξ'
  obtain ⟨⟨N₁, hN₁⟩, hk⟩ := hξ
  obtain ⟨⟨N₂, hN₂⟩, hk'⟩ := hξ'
  ext1 u
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  have hπ' : Valued.v ((π : s.v.adicCompletion (maximalRealSubfield L))) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  set N := max N₁ N₂ with hN
  have hN1 : N₁ ≤ N := le_max_left _ _
  have hN2 : N₂ ≤ N := le_max_right _ _
  have hu0 : (u : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := u.ne_zero
  have hπ0 : (π : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := by
    intro h; rw [h, map_zero] at hπ'; exact (WithZero.exp_ne_zero) hπ'.symm
  have hvr : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) * (π : s.v.adicCompletion (maximalRealSubfield L)) ^ N)
      = Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) * WithZero.exp (-(N : ℤ)) := by
    rw [map_mul, map_pow, hπ', ← WithZero.exp_nsmul]; congr 2; simp
  have hnhds := ball_mem_nhds' (u : s.v.adicCompletion (maximalRealSubfield L)) _ (mul_ne_zero hu0 (pow_ne_zero N hπ0))
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v).mem_nhds hnhds
  rw [Set.mem_setOf_eq, hvr] at hx
  have hle : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  obtain ⟨hy0, hw⟩ := val_div_sub_one_lt hu0 hle hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  set k : Lˣ := Units.mk0 (algebraMap (maximalRealSubfield L) L x) ((map_ne_zero _).2 hx0) with hkdef
  have hik : ((Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k : _) : s.v.adicCompletion (maximalRealSubfield L))
      = algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x := by
    simp [k]
  set w : (s.v.adicCompletion (maximalRealSubfield L))ˣ := u * (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)⁻¹ with hwdef
  have hu : u = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k * w := by simp [w]
  have hw' : Valued.v ((w : s.v.adicCompletion (maximalRealSubfield L)) - 1) < WithZero.exp (-(N : ℤ)) := by
    have : (w : s.v.adicCompletion (maximalRealSubfield L)) = (u : s.v.adicCompletion (maximalRealSubfield L)) *
        (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x)⁻¹ := by
      rw [hwdef, Units.val_mul, Units.val_inv_eq_inv_val, hik]
    rw [this]; exact hw
  have e1 : ξ w = 1 := hN₁ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  have e2 : ξ' w = 1 := hN₂ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  clear_value w
  rw [hu, map_mul, map_mul, e1, e2, hk, hk']

end GlobalTheory.CompAtUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUniqueStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  first | exact @GlobalTheory.CompAtUniq.main | exact GlobalTheory.CompAtUniq.main | (intros; apply GlobalTheory.CompAtUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesOfAdmissibleTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SepPlaces

theorem mem_of_conj {R : Ranks} (H : Host R) (p : ℕ) {w w' : HeightOneSpectrum (𝓞 H.E)}
    (h : IsConjPl H w w') : w ∈ placesOver H.E p ↔ w' ∈ placesOver H.E p := by
  have hc : ((p : 𝓞 H.E) : H.E) = H.conj ((p : 𝓞 H.E) : H.E) := by
    push_cast; exact (map_natCast _ p).symm
  exact h _ _ hc

theorem not_mem_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : w ∈ placesOver E p) (h2 : w ∈ placesOver E q) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨a, b, hab⟩ := hc
  have h1' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal := h2
  have : (1 : 𝓞 E) ∈ w.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1') (w.asIdeal.mul_mem_left _ h2')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem same_v (D : D7) (s s' : SplitPlace D.host.E) (h : s.v = s'.v) :
    s.w = s'.w ∨ IsConjPl D.host s'.w s.w := by
  apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
  show Ideal.comap _ _ = _
  rw [s'.w_under, h]

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

theorem sep_gen (D : D7) {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ)
    (hQ : ∀ P ∈ Q, P ∉ D.ntw.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k'))
    (P' : PlE D.host) (hP' : P' ∈ M.QP ∨ P' ∈ M.DP) :
    ¬ (P' ∈ M.QP ∧ P' ∈ M.DP) ∧ (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P').v) ∧
      (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P').v → P'' = P') ∧
      (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P').v → P'' = P') := by
  set pX := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hpX
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ P ∈ placesOver D.host.E pX := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq i]
  have hpXp : pX.Prime := by
    rw [hpX]; split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hpXg : ∀ kk, pX ≠ D.host.g kk := fun kk => by
    rw [hpX]; split_ifs
    · exact (D.host.pde_ne_g kk).2
    · exact (D.host.pde_ne_g kk).1

  have hnotG : ∀ P, (P ∈ M.QP ∨ P ∈ M.DP) → ∀ kk, P ∉ placesOver D.host.E (D.host.g kk) := by
    rintro P (hP | hP) kk hg
    · exact (hQ P (M.QP_sub hP)).2 kk hg
    · exact not_mem_two hpXp (D.host.g_prime kk) (hpXg kk) ((hpD P).1 (M.DP_sub hP)) hg
  have hwP' : (M.sp P').w = P' := M.sp_w P' (by rcases hP' with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact (hQ P' (M.QP_sub h1)).1 (M.DP_sub h2)
  · intro kv hv
    have hwG : (M.sp (NX.pG D kv)).w = NX.pG D kv := M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))
    have hG : NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := D.naut.plGw_over kv.1 kv.2
    rcases same_v D _ _ hv with h | h
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 (h ▸ hG)
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 ((mem_of_conj D.host _ h).2 hG)
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact M.QP_nconj P' h1 P'' hP'' h
      · exact (hQ P'' (M.QP_sub hP'')).1
          ((hpD P'').2 ((mem_of_conj D.host _ h).1 ((hpD P').1 (M.DP_sub h1))))
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact (hQ P' (M.QP_sub h1)).1
          ((hpD P').2 ((mem_of_conj D.host _ h).2 ((hpD P'').1 (M.DP_sub hP''))))
      · exact M.DP_nconj P' h1 P'' hP'' h

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

end GlobalTheory.SepPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddChar
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.ResidueChar

@[reducible] def unitsDivC : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnitC {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend_subring {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDivC
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnitC ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnitC, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnitC, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add (f := _)] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnitC] using e

theorem red_eq_zero_of_lt_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (y : v.adicCompletionIntegers K)
    (hy : Valued.v (y : v.adicCompletion K) < 1) : red y = 0 := by
  by_contra h
  set n : ℕ := (-(red y)⁻¹ : ZMod p).val with hn
  have hnc : ((n : ℕ) : ZMod p) = -(red y)⁻¹ := ZMod.natCast_zmod_val _
  set z : v.adicCompletionIntegers K := 1 + y * (n : v.adicCompletionIntegers K) with hz
  have hred : red z = 0 := by
    rw [hz, map_add (f := _), map_one, map_mul, map_natCast, hnc, mul_neg, mul_inv_cancel₀ h, add_neg_cancel]
  have hlt : Valued.v ((y * (n : v.adicCompletionIntegers K) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 := by
    have hn1 : Valued.v (((n : v.adicCompletionIntegers K)) : v.adicCompletion K) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
    rw [Subring.coe_mul, map_mul]
    calc Valued.v (y : v.adicCompletion K) * Valued.v (((n : v.adicCompletionIntegers K)) : v.adicCompletion K)
        ≤ Valued.v (y : v.adicCompletion K) * 1 := by gcongr
      _ = Valued.v (y : v.adicCompletion K) := mul_one _
      _ < 1 := hy
  have hz1 : Valued.v ((z : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    rw [hz, Subring.coe_add, Subring.coe_one]
    rw [Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact hlt
  have hu : IsUnit z := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).2 hz1
  have hu' : IsUnit (red z) := hu.map red
  rw [hred] at hu'
  exact not_isUnit_zero hu'

theorem exists_addChar_completion_lift_residue : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (ψ' : AddChar (ZMod p) ℂ), ψ' ≠ 1 →
    ∃ ψ₀ : AddChar (v.adicCompletion K) ℂ, (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ (∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1) ∧
      ∀ y : v.adicCompletionIntegers K, ψ₀ (y : v.adicCompletion K) = ψ' (red y) := by
  intro K _ _ v p _ red ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend_subring (v.adicCompletionIntegers K).toSubring
    (ψ'.compAddMonoidHom red.toAddMonoidHom)
  refine ⟨ψ₀, fun x hx => ?_, ?_, fun x => h x⟩
  · have hx1 : x ∈ v.adicCompletionIntegers K :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : red ⟨x, hx1⟩ = 0 := red_eq_zero_of_lt_one v p red ⟨x, hx1⟩ hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (v.adicCompletionIntegers K).toSubring) : v.adicCompletion K) from rfl, e1]
    show ψ' (red ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    have hy' : ((y.val : ℕ) : ZMod p) = y := ZMod.natCast_zmod_val y
    let x : v.adicCompletionIntegers K := (y.val : v.adicCompletionIntegers K)
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : v.adicCompletion K) = ψ₀ ((x : (v.adicCompletionIntegers K).toSubring) : v.adicCompletion K) from rfl, e1]
    show ψ' (red x) ≠ 1
    rw [show red x = y by simp only [x, map_natCast, hy']]
    exact hy

end GlobalTheory.ResidueChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddCharStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_completion_of_residue_addChar : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (ψ' : AddChar (ZMod p) ℂ), ψ' ≠ 1 →
    ∃ ψ₀ : AddChar (v.adicCompletion K) ℂ, (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ (∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1) ∧
      ∀ y : v.adicCompletionIntegers K, ψ₀ (y : v.adicCompletion K) = ψ' (red y) := by
  first | exact @GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue | exact GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue | (intros; apply GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEqLocalFactorAtTypePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEqLocalFactorAtTypePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevChiAt

section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_comp (s : SplitPlace L) :
    s.proj = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom.comp
      (compAt L s.v) := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem locM_eq_one (s : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (κ : GAf L n)
    (hκ : TrivOutside {v} κ) (hne : s.v ≠ v) : NX.locM s κ = 1 := by
  have h := hκ s.v (by simpa using hne)
  have e : NX.locM s κ = ((κ.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)).map
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom := by
    rw [Matrix.map_map, ← RingHom.coe_comp, ← proj_eq_comp]
    rfl
  rw [e, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Gen

variable {D : D7}

section Red
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intLift_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (1 : v.adicCompletion (maximalRealSubfield L)) = 1 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · exact absurd (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem h

theorem intLift_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (0 : v.adicCompletion (maximalRealSubfield L)) = 0 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · rfl

theorem redMat_topR_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) {n r : ℕ} (h : r ≤ n) :
    NX.redMat v red (NX.topR h (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))) = 1 := by
  ext a c
  simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
  by_cases hac : a = c
  · subst hac; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne (fun e => hac (Fin.castLE_injective _ e)), Matrix.one_apply_ne hac, intLift_zero, map_zero]

theorem detT_one {R : Type} [CommRing R] (n r : ℕ) : NX.detT r (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold NX.detT
  have : (1 : Matrix (Fin n) (Fin n) R).submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) = 1 := by
    ext a c
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

end Red

theorem gVal_one (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  classical
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 := by
    apply Units.ext
    rw [NX.glOf_val _ (by simp)]
    rfl
  have hpsi : NX.psiUTot D i b (1 : G0g D.nd) = 1 := by
    unfold NX.psiUTot
    rw [dite_eq_left (Subgroup.one_mem _)]
    have : (⟨1, Subgroup.one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [this, map_one]; rfl
  unfold NX.gVal
  erw [redMat_topR_one, hgl, Pi.mulSingle_one, hpsi, detT_one, intLift_one, map_one red, map_one, one_mul]
  rw [dite_eq_left isUnit_one]
  have : (isUnit_one : IsUnit (1 : ZMod (D.host.g kv.1))).unit = 1 := Units.ext rfl
  rw [this, map_one]
  exact map_one _

theorem loc_one_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) :
    NX.locM s (1 : GAf L n) = 1 := by
  simp [NX.locM]

theorem chi_eq_at : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ (h : κ ∈ M.J), TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      ((M.χ ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) =
        NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hkv hQ hD κ h hκ
  have hG : ∀ kv, kv ≠ kv0 → NX.locM (M.sp (NX.pG D kv)) κ = 1 := fun kv hne => locM_eq_one _ κ hκ (hkv kv hne)
  have hQl : ∀ P ∈ M.QP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hQ P hP)
  have hDl : ∀ P ∈ M.DP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hD P hP)
  have h1 := M.chi_eq 1 M.J.one_mem
  have e1 : (⟨1, M.J.one_mem⟩ : M.J) = 1 := rfl
  rw [e1, map_one, Units.val_one] at h1
  simp only [loc_one_eq, gVal_one, Finset.prod_const_one, one_mul] at h1
  rw [M.chi_eq κ h, Fintype.prod_eq_single kv0 (fun kv hne => by rw [hG kv hne, gVal_one]), mul_assoc]
  conv_rhs => rw [← mul_one (NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ))]
  congr 1
  rw [h1]
  congr 1
  · exact Finset.prod_congr rfl fun P hP => by rw [hQl P hP]
  · exact Finset.prod_congr rfl fun P hP => by rw [hDl P hP]

end GlobalTheory.LevChiAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEqLocalFactorAtTypePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_eq_localFactor_at_typePlace : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ (h : κ ∈ M.J), TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      ((M.χ ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) =
        NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ) := by
  first | exact @GlobalTheory.LevChiAt.chi_eq_at | exact GlobalTheory.LevChiAt.chi_eq_at | (intros; apply GlobalTheory.LevChiAt.chi_eq_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypeCharRead

variable {K : Type} [Field K] [NumberField K]

theorem isUnit_of_val_eq_one (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K)
    (h : Valued.v (x : v.adicCompletion K) = 1) : IsUnit x :=
  (Valuation.integer.integers (Valued.v (R := v.adicCompletion K))).isUnit_iff_valuation_eq_one.2 h

theorem red_eq_zero_of_val_lt_one (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (x : v.adicCompletionIntegers K)
    (hx : Valued.v (x : v.adicCompletion K) < 1) : red x = 0 := by
  by_contra h
  have ht : (red x)⁻¹ * red x = 1 := inv_mul_cancel₀ h
  set n : ℕ := ((red x)⁻¹ : ZMod p).val with hn
  set z : v.adicCompletionIntegers K := 1 - (n : v.adicCompletionIntegers K) * x with hz
  have hrz : red z = 0 := by
    rw [hz, map_sub, map_mul, map_one, map_natCast, hn, ZMod.natCast_zmod_val, ht, sub_self]
  have hnv : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
  have hlt : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K)) < 1 := by
    rw [map_mul]
    calc Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) * Valued.v (x : v.adicCompletion K)
        ≤ 1 * Valued.v (x : v.adicCompletion K) := by gcongr
      _ < 1 := by rw [one_mul]; exact hx
  have hvz : Valued.v (z : v.adicCompletion K) = 1 := by
    have e : (z : v.adicCompletion K) = 1 - ((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K) := by
      rw [hz]; push_cast; rfl
    rw [e]
    exact Valuation.map_one_sub_of_lt _ hlt
  have hu := (isUnit_of_val_eq_one v z hvz).map red
  rw [hrz] at hu
  exact not_isUnit_zero hu

end GlobalTheory.TypeCharRead

open Formalism.L2.DIV (kP)
open Formalism.IndefR.Links (IsRes)

namespace GlobalTheory.TypeCharRead

theorem compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv s hsw χ hχ red
  haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D 0
  obtain ⟨φ, hφs, hφ0, hφa, -⟩ := h4 s
  have hker : RingHom.ker φ ≤ RingHom.ker red := fun x hx =>
    (RingHom.mem_ker).2 (red_eq_zero_of_val_lt_one s.v red x ((hφ0 x).1 ((RingHom.mem_ker).1 hx)))
  set ι := φ.liftOfSurjective hφs ⟨red, hker⟩ with hι
  have hιφ : ∀ x, ι (φ x) = red x := fun x => RingHom.liftOfSurjective_comp_apply φ hφs ⟨red, hker⟩ x
  have hred0 : ∀ x, red x = 0 → Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := by
    intro x hx
    refine lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2) (fun h1 => ?_)
    have hu := (isUnit_of_val_eq_one s.v x h1).map red
    rw [hx] at hu
    exact not_isUnit_zero hu
  let c : (kP s.w)ˣ →* ℂˣ :=
    (Units.map (embLL0 D).toMonoidHom).comp ((τ (j.1 + 1) kv).comp (Units.map ι.toMonoidHom))
  have hres : IsRes (cf.mu0 j * χ) s.w c := by
    intro a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have ha0 : ((a : 𝓞 D.host.E) : D.host.E) ≠ 0 := hk ▸ k.ne_zero
    obtain ⟨hia, hφia⟩ := hφa a
    set x : (ZMod (D.host.g kv.1))ˣ := Units.map ι.toMonoidHom u with hx
    have hxv : (x : ZMod (D.host.g kv.1)) = red ⟨_, hia⟩ := by
      show ι (u : kP s.w) = _
      rw [hu, ← hφia, hιφ]
    have hmem : (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a) ∈ (NX.pG D kv).asIdeal := by
      rw [← hsw]
      obtain ⟨hib, hφib⟩ := hφa (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφib]
      apply (hφ0 _).2
      apply hred0
      have e : (⟨_, hib⟩ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) =
          (((x : ZMod (D.host.g kv.1)).val : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) - ⟨_, hia⟩ := by
        apply Subtype.ext
        show s.i (((((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a : 𝓞 D.host.E)) : D.host.E) = _
        push_cast
        rw [map_sub, map_natCast]
      rw [e, map_sub, map_natCast, ZMod.natCast_zmod_val, hxv, sub_self]
    have h61 := GlobalTheory.T.levelCharacters_typePlaces_eq_local_components hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x a ha0 hmem
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : χ.locK s.w k = 1 := hχ _ hunit
    have hk' : Units.mk0 ((a : 𝓞 D.host.E) : D.host.E) ha0 = k := Units.ext hk.symm
    rw [hk', ← hsw] at h61
    apply Units.ext
    have e : (cf.mu0 j * χ).locK s.w k = (cf.mu0 j).locK s.w k * χ.locK s.w k := rfl
    rw [e, h2, mul_one, ← h61]
    rfl
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue D s φ hφs hφ0 hφa _ c hres
  refine ⟨ξ, hξc, fun y hy uu huu => ?_⟩
  have hyv : Valued.v (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
    refine le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2) (not_lt.1 fun hlt => ?_)
    have h0 := red_eq_zero_of_val_lt_one s.v red y hlt
    rw [h0] at hy
    exact not_isUnit_zero hy
  have hyu : IsUnit (φ y) := (isUnit_of_val_eq_one s.v y hyv).map φ
  rw [hξr uu y hyu.unit huu.symm hyu.unit_spec.symm]
  have hw : Units.map ι.toMonoidHom hyu.unit = hy.unit := by
    apply Units.ext
    show ι ((hyu.unit : kP s.w)) = red y
    rw [hyu.unit_spec, hιφ]
  show (embLL0 D) ((τ (j.1 + 1) kv (Units.map ι.toMonoidHom hyu.unit) : (↥D.LL0)ˣ) : ↥D.LL0) = _
  rw [hw]

end GlobalTheory.TypeCharRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compAt_baseCharacter_mul_unramified_eq_typeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  first | exact @GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt | exact GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt | (intros; apply GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt <;> assumption)
end
end
