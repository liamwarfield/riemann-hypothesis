module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValuesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommute
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCommute

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem hLC_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  classical
  intro D M C hR hstd hgen hsplit j w v k v' k'
  by_cases h : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k
  swap
  · have : hLC (mt0 M) C.Q hR j w v k = 0 := by unfold hLC; rw [dite_eq_right h]
    rw [this]; exact Commute.zero_left _
  by_cases h' : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v' k'
  swap
  · have : hLC (mt0 M) C.Q hR j w v' k' = 0 := by unfold hLC; rw [dite_eq_right h']
    rw [this]; exact Commute.zero_right _
  obtain ⟨⟨h1, h2⟩, hg⟩ := h
  obtain ⟨-, hg'⟩ := h'
  obtain ⟨B, hB, hBv⟩ := hgen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hsplit v hg.1
  obtain ⟨s', ϖ', hc', hu'⟩ := hsplit v' hg'.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hsB' : s'.v ∉ B := hBv v' k' s' hg' hc'
  have hstd' := hstd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hB s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hcomm := hstd'.2.2.1 s' ϖ' k' hsB' hu' hg'.2.2.2.2.1 hg'.2.2.2.2.2
  rw [commute_iff_eq]
  ext x
  apply Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective
  apply (M (D.what₂.muTw w) j h1 h2).real_inj
  have hf : (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x) ∈
      NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ := by
    rw [← (M (D.what₂.muTw w) j h1 h2).real_range]; exact LinearMap.mem_range_self _ _
  have e1 := hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu
  have e2 := hLC_spec (mt0 M) C.Q hR j w v' k' h1 h2 hg' s' ϖ' hc' hu'
  simp only [Module.End.mul_apply]
  change (mt0 M (D.what₂.muTw w) j h1 h2).real _ = (mt0 M (D.what₂.muTw w) j h1 h2).real _
  rw [e1, e2, e2, e1]
  exact hcomm _ hf

end GlobalTheory.HeckeLocCommute
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommuteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedHeckeOperators_at_generators_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  first | exact @GlobalTheory.HeckeLocCommute.hLC_commute | exact GlobalTheory.HeckeLocCommute.hLC_commute | (intros; apply GlobalTheory.HeckeLocCommute.hLC_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationHeckeRingIsLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationHeckeRingIsLocalRing
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.TLocal

theorem isLocalRing_of_congr {O X : Type} [CommRing O] [IsLocalRing O] [Finite X] [Nonempty X] (T : Subalgebra O (X → O))
    (h : ∀ f ∈ T, ∀ x y, f x - f y ∈ IsLocalRing.maximalIdeal O) : IsLocalRing T := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have key : ∀ f : T, IsUnit ((f : X → O) x) → IsUnit f := by
    intro f hx
    have : Algebra.IsIntegral T (X → O) := Algebra.IsIntegral.tower_top O
    have hu : IsUnit (algebraMap T (X → O) f) := by
      refine Pi.isUnit_iff.2 fun y => ?_
      by_contra hy
      have h1 := add_mem (h f f.2 x y) ((IsLocalRing.mem_maximalIdeal _).2 hy)
      exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using h1) hx
    have hl := RingHom.IsIntegral.isLocalHom (f := algebraMap T (X → O))
      (fun g => Algebra.IsIntegral.isIntegral g) Subtype.val_injective
    exact hl.map_nonunit f hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → O) x)).imp (key f) (key (1 - f))

theorem sub_mem_of_ker_eq {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] (ψ φ : A →ₐ[O] O)
    (h : RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom) = RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom))
    (a : A) : ψ a - φ a ∈ IsLocalRing.maximalIdeal O := by
  have h1 : a - algebraMap O A (φ a) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom) := by
    rw [RingHom.mem_ker]; simp
  rw [← h, RingHom.mem_ker] at h1
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa using h1


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (i : LocT B), IsLocalRing (TOf B i) := by
  intro R H what₂ B hs hd i
  have := xFin_of hs hd i
  have := xNe_of hs hd i
  refine isLocalRing_of_congr (TOf B i) fun f hf x y => ?_
  rw [← Ideal.Quotient.eq]
  unfold TOf at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    refine Ideal.Quotient.eq.2 ?_
    simp only [hTfun, dif_pos hvk]
    exact sub_mem_of_ker_eq x.1 y.1 (x.2.1.trans y.2.1.symm) _
  | algebraMap r => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, map_add (f := _), hf, hg]
  | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]

end GlobalTheory.HeckeLocN.TLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationHeckeRingIsLocalRingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_heckeRing_isLocalRing : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (i : LocT B), IsLocalRing (TOf B i) := by
  first | exact @GlobalTheory.HeckeLocN.TLocal.main | exact GlobalTheory.HeckeLocN.TLocal.main | (intros; apply GlobalTheory.HeckeLocN.TLocal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsOverRealPlacesAndConjStable
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsOverRealPlacesAndConjStable
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.CondConj

theorem unrAt_of_under_eq {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P Q : HeightOneSpectrum (𝓞 E)}
    (hPQ : Q.under (𝓞 F) = P.under (𝓞 F)) (hu : χ.UnrAt P) : χ.UnrAt Q := by
  by_cases e : Q = P
  · rwa [e]
  obtain rfl := ((GlobalTheory.NormOneUnit.under_eq_iff hF hr hc P Q).1 hPQ).resolve_left e
  intro x hx
  obtain ⟨k, y, hk, hy, hcong⟩ := (GlobalTheory.localUnit_congr_global E _ x hx).1
  have hv : (Col.conjPrime₂ P).valuation E (k : E) = 1 := by
    rw [hk]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hy
  have hkQ : IsUnitAt (Col.conjPrime₂ P) (atFin (Col.conjPrime₂ P) k) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ (k : E)).trans hv
  have hxk : IsUnitAt (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : χ.loc (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) = 1 := ht _ _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have hs0 : star (k : E) ≠ 0 := star_ne_zero.2 k.ne_zero
  have h2 := GlobalTheory.NormOneProd.split_unit hF hr hc hχ ht (Ne.symm e) (y' := Units.mk0 _ hs0) rfl hv
  rw [GlobalTheory.NormOneUnit.locK_unr hu (y := Units.mk0 _ hs0) ((GlobalTheory.CharVal.valuation_conjP P _).symm.trans hv), one_mul] at h2
  exact h1.trans h2

theorem cond_of_under_eq {R : Ranks} (H : Host R) {l : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 H.E))} {χ : HChar H.E}
    (h : IsPsi l Q χ) {v v' : HeightOneSpectrum (𝓞 H.E)} (hv : v.under (𝓞 H.F) = v'.under (𝓞 H.F)) (hQ : v ∈ Q) : v' ∈ Q := by
  letI := H.cmStar
  haveI : IsCMField H.E := H.isCMField_hostE
  by_contra hn
  refine (h.ram v).1 (unrAt_of_under_eq (F := H.F) (fun x => ?_) ?_ ?_ h.triv h.tame hv ((h.ram v').2 hn)) hQ
  · exact IsCMField.complexConj_apply_eq_self H.E x
  · exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield H.E) H.E
  · by_contra hh
    push Not at hh
    exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext hh)

theorem under_eq_of_conj {R : Ranks} (H : Host R) {v v' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H v v') :
    v.under (𝓞 H.F) = v'.under (𝓞 H.F) := by
  ext a
  refine h (algebraMap (𝓞 H.F) (𝓞 H.E) a) (algebraMap (𝓞 H.F) (𝓞 H.E) a) ?_
  haveI : IsCMField H.E := H.isCMField_hostE
  apply H.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, ← IsCMField.complexEmbedding_complexConj]
  exact congrArg H.φ₀ (IsCMField.complexConj_apply_eq_self H.E (a : H.F)).symm

theorem cond_over_conj : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  intro D cf C tp h0
  have key : ∀ w (v v' : PlE D.host), v.under (𝓞 D.host.F) = v'.under (𝓞 D.host.F) → v ∈ C.Q w → v' ∈ C.Q w := by
    intro w v v' hv hQ
    by_cases hw : TwistedAt D w
    · exact cond_of_under_eq D.host (tp.psi_is w hw) hv hQ
    · rw [h0 w hw] at hQ
      exact absurd hQ (Finset.notMem_empty _)
  refine ⟨fun w v v' hQ ⟨v₀, h1, h2⟩ => key w v v' (HeightOneSpectrum.ext (h1.trans h2.symm)) hQ,
    fun w v v' hQ hc => key w v' v (under_eq_of_conj D.host hc).symm hQ⟩

end GlobalTheory.HeckeLocN.CondConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsOverRealPlacesAndConjStableStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistConductors_over_real_places_and_conj_stable : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  first | exact @GlobalTheory.HeckeLocN.CondConj.cond_over_conj | exact GlobalTheory.HeckeLocN.CondConj.cond_over_conj | (intros; apply GlobalTheory.HeckeLocN.CondConj.cond_over_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
  (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))

theorem mem_parLev_of_Q (i : Fin X.toD7.R.m) (t : TupU I U) (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t) := q.2.1

def rV (i : Fin X.toD7.R.m) (t : TupU I U) (x : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)) : G0 L.Pg X.toD7.R.r :=
  rTup (L.βV i) (L.datVt i t) x

theorem rV_one (i : Fin X.toD7.R.m) (t : TupU I U) : rV X I U L i t 1 = 1 := rTup_one

theorem rV_mul (i : Fin X.toD7.R.m) (t : TupU I U) {x y : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)}
    (hx : x ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t))
    (hy : y ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t)) :
    rV X I U L i t (x * y) = rV X I U L i t x * rV X I U L i t y := rTup_mul hx hy

def redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U) :
    (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q →* Gc X.B px where
  toFun q := eG.symm (rV X I U L i t
    (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    rw [rV_one, map_one]
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul]
    rw [rV_mul X I U L i t (mem_parLev_of_Q X I U L i t a) (mem_parLev_of_Q X I U L i t b), map_mul]

theorem redQ_apply (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = eG.symm (rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := rfl

theorem eG_redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    eG (redQ X I U L eG i t q) = rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) := by
  rw [redQ_apply]
  exact eG.apply_symm_apply _

theorem redQ_eq_one_iff (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = 1 ↔ (q : Bridge.Gf (Vc X.toD7 i)) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := by
  rw [redQ_apply, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    exact ⟨mem_parLev_of_Q X I U L i t q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

def ptS (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.nV) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  ptL X I U i t A k g

def redZ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  fun w => Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k))

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEq
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC cc)
open scoped Matrix

namespace GlobalTheory.PeriodUnipotent

theorem eq_of_span {E : Type} [Field E] {r : ℕ} (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ v w, Φ (v + w) = Φ v + Φ w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ (c : E) v, Φ (c • v) = σ c * Φ v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0) (h : ∀ v ∈ S, Φ v = Φ₀ v) (v : Fin r → E) : Φ v = Φ₀ v :=
  tendsto_const_nhds_iff.1 (GlobalTheory.PeriodLift.tendsto_of_span (𝓕 := (⊤ : Filter Unit)) S hS σ (fun _ => Φ) Φ₀
    (fun _ => ha) ha₀ (fun _ => hs) hs₀ hσ (fun v hv => by rw [h v hv]; exact tendsto_const_nhds) v)

theorem inv_mul_apply {r p : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hc : ∀ a : Fin r, (a : ℕ) < p → ∀ k, B k a = A k a)
    (hr : ∀ a : Fin r, ¬ (a : ℕ) < p → ∀ k, B⁻¹ a k = A⁻¹ a k) (a c : Fin r) (hac : c ≤ a) :
    (A⁻¹ * B) a c = (1 : Matrix (Fin r) (Fin r) ℂ) a c := by
  by_cases h : (c : ℕ) < p
  · rw [← Matrix.nonsing_inv_mul A (Ne.isUnit hA)]
    simp only [Matrix.mul_apply, hc c h]
  · have h' : ¬ (a : ℕ) < p := by
      have : (c : ℕ) ≤ a := hac
      omega
    rw [← Matrix.nonsing_inv_mul B (Ne.isUnit hB)]
    simp only [Matrix.mul_apply, hr a h']

theorem exists_unipotent_of_pc_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  intro E _ _ _ r X x x' hx hx' h
  have key : ∀ (τ : X.Ψ) (a c : Fin r), c ≤ a →
      ((mat x τ)⁻¹ * mat x' τ) a c = (1 : Matrix (Fin r) (Fin r) ℂ) a c := by
    intro τ
    refine inv_mul_apply (p := X.p0) _ _ (hx τ).1 (hx' τ).1 ?_ ?_
    · intro a ha k
      have := eq_of_span (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun v => hermC τ.1 X.Gm (col (mat x' τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [GlobalTheory.GenericFrames.pc, ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [GlobalTheory.PeriodLift.hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := eq_of_span (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun v => ((mat x' τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [GlobalTheory.GenericFrames.pc, ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
    fun τ i => ?_, funext fun τ => ?_⟩
  · change ((mat x τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit (hx τ).1)).ne_zero (hx' τ).1
  · exact (key τ a c hca.le).trans (Matrix.one_apply_ne hca.ne')
  · exact (key τ i i le_rfl).trans (Matrix.one_apply_eq i)
  · change mat x' τ = mat x τ * ((mat x τ)⁻¹ * mat x' τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit (hx τ).1)]

end GlobalTheory.PeriodUnipotent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEqStatement
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentTriangular_of_periodCoordinates_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  first | exact @GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | exact GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | (intros; apply GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterRamifiedAtConductorTrivialAboveL
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterRamifiedAtConductorTrivialAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.TwistRamLoc

def Disc (M : Type) : Type := M

instance (M : Type) [CommGroup M] : CommGroup (Disc M) := ‹CommGroup M›
instance (M : Type) : TopologicalSpace (Disc M) := ⊥
instance (M : Type) : DiscreteTopology (Disc M) := ⟨rfl⟩
instance (M : Type) [CommGroup M] : IsTopologicalGroup (Disc M) := inferInstance

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

end GlobalTheory.TwistRamLoc

namespace GlobalTheory.TwistRamLoc

theorem twist_ram_and_trivial_at_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  intro D cf C tp w hGAR _ hTied hTw hVal hAdm
  classical
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex (D.what₂.places.resChar w)
  have hP : IsPsi (D.what₂.places.resChar w) (C.Q w) (tp.psi w) := tp.psi_is w hTw
  obtain ⟨a, hord⟩ := hP.ord
  have hm : 0 < D.what₂.places.resChar w ^ a := pow_pos (D.what₂.places.resChar_prime w).pos a
  obtain ⟨r, hr, hL⟩ :=
    GlobalTheory.HeckeGal.IsGlobalArtin.exists_isLAdicOf ha ι (GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd hm hord)
  set Ψ := (C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)) with hΨ
  let φ : D.ntw.Ok (C.twI w) (C.k' w) →+* FractionRing (C.Oe w) :=
    (algebraMap (C.Oe w) (FractionRing (C.Oe w))).comp (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w))
  have hφ : Function.Injective φ :=
    (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))).comp (C.Oe_inj w)
  let Γ : Subgroup ((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) :=
    { carrier := {p | ∃ y : D.what₂.LL, ((p.1 : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) =
          ι.symm (D.what₂.embLL y) ∧ φ (p.2 : D.ntw.Ok (C.twI w) (C.k' w)) = C.embW w y}
      mul_mem' := by
        rintro p q ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
        exact ⟨y * y', by simp [h1, h1'], by simp [h2, h2']⟩
      one_mem' := ⟨1, by simp, by simp⟩
      inv_mem' := by
        rintro p ⟨y, h1, h2⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · rw [Prod.fst_inv, Units.val_inv_eq_inv_val, h1, map_inv₀, map_inv₀]
        · rw [Prod.snd_inv, map_units_inv φ, h2, map_inv₀] }
  let Φ : G D.host.E D.nd.Om →* Disc (((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) ⧸ Γ) :=
    (QuotientGroup.mk' Γ).comp (r.prod Ψ)
  have hrm : ∀ g, r g ^ (D.what₂.places.resChar w ^ a) = 1 := fun g => by
    have := DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hord) g
    rwa [MonoidHom.pow_apply] at this
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hr hm hrm
  have hΨo : IsOpen (Ψ.ker : Set (G D.host.E D.nd.Om)) := hAdm.2.2.1
  have hΦc : Continuous Φ := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' Φ (Subgroup.isOpen_mono (H₁ := r.ker ⊓ Ψ.ker) ?_ ?_)
    · intro g hg
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' Γ (r g, Ψ g) = 1
      rw [hg.1, hg.2]
      exact map_one _
    · rw [Subgroup.coe_inf]
      exact hro.inter hΨo
  let S : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
    C.Q w ∪ (finite_placesOver D.host.E (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w).ne_zero).toFinset
  have hΦ1 : Φ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha _ Φ hΦc S fun v hv A hA σ hσ => ?_
    have hvQ : v ∉ C.Q w := fun h => hv (Finset.mem_union_left _ h)
    have hvl : v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun h =>
      hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hu : (tp.psi w).UnrAt v := (hP.ram v).2 hvQ
    obtain ⟨y0, hy0⟩ := hVal v hu
    have hy0' : D.what₂.embLL y0 = (((tp.psi w).val v : ℂˣ) : ℂ) := by simpa [HChar.valTw] using hy0
    have hy : D.what₂.embLL y0⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by
      rw [map_inv₀, hy0', Units.val_inv_eq_inv_val]
    have h2 := hTied w hTw v hvQ hvl A σ hA hσ y0⁻¹ hy
    have h1 := hL.frob_unr ha (Or.inr rfl) hu hA hσ
    show QuotientGroup.mk' Γ (r σ, Ψ σ) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨y0⁻¹, ?_, h2.symm⟩
    show ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _
    rw [h1, map_inv₀, hy0', map_inv₀]
  have hmem : ∀ σ, (r σ, Ψ σ) ∈ Γ := fun σ => by
    have := DFunLike.congr_fun hΦ1 σ
    exact (QuotientGroup.eq_one_iff _).1 this
  have key : ∀ σ, r σ = 1 ↔ Ψ σ = 1 := fun σ => by
    obtain ⟨y, h1, h2⟩ := hmem σ
    constructor
    · intro h
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective,
        map_eq_one_iff _ D.what₂.embLL.injective] at h1
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h1, map_one, ← map_one φ] at h2
      exact Units.ext (hφ h2)
    · intro h
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h, Units.val_one, map_one, eq_comm, map_eq_one_iff _ (C.embW w).injective] at h2
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h2, map_one, map_one] at h1
      exact Units.ext h1
  refine ⟨fun v hv A hA => ?_, fun v hv A hA σ hσ => ?_⟩
  · have hnu : ¬ (tp.psi w).UnrAt v := fun h => (hP.ram v).1 h hv
    rw [← hL.unr_iff ha (Or.inr rfl) hA] at hnu
    push_neg at hnu
    obtain ⟨σ, hσ, hne⟩ := hnu
    exact ⟨σ, hσ, fun h => hne ((key σ).2 h)⟩
  · have hloc : (tp.psi w).loc v = 1 := MonoidHom.ext (hP.atl v hv)
    exact (key σ).1 (((hL.dec_triv ha hr (Or.inr rfl) hA).2 hloc) σ hσ)

end GlobalTheory.TwistRamLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterRamifiedAtConductorTrivialAboveLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  first | exact @GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l | exact GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l | (intros; apply GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCont

open IsLocalRing

theorem continuous_of_le_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (h : maximalIdeal A ≤ (maximalIdeal B).comap φ) : Continuous φ := by
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [isAdic_iff] at hA hB
  intro s hs
  simp only [map_zero] at hs
  obtain ⟨n, hn⟩ := hB.2 s hs
  have h1 : ((maximalIdeal A ^ n : Ideal A) : Set A) ∈ nhds (0 : A) :=
    (hA.1 n).mem_nhds (Ideal.zero_mem _)
  refine Filter.mem_map.2 (Filter.mem_of_superset h1 fun a ha => hn ?_)
  have : (maximalIdeal A ^ n).map φ ≤ maximalIdeal B ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n
  exact this (Ideal.mem_map_of_mem φ ha)

theorem comap_maximalIdeal_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal O))

theorem p_mem_maximalIdeal {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : ((p : ℕ) : O) ∈ maximalIdeal O := by
  have hp : ((p : ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  rw [← comap_maximalIdeal_padicInt O] at hp
  simpa using hp

theorem le_comap_of_padicInt {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [IsLocalRing A] [Algebra ℤ_[p] A]
    [Module.Finite ℤ_[p] A] [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ z, φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[p] B z) : maximalIdeal A ≤ (maximalIdeal B).comap φ := by
  have hc : ((maximalIdeal B).comap φ).comap (algebraMap ℤ_[p] A) = maximalIdeal ℤ_[p] := by
    rw [Ideal.comap_comap, ← comap_maximalIdeal_padicInt B]
    congr 1
    exact RingHom.ext hφ
  haveI : ((maximalIdeal B).comap φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ_[p] A)
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance))
      ((maximalIdeal B).comap φ) (by rw [hc]; infer_instance)
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem continuous_of_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = q) {A B : Type} [CommRing A] [IsLocalRing A]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [IsLocalRing B]
    [Algebra ℤ_[q] B] [Module.Finite ℤ_[q] B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[q] B z') : Continuous φ := by
  subst hpq
  exact continuous_of_le_comap hA hB φ (le_comap_of_padicInt φ fun z => hφ z z HEq.rfl)

theorem continuous_algebraMap_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (maximalIdeal O)) :
    Continuous (algebraMap ℤ_[p] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] O) ?_
  rw [ContinuousAt, map_zero, hO.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[p]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (p_mem_maximalIdeal O) n)

section Units

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_units {O : Type} [Monoid O] [TopologicalSpace O] (φ : Γ →* Oˣ)
    (h : Continuous fun g => (φ g : O)) : Continuous φ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have : (fun g => ((φ g)⁻¹ : Oˣ).val) = fun g => (φ g⁻¹ : O) := by
    funext g; rw [map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem continuous_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B] (f : A →* B)
    (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

theorem continuous_of_isOpen_ker {N : Type} [Group N] [TopologicalSpace N] (φ : Γ →* N)
    (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine IsLocallyConstant.continuous fun s => ?_
  have e : φ ⁻¹' s = ⋃ x ∈ φ ⁻¹' s, (fun g => x⁻¹ * g) ⁻¹' (φ.ker : Set Γ) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, exists_prop]
    constructor
    · intro hg; exact ⟨g, hg, inv_mul_cancel _⟩
    · rintro ⟨x, hx, hxg⟩
      rw [inv_mul_eq_one] at hxg
      rwa [← hxg]
  rw [e]
  exact isOpen_biUnion fun x _ => h.preimage (continuous_const.mul continuous_id)

end Units

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem chiN_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  intro D M C hR X hS twC ψ0 hP htw hker i c
  have hadic : ∀ j w, IsAdic (maximalIdeal (OcC X j w)) := oc_adic X
  have htwc : ∀ j w, Continuous (twC j w) := fun j w =>
    continuous_of_heq (C.twI_l w) (D.ntw.twistBaseCoefficientRing_isAdic (C.twI w)) (hadic j w) (twC j w) (htw j w)
  have h1 : Continuous (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i)
      (C.sd (wOf (base M C hR X hS) i))) :=
    continuous_units _ (D.ntw.twistCharacterFamily_continuous _ _ _)
  have h2 : Continuous (psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)) :=
    continuous_of_isOpen_ker _ (hker _ _)
  have h3 : Continuous (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (htwc _ _)
  haveI : Fact (lOf (base M C hR X hS) i).Prime := ⟨D.what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).algOc _ _
  haveI : Module.Finite ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).finOc _ _
  have h4 : Continuous (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (continuous_algebraMap_padicInt _ (hadic _ _))
  have h5 := continuous_cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i)
  refine Units.continuous_val.comp ?_
  change Continuous fun g =>
    ((show (OOf (base M C hR X hS) i)ˣ from (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom)
      (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i) (C.sd (wOf (base M C hR X hS) i)) g)) *
      (show (OOf (base M C hR X hS) i)ˣ from psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i) g)) *
    (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom
      (cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i) g)) ^ (-((c : ℤ) - 1))
  exact ((h3.comp h1).mul h2).mul ((h4.comp h5).zpow _)

end GlobalTheory.HeckeLocCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuousStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_galoisCharacter_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  first | exact @GlobalTheory.HeckeLocCont.chiN_continuous | exact GlobalTheory.HeckeLocCont.chiN_continuous | (intros; apply GlobalTheory.HeckeLocCont.chiN_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstOrtho
namespace GlobalTheory.OneMapRef.Kappa

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.AdTh.GenConst
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ex_eq [Algebra c.F ℂ] {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (A A' : AnFib X bas idx e x L y) :
    A.ex = A'.ex :=
  GlobalTheory.CuspFamilyCompare.exp_unique A.ex_add A'.ex_add A.hol A'.hol (fun j => y.u (e j).1 (e j).2)
    (fun j => by simpa only [Equiv.symm_apply_apply] using A.der (e j))
    (fun j => by simpa only [Equiv.symm_apply_apply] using A'.der (e j))

theorem exists_root {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l L mk) {n N : ℕ}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (hY : IsRoots l L mk N Y) {y : Matrix (Fin n) (Fin r) E}
    (hy : ∀ b, (l.M : E) • y b ∈ Mfr l • L) : ∃ q, ∀ b, Y q b - y b ∈ L := by
  have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (LevCover.M_pos l).ne'
  choose a ha t ht h using fun b => hmk.surj _ (hy b)
  refine ⟨fun b => Submodule.Quotient.mk (a b), fun b => ?_⟩
  obtain ⟨⟨a', ha', hq, h'⟩, -⟩ := hY (fun b => Submodule.Quotient.mk (a b)) b
  obtain ⟨d, hd⟩ := LevCover.modN_of_mem_both l ((Submodule.Quotient.eq _).1 hq) (Submodule.sub_mem _ ha' (ha b))
  have e₀ : mk a' = mk (a b) + (l.M : E) • mk d := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hd, ← map_add (f := _), add_sub_cancel]
  have e₁ : y b = (l.M : E)⁻¹ • mk (a b) + t b := by
    rw [← inv_smul_smul₀ hM0 (y b), h, smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
  rw [e₀, smul_add, inv_smul_smul₀ hM0] at h'
  convert L.sub_mem (L.add_mem h' (hmk.mem d)) (ht b) using 1
  rw [e₁]
  abel

theorem exists_const {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (hr1 : 1 ≤ r) (k : U.Comp) (t : ℝ) (ht : ∀ τ, (U.X k).c τ = t) (n : ℕ) (hn : Even n)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas)
    (hI : ∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (e j).1) (e j).2)
    (v : TF n g) (hv : IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v) :
    ∃ C : ℂ, ∀ x : (U.X k).dom, (U.X k).IsOrtho x.1 → letI : Algebra c.F ℂ := σ.toAlgebra
      ∀ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC U k x)) (ϑ : (Fin g → ℂ) → ℂ), A.Reads 1 (unC U k x).s ϑ →
        ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hC := GlobalTheory.ChartFree.chartIndep
  obtain ⟨W⟩ := nonempty_uw hU
  obtain rfl : g = W.g := Fin.equiv_iff_eq.1 ⟨e.trans W.e.symm⟩
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, hDe, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  subst hDe
  obtain rfl : idx = Dc.idx := idx_unique hs fun x u j => (hI x u j).trans (Dc.per_eq x u j).symm
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv
  have hpt : ∀ x (hx : x ∈ (U.X k).dom), IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib (U.X k) bas Dc.idx Dc.e x (U.X k).Λ (unC U k ⟨x, hx⟩)) (ϑ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC U k ⟨x, hx⟩).s ϑ ∧
        IsTheta1 (U.X k) bas Dc.idx (H.w0 : E) x (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas Dc.idx x (U.X k).Λ ϑ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ (z b) = κ * thA (U.X k) bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨π, hπ⟩ : ∃ π : Fin W.g ≃ Fin W.g, π.trans W.e = Dc.e := ⟨Dc.e.trans W.e.symm, by ext1; simp⟩
    have hπ' : ∀ j, W.e j = Dc.e (π.symm j) := fun j => by rw [← hπ]; simp
    have hid : π.trans (π.symm.trans Dc.idx) = Dc.idx := by ext1; simp
    obtain ⟨A₀, hA₀, ϑ₀, hϑ₀, hm₀⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k bas (π.symm.trans Dc.idx) hs
      (fun x u j => by rw [hπ']; exact Dc.per_eq x u _) (fun j => by rw [hπ']; exact Dc.ty_eq _) ⟨x, hx⟩ hux
    have h1 := exists_anFib_trans π A₀
    have hmean := meanOne_trans π hm₀
    rw [hid, hπ] at h1
    rw [hid] at hmean
    obtain ⟨A, hA, hR⟩ := h1
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x _ _ A hs hx hL _ (hR _ hϑ₀)
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x hx _ hT
    exact ⟨κ, hnorm x hx hux _ κ hT hmean hκ, A, _, hA _ hA₀, hR _ hϑ₀, hT, hmean, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const (U.X k) (Formalism.L2.PjFree.laU U 0 n k) ρ hρ κ hκ
  refine ⟨C, fun x hox A ϑ hϑ => ?_⟩
  have hux : IsUnitFr (U.X k) x.1 := PullbackSections.PfSupAtUnit.dmin_ortho _ hox
  obtain ⟨A₀, ϑ₀, hA₀, -, hT₀, hmean, hprod₀⟩ := hpt x.1 x.2 hux
  have hA : A.Marked (W.mark k) := fun a ha => (hA₀ a ha).trans (congrFun (ex_eq A₀ A) _)
  obtain ⟨κ', hprod⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x.1 x.2 _
    (isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x.1 _ _ A hs x.2 hL _ hϑ)
  have hM := LevCover.M_pos l
  obtain ⟨-, -, h1, h2, hY⟩ := DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')
  obtain ⟨Y, hY⟩ := hY n l.M hM
  have ht0 : 0 < t := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
    rw [← ht ⟨τ, hτ⟩]
    exact mul_pos two_pos (norm_pos_iff.2 ((_root_.map_ne_zero τ).2 (U.X k).ξ0_ne))
  obtain ⟨y, hy, hne⟩ := exists_level_translate_jet_ne_zero E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn H.w0 hw' _ hL
    x.1 x.2 hox t ht0 ht (Mfr l) l.M l.odd (by rw [h1, h2]) v hv ϑ₀ _ hT₀ hmean hprod₀ 1 one_ne_zero
    (by rw [MvPolynomial.totalDegree_one]; exact le_trans (by norm_num) l.three_le)
  obtain ⟨q, hq⟩ := exists_root hmk hY hy
  have h3 := right_ne_zero_of_mul (hne _ hq)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  have hsec : f ∈ sec Xo c 0 n := GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩
  have hsb : IsSB (heisG (U.X k) bas (Y q) v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g bas Dc.idx n hs hn).2.2.2 (Y q) v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn Dc.k Dc.k'
    _ hsb _ (Dc.mem 1 hP.1)
  have hS := hU.2.2.2.2.1 0 n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = Formalism.L2.PjFree.laU U 0 n k := Dc.wt_eq
  rw [hwt] at hhol
  have hval : ∀ x' (hx' : x' ∈ (U.X k).dom)
      (A' : AnFib (U.X k) bas Dc.idx Dc.e x' (U.X k).Λ (unC U k ⟨x', hx'⟩)) (ϑ' : (Fin W.g → ℂ) → ℂ) (κ'' : ℂ),
      A'.Marked (W.mark k) → A'.Reads 1 (unC U k ⟨x', hx'⟩).s ϑ' →
      (∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ' (z b) = κ'' * thA (U.X k) bas Dc.idx v x' z) →
      Formalism.L2.PjFree.rdU U f k x' = κ'' * thP (U.X k) Dc.hr bas Dc.idx (heisG (U.X k) bas (Y q) v)
        (MvPolynomial.rename Dc.eL (MvPolynomial.map σ 1)) x' := fun x' hx' A' ϑ' κ'' hA' hϑ' hprod' => by
    have := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) bas Dc.idx Dc.e x' _ _ A' hs hx' hL Dw.p n Dc.hr
      Dc.eL hU.1 hn Dc.dir_eq nab hnab ϑ' v _ hϑ' hv hprod' (W.mark k) hmk hA' (fun b => levRep (q b)) (Y q)
      (fun b => by
        obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
        exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
          (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
      (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k ⟨x', hx'⟩))
    exact Eq.trans (dif_pos hx') this
  have h4 := hCe _ _ hS.1 hhol.1 (fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩)
    (fun x' hx' hu' => by
      obtain ⟨A', ϑ', hA', hϑ', -, -, hprod'⟩ := hpt x' hx' hu'
      exact hval x' hx' A' ϑ' _ hA' hϑ' hprod') x.1 x.2
  rw [hval x.1 x.2 A ϑ κ' hA hϑ hprod, map_one, map_one] at h4
  rw [← mul_right_cancel₀ h3 h4]
  exact hprod

end GlobalTheory.OneMapRef.Kappa

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.exists_const_ortho : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (t : ℝ), (∀ τ, (U.X k).c τ = t) → ∀ n : ℕ, Even n → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → Matched c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : D.host.E) (tens (stdL D.host.E n) (U.X k).Λ) v → ∃ C : ℂ, ∀ x : (U.X k).dom, (U.X k).IsOrtho x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (ptC U k x)) (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U k x).s th → ∀ z : Fin n → Fin g → ℂ, ∏ b, th (z b) = C * thA (U.X k) bas idx v x.1 z := by
  intro D H Dw l Xo c σ r U hσ hU hr _ k t ht n hn g bas idx e hs hm v hv
  exact GlobalTheory.OneMapRef.Kappa.exists_const (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr k t ht n hn bas idx e hs hm.1 v hv
end
