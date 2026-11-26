module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.DivisionOneGeometricRepresentation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdjoinForm
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.AdjoinForm.adjoin_form :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → ∀ y ∈ ℚ⟮x⟯, ∃ (s : ℚ) (t : ℚ), y = (↑s : E) + (↑t : E) * x := by
  intro E _ _ d _ x hx y hy
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h : y ∈ (ℚ⟮x⟯).toSubalgebra := hy
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at h
  clear hy
  induction h using Algebra.adjoin_induction with
  | mem a ha =>
    rw [Set.mem_singleton_iff] at ha
    exact ⟨0, 1, by simp [ha]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s + s', t + t', by push_cast; ring⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s * s' - t * t' * d, s * t' + t * s', by push_cast; linear_combination (t * t' : E) * hx⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateElement
theorem UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d hd x hx
  let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  have h : (φ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : (φ x).re * (φ x).im = 0 := by linarith
  have hr : (φ x).re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg (φ x).re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cpl (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) := conjSrc (GlobalTheory.SplitPts.conjE E) w


omit [NumberField E] [IsCMField E] in
def SameK (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → (y ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def CplMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (y y' : 𝓞 E),
    (y' : E) = IsCMField.complexConj E (y : E) → (y ∈ (cpl w).asIdeal ↔ y' ∈ w.asIdeal)

def SameOr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l d : ℕ), l.Prime → 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ w w' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ((l : ℕ) : 𝓞 E) ∈ w'.asIdeal → SameK x w w' ∨ SameK x (cpl w) w'

def LocIso : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
    locU (E := E) a (cpl w) = locU a w ∧
    ∃ β : GL (Fin a) ((cpl w).adicCompletion E) ≃ₜ* GL (Fin a) (w.adicCompletion E),
      (∀ x : UA E a, β (cLoc (cpl w) x) = cLoc w x) ∧ (∀ g, g ∈ GlobalTheory.LFun.KGL (cpl w) (n := a) → β g ∈ GlobalTheory.LFun.KGL w (n := a)) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V),
        GlobalTheory.SmGL.IsCuspidal σ → GlobalTheory.SmGL.IsCuspidal (σ.comp β.toMulEquiv.toMonoidHom)

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
      (∃ B, UpperTheory.Gal.TP.Sub.SatU U w B) → ∃ B, UpperTheory.Gal.TP.Sub.SatU U (cpl w) B

def TyConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ) (U : Submodule ℂ (UA E a → ℂ))
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → GlobalTheory.CongW.TyEll E l a w U → GlobalTheory.CongW.TyEll E l a (cpl w) U

def LacConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (U : Submodule ℂ (UA E a → ℂ)) (v : HeightOneSpectrum (𝓞 E)), LacWtAt ι v U → LacWtAt ι (cpl v) U

def GapLac : Prop := ∀ (a : ℕ) (J : Finset ℤ), J.card = a → GapJ a J.val → Lacunary J

end UpperTheory.Gal.Int.Div

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.satConj_of :
    LocIso → SatConj := by
  intro hL E _ _ _ a U hU w hw ⟨B, σ, ⟨hirr, f, hf0, hfU, hfe⟩, hB⟩
  obtain ⟨hloc, β, hβ, hK, -⟩ := hL E a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hpe : ∀ g, cLoc w ((e.symm g : locU a w) : UA E a) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 hirr).2 _ (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 := hfe (e.symm g) v
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hpe] at h1
    rw [h1, hv, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have h0 : f x ≠ 0 := (map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx.1
  obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hw
  have hs : IsSplitAt (cpl w) := ⟨w, hne.symm, hund.symm⟩
  have hfix : ∀ y ∈ locU a (cpl w), cLoc (cpl w) y ∈ GlobalTheory.LFun.KGL (cpl w) (n := a) → RU E a y (f x) = f x := by
    intro y hy hk
    have hy' : y ∈ locU a w := hloc ▸ hy
    have hk' : cLoc w y ∈ GlobalTheory.LFun.KGL w (n := a) := by
      rw [← hβ y]
      exact hK _ hk
    have h2 := GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ hk'
    have h1 := hfe ⟨y, hy'⟩ x
    change f (σ.ρ (cLoc w y) x) = RU E a y (f x) at h1
    rw [h2] at h1
    exact h1.symm
  obtain ⟨σ', S, hc, hS, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU (cpl w) hs (f x) (hfU x) h0 hfix
  exact ⟨S, σ', hc, hS⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.SeedFinOddOf
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Geo (GeoOne)

namespace UpperTheory.Gal.Int.Div

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem apart_cpl {w u : HeightOneSpectrum (𝓞 E)} (hu : IsSplitAt u) : Apart w (cpl u) ↔ Apart w u := by
  unfold Apart
  rw [(GlobalTheory.SplitPts.over_split hu).2.1]

private theorem apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) : Apart u w := Ne.symm h

private theorem mem_cpl (hC : CplMem) {l : ℕ} {u : HeightOneSpectrum (𝓞 E)} (h : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    ((l : ℕ) : 𝓞 E) ∈ (cpl u).asIdeal := (hC E u l l (by simp)).2 h

private theorem move (hC : CplMem) (hS : SameOr) {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E} (hx : x ^ 2 = -(d : E))
    {u w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt u) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) (hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {p : HeightOneSpectrum (𝓞 E) → Prop} (h1 : p u) (h2 : p (cpl u)) :
    ∃ u', ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal ∧ SameK x u' w ∧ p u' ∧ ∀ y, Apart y u' ↔ Apart y u := by
  rcases hS E l d hl hd x hx u w hu hw with h | h
  · exact ⟨u, hu, h, h1, fun _ => Iff.rfl⟩
  · exact ⟨cpl u, mem_cpl hC hu, h, h2, fun _ => apart_cpl hs⟩

end

theorem seedFinOdd_of (hD : DivAll) (hC : CplMem) (hS : SameOr) (hSat : SatConj) (hTy : TyConj) (hLac : LacConj) (hGap : GapLac)
    (hGen : DGenMul) (hG : GeoOne) : SeedFinOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha hodd d hd T hT w₀ v' hw₀ hs₀ hv' hs' hap U₀ S Y
  refine ⟨∅, by simp, fun U hA hty hwt hsph hsv _ => ?_⟩
  obtain ⟨hd0, x, hx⟩ := hd.1
  have hlac : LacWtAt ι v' U := by
    obtain ⟨-, τ, hτ, h⟩ := hwt
    obtain ⟨lam, hlam⟩ := GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hA.1
    exact ⟨τ, hτ, lam τ, hlam τ, hGap a _ (card_wtJumps _) (h _ (hlam τ) _ (wtJumps_val _))⟩
  have geo : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ u₀ u', SameK x w u' ∧ (∀ y, Apart y u₀ ↔ Apart y w₀) ∧
      (∀ y, Apart y u' ↔ Apart y v') ∧ _ := fun w hw => by
    obtain ⟨u₀, a1, a2, a3, a4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs₀ hw₀ hw
      (p := fun u => GlobalTheory.CongW.TyEll E l a u U) hty (hTy E l a U w₀ hs₀ hty)
    obtain ⟨u', b1, b2, b3, b4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs' hv' hw
      (p := fun u => (∃ B, SatU U u B) ∧ LacWtAt ι u U) ⟨hsv, hlac⟩ ⟨hSat E a U hA.1 v' hs' hsv, hLac E l ι a ha U v' hlac⟩
    exact ⟨u₀, u', fun y hy => (b2 y hy).symm, a4, b4, hG E Ω l ι a hodd d hd x hx T hT u₀ u' a1 b1
      ((a4 u').2 (apart_symm ((b4 w₀).2 (apart_symm hap)))) (fun y hy => (a2 y hy).trans (b2 y hy).symm) S U hA a3
      (fun y h1 h2 h3 => hsph y h1 ((a4 y).1 h2) h3) b3.1 b3.2⟩
  obtain ⟨_, _, -, -, -, g1, g2, -⟩ := geo v' hv'
  obtain ⟨r, ⟨r1, r2, V, X, v1, v2, v3⟩, hr⟩ := hD E Ω l ι a ha d hd.1 U hA.1 g1
  have hgm : ∀ w B, SatU U w B → GlobalTheory.CongW.GenOf DGen a (normV w) B → GenericMul B := fun w B hB hg =>
    hGen a _ B ha hB.choose_spec.2.card hg
  have hsp : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw => by
    by_contra h
    exact (hd.2.2.2 w h).1 hw
  refine ⟨r, r1, r2, ⟨V, X, v1, v2, fun w h1 h2 h3 _ => v3 w h1 h2 h3⟩, fun w _ h1 h2 _ B hB hg => ?_,
    fun w _ h1 h2 h3 h4 => ?_, fun w _ h1 h2 h3 _ B hB hg => ?_⟩
  · obtain ⟨dd, ρ, k1, k2⟩ := g2 w h1 h2 ⟨B, hB⟩
    exact (hr dd ρ k1 w).1 h1.1 h2 B hB (hgm w B hB hg) (k2 B hB)
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨⟨dd, ρ, k1, k2, k3⟩, -⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) (hsph w (hsp w h1) h2 h4)
    exact (hr dd ρ k1 w).2.1 k2 k3
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨-, dd, ρ, k1, k2⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) ⟨B, hB⟩
    exact ((hr dd ρ k1 w).2.2 (hsp w h1) B hB (hgm w B hB hg) (k2 B hB)).2.phiAt

end UpperTheory.Gal.Int.Div

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PGapLac
noncomputable section

open GlobalTheory.RoadWGeo GlobalTheory.CongL

namespace UpperTheory.Gal.Int.Div

private theorem getD_eq (J : Finset ℤ) (a : ℕ) (hcard : J.card = a) (i : ℕ) (hi : i < a) :
    (J.val.sort (· ≤ ·)).getD i 0 = J.orderEmbOfFin hcard ⟨i, hi⟩ := by
  rw [Finset.orderEmbOfFin_apply]
  have hl : i < (J.val.sort (· ≤ ·)).length := by
    simpa [hcard] using hi
  rw [List.getD_eq_getElem _ _ hl]
  rfl

private theorem sum_shift (A : Finset ℤ) (c : ℤ) : ∑ x ∈ A, (x - c) = A.sum id - (A.card : ℤ) * c := by
  simp [Finset.sum_sub_distrib]

private theorem avg_lt {J A B : Finset ℤ} {c : ℤ} (hmin : ∀ x ∈ J, c ≤ x)
    (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * (x - c) < y - c) (hA : A ⊆ J) (hB : B ⊆ J)
    (hBn : B.Nonempty) {m : ℤ} (hm : m ∈ A) (hlt : ∀ b ∈ B, b < m) :
    (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
  have h1 : m - c ≤ ∑ x ∈ A, (x - c) :=
    Finset.single_le_sum (f := fun x => x - c) (fun x hx => sub_nonneg.2 (hmin x (hA hx))) hm
  have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
  have h2 : ∑ b ∈ B, (A.card : ℤ) * (b - c) < ∑ _b ∈ B, (m - c) := by
    refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
    have h3 := hg b (hB hb) m (hA hm) (hlt b hb)
    have h4 := mul_le_mul_of_nonneg_right hc (sub_nonneg.2 (hmin b (hB hb)))
    linarith
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, sum_shift] at h2
  rw [sum_shift] at h1
  have h5 : (B.card : ℤ) * (m - c) ≤ B.card * (A.sum id - (A.card : ℤ) * c) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

private theorem lacunary_of_shift {J : Finset ℤ} {c : ℤ} (hmin : ∀ x ∈ J, c ≤ x)
    (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * (x - c) < y - c) : Lacunary J := by
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (avg_lt hmin hg hA hB hBn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (avg_lt hmin hg hB hA hAn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem gapLac_of : GapLac := by
  intro a J hcard hgap
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hJ : J = ∅ := Finset.card_eq_zero.1 hcard
    subst hJ
    exact lacunary_of_shift (c := 0) (by simp) (by simp)
  have hmem : ∀ x ∈ J, ∃ i, J.orderEmbOfFin hcard i = x := by
    intro x hx
    have : x ∈ Set.range (J.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    exact this
  refine lacunary_of_shift (c := J.orderEmbOfFin hcard ⟨0, ha⟩) (fun x hx => ?_) fun x hx y hy hxy => ?_
  · obtain ⟨i, rfl⟩ := hmem x hx
    exact (J.orderEmbOfFin hcard).monotone (Fin.mk_le_of_le_val (Nat.zero_le _))
  · obtain ⟨i, rfl⟩ := hmem x hx
    obtain ⟨j, rfl⟩ := hmem y hy
    have hij : i < j := (J.orderEmbOfFin hcard).lt_iff_lt.1 hxy
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by have : (i : ℕ) < j := hij; omega⟩
    have hk1 : k + 1 < a := hk ▸ j.2
    have hk0 : k < a := by omega
    have hjk : j = ⟨k + 1, hk1⟩ := Fin.ext hk
    have hg := hgap k hk1
    rw [getD_eq J a hcard (k + 1) hk1, getD_eq J a hcard 0 ha, getD_eq J a hcard k hk0] at hg
    have hik : J.orderEmbOfFin hcard i ≤ J.orderEmbOfFin hcard ⟨k, hk0⟩ :=
      (J.orderEmbOfFin hcard).monotone (by
        have : (i : ℕ) < j := hij
        show (i : ℕ) ≤ k
        omega)
    rw [hcard, hjk]
    have h6 := mul_le_mul_of_nonneg_left (sub_le_sub_right hik (J.orderEmbOfFin hcard ⟨0, ha⟩))
      (Int.natCast_nonneg a)
    linarith

end UpperTheory.Gal.Int.Div

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLacConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private theorem lacunary_image_sub {J : Finset ℤ} (c : ℤ) (h : Lacunary J) :
    Lacunary (J.image fun x => c - x) := by
  classical
  intro A B hA hB hd hAn hBn e
  have inj : Function.Injective (fun x : ℤ => c - x) := fun x y e => by simpa using e
  have back : ∀ S : Finset ℤ, S ⊆ J.image (fun x => c - x) → S.image (fun x => c - x) ⊆ J := by
    intro S hS x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 (hS hy)
    simpa using hz
  have hsum : ∀ S : Finset ℤ, (S.image fun x => c - x).sum id = (S.card : ℤ) * c - S.sum id := by
    intro S
    rw [Finset.sum_image (fun x _ y _ e => inj e)]
    simp only [id]
    rw [Finset.sum_sub_distrib (fun _ => c) (fun x => x), Finset.sum_const, nsmul_eq_mul]
  refine h _ _ (back A hA) (back B hB) ((Finset.disjoint_image inj).2 hd) (hAn.image _) (hBn.image _) ?_
  rw [Finset.card_image_of_injective _ inj, Finset.card_image_of_injective _ inj, hsum, hsum]
  linear_combination -e

private theorem wtJumps_dual {a : ℕ} (lam : DomWeight a) :
    wtJumps lam.dual = (wtJumps lam).image fun x => ((a : ℤ) - 1) - x := by
  have key : ∀ k : Fin a, ((k : ℕ) : ℤ) - lam.dual.w k = ((a : ℤ) - 1) - (((k.rev : ℕ) : ℤ) - lam.w k.rev) := by
    intro k
    have h1 : lam.dual.w k = -lam.w k.rev := rfl
    have h2 := Fin.val_rev k
    have h3 := k.2
    rw [h1]
    omega
  ext x
  simp only [wtJumps, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k.rev, rfl⟩, (key k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨k.rev, ?_⟩
    rw [key, Fin.rev_rev]

theorem UpperTheory.Gal.Int.Div.lacConj_of :
    CplMem → LacConj := by
  intro hC E _ _ _ l _ ι a ha U v ⟨τ, hτ, lam, hw, hl⟩
  refine ⟨ComplexEmbedding.conjugate τ, ?_, lam.dual, GlobalTheory.DefiniteBC.hasWeightAt_conjugate ha hw, ?_⟩
  · intro x hx
    have hy : ((IsCMField.ringOfIntegersComplexConj E x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := rfl
    have h := hτ _ ((hC E v x _ hy).1 hx)
    rw [hy, IsCMField.complexEmbedding_complexConj] at h
    exact h
  · rw [wtJumps_dual]
    exact lacunary_image_sub _ hl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PTyConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private def smIrrComap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (β : G ≃ₜ* H) (σ : SmIrr G) : SmIrr H :=
  ⟨σ.V, σ.ρ.comp β.symm.toMulEquiv.toMonoidHom, fun v => (σ.smooth v).preimage β.symm.continuous,
    (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := σ.ρ.comp β.symm.toMulEquiv.toMonoidHom) (σ := σ.ρ)
      (fun h => β.symm h) β.symm.surjective (LinearEquiv.refl ℂ _) (fun _ _ => rfl)).2 σ.irred⟩

theorem UpperTheory.Gal.Int.Div.tyConj_of :
    LocIso → TyConj := by
  intro hL E _ _ _ l a U w hw hT
  obtain ⟨hU, β, hβ, -, hc⟩ := hL E a w hw
  obtain ⟨m, J, θ, χ, hJo, hJc, hJt, hθ, hχ, hcus, φ, hφU, hφ0, hφ⟩ := hT
  let J' : Subgroup (GL (Fin a) ((cpl w).adicCompletion E)) := J.comap β.toMulEquiv.toMonoidHom
  let r : J' →* J :=
    { toFun := fun g => ⟨β g.1, g.2⟩
      map_one' := Subtype.ext (map_one β)
      map_mul' := fun x y => Subtype.ext (map_mul β _ _) }
  refine ⟨m, J', θ.comp r, χ, ?_, ?_, ?_, ?_, hχ, ?_, φ, hφU, hφ0, ?_⟩
  · exact hJo.preimage β.continuous
  · exact β.toHomeomorph.isCompact_preimage.2 hJc
  · intro x hx k hk hxk
    have h := hJt (β x) hx k hk (by rw [← map_pow, hxk, map_one])
    exact β.injective (h.trans (map_one β).symm)
  · intro t
    obtain ⟨g, rfl⟩ := hθ t
    have hg : β.symm g.1 ∈ J' := by
      show β (β.symm g.1) ∈ J
      rw [β.apply_symm_apply]
      exact g.2
    refine ⟨⟨β.symm g.1, hg⟩, ?_⟩
    show θ (r _) = θ g
    exact congrArg θ (Subtype.ext (β.apply_symm_apply _))
  · intro σ' v hv he
    have hcu : GlobalTheory.SmGL.IsCuspidal (smIrrComap β σ').ρ := by
      refine hcus (smIrrComap β σ') v hv fun g => ?_
      have hg : β.symm g.1 ∈ J' := by
        show β (β.symm g.1) ∈ J
        rw [β.apply_symm_apply]
        exact g.2
      have h := he ⟨β.symm g.1, hg⟩
      have e : r ⟨β.symm g.1, hg⟩ = g := Subtype.ext (β.apply_symm_apply _)
      have e' : (θ.comp r) ⟨β.symm g.1, hg⟩ = θ g := congrArg θ e
      rw [e'] at h
      exact h
    have h3 := hc σ'.V (σ'.ρ.comp β.symm.toMulEquiv.toMonoidHom) hcu
    have e : (σ'.ρ.comp β.symm.toMulEquiv.toMonoidHom).comp β.toMulEquiv.toMonoidHom = σ'.ρ :=
      MonoidHom.ext fun g => congrArg σ'.ρ (β.symm_apply_apply g)
    rwa [e] at h3
  · intro x hx h
    have hx' : x ∈ locU a w := hU ▸ hx
    have hm : cLoc w x ∈ J := by
      rw [← hβ]
      exact h
    rw [hφ x hx' hm]
    have e : r ⟨cLoc (cpl w) x, h⟩ = ⟨cLoc w x, hm⟩ := Subtype.ext (hβ x)
    show _ = ((χ (θ (r ⟨cLoc (cpl w) x, h⟩)) : ℂˣ) : ℂ) • φ
    rw [e]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSameOr
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private theorem conj_alt_bis {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis hd hx

private theorem adjoin_form {E : Type} [Field E] [NumberField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (y : E) (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ s t : ℚ, y = (s : E) + (t : E) * x :=
  _root_.UpperTheory.Reformulated.B.AdjoinForm.adjoin_form hd hx y hy

private theorem two_cases {R : Type} [CommRing R] (T : R → Prop) (hT : ∀ a b, T a → T b → T (a + b))
    (I J : Ideal R) (h : ∀ y, T y → y ∈ I ∨ y ∈ J) : (∀ y, T y → y ∈ I) ∨ (∀ y, T y → y ∈ J) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨a, ha, haI⟩, b, hb, hbJ⟩ := hcon
  have haJ : a ∈ J := (h a ha).resolve_left haI
  have hbI : b ∈ I := (h b hb).resolve_right hbJ
  rcases h (a + b) (hT a b ha hb) with h1 | h1
  · exact haI ((Submodule.add_mem_iff_left I hbI).mp h1)
  · exact hbJ ((Submodule.add_mem_iff_right J haJ).mp h1)

private theorem core {R : Type} [CommRing R] (c : R ≃+* R) (hcc : ∀ y, c (c y) = y) (K : R → Prop)
    (hKa : ∀ a b, K a → K b → K (a + b)) (hKc : ∀ y, K y → K (c y)) (W W' : Ideal R)
    (h1 : ∀ y, K y → y ∈ W → y ∈ W' ∨ c y ∈ W') (h2 : ∀ y, K y → y ∈ W' → y ∈ W ∨ c y ∈ W) :
    (∀ y, K y → (y ∈ W ↔ y ∈ W')) ∨ (∀ y, K y → (c y ∈ W ↔ y ∈ W')) := by
  have A := two_cases (fun y => K y ∧ y ∈ W') (fun a b ha hb => ⟨hKa a b ha.1 hb.1, W'.add_mem ha.2 hb.2⟩)
    W (W.comap (c : R →+* R)) (fun y hy => by simpa [Ideal.mem_comap] using h2 y hy.1 hy.2)
  have B := two_cases (fun y => K y ∧ y ∈ W) (fun a b ha hb => ⟨hKa a b ha.1 hb.1, W.add_mem ha.2 hb.2⟩)
    W' (W'.comap (c : R →+* R)) (fun y hy => by simpa [Ideal.mem_comap] using h1 y hy.1 hy.2)
  simp only [Ideal.mem_comap, RingHom.coe_coe] at A B
  rcases A with A | A <;> rcases B with B | B
  · exact Or.inl fun y hy => ⟨fun h => B y ⟨hy, h⟩, fun h => A y ⟨hy, h⟩⟩
  · refine Or.inl fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := A (c y) ⟨hKc y hy, B y ⟨hy, h⟩⟩
    have h4 := B (c y) ⟨hKc y hy, h3⟩
    rwa [hcc] at h4
  · refine Or.inr fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := B (c y) ⟨hKc y hy, h⟩
    have h4 := A (c y) ⟨hKc y hy, h3⟩
    rw [hcc] at h4
    exact B y ⟨hy, h4⟩
  · refine Or.inr fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := B (c y) ⟨hKc y hy, h⟩
    rwa [hcc] at h3

private theorem int_mem {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) {u u' : Ideal R} (hu : u ≠ ⊤)
    (hlu : (l : R) ∈ u) (hlu' : (l : R) ∈ u') {n : ℤ} (hn : (n : R) ∈ u) : (n : R) ∈ u' := by
  by_cases hd : (l : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hd
    push_cast
    exact u'.mul_mem_right _ hlu'
  · have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) n := (Prime.coprime_iff_not_dvd hp).mpr hd
    exfalso
    apply hu
    rw [Ideal.eq_top_iff_one]
    have : ((a * l + b * n : ℤ) : R) = 1 := by rw [hab]; simp
    rw [← this]
    push_cast
    exact u.add_mem (u.mul_mem_left _ hlu) (u.mul_mem_left _ hn)

private theorem norm_int {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (y y' : 𝓞 E) (hy : (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (hy' : (y' : E) = IsCMField.complexConj E (y : E)) : ∃ n : ℤ, y * y' = (n : 𝓞 E) := by
  obtain ⟨s, t, hst⟩ := adjoin_form hd hx _ hy
  have hc := conj_alt_bis hd hx
  have hq : ((y * y' : 𝓞 E) : E) = algebraMap ℚ E (s ^ 2 + d * t ^ 2) := by
    have h1 : (y' : E) = (s : E) - t * x := by
      rw [hy', hst, map_add (f := _), map_mul, hc]
      simp [sub_eq_add_neg]
    change (y : E) * (y' : E) = _
    rw [h1, hst, eq_ratCast]
    push_cast
    linear_combination (-(t : E) ^ 2) * hx
  have hI : IsIntegral ℤ (algebraMap ℚ E (s ^ 2 + d * t ^ 2)) := hq ▸ RingOfIntegers.isIntegral_coe _
  have hI' : IsIntegral ℤ (s ^ 2 + d * t ^ 2 : ℚ) := (isIntegral_algebraMap_iff ).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  refine ⟨n, RingOfIntegers.ext ?_⟩
  rw [hq, ← hn]
  simp

private theorem two_places {E : Type} [Field E] [NumberField E] [IsCMField E] {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (u u' : HeightOneSpectrum (𝓞 E)) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hu' : ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal) (y y' : 𝓞 E) (hy : (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (hy' : (y' : E) = IsCMField.complexConj E (y : E)) (hm : y ∈ u.asIdeal) : y ∈ u'.asIdeal ∨ y' ∈ u'.asIdeal := by
  obtain ⟨n, hn⟩ := norm_int hd hx y y' hy hy'
  have h1 : (n : 𝓞 E) ∈ u.asIdeal := hn ▸ u.asIdeal.mul_mem_right _ hm
  have h2 := int_mem hl u.isPrime.ne_top hu hu' h1
  rw [← hn] at h2
  exact u'.isPrime.mem_or_mem h2

theorem UpperTheory.Gal.Int.Div.sameOr_of :
    CplMem → SameOr := by
  intro hC E _ _ _ l d hl hd x hx w w' hw hw'
  let c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
  have hcE : ∀ y : 𝓞 E, ((c y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := fun y => rfl
  have hcc : ∀ y, c (c y) = y := fun y => RingOfIntegers.ext (by
    rw [hcE, hcE, IsCMField.complexConj_apply_apply])
  have hKc : ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → ((c y : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {x} := by
    intro y hy
    obtain ⟨s, t, hst⟩ := adjoin_form hd hx _ hy
    have hxK : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
    have h1 : ((c y : 𝓞 E) : E) = (s : E) + ((-t : ℚ) : E) * x := by
      rw [hcE, hst, map_add (f := _), map_mul, conj_alt_bis hd hx]
      simp
    rw [h1]
    exact add_mem (SubfieldClass.ratCast_mem _ s) (mul_mem (SubfieldClass.ratCast_mem _ _) hxK)
  have key := core c hcc (fun y : 𝓞 E => (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (fun a b ha hb => by simpa using add_mem ha hb) hKc w.asIdeal w'.asIdeal
    (fun y hy hm => two_places hl hd hx w w' hw hw' y (c y) hy (hcE y) hm)
    (fun y hy hm => two_places hl hd hx w' w hw' hw y (c y) hy (hcE y) hm)
  rcases key with h | h
  · exact Or.inl fun y hy => h y hy
  · exact Or.inr fun y hy => (hC E w y (c y) (hcE y)).trans (h y hy)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCplMem
open NumberField IsDedekindDomain

namespace UpperTheory.Gal.Int.Div

theorem cplMem_of : CplMem := by
  intro E _ _ _ w y y' hy
  exact (GlobalTheory.Mem.Chr.conjPl_iff_mem (GlobalTheory.SplitPts.conjE E) (cpl w) w).1
    (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w) y y' hy

end UpperTheory.Gal.Int.Div
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocIso
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

open GlobalTheory.SplitPts in
private noncomputable def cEq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cpl w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (conjE E) w) ⟨(conjLoc (conjE E) w).injective, fun y => ⟨psi w y, conjLoc_psi w y⟩⟩

open GlobalTheory.SplitPts in
private theorem conjInvT_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (g : GL (Fin a) ((cpl w).adicCompletion E)) :
    GlobalTheory.LFun.ConjPlace.invT (cEq w) a g = invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

private theorem invT_invT {R : Type} [CommRing R] {a : ℕ} (h : GL (Fin a) R) : invT a R (invT a R h) = h := by
  apply Units.ext
  change ((invT a R h)⁻¹ : GL (Fin a) R).val.transpose = h.val
  rw [← map_inv]
  change (((h⁻¹)⁻¹ : GL (Fin a) R).val.transpose).transpose = h.val
  rw [inv_inv, Matrix.transpose_transpose]

open GlobalTheory.SplitPts in
private theorem conjInvT_symm_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (h : GL (Fin a) (w.adicCompletion E)) :
    (GlobalTheory.LFun.ConjPlace.invT (cEq w) a).symm h = invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := by
  rw [MulEquiv.symm_apply_eq, conjInvT_eq, invT_map,
    show Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (Matrix.GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _), invT_invT]

open GlobalTheory.SplitPts in
theorem UpperTheory.Gal.Int.Div.locIso_of :
    LocIso := by
  intro E _ _ _ a w hw
  refine ⟨?_, ?_⟩
  · unfold locU
    rw [(over_split hw).2.1]
  let e := GlobalTheory.LFun.ConjPlace.invT (cEq w) a
  have hc1 : Continuous e := by
    have e1 : (e : GL (Fin a) ((cpl w).adicCompletion E) → GL (Fin a) (w.adicCompletion E)) =
        fun g => invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) := funext (conjInvT_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec (conjE E) w).1))
  have hc2 : Continuous e.symm := by
    have e1 : (e.symm : GL (Fin a) (w.adicCompletion E) → GL (Fin a) ((cpl w).adicCompletion E)) =
        fun h => invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := funext (conjInvT_symm_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))
  refine ⟨{ e with continuous_toFun := hc1, continuous_invFun := hc2 }, fun x => ?_, fun g hg => ?_, ?_⟩
  · change e (cLoc (cpl w) x) = cLoc w x
    have h := comp_eq x w
    rw [conjInvT_eq w]
    set m := Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (cLoc (cpl w) x) with hm
    have h' : m.val.transpose * (cLoc w x).val = 1 := h
    apply Units.ext
    change ((m⁻¹ : GL (Fin a) _).val).transpose = (cLoc w x).val
    calc ((m⁻¹ : GL (Fin a) _).val).transpose
        = ((m⁻¹ : GL (Fin a) _).val).transpose * (m.val.transpose * (cLoc w x).val) := by rw [h', Matrix.mul_one]
      _ = (m.val * (m⁻¹ : GL (Fin a) _).val).transpose * (cLoc w x).val := by
          rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (cLoc w x).val := by
          rw [Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  · exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (cEq w)
      (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff (cEq w) (conjLoc_spec (conjE E) w).2.2) g).1 hg
  · intro V _ _ σ hσ
    have h1 := GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap (cEq w).symm
      (conjLoc_spec (conjE E) w).1 (σ.comp (GlobalTheory.TypeTame.invTranspose a))
      (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose _ a V σ hσ)
    convert h1 using 1
    refine MonoidHom.ext fun g => ?_
    change σ (e g) = σ (GlobalTheory.TypeTame.invTranspose a (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g))
    rw [conjInvT_eq w]
    rfl
end

namespace UpperTheory.Gal.Int.Div

theorem seedFinOdd_of_geoOne (h : UpperTheory.Gal.Int.Geo.GeoOne) : GlobalTheory.CongL.SeedFinOdd :=
  seedFinOdd_of divAll_holds cplMem_of (sameOr_of cplMem_of) (satConj_of locIso_of) (tyConj_of locIso_of) (lacConj_of cplMem_of)
    gapLac_of dGenMul_of h

end UpperTheory.Gal.Int.Div
