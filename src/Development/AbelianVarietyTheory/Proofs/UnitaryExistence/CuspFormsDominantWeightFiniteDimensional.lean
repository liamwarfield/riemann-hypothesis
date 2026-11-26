module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.cuspForms_finiteDimensional_of_isUnf : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.PjFree.Unf Xo c σ r)
    (σ : c.F →+* ℂ), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf (U σ) → _root_.Formalism.L2.PjFree.CuspFD Xo c U := by
  intro hB E _ _ _ H Dw l Xo c r U σ hgood hunf
  unfold _root_.Formalism.L2.PjFree.CuspFD
  intro a n _
  obtain ⟨hind, -⟩ := _root_.GlobalTheory.reading_linearIndependent_and_injective hB E H Dw l Xo c σ r (U σ) hunf a n
  set V := _root_.Formalism.L2.PjFree.cusp Xo c U a n with hV
  set W : Submodule ℂ (_root_.Formalism.L2.PjFree.FDSec (U σ).X) :=
    Submodule.span ℂ ((_root_.Formalism.L2.PjFree.rdU (U σ)) '' (V : Set (_root_.Formalism.L2.Pj.Rul Xo c))) with hWdef
  have hWle : W ≤ _root_.Formalism.L2.PjFree.holSub (U σ).X (_root_.Formalism.L2.PjFree.laU (U σ) a n) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ((_root_.Formalism.L2.PjFree.mem_cusp Xo c U a n f).mp hf).2 σ hgood
  have hoff : ∀ P ∈ W, ∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0 := by
    intro P hP k x hx
    induction hP using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, -, rfl⟩ := hg
      simp [_root_.Formalism.L2.PjFree.rdU, hx]
    | zero => rfl
    | add g h _ _ hg hh =>
      show g k x + h k x = 0
      rw [hg, hh, add_zero]
    | smul z g _ hg =>
      show z • g k x = 0
      rw [hg, smul_zero]
  have : FiniteDimensional ℂ W :=
    _root_.GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub E r (U σ).Comp (U σ).X
      (_root_.Formalism.L2.PjFree.laU (U σ) a n) W hWle hoff
  have hrank : Module.rank c.F V ≤ Module.finrank ℂ W := by
    apply rank_le
    intro s hs
    let e := s.equivFin
    let b : Fin s.card → _root_.Formalism.L2.Pj.Rul Xo c := fun i => ((e.symm i : s) : V).1
    have hbV : ∀ i, b i ∈ _root_.Formalism.L2.Pj.sec Xo c a n := fun i =>
      _root_.Formalism.L2.PjFree.cusp_le_sec Xo c U a n ((e.symm i : s) : V).2
    have hbind : LinearIndependent c.F b :=
      (hs.comp e.symm e.symm.injective).map' V.subtype V.ker_subtype
    have himg := hind s.card b hbV hbind
    let b' : Fin s.card → W := fun i =>
      ⟨_root_.Formalism.L2.PjFree.rdU (U σ) (b i), Submodule.subset_span ⟨b i, ((e.symm i : s) : V).2, rfl⟩⟩
    have hb' : LinearIndependent ℂ b' := LinearIndependent.of_comp W.subtype himg
    simpa using hb'.fintype_card_le_finrank
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensionalStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_dominantWeight_finiteDimensional : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), GoodEmb c σ → IsUnf (U σ) → CuspFD Xo c U := by
  first | exact @GlobalTheory.cuspForms_finiteDimensional_of_isUnf | exact GlobalTheory.cuspForms_finiteDimensional_of_isUnf | (intros; apply GlobalTheory.cuspForms_finiteDimensional_of_isUnf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.SecSeparation

theorem exists_frBor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (t : Ix Dw → Sˣ) : ∃ y' : FrPt Xo c S, FrBor t y y' := by
  classical
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y
    (fun τ => Matrix.diagonal fun i => (t (some ⟨τ, i⟩) : S)) (t none) (fun τ => by
      rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 fun i => Units.isUnit _)
  refine ⟨y', ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨_, ?_, ?_, hy'⟩⟩
  · intro τ i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne
  · intro τ i
    exact Matrix.diagonal_apply_eq _ _

end GlobalTheory.SecSeparation

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

theorem exists_isSplit_of_splitLat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hD : SplitLat D) :
    ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  obtain ⟨Lp, Lm, hs, ho, -, -, hp, hm⟩ := hD
  have two : ∀ m, (D.EF (H.rt • m) m : ℝ) = 2 * D.EF (H.w0 • m) m := fun m => by
    have : D.EF ((2 * H.w0) • m) m = D.EF ((1 + H.rt) • m) m := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply,
      D.alt] at this
    have h : D.EF (H.rt • m) m = 2 * D.EF (H.w0 • m) m := by linarith
    exact_mod_cast h
  obtain ⟨P, hP, k₁, k₂⟩ := GlobalTheory.CM.FamCompare.exists_period D Lp Lm
    (fun z => ⟨1, one_pos, hs ▸ Submodule.mem_top⟩) ho
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hp x hx h
        rw [two] at this
        linarith)
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hm x hx h
        rw [two] at this
        linarith) hty
  exact ⟨P, hP, top_le_iff.1 (hs ▸ sup_le_sup k₁ k₂)⟩

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → SplitLat D → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  first | exact @GlobalTheory.CompRat.exists_isSplit_of_splitLat | exact GlobalTheory.CompRat.exists_isSplit_of_splitLat | (intros; apply GlobalTheory.CompRat.exists_isSplit_of_splitLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem SupNormCusp.eq_zero_of_pnorm_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (h : X.pnorm la P x = 0) : P x = 0 := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx' τ).2 i
    rw [h0] at this
    simp at this
  unfold Data.pnorm at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact norm_eq_zero.1 h1
  · exfalso
    refine (ne_of_gt ?_) h1
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))

theorem supNorm_definite_on_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → Formalism.L2.PjFree.SupDef Xo c U := by
  intro E _ _ _ H Dw l Xo c r U hU a n hd σ hσ f hf h0
  refine (GlobalTheory.T.rdU_linearIndependent_and_injective GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c σ r (U σ) (hU σ hσ) a n).2 f
    (Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf) fun k x hx => ?_
  have hfin := Formalism.L2.PjFree.supE_cusp_ne_top hσ hf
  have hE : Formalism.L2.PjFree.supE (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) f) = 0 := by
    unfold Formalism.L2.PjFree.supN at h0
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 hfin
  have hle : ENNReal.ofReal (((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k)
      (Formalism.L2.PjFree.rdU (U σ) f k) x) ≤ 0 := by
    rw [← hE]
    exact le_iSup (fun p : Formalism.L2.PjFree.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm
      (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
  have hp : ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x = 0 := by
    refine le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hle zero_le)) ?_
    unfold Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)
  exact SupNormCusp.eq_zero_of_pnorm_eq_zero _ _ _ x hx hp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supNorm_definite_on_cuspForms_goodEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → Formalism.L2.PjFree.SupDef Xo c U := by
  first | exact @GlobalTheory.supNorm_definite_on_cusp | exact GlobalTheory.supNorm_definite_on_cusp | (intros; apply GlobalTheory.supNorm_definite_on_cusp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponent
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

namespace DefiniteData

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_std (x y : Fin r → E) :
    herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

theorem emb_herm_self (φ : E →+* ℂ) (x : Fin r → E) :
    φ (herm (1 : Matrix (Fin r) (Fin r) E) x x) = ((∑ a, ‖φ (x a)‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [herm_std, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

def stdLat (E : Type) [Field E] [NumberField E] (r : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin r))

omit [IsCMField E] in
theorem mem_stdLat (x : Fin r → E) : x ∈ stdLat E r ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · rintro ⟨y, rfl⟩ a
    exact (y a).isIntegral_coe
  · intro h
    exact ⟨fun a => ⟨x a, h a⟩, rfl⟩

omit [IsCMField E] in
theorem single_mem_stdLat (b : Fin r) : (Pi.single b 1 : Fin r → E) ∈ stdLat E r := by
  rw [mem_stdLat]
  intro a
  by_cases h : a = b
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem stab_finite :
    {γ : GL (Fin r) E | IsUStab (1 : Matrix (Fin r) (Fin r) E) (stdLat E r) γ}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ) 1
  have hpi := Set.Finite.pi' (fun _ : Fin r => Set.Finite.pi' (fun _ : Fin r => hfin))
  refine Set.Finite.of_finite_image (hpi.subset ?_) ?_
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
  · rintro _ ⟨γ, ⟨hh, hl⟩, rfl⟩ a b
    have hv : ∀ i, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single b 1) i =
        (γ : Matrix (Fin r) (Fin r) E) i b := by
      intro i; simp
    refine ⟨?_, fun φ => ?_⟩
    · have := (mem_stdLat _).1 ((hl _).1 (single_mem_stdLat b)) a
      rwa [hv] at this
    · have h1 := congrArg φ (hh (Pi.single b 1) (Pi.single b 1))
      rw [emb_herm_self, emb_herm_self] at h1
      have h2 := Complex.ofReal_injective h1
      have h3 : ∑ i, ‖φ ((Pi.single b 1 : Fin r → E) i)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro i _ hi; simp [hi]
        · simp
      rw [h3] at h2
      simp only [hv] at h2
      have h4 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2 ≤ 1 := by
        rw [← h2]
        exact Finset.single_le_sum (f := fun i => ‖φ ((γ : Matrix (Fin r) (Fin r) E) i b)‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ a)
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
  · intro γ _ δ _ h
    apply Units.ext
    ext a b
    exact congrFun (congrFun h a) b

theorem eq_zero_of_herm_self {x : Fin r → E}
    (h : herm (1 : Matrix (Fin r) (Fin r) E) x x = 0) : x = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := emb_herm_self φ x
  rw [h, map_zero] at h1
  have h2 : ∑ a, ‖φ (x a)‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  funext a
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h2 a (Finset.mem_univ a)
  have h4 : φ (x a) = 0 := by simpa using h3
  exact (map_eq_zero_iff φ φ.injective).1 h4

theorem nonempty_data (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) :
    Nonempty (FD.Data E r) := by
  classical
  let X : FD.Data E 1 := inhab
  exact ⟨
  { Ψ := X.Ψ
    cmType := X.cmType
    Gm := 1
    Gm_herm := by
      intro a b
      by_cases h : a = b
      · subst h; simp [cc_one]
      · simp [h, Ne.symm h, cc_zero]
    Gm_det := by simp
    p0 := r
    p0_le := le_rfl
    signature := by
      intro τ
      refine ⟨1, by simp, ?_⟩
      ext a b
      by_cases h : a = b
      · subst h
        simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite]
      · simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite, h, Ne.symm h]
    Λ := stdLat E r
    Λ_fg := by
      unfold stdLat
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    Λ_span := by
      rw [eq_top_iff]
      intro x _
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat b))
    den := 1
    den_ne := one_ne_zero
    Λ_int := by
      intro x hx y hy
      rw [herm_std, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
      exact IsIntegral.sum _ fun a _ =>
        ((mem_stdLat x).1 hx a).mul (isIntegral_cc ((mem_stdLat y).1 hy a))
    Γ := ⊥
    Γ_stab := by
      intro γ hγ
      rw [Subgroup.mem_bot] at hγ
      subst hγ
      simp [IsUStab]
    Γ_index := ⟨(stab_finite (E := E) (r := r)).toFinset, fun γ hγ =>
      ⟨γ, (Set.Finite.mem_toFinset _).2 hγ, by simp⟩⟩
    Γ_free := fun γ hγ _ _ _ _ _ => Subgroup.mem_bot.mp hγ
    χ := fun _ _ => 1
    χ_mul := by intros; simp
    χ_add := by intros; simp
    χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
    ξ0 := X.ξ0
    ξ0_im := X.ξ0_im
    ξ0_ne := X.ξ0_ne
    κ0 := X.κ0
    κ0_xi := X.κ0_xi
    κ0_sign := X.κ0_sign
    m := 1
    m_pos := one_pos
    transv := by
      intro ξ _ hiso s _ _
      have hξ := eq_zero_of_herm_self hiso
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [transvMat, hξ, Matrix.one_apply] }⟩

end DefiniteData

theorem exists_unf_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  intro E _ _ _ H Dw l Xo c h σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data E (Dw.p + Dw.q)
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist E H Dw l Xo c h σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponentStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisationData_nonempty_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  first | exact @GlobalTheory.exists_unf_nonempty_comp | exact GlobalTheory.exists_unf_nonempty_comp | (intros; apply GlobalTheory.exists_unf_nonempty_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVector
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVector
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_hom_of_pureType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ _ C i P hP ε a ha
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t
  obtain ⟨φ, -, hφ⟩ := exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq
    C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.CompRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVectorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  first | exact @GlobalTheory.CompRat.exists_hom_of_pureType | exact GlobalTheory.CompRat.exists_hom_of_pureType | (intros; apply GlobalTheory.CompRat.exists_hom_of_pureType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTriple
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

open Moduli.LevelAction in
theorem levMove_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (_c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  intro E _ _ _ H Dw l Xo _ ρ ρ' ν ν' gM gM' gA gA' hpq hM hA _ _ ⟨hs, e, eA⟩ ⟨hs', e', eA'⟩ ⟨g, hgM, hgA, hν⟩
  have hred : IsReduced Xo.X := by
    have := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  obtain ⟨o, m, a₁, b₁⟩ := exists_obj_twist_by_similitude SimAlg.sim_group E H Dw l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨n, hn⟩ := Moduli.LevelAction.exists_comp_sabMap m ν (Category.id_comp ρ)
  obtain ⟨n', hn'⟩ := Moduli.LevelAction.exists_comp_sabMap m ν' (Category.id_comp ρ')
  have c₁ : ∀ a, (o.eta a).left ≫ n.φ = ρ ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn, ← Category.assoc, a₁, Moduli.LevelAction.eta_congr Xo.univ (hgM a), e]
  have c₂ : ∀ a, (o.etaA a).left ≫ n.φ = ρ ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn, ← Category.assoc, b₁, Moduli.LevelAction.etaA_congr Xo.univ (hgA a), eA]
  have d₁ : ∀ a, (o.eta a).left ≫ n'.φ = ρ' ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn', ← Category.assoc, a₁, Moduli.LevelAction.eta_congr Xo.univ (hgM a), Moduli.LevelAction.eta_congr Xo.univ (hM a), e']
  have d₂ : ∀ a, (o.etaA a).left ≫ n'.φ = ρ' ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn', ← Category.assoc, b₁, Moduli.LevelAction.etaA_congr Xo.univ (hgA a), Moduli.LevelAction.etaA_congr Xo.univ (hA a), eA']
  obtain rfl : ρ = ρ' := (Xo.rep _ Xo.s hred o).unique ⟨hs, ⟨⟨n, c₁, c₂⟩⟩⟩ ⟨hs', ⟨⟨n', d₁, d₂⟩⟩⟩
  refine ⟨rfl, ?_⟩
  have h := obj_rigid_closed firstFiveLaws.1 E H Dw l _ _ _ _ _ _ _ _ Xo.univ o ρ (Or.inl hred) n n'
    fun a => ⟨_, c₁ a, d₁ a⟩
  have : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [hn, hn'] at h
  exact (cancel_epi m.φ).1 h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTripleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_moduli_unique_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  first | exact @GlobalTheory.levMove_unique | exact GlobalTheory.levMove_unique | (intros; apply GlobalTheory.levMove_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBiject
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBiject
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompBij

open GlobalTheory.CompInj

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ik_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  intro E _ _ _ H D l Xo c σ r U h1 hσ hU g e F ik φ hEF hP
  obtain ⟨hr, hX, hcov, hfib, -⟩ := hU
  refine ⟨fun k k' hk => ?_, fun i => ?_⟩
  · obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
    obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
    obtain ⟨P, -, hper, hpt, hder⟩ := hP k ⟨x, hx⟩
    obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
    have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2⟩ : _ ∧ _ ∧ _)
    have hEF' := hEF k'
    generalize φ k' = ψ at hP₀ hP' hEF'
    clear hP hEF φ
    generalize ik k' = n at *
    subst hk
    obtain ⟨x', hx', hPx⟩ := exists_frame (c := c) (σ := σ) hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1
      (F.sig _).2 ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
    obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
    obtain rfl : P = P' := by
      ext a j
      exact (hPx a j).trans (hP' a j).symm
    have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
    obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
    exact (congrArg Sigma.fst h).symm
  · have hty : IsTypeFn H (F.Di i).p (F.Di i).q (fun j => relab c σ (e j).1) := by
      rw [(F.sig i).1, (F.sig i).2]
      exact (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e
    obtain ⟨-, P, hPi⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di i) g _ hty
    let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨y, hy⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (F.u i P) ((F.over_σ i P hPi).trans rfl)
    obtain ⟨k, x, t, hb⟩ := hcov y
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k x
    exact ⟨k, F.disj _ _ Pm P hPm hPi (hx.symm.trans (hb.1.symm.trans hy))⟩

end GlobalTheory.CompBij
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBijectStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  first | exact @GlobalTheory.CompBij.ik_bijective | exact GlobalTheory.CompBij.ik_bijective | (intros; apply GlobalTheory.CompBij.ik_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPoints
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace ComplexTransfer

theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem countable_of_finiteType (K A : Type) [CommRing K] [Countable K] [CommRing A] [Algebra K A]
    [h : Algebra.FiniteType K A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  haveI : Countable (MvPolynomial (Fin n) K) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem exists_common_field {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) {A B k : Type} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Countable A] [Countable B] [Field k] [Algebra K k]
    (φ : A →ₐ[K] k) (ψ : B →ₐ[K] k) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (ι : L →ₐ[K] k) (j : L →ₐ[K] CAt σ) (φL : A →ₐ[K] L)
      (ψL : B →ₐ[K] L), ι.comp φL = φ ∧ ι.comp ψL = ψ ∧ Function.Injective j := by
  let s : Set k := Set.range φ ∪ Set.range ψ
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_range _)
  let L := IntermediateField.adjoin K s
  have hL : Countable L := by
    have := hs.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le K s).trans ?_
    simp
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨j⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K L
  refine ⟨L, inferInstance, inferInstance, L.val, j,
    φ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inl ⟨a, rfl⟩),
    ψ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inr ⟨a, rfl⟩), ?_, ?_, ?_⟩
  · ext a; rfl
  · ext a; rfl
  · exact j.toRingHom.injective

theorem evalAt_of_mapR {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (z : pts S)
    (hz : mapR φ y z) : evalAt pts mapR f z = φ (f p y) := by
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  unfold evalAt
  rw [dite_eq_left hT]
  exact (hW f hf S p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec).symm

end ComplexTransfer

theorem exists_complex_framed_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c k _ _ y y'
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  obtain ⟨p, φ, y₀, hy⟩ := hA k y
  obtain ⟨q, ψ, y₁, hy'⟩ := hA k y'
  haveI := c.fin
  haveI : Countable c.F := ComplexTransfer.countable_of_finiteType ℚ c.F
  haveI : Countable p.R := ComplexTransfer.countable_of_finiteType c.F p.R
  haveI : Countable q.R := ComplexTransfer.countable_of_finiteType c.F q.R
  obtain ⟨L, _, _, ι, j, φL, ψL, hφ, hψ, hj⟩ :=
    ComplexTransfer.exists_common_field c.F.val.toRingHom φ ψ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp φL) y₀
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp ψL) y₁
  have hι : Function.Injective ι := ι.toRingHom.injective
  have ev : ∀ f ∈ sec Xo c 0 0, evR Xo c f y = ι (φL (f p y₀)) ∧ evR Xo c f y' = ι (ψL (f q y₁)) ∧
      evR Xo c f z = j (φL (f p y₀)) ∧ evR Xo c f z' = j (ψL (f q y₁)) := by
    intro f hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hφ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p φ y₀ y hy
    · rw [← AlgHom.comp_apply, hψ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q ψ y₁ y' hy'
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p _ y₀ z hz
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q _ y₁ z' hz'
  refine ⟨z, z', ?_, ?_, ?_⟩
  · intro ρ h
    have e1 : y.x = spMap ι.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy.1, ← hφ]; rfl
    have e2 : y'.x = spMap ι.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy'.1, ← hψ]; rfl
    have e3 : z.x = spMap j.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz.1]; rfl
    have e4 : z'.x = spMap j.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz'.1]; rfl
    haveI := ComplexTransfer.epi_spMap_field ι.toRingHom
    rw [e1, e2, Category.assoc, cancel_epi] at h
    rw [e3, e4, h]
    simp only [Category.assoc]
  · intro f hf h
    obtain ⟨h1, -, h3, -⟩ := ev f hf
    rw [h1, map_eq_zero_iff ι hι] at h
    rw [h3, h, map_zero]
  · intro f hf a h
    obtain ⟨h1, h2, h3, h4⟩ := ev f hf
    rw [h3, h4, ← j.commutes, ← map_mul] at h
    rw [h1, h2, hj h, map_mul, ι.commutes]

end GlobalTheory.Frames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpaces
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem exists_indicator_function {X : Scheme.{0}} (U : Set X) (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), e * e = e ∧ ∀ x : Sp ℂ ⟶ X,
      (x (IsLocalRing.closedPoint ℂ) ∈ U → valAt' x ⊤ e = 1) ∧
      (x (IsLocalRing.closedPoint ℂ) ∉ U → valAt' x ⊤ e = 0) := by
  let V : Bool → X.Opens := fun b => match b with
    | true => ⟨U, hU.2⟩
    | false => ⟨Uᶜ, hU.1.isOpen_compl⟩
  let sf : ∀ b, Γ(X, V b) := fun b => match b with
    | true => 1
    | false => 0
  have hcov : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : x ∈ U
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have hsub : ∀ W : X.Opens, W = ⊥ → Subsingleton Γ(X, W) := by
    rintro _ rfl
    infer_instance
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro a b
    cases a <;> cases b
    · simp [sf]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · simp [sf]
  obtain ⟨e, he'⟩ : ∃ e : Γ(X, ⊤), ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b :=
    (X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcov sf hcomp).exists
  have hpt : ∀ (x : Sp ℂ ⟶ X) (b : Bool), x (IsLocalRing.closedPoint ℂ) ∈ V b → ⊤ ≤ x ⁻¹ᵁ V b := by
    intro x b h z _
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) z (IsLocalRing.closedPoint ℂ)]
  refine ⟨e, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine X.sheaf.eq_of_locally_eq' V ⊤ (fun b => homOfLE le_top) hcov _ _ fun b => ?_
    show X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op (e * e) = X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e
    rw [map_mul, he']
    cases b <;> simp [sf]
  · refine (TB.ValAt.valAt'_res x le_top (hpt x true h) e).symm.trans ((congrArg (valAt' x _) (he' true)).trans ?_)
    exact TB.ValAt.valAt'_one x _ (hpt x true h)
  · refine (TB.ValAt.valAt'_res x le_top (hpt x false h) e).symm.trans ((congrArg (valAt' x _) (he' false)).trans ?_)
    exact (valHom x _ (hpt x false h)).map_zero

theorem eq_val_of_A_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (σ : KA l →+* ℂ) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = (KA l).val.toRingHom := by
  have hz : zeta l.A = 1 := by
    rw [hA, zeta, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]
  ext ⟨x, hx⟩
  show σ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hσ
    · have : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      exact (congrArg σ this).trans ((map_one σ).trans hz.symm)
  | algebraMap q => exact (map_ratCast σ q)
  | add x y hx hy h1 h2 => exact (map_add σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | mul x y hx hy h1 h2 => exact (map_mul σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | inv x hx h1 => exact (map_inv₀ σ ⟨x, hx⟩).trans (by rw [h1])

theorem exists_coeff_idempotent_functions :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ hσ _ hA c
  obtain rfl := eq_val_of_A_eq_one σ₀ hσ hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpacesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffField_idempotent_cutting_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompRat.exists_coeff_idempotent_functions | exact GlobalTheory.CompRat.exists_coeff_idempotent_functions | (intros; apply GlobalTheory.CompRat.exists_coeff_idempotent_functions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LeastOrderBoundOfOrdTieTriv
noncomputable section

namespace GlobalTheory.TrivOrderTieCompare

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isClopen_comp (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have hZ : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  obtain ⟨z, hz⟩ := hZ.nonempty
  have h1 : (Z : Set (Xo.XF c)) ⊆ connectedComponent z :=
    hZ.isConnected.isPreconnected.subset_connectedComponent hz
  have h2 : IsIrreducible (connectedComponent z) :=
    ⟨⟨z, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth (strK (Xo := Xo) (c := c)) z⟩
  rw [Set.Subset.antisymm h1 (Z.2.2 h2 h1)]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace z⟩

variable [Fintype (Comp Xo c)]

section Concrete

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end Concrete

end GlobalTheory.TrivOrderTieCompare
end
end
