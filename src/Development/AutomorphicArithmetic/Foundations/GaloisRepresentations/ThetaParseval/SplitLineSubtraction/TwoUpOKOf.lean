module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.AllCoreOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)

namespace UpperTheory.Gal.TP.Sub

structure Dict {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) {t : ℕ}
    (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ)
    (κ : HChar E) (m : (E →+* ℂ) → ℤ) (ψ : Fin t → HChar E) (p : Fin t → (E →+* ℂ) → ℤ) : Prop where
  alg : ∀ i, IsAlgPos (ψ i) (p i)
  m₁ : ∀ w, 2 * m (emb w).1 = mW w - mX w + t
  m₂ : ∀ w, 2 * m (ComplexEmbedding.conjugate (emb w).1) = mX w - mW w + t
  p₁ : ∀ i w, 2 * p i (emb w).1 = mX w + 2 * (i : ℕ) - (n + 2 * t - 2)
  p₂ : ∀ i w, 2 * p i (ComplexEmbedding.conjugate (emb w).1) = -mX w + 2 * (i : ℕ) - (n + 2 * t - 2)
  loc : ∀ w : HeightOneSpectrum (𝓞 E), κ.UnrAt w → (∀ i, (ψ i).UnrAt w) → GlobalTheory.LFun.UnrAt χX w ∧ GlobalTheory.LFun.UnrAt χW w ∧
    ((κ.val w : ℂˣ) : ℂ) = (GlobalTheory.LFun.val χW w : ℂ) * (GlobalTheory.LFun.val χX w : ℂ)⁻¹ *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2)) ∧
    ∀ i, (((ψ i).val w : ℂˣ) : ℂ) = (GlobalTheory.LFun.val χX w : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (i : ℕ))

def ChrPairs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n t : ℕ), Even n → Odd t → ∀ (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (b : ℤ) (w₀ : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ) (χX χW : Fin 2 → Chr (maximalRealSubfield E) E)
      (mX mW : Fin 2 → InfinitePlace (maximalRealSubfield E) → ℤ) (ψ : Fin 2 → Fin t → HChar E) (p : Fin 2 → Fin t → (E →+* ℂ) → ℤ),
      IsAlgPos κ m ∧ (∀ j, GlobalTheory.LFun.IsHecke (maximalRealSubfield E) E (χX j) ∧ GlobalTheory.LFun.IsHecke (maximalRealSubfield E) E (χW j) ∧
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range (χX j) n ∧
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range (χW j) (n + t) ∧
        HasExp emb (χX j) (mX j) ∧ HasExp emb (χW j) (mW j) ∧ (∀ w, mW j w ≤ b) ∧
        Dict n emb (χX j) (χW j) (mX j) (mW j) κ m (ψ j) (p j)) ∧
      (∀ i i', ψ 0 i ≠ ψ 1 i') ∧ κ.UnrAt w₀ ∧ ∀ i, (ψ 0 i).UnrAt w₀

def EmbSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w),
    (∀ τ : E →+* ℂ, ∃ w, τ = (emb w).1 ∨ τ = ComplexEmbedding.conjugate (emb w).1) ∧
    (∀ w w', (emb w).1 = (emb w').1 → w = w') ∧ ∀ w w', (emb w).1 ≠ ComplexEmbedding.conjugate (emb w').1

def WtId : Prop :=
  ∀ (n t : ℕ) (lam : DomWeight n) (lam' : DomWeight (n + t)) (mX mW : ℤ), UpperTheory.TP.IsLiftWt lam mX mW lam' →
    (∀ (m : ℤ) (p : Fin t → ℤ), 2 * m = mW - mX + t → (∀ i, 2 * p i = mX + 2 * (i : ℕ) - (n + 2 * t - 2)) →
      wtJumps lam' = (wtJumps lam).map (· + m) + Finset.univ.val.map fun i => -p i) ∧
    ∀ (m : ℤ) (p : Fin t → ℤ), 2 * m = mX - mW + t → (∀ i, 2 * p i = -mX + 2 * (i : ℕ) - (n + 2 * t - 2)) →
      wtJumps lam'.dual = (wtJumps lam.dual).map (· + m) + Finset.univ.val.map fun i => -p i

def SatId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n t : ℕ) (B : Multiset ℂˣ) (x y : ℂˣ) (k : ℂ) (c : Fin t → ℂ),
    k = (y : ℂ) * (x : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2)) →
    (∀ i, c i = (x : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (i : ℕ))) →
    algSat (n + t) (Ideal.absNorm w.asIdeal) (B.map (· * (x * y⁻¹)) + GlobalTheory.LFun.seg w x t) =
      (algSat n (Ideal.absNorm w.asIdeal) B).map (· * k⁻¹) + Finset.univ.val.map c

def UpOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n t : ℕ), 1 ≤ n → n < t → ∀ (Bs : Base (maximalRealSubfield E) E) (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ)
    (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight n,
    (∀ τ, GlobalTheory.UnitaryBC.HasWeightAt U τ (lam τ)) → ∀ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E (n + t) → ℂ),
    UpperTheory.TP.IsLift Bs χX χW mX mW (fun w => lam (Bs.emb w).1) U U' →
    ∀ (κ : HChar E) (m : (E →+* ℂ) → ℤ) (ψ : Fin t → HChar E) (p : Fin t → (E →+* ℂ) → ℤ),
      Dict n Bs.emb χX χW mX mW κ m ψ p → ∃ lam', IsUp U lam κ m U' lam' ψ p

def BaseNG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) → InertOK E →
    ∃ (Bs : Base (maximalRealSubfield E) E) (δ : E) (𝔞 : Submodule (𝓞 E) E), UpperTheory.TP.GoodNG (UpperTheory.TP.cj E) Bs ∧
      (∀ n, (Skew.stdSpc (maximalRealSubfield E) E n).IsHerm (UpperTheory.TP.cj E) Bs n 0) ∧
      ∀ d, (Skew.skewSpc (maximalRealSubfield E) δ 𝔞 d).IsSkew (UpperTheory.TP.cj E) Bs d 0

end UpperTheory.Gal.TP.Sub

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClSub
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem cont_sum {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (hr : Continuous r) (hs : Continuous s) : Continuous (sumRep r s) := by
  have h : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) :=
    GlobalTheory.BCGal.cont_sumRep r s (Units.continuous_val.comp hr) (Units.continuous_val.comp hs)
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have e : (fun g => (((sumRep r s g)⁻¹ : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k)) =
      (fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k)) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact e ▸ h.comp continuous_inv

private theorem unrPol_add (S : Multiset ℂ) (c : ℂ) (m : ℤ) :
    unrPol (S + {c}) m = unrPol S m * unrPol {c} m := by
  simp only [unrPol, Multiset.map_add (f := _), Multiset.prod_add]

private theorem unrPol_single_ne (c : ℂ) (m : ℤ) : unrPol {c} m ≠ 0 := by
  simp only [unrPol, Multiset.map_singleton, Multiset.prod_singleton]
  exact X_sub_C_ne_zero _

theorem UpperTheory.Gal.TP.Sub.clSub_holds :
    FrobSub → SumDR → PstOfDR → WDFacts → ClSub := by
  intro hF hD hP hW E Ω _ _ _ _ _ l _ ι a s μ hs hμ w S c J m hc hsum
  refine ⟨fun hl => (hF E Ω l ι a w S c μ (hc.1 hl)).1 s (hsum.1 hl), ?_⟩
  intro P AI hT A h O _ _ _ Bw hj
  obtain ⟨-, d1, j1, p1⟩ := hc.2 P AI hT A h O Bw hj
  obtain ⟨c2, d2, j2, p2⟩ := hsum.2 P AI hT A h O Bw hj
  have ci : Continuous (Dec (F := E) A).subtype := continuous_subtype_val
  have cμ : Continuous (rk1 μ) := (contLeft_holds (G E Ω) (Qbar l) a 1).2.2.2 μ hμ
  have cS : Continuous ((sumRep s (rk1 μ)).comp (Dec (F := E) A).subtype) :=
    (cont_sum s (rk1 μ) hs cμ).comp ci
  have e : (sumRep s (rk1 μ)).comp (Dec (F := E) A).subtype =
      sumRep (s.comp (Dec (F := E) A).subtype) ((rk1 μ).comp (Dec (F := E) A).subtype) := by
    ext; rfl
  rw [e] at c2 d2 j2 p2 cS
  obtain ⟨dS, -, jS⟩ := hD l P AI hT E Ω A O Bw a 1 _ _ d2
  have pS : IsPstAt P Bw (s.comp (Dec (F := E) A).subtype) :=
    hP l P AI hT E Ω A O Bw a _ (hs.comp ci) dS
  have pM : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    hP l P AI hT E Ω A O Bw 1 _ (cμ.comp ci) d1
  have pT := hP l P AI hT E Ω A O Bw (a + 1) _ cS d2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a 1 _ _ pS pM pT
  have hu := (GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ pT).2 c2
  rw [hw] at hu p2
  refine ⟨(GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ pS).1 ((hW E Ω A w h _ _).1 hu), dS,
    fun τ LL' τ' hi => jS τ (J τ) {m τ} (j2 τ LL' τ' hi) (j1 τ LL' τ' hi), fun g => ?_⟩
  have q := p2 g
  rw [(hW E Ω A w h _ _).2.1 g, p1 g, unrPol_add] at q
  exact mul_right_cancel₀ (unrPol_single_ne c (deg g)) q
end
