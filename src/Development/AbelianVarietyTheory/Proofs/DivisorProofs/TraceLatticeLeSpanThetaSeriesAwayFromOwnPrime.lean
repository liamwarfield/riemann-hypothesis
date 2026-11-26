module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesTraceTermAtEvaluationVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

open Classical

namespace GlobalTheory.EvalLowType

theorem zero_of_span {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : (∀ j, L j) →ₘₗ[ℂ] X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := _root_.GlobalTheory.TraceRatPf.zero_of_span' (ι := ι) (L := L) (X := X) F v₀ P hspan hstep h0

theorem adForm_lowT_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hHW i x τ k hk v u hu
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have e2 : ((R.MW i (sg0 D A)).fr τ)⁻¹ * (R.MW i (sg0 D A)).fr τ = 1 := Matrix.nonsing_inv_mul _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.EvalLowType

theorem GlobalTheory.EvalLowType.lowType_of_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hcore i _ _ _ _ _ _ v _ _ _ _ _ _ _ _ ℓ _ _ U χ ξR ω φ hker Λ h _ _ N x₀ P x f y _ _ _ _ _ _ _ _ y₀ c _ φ' hvec u hu
  have hext : IsExtVec (R.MW i (sg0 D A)) (v₀ i (sg0 D A)) := (fw.hv₀ i (sg0 D A)).1
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  let w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hext ρ).2.1⟩
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g => Datum.thetaKO ω h g (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ' (R.ioP i t ((O i).c0' y)))
      map_add' := fun a b => by funext g; simp [Datum.thetaKO, map_add (f := _)]
      map_smul' := fun a b => by funext g; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹))
  let Rt : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (D.what₂.embLL c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (adForm R i (cuspTo hT.p fw i (f u))).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = D.what₂.embLL c • act (singleSeries R i ω φ' h ((O i).c0' y) w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g a - s • Formalism.L2.Theta.rTr (Wc D i) g b = Formalism.L2.Theta.rTr (Wc D i) g (a - s • b) :=
    fun _ _ _ _ => rfl
  have key := GlobalTheory.EvalLowType.zero_of_span (Lf - Rt) w₀
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ i (sg0 D A) ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw]
      have e1 := GlobalTheory.EvalLowType.adForm_lowT_equiv R hcore.models.HW i (cuspTo hT.p fw i (f u)) ρ k hk w z hu2
      have e2 := GlobalTheory.T.singleThetaSeries_K_equivariant_lowest_type R F hcore i _ χ ξR _ ω φ hker _ _ φ' hvec h ((O i).c0' y) ((u : G)⁻¹) ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - D.what₂.embLL c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by
      rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt]
      exact hu w₀ fun ρ => rfl)
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVectorStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestTypeEquality_of_evaluationVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  first | exact @GlobalTheory.EvalLowType.lowType_of_eval | exact GlobalTheory.EvalLowType.lowType_of_eval | (intros; apply GlobalTheory.EvalLowType.lowType_of_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.OneMapExact.splitOff_of_dvd {D : D7} {V : HSp D} {b b' : ℕ} (hd : b ∣ b') {g : GA D V} (H : SplitOffBad V b' g) :
    SplitOffBad V b g := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hP hb => h3 PP hP ?_, h4⟩
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hb

theorem GlobalTheory.OneMapExact.trace_of_terms {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (S : GA D (Wc D i) → ℂ) (c : D.what₂.LL) (X : U → Fin (R.nW i) → D.what₂.LL)
    (w : ∀ τ, (R.MW i (sg0 D A)).sm τ)
    (H : ∀ u : U, adForm R i (X u) w =
      D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) S) :
    adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • X u) w = D.what₂.embLL c • levelTrace R i U ψ S := by
  classical
  have h0 : adForm R i 0 = 0 := by
    have := adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at this
    exact this
  have hadd : ∀ (s : Finset U) (Y : U → Fin (R.nW i) → D.what₂.LL),
      adForm R i (∑ u ∈ s, Y u) = ∑ u ∈ s, adForm R i (Y u) := by
    intro s Y
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adForm_add, ih]
  rw [finsum_eq_sum_of_fintype, hadd]
  simp only [adForm_smul]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  ext1 g
  simp only [MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.smul_apply,
    H, smul_eq_mul]
  set Fn : G → ℂ := fun d => (if hg : d ∈ U then D.what₂.embLL ((ψ ⟨d, hg⟩)⁻¹ : D.what₂.LLˣ) else 0) *
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG d) S g with hFn
  have e1 : ∑ d : G, Fn d = ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g := by
    calc ∑ d : G, Fn d = ∑ d ∈ Finset.univ.filter (· ∈ U), Fn d :=
          (Finset.sum_filter_of_ne fun d _ h => by
            by_contra hd
            exact h (by simp only [hFn, dif_neg hd, zero_mul])).symm
      _ = ∑ u : U, Fn u := Finset.sum_subtype _ (by simp) Fn
      _ = _ := Finset.sum_congr rfl fun u _ => by simp only [hFn, dif_pos u.2]
  have e2 : ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g =
      ∑ u : U, D.what₂.embLL ((ψ u⁻¹)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u⁻¹ : U) : G)) S g :=
    (Equiv.sum_comp (Equiv.inv U) (fun u : U => D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g)).symm
  rw [e2] at e1
  calc _ = D.what₂.embLL c * ∑ d : G, Fn d := by
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [map_inv, inv_inv, Subgroup.coe_inv]
        ring
    _ = _ := by
        congr 1


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.OneMapExact.one_term : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  have hterm := GlobalTheory.T.shortSeries_trace_term_at_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := hterm
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w u =>
    GlobalTheory.T.lowestTypeEquality_of_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U χ ξR ω φ h17 Λ h (GlobalTheory.OneMapExact.splitOff_of_dvd (dvd_mul_right _ _) h18) h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27 y₀ c hr φ' hφ' u (fun w₀ hw₀ => H φ' hφ' w₀ hw₀ u) w⟩


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.OneMapExact.trace_short_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • levelTrace R i U ψ (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU ψ χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := GlobalTheory.OneMapExact.one_term D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w => GlobalTheory.OneMapExact.trace_of_terms R i U ψ _ c _ _ (H φ' hφ' w)⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeriesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_shortSeries_eq_mul_adelicSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • levelTrace R i U ψ (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  first | exact @GlobalTheory.OneMapExact.trace_short_eq | exact GlobalTheory.OneMapExact.trace_short_eq | (intros; apply GlobalTheory.OneMapExact.trace_short_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorEqTranslateKernelDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorEqTranslateKernelDatum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.FreeBlockMove

theorem vecFree_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ' = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i ξ χ ξR Q ω φ hK p hp hξ hV y₀ hy₀
  obtain ⟨φ₁, hφ₁, k₁, hk₁, c₁, m, e₁, i₁, i₁', c₁0, L₁⟩ := GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK p hp hξ hV
  obtain ⟨φ', hφ', k₂, hk₂, c₂, e₂, i₂, i₂', c₂0, L₂⟩ := GlobalTheory.T.typePlaces_datum_move_to_fullRank D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK y₀ hy₀ φ₁ hφ₁
  refine ⟨φ', hφ', k₂ * k₁, mul_mem hk₂ hk₁, c₂ * c₁, m, ?_, ?_, ?_, mul_ne_zero c₂0 c₁0, ?_⟩
  · have hm : ((k₂ * k₁, (1 : GA D (Wc D i))) : GA D (Vc D i) × GA D (Wc D i)) = (k₂, 1) * (k₁, 1) := by
      simp
    rw [e₂, e₁, hm, map_mul ω, Module.End.mul_apply, map_smul, smul_smul, map_mul D.what₂.embLL]
  · have := i₂.mul i₁
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · have := i₂'.mul i₁'
    simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  · intro h hh w hw
    have := L₁ (h * k₂) (mul_mem hh hk₂) w (L₂ h hh w hw)
    simpa [mul_assoc] using this

end GlobalTheory.FreeBlockMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorEqTranslateKernelDatumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeLowerBlockVector_eq_translate_kernelDatum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ' = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  first | exact @GlobalTheory.FreeBlockMove.vecFree_translate | exact GlobalTheory.FreeBlockMove.vecFree_translate | (intros; apply GlobalTheory.FreeBlockMove.vecFree_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulCoeffIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.HarmInCoef

open NumberField IsDedekindDomain _root_.Formalism.L2.DIV

private theorem not_isBasisAt_dualFr_tauLat {E K : Type} [Field E] [NumberField E]
    [Field K] [NumberField K] {ι : Type} {n : ℕ} (emb : ι → E →+* K) (τ : ι)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Submodule.span E (L : Set (Fin n → E)) ≠ ⊤)
    (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) :
    ¬ IsBasisAt w (dualFr (tauLat emb τ L)) B := by
  intro hB
  unfold IsBasisAt at hB
  obtain ⟨f, hf, hker⟩ := (Submodule.span E (L : Set (Fin n → E))).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hL)
  let u := (dotProductEquiv E (Fin n)).symm f
  have hu : dotProductEquiv E (Fin n) u = f := (dotProductEquiv E (Fin n)).apply_symm_apply f
  have hu0 : u ≠ 0 := fun h => hf (by rw [← hu, h, map_zero])
  let v : Fin n → K := fun i => emb τ (u i)
  have hv0 : v ≠ 0 := fun h => hu0 (funext fun i => (emb τ).injective (by
    simpa [v] using congrFun h i))
  have hvker : tauLat emb τ L ≤ (dotProductEquiv K (Fin n) v).ker.restrictScalars (𝓞 K) := by
    rw [tauLat, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hfy : f y = 0 := hker (Submodule.subset_span hy)
    change v ⬝ᵥ (fun i => emb τ (y i)) = 0
    rw [← GlobalTheory.TauLat.map_dot (emb τ) u y, show u ⬝ᵥ y = f y from DFunLike.congr_fun hu y,
      hfy, map_zero]
  -- The dual contains every field multiple of the nonzero vector v.
  have hline (r : K) : r • v ∈ dualFr (tauLat emb τ L) := by
    intro y hy
    have hzero : v ⬝ᵥ y = 0 := hvker hy
    rw [smul_dotProduct, hzero, smul_zero]
    exact Submodule.zero_mem _
  let A : Matrix (Fin n) (Fin n) K := ↑(B⁻¹ : GL (Fin n) K)
  have hA : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (B⁻¹).isUnit
  have hAv : A *ᵥ v ≠ 0 := fun h => hv0 (hA (h.trans (Matrix.mulVec_zero A).symm))
  obtain ⟨j, hj0⟩ : ∃ j, (A *ᵥ v) j ≠ 0 := Function.ne_iff.mp hAv
  obtain ⟨q, hqw, hq⟩ := IsConcreteLE.not_le_iff_exists.mp (show ¬ w.asIdeal ≤ ⊥ from
    fun h => w.ne_bot (le_bot_iff.mp h))
  have hq0 : (q : K) ≠ 0 := by
    intro h
    have hqzero : q = 0 := RingOfIntegers.coe_injective (h.trans (map_zero (algebraMap (𝓞 K) K)).symm)
    exact hq (hqzero.symm ▸ Submodule.zero_mem _)
  let r : K := ((q : K) * (A *ᵥ v) j)⁻¹
  have hr : r * (A *ᵥ v) j = (q : K)⁻¹ := by
    dsimp only [r]
    field_simp
  have hrmem : r • v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) :=
    hB ▸ ⟨1, Submonoid.one_mem _, by simpa using hline r⟩
  obtain ⟨s, hs, hcs⟩ := hrmem
  obtain ⟨c, hc⟩ : ∃ c : Fin n → 𝓞 K,
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (c j : K)) = s • (r • v) := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hcs
    refine ⟨c, ?_⟩
    funext i
    simpa [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm] using congrFun hc i
  have hcoefs := congrArg A.mulVec hc
  rw [Matrix.mulVec_mulVec, show A * (B : Matrix (Fin n) (Fin n) K) = 1 from Units.inv_mul B,
    Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul] at hcoefs
  have hcj : (c j : K) = (s : K) * ((q : K)⁻¹) := by
    have hjc : (c j : K) = (s : K) * (r * (A *ᵥ v) j) := congrFun hcoefs j
    rw [hjc, hr]
  have hmul : c j * q = s := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_mul]
    change (c j : K) * (q : K) = (s : K)
    rw [hcj, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
  exact hs (hmul ▸ w.asIdeal.mul_mem_left (c j) hqw)

theorem exists_nat_smul_mem_nabAtr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w₀ : HeightOneSpectrum (𝓞 K)) (ha : a.Coprime (ringChar (𝓞 K ⧸ w₀.asIdeal)))
    {x : VV K lam} (hx : x ∈ nabAtr emb lam L) :
    ∃ s : ℕ, (s : 𝓞 K) ∉ w₀.asIdeal ∧ s • x ∈ nabAtr emb lam L' := by
  classical
  by_cases hspan' : Submodule.span E (L' : Set (Fin n → E)) = ⊤
  case neg =>
    refine ⟨1, fun h1 => w₀.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h1)), ?_⟩
    rw [one_smul]
    change (x : Pol K ι n) ∈ transLat lam (nabStd K lam) (fun τ => dualFr (tauLat emb τ L'))
    apply (GlobalTheory.TransLoc.mem_transLat ..).2
    intro w B hB
    -- Any target basis family also works for the source, since its index type must be empty.
    have hB₀ : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ L)) (B τ) := fun τ =>
      (not_isBasisAt_dualFr_tauLat emb τ hspan' w (B τ) (hB τ)).elim
    exact (GlobalTheory.TransLoc.mem_transLat lam _ (fun τ => dualFr (tauLat emb τ L)) _).1 hx w B hB₀
  have hp : (ringChar (𝓞 K ⧸ w₀.asIdeal)).Prime := by
    haveI := w₀.isMaximal
    haveI : Finite (𝓞 K ⧸ w₀.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w₀.ne_bot
    letI := Ideal.Quotient.field w₀.asIdeal
    exact CharP.prime_ringChar _
  set p := ringChar (𝓞 K ⧸ w₀.asIdeal) with hpdef
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  have ha0 : a ≠ 0 := fun h0 => by
    subst a
    exact GlobalTheory.GO.natCast_notMem_of_coprime ha w₀ hpw (by simp)
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← hspan', Submodule.span_le]
    intro y hy
    apply (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.mpr ha0 : (a : E) ≠ 0)).1
    rw [Nat.cast_smul_eq_nsmul E]
    exact Submodule.subset_span (h' y hy)
  have hfull : Submodule.IsFullLattice E L := { toIsLattice := hL, span_eq_top := hspan }
  have hfull' : Submodule.IsFullLattice E L' := { toIsLattice := hL', span_eq_top := hspan' }
  let J : Ideal (𝓞 K) := (nabAtr emb lam L').comap (LinearMap.toSpanSingleton (𝓞 K) _ x)
  have hmemJ : ∀ r : 𝓞 K, r ∈ J ↔ r • x ∈ nabAtr emb lam L' := fun r => Iff.rfl
  have hJw : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → ¬ J ≤ w.asIdeal := by
    intro w hw hle
    have hcong := (GlobalTheory.GO.localization_nabAtr_delAtr_congr emb lam hfull hfull' h h' w
      (GlobalTheory.GO.natCast_notMem_of_coprime ha w hw)).1
    have hx0 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L) :=
      ⟨1, fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hx⟩
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L') := hcong ▸ hx0
    obtain ⟨u, hu, hux⟩ := hx'
    exact hu (hle ((hmemJ u).2 hux))
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hJp : J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpm : ((p : ℕ) : 𝓞 K) ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hm0 : m ≠ ⊥ := fun h0 => hp0 (by rw [h0] at hpm; exact (Submodule.mem_bot _).1 hpm)
    exact hJw ⟨m, hm.isPrime, hm0⟩ hpm (le_sup_left.trans hle)
  have hJ0 : J ≠ ⊥ := fun h0 => hJw w₀ hpw (h0 ▸ bot_le)
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · intro hmem
    have hdvd : p ∣ Ideal.absNorm J := by
      refine (ringChar.spec (𝓞 K ⧸ w₀.asIdeal) _).1 ?_
      rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (𝓞 K ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hJ0
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ J) p
      (by rwa [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply])
    have h1mem : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := hJp ▸ Submodule.mem_top
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1mem
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have h1 : Ideal.Quotient.mk J (c * (p : 𝓞 K)) = 1 := by
      rw [← map_one (Ideal.Quotient.mk J), ← hjy, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    have hpz : p • z = 0 := hz ▸ addOrderOf_nsmul_eq_zero z
    have hz0 : z = 0 := by
      calc z = Ideal.Quotient.mk J (c * (p : 𝓞 K)) * z := by rw [h1, one_mul]
        _ = Ideal.Quotient.mk J c * (p • z) := by rw [map_mul, nsmul_eq_mul, map_natCast]; ring
        _ = 0 := by rw [hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
  · rw [← Nat.cast_smul_eq_nsmul (𝓞 K)]
    exact (hmemJ _).1 (Ideal.absNorm_mem J)

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open NumberField MvPolynomial _root_.Formalism.L2.Pj

theorem coeff_aeval_scale {σ K : Type} [Field K] (t : K) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (aeval (fun i => C t * X i) P).coeff m = t ^ (m.sum fun _ e => e) * P.coeff m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    have e : aeval (fun i => C t * X i) (monomial d a) = monomial d (t ^ (d.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_pow, Finsupp.prod_mul, Finsupp.prod, Finsupp.sum,
        Finset.prod_pow_eq_pow_sum, C_mul, C_pow, algebraMap_eq]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    rw [e, coeff_monomial, coeff_monomial]
    by_cases h : d = m
    · subst h; simp
    · simp [h]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (c : Coeff l)

theorem symO_std_le {n : ℕ} :
    symO (Dw := Dw) c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n) ≤
      (MvPolynomial.map (algebraMap (integralClosure ℤ c.F) c.F)).range := by
  refine (Subring.closure_le).2 ?_
  rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
  · exact ⟨C o, by simp⟩
  · have hb' : ∀ j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = b j := fun j => by
      have := (Submodule.mem_pi.1 hb) j (Set.mem_univ _)
      exact Submodule.mem_one.1 this
    choose y hy using hb'
    have hint : ∀ j, IsIntegral ℤ (embF c σ (b j)) := fun j => by
      rw [← hy j]
      exact (RingOfIntegers.isIntegral_coe (y j)).map (embF c σ).toIntAlgHom
    refine ⟨∑ j, C (⟨embF c σ (b j), (mem_integralClosure_iff ℤ c.F).2 (hint j)⟩ : integralClosure ℤ c.F) *
      X (⟨σ, i, j⟩ : LtN Dw n), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in simp [letB]

theorem scale_mem_symO {n : ℕ} (Λ : GenLat E n) (k : ℕ) (hk : ∀ b ∈ Λ.La, (k : 𝓞 E) • b ∈ Formalism.L2.Pj.stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) :
    aeval (fun i => C (k : c.F) * X i) P ∈ symO c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n) := by
  let φ : MvPolynomial (LtN Dw n) c.F →+* MvPolynomial (LtN Dw n) c.F :=
    (aeval (fun i => C (k : c.F) * X i) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] _).toRingHom
  have hle : symO c Λ ≤ (symO c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n)).comap φ := by
    refine (Subring.closure_le).2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      simp [φ]
    · refine Subring.subset_closure (Or.inr ⟨σ, i, (k : 𝓞 E) • b, hk b hb, ?_⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [φ, letB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, aeval_C, aeval_X,
        algebraMap_eq, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← C_mul]
      congr 2
      rw [Algebra.smul_def, map_mul, map_natCast, map_natCast, mul_comm]
  exact hle hP

theorem exists_pow_mul_coeff_integral {n : ℕ} (Λ : GenLat E n) (k : ℕ) (hk : ∀ b ∈ Λ.La, (k : 𝓞 E) • b ∈ Formalism.L2.Pj.stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) :
    ∃ D : ℕ, ∀ m, IsIntegral ℤ ((k : c.F) ^ D * P.coeff m) := by
  refine ⟨P.totalDegree, fun m => ?_⟩
  by_cases hm : m ∈ P.support
  · obtain ⟨Q, hQ⟩ := symO_std_le c (scale_mem_symO c Λ k hk hP)
    have h1 : IsIntegral ℤ ((k : c.F) ^ (m.sum fun _ e => e) * P.coeff m) := by
      rw [← coeff_aeval_scale, ← hQ, coeff_map]
      exact (mem_integralClosure_iff ℤ c.F).1 (Q.coeff m).2
    have h2 : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    rw [← Nat.sub_add_cancel h2, pow_add, mul_assoc]
    have hk' : IsIntegral ℤ (k : c.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ c.F (k : ℤ)))
    exact (hk'.pow _).mul h1
  · rw [notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open MvPolynomial _root_.Formalism.L2.Pj

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ HHa r n k cc isX a) (t : k) : t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1, fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm σ i => hP.2.2 m (MvPolynomial.support_smul hm) σ i⟩

theorem map_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k K : Type} [Field k] [CharZero k] [Field K] (f : k →+* K)
    {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n K cc isX a :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map f hP.1, GlobalTheory.RowSpan.rowInv_map f hP.2.1,
    fun m hm => hP.2.2 m (MvPolynomial.support_map_subset f P hm)⟩

theorem coeff_smul_map_mem {σ k K : Type} [Field k] [Field K] (f : k →+* K) (t : k) (P : MvPolynomial σ k) (m : σ →₀ ℕ)
    (h : IsIntegral ℤ (t * P.coeff m)) :
    (f t • MvPolynomial.map f P).coeff m ∈ (integralClosure ℤ K).toSubring := by
  rw [coeff_smul, coeff_map, smul_eq_mul, ← map_mul]
  exact Subalgebra.mem_toSubring.2 ((mem_integralClosure_iff ℤ _).2 (h.map f.toIntAlgHom))

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open NumberField IsDedekindDomain MvPolynomial _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.IndefR.FWT


set_option maxHeartbeats 1000000 in
theorem harm_mem_coefLat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (lam : HeightOneSpectrum (𝓞 D.what₂.LL)), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∀ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)), ∃ (y : VsV D i (O i).c'.F) (s : ℕ), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P ∧ (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ InCoefLat R i h ((s : ℂ) • (O i).c0' y) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT _hk i hpins Λ h _hsplit hLa lam htriv P hP

  obtain ⟨hfield, hP'⟩ := hpins
  obtain ⟨k, hkcop, hk1, hk2⟩ := htriv
  have hlift := hP'.lift
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hlift.c0
  have hfld : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hlift.field
  obtain ⟨_, cga, hIo⟩ := hP'.io
  have hsub := hIo.2.2.2.2.2.2.2

  have hp : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
    haveI := lam.isMaximal
    haveI : Finite (𝓞 D.what₂.LL ⧸ lam.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ lam.ne_bot
    letI := Ideal.Quotient.field lam.asIdeal
    exact CharP.prime_ringChar _
  have hplam : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.1 hkcop)
  have hklam : ((k : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := GlobalTheory.GO.natCast_notMem_of_coprime hkcop lam hplam

  have hkΛ : ∀ b ∈ Λ.La, (k : 𝓞 D.host.E) • b ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := fun b hb =>
    hk1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hb)
  obtain ⟨Dg, hDg⟩ := exists_pow_mul_coeff_integral _ Λ k hkΛ hP.2

  set f := incF T.J.toCore.Q.c (O i).c' (O i).hle with hf
  have hQ : f ((k : T.Q.c.F) ^ Dg) • MvPolynomial.map f P ∈ harmA (Dw := T.J.toCore.Q.Dw ((i : ℕ) + 1)) (O i).c'
      (wtA (κ i)) (Vc D i).rank :=
    ⟨smul_mem_HHa (map_mem_HHa f hP.1) _, fun m => coeff_smul_map_mem f _ P m (hDg m)⟩
  obtain ⟨y0, hy0, hy0io⟩ := hsub hQ

  have hsurj : Function.Surjective (O i).jL := by
    intro z
    have hz : (z : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hfield ▸ z.2
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 hz
    refine ⟨a, Subtype.ext ?_⟩
    exact (RingHom.congr_fun hfld a).trans ha
  let e : D.what₂.LL ≃+* (O i).c'.F := RingEquiv.ofBijective (O i).jL ⟨(O i).jL.injective, hsurj⟩
  have hje : (O i).jL.comp (e.symm : (O i).c'.F →+* D.what₂.LL) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    exact e.apply_symm_apply z
  let F0 : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank := MvPolynomial.map (e.symm : (O i).c'.F →+* D.what₂.LL) (y0 : Pol _ _ _)
  have hF0 : MvPolynomial.map (O i).jL F0 = (y0 : Pol _ _ _) := by
    rw [MvPolynomial.map_map, hje, MvPolynomial.map_id]
  have hx0V : F0 ∈ VV D.what₂.LL (lamV D i) :=
    ((Formalism.L2.DIV.baseChangeSpace_holds D.what₂.LL (O i).c'.F (O i).jL D.what₂.Tau (Vc D i).rank (lamV D i)).1 F0).2
      (hF0 ▸ y0.2)
  let x0 : VsV D i D.what₂.LL := ⟨F0, hx0V⟩

  have hstd : Submodule.IsLattice D.host.E (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    have := GlobalTheory.RepsCompare.isLattice_hLat (Vc D i) 1
    rw [hlift.std.2] at this
    exact this
  have hstdFull : Submodule.IsFullLattice D.host.E (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    refine { toIsLattice := hstd, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro v _
    have hv : v = ∑ j, v j • (Pi.single j 1 : Fin (Vc D i).rank → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine Submodule.mem_pi.2 fun k _ => ?_
    by_cases h : j = k
    · simpa [Pi.single_apply, h] using (Submodule.mem_one.2 ⟨(1 : 𝓞 D.host.E), map_one _⟩ :
        (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E))
    · simpa [Pi.single_apply, h] using (Submodule.zero_mem (1 : Submodule (𝓞 D.host.E) D.host.E))
  have hemb : (fun τ => (O i).jL.comp (labLL D τ)) = fun τ => embF (O i).c' (tauE D τ) :=
    funext fun τ => embV_eq_embF (O i).c' (O i).jL hfld τ
  have hx0nab : x0 ∈ nabAtr (labLL D) (lamV D i) (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    refine ((Formalism.L2.DIV.nablaDeltaDescentAt_holds D.host.E D.what₂.LL (O i).c'.F (O i).jL D.what₂.Tau (Vc D i).rank
      (labLL D) (lamV D i) _ hstdFull x0 y0 hF0.symm).2.2.1).2 ?_
    rw [hemb]
    exact hy0

  have hstarStd : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank,
      (fun b => star (x b)) ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := by
    intro x hx
    refine Submodule.mem_pi.2 fun j _ => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hx) j (Set.mem_univ _))
    have hint : IsIntegral ℤ (star (x j)) := by
      rw [← hy]
      exact (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨star (x j), (mem_integralClosure_iff ℤ _).2 hint⟩, rfl⟩
  have hcmp1 : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank, k • x ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h) := by
    intro x hx
    have h2 : (k : 𝓞 D.host.E) • (fun b => star (x b)) ∈ Λ.La :=
      hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hstarStd x hx))
    have h3 := (hLa _).1 h2
    convert h3 using 1
    funext b
    simp [Algebra.smul_def, star_mul', star_natCast]
  have hcmp2 : ∀ x ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h), k • x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := by
    intro x hx
    have h1 : (fun b => star (x b)) ∈ Λ.La := (hLa _).2 (by simpa using hx)
    have h2 : (k : 𝓞 D.host.E) • (fun b => star (x b)) ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank :=
      hk1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) h1)
    have h3 := hstarStd _ h2
    convert h3 using 1
    funext b
    simp [Algebra.smul_def, star_mul', star_natCast]
  obtain ⟨s, hs, hsx⟩ := exists_nat_smul_mem_nabAtr (labLL D) (lamV D i) hstd
    (GlobalTheory.RepsCompare.isLattice_hLat (Vc D i) (fin (Vc D i) h)) hcmp1 hcmp2 lam hkcop hx0nab

  obtain ⟨v', hv'pol, hv'c⟩ := hC0 (s • x0)
  have hv'eq : v' = s • y0 := by
    apply Subtype.ext
    rw [hv'pol]
    show MvPolynomial.map (O i).jL (s • F0) = s • (y0 : Pol _ _ _)
    rw [map_nsmul, hF0]
  set r : (O i).c'.F := f ((k : T.Q.c.F) ^ Dg) with hrdef
  have hr : r = (k : (O i).c'.F) ^ Dg := by rw [hrdef]; erw [map_pow, map_natCast]
  have hr0 : r ≠ 0 := by rw [hr]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hk0)
  set_option synthInstance.maxHeartbeats 200000 in
  refine ⟨r⁻¹ • y0, s * k ^ Dg, ?_, ?_, ?_⟩
  · rw [map_smul, hy0io]
    exact inv_smul_smul₀ hr0 _
  · push_cast
    intro hm
    rcases lam.isPrime.mem_or_mem hm with h1 | h1
    · exact hs h1
    · exact hklam (lam.isPrime.mem_of_pow_mem _ h1)
  · refine ⟨gramR, c0R, c0L, hFT, s • x0, hsx, ?_⟩
    set_option synthInstance.maxHeartbeats 200000 in
    have hsm : (s * k ^ Dg) • (r⁻¹ • y0) = s • y0 := by
      rw [← Nat.cast_smul_eq_nsmul (O i).c'.F, ← Nat.cast_smul_eq_nsmul (O i).c'.F s, smul_smul, Nat.cast_mul,
        Nat.cast_pow, ← hr, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
    refine Eq.trans ?_ hv'c
    rw [hv'eq, ← hsm, map_nsmul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.HarmInCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLatticeLeSpanThetaSeriesAwayFromOwnPrime
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompareOff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons _root_.Formalism.L2.Pj _root_.Formalism.L2.Indef _root_.Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Formalism.HermitianLatticesTheory (localization₂)

theorem mem_localization_iff {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L : Submodule Rr W) (x : W) : x ∈ localization₂ p L ↔ ∃ s : Rr, s ∉ p ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem localization_le_of_le_localization' {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L M : Submodule Rr W) (h : L ≤ localization₂ p M) : localization₂ p L ≤ localization₂ p M := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, hy⟩ := (mem_localization_iff p M _).1 (h hx)
  refine (mem_localization_iff p M x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hm with h1 | h1
  · exact ht h1
  · exact hs h1

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    (hne : Formalism.EigenvalueLevelCeiling.plc lam ≠ p) : ((p : 𝓞 K)) ∉ lam.asIdeal := by
  intro hm
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have h0 : ((p : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ p := ringChar.dvd h0
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hne h1

theorem splitOffBad_of_mul {D : D7} {V : HSp D} {a b : ℕ} {h : GA D V} (H : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hPP hm => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem singleSeries_transl (R : RealDat D A Ks) (i : Fin D.R.m) {ξ χ ξR Q ω φ} (hK : KerDat R i ξ χ ξR Q ω φ)
    {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω (c • ω (k, 1) φ) h w v = c • singleSeries R i ω φ (h * k) w v := by
  funext g
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  simp only [singleSeries, Datum.thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ k hk 1
    (one_mem _) _ _ _ _ φ _ hth, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem compareOffOwn_run : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  intro lam hlam
  refine localization_le_of_le_localization' _ _ _ (Submodule.span_le.2 ?_)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, s, f', Λ, h, N, x₀, P, x, hs, hsf, hSplit, hLat, hΛlam, hUni, hTriv, hTrivM, hLevN, hAdm, hP, hx⟩ :=
    GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins ℓ U lam f hf
  obtain ⟨y, s', hy, hs', hyLat⟩ := GlobalTheory.HarmInCoef.harm_mem_coefLat D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins Λ h (splitOffBad_of_mul hSplit) hLat lam hΛlam P hP
  obtain ⟨ω, φ, hBase⟩ := GlobalTheory.OnCmp.exists_baseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu
  obtain ⟨χ, ξR, hKer⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu ω φ hBase
  have hEx := GlobalTheory.OneMapExact.trace_short_eq D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu
    hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  obtain ⟨y₀, c, hy₀, hcInt, hSer⟩ :=
    hEx χ ξR ω φ hKer Λ h hSplit hLat N x₀ P x f' y hUni hTriv hTrivM hLevN hAdm hP hx hy
  obtain ⟨φ', hVec, k, hk, c', m, hφ', hpc, -, hc'0, hLatk⟩ := GlobalTheory.T.freeLowerBlockVector_eq_translate_kernelDatum D G Pl0 T0 A T.J.Q.c.F R F hC i _ χ ξR _ ω φ hKer
    (ownAt D v) (fun PP hPP => by classical exact (Finset.mem_filter.1 hPP).2) hξ hVal y₀ hy₀
  obtain ⟨s'', hs'', hs''c⟩ := hcInt lam hΛlam
  obtain ⟨g', hg'⟩ : ∃ g', g' = ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f' u) := ⟨_, rfl⟩
  rw [← hg'] at hSer
  have hp : (ownAt D v).Prime := by
    rcases hFO.own with e | e <;> rw [e]
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hpl : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := natCast_not_mem lam hp hlam
  have hA : ((s : ℕ) : D.what₂.LL) • (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
      algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • g' := by
    classical
    have e1 : ∀ u, ((s : ℕ) : D.what₂.LL) • cuspTo hT.p fw i (f u) =
        algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • cuspTo hT.p fw i (f' u) := by
      intro u
      have e2 : ((s : ℕ) : T.J.Q.c.F) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f u) =
          (show T.J.Q.c.F from (a : T.Q.c.F)) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f' u) :=
        Subtype.ext (hsf u)
      have e3 := congrArg (cutTo fw i) e2
      rw [map_smul, map_smul] at e3
      rw [← algebraMap_smul D.what₂.LL ((s : ℕ) : T.J.Q.c.F), ← algebraMap_smul D.what₂.LL (show T.J.Q.c.F from (a : T.Q.c.F)),
        map_natCast] at e3
      exact e3
    rw [hg', finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_comm, e1 u, smul_comm]
  have hdet : ∀ x : Fin (R.nW i) → D.what₂.LL,
      (∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => w ρ) = 0) → x = 0 := by
    intro x hx
    have h4 : (R.FW i).j (sg0 D A) x = 0 := by
      obtain ⟨u, hu, -⟩ := hIo i
      exact GlobalTheory.TraceIncl.eq_of_low (R := R) (i := i) hC.models.HW ⟨u, hu⟩
        (x := (R.FW i).j (sg0 D A) x) (y := 0) fun w => by rw [map_zero]; exact hx w
    by_contra hne
    exact ((hLU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 h4
  by_cases hc : c = 0
  · have hz : g' = 0 := hdet g' fun w => by rw [hSer φ' hVec w, hc, map_zero, zero_smul]
    refine (mem_localization_iff _ _ _).2 ⟨(s : 𝓞 D.what₂.LL), hs, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.what₂.LL, hA, hz, smul_zero]
    exact zero_mem _
  · have hs'n : s' ≠ 0 := by
      rintro rfl
      exact hs' (by simp)
    have hs'0 : (s' : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hs'n
    have hp0 : ((ownAt D v : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hc0 : c ≠ 0 := hc
    have hce : D.what₂.embLL c ≠ 0 := (map_ne_zero _).2 hc
    have hce' : D.what₂.embLL c' ≠ 0 := (map_ne_zero _).2 hc'0
    obtain ⟨e, he⟩ : ∃ e, e = (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (c * c')⁻¹) • g' := ⟨_, rfl⟩
    have hmem : e ∈ thetaBase R i U ψ 1 v (ownAt D v) := by
      refine Submodule.subset_span ⟨ω, φ, hKer.isKernel, h * k, mul_mem hSplit.1 hk,
        ((ownAt D v : ℂ)) ^ m • ((s' : ℂ) • (O i).c0' y), hLatk h hSplit.1 _ hyLat, fun w => ?_⟩
      rw [he, adForm_smul, MultilinearMap.smul_apply, hSer φ' hVec w, hφ', singleSeries_transl R i hKer hk,
        singleSeries_smul, singleSeries_smul, map_smul, map_smul, map_smul, one_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, map_inv₀, map_pow, map_natCast]
      field_simp
    have hgg : g' = (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹) • e := by
      rw [he, smul_smul]
      conv_lhs => rw [← one_smul D.what₂.LL g']
      congr 1
      field_simp
    have hint : IsIntegral ℤ (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) *
        (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')) :=
      ((RingOfIntegers.isIntegral_coe a).algebraMap.mul hs''c).mul hpc
    have hpr := lam.isPrime
    have ht : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal := by
      simp only [Ideal.IsPrime.mul_mem_iff_mem_or_mem hpr, not_or]
      exact ⟨⟨⟨⟨fun h1 => hpl (hpr.mem_of_pow_mem _ h1), fun h1 => hpl (hpr.mem_of_pow_mem _ h1)⟩, hs'⟩, hs''⟩, hs⟩
    refine (mem_localization_iff _ _ _).2 ⟨_, ht, ?_⟩
    have key : (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) •
        (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
        (⟨_, hint⟩ : 𝓞 D.what₂.LL) • e := by
      rw [← algebraMap_smul D.what₂.LL, ← algebraMap_smul D.what₂.LL (⟨_, hint⟩ : 𝓞 D.what₂.LL)]
      have et : algebraMap (𝓞 D.what₂.LL) D.what₂.LL
          (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) =
          ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
            (s : D.what₂.LL) := by
        simp
      have hsc : ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
          (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹)) =
          algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c') := by
        field_simp
      rw [et, mul_smul, hA, hgg, smul_smul, smul_smul]
      congr 1
      show _ = algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')
      rw [← hsc]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory.CompareOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLatticeLeSpanThetaSeriesAwayFromOwnPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceLattice_le_span_thetaSeries_awayFromOwnPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  first | exact @GlobalTheory.CompareOff.compareOffOwn_run | exact GlobalTheory.CompareOff.compareOffOwn_run | (intros; apply GlobalTheory.CompareOff.compareOffOwn_run <;> assumption)
end
