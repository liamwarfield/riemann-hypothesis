module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFiniteHeis

private theorem _theta_add_aux {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  refine {
      quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
      level := by
        obtain ⟨U, hU, h1⟩ := hf.level
        obtain ⟨U', hU', h2⟩ := hg.level
        refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu.1 h0) w
        have e2 := congrFun (h2 u hu.2 h0) w
        unfold heisO at e1 e2 ⊢
        rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
      cont := hf.cont.add hg.cont
      smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

  }

private theorem _theta_smul_aux {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) := by
  refine {
      quasi γ w := by
        rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
      level := by
        obtain ⟨U, hU, h1⟩ := hf.level
        refine ⟨U, hU, fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu h0) w
        unfold heisO at e1 ⊢
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
      cont := hf.cont.const_smul c
      smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
  }


variable {D : D7}

theorem foldr_lin {ι X : Type} (p : (X → ℂ) → Prop) (A : ι → (X → ℂ) → (X → ℂ))
    (hp : ∀ i f, p f → p (A i f)) (hadd : ∀ i f g, p f → p g → A i (f + g) = A i f + A i g)
    (hsmul : ∀ i (c : ℂ) f, p f → A i (c • f) = c • A i f) (padd : ∀ f g, p f → p g → p (f + g))
    (psmul : ∀ (c : ℂ) f, p f → p (c • f)) (c : ℂ) {f g : X → ℂ} (hf : p f) (hg : p g) (l : List ι) :
    l.foldr (fun i h => A i h) (c • f + g) = c • l.foldr (fun i h => A i h) f + l.foldr (fun i h => A i h) g := by
  have hm : ∀ l : List ι, p (l.foldr (fun i h => A i h) f) ∧ p (l.foldr (fun i h => A i h) g) := by
    intro l
    induction l with
    | nil => exact ⟨hf, hg⟩
    | cons i l ih => exact ⟨hp i _ ih.1, hp i _ ih.2⟩
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, hadd i _ _ (psmul c _ (hm l).1) (hm l).2,
      hsmul i c _ (hm l).1]

theorem pureTensorO_lin (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : ℂ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f + g) φ =
      c • pureTensorO ψ θ S T sS sT BS BT f φ + pureTensorO ψ θ S T sS sT BS BT g φ := by
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := _root_.GlobalTheory.FockFiniteHeis._theta_add_aux hf hg
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := _root_.GlobalTheory.FockFiniteHeis._theta_smul_aux c hf
  have h : pureTensorO ψ θ S T sS sT BS BT (c • f + g) =
      c • pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT g := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    unfold pureTensorO pureTensorL
    rw [Module.Basis.constr_basis, Module.Basis.constr_basis, Module.Basis.constr_basis]
    unfold opPow
    have A1 : ∀ k f, IsThetaFunO ψ S T f →
        IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f) :=
      fun k f hf => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf
    have A2 : ∀ k f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (f + g) =
          aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f +
            aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g :=
      fun k f g hf hg => GlobalTheory.FockIndep.aPlus_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf hg
    have A3 : ∀ k (c : ℂ) f, IsThetaFunO ψ S T f →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (c • f) =
          c • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f :=
      fun k c f hf => GlobalTheory.FockIndep.aPlus_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ c hf
    exact foldr_lin (IsThetaFunO ψ S T) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) A1 A2 A3
      (fun _ _ hf hg => theta_add hf hg) (fun c _ hf => theta_smul c hf) c hf hg _
  rw [h, LinearMap.add_apply, LinearMap.smul_apply]

end GlobalTheory.FockFiniteHeis

namespace GlobalTheory.FockFiniteHeis

theorem pureTensorO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have h := pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (-1) theta_zero theta_zero φ
  rwa [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h

theorem heis_comb_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ sS sT BS BT (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0) → ∀ φ, ∑ i, a i • heisO ψ S T (y i) (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT (∑ i, a i • heisO ψ S T (y i) f) φ ∧ pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  intro D ψ θ S T hψ hθ sS sT BS BT f hf n a y hy φ
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := _root_.GlobalTheory.FockFiniteHeis._theta_add_aux hf hg
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := _root_.GlobalTheory.FockFiniteHeis._theta_smul_aux c hf
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f hf
  have hth : ∀ i, IsThetaFunO ψ S T (heisO ψ S T (y i) f) := fun i => (ft.2 (y i) (hy i)).1
  have key : ∀ s : Finset (Fin n), IsThetaFunO ψ S T (∑ i ∈ s, a i • heisO ψ S T (y i) f) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • heisO ψ S T (y i) f) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T (y i) f) φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ⟨theta_zero, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine ⟨theta_add (theta_smul _ (hth i)) ih.1, ?_⟩
      rw [pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hth i) ih.1 φ, ih.2]
  refine ⟨?_, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  rw [(key Finset.univ).2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(ft.2 (y i) (hy i)).2 sS BS sT BT φ]

end GlobalTheory.FockFiniteHeis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ sS sT BS BT (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0) → ∀ φ, ∑ i, a i • heisO ψ S T (y i) (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT (∑ i, a i • heisO ψ S T (y i) f) φ ∧ pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  first | exact @GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO | exact GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO | (intros; apply GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.LStab
section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem col_mem_hatL {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ)
    (j : Fin n) : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  rw [hβ]
  intro k
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem exists_fg_sub {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ) :
    ∃ Λ₁ ≤ Λ, Λ₁.FG ∧ Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ := by
  classical
  have hcol : ∀ j, ∃ T : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ⊆ (fun x : Fin n → E => fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) '' (Λ : Set (Fin n → E)) ∧
      β.1 *ᵥ Pi.single j 1 ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := fun j =>
    Submodule.mem_span_finite_of_mem_span (col_mem_hatL hβ j)
  choose T hT hmem using hcol
  let U : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := Finset.univ.biUnion T
  have hUsub : ∀ y ∈ U, ∃ x ∈ Λ, (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) = y := fun y hy => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨x, hx, e⟩ := hT j hj
    exact ⟨x, hx, e⟩
  choose! pre hpre hpref using hUsub
  have hle : Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hpre y hy
  refine ⟨Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))), hle,
    Submodule.fg_def.2 ⟨_, (U.finite_toSet.image pre), rfl⟩, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hle hx, rfl⟩
  · have hcolm : ∀ j, β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)))) := by
      intro j
      refine Submodule.span_mono ?_ (hmem j)
      intro y hy
      have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hy⟩
      exact ⟨pre y, Submodule.subset_span ⟨y, hyU, rfl⟩, hpref y hyU⟩
    intro y hy
    have hc := (hβ y).1 hy
    obtain ⟨c, hcdef⟩ : ∃ c, c = (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ y := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have ey : y = ∑ j, c j • (β.1 *ᵥ Pi.single j 1) := by
      have e1 : y = β.1 *ᵥ c := by
        rw [hcdef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : c = ∑ j, c j • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e1]
      conv_lhs => rw [e2]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
    rw [ey]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨c j, hc j⟩ : Formalism.L2.Herm.intAf F E) (hcolm j)

theorem latLoc_eq {Λ₁ Λ : Submodule (𝓞 E) (Fin n → E)} (hle : Λ₁ ≤ Λ) (hfg : Λ₁.FG)
    (heq : Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.AdelicU.latLoc F Λ₁ v = GlobalTheory.AdelicU.latLoc F Λ v := by
  apply le_antisymm
  · intro y hy
    exact GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => GlobalTheory.AdelicU.tmul_mem_latLoc ha (hle hx)) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
  · intro y hy
    refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    have h1 : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ₁ :=
      heq ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ₁ : Set (Fin n → E)) :=
      (GlobalTheory.LevSplit.latHat_iff Λ₁ _).2 h1
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hfg _).1 h2 v
    have h4 : GlobalTheory.AdelicU.vecLoc v (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) = fun i => (1 : Fv F v) ⊗ₜ[F] x i := by
      funext i
      simp [GlobalTheory.AdelicU.vecLoc]
    rw [h4] at h3
    have h5 := (GlobalTheory.AdelicU.latLoc F Λ₁ v).smul_mem
      ⟨a ⊗ₜ[F] ((1 : 𝓞 E) : E), GlobalTheory.AdelicU.tmul_mem_intLoc ha 1⟩ h3
    convert h5 using 1
    funext i
    show _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp

end General

section Adelic
variable {D : D7}

theorem finE_mem_St_iff_of_fg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (hfg : Λ.FG) (g : GA D V) :
    Lev.finE V g ∈ Formalism.L2.DIV.St β ↔
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  have h1 := GlobalTheory.LevSplit.mem_St_iff β Λ hfr (Lev.finE V g)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V g)
  have h3 := GlobalTheory.AdelicU.mem_levelOpen_iff_latHat D.sp.cm.sig V.gram hfg g
  have h4 := GlobalTheory.AdelicU.mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := Λ) (g := g)
  exact h1.trans (h2.symm.trans (h3.symm.trans h4))

end Adelic

theorem finE_mem_St_iff_stabLoc : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  intro D V β Λ hfr g
  obtain ⟨Λ₁, hle, hfg, heq⟩ := exists_fg_sub hfr
  have hfr₁ : Formalism.L2.DIV.IsFrame β Λ₁ := fun x => by
    rw [heq]; exact hfr x
  rw [finE_mem_St_iff_of_fg V β Λ₁ hfr₁ hfg g]
  have hL : ∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ₁ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := fun v => by
    unfold GlobalTheory.AdelicU.stabLoc
    rw [latLoc_eq hle hfg heq v]
  simp only [hL]

end GlobalTheory.ChainOnto.LStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  first | exact @GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc | exact GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc | (intros; apply GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem exists_doubled_weilDatum : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → ∃ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh := by
  intro H D ψ A B χA χB om h
  have h0 : ResEta D 1 0 := by
    have h1 := resEta_parity (m := 0) (resEta_mul h.resS (resEta_inv h.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h1
  have h2 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  exact H D ψ (dblSp A) B 1 χB h.1 h2 h.3 (resEta_parity h0 (by change 0 % 2 = (A.rank + A.rank) % 2; omega)) h.resT

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubledStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → ∃ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh := by
  first | exact @GlobalTheory.Core.Rk.exists_doubled_weilDatum | exact GlobalTheory.Core.Rk.exists_doubled_weilDatum | (intros; apply GlobalTheory.Core.Rk.exists_doubled_weilDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem coefClause_of_thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → ThetaClause ψ A B χB om omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → CoefClause ψ A B om omh ν 𝓕 := by
  intro D ψ A B χA χB om omh _ hT ν 𝓕 _ f₁ f₂ h₁ h₂
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta A B ν 𝓕 f₁ f₂, fun g => ?_⟩
  have h := ((hT f₁ f₂ h₁ h₂).2 g 1 1).1
  have h1 : om ((1 : GA D A), (1 : GA D B)) f₂ = f₂ := by
    rw [show ((1 : GA D A), (1 : GA D B)) = (1 : GA D A × GA D B) from rfl, map_one]; rfl
  have hd : detA A (1 : GA D A) = 1 := map_one _
  rw [h1, hd, map_one, inv_one, Circle.coe_one, one_smul] at h
  simp only [swSec]
  rw [h, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta]

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficientStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → ThetaClause ψ A B χB om omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → CoefClause ψ A B om omh ν 𝓕 := by
  first | exact @GlobalTheory.Core.Rk.coefClause_of_thetaClause | exact GlobalTheory.Core.Rk.coefClause_of_thetaClause | (intros; apply GlobalTheory.Core.Rk.coefClause_of_thetaClause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.CuspConj

theorem isKFinite_conj {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ} (h : GlobalTheory.Doubling.IsKFinite K Φ) :
    GlobalTheory.Doubling.IsKFinite K fun g => conj (Φ g) := by
  unfold GlobalTheory.Doubling.IsKFinite GlobalTheory.Doubling.kSpan at *
  refine GlobalTheory.Mem.AutConj.finiteDimensional_span_star h ?_
  rintro f ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  funext g
  show star (conj (Φ (g * k))) = Φ (g * k)
  rw [starRingEnd_apply, star_star]

theorem conj_comp_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ →
    ∀ u ∈ GlobalTheory.Cusp.A0 θ A cA, (fun g => conj (u g)) ∈ GlobalTheory.Cusp.A0 θ A cA := by
  intro D θ A cA hθ u hu
  have hu' : u ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A := hu
  show (fun g => conj (u g)) ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hu'
  obtain ⟨hs, hk⟩ := mem_autForms.1 h1
  refine Submodule.mem_inf.2 ⟨mem_autForms.2 ⟨?_, isKFinite_conj hk⟩, conj_mem_cuspCont h2⟩
  exact GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ A u hs

end GlobalTheory.Core.Rk.CuspConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMemStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ u ∈ A0 θ A cA, (fun g => conj (u g)) ∈ A0 θ A cA := by
  first | exact @GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 | exact GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 | (intros; apply GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)

noncomputable section

namespace GlobalTheory.Core.Rk.DeltaTheta

variable {D : D7}

def fstH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun x := -resR A B x
  map_zero' := neg_zero
  map_add' x y := neg_add (resR A B x) (resR A B y)

theorem continuous_fstH (A B : HSp D) : Continuous (fstH A B) :=
  continuous_matrix fun i _ => continuous_id.matrix_elem i _

theorem continuous_sndH (A B : HSp D) : Continuous (sndH A B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  have h : Continuous (resR A B) := continuous_matrix fun i _ => continuous_id.matrix_elem i _
  exact h.neg

theorem map_fstH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (fstH A B u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h i) (finSumFinEquiv (Sum.inl j))

theorem map_sndH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (sndH A B u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u i (finSumFinEquiv (Sum.inr j))) = 0 := congrFun (congrFun h i) (finSumFinEquiv (Sum.inr j))
    change φ (-(u i (finSumFinEquiv (Sum.inr j)))) = 0
    rw [map_neg, e, neg_zero]

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (fstH A B x) (fstH A B y) - hO A B (sndH A B x) (sndH A B y) := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, fstH, sndH, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y =
      symplOH A B (fstH A B x) (fstH A B y) - symplOH A B (sndH A B x) (sndH A B y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, hO_dbl, map_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem isThetaFunO_delta {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) {A B : HSp D} {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) : IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) := by
  have hd : delta A B f₁ f₂ = fun w => f₁ (fstH A B w) * conj (f₂ (sndH A B w)) := rfl
  rw [hd]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e₁ : fstH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => γ i (finSumFinEquiv (Sum.inl j))) := rfl
    have e₂ : sndH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => -γ i (finSumFinEquiv (Sum.inr j))) :=
      Matrix.ext fun i j => (map_neg (incA D) _).symm
    rw [map_add (f := _), map_add (f := _), symplOH_dbl, e₁, e₂, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (fstH A B) ⊓ U₂.comap (sndH A B),
      (hU₁.preimage (continuous_fstH A B)).inter (hU₂.preimage (continuous_sndH A B)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_fstH _ _ _ h0)) (fstH A B w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ _ _ h0)) (sndH A B w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOH_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _), map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_fstH A B)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH A B)))
  · simp only [map_add (f := _)]
    exact (h₁.smooth k ((fstH A B).comp L) ((continuous_fstH A B).comp hL) (fun t => map_fstH _ _ _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH A B).comp L) ((continuous_sndH A B).comp hL)
        (fun t => map_sndH _ _ _ (h0 t)) _))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ → IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) :=
  fun _ _ _ _ hψ _ _ h₁ h₂ => isThetaFunO_delta hψ.1.2.1 h₁ h₂

end GlobalTheory.Core.Rk.DeltaTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardCharStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ → IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) := by
  first | exact @GlobalTheory.Core.Rk.DeltaTheta.main | exact GlobalTheory.Core.Rk.DeltaTheta.main | (intros; apply GlobalTheory.Core.Rk.DeltaTheta.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem continuous_covolOne_integral {D : D7} {m n : ℕ} {X : Type} [TopologicalSpace X] {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (F : X → Mx D m n → ℂ)
    (hc : Continuous fun p : X × Mx D m n => F p.1 p.2)
    (hF : ∀ x, ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, F x (γ + a) = F x a) :
    Continuous fun x => ∫ a in 𝓕, F x a ∂μ := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have hi : ∀ x, IntegrableOn (F x) 𝓕 μ := fun x =>
    GlobalTheory.MixModel.covolOne_integrableOn h _ (hc.comp (Continuous.prodMk_right x)) (hF x)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc' : Continuous fun p : X × Mx D m n => ‖F p.1 p.2 - F x₀ p.2‖ :=
    (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).norm
  have hev : ∀ᶠ x in nhds x₀, ∀ a ∈ K, ‖F x a - F x₀ a‖ < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hc'.continuousAt.eventually_lt continuousAt_const ?_
    simpa using hε
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  have hb : ∀ a, ‖F x a - F x₀ a‖ ≤ ε / 2 := fun a => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hF x γ hγ a, ← hF x₀ γ hγ a]
    exact (hx _ ha).le
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)).trans_lt ?_
  rw [measureReal_def, Measure.restrict_apply_univ, h.2.2, ENNReal.toReal_one, mul_one]
  exact half_lt_self hε

theorem swSec_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IntegrableOn (fun w => φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w)) 𝓕 ν ∧ Continuous (swSec A B omh ν 𝓕 φ) := by
  intro D ψ A B χB omh hω ν 𝓕 hν φ hφ
  refine ⟨GlobalTheory.ThetaMean.integrableOn_lagr hν hφ, ?_⟩
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ omh hω φ hφ
  exact continuous_covolOne_integral hν (fun g w => omh (g, 1) φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w))
    (hj.comp ((continuous_fst.prodMk continuous_const).prodMk (GlobalTheory.ThetaMean.continuous_lagr.comp continuous_snd)))
    (fun g => GlobalTheory.ThetaMean.periodic_lagr (hω.om_pres _ _ hφ))

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuousStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSection_integrable_and_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IntegrableOn (fun w => φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w)) 𝓕 ν ∧ Continuous (swSec A B omh ν 𝓕 φ) := by
  first | exact @GlobalTheory.Core.Rk.IP.swSec_integrable_continuous | exact GlobalTheory.Core.Rk.IP.swSec_integrable_continuous | (intros; apply GlobalTheory.Core.Rk.IP.swSec_integrable_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
noncomputable section

namespace GlobalTheory.Core.Rk.IP.Cartan

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

section Complex

variable {n : ℕ} {G s b c : Matrix (Fin n) (Fin n) ℂ}

theorem herm_of_isCartanInv (hs : IsCartanInv G s) : Gᴴ = G := by
  obtain ⟨h1, h2, h3⟩ := hs
  have h4 : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul]; exact h3.1
  have h5 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← mul_assoc, h5, one_mul]
    _ = G := by rw [h4, ← mul_assoc, h2]

theorem frame_gram_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : bᴴ * G * b = c * s * b := by
  calc bᴴ * G * b = bᴴ * (G * (s * (b * c) * s)) * b := by rw [hbc, mul_one, hs, mul_one]
    _ = (bᴴ * (G * s) * b) * (c * s * b) := by simp only [mul_assoc]
    _ = _ := by rw [h, one_mul]

theorem frame_gram_sq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) :
    (bᴴ * G * b) * (bᴴ * G * b) = 1 := by
  rw [frame_gram_eq hbc hs h]
  calc c * s * b * (c * s * b) = c * (s * (b * c) * s) * b := by simp only [mul_assoc]
    _ = 1 := by rw [hbc, mul_one, hs, mul_one, mul_eq_one_comm.1 hbc]

theorem frame_inv_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : b * bᴴ * G = s := by
  rw [mul_conjTranspose_mul_eq hbc (frame_gram_eq hbc hs h)]
  calc b * (c * s * b) * c = (b * c) * s * (b * c) := by simp only [mul_assoc]
    _ = s := by rw [hbc, one_mul, mul_one]

theorem blkMat_conjTranspose (x y : Matrix (Fin n) (Fin n) ℂ) :
    (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := by
  simp [blkMat, Matrix.fromBlocks_conjTranspose]

end Complex

variable {D : D7} {θ : InfFam D}

theorem compAt_blkGL (τ : D.what₂.Tau) {n : ℕ} (a : GL (Fin n) (AE D)) :
    compAt θ τ (blkGL finSumFinEquiv (a, a)).1 = blkMat finSumFinEquiv (compAt θ τ a.1) (compAt θ τ a.1) :=
  blkMat_map finSumFinEquiv ((θ τ).comp (infPart D)) (map_zero _) _ _

theorem commute_of_mem_Kmax (hθ : IsInfFam θ) {V : HSp D} {a : GL (Fin V.rank) (AE D)} (τ : D.what₂.Tau)
    (hd : ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) = 1)
    {g : GA D V} (hg : g ∈ Kmax V a) :
    Commute (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) (frameInv θ V a τ) := by
  refine (unitary_iff_commute (compAt_mul_inv τ a) rfl hd (infMat_isometry hθ τ g)).1 ?_
  rw [compAt_eq_map hθ, compAt_eq_map hθ, eq_infProj hθ (embOverOf D τ) rfl]
  exact (mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) V.gram a g).1
    (((mem_levelAll (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V) (a := a) (g := g)).1 hg).2 _)

theorem cartan_dbl : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D θ A sA a hθ hs ha
  have hbc := fun τ => compAt_mul_inv (θ := θ) τ a
  have e : ∀ τ, frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ = blkMat finSumFinEquiv (sA τ) (-sA τ) := fun τ => by
    rw [frameInv_dblSp, show frameInv θ A a τ = sA τ from frame_inv_eq (hbc τ) (hs τ).1 (ha τ)]
  have hd : ∀ τ, (compAt θ τ (blkGL finSumFinEquiv (a, a)).1)ᴴ * blkMat finSumFinEquiv (gramAt D A τ) (-gramAt D A τ) *
      compAt θ τ (blkGL finSumFinEquiv (a, a)).1 =
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) := fun τ => by
    rw [compAt_blkGL, blkMat_conjTranspose, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  have hd2 : ∀ τ, blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) *
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) = 1 := fun τ => by
    rw [blkMat_mul, neg_mul_neg, frame_gram_sq (hbc τ) (hs τ).1 (ha τ), blkMat_one]
  refine ⟨fun τ => ?_, fun k hk τ => ?_⟩
  · have h := isCartanInv_of_frame (compAt_mul_inv (θ := θ) τ (blkGL finSumFinEquiv (a, a))) (hd τ) (hd2 τ) (by
      rw [blkMat_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, herm_of_isCartanInv (hs τ), ← mul_assoc])
    rw [← gramAt_dblSp] at h
    have h' : IsCartanInv (gramAt D (dblSp A) τ) (frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ) := h
    rw [e] at h'
    exact h'
  · rw [Khat_eq] at hk
    have h := commute_of_mem_Kmax hθ (V := dblSp A) (a := blkGL finSumFinEquiv (a, a)) τ (by
      rw [gramAt_dblSp]
      exact (congrArg₂ (· * ·) (hd τ) (hd τ)).trans (hd2 τ)) hk
    rw [e] at h
    exact h

end GlobalTheory.Core.Rk.IP.Cartan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompactStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  first | exact @GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl | exact GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl | (intros; apply GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem integrable_quotHeight_pow_mul_norm_of_rapidDec : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (u : GA D A → ℂ), GlobalTheory.Grow.RapidDec A u → ∀ N : ℕ, Integrable (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) (autMeasure A m) := by
  intro D A m hm u hu N
  haveI := hm
  have : BorelSpace (GA D A) := ⟨rfl⟩
  set f : GA D A → ℝ := fun g => GlobalTheory.Grow.quotHeight A g ^ N * ‖u g‖ with hf
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) f := fun γ hγ g => by
    simp only [f, GlobalTheory.Grow.quotHeight_left A hγ, hu.left hγ]
  have hfc : Continuous f := ((GlobalTheory.Grow.continuous_quotHeight A).pow N).mul hu.continuous.norm
  have e : (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) = GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f := rfl
  rw [e]
  have hfd : IsFundamentalDomain (GQ A) (GlobalTheory.AutomorphicL2Unitary.stdDom (GQ A)) m := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ m
  haveI : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.autMeasure A m) := ⟨by
    rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol A m _ hm hfd⟩
  obtain ⟨C, hC⟩ := hu.decay N
  have hmeas : Measurable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f) := by
    refine measurable_from_quotient.2 ?_
    have h' : (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f ∘ Quotient.mk'') = f := funext fun g => hL.descend_mk g
    rw [h']
    exact hfc.measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable C (.of_forall fun q => ?_)
  have hq : 0 ≤ GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f q :=
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le N) (norm_nonneg _)
  rw [Real.norm_of_nonneg hq]
  show GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖ ≤ C
  rw [mul_comm]
  exact hC _

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecrStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (u : GA D A → ℂ), GlobalTheory.Grow.RapidDec A u → ∀ N : ℕ, Integrable (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) (autMeasure A m) := by
  first | exact @GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec | exact GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec | (intros; apply GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec <;> assumption)
end
end
