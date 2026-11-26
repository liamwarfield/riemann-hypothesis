module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.HasDSComp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.CptSt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrUnitaryTraceNeZeroCopyFinDSX
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PsCo.Plug

theorem archTrace : _root_.GlobalTheory.Published.DiscreteSeriesClassification → True → True →
    ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.IsTestDataX V lam M T U μa μf μ fa ff →
    ∀ (ρ : D.what₂.Tau) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (δ : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (X →L[ℂ] X)), IsIrrUnitary δ →
    ∃ c, HasTrace (repOp δ (μa (placeOf D ρ)) (fa (placeOf D ρ))) c ∧ (c ≠ 0 → IsUnitEquiv δ (dsRep M ρ)) := by
  intro _ _ _ D V lam S M T U μa μf μ _ _ fa ff hT ρ X _ _ _ δ hδ
  obtain ⟨-, -, -, -, -, harch, -⟩ := hT
  haveI := (M.ds ρ).1
  have h := harch ρ
  by_cases he : IsUnitEquiv δ (dsRep M ρ)
  · exact ⟨1, he.symm.hasTrace h.trace_self, fun _ => he⟩
  · exact ⟨0, h.trace_other X δ hδ.unitary hδ.irred he, fun h0 => absurd rfl h0⟩

end GlobalTheory.PsCo.Plug

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.AutMult
section Helpers
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
end Helpers

open Classical in
theorem hasTrace_repOp_of_isCopyFinDSX : ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c → HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c := by
  intro D V lam S M T U μa μf μ _ _ fa ff hT ν hν H _ _ _ π hπ W _ _ σ hirr hadm hcopy c hc
  obtain ⟨-, -, -, -, hres, harch, hfin⟩ := hT
  have hff := hfin.isFinFamily
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨Tm, hTm, hinj, hdense⟩ := hcopy
  have hTm' : Tm ∈ homTensorPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) π ⊤ := hTm
  obtain ⟨A, hA, hAtr⟩ := hc
  have hσ : GlobalTheory.PRep.IsSmooth σ := hadm.1
  have hX := GlobalTheory.TrOpTensor.opTensor D V S M μa μf μ hres ν hν fa ff harch.mem hff W σ hσ H π hπ.unitary Tm hTm A hA
  obtain ⟨hlc, hcs⟩ := GlobalTheory.FinTrace.finFn_mem_SB V hff
  obtain ⟨U₀, hU₀, hbi⟩ := GlobalTheory.Orb.exists_biinvariant (f := finFn V ff) ⟨hlc, hcs⟩
  obtain ⟨K₀, hK₀o, hK₀c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup (GfC V), K = U₀ ⊓ K₀ := ⟨_, rfl⟩
  have hKo : IsOpen (K : Set (GfC V)) := hKdef ▸ hU₀.inter hK₀o
  have hKc : IsCompact (K : Set (GfC V)) := hKdef ▸ hK₀c.inter_left (U₀.isClosed_of_isOpen hU₀)
  have hKU : ∀ k ∈ K, k ∈ U₀ := fun k hk => (Subgroup.mem_inf.1 (hKdef ▸ hk)).1
  have hZ : FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) := hadm.2 K hKo hKc
  have hrange : LinearMap.range A ≤ GlobalTheory.PRep.fixed σ K := by
    rintro _ ⟨w, rfl⟩
    exact GlobalTheory.IwahoriRel.isIntegralOp_mem_fixed hA (fun k hk g => (hbi k (hKU k hk) g).1) w

  obtain ⟨e, he⟩ : ∃ e, e = GlobalTheory.InvBilinTest.cosetInd K hKo hKc 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = smoothOp σ ν e.1 := ⟨_, rfl⟩
  have hP : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ e.1 P := by
    intro v l
    refine ⟨?_, ?_⟩
    · have h := GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.smoothOp_integrand e.2.1 e.2.2 v).1
        (hσ.smoothOp_integrand e.2.1 e.2.2 v).2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using h
    · rw [hPdef, hσ.map_smoothOp e.2.1 e.2.2 l v]
      simp only [smul_eq_mul]
  have hconv := (GlobalTheory.OpConv.isIntegralOp_conv_and_translate _ ν W σ hσ _ ⟨hlc, hcs⟩ e.1 e.2 A P hA hP).1
  rw [he, conv_cosetInd_eq_smul ν K hKo hKc _ (fun k hk g => (hbi k (hKU k hk) g).2)] at hconv
  have hAP : A ∘ₗ P = (ν.real K : ℂ) • A := hconv.unique (isIntegralOp_const_mul hA _)
  have hvol : (ν.real K : ℂ) ≠ 0 := by
    have h1 : ν K ≠ 0 := (hKo.measure_pos ν ⟨1, K.one_mem⟩).ne'
    have h2 : ν.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hKc.measure_ne_top⟩
    exact_mod_cast h2
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  have hinner : ∀ w w' y y', inner ℂ (Tm w' y') (Tm w y) = bePi (Tm w) (Tm w') * ∏ τ, inner ℂ (y' τ) (y τ) :=
    fun w w' y y' => inner_eq_bePi hδ hπ.unitary (hTm'.1 w) (hTm'.1 w') y y'
  have hcond : ∀ w, (∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm w) (Tm z) = 0) → A w = 0 := by
    intro w hw
    have hPw : P w ∈ GlobalTheory.PRep.fixed σ K := hPdef ▸ hσ.smoothOp_mem_fixed (μ := ν) e.2.1 e.2.2 (fun k hk g => by
      simp only [he, GlobalTheory.InvBilinTest.cosetInd_apply, inv_one, mul_one, K.mul_mem_cancel_left hk]) w
    have hβP : ∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm (P w)) (Tm z) = (ν.real K : ℂ) * bePi (Tm w) (Tm z) := by
      intro z hz
      let l : W →ₗ[ℂ] ℂ :=
        { toFun := fun v => bePi (Tm v) (Tm z)
          map_add' := fun a b => by simp [bePi, inner_add_right]
          map_smul' := fun a b => by simp [bePi, inner_smul_right] }
      have hl : ∀ g ∈ K, l (σ g w) = l w := fun g hg => by
        have hz' : σ g z = z := mem_fixed.1 hz g hg
        show bePi (Tm (σ g w)) (Tm z) = bePi (Tm w) (Tm z)
        simp only [bePi]
        calc inner ℂ (Tm z fun i => unitVec (M.H i)) (Tm (σ g w) fun i => unitVec (M.H i))
            = inner ℂ (Tm (σ g z) fun i => unitVec (M.H i)) (Tm (σ g w) fun i => unitVec (M.H i)) := by rw [hz']
          _ = inner ℂ (π g (Tm z fun i => unitVec (M.H i))) (π g (Tm w fun i => unitVec (M.H i))) := by
            rw [(mem_homTensorPi.1 hTm').2.1, (mem_homTensorPi.1 hTm').2.1]; rfl
          _ = _ := inner_map_map hπ.unitary _ _ _
      have h1 := (hP w l).2
      have h2 : ∫ g, e.1 g * l (σ g w) ∂ν = ∫ g, (if g ∈ K then l w else 0) ∂ν := by
        refine integral_congr_ae (.of_forall fun g => ?_)
        by_cases hg : g ∈ K
        · simp [he, GlobalTheory.InvBilinTest.cosetInd_apply, hg, hl g hg]
        · simp [he, GlobalTheory.InvBilinTest.cosetInd_apply, hg]
      rw [h2, GlobalTheory.InvBilinTest.integral_ite K hKo] at h1
      exact h1
    have h0 : P w = 0 := by
      by_contra hne
      have hT0 : Tm (P w) ≠ 0 := fun h => hne (hinj (h.trans (map_zero Tm).symm))
      have hpos := bePi_self_pos hδ hπ.unitary (hTm'.1 (P w)) hT0
      rw [hβP (P w) hPw, hw (P w) hPw, mul_zero] at hpos
      exact lt_irrefl _ hpos
    have h3 := LinearMap.congr_fun hAP w
    rw [LinearMap.comp_apply, h0, map_zero, LinearMap.smul_apply] at h3
    exact (smul_eq_zero.1 h3.symm).resolve_left hvol
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  have key := GlobalTheory.TensorTrace.hasTrace_finiteRank_tensor D.what₂.Tau M.H H W Tm (fun w w' => bePi (Tm w) (Tm w')) hinner hinj hdense A c hAtr
    (GlobalTheory.PRep.fixed σ K) hZ hrange hcond (fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ)))
    (fun _ => 1) (fun τ => (harch τ).trace_self) (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) hX
  simpa using key
end GlobalTheory.AutMult
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.copyTraceT : ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c → HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c := by
  first | exact @GlobalTheory.AutMult.hasTrace_repOp_of_isCopyFinDSX | exact GlobalTheory.AutMult.hasTrace_repOp_of_isCopyFinDSX | (intros; apply GlobalTheory.AutMult.hasTrace_repOp_of_isCopyFinDSX <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
namespace GlobalTheory

end GlobalTheory
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

end GlobalTheory
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.TestFnCusp

theorem isCuspidalOp_tensorX : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  intro hCO hPC D V lam S M T U μa μf μ _ _ fa ff hTD
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hT : IsTestFnGX M T U μa μf (tensor D.sp.cm.sig V.gram fa ff) := ⟨fa, ff, ha, hb, rfl⟩
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := hT.isPureTensor.2
  have hU := hPC.2 D V hodd S M T (hypH_of_noFixed T hnf) U μa μf _ hT
  refine hCO D V μ _ hf ?_ ?_
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).1 ν x y).2
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).2 ν x y).2
end GlobalTheory.TestFnCusp
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.cuspOpT : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  first | exact @GlobalTheory.TestFnCusp.isCuspidalOp_tensorX | exact GlobalTheory.TestFnCusp.isCuspidalOp_tensorX | (intros; apply GlobalTheory.TestFnCusp.isCuspidalOp_tensorX <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SpecTraceProof
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

end GlobalTheory.SpecTraceProof
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PsCo.SpecX

open GlobalTheory GlobalTheory.SpecTraceProof MainStatements.Flath2

theorem hasDSComp (h1 : IrredSt) (h2 : CompSt) : GlobalTheory.Published.DiscreteSeriesClassification →  True → True → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
  have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
  have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨Q, hQ, hrep⟩ := GlobalTheory.T.pureTensorOperator_split_oneRealPlace D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
  haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
  have hcont := continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem (placeOf D τ))
  have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) := hcont.integrable_of_hasCompactSupport (hmem _).1
  have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
    isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
  obtain ⟨W, hW⟩ := h1 _ H _ hπw (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ))) Q
    (fun S hS => hπw.comp_repOp hπw hcont (hmem _).1 S fun g v => DFunLike.congr_fun (hS g) v) hQ
    (GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt htc.isHilbertSchmidt)
    (fun h0 => hc0 (by rw [← hc.2, hrep, h0]; exact trace_zero))
  obtain ⟨δ, hδ'⟩ := h2 D V H π hπ (placeOf D τ) W hW
  obtain ⟨c', hc', himp⟩ := GlobalTheory.PsCo.Plug.archTrace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    haveI := δ.isIrr.complete
    have hc'w : HasTrace (repOp δ.π (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δ.π _ δ.isIrr hπw hδ' Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact GlobalTheory.isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

theorem copyFinDS (h1 : IrredSt) (h2 : CompSt) (h4 : AdmSt) : GlobalTheory.Published.DiscreteSeriesClassification →  True → True → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ f ∈ CcGA V, IsCompactOperator (repOp π μ f)) → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ hcp c hc hc0
  have hcomp : HasDSComp M π := hasDSComp h1 h2 hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hcomp hU
  have hadm := h4 D V S M μ H π hπ.unitary hcp hU
  have hirr := GlobalTheory.FinPartIrrAdm.irreducible hπ hcomp hU hadm
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := GlobalTheory.PsCo.Plug.copyTraceT D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

theorem specTrace (h1 : IrredSt) (h2 : CompSt) (h3 : CptSt) (h4 : AdmSt) : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → True → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → True → SpecTraceX := by
  intro hDSC tc hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := GlobalTheory.PsCo.Plug.cuspOpT hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := copyFinDS h1 h2 h4 hDSC hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr
      (h3 tc D V μ x.rep.H x.rep.π x.rep.isIrr hm') _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (GlobalTheory.PsCo.Plug.copyTraceT D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

theorem main : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.TrMult.SpecTraceX :=
  fun ds tc => specTrace irredSt compSt cptSt admissible_representation_factorisation ds tc trivial (GlobalTheory.T.cuspidalOperators_vanishingRadicalIntegrals_unitaryGroup tc) GlobalTheory.PsCo.Plug.parabolicT trivial

end GlobalTheory.PsCo.SpecX

end
