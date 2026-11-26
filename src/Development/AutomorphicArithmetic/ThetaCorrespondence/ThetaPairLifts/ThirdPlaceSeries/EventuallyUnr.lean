module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAbove
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeometricOfHyp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadingStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip
open GlobalTheory.Mem.Chr hiding HChar
namespace GlobalTheory.CuspRep.ParLaws
section Group
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end Group
section Local
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Par
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem reciprocity_unramified_iff_spherical (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (σ : IrrRep (GL (Fin a) (w.adicCompletion E))) :
    (rc (cls σ)).unr ↔ IsSpherical σ.ρ := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  rw [← H.sph]
  exact ⟨fixed_ne_bot_of_equiv (equivRep σ).symm, fixed_ne_bot_of_equiv (equivRep σ)⟩
theorem reciprocity_eq_diagonal_inv_of_has_satake (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ}
    (hα : HasSatake σ.ρ α) : rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  have φ := equivRep σ
  exact H.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
variable [_root_.NumberField.IsTotallyComplex E]
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
theorem local_parameter_eq_reciprocity_of_is_local_component {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ)
    (h : IsPlaceOver A w) : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls (toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [_root_.GlobalTheory.CuspRep.ParLawsT.locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl
theorem dim_local_parameter_eq_rank (π : CG E a) (h : IsPlaceOver A w) : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpDim = a := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
include hF in
theorem eventually_unramified_local_parameter (π : CG E a) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).unr := by
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  refine (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h).symm ▸ (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) _).2 ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm
theorem local_parameter_of_hecke_character_eq_reciprocity (χ : HChar E) (h : IsPlaceOver A w) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (.ofChar (χ.loc w) (isSmoothChar_loc χ w)) :=
  _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (CG.isLoc_ofChar χ w) h
end Par
section Conj
end Conj
section Host
end Host
end GlobalTheory.CuspRep.ParLaws
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecUnit
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LocLanglands
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem _root_.UpperTheory.Zero.LLC.IsRecT.recSupp {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) :
    RecSupp fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := H
  intro n s π d σ hs g
  have h1 := (hasSupport_of_isCuspSupport hs).of_equiv (equivRep (toIrrRep π))
  have h2 := H.supp (cls (toIrrRep π)) _ h1 g
  rw [Multiset.map_map] at h2
  exact h2
theorem _root_.UpperTheory.Zero.LLC.IsRecT.recUnit {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := H
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _
end GlobalTheory.LocLanglands
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAlgNorm
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalOfCusp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
variable [IsAlgClosure E Ω] [IsCMField E]
end GlobalTheory.GalOfCusp
namespace GlobalTheory.Published
open GlobalTheory.GalOfCusp
end GlobalTheory.Published
namespace GlobalTheory.GalOfCusp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem rec_algNorm_alt {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    rc (algNorm σ) = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  exact H.nu_eq _ _
end GlobalTheory.GalOfCusp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIs
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem com_is_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (_root_.GlobalTheory.BaseChain.com_z W).Is := by
  intro D L hT Gi Gl Kc Yd cX ex W hP
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have h2 := D.R.two_le_m
  exact GlobalTheory.SeeSaw.ComCols.com_is_of_levCh (levAt_is hC.lev) (_root_.GlobalTheory.BaseChain.com_z W) hC.models.inf
    (hC.chain.ωY W.P.A3.A.μ0 0 (by omega)).std rfl (chrEq_mu_base hC.lev) hC.lev.eta hC.lev.chi
end GlobalTheory.BaseChain
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChain_com_z_is_of_pkHyp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (_root_.GlobalTheory.BaseChain.com_z W).Is := by
  first | exact @_root_.GlobalTheory.BaseChain.com_is_alt | exact _root_.GlobalTheory.BaseChain.com_is_alt | (intros; apply _root_.GlobalTheory.BaseChain.com_is_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSupportCompatible
section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SupportCompat
section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.IsIrreducibleOfIsIrrRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace Ysupp.IrreducibleSupport

open GlobalTheory GlobalTheory.SerSys

section Chain

open GlobalTheory.LocGL

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

end Chain

end Ysupp.IrreducibleSupport
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace UpperTheory.One.M

open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem mapsToProd_tw {g : ℕ} [Fact g.Prime] {n a b : ℕ} {V W W' W'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup W''] [Module ℂ W'']
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
    {ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'} {ρ' : Representation ℂ (GL (Fin b) ℚ_[g]) W''} (μ : ℚ_[g]ˣ →* ℂˣ)
    (hμ : Supp.IsUnram μ) (e : W' ≃ₗ[ℂ] W'')
    (he : ∀ y v, ρ' y (e v) = ((μ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • e (ρ y v)) (h : Supp.MapsToProd π σ ρ) :
    Supp.MapsToProd π σ ρ' := by
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, h0, H⟩ := h
  refine ⟨hn, ν₁, ν₂ * μ⁻¹, (TensorProduct.congr (LinearEquiv.refl ℂ W) e).toLinearMap ∘ₗ Λ, h₁, fun u => ?_, fun h => h0 (LinearMap.ext fun v => ?_),
    fun p x y hp hx hy v => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h₂ u, hμ u, inv_one, mul_one]
  · exact (TensorProduct.congr (LinearEquiv.refl ℂ W) e).map_eq_zero_iff.1 (LinearMap.congr_fun h v)
  · have key : ∀ z, TensorProduct.map (σ x) (ρ' y) (TensorProduct.congr (LinearEquiv.refl ℂ W) e z) =
        ((μ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
          TensorProduct.congr (LinearEquiv.refl ℂ W) e (TensorProduct.map (σ x) (ρ y) z) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s t => simp [he, TensorProduct.tmul_smul]
      | add s t hs ht => simp only [map_add (f := _), hs, ht, smul_add]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [H p x y hp hx hy v, key, map_smul, smul_smul]
    congr 1
    simp [mul_assoc]

theorem inInd_reps {g : ℕ} [Fact g.Prime] {π : Supp.GLRep g} {L : List (Supp.GLRep g)} (h : Supp.InInd π L) :
    ∀ y : List (IrrGL (k := ℚ_[g])), List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL (k := ℚ_[g])) =>
      ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y →
      Supp.InInd π (y.map fun x => ⟨x.1, Rep.of x.rep⟩) := by
  induction h with
  | nil π h0 hi =>
    intro y hy
    cases hy
    exact .nil π h0 hi
  | cons π σ ρ S hπ hρ _ hM ih =>
    intro y hy
    cases hy with
    | cons h1 h2 =>
      obtain ⟨hs, hi, μ, hμ, rfl⟩ := h1
      let φ := (GlobalTheory.TypeRec.TwistInert.twistEquiv (IrrGL.equivOf ρ.2.ρ hs hi) (detChar (Fin ρ.1) μ)).trans
        (IrrGL.twEquiv (IrrGL.of ρ.2.ρ hs hi) μ (isSmoothChar_of_isUnram hμ))
      refine .cons π σ _ _ hπ (Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _)) (ih _ h2)
        (mapsToProd_tw μ (fun u => hμ _ ?_) φ.toLinearEquiv (fun y v => ?_) hM)
      · have hn : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := PadicInt.norm_units u
        have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g ((u : ℤ_[g]) : ℚ_[g]) 1
        have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 ((u : ℤ_[g]) : ℚ_[g])
        rw [hn, map_one, norm_one] at a1 a2
        exact le_antisymm (not_lt.1 fun h => lt_irrefl _ (a2.1 h)) (not_lt.1 fun h => lt_irrefl _ (a1.1 h))
      · rw [← map_smul]
        exact (LinearMap.congr_fun (φ.isIntertwining' y) v).symm

end UpperTheory.One.M
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MSuppC
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppIne
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.SuppIne
open GlobalTheory.LocGL GlobalTheory.SmGL
section Transport
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Transport
end GlobalTheory.SuppIne
namespace GlobalTheory.SuppIne
open GlobalTheory.LocGL GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem ine_pol_rc_eq_char_pol_loc_rec {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D}
    {rc : GlobalTheory.SerSys.Corr D} (h : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) (k : Fin 2) (v : D.nd.PlG k) (n : ℕ)
    (σ : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) (π : QRep (D.host.g k) n)
    (e : Nonempty (π ≅ pull I k v σ)) :
    D.naut.inePol (rc k v n π) (D.ntypes.tg k v) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)).charPol
        (GlobalTheory.WeilDeligne.ineIncl _ ⟨D.ntypes.tg k v, D.ntypes.tg_mem k v⟩) := by
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), h k v n σ π e,
    GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ (D.ntypes.tg_mem k v)]
theorem ine_pol_rc_eq_prod_of_has_support : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Supp.GLRep (D.host.g k)) (y : List (GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k])), GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k])) → D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = (y.map fun x => D.naut.inePol (rc k v x.1 (Rep.of x.rep)) (D.ntypes.tg k v)).prod := by
  intro hL D T I rc hRc k v π y hy
  obtain ⟨n, ρ⟩ := π
  have hs := hy.isSmooth
  have hi := hy.isIrreducible
  change D.naut.inePol (rc k v n ρ) _ = _
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hsupp : HasSupport (GlobalTheory.LocLanglands.cls (tr I k v ρ hs hi)).rep
      ((y : Multiset _).map (trGL (I.i k v) (continuous_symm I k v))) :=
    (hasSupport_comp (I.i k v) (I.cont k v) (continuous_symm I k v) hy).of_equiv (IrrGL.equivOf _ _ _)
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_char_pol_loc_rec hRc k v n _ ρ (iso_pull I k v ρ hs hi), H.supp _ _ hsupp, Multiset.map_coe, Multiset.map_coe,
    Multiset.prod_coe, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Function.comp_apply, _root_.GlobalTheory.SuppIne.ine_pol_rc_eq_char_pol_loc_rec hRc k v x.1 _ (Rep.of x.rep)
    (iso_pull I k v (Rep.of x.rep) x.2.rep.smooth x.2.rep.irr)]
  rfl
end GlobalTheory.SuppIne
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace UpperTheory.One.M
open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil
theorem supportCompat_alt_alt : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hZ hL D T I rc hrc k v π hi hs
  obtain ⟨L, y, hind, -, hsup, hf⟩ := GlobalTheory.SerSys.SuppTame.chain hZ (D.host.g k) π hi hs
  refine ⟨_, inInd_reps hind y hf, fun ρ hρ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hρ
    have hc := hsup.isCusp (Multiset.mem_coe.2 hx)
    exact ⟨hc.1, Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _),
      GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[D.host.g k] x.1 _ x.rep hc.2⟩
  show D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = _
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_prod_of_has_support hL D T I rc hrc k v π y hsup, List.map_map]
  rfl
end UpperTheory.One.M
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  first | exact @_root_.UpperTheory.One.M.supportCompat_alt_alt | exact _root_.UpperTheory.One.M.supportCompat_alt_alt | (intros; apply _root_.UpperTheory.One.M.supportCompat_alt_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAboveOfAlgebraicCharacterWDAl
set_option synthInstance.maxHeartbeats 200000

section
namespace GlobalTheory
theorem heckeLAdicParameterAbove_of_algebraicCharacterWD_alt (H : GlobalTheory.Published.AlgebraicCharacterWD) :
    _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A h O _ _ _ Bw hj ξ hξ rc hrc
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, L⟩ := hOpn) | obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [H E Ω l P AI hT ι art hart χ n μ hχ hμ hL w A h O Bw hj ξ hξ a ha]
  exact (L.one ξ hξ.1).symm
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricOfHyp
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovHt.GeomBound
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem geom_of_prints_toroidal_deepGood_size : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.GeometricCondition := by
  intro hX hG hQ hP h1 h2 h3 _ hS
  have hH := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 0
  have hW := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovHt.GeometricCondition _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.SizeCondition _root_.GlobalTheory.CovTop.LiftsCondition at hS
  unfold _root_.GlobalTheory.CovTop.HostNAlt _root_.GlobalTheory.CovTop.LiftsCondition at hH
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at hW
  refine ((hS.and hH).and hW).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, hx0⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3⟩ := hx0 x hx hle ι p hp
  exact _root_.GlobalTheory.CovHt.GeomBound.geometric_height_bound_at_place p i hX hG hQ hP h1 h2 h3 (b1 i) (b2 i) (b3 i) hi Y hY u1 hu
end GlobalTheory.CovHt.GeomBound
end
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covHt_geom_of_siegel_toroidal_semiAbelian : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.GeometricCondition := by
  first | exact @_root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size | exact _root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size | (intros; apply _root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepGoodReductionStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankPosNegativeWeightBundle
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNonzeroCuspForm
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.LowNonzero
theorem exists_cusp_uM_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (dat p i) (uM p i) 0), f ≠ 0 := by
  intro hP hG hQ hS hT hN
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have W := _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis
  have B := _root_.GlobalTheory.HSApp.wtBig_run_alt
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (W.and B)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, hf, hj, -⟩ := hA i hi
  obtain ⟨-, -, -, -, -, ⟨w, -, hw⟩, -⟩ := hB i hi
  have hbig := hC i hi
  obtain ⟨Z⟩ := GlobalTheory.CovTop.good_comp_nonempty _ p.T hL _ hj Y _ _ hY.1
  refine ⟨Z, _root_.GlobalTheory.CovTop.LowNonzero.exists_cusp_value_ne_zero_low_level hP hG hQ hS hT hN Y hY.1 hf hbig.one_le Z _ ?_⟩
  rw [hw]
  exact gapGe_wt_add_parWt _ hbig _ w
end GlobalTheory.CovTop.LowNonzero
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_cuspOn_of_covers : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (dat p i) (uM p i) 0), f ≠ 0 := by
  first | exact @_root_.GlobalTheory.CovTop.LowNonzero.exists_cusp_uM_alt_alt | exact _root_.GlobalTheory.CovTop.LowNonzero.exists_cusp_uM_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.LowNonzero.exists_cusp_uM_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.LowPos
open GlobalTheory.FlatTw GlobalTheory.FlatLine
theorem lowered_rank_pos_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hP hG hQ hS hKS hLie
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have F := _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le (_root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints hP)
  have S := _root_.GlobalTheory.T.exists_ne_zero_cuspOn_of_covers hP hG hQ hS hKS.toroidalChartsForFan hLie
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (F.and S)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, hp1, hq1, hf, hj, hn, -, -, hs⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  obtain ⟨Z, g, hg, hg0⟩ := hC i hi Y hY
  have hgood := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn
    (hs _ (Or.inl rfl)).1 (hs _ (Or.inl rfl)).2
  obtain ⟨g', hg', hg'0⟩ := _root_.GlobalTheory.CovTop.LowPos.exists_twist_ne_zero_of_lowered hP p.T _ Y _ _ hL hj hY.1 hFl (uM p i)
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)) ((p.κ i).n / 2) Z hg hg0
  exact rk_pos hgood (mem_cuspW_of_exZ hY.1.unf (exZ_lowered _ _ _ _ _ hn) hg'.1) hg'0
end GlobalTheory.CovTop.LowPos
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_pos_negative_weight_bundle_on_covers : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.LowPos.lowered_rank_pos_alt_alt | exact _root_.GlobalTheory.CovTop.LowPos.lowered_rank_pos_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.LowPos.lowered_rank_pos_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.DeepGoodAll
theorem deepGood_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness := by
  intro hP hG hQ hS hT hN
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have P := _root_.GlobalTheory.T.rank_pos_negative_weight_bundle_on_covers hP hG hQ hS hT hN
  unfold _root_.GlobalTheory.CovTop.DeepGoodness _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and P).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, hp1, hq1, hf, hj, hn, hu1, hu2, hs⟩ := hA i hi
  have hpos := hB i hi Y hY
  have hYg := hY.1
  have g := fun s hs' => _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg (wtA (p.κ i)) (p.κ i).n s hn
    (hs s hs').1 (hs s hs').2
  have hon := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg (uM p i) hu1 hu2
  refine ⟨?_, g _ (Or.inl rfl), g _ (Or.inr (Or.inr rfl)), hon.1, hpos, CompFin.finite_comp _ _,
    GlobalTheory.CovTop.good_comp_nonempty _ p.T hL _ hj Y _ _ hYg, hon.2⟩
  have := g 0 (Or.inr (Or.inl rfl))
  rwa [shiftG_zero] at this
end GlobalTheory.CovTop.DeepGoodAll
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepGood_of_toroidal_and_semiabelian : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness := by
  first | exact @_root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt_alt | exact _root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt_alt <;> assumption)
end
end
end
