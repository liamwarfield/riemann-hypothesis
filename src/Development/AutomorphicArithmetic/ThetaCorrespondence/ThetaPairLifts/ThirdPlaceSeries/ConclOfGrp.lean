module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSide
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeSide
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeSide
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeckeFrob
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem twisted_reciprocity_unramified_and_frobenius_eigenvalues_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (α : Fin n → ℂˣ) (hα : GlobalTheory.SmGL.HasSatake σ.ρ α) :
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).unr ∧
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).frobEig = twEig w α := by
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hα]
  have hu : (GlobalTheory.WeilDeligne.WD.mk (GlobalTheory.WeilDeligne.WDRep.diag h fun i => (α i)⁻¹)).unr :=
    (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _)
  refine ⟨(GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 hu, ?_⟩
  rw [GlobalTheory.WeilDeligne.WD.frobEig_tw _ _ hu, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  simp [twEig]
theorem heckeSide_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {L : Type} [Field L] [NumberField L] [IsCMField L] {Ω : Type}
    [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω} {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (hu : IsUnif L s.v ϖ) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) (f : GAf L n → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) (c : ℕ → ℂ)
    (hc : ∀ k, 1 ≤ k → k ≤ n → NG.tN J s ϖ k f = c k • f) (hp : IsPlaceOver A (conjSplit s).w)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSplit s).w.adicCompletion L))) (hσ : IsLocS π.S (conjSplit s) σ) :
    ∃ α, GlobalTheory.SmGL.HasSatake σ.ρ α ∧ ∀ k, 1 ≤ k → k ≤ n →
      ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k = (twEig (conjSplit s).w α).esymm k := by
  obtain ⟨i, T, hic, hcomp, hinj, hmem, heq⟩ := hσ
  have hf' := GlobalTheory.T.autRep_isotypic_splitPlace_localComponent L n π (conjSplit s) σ i T hinj hmem heq f hf
  obtain ⟨m, Tj, ej, hTj, hej, hsum⟩ := GlobalTheory.T.splitPlace_fixed_vector_sum_spherical_images L n π (conjSplit s) σ i hic hcomp f hf' hfix
  have hne : ∃ j, ej j ≠ 0 := by
    by_contra h
    push Not at h
    apply hf0
    rw [hsum]
    simp [h]
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    obtain ⟨j, hj⟩ := hne
    exact (Submodule.ne_bot_iff _).2 ⟨ej j, hej j, hj⟩
  have hR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL hp
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hR ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hR σ).2 hsph)
  refine ⟨α, hα, fun k hk1 hk2 => ?_⟩
  have hfin := GlobalTheory.T.finite_heckeDoubleCoset_cosets_at_splitPlace L n s ϖ hu J hJ k
  have key : ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k f =
      (twEig (conjSplit s).w α).esymm k • f := by
    conv_lhs => rw [hsum]
    rw [tN_sum J s ϖ k hfin, Finset.smul_sum, hsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ =>
      GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical L n s ϖ hu J hJ σ α hα i hic hcomp (Tj j) (hTj j) (ej j) (hej j) k hk1 hk2
  rw [hc k hk1 hk2, smul_smul] at key
  exact smul_left_injective ℂ hf0 key
theorem locPol_eq_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  intro hL D π s w ϖ hcw hu J hJ f hf hf0 hfix c hc x hx
  have hw := conjSplit_w D s w hcw
  subst hw
  obtain ⟨σc, hσc, huniq⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π (conjSplit s)
  obtain ⟨s', σ', h', hσ', hxe⟩ := hx
  have hh := huniq π s' h' σ' ((NG.AutRep.iso_equivalence (L := D.host.E) (n := D.R.nV)).refl π) hσ'
  have hxc : x = GlobalTheory.LocLanglands.cls σc := eq_of_heq (hxe.symm.trans (cls_heq h' σ' σc hh))
  subst hxc
  obtain ⟨α, hα, heig⟩ := _root_.GlobalTheory.HeckeFrob.heckeSide_alt hL π s ϖ hu J hJ f hf hf0 hfix c hc (D.nd.plOm.2 _) σc hσc
  obtain ⟨hun, hfe⟩ := _root_.GlobalTheory.HeckeFrob.twisted_reciprocity_unramified_and_frobenius_eigenvalues_eq hL (D.nd.plOm.2 _) σc α hα
  refine ⟨hun, ?_⟩
  rw [hfe, prod_eq_vieta D.R.nV _ (by simp [twEig])]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  rw [mul_assoc, heig k hk1 hk2]
end
end GlobalTheory.HeckeFrob
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeSideStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vector_fixed_local_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  first | exact @_root_.GlobalTheory.HeckeFrob.locPol_eq_alt | exact _root_.GlobalTheory.HeckeFrob.locPol_eq_alt | (intros; apply _root_.GlobalTheory.HeckeFrob.locPol_eq_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTail
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTail
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.SphLoc
section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
end Alg
section Val
open ValuativeRel Filter Topology
variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
end Val
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end
end GlobalTheory.SphLoc
end
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.SphLoc.main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphericalAtPlace s.v → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) x).unr := by
  intro hL D π s x hx hs
  obtain ⟨s', σ, h, hσ, e⟩ := hx
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have hsph := _root_.UpperTheory.One.M.Sph.isSph π s' σ hσ (hv ▸ hs)
  have hu := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s'.w)) σ).2 hsph
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 D.host.E)) (_ : u = u') (a : GlobalTheory.LocGL.IrrGL (k := u.adicCompletion D.host.E))
      (b : GlobalTheory.LocGL.IrrGL (k := u'.adicCompletion D.host.E)), HEq a b →
      (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 u) a).unr → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 u') b).unr := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    exact id
  exact key _ _ h _ _ e hu
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTailStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locRecT_unr_of_sphAt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphericalAtPlace s.v → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) x).unr := by
  first | exact @_root_.GlobalTheory.SphLoc.main_alt_alt | exact _root_.GlobalTheory.SphLoc.main_alt_alt | (intros; apply _root_.GlobalTheory.SphLoc.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NbcOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
variable {L n}
variable (L n)
variable {L n}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
end
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
open Classical in
def locOf_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w
set_option synthInstance.maxHeartbeats 400000 in
def boundaryConditionOfNoLocal (hE : IsEmpty D.nd.Loc) : NBC D.naut where
  AU := fun _ => AUq D.host.E D.R.nV
  multAU := fun _ X => X.rep.mult
  sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ X.rep.SphAt v
  locAU := fun _ X w => _root_.GlobalTheory.AutQuot.locOf_alt hL D T X.rep w
  satAU := fun _ X w => satOf X.rep w
  satAU_card := fun _ X w => satOf_card X.rep w
  Wt := fun _ => WtQ D.host.E D.R.nV
  infW := fun _ Y τ => NG.infOf (hwOf Y.rep τ)
  infW_card := fun _ Y τ => infOf_card _
  wtAU := fun _ X => wtOf D X.rep
  infW_alg := fun _ Y τ => infOf_nodup_alg (hwOf_antitone Y.rep τ)
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i
end GlobalTheory.AutQuot
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSide
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem locOf_eq_alt {π : NG.AutRep D.host.E D.R.nV} {w : PlE D.host} {x} (hx : LocAt π w x) :
    _root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w = (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x) := by
  have hex : ∃ x, LocAt (clsA π).rep w x := by
    obtain ⟨s, σ, hs, -, -⟩ := hx
    subst hs
    exact locAt_of_split _ s
  unfold _root_.GlobalTheory.AutQuot.locOf_alt
  rw [dite_eq_left hex, locAt_unique (rep_iso π) hex.choose_spec hx]
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem f_sph_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : NG.OverPl w v) : (∃ v', NG.OverPl w v' ∧ (clsA π).rep.SphericalAtPlace v') ↔ π.SphericalAtPlace v := by
  constructor
  · rintro ⟨v', hv', hs⟩
    rw [overPl_unique hv hv']
    exact _root_.UpperTheory.One.M.New.sphAt_iso (rep_iso π) hs
  · intro hs
    exact ⟨v, hv, _root_.UpperTheory.One.M.New.sphAt_iso (autIso_symm (rep_iso π)) hs⟩
theorem unr_locOf_of_sphAt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (hs : π.SphericalAtPlace s.v) :
    D.naut.unr (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) := by
  obtain ⟨x, hx⟩ := locAt_of_split π s
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx, T.unr, Equiv.apply_symm_apply]
  exact _root_.GlobalTheory.T.locRecT_unr_of_sphAt hL D π s x hx hs
theorem f_locPol_alt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ)
    (J : Subgroup (GAf D.host.E D.R.nV)) (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV))
    (f : GAf D.host.E D.R.nV → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) (c : ℕ → ℂ)
    (hc' : ∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) :
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w) ((1 - (D.R.nV : ℝ)) / 2)) := by
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_localComponent_conj_splitPlace D π s w hc
  obtain ⟨hun, hpol⟩ := _root_.GlobalTheory.T.spherical_vector_fixed_local_alt hL D π s w ϖ hc hu J hJ f hf hf0 hfix c hc' x hx
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx]
  have hu2 : D.naut.unr (D.naut.lpTw ((T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x))
      ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [T.unr, T.tw, Equiv.apply_symm_apply]; exact hun
  unfold galPol
  rw [T.frobEig _ _ hu2, T.tw, Equiv.apply_symm_apply]
  exact hpol
theorem e_locOf_eq_locRecT_of_isLocS (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS π.S s σ) :
    T.e s.w (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) =
      _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ) := by
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T ⟨s, σ, rfl, hσ, HEq.rfl⟩, Equiv.apply_symm_apply]
set_option maxHeartbeats 1000000 in
theorem exists_nbc_auSide_true_of_empty (hE : IsEmpty D.nd.Loc) :
    ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  ⟨{ _root_.GlobalTheory.AutQuot.boundaryConditionOfNoLocal hL D T hE with
      sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ (AUq.rep X).SphericalAtPlace v
      embAV_sph := fun i => isEmptyElim i },
    { cls := fun _ _ _ π => clsA π
      surj := fun _ _ _ X => ⟨X.rep, AUq.cls_rep X⟩
      iso := fun _ _ _ π π' => clsA_eq_iff π π'
      mult := fun _ _ _ π => GlobalTheory.T.automorphic_multiplicity_eq_of_iso _ _ _ _ (rep_iso π)
      sph := fun _ _ _ π w v _ hv => _root_.GlobalTheory.AutQuot.f_sph_alt D π w v hv
      sat := fun _ _ _ π v w hv Dv hα => f_sat D π v w hv Dv hα
      clsWt := fun _ _ _ a => clsW a
      surjWt := fun _ _ _ Y => ⟨Y.rep, WtQ.cls_rep Y⟩
      isoWt := fun _ _ _ a b => clsW_eq_iff a b
      wt := fun _ _ _ π a hd => f_wt D π a hd
      infW := fun _ _ _ a τ lam hl => f_infW D a τ lam hl
      locUnr := fun _ _ _ π s hs => _root_.GlobalTheory.AutQuot.unr_locOf_of_sphAt hL D T π s hs
      locPol := fun _ _ _ π s w ϖ hc hu J hJ f hf hf0 hfix c hc' => _root_.GlobalTheory.AutQuot.f_locPol_alt hL D T π s w ϖ hc hu J hJ f hf hf0 hfix c hc' },
    fun _ _ _ π s σ hσ => _root_.GlobalTheory.AutQuot.e_locOf_eq_locRecT_of_isLocS hL D T π s σ hσ⟩
end
end GlobalTheory.AutQuot
theorem GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc →
    ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  fun hL D hE T => _root_.GlobalTheory.AutQuot.exists_nbc_auSide_true_of_empty hL D T hE
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSideStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nbc_auSide_true_of_isEmpty_loc : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc → ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A := by
  first | exact @_root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty | exact _root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty | (intros; apply _root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRowTame
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LpDimLocRec
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem lpDim_locRec_alt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E))) : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).lpDim = n := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
def weilDeligneParameterOfLocalDatum {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  p.2.1 ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 p.1.1.w) (cls p.1.2)
def weilDeligneParameterAtPlace (σ : D.what₂.FT) (w : PlE D.host) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) := by
  classical
  exact if h : Nonempty (LocAt D rep σ w) then _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep h.some else (unrW D).par σ w
theorem parameter_of_local_datum_eq_reciprocity {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) (s : SplitPlace D.host.E) (hs : s.w = w)
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep p = hs ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
  subst hs
  obtain rfl := splitPlace_eq_of_isLocS _ _ s s0 hw τ τ0 hτ hl
  show _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ0) =
    _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ)
  rw [show GlobalTheory.LocLanglands.cls τ0 = GlobalTheory.LocLanglands.cls τ from
    congrArg (Sigma.mk _) (cl_eq_of_isLocS (rep σ) _ τ0 τ hl hτ)]
theorem parameter_at_place_eq_reciprocity_of_local_component (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  classical
  have h : Nonempty (LocAt D rep σ s.w) := ⟨⟨⟨s, τ⟩, rfl, hτ⟩⟩
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  rw [dite_eq_left h]
  exact _root_.GlobalTheory.RowPar.parameter_of_local_datum_eq_reciprocity hL D rep _ s rfl τ hτ
theorem dim_parameter_at_place_eq_rank (σ : D.what₂.FT) (w : PlE D.host) : (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ w).lpDim = D.R.r := by
  classical
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  by_cases h : Nonempty (LocAt D rep σ w)
  · rw [dite_eq_left h]
    generalize h.some = p
    obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
    subst hw
    exact _root_.GlobalTheory.RowPar.lpDim_locRec_alt hL _ τ0
  · rw [dite_eq_right h]
    exact (unrW D).dim σ w
end Loc
end GlobalTheory.RowPar
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem tame_reciprocity_of_fixed_ne_bot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (w.adicCompletion E)) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).tame := by
  obtain ⟨a, ha, ε, H⟩ := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h)
  have hx : GlobalTheory.PRep.fixed (cls τ).rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin (cls τ).1)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hf
  obtain ⟨m, b, hb, hw⟩ := haveI := UpperTheory.One.M.charZero_compl w; _root_.UpperTheory.One.M.LawsM.depth H _ (UpperTheory.One.M.good_of_fixed hq _ hx) hx
  rw [← hb, GlobalTheory.WeilDeligne.WD.tame_mk]
  intro g hg
  refine hw g ⟨GlobalTheory.WeilDeligne.Wild_le_Ine hg, fun x hx0 => ?_⟩
  have h1 := hg x hx0
  have e : ((g : G E Ω) x - x) = ((g : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  have h2 : (0 : _) < A.valuation x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx0
  calc A.valuation ((g : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x := by
        exact mul_lt_mul_of_pos_right h1 h2
    _ = A.valuation x := one_mul _
end Loc
end GlobalTheory.RowPar
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
theorem tame_parameter_at_place_of_fixed_ne_bot (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ)
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (s.w.adicCompletion D.host.E)) :
    (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w).tame := by
  rw [_root_.GlobalTheory.RowPar.parameter_at_place_eq_reciprocity_of_local_component hL D rep σ s τ hτ]
  exact _root_.GlobalTheory.RowPar.tame_reciprocity_of_fixed_ne_bot hL _ τ hf hq
end Loc
end GlobalTheory.RowPar
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
end Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
theorem exists_rowWD_rowTrue_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), RowDepth D rep →
    ∃ Rw : RowWD D, _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep Rw.par Rw.sat := by
  intro hL D rep hD
  refine ⟨⟨_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep, fun σ => satOf (rep σ).S, _root_.GlobalTheory.RowPar.dim_parameter_at_place_eq_rank hL D rep, fun σ k v => ?_⟩, ?_, ?_⟩
  · obtain ⟨s, τ, hs, hl, hf⟩ := hD σ k v
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hq : UpperTheory.One.M.IsQg ((D.naut.plGw k v).adicCompletion D.host.E) := ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩
    rw [← hs] at hq ⊢
    exact _root_.GlobalTheory.RowPar.tame_parameter_at_place_of_fixed_ne_bot hL D rep σ s τ hl hf hq
  · intro σ s τ hτ
    exact _root_.GlobalTheory.RowPar.parameter_at_place_eq_reciprocity_of_local_component hL D rep σ s τ hτ
  · intro σ v w hO Dv hα
    exact satOf_spec (rep σ).S v w hO Dv hα
end GlobalTheory.RowPar
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrp
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.TopA
def ConclAlt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Prop :=
  ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_au_true_and_types_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (h1 : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT))
    (h2 : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au) (h3 : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR)
    (h4 : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W)
    (h5 : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (h6 : LabConj D A.wdT) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep :=
  ⟨lay0 D, ⟨D.Z_tie, D.Zgood_tie⟩, D.etaJ_tie, A, h1, h2, h3, h4, rfl, HEq.rfl, HEq.rfl, HEq.rfl, h5, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, h6⟩
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem concl_setK_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk)
    (k1 : L.nd.PlG = D.nd.PlG) (k2 : HEq L.naut.plGw D.naut.plGw) (k3 : HEq L.ntypes.cenAmb D.ntypes.cenAmb)
    (k4 : HEq L.ntypes.cenMt D.ntypes.cenMt) (k5 : L.loc = D.loc) (k6 : HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd))
    (k7 : HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd))
    (k8 : HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd))
    (k9 : HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd))
    (h : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setK D L hZ hη) (cfK L hZ hη cf) jE rep) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨L', hZ', hη', A, h1, h2, h3, h4, e1, e2, e3, e4, h5, e5, e6, e7, e8, e9, h6⟩ := h
  exact ⟨L', hZ', hη', A, h1, h2, h3, h4, e1.trans k1, e2.trans k2, e3.trans k3, e4.trans k4, h5, e5.trans k5, e6.trans k6,
    e7.trans k7, e8.trans k8, e9.trans k9, h6⟩
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_automorphic_side_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T)) (chr : CharSide D cf) (au : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (hau : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T au) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨Pl⟩ := GlobalTheory.HeightCounting.nonempty_plSide D
  obtain ⟨X, h1, h0, e1, e2, e3, e4, e5, ⟨par⟩, hι⟩ := GlobalTheory.ParRay.exists_types hR hC D hE jE Pl hray
  obtain ⟨Γ', hΓ⟩ := exists_grp_setTy D hE X h1 h0 e1 e2 e3 Γ
  obtain ⟨wd⟩ := GlobalTheory.HeightCounting.exists_wdSide hdR (setTy D hE X h1 h0) T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setTy D hE X h1 h0) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlab' : LabTrue (setTy D hE X h1 h0) T := by
    intro k v a
    have := hlab k v a
    rw [← e1, ← e2] at this
    exact this
  have hconj' : LabConj (setTy D hE X h1 h0) T := by
    intro k v w hw
    have := hconj k v w hw
    rw [← e1, ← e2] at this
    exact this
  have hχ' : ChiTOk (setTy D hE X h1 h0) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← e1, ← e2] at this
    exact this
  have hT' : GlobalTheory.Mem.Top.TypesTrue X cf.P cf.W :=
    ⟨hT.pl, fun k => (congrFun e2 k).trans (hT.teich k), hT.chi, fun k p => (congrFun (congrFun e3 k) p).trans (hT.ser k p)⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setTy D hE X h1 h0) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_au_true_and_types_true hL (setTy D hE X h1 h0) cf' jE rep
      { bare := hE, wdT := T, lab := hlab', chr := { chr with }, row := ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩
        pl := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩, iota := hι ⟨Γ⟩, wd := wd, grp := Γ', par := par, au := { au with }
        chiT := hχ' }
      ⟨{ cg with }⟩ hau hrow hT' (fun k => (congrFun hΓ k).trans (hζ k)) hconj'
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setTy D hE X h1 h0)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl (heq_of_eq e4) (heq_of_eq e5) rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_cusp_galois_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T)) (chr : CharSide D cf) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨C, au, hau⟩ := _root_.GlobalTheory.T.exists_nbc_auSide_true_of_isEmpty_loc hL D hE T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setBC D C) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setBC D C) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_automorphic_side_true hL hdR hR hC (setBC D C) hE cf' jE rep hray hT { Γ with } hζ hχ T hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow
      ⟨{ cg with }⟩ { chr with } au hau
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setBC D C)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_local_parameters_true (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR) :
    _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨K, hcg, ⟨chr⟩⟩ := _root_.UpperTheory.One.M.New.exists_cgTrue_charSide hL hA D hE T cf hT.pl
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setCG D hE K) (cfCG hE K cf) jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_cusp_galois_true hL hdR hR hC (setCG D hE K) hE (cfCG hE K cf) jE rep hray ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩ { Γ with } hζ hχ
      (wdCG hE K T) hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow hcg chr
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setCG D hE K)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_group_side (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (hd : RowDepth D rep) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨Rw, hRw⟩ := _root_.GlobalTheory.RowPar.exists_rowWD_rowTrue_m_alt hL D rep hd
  obtain ⟨lab, h, A, C, tm, tg, hl, hpl, T, hlab, hconj, Rs, hp, hs⟩ := GlobalTheory.HeightCounting.exists_setAut_wdTie_labConj D hE Rw
  let cf' : CharFrame (setAut D hE lab h A C tm tg hl) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hk := fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_kv_of_eq D (hpl k v) (D.ntypes.tg k v) (Γ.ζ k) (Γ.kv k v) (Γ.tg_tame k v)
  choose kv hkv using hk
  have hχ' : ChiTOk (setAut D hE lab h A C tm tg hl) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← hpl k v] at this
    exact this
  have hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setAut D hE lab h A C tm tg hl) rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR := by
    have e1 : (fun σ w => T.e w (Rs.locR σ w)) = Rw.par := funext fun σ => funext fun w => hp σ w
    have e2 : Rs.satR = Rw.sat := funext fun σ => funext fun w => hs σ w
    rw [e1, e2]
    exact hRw
  have hT' : GlobalTheory.Mem.Top.TypesTrue (setAut D hE lab h A C tm tg hl).ntypes cf.P cf.W :=
    ⟨fun k v => (hpl k v).symm ▸ hT.pl k v, hT.teich, hT.chi, hT.ser⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setAut D hE lab h A C tm tg hl) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_local_parameters_true hA hL hdR hR hC (setAut D hE lab h A C tm tg hl) hE cf' jE rep hray hT'
      { Γ with kv := kv, tg_tame := hkv } hζ hχ' T hlab hconj Rs hrow
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setAut D hE lab h A C tm tg hl)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl (heq_of_eq (funext fun k => funext fun v => hpl k v)) HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_sideA_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → RowDepth D rep → (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT := by
  intro hL hA hdR hG hAr hR hC D hE cf jE rep hz hT hd hray
  obtain ⟨L, hZ, hη, hE', hT', k1, k2, k3, k4, ⟨Γ, hζ⟩, hχ, k5, k6, k7, k8, k9⟩ := GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling hG hAr D hE cf hz hT
  have hd' : RowDepth (setK D L hZ hη) rep := by
    intro σ k v
    obtain ⟨v₀, e⟩ := exists_eq_of_heq k1 k2 k v
    obtain ⟨s, τ, h1, h2⟩ := hd σ k v₀
    exact ⟨s, τ, h1.trans e, h2⟩
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep L hZ hη k1 k2 k3 k4 k5 k6 k7 k8 k9
    (_root_.GlobalTheory.HeightCounting.TopA.conclusion_of_group_side hA hL hdR hR hC (setK D L hZ hη) hE' (cfK L hZ hη cf) jE rep hray hT' Γ hζ hχ hd')
end GlobalTheory.HeightCounting.TopA
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrpStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.types_true_of_ray_class_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → RowDepth D rep → (∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT := by
  first | exact @_root_.GlobalTheory.HeightCounting.TopA.exists_sideA_alt | exact _root_.GlobalTheory.HeightCounting.TopA.exists_sideA_alt | (intros; apply _root_.GlobalTheory.HeightCounting.TopA.exists_sideA_alt <;> assumption)
end
end
