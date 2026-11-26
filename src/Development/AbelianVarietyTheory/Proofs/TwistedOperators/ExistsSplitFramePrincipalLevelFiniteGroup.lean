module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameInvMul
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
open scoped TensorProduct

namespace GlobalTheory.SplitPlaceRed

theorem isFrame_inv_mul {D : D7} {n : ℕ} {L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (β A : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (hA : A.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) L : Set (Fin n → Formalism.IndefR.Lev.EAf D)) =
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin n → Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.IsFrame (A⁻¹ * β) L := by
  intro x
  have hAm : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) L ↔ A.1.mulVec z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    intro z
    constructor
    · intro hz
      rw [← SetLike.mem_coe, ← hA]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [← SetLike.mem_coe, ← hA] at hz
      obtain ⟨z', hz', e⟩ := hz
      have e2 := congrArg (A⁻¹).1.mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at e2
      exact e2 ▸ hz'
  rw [hAm, hβ]
  have e : ((A⁻¹ * β)⁻¹).1 = (β⁻¹).1 * A.1 := by
    rw [mul_inv_rev, inv_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec]


set_option maxHeartbeats 1000000 in
theorem map_intGL_eq {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (A : GA D V) (g : Gv V v)
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = finE V (A * embV V v g * A⁻¹)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β))⁻¹ * splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g *
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β) := by
  set Φ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) →* GL (Fin V.rank) (Fv D.host.F v) :=
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) with hΦ
  have hfin : ∀ h : GA D V, Φ (finE V h) = Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom V h) := by
    intro h
    apply Units.ext
    apply Matrix.ext
    intro p q
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((finE V h).1 p q) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ ((Formalism.L2.Theta.matHom V h).1 p q)
    rw [GlobalTheory.LevSplit.finE_val]
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hk : Φ (finE V (embV V v g)) = splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g := by
    rw [hfin]
    exact GlobalTheory.SplitChartLink.rdA_matHom_embV V φ _
  have hyv : Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
    show _ = β⁻¹ * (β * _ * β⁻¹) * β
    group
  rw [hyv, hy]
  show _ = (Φ ((finE V A)⁻¹ * β))⁻¹ * _ * Φ ((finE V A)⁻¹ * β)
  simp only [map_mul, map_inv, hk]
  group

end GlobalTheory.SplitPlaceRed

namespace GlobalTheory.SplitPlaceRed


set_option maxHeartbeats 1000000 in
theorem splitRed_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (a : GfC V), IsBaseFrame V β Λ N → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ Formalism.IndefR.Lev.IsConjPl PP PP → (∀ k : Kv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β) → ∃ (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ResF v ≃+* kP PP), ∀ (k : Kv V v) (i j : Fin V.rank), (redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))).1 i j = ρ ((s.red k).1 i j) := by
  intro D V β Λ N a hB hL v PP hv hc hst

  have hcc : Formalism.IndefR.Lev.IsConjPl PP (Formalism.L2.DIV.conjPl PP) := by
    intro c hc'
    refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]
    exact hc'
  have hne : PP ≠ Formalism.L2.DIV.conjPl PP := fun e => hc (by
    have := hcc
    rw [← e] at this
    exact this)
  have hv' : (Formalism.L2.DIV.conjPl PP).under (𝓞 D.host.F) = v :=
    (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hcc).symm.trans hv
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) hne hv hv'
  set φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v := splitProj τ with hφ
  have hemb : GlobalTheory.SplitProjChart.emb φ = τ := by
    ext x; simp [hφ, GlobalTheory.SplitProjChart.emb, splitProj]

  have hfr := isFrame_inv_mul β (finE V (a : GA D V)) hB.1 hL.2
  have hsb := GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ
  let s : SplitAt D.sp.cm.sig V.gram (frameLat V) v :=
    ⟨GlobalTheory.SplitProjChart.emb φ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V (a : GA D V))⁻¹ * β), isCMExt_host D,
      GlobalTheory.ChartStab.hermND D V, GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v, hsb⟩
  have hP : splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := hemb ▸ hτ
  let ρ : ResF v ≃+* kP PP :=
    (splitResidueEquiv (GlobalTheory.SplitProjChart.emb φ)).symm.trans (Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP))
  refine ⟨s, ρ, fun k i j => ?_⟩
  obtain ⟨y, hy⟩ := hst k
  have hg0 : ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) = (a : GA D V) * embV V v (k : Gv V v) * (a : GA D V)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_locFin, Subgroup.coe_inv]
  rw [← hy, redFn_frGL]
  rw [hg0] at hy
  show resS D.host.F PP (y.1 i j) = ρ ((s.red k).1 i j)

  have hg : ∀ x : 𝓞 D.host.E, ((ρ : ResF v →+* kP PP).comp ((IsLocalRing.residue _).comp (GlobalTheory.PlaceRed.rdS φ)))
      (oToS D.host.F D.host.E x) = Ideal.Quotient.mk PP.asIdeal x := by
    intro x
    simp only [RingHom.comp_apply, GlobalTheory.PlaceRed.rdS_oToS]
    have e1 : GlobalTheory.PlaceRed.rdO φ x = splitInt (GlobalTheory.SplitProjChart.emb φ) x := Subtype.ext rfl
    rw [e1, ← splitResidueEquiv_mk]
    show Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP) ((splitResidueEquiv _).symm (splitResidueEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  rw [← GlobalTheory.PlaceRed.eq_resS PP _ hg]
  show ρ (IsLocalRing.residue _ (GlobalTheory.PlaceRed.rdS φ (y.1 i j))) = ρ ((s.red k).1 i j)
  congr 1
  have hred : (s.red k).1 i j = IsLocalRing.residue _ ((stabLocEquiv (isCMExt_host D) (GlobalTheory.ChartStab.hermND D V)
      (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v) hsb k).1 i j) := by
    show (splitRed _ _ _ _ k).1 i j = _
    rw [splitRed_val]; rfl
  rw [hred]
  congr 1
  apply Subtype.ext
  rw [coe_stabLocEquiv, splitEquivIn_apply]
  exact congrArg (fun m : GL (Fin V.rank) (Fv D.host.F v) => m.1 i j) (map_intGL_eq V φ β (a : GA D V) (k : Gv V v) y hy)

end GlobalTheory.SplitPlaceRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPointCarryingFrameLat
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FramePointMove

open scoped Matrix

theorem conj_maps_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, (J * x * J⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, x.1 *ᵥ w ∈ P := by
  have hinj : Function.Injective J.1.mulVec := fun a b h => by
    have := congrArg (fun z => (J⁻¹).1 *ᵥ z) h
    simpa [Matrix.mulVec_mulVec] using this
  have mem : ∀ z, J.1 *ᵥ z ∈ Q ↔ z ∈ P := fun z => by
    rw [← hJ, hinj.mem_set_image]
  have e : ∀ w, (J * x * J⁻¹).1 *ᵥ (J.1 *ᵥ w) = J.1 *ᵥ (x.1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp [Matrix.mul_assoc]
  constructor
  · intro h w hw
    have := h _ ((mem w).2 hw)
    rwa [e, mem] at this
  · intro h y hy
    rw [← hJ] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [e, mem]
    exact h w hw

theorem conj_maps_inv_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, ((J * x * J⁻¹)⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, (x⁻¹).1 *ᵥ w ∈ P := by
  have hinv : (J * x * J⁻¹)⁻¹ = J * x⁻¹ * J⁻¹ := by group
  rw [hinv]
  exact conj_maps_iff J x⁻¹ hJ


set_option maxHeartbeats 800000 in
theorem exists_point_carrying_frameLat : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ a : GfC V, GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val ∧ ∀ g : GfC V, finE V ((a * g * a⁻¹ : GfC V) : GA D V) ∈ St β ↔ ∀ v, finLoc V v g ∈ Kv V v := by
  intro D V β Λ N hβ
  obtain ⟨β₀, -, hβ₀⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D V
  obtain ⟨j, hj, -⟩ := GlobalTheory.FinAdIdent.exists_latIsom V V rfl (frameLat V) Λ β₀ β 1 N hβ₀ hβ ∅
    (fun _ h => absurd h (Set.notMem_empty _))
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  let J : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) := ⟨j, j', h1, h2⟩
  have hJ : J ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := hj.1.2
  obtain ⟨k, hk, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V J hJ
  refine ⟨⟨k, hk⟩, ?_, fun g => ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V k).val
    rw [e]
    exact hj
  · have hg : finE V ((⟨k, hk⟩ * g * ⟨k, hk⟩⁻¹ : GfC V) : GA D V) = J * finE V (g : GA D V) * J⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, e]
    have hJP : J.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) (frameLat V) : Set _) =
        (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) := hj.2
    rw [hg, GlobalTheory.LevSplit.mem_St_iff β Λ hβ.1]
    have hs := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β₀ (frameLat V) hβ₀.1 (g : GA D V)
    rw [GlobalTheory.LevSplit.mem_St_iff β₀ (frameLat V) hβ₀.1] at hs
    refine Iff.trans ?_ hs
    exact and_congr (conj_maps_iff J _ hJP) (conj_maps_inv_iff J _ hJP)

end GlobalTheory.FramePointMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedFnConjLocFinEqOne
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PlaceAwayRed

theorem redFn_conj_locFin_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (a : GfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v → ∀ k : Gv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β → redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
  intro D V β a v PP hPP k hS
  refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at hu
  subst hu
  have e : proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (embV V v k) = 1 := proj_emb_ne _ _ hPP k
  show proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((a : GA D V) * (locFin V v k : GA D V) * ((a⁻¹ : GfC V) : GA D V)) = 1
  rw [coe_locFin, MonoidHom.map_mul, MonoidHom.map_mul, e, mul_one, ← MonoidHom.map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, MonoidHom.map_one]

end GlobalTheory.PlaceAwayRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroup
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
namespace GlobalTheory.TrPtFrame

theorem finLoc_locFin_ne {D : D7} (V : HSp D) {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v) (x : Gv V v) :
    finLoc V u (locFin V v x) = 1 := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u ((locFin V v x : GfC V) : GA D V) = 1
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_ne _ _ h x

theorem mem_parLev {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank) (hQ : L.Q = ∅) {x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (hU : x ∈ UA D.sp.cm V.gram) (hS : x ∈ St β) : x ∈ parLev D.sp.cm V.gram β L := by
  rw [Formalism.L2.DIV.mem_parLev]
  refine ⟨hU, hS, fun PP _ => ?_, fun PP hP => ?_⟩
  · rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    exfalso
    simp [Formalism.L2.DIV.blkOf, h] at hij
  · exfalso
    simp [hQ] at hP

theorem upperLeftBlock_apply_of_eq {D : D7} {n r : ℕ} (hr : r ≤ n) (h : r = n) (PP : Pl D.host.E) (g : GL (Fin n) (kP PP)) (i j : Fin r) :
    ((upperLeftBlock hr g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) i j = (g : Matrix (Fin n) (Fin n) (kP PP)) (i.cast h) (j.cast h) := by
  subst h
  have hm : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro a b hab
    exfalso
    simp [Formalism.L2.DIV.blk2] at hab
  rw [Formalism.L2.DIV.upper_block_val_submatrix hr hm, Matrix.submatrix_apply]
  rfl

private theorem finLoc_locFin' {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Gv V v) :
    finLoc V v (locFin V v x) = x := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v ((locFin V v x : GfC V) : GA D V) = x
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_self _ _ v x

private theorem upperLeftBlock_one {D : D7} {n r : ℕ} (hr : r ≤ n) (PP : Pl D.host.E) :
    (upperLeftBlock hr (1 : GL (Fin n) (kP PP)) : GL (Fin r) (kP PP)) = 1 :=
  Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (Formalism.L2.DIV.blkR hr)

theorem exists_splitFrame_levG : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  intro D V β Λ N L h hB hQ hPg
  classical
  obtain ⟨a, hLat, hSt⟩ := GlobalTheory.FramePointMove.exists_point_carrying_frameLat D V β Λ N hB

  have hStk : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : Gv V v), k ∈ Kv V v →
      finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β := by
    intro v k hk
    refine (hSt (locFin V v k)).2 fun u => ?_
    by_cases huv : u = v
    · subst huv
      rw [finLoc_locFin']
      exact hk
    · rw [finLoc_locFin_ne V huv k]
      exact Subgroup.one_mem _

  have hinj : ∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
    intro PP hP PP' hP' he
    by_contra hne
    exact hPg PP hP PP' hP' (GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D PP PP' he hne)
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := L.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  let f : L.Pg → S := fun PP => ⟨PP.1.under (𝓞 D.host.F), Finset.mem_image_of_mem _ PP.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro PP PP' he
      exact Subtype.ext (hinj _ PP.2 _ PP'.2 (congrArg Subtype.val he))
    · intro v
      obtain ⟨PP, hP, he⟩ := Finset.mem_image.1 v.2
      exact ⟨⟨PP, hP⟩, Subtype.ext he⟩
  let pl : S ≃ L.Pg := (Equiv.ofBijective f hf).symm
  have hunder : ∀ v : S, (pl v).1.under (𝓞 D.host.F) = v.1 := fun v =>
    congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply v)
  choose s ρ hsρ using fun v : S =>
    GlobalTheory.SplitPlaceRed.splitRed_frame D V β Λ N a hB hLat v.1 (pl v).1 (hunder v)
      (hPg _ (pl v).2 _ (pl v).2) (fun k => hStk v.1 k.1 k.2)
  refine ⟨a, S, pl, s, ρ, ?_, ?_⟩
  · intro v hv k hk
    have hx := hStk v k hk
    rw [Formalism.IndefR.Lev.levG, Formalism.IndefR.Lev.mem_levA]
    refine ⟨(a * locFin V v k * a⁻¹ : GfC V).2, ?_⟩
    rw [Formalism.L2.DIV.mem_lev]
    refine ⟨mem_parLev (flag1L L) h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, ?_⟩
    have hone : ∀ PP ∈ L.Pg, redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
      intro PP hP
      refine GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v PP (fun he => hv ?_) k hx
      rw [← he]
      exact Finset.mem_image_of_mem _ hP
    have hrt : rTup β (flag1L L) (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = rTup β (flag1L L) 1 := by
      funext PP
      simp only [Formalism.L2.DIV.rTup]
      rw [hone PP.1 PP.2, Formalism.L2.DIV.redFn_one]
    rw [hrt, Formalism.L2.DIV.rTup_one]
    exact Subgroup.one_mem _
  · intro v k
    have hx := hStk v.1 k.1 k.2
    refine ⟨rTup β L (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)),
      ⟨(a * locFin V v k * a⁻¹ : GfC V).2, mem_parLev L h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, rfl⟩, ?_, ?_⟩
    · intro PP hne
      have hu : PP.1.under (𝓞 D.host.F) ≠ v.1 := by
        intro he
        exact hne (Subtype.ext (hinj _ PP.2 _ (pl v).2 (he.trans (hunder v).symm)))
      show upperLeftBlock L.hr (redFn β PP.1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) = 1
      rw [GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v.1 PP.1 hu k.1 hx]
      exact upperLeftBlock_one L.hr PP.1
    · intro i j
      show ((upperLeftBlock L.hr (redFn β (pl v).1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) :
        GL (Fin L.r) (kP (pl v).1)) : Matrix (Fin L.r) (Fin L.r) (kP (pl v).1)) i j = _
      rw [upperLeftBlock_apply_of_eq L.hr h]
      exact hsρ v k (i.cast h) (j.cast h)

end GlobalTheory.TrPtFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroupStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  first | exact @GlobalTheory.TrPtFrame.exists_splitFrame_levG | exact GlobalTheory.TrPtFrame.exists_splitFrame_levG | (intros; apply GlobalTheory.TrPtFrame.exists_splitFrame_levG <;> assumption)
end
