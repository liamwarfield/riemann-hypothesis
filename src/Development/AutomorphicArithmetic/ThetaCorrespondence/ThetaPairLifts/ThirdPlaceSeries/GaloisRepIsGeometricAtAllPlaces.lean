module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsOfTiedLattices
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigStringAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameGeneratorResidual
noncomputable section

namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem cpAt' : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.IotaRed D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩; Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _) = ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  intro D hT hI hL hR σ k v i hl hocc hgood
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hW⟩ := hR i σ hocc hgood
  obtain ⟨B, κ, h1, h2⟩ := hI i
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (k := k) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rwa [(hW k v hl).dim, D.naut.lpDim_tw] at h
  have hfull : (D.naut.items₂ k _ (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)) :=
    (UpperTheory.GalS.nc_tw _ _).2 (hL.2 k v _ hfull (by rw [← D.naut.lab_loc i k σ v]; exact (hgood k).1.2.1 v)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by rw [hdim]; unfold Ranks.nV; omega)))
  have hine : ((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        (iotaO D.nd D.naut i) =
      ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    have e := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont _ (D.ntypes.tg_mem k v)
    rw [(hW k v hl).ine hn _ (D.ntypes.tg_mem k v), D.naut.inePol_tw _ _ _ (D.ntypes.tg_mem k v), D.ntypes.inertiaCharpoly_type k v _ hfull,
      ← D.naut.lab_loc i k σ v] at e
    rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact e
  have hred := GlobalTheory.TypeLeaf.map_eq_prod_of_valuationSubring B (iotaO D.nd D.naut i)
    (((fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom.comp
      κ.toRingHom).comp (IsLocalRing.residue B))
    ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) h1 (D.ntypes.teichC k)
    (fun x => fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
      (D.ntypes.iota k v (D.nd.w i) x))
    (fun x => by
      obtain ⟨h, e⟩ := h2 k v x
      exact ⟨h, congrArg (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out) e⟩)
    _ _ hine
  rw [← hT.2 i σ hocc hgood Sig ρ hP hρ (D.ntypes.tg k v)] at hred
  apply Polynomial.map_injective
    (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
    (RingHom.injective _)
  rw [hred, Polynomial.map_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  simp [GlobalTheory.TypeLeaf.map_primeToPart_fbar]

end GlobalTheory.ResidualTame

namespace GlobalTheory.RowWildTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem main_alt : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  intro D hT hL hR σ k v i hl hocc hgood s hs hwild
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hc⟩ := hR i σ hocc hgood
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, hιi⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have e := hc k v hl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rw [e.dim, D.naut.lpDim_tw] at this
    exact this
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)) :=
    (UpperTheory.GalS.nc_tw _ _).2 (hL.2 k v _ hfull (by rw [← D.naut.lab_loc i k σ v]; exact (hgood k).1.2.1 v)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by rw [hdim]; unfold Ranks.nV; omega)))
  have h1 := hL.1 k v _ hfull s hs hwild
  rw [hdim] at h1
  have h2 := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont s hs
  rw [e.ine hn s hs, D.naut.inePol_tw _ _ _ hs, h1] at h2
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have h3 : ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i)
      ((D.naut.iotaQC i).injective.comp hιi)
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, hcomp,
      ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact h2
  have h4 := hT.2 i σ hocc hgood Sig ρ hP hρ s
  rw [h3, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at h4
  have h5 : ((D.ntypes.rbar σ (D.nd.w i) s : GL (Fin D.R.r) (Fb (D.what₂.places.resChar (D.nd.w i))
      (D.what₂.places.resChar_prime (D.nd.w i)))) : Matrix (Fin D.R.r) (Fin D.R.r)
      (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
      (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
      (RingHom.injective _)
    rw [h4, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  have h6 : s ∈ (D.ntypes.rbar σ (D.nd.w i)).ker := by
    refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _ inferInstance
      (D.ntypes.rbar_open σ _) s ((D.what₂.places.resChar (D.nd.w i)) ^ D.R.r) (fun hmem => hw ?_) hwild ?_
    · rw [Nat.cast_pow, D.nd.w_l i] at hmem
      exact (D.naut.plGw k v).isPrime.mem_of_pow_mem _ hmem
    · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
      exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ h5
  exact h6

end GlobalTheory.RowWildTame

namespace GlobalTheory.RowTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

end GlobalTheory.RowTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricAtRamifiedPlaces
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsBClosing
end GlobalTheory.RowsBClosing
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  first | exact @_root_.UpperTheory.One.M.latticesB_closing_alt | exact _root_.UpperTheory.One.M.latticesB_closing_alt | (intros; apply _root_.UpperTheory.One.M.latticesB_closing_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricOfLocalConditions
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAClose
end GlobalTheory.RowsAClose
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.RowsAAlt D := by
  first | exact @_root_.UpperTheory.GalS.a_close_main | exact _root_.UpperTheory.GalS.a_close_main | (intros; apply _root_.UpperTheory.GalS.a_close_main <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisLast
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRest
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRest
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowPointLoc
theorem main_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) :
    GlobalTheory.SplitRead.RowPoint D.nd D.naut := by
  intro i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ
end GlobalTheory.RowPointLoc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRestStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_of_aux42_aux41
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.Conclusion42 D →
      _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
      GlobalTheory.SplitRead.RowPoint D.nd D.naut :=
  _root_.GlobalTheory.RowPointLoc.main_alt_alt hL D P
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PtLocalPin

theorem eig_at_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (w : PlE D.host) (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hcw : IsConjPl D.host w s.w)
    (hu : IsUnif D.host.E s.v ϖ) :
    ∃ c : ℕ → ℂ, X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.naut.locV i Q w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ k, 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i Q,
        NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) = c k • (P.M.loc i).real y := by
  classical
  have HT := P.H.hecke
  have hsB : s.v ∉ badPl D i := GlobalTheory.HeckeScalarAll.not_bad HT i hw s hcw
  have hex : ∀ k, ∃ c : ℂ, ∀ f ∈ P.H.av.S i Q,
      (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) →
      NG.tN (Umax D.host.E D.R.nV) s ϖ k f = c • f := fun k =>
    GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s ϖ k hu
  choose c hc using hex
  have hfT : ∀ y, (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    intro y
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : ∀ y ∈ D.naut.typeV i Q, (P.M.loc i).real y ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro y hy
    rw [P.H.av.typeV] at hy; exact hy
  have hfix : ∀ y, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real y) = (P.M.loc i).real y := by
    intro y κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ :=
      GlobalTheory.HeckeScalarAll.trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := (hfT y).2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    have hf0 : (P.M.loc i).real y0 ≠ 0 := fun h =>
      hy00 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
    obtain ⟨g, hg, hg0, hgfix⟩ := exists_fixed_of_isoTyp (P.H.av.irr i Q) s.v _ (hfI y0 hy0) hf0 (hfix y0)
    have hpol := P.H.au.locPol (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) s w ϖ hcw hu
      (Umax D.host.E D.R.nV) (fun κ _ => Iff.rfl) g hg hg0 hgfix c (fun k _ _ => hc k g hg hgfix)
    rw [hpol, D.nbc.embAV_loc, P.H.emb]
  · intro k _ _ y hy
    have hfinU := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
      (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
    have e1 : NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) =
        NG.tN (Umax D.host.E D.R.nV) s ϖ k ((P.M.loc i).real y) := by
      simp only [NG.tN]
      rw [GlobalTheory.HeckeScalarAll.heckeD_eq_of_fixed (P.M.loc i).J (P.M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _
        (hfix y)]
    rw [e1]
    exact GlobalTheory.HeckeScalarAll.tN_isoTyp (P.H.av.irr i Q) s ϖ k hfinU (c k) (hc k) _ (hfI y hy) (hfix y)
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i,
    GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro hL D P i
  refine GlobalTheory.T.pointLocalEigen_galoisPolynomial_split D P.M P.H.hecke P.H.rational P.H.av P.H.cover i ?_
  intro Q w hw
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  obtain ⟨c0, hp0, -⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s0 ϖ0 hc0 hu0
  have hN : normV w ≠ 0 := (lt_trans zero_lt_one (GlobalTheory.WeilDeligne.one_lt_normV w)).ne'
  refine ⟨c0, hp0.symm, fun k s ϖ hc hu h1 h2 y hy => ?_⟩
  obtain ⟨c, hp, hy'⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s ϖ hc hu
  rw [hy' k h1 h2 y hy, coeff_eq hN (hp.trans hp0.symm) h1 h2]

end GlobalTheory.PtLocalPin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptLocal_theta_exhaustion : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  exact _root_.GlobalTheory.PtLocalPin.main_alt_alt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTer
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PartOrthPin
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) → GlobalTheory.ThetaExh.PartOrth D.nd i := by
  intro hL D P i ⟨X⟩ σ σ' hne
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hni : ¬ (P.rep σ).Iso (P.rep σ') := fun h => hne (P.rep_inj σ σ' h)
  rw [X.φ_inner]
  exact GlobalTheory.IsotOrth.isotIn_orthogonal D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos X.stab X.inv X.adm
    (P.rep σ) (P.rep σ') hni _ ((X.isot σ u).1 hu) _ ((X.isot σ' v).1 hv)
end GlobalTheory.PartOrthPin
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameGeneratorResidual
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionTrivialOnWildInertia
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → _root_.UpperTheory.GalS.LabTameS D.nd D.naut → _root_.UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  first | exact @_root_.GlobalTheory.RowWildTame.main_alt | exact _root_.GlobalTheory.RowWildTame.main_alt | (intros; apply _root_.GlobalTheory.RowWildTame.main_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.ResidualTame
namespace GlobalTheory.RowWildTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.RowWildTame
namespace GlobalTheory.RowTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem tameGenerator_residual_alt_alt (D : D7) (h1 : GlobalTheory.RowCopy.RbarTie D) (h2 : GlobalTheory.RowTie.IotaRed D)
    (h3 : _root_.UpperTheory.GalS.LabTameS D.nd D.naut) (h4 : _root_.UpperTheory.GalS.RowRepAtGN D) :
    GlobalTheory.RowCopy.JointOccurrenceCondition D := by
  intro σ k v _ _ i hl hne hg
  refine ⟨_root_.GlobalTheory.ResidualTame.cpAt' D h1 h2 h3 h4 σ k v i hl hne hg, ?_⟩
  obtain ⟨φ, hI, hW⟩ := GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild _ _ _ D.nd D.naut k v _ (D.ntypes.tg_mem k v)
  refine ⟨φ, ?_⟩
  have h := _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN D h1 h3 h4 σ k v i hl hne hg _ hI hW
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h
  exact h
end GlobalTheory.RowTie
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondRho
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaPoint
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ParamRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
theorem rep_at_point_alt_alt (hLP : Formalism.MainNotions.SumRepresentations.At.TieLP N A) (hAut : Formalism.MainNotions.SumRepresentations.At.TieAut N A)
    (hW : WeightRegular N A) (hGal : _root_.UpperTheory.GalS.AutomorphicGaloisAdmissible N A) (hAN : Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne N A)
    (h41 : ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.provisionFortyOne N A i) (hGC : GoodCuspidal N A) (hXi : GlobalTheory.SplitRead.XiOverO N A)
    (a : N.Loc) (x : N.X a) (Sig : List (Part A.CG)) (hSig : HasParamX N A a x Sig)
    (hgood : goodSig N A Sig) :
    ∃ (ρ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.r) (N.O a)) (ξ : Formalism.ConjugateSelfDual.G H.E N.Om →* (N.O a)ˣ),
      IsRepOfSig N A a Sig ρ ∧
      (∀ k, N.l a ≠ H.g k → ∀ v ∈ placesOver H.E (H.g k), ∀ σ ∈ Ine (F := H.E) (N.plOm.1 v), ξ σ = 1) ∧
      IsRhoOf N a x (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) := by
  obtain ⟨π, rfl⟩ := hGC a x Sig hSig hgood
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨ξ, hξc, hξ⟩ := hXi a
  have hη : EtaType N A := ⟨hAut.1.1, fun τ z hz => by
    rcases (hAut.2.1 τ).1 with h | h <;> rw [h, Multiset.mem_singleton] at hz <;> subst hz
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by norm_num⟩⟩
  have al := part_alg N A hη hW a P _ hB ⟨R.r, A.tw π A.etaTinv, 1⟩ (by simp [twistIso]) (r_odd R) odd_one
  obtain ⟨ρ₀, hc0, -, haw, -⟩ := (_root_.UpperTheory.GalS.weakA' hGal a).1 R.r (r_odd R).pos _ al.1 al.2
  have hwd : ∀ w, w ∉ placesOver H.E (N.l a) → A.unr (A.locG π w) →
      A.wdOf a ρ₀ w = A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2) := by
    intro w hw hu
    have k1 := haw w hw
    rw [locG_tw_tw N A hLP] at k1
    exact k1.eq_of_unr ((A.unr_tw _ _).2 hu)
  obtain ⟨⟨-, rf, hr⟩, -, -⟩ := h41 a
  obtain ⟨hrc, hrs, hrf⟩ := hr x
  have hιc : Continuous (iotaOQ N A a) := GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A a
  have hcomp : iotaO N A a = (A.iotaQC a).toRingHom.comp (iotaOQ N A a) := rfl
  have hinj : Function.Injective (Polynomial.map (A.iotaQC a).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC a).injective
  have hfr : ∀ w, w ∉ placesOver H.E (N.l a) → A.unr (A.locG π w) → ∀ (B : ValuationSubring N.Om)
      (σ : Formalism.ConjugateSelfDual.G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      (((ρ₀ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom).charpoly =
        galPol A (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2)) := by
    intro w h1 h2 B σ hB hσ
    have hu : A.unr (A.wdOf a ρ₀ w) := by
      rw [hwd w h1 h2]; exact (A.unr_tw _ _).2 h2
    have e := A.wdOf_frob a ρ₀ w h1 hc0 hu B σ hB hσ
    rw [hwd w h1 h2] at e
    rw [Matrix.charpoly_map]
    exact e
  let R1 := Formalism.MainNotions.SumRepresentations.At.twGL ρ₀ ((Units.map (iotaOQ N A a).toMonoidHom).comp ξ)
  have hR1 : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) =
      iotaOQ N A a ((ξ g : (N.O a)ˣ) : N.O a) • ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) :=
    fun g => coe_twGL _ _ g
  have hR1c : Continuous fun g => ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) := by
    simp only [hR1]
    exact (hιc.comp hξc).smul hc0
  have hR1C : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom =
      iotaO N A a ((ξ g : (N.O a)ˣ) : N.O a) •
        ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom := by
    intro g
    rw [hR1, map_smul_matrix]
    rfl
  have hfin := placesOver_finite_joint_conditions_zpowers H.E (N.l a) (N.lPrime a).out.ne_zero
  have hall := (((hfin.eventually_cofinite_notMem.and (N.S a).finite_toSet.eventually_cofinite_notMem).and
    (N.Q a).finite_toSet.eventually_cofinite_notMem).and (A.locG_unr_ae π)).and
      (A.locG_unr_ae (A.tw π A.etaTinv))
  have hd := dense_iff_closure_eq.2 (hAN.2.2.1 _ (Filter.eventually_cofinite.1 hall))
  have hkey := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (Formalism.ConjugateSelfDual.G H.E N.Om) (Qbar (N.l a)) (R.r + R.t)
    (fun g => ((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a))
    (fun g => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) 0 0
      (Matrix.diagonal fun c : Fin R.t => iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))))
    _ hd (hrc.matrix_map hιc)
    (by
      refine Continuous.matrix_reindex ?_ _ _
      refine Continuous.matrix_fromBlocks hR1c continuous_const continuous_const ?_
      exact Continuous.matrix_diagonal (continuous_pi fun c => hιc.comp (N.chi_cont a _)))
    (by
      rintro g ⟨v, hv, hsp, B, hBv, hg⟩
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := not_not.1 hv
      have hso : SplitOut N a v := ⟨hsp, h1, h2, h3⟩
      apply hinj
      have eL : (((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map
          (iotaOQ N A a)).charpoly.map (A.iotaQC a).toRingHom = (heckePol N a x v).map (iotaO N A a) := by
        rw [Matrix.charpoly_map, Polynomial.map_map, ← hcomp, hrf v hso B g hBv hg]
      refine eL.trans ?_
      rw [charpoly_block, Polynomial.map_mul, ← Matrix.charpoly_map, hR1C g,
        hecke_split N A a x π P hP hB hso h5 hBv hg,
        galPol_twist N A π h4 _ ((hξ v h1).2 B g hBv hg),
        charpoly_smul_of_prod _ _ _ (hfr v h1 h4 B g hBv hg), prod_Icc_eq_fin, Polynomial.map_prod]
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl)
  haveI : CharZero (Qbar (N.l a)) := (RingHom.charZero_iff (A.iotaQC a).toRingHom.injective).2 inferInstance
  haveI : CharZero (Kf N a) := (RingHom.charZero_iff (A.iotaQ a).injective).2 inferInstance
  have hkey' : ∀ g, (((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly *
        ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) :=
    fun g => (Matrix.charpoly_map _ _).symm.trans ((hkey g).trans (charpoly_block _ _))
  obtain ⟨ρ', hρc, hρs, hρp⟩ := GlobalTheory.LatticeComplement.exists_lattice_complement (Formalism.ConjugateSelfDual.G H.E N.Om) (N.O a) (Kf N a)
    R.r R.t (rf x) (fun c : Fin R.t => N.chi a ((c : ℕ) + 1)) hrc hrs
    ⟨Qbar (N.l a), inferInstance, A.iotaQ a, R1, hkey'⟩
  have hcan : ∀ g, ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly := by
    intro g
    have e1 : (((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
        ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) *
          ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := by
      have := congrArg (Polynomial.map (iotaOQ N A a)) (hρp g)
      rw [Polynomial.map_mul, Polynomial.map_prod] at this
      refine this.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hne : (∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))) ≠ 0 :=
      (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _).ne_zero
    exact mul_right_cancel₀ hne (e1.symm.trans (hkey' g))
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹, ξ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have e : (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a))) =
        fun g => ((ξ g⁻¹ : (N.O a)ˣ) : N.O a) • ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)) := by
      funext g
      rw [coe_twGL, MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (hξc.comp continuous_inv).smul hρc
  · rw [mapRep_twGL]
    exact isSSRep_twGL _ _ hρs
  · filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hBw hσ
    have iso : isoLoc N A [⟨R.r, π, 1⟩] w = A.locG π w := by
      simp [isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]
    rw [iso]
    have h0 := hfr w h1 h2 B σ hBw hσ
    have c1 : (((ρ' σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).map (iotaO N A a)).charpoly =
        (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map fun α => X - C α).prod := by
      rw [Matrix.charpoly_map, hcomp, ← Polynomial.map_map, hcan σ, ← Matrix.charpoly_map, hR1C σ]
      exact charpoly_smul_of_prod _ _ _ h0
    have c2 := charpoly_smul_of_prod _ (iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) _ c1
    have huv : iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a) * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a) = 1 := by
      rw [← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
      simp
    have hL : ((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map
          (· * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) =
        A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2)) := by
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl fun α _ => ?_).trans (Multiset.map_id _)
      show α * _ * _ = α
      rw [mul_assoc, huv, mul_one]
    rw [← Matrix.charpoly_map, coe_twGL, map_smul_matrix, c2, hL]
    rfl
  · exact fun k hk v hv σ hσ =>
      (hξ v (not_mem_placesOver_of_ne (N.lPrime a).out (H.g_prime k) hk hv)).1 σ hσ
  · rw [twGL_twGL_inv]
    refine ⟨hρc, hρs, fun w hw B σ hB hσ => ?_⟩
    rw [prod_Icc_eq_fin (fun c => X - C ((N.chi a c σ : (N.O a)ˣ) : N.O a))]
    exact (hρp σ).symm.trans (hrf w hw B σ hB hσ)
end GlobalTheory.ParamRep
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ParamRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
section Twist
variable {Γ : Type} [Group Γ]
end Twist
end GlobalTheory.ParamRep
section Final
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem GlobalTheory.ParamRep.jointCond_33_rho_of_signature_adm5 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut → XiOverO D.nd D.naut → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D := by
  intro D h0 h2 _ h5 h41 hGC hXi a x _ Sig hSig hgood
  exact _root_.GlobalTheory.ParamRep.rep_at_point_alt_alt D.nd D.naut h0.1 h0.2.1 (GlobalTheory.LocalInv.weightRegular_definite D) h2 h5 h41 hGC hXi
    a x Sig hSig hgood
end Final
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaSig
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
noncomputable section
namespace GlobalTheory.RowRepOcc
theorem wdOf_of_isRepOfSig_alt_alt (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tie0 D) (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : Formalism.MainNotions.SumRepresentations.adm5 D)
    (i : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) (hr1 : 1 ≤ D.R.r)
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (hρ : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ)
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E (D.nd.l i)) :
    UpperTheory.GalS.RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) w)
      (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) := by
  obtain ⟨r, hrc, hrss, hraway, -⟩ := (_root_.UpperTheory.GalS.weak' h2 i).1 D.R.r hr1 π hc hr
  have hι := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  haveI := charZero_Kf D.nd D.naut i
  have hQc : Continuous fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL _ _) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))) := by
    simp only [coe_mapRep]
    exact hρ.1.matrix_map hι.1
  have hQss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) ρ) := by
    have e : mapRep (iotaOQ D.nd D.naut i) ρ =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) := by
      rw [mapRep_mapRep]
      rfl
    rw [e]
    exact isSSRep_map _ _ hρ.2.1
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  have hall := hρ.2.2.and ((D.naut.locG_unr_ae π).and hfin.eventually_cofinite_notMem)
  have hdense := dense_iff_closure_eq.2 (h5.2.2.1 _ (Filter.eventually_cofinite.1 hall))
  have hcp := GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.nd.l i)) D.R.r
    (fun g => ((r g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    _ hdense hrc hQc (by
      rintro σ ⟨w', hw', -, B, hB, hσ⟩
      obtain ⟨h1, hu, hwl⟩ := not_not.1 hw'
      apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
      have hunr : D.naut.unr (D.naut.wdOf i r w') := by
        rw [(hraway w' hwl).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
        exact (D.naut.unr_tw _ _).2 hu
      rw [D.naut.wdOf_frob i r w' hwl hrc hunr B σ hB hσ, (hraway w' hwl).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
      simp only [coe_mapRep]
      rw [Matrix.charpoly_map, Polynomial.map_map]
      have e : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaO D.nd D.naut i := rfl
      rw [e, h1 B σ hB hσ, isoLoc_one]
      rfl)
  obtain ⟨Pm, hPm⟩ := h5.2.2.2 (Qbar (D.nd.l i)) D.R.r r _ hrss hQss hcp
  rw [((hT.2.2.2.2.2 i).2.1 D.R.r r _ hrc Pm hPm).2.1 w (Or.inl hw)]
  exact hraway w hw
theorem repAtGN_of_point_split : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.adm5 D →
    Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → RowPoint D.nd D.naut → UpperTheory.GalS.RowRepAtGN D := by
  intro D hT h2 h5 h42 hJ hsp hRP i σ hne hg
  obtain ⟨i', hj, hl, hloc, ⟨φ, hφc, hφι⟩, P, x, hθ, hPx⟩ := hRP i σ hne
  have hne' : D.what₂.isot (D.nd.j i') σ ≠ ⊥ := by rw [hj]; exact hne
  obtain ⟨-, ⟨Sig, hW', hBC⟩, hcusp⟩ := h42 i' σ hne'
  have hB := hBC P hθ
  have hX : HasParamX D.nd D.naut i' x Sig := ⟨P, hPx, hB⟩
  have hgs : goodSig D.nd D.naut Sig := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW'.2.2).1 hg
  have hZ : x ∈ ZgoodN D.nd D.naut i' :=
    ⟨⟨P, hPx, _, hB, List.mem_map.2 ⟨muPart D.nd D.naut i', by simp, rfl⟩⟩, Sig, hX, hgs⟩
  obtain ⟨ρ₀, -, hρ₀, -, -⟩ := hJ i' x hZ Sig hX hgs
  obtain ⟨π, rfl⟩ := hcusp hg Sig hW'
  have hr1 : 1 ≤ D.R.r := (hW'.1 _ (List.mem_singleton_self _)).1
  obtain ⟨hc, hr⟩ := pointPar D hT h5 i' x π hX
  have hW : HasParamW D.nd D.naut i σ [⟨D.R.r, π, 1⟩] :=
    ⟨hW'.1, hW'.2.1, fun w hw => (hW'.2.2 w hw).trans (hloc w hw)⟩
  have hρ := isRepOfSig_transport D.nd D.naut φ hφc hφι _ ρ₀ hρ₀
  refine ⟨_, _, hW, hρ, fun k v hkl => ?_⟩
  have hv : D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) :=
    Formalism.MainNotions.N.placesOver_disj D.host.E (D.host.g_prime k) (D.nd.lPrime i).out (Ne.symm hkl) _ (D.naut.plGw_over k v)
  rw [← hW.2.2 _ (hsp k v), isoLoc_one]
  exact _root_.GlobalTheory.RowRepOcc.wdOf_of_isRepOfSig_alt_alt D hT h2 h5 i π hc hr hr1 _ hρ _ hv
end GlobalTheory.RowRepOcc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsLast
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.GoodDepthZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem main_alt_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → Formalism.MainNotions.N.GlobalDatumDepthZeroCondition D := by
  intro D hT hA h41 _ a x hx Sig hSig k v
  obtain ⟨-, Sig', hSig', hgood⟩ := hx
  have hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := hA.2.2
  have hL := charSum_of_tie D hT.1 hc
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨P', hP', hB'⟩ := id hSig'
  have hperm := ((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'
  have e1 := GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)
  rw [GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL] at e1
  have e2 := congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1
  simp only [lpChar_eta_back D hT.1] at e2
  rw [GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton] at e2
  rw [hc _ _ _ _ e2]
  exact GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v
end GlobalTheory.GoodDepthZero
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisLast
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsCClose
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D →
    GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D →
    (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  intro hL D P J hA hB a1 a8 p1 hi
  obtain ⟨p41, _, p42⟩ := p1
  obtain ⟨tl, lt, io, rb⟩ := _root_.GlobalTheory.TieLabAt.main_alt_alt hL D P
  have iface := _root_.GlobalTheory.AdmIface.main_alt_alt D
  have bc : ∀ i, BCEx D.nd D.naut i := iface.1 a1
  have lift : ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i := iface.2.2.1 p42
  have isot : Rows.IsotInternal D.what₂ := iface.2.2.2.2.2.mp a8
  have rho : GlobalDatumResidualRepCondition D :=
    _root_.GlobalTheory.ParamRep.jointCond_33_rho_of_signature_adm5 D hA.tie0 hA.a2 hB.a4 hA.a5 p41 (GlobalTheory.GoodCuspPoint.main D tl)
      (_root_.GlobalTheory.XiOver.main_alt_alt_alt D P.cf P.C P.tp P.chr P.val hA.tie0 hA.a2 hA.a5)
  have rp : _root_.UpperTheory.GalS.RowRepAtGN D :=
    _root_.GlobalTheory.RowRepOcc.repAtGN_of_point_split D hA.tie0 hA.a2 hA.a5 p42 rho hA.gsp (_root_.GlobalTheory.T.point_of_aux42_aux41 hL D P p42 p41)
  exact
    { c4b := _root_.GlobalTheory.RowTie.tameGenerator_residual_alt_alt D rb io lt rp
      rho := rho
      dz := _root_.GlobalTheory.GoodDepthZero.main_alt_alt D hA.tie0 hB.a4 p41 hA.gsp
      parUp := GlobalTheory.RowTie.parUpRec_of_ties D P.T hB.thetaOne (fun i => (hi i).1) bc (fun i => (hi i).2.1)
        (fun i => (hi i).2.2)
      downMem := GlobalTheory.RowTie.downMemRec_of_ties D P.T hB.thetaOne isot
        (fun i => _root_.GlobalTheory.PartOrthPin.main_alt_alt hL D P i ⟨J.rowM i⟩) (fun i => _root_.GlobalTheory.T.type_orthogonality_of_form' hL D P i (J.form i))
        (fun i => (hi i).1) bc (fun i => (hi i).2.1)
      goodPart := GlobalTheory.Proof.GoodComponentRecursion.goodPartRec_of_ties D P.T hB.thetaOne lift (fun i => _root_.GlobalTheory.T.ptLocal_theta_exhaustion hL D P i) bc
        (fun i => (hi i).2.1) }
end GlobalTheory.RowsCClose
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisLastStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.c_statement_of_pair_lift_splitBC_repOfLoc : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D → GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D → (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  first | exact @_root_.GlobalTheory.RowsCClose.main_alt_alt | exact _root_.GlobalTheory.RowsCClose.main_alt_alt | (intros; apply _root_.GlobalTheory.RowsCClose.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigCLe
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigCLe
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.EigGoodTypes
theorem eigC_le_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (hMt : MtParTie D.nd D.naut D.ntypes) (hbc : Formalism.MainNotions.SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D)
    (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) :
    ∃ σ' : D.ntypes.Par, eigC D.nd D.naut i x ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' ∧ D.ntypes.goodPar σ' := by
  obtain ⟨-, Sig, ⟨P0, hP0, hB0⟩, hg⟩ := hx
  let σ' : D.ntypes.Par := P.ty.par.eP.symm ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩
  have hloc : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w := fun w => by
    have e : P.ty.par.eP σ' = ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩ := Equiv.apply_symm_apply _ _
    rw [P.ty.par.locPar_def, e]
  refine ⟨σ', ?_, ?_⟩
  · rw [hMt i σ']
    refine iSup₂_le fun Q hQ => le_iSup₂_of_le Q ⟨Sig, fun w => (hloc w).symm, ?_⟩ le_rfl
    have hQ' : D.naut.ptV i Q = some x := hQ
    obtain ⟨Pa, hPa⟩ := hbc i Q
    have hperm := ((h41 i).2.1 P0 Q (by rw [hP0]; simp) (hP0.trans hQ'.symm)).1 _ _ hB0 hPa
    exact GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hPa
  · intro k
    simp only [D.ntypes.labPar_def, hloc]
    exact hg k
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D →
    Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  intro hL D P X h41 _ hMt hbc h0 h4 h5 hE0 hRead i hμ j hj x hx f hf y hy
  obtain ⟨σ', hle, hgood⟩ := _root_.GlobalTheory.EigGoodTypes.eigC_le_alt P h41 hMt hbc h0 h4 h5 i x hx
  exact (hRead _ hμ j f y hy).1 (onMt_cast hj f (hE0 i σ' _ (hle hf) hgood))
end GlobalTheory.EigGoodTypes
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigCLeStatement
namespace GlobalTheory.T

alias eigGood_of_archimedean_signature_adm5 := _root_.GlobalTheory.EigGoodTypes.main_alt_alt

end GlobalTheory.T
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoin
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoin
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeNZJoin
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
theorem typeNZRec_of_join_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) →
    ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  intro hL D P X _ hT i hS hG x hx
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  obtain ⟨hjPos, hjLe⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.val + 1 = D.nd.j i := Nat.sub_add_cancel hjPos
  exact of_cast (D := D) (μ := D.nd.mu i) hj _
    (fun f hf h0 => inj_at X hT i hS hG hμ j hj x hx f hf h0)
end GlobalTheory.TypeNZJoin
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoinStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) → ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i :=
  _root_.GlobalTheory.TypeNZJoin.typeNZRec_of_join_alt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAll
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  intro hP hHC hCusp hL D I hJ
  have a : _root_.GlobalTheory.NRows.RowsAAlt D := _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard hP hL D I.P hJ
  obtain ⟨J⟩ := _root_.GlobalTheory.T.nonempty_join_of_agree hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) a b
  have c : GlobalTheory.NRows.RowsC D := _root_.GlobalTheory.T.c_statement_of_pair_lift_splitBC_repOfLoc hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' hL D I.P I.X I.agree I.typeNZ i
    (_root_.GlobalTheory.T.eigString_of_agree_aux41_adm7_tieLab hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (_root_.GlobalTheory.T.eigGood_of_archimedean_signature_adm5 hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)
end GlobalTheory.RowsAll
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  first | exact @_root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
